{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- LIQUID "--fullcheck" -}
module Main where

import           GHC.Generics (Generic)

import           Data.Maybe

import           Data.Bits    ((.&.), (.|.))
import qualified Data.Bits    as Bits

import           Data.List    (foldl')

import           Data.Set     (Set)
import qualified Data.Set     as Set

(|>) :: a -> (a -> b) -> b
(|>) = flip ($)
infixl 0 |>

(.>) :: (a -> b) -> (b -> c) -> a -> c
(.>) = flip (.)
infixl 9 .>

-- | The type of generalized regular expressions over a given alphabet.
data Regex tok
  = Ø
  -- ^ The regular expression corresponding to the empty language.
  | Ɛ
  -- ^ The regular expression matching only the empty string.
  | Tok   !tok
  -- ^ The regular expression matching exactly one token.
  | Star  !(Regex tok)
  -- ^ Kleene's star operator.
  | Comp  !(Regex tok)
  -- ^ The complement of a regular expression.
  | (:.:) !(Regex tok) !(Regex tok)
  -- ^ The concatenation of two regular expressions.
  | (:|:) !(Regex tok) !(Regex tok)
  -- ^ The union of two regular expressions.
  | (:&:) !(Regex tok) !(Regex tok)
  -- ^ The intersection of two regular expressions.
  deriving (Eq, Functor, Generic)

{-@ autosize Regex @-}

-- | Returns true if the language of the given regular expression contains Ɛ,
--   and otherwise returns false.
isNullable :: Regex tok -> Bool
isNullable Ø         = False
isNullable Ɛ         = True
isNullable (Tok _)   = False
isNullable (Comp r)  = not (isNullable r)
isNullable (Star r)  = True
isNullable (r :|: s) = isNullable r || isNullable s
isNullable (r :&: s) = isNullable r && isNullable s
isNullable (r :.: s) = isNullable r && isNullable s

-- | Returns Ɛ if the language of the given regular expression contains Ɛ, and
--   otherwise returns Ø.
nullable :: Regex tok -> Regex tok
nullable r = if isNullable r then Ɛ else Ø

-- | The Brzozowski derivative of a regular expression with respect to a token.
deriv :: (Eq tok) => tok -> Regex tok -> Regex tok
deriv a Ø         = Ø
deriv a Ɛ         = Ø
deriv a (Tok t)   = if t == a then Ɛ else Ø
deriv a (Comp r)  = Comp (deriv a r)
deriv a (Star r)  = deriv a r :.: Star r
deriv a (r :|: s) = deriv a r :|: deriv a s
deriv a (r :&: s) = deriv a r :&: deriv a s
deriv a (r :.: s) = let d1 = deriv a r
                        d2 = deriv a s
                    in if isNullable r
                       then (d1 :.: s) :|: d2
                       else d1 :.: s

-- | The Brzozowski derivative of a regular expression with respect to a string.
derivative :: (Eq tok, Foldable t) => t tok -> Regex tok -> Regex tok
derivative tokens rx = foldr deriv rx tokens

{-@ measure matchDeriv :: Regex tok -> [tok] -> Bool @-}
-- | Match the given string against the given regular expression by taking the
-- Brzozowski derivative.
matchDeriv :: (Eq tok) => Regex tok -> [tok] -> Bool
matchDeriv rx str = isNullable (derivative str rx)

-- | A refinement type alias for Int.
type Natural = Int
{-@ type Natural = Nat @-}

-- | The type representing states in an NFA.
data NatSet = MkNatSet {-# UNPACK #-} !Natural !Integer
            deriving (Eq, Ord, Generic)

-- | FIXME: doc
emptyNS :: NatSet
emptyNS = MkNatSet 0 0

-- | FIXME: doc
singletonNS :: Natural -> NatSet
singletonNS x = MkNatSet 1 (Bits.shiftL 1 x)

-- | FIXME: doc
intersectionNS :: NatSet -> NatSet -> NatSet
intersectionNS (MkNatSet m x) (MkNatSet n y) = MkNatSet (max m n) (x .&. y)

-- | FIXME: doc
(∩) :: NatSet -> NatSet -> NatSet
(∩) = intersectionNS

-- | FIXME: doc
unionNS :: NatSet -> NatSet -> NatSet
unionNS (MkNatSet m x) (MkNatSet n y) = MkNatSet (max m n) (x .|. y)

-- | FIXME: doc
(∪) :: NatSet -> NatSet -> NatSet
(∪) = unionNS

-- | FIXME: doc
shiftNS :: Natural -> NatSet -> NatSet
shiftNS k (MkNatSet n x) = MkNatSet (n + k) (Bits.shiftL x k)

-- | FIXME: doc
nullNS :: NatSet -> Bool
nullNS (MkNatSet _ x) = (x == 0)

{-@ assume sizeNS :: NatSet -> Natural @-} -- FIXME
-- | FIXME: doc
sizeNS :: NatSet -> Natural
sizeNS (MkNatSet _ x) = Bits.popCount x

-- | FIXME: doc
containsNS :: NatSet -> Natural -> Bool
containsNS (MkNatSet _ x) k = Bits.testBit x k

{-@ assume rangeNS :: NatSet -> Natural @-} -- FIXME
-- | FIXME: doc
rangeNS :: NatSet -> Natural
rangeNS (MkNatSet n _) = n

-- | FIXME: doc
foldlNS :: forall b. (b -> Natural -> b) -> b -> NatSet -> b
foldlNS f acc0 ns = go (rangeNS ns) acc0 (sizeNS ns) 0
  where
    {-@ go :: d:Nat -> b -> Nat -> Nat -> b / [d] @-}
    go :: Natural -> b -> Natural -> Natural -> b
    go d !acc n b | (n <= 0) || (d <= 0) = acc
                  | containsNS ns b      = go (d - 1) (f acc b) (n - 1) (b + 1)
                  | otherwise            = go (d - 1) acc       n       (b + 1)

-- | FIXME: doc
unionsNS :: (Foldable t) => t NatSet -> NatSet
unionsNS = foldr unionNS emptyNS

-- | The type representing an NFA.
--
-- This type and many of the functions using it are based on Gabriel Gonzalez's
-- <http://github.com/Gabriel439/slides/blob/master/regex/regex.md notes>.
data NFA tok
  = MkNFA
    { nfaNumStates  :: Natural
      -- ^ The number of states.
    , nfaStarting   :: NatSet
      -- ^ The set of starting states.
    , nfaTransition :: tok -> Natural -> NatSet
      -- ^ The transition function.
    , nfaAccepting  :: NatSet
      -- ^ The set of accepting states.
    }
  deriving (Generic)

-- | Match a sequence of tokens against an NFA.
matchNFA :: NFA tok -> [tok] -> Bool
matchNFA (MkNFA n as f bs) ts = intersectionNS bs (foldl' step' as ts)
                                |> nullNS |> not
  where
    step' s0 i = foldlNS (\acc j -> unionNS acc (f i j)) emptyNS s0

-- | The NFA that accepts a single token if it satisfies a given predicate.
satisfyNFA :: (tok -> Bool) -> NFA tok
satisfyNFA predicate = MkNFA n as f bs
  where
    n = 2
    as = singletonNS 0
    bs = singletonNS 0
    f t s = if (s == 0) && predicate t then singletonNS 1 else emptyNS

-- | The NFA that matches no strings.
empNFA :: NFA tok
empNFA = MkNFA 0 emptyNS (\_ _ -> emptyNS) emptyNS

-- | The NFA matching only an empty string.
epsNFA :: NFA tok
epsNFA = MkNFA 1 (singletonNS 0) (\_ _ -> emptyNS) (singletonNS 0)

-- | The union of two NFAs.
unionNFA :: NFA tok -> NFA tok -> NFA tok
unionNFA (MkNFA nL asL fL bsL) (MkNFA nR asR fR bsR) = MkNFA n as f bs
  where
    n = nL + nR
    as = asL ∪ shiftNS nL asR
    bs = bsL ∪ shiftNS nL bsR
    f i s | s < nL    = fL i s
          | otherwise = shiftNS nL (fR i (s - nL))

-- | Sequential composition of NFAs.
sequenceNFA :: NFA tok -> NFA tok -> NFA tok
sequenceNFA (MkNFA nL asL fL bsL) (MkNFA nR asR fR bsR) = MkNFA n as f bs
  where
    n = nL + nR
    as = if nullNS (asL ∩ bsL)
         then asL
         else asL ∪ shiftNS nL asR
    bs = shiftNS nL bsR
    f i s = let x = fL i s
            in if s < nL
               then if nullNS (x ∩ bsL)
                    then x
                    else x ∪ shiftNS nL asR
               else shiftNS nL (fR i (s - nL))

{- measure dfaStates :: DFA st tok -> Set st @-}

{-@
data DFA st tok
  = MkDFA
    { dfaStates     :: Set st
    , dfaStarting   :: {q : st | Set_mem q dfaStates}
    , dfaTransition :: tok
                    -> {qI : st | Set_mem qI dfaStates}
                    -> {qO : st | Set_mem qO dfaStates}
    , dfaAccepting  :: {q : st | Set_mem q dfaStates} -> Bool
    }
@-}

data DFA st tok
  = MkDFA
    { dfaStates     :: Set st
      -- ^ The set of states.
    , dfaStarting   :: st
      -- ^ The starting state.
    , dfaTransition :: tok -> st -> st
      -- ^ The transition function.
    , dfaAccepting  :: st -> Bool
      -- ^ The accepting states.
    }
  deriving (Generic)

{-@ autosize DFA @-}

{-@ type VState dfa = {q : _ | Prop (Set_mem q (dfaStates dfa))} @-}

-- | The "free" NFA corresponding to a given DFA.
fromDFAtoNFA :: (Ord st) => DFA st tok -> NFA tok
fromDFAtoNFA (MkDFA ss s f acc) = MkNFA (Set.size ss) s' f' acc'
  where
    s'   = toNS s
    f'   = \t q -> toNS $ f t (toSt q)
    acc' = unionsNS $ map toNS $ filter acc $ Set.toList ss
    toSt n = Set.elemAt n ss
    toNS q = singletonNS $ Set.findIndex q ss

-- | The powerset DFA corresponding to a given NFA.
fromNFAtoDFA :: NFA tok -> DFA NatSet tok
fromNFAtoDFA (MkNFA n as f bs) = MkDFA ss _ _ _ -- FIXME
  where
    ss :: Set NatSet
    ss = _

-- | Minimizes the number of states in the given DFA.
minimizeDFA :: DFA st tok -> DFA st tok
 -- FIXME: use a better DFA minimization algorithm
minimizeDFA (MkDFA ss s f acc) = MkDFA ss s f acc

-- | The complement of a given DFA.
complementDFA :: DFA st tok -> DFA st tok
complementDFA (MkDFA ss s f acc) = MkDFA ss s f (acc .> not)

-- | The intersection of two DFAs.
intersectionDFA :: DFA st tok -> DFA st tok -> DFA (st, st) tok
intersectionDFA (MkDFA nL sL fL accL) (MkDFA nR sR fR accR) = MkDFA n s f acc
  where
    -- FIXME
    n   = _
    s   = _
    f   = _
    acc = _

-- | The complement of a given NFA.
complementNFA :: NFA tok -> NFA tok
complementNFA = fromNFAtoDFA .> minimizeDFA .> complementDFA .> fromDFAtoNFA

-- | The intersection of two NFAs.
intersectionNFA :: NFA tok -> NFA tok -> NFA tok
intersectionNFA nL nR = let toDFA = fromNFAtoDFA .> minimizeDFA
                            (dL, dR) = (toDFA nL, toDFA nR)
                        in intersectionDFA dL dR |> minimizeDFA |> fromDFAtoNFA

-- | An implementation of Thompson's construction, which converts regular
-- expressions to nondeterministic finite automata.
thompson :: forall tok. (Eq tok) => Regex tok -> NFA tok
thompson Ø         = empNFA
thompson Ɛ         = epsNFA
thompson (Tok t)   = satisfyNFA (== t)
thompson (Comp r)  = complementNFA (thompson r)
thompson (Star r)  = let MkNFA n as f bs = thompson r
                         f' i s = let x = f i s
                                  in if nullNS (x ∩ bs) then x else x ∪ as
                     in MkNFA n as f' bs
thompson (r :|: s) = unionNFA (thompson r) (thompson s)
thompson (r :&: s) = intersectionNFA (thompson r) (thompson s)
thompson (r :.: s) = sequenceNFA (thompson r) (thompson s)

{-@ matchRegex
      :: rx:(Regex tok)
      -> str:[tok]
      -> {v : Bool | ((Prop v) <=> (Prop (matchDeriv rx str)))}
@-}
matchRegex :: (Eq tok) => Regex tok -> [tok] -> Bool
matchRegex rx toks = matchNFA (thompson rx) toks

main :: IO ()
main = pure ()
