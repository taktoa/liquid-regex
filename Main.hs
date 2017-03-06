{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- LIQUID "--fullcheck" -}
module Main where

import           GHC.Generics (Generic)

import           Data.Bits    ((.&.), (.|.))
import qualified Data.Bits    as Bits

import           Data.List    (foldl')

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

-- | Match the given string against the given regular expression by taking the
-- Brzozowski derivative.
matchDeriv :: (Eq tok) => Regex tok -> [tok] -> Bool
matchDeriv rx str = isNullable (derivative str rx)

-- | A refinement type alias for Int.
type Natural = Int
{-@ type Natural = Nat @-}

-- | The type representing states in an NFA.
data NatSet = MkNatSet {-# UNPACK #-} !Natural !Integer

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

data DFA tok
  = MkDFA
    { dfaNumStates  :: Natural
      -- ^ The number of states.
    , dfaStarting   :: Natural
      -- ^ The starting state.
    , dfaTransition :: tok -> Natural -> Natural
      -- ^ The transition function.
    , dfaAccepting  :: NatSet
      -- ^ The accepting states.
    }

-- | The free NFA corresponding to a given DFA.
fromDFAtoNFA :: DFA tok -> NFA tok
fromDFAtoNFA (MkDFA n s f acc) = let f' t q = singletonNS (f t q)
                                 in MkNFA n (singletonNS s) f' acc

-- | The powerset DFA corresponding to a given NFA.
fromNFAtoDFA :: NFA tok -> DFA tok
fromNFAtoDFA (MkNFA n as f bs) = MkDFA (2 ^ n) _ _ _ -- FIXME

-- | Minimizes the number of states in the given DFA.
minimizeDFA :: DFA tok -> DFA tok
minimizeDFA (MkDFA n s f acc) = _ -- FIXME

-- | The complement of a given DFA.
complementDFA :: DFA tok -> DFA tok
complementDFA (MkDFA n s f acc) = MkDFA n s f acc'
  where
    acc' = foldr unionNS emptyNS
           [singletonNS k | k <- [0 .. n - 1], not (containsNS acc k)]

-- | The intersection of two DFAs.
intersectionDFA :: DFA tok -> DFA tok -> DFA tok
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
      -> {v : Bool | ((Prop v) <=> (Prop (matchDeriv rx str))) }
@-}
matchRegex :: (Eq tok) => Regex tok -> [tok] -> Bool
matchRegex rx toks = matchNFA (thompson rx) toks

main :: IO ()
main = pure ()
