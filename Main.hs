{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- LIQUID "--fullcheck" -}
module Main where

import           GHC.Generics (Generic)

import           Data.Set     (Set)
import qualified Data.Set     as Set

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

-- | A refinement type alias for Int.
type Natural = Int
{-@ type Natural = Nat @-}

-- | The type representing states in an NFA.
type NFAState = Natural

-- | The type representing an NFA.
--
-- This type and many of the functions using it are based on Gabriel Gonzalez's
-- <http://github.com/Gabriel439/slides/blob/master/regex/regex.md notes>.
data NFA tok
  = MkNFA
    { numStates  :: Natural
      -- ^ The number of states.
    , starting   :: Set NFAState
      -- ^ The set of starting states.
    , transition :: tok -> NFAState -> Set NFAState
      -- ^ The transition function.
    , accepting  :: Set NFAState
      -- ^ The set of accepting states.
    }

-- | Match a sequence of tokens against an NFA.
matchNFA :: NFA tok -> [tok] -> Bool
matchNFA (MkNFA _ as _ bs) []     = not (Set.null (Set.intersection as bs))
matchNFA (MkNFA n as f bs) (i:is) = let as' = Set.unions (f i <$> Set.elems as)
                                    in matchNFA (MkNFA n as' f bs) is

-- | The NFA that accepts a single token if it satisfies a given predicate.
satisfy :: (tok -> Bool) -> NFA tok
satisfy predicate = MkNFA n as f bs
  where
    n = 2
    as = Set.singleton 0
    bs = Set.singleton 0
    f t s = if (s == 0) && predicate t then Set.singleton 1 else Set.empty

thompson :: forall tok. (Eq tok) => Regex tok -> NFA tok
thompson = go
  where
    go :: Regex tok -> NFA tok
    go Ø         = empNFA
    go Ɛ         = epsNFA
    go (Tok t)   = satisfy (== t)
    go (Comp r)  = error "complement not supported :("
    go (Star r)  = let MkNFA n as f bs = thompson r
                       f' i s = let x = f i s
                                in if Set.null (Set.intersection x bs)
                                   then x
                                   else Set.union x as
                   in MkNFA n as f' bs
    go (r :|: s) = let MkNFA nL asL fL bsL = thompson r
                       MkNFA nR asR fR bsR = thompson s
                       n = nL + nR
                       as = Set.union asL (shift nL asR)
                       bs = Set.union bsL (shift nL bsR)
                       f i s | s < nL    = fL i s
                             | otherwise = shift nL (fR i (s - nL))
                   in MkNFA n as f bs
    go (r :&: s) = error "intersection not supported :("
    go (r :.: s) = let MkNFA nL asL fL bsL = thompson r
                       MkNFA nR asR fR bsR = thompson s
                       n = nL + nR
                       as = Set.union asL
                            (if Set.null (Set.intersection asL bsL)
                             then Set.empty
                             else shift nL asR)
                       bs = shift nL bsR
                       f i s = let x = fL i s
                               in if s < nL
                                  then if Set.null (Set.intersection x bsL)
                                       then x
                                       else Set.union x (shift nL asR)
                                  else shift nL (fR i (s - nL))
                   in MkNFA n as f bs

    empNFA, epsNFA :: NFA tok
    empNFA = MkNFA 0 Set.empty (\_ _ -> Set.empty) Set.empty
    epsNFA = MkNFA 1 (Set.singleton 0) (\_ _ -> Set.empty) (Set.singleton 0)

    shift :: Int -> Set NFAState -> Set NFAState
    shift n = Set.fromAscList . map (+ n) . Set.toAscList


main :: IO ()
main = pure ()
