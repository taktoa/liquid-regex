{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- LIQUID "--fullcheck" -}
module Main where

import           GHC.Generics (Generic)
-- import           ProofCombinators

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
isNullable Ø           = False
isNullable Ɛ           = True
isNullable (Tok _)     = False
isNullable (Comp r)    = not (isNullable r)
isNullable (Star r)    = True
isNullable ((:|:) r s) = isNullable r || isNullable s
isNullable ((:&:) r s) = isNullable r && isNullable s
isNullable ((:.:) r s) = isNullable r && isNullable s

-- | Returns Ɛ if the language of the given regular expression contains Ɛ, and
--   otherwise returns Ø.
nullable :: Regex tok -> Regex tok
nullable r = if isNullable r then Ɛ else Ø

{-@ type Fin n a = {xs : [a] | ((len xs) <= k)} @-}

{-@ assume splitAt
    :: forall a. k:Nat
    -> xs:(Fin k a)
    -> {p : ([a], [a]) | (k = (len (fst p)))
                         && ((len xs) = (len (fst p) + len (snd p)))} @-}

{- inline myAny -}
myAny :: (a -> Bool) -> [a] -> Bool
myAny _ []     = False
myAny f (x:xs) = f x || myAny f xs

-- {- range :: lower:Int -> upper:Int -> [{x : Int | (lower <= x) && (x <= upper)}] -}
-- range :: Int -> Int -> [Int]
-- range = \lower upper -> reverse (go lower upper)
--   where
--     {- go :: lower:Int -> upper:Int -> [{x : Int | (lower <= x) && (x <= upper)}] / [upper] -}
--     go :: Int -> Int -> [Int]
--     go lower upper = if lower <= upper then [] else upper : go lower (upper - 1)

-- {- axiomatize matches -}
-- {- matches :: [tok] -> rx:(Regex tok) -> Bool / [autolen rx] -}
-- matches :: (Eq tok) => [tok] -> Regex tok -> Bool
-- matches []  Ɛ         = True
-- matches [a] (Tok tok) = tok == a
-- matches str (r :|: s) = matches str r || matches str s
-- matches str (r :&: s) = matches str r && matches str s
-- matches str (r :.: s) = myAny (\(a, b) -> matches a r && matches b s)
--                         $ map (\i -> splitAt i str) [0 .. length str]
-- matches _   _         = False

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

{-
derivWorks
  :: x:tok
  -> xs:[tok]
  -> rx:(Regex tok)
  -> {v : Proof | (Prop (matches (x:xs) rx)) <=> (Prop (matches xs (deriv x rx))) }
-}
-- derivWorks :: tok -> [tok] -> Regex tok -> ()
-- derivWorks x xs rx = trivial *** QED

main :: IO ()
main = pure ()
