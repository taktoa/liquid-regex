{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--full" @-}
module Main where

import           GHC.Generics (Generic)

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

{-
data Regex tok
  = Ø
  | Ɛ
  | Tok   tok
  | Comp  (Regex tok)
  | Star  (Regex tok)
  | (:|:) (Regex tok) (Regex tok)
  | (:&:) (Regex tok) (Regex tok)
  | (:.:) (Regex tok) (Regex tok)
-}

{-@ measure ratomic @-}
ratomic :: Regex tok -> Bool
ratomic Ø           = True
ratomic Ɛ           = True
ratomic (Tok t)     = True
ratomic (Star r)    = False
ratomic (Comp r)    = False
ratomic ((:.:) r s) = False
ratomic ((:|:) r s) = False
ratomic ((:&:) r s) = False


{-@ inline maxInt @-}
maxInt :: Int -> Int -> Int
maxInt x y = if x > y then x else y

-- -- rsize :: rx:(Regex tok) -> {v : Int | (v >= 0) && (not (ratomic rx) => (v > 0))}
-- {-@ measure rsize @-}
-- {-@ rsize :: rx:(Regex tok) -> {v : Int | (v >= 0) && (v = rsize rx)} @-}
-- rsize :: Regex tok -> Int
-- rsize Ø           = 0
-- rsize Ɛ           = 0
-- rsize (Tok _)     = 0
-- rsize (Star r)    = 1 + rsize r
-- rsize (Comp r)    = 1 + rsize r
-- rsize ((:.:) r s) = 1 + maxInt (rsize r) (rsize s)
-- rsize ((:|:) r s) = 1 + maxInt (rsize r) (rsize s)
-- rsize ((:&:) r s) = 1 + maxInt (rsize r) (rsize s)

{-@ type RegexN tok n = {rx : Regex tok | (n >= rsize rx)} @-}

{-@ measure isNullable @-}
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

{-@ axiomatize isEmpty @-}
isEmpty Ø = True
isEmpty r = False

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


-- {-@ deriv' :: n:Nat -> tok -> RegexN tok n -> Regex tok @-}
-- deriv' :: (Eq tok) => Int -> tok -> Regex tok -> Regex tok
-- deriv' n a = if n > 0 then go n a else id
--   where
--     go n a Ø         = Ø
--     go n a Ɛ         = Ø
--     go n a (Tok t)   = if t == a then Ɛ else Ø
--     go n a (Comp r)  = Comp (deriv' (n - 1) a r)
--     go n a (Star r)  = deriv' (n - 1) a r :.: Star r
--     go n a (r :|: s) = deriv' (n - 1) a r :|: deriv' (n - 1) a s
--     go n a (r :&: s) = deriv' (n - 1) a r :&: deriv' (n - 1) a s
--     go n a (r :.: s) = let d1 = deriv' (n - 1) a r
--                            d2 = deriv' (n - 1) a s
--                        in if isNullable r
--                           then (d1 :.: s) :|: d2
--                           else d1 :.: s
--
-- -- | The Brzozowski derivative of a regular expression with respect to a token.
-- deriv :: (Eq tok) => tok -> Regex tok -> Regex tok
-- deriv a rx = deriv' (succ (rsize rx)) a rx

-- | The Brzozowski derivative of a regular expression with respect to a string.
derivative :: (Eq tok, Foldable t) => t tok -> Regex tok -> Regex tok
derivative tokens rx = foldr deriv rx tokens

main :: IO ()
main = pure ()
