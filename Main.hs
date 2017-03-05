{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

{-@ LIQUID "--full" @-}
module Main where

import           GHC.Generics (Generic)

-- {-@ type NonEmpty = {v : [a] | 0 < length v } @-}

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

-- | Returns Ɛ if the language of the given regular expression contains Ɛ, and
--   otherwise returns Ø.
nullable :: Regex tok -> Regex tok
nullable = \x -> if go x then Ɛ else Ø
  where
    go :: Regex t -> Bool
    go Ø         = False
    go Ɛ         = True
    go (Tok _)   = False
    go (Comp r)  = not (go r)
    go (Star _)  = True
    go (r :|: s) = go r || go s
    go (r :&: s) = go r && go s
    go (r :.: s) = go r && go s

-- | The Brzozowski derivative of a regular expression with respect to a token.
deriv :: (Eq tok) => tok -> Regex tok -> Regex tok
deriv _ Ø         = Ø
deriv _ Ɛ         = Ø
deriv a (Tok t)   = if t == a then Ɛ else Ø
deriv a (Comp r)  = Comp (deriv a r)
deriv a (Star r)  = deriv a r :.: Star r
deriv a (r :|: s) = deriv a r :|: deriv a s
deriv a (r :&: s) = deriv a r :&: deriv a s
deriv a (r :.: s) = let r' = deriv a r
                        s' = deriv a s
                    in (r' :.: s) :|: (nullable r :.: s')

-- | The Brzozowski derivative of a regular expression with respect to a string.
derivative :: (Eq tok, Foldable t) => t tok -> Regex tok -> Regex tok
derivative tokens rx = foldr deriv rx tokens

main :: IO ()
main = pure ()
