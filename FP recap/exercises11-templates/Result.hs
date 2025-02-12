{-# LANGUAGE InstanceSigs #-}
module Result where

import Data.List

data Result a = Okay a | Error [String]
  deriving (Eq,Ord,Show)

instance Functor Result where
  fmap :: (a -> b) -> Result a -> Result b
  fmap f (Okay x) = Okay (f x)
  fmap _ (Error es) = Error es

instance Applicative Result where
  (<*>) :: Result (a -> b) -> Result a -> Result b
  (Okay f) <*> (Okay x) = Okay (f x)
  Error es <*> (Okay _) = Error es
  (Okay _) <*> (Error es) = Error es
  Error es1 <*> (Error es2) = Error (es1 ++ es2)
  pure = Okay
