module BtreeMonad where

data Btree a = Tip a | Bin (Btree a) (Btree a)
  deriving Show

instance Functor Btree where
  fmap :: (a -> b) -> Btree a -> Btree b
  fmap f (Tip x)   = Tip (f x)
  fmap f (Bin l r) = Bin (fmap f l) (fmap f r)

instance Applicative Btree where
  pure :: a -> Btree a
  pure = Tip
  (<*>) :: Btree (a -> b) -> Btree a -> Btree b
  (Tip f) <*> tx = fmap f tx
  (Bin l r) <*> (Bin l' r') = Bin (l <*> l') (r <*> r')
  (Bin l r) <*> tx = l <*> tx -- Choose left function if tree is exhausted but not function tree.

instance Monad Btree where
  return :: a -> Btree a
  return = pure
  (>>=) :: Btree a -> (a -> Btree b) -> Btree b
  (Tip x) >>= f = f x
  (Bin l r) >>= f = Bin (l >>= f) (r >>= f)

  

  

