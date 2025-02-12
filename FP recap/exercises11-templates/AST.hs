module AST where

-- this template uses infix constructors; feel free to use AST2.hs (which uses prefix ones) if you prefer
-- (if you really liked your own solution to Exercise 4.7, you can use that as well)

type Identifier = String

data Expr = Lit Integer | Var Identifier | Expr :+: Expr | Expr :-: Expr | Expr :*: Expr | Expr :/: Expr
  deriving (Show)

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


infixl 6 :+: 
infixl 6 :-: 
infixl 7 :/:
infixl 7 :*:

eval :: (Fractional a, Eq a) => Expr -> [(Identifier,a)] -> Result a 
eval (Lit k) vars = pure (fromInteger k)
eval (x :+: y) vars = (+) <$> eval x vars <*> eval y vars
eval (x :-: y) vars = (-) <$> eval x vars <*> eval y vars
eval (x :*: y) vars = (*) <$> eval x vars <*> eval y vars
eval (x :/: y) vars = (/) <$> eval x vars <*> eval y vars
eval (Var name) vars = case lookup name vars of
  Nothing -> Error ["unknown variable: " ++ name]
  Just x -> Okay x
  
  