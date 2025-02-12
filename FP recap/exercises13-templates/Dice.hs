module Dice where
import RandomState
import RandomGen
--import LCH
import Control.Monad
import Control.Applicative
import Data.List

data Expr = Lit Int | Dice Int 
          | Expr :+: Expr | Expr :-: Expr | Expr :/: Int
          | Min Expr Expr | Max Expr Expr
  deriving (Show)

infixl 6 :+: 
infixl 7 :-:
infixl 8 :/:

type DiceAction m = Int -> m Int

{--evalM :: Expr -> DiceAction IO -> IO Int             -- prototype
evalM (Lit n) _ = pure n

evalM (Dice n) d = do
  int1 <- d n
  pure(int1)

evalM (e1 :+: e2) d = do 
  int1 <- (evalM e1 d)
  int2 <- (evalM e2 d)
  pure (int1 + int2)

evalM (Min e1 e2) d = do
  int1 <- (evalM e1 d)
  int2 <- (evalM e2 d)
  if int1 < int2 then
    pure(int1)
  else do
    pure(int2)

evalM (Max e1 e2) d = do
  int1 <- (evalM e1 d)
  int2 <- (evalM e2 d)
  if int1 > int2 then
    pure(int1)
  else do
    pure(int2)--}
{-
evalM :: (Monad m) => Expr -> DiceAction m -> m Int  -- final version
evalM (Lit n) _ = pure n
evalM (Dice n) diceaction = (pure n) >>= diceaction
evalM (e1 :+: e2) d = (+) <$> (evalM e1 d) <*> (evalM e2 d) 
evalM (e1 :-: e2) d = (-) <$> (evalM e1 d) <*> (evalM e2 d) 
evalM (e1 :/: e2) d = (div) <$> (pure(fromIntegral) <*> (evalM e1 d)) <*> (pure(fromIntegral) <*> (evalM e2 d))
evalM (Min e1 e2) d = min <$> (evalM e1 d) <*> (evalM e2 d)
evalM (Max e1 e2) d = max <$> (evalM e1 d) <*> (evalM e2 d)


evalRIO :: Expr -> IO Int
evalRIO expr = evalM expr (\dice->randomRIO (1,dice) >>= return) -- silent version
--evalRIO expr = evalM expr (\dice->randomRIO (1,dice) >>= report) -- verbose version
--  where report x = do { putStr "rolled a "; print x; return x }

readInt:: Int -> IO Int
readInt max = do 
  text <- getLine

  if (read text::Int) <= max then
    pure(read text::Int)
  else
    pure(max)


evalIO :: Expr -> IO Int
evalIO expr = evalM expr (\dice -> readInt dice)

evalND :: Expr -> [Int]
evalND expr = evalM expr (\dice -> [1 .. dice])

avg :: (Fractional a) => [Int] -> a
avg xs = fromIntegral (sum xs) / fromIntegral (length xs)

expectation :: (Fractional a) => Expr -> a
expectation e = avg (evalND e)

--evalR :: Expr -> RandomState Int

helper :: Int -> Int -> Expr -> IO Int
helper n t e = do
  x <- evalRIO e
  if n == 1 then
    pure (t + x)
  else
    helper (n-1) (t+x) e
  

observed :: (Fractional a) => Int -> Expr -> IO a
observed n e = do
  total <- (helper n 0 e)
  pure((fromIntegral total) / (fromIntegral n))
-}