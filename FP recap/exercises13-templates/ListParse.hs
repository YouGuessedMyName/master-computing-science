{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module ListParse where

import Control.Applicative
import Control.Monad
import Parser

{- grammar:
 -   intList   = "{" { integer } "}"
 -}

intList :: Parser [Int]
-- intList = char '{' *> nat `sepBy` space <* char '}'
intList = do
    char '{' 
    xs <- nat `sepBy` space 
    char '}'
    pure xs


{- grammar:
 -   intRecord = "{" integer "#" { integer } "}"
 -                   ^ =: n      ^^^^^^^^^^^ (repeat n# times)
 -}

intRecord :: Parser [Int]
intRecord = do
    char '{'
    n <- nat
    char '#' 
    xs <- nat `sepBy` space
    if length xs == n then return xs else failure