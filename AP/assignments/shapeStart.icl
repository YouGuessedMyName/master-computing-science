module shapeStart

/*
A starting point for assignment 9 in advanced Programming, May 2023.
Pieter Koopman, Radboud University Nijmegen, The Netherlands. pieter@cs.ru.nl
*/

import StdEnv
import Text => qualified join
import Control.Applicative, Data.Functor, Control.Monad.Fail
from Control.Monad import class Monad(bind,>>=,>>|), class MonadPlus(..)

Start = e_plain

// ===== given ======

e_plain :: Bool
e_plain =
    let p0   = {x=6.0, y=0.0} in
    let p1   = {x=3.0, y=0.0} in
    let disc = Scale 5.0 Circle in
    let lens = disc * (Trans p1 disc) in
    ~ (inside p0 lens) * inside p0 (~ lens)

:: Point = {x :: Real, y :: Real}
:: Shape = Circle | Intersection Shape Shape | Trans Point Shape | Invert Shape | Scale Real Shape

instance +        Point where (+) p q = {x = p.x + q.x, y = p.y + q.y}
instance -        Point where (-) p q = {x = p.x - q.x, y = p.y - q.y}
instance toString Point where toString p = "{x=" <+ p.x <+ ", y=" <+ p.y <+ "}"
instance *        Shape where (*) x y = Intersection x y
instance *        Bool  where (*) x y = x && y
instance ~        Shape where  ~ s = Invert s
instance ~        Bool  where  ~ b = not b

inside :: Point Shape -> Bool
inside point shape
    = case shape of
        Circle           = point.x * point.x + point.y * point.y <= 1.0
        Scale r shape    = inside {x = point.x / r, y = point.y / r} shape
        Trans t shape    = inside (point - t) shape
        Invert  shape    = not (inside point shape)
        Intersection x y = inside point x && inside point y

// ===== dsl =====

// ===== evaluation =====

:: E a = E a

eval :: (E a) -> a
eval (E a) = a

// ===== counting circles =====

// ===== printing =====

:: Print a =: P (PS -> (a, PS))
:: PS       = {i :: Int, out :: [String]}

instance pure      Print where pure a = undef
instance Monad     Print where bind (P f) a = undef
instance Functor   Print where fmap f p = undef
instance <*>       Print where (<*>) f x = undef
instance MonadFail Print where fail s = undef

print :: a -> Print b | toString a
print a = P \s = (undef, {s & out = [toString a: s.out]})

fresh :: Print String
fresh  = P \s = ("v" <+ s.i, {s & i = s.i + 1})

prnt :: (Print a) -> String | toString a
prnt (P f) = "\n" <+ 'Text'.join "" (reverse (snd (f {i=0, out=[]})).out)
