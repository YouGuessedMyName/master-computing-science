module MaybeMonad where

import Data.Functor
import Control.Monad

maybeMap :: (a -> b) -> Maybe a -> Maybe b
maybeMap = fmap
-- maybeMap f ma = f <$> ma
-- maybeMap f ma = ma <&> f
-- maybeMap f ma = ma >>= (return . f)
-- maybeMap f ma = ma >>= (\x -> return (f x))

stripMaybe :: Maybe (Maybe a) -> Maybe a
stripMaybe ma = join ma
-- stripMaybe ma = ma >>= id

applyMaybe:: (a -> Maybe b) -> Maybe a -> Maybe b
applyMaybe ma f = f >>= ma

-- applyMaybe = maybe Nothing
-- applyMaybe f = maybe Nothing f
-- applyMaybe f ma = maybe Nothing f ma
-- applyMaybe f ma = case ma of
    -- Nothing -> Nothing
    -- Just x -> f x
