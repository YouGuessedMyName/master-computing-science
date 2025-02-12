module FindDefs where

(?$) :: Maybe (a -> b) -> Maybe a -> Maybe b
Nothing ?$ _ = Nothing
Just _ ?$ Nothing = Nothing
Just f ?$ Just x = Just (f x)

pair :: (Applicative f) => f a -> f b -> f (a,b)
pair x y = (,) <$> x <*> y

apply :: [a -> b] -> a -> [b]
-- apply [] _ = []
-- apply (f:fs) x = f x : apply fs x
apply fs x = fs <*> pure x

apply2nd :: [a -> b -> c] -> b -> [a -> c]
apply2nd fs x = flip <$> fs <*> pure x
