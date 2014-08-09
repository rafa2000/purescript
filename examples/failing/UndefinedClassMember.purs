module Main where

class Size f where
  fold :: forall a r. (r -> a -> r) -> r -> f a -> r
  size :: forall a. f a -> Number

data One a = One a

instance sizeOne :: Size One where
  fold f r (One a) = f r a
  size x = fold (\n _ -> n + 1) 0 x
