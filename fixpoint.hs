{-# LANGUAGE ImpredicativeTypes, RankNTypes, ExistentialQuantification, UnicodeSyntax, NoMonomorphismRestriction, TypeFamilies, DeriveFunctor, GADTs, TupleSections #-}

module Fixpoint where
import Prelude hiding (succ,repeat,head,tail) 

maybe_alg f z m = case m of Nothing -> z; Just x -> f x
push x k = k x

type Algebra f a = f a -> a

data Functor f => Least f = Least (forall x. (f x -> x) -> x)
unLeast (Least f) = f 

fold f = push f . unLeast

iin = \s -> Least $ \alg -> (alg . fmap (fold alg)) s
iout = fold (fmap iin)

--injective := domain = coimage
--surjective := codomain = image
--leastmap :: forall a b. (a -> b) -> (Least f) a -> (Least f) b

--data Greatest f where
--    Greatest :: Functor f => (x -> f x, x) -> Greatest f

data Functor f => Greatest f = forall x. Greatest (x -> f x, x)
unfold = curry Greatest

tout t = case t of Greatest (coalg, x) -> fmap (unfold coalg) (coalg x)
tin = unfold (fmap tout)


newtype Nat = Nat (Least Maybe)
unNat (Nat n) = n

natin = Nat . iin
natout = iout . unNat

zero = natin Nothing
succ = natin . Just . unNat

natfold :: (Maybe a -> a) -> Nat -> a
natfold  f   = fold f . unNat

natfold' :: (a -> a) -> a -> Nat -> a
natfold' f x = natfold (maybe_alg f x)

instance Show Nat where
  show = natfold' ("S "++) "0" 
	
plus = natfold' succ

mult m = natfold' (plus m) zero

mult' m = natfold' (natfold' succ m) zero

binatfold f x = natfold' (natfold' f x)

mult'' = binatfold succ zero

multy m plus = natfold' (plus m) zero

times :: (b -> a -> a) -> a -> b -> Nat -> a
times plus zero m (Nat x) = case iout x of
                              Just n  -> m `plus` (times plus zero m (Nat n))
                              Nothing -> zero

k :: (b -> a -> a) -> a -> b -> Nat -> a
k f z m  = h . natout
  where h (Just n) = f m (k f z m (Nat n))
        h Nothing  = z

k' :: (b -> a -> a) -> a -> b -> Nat -> a
k' f z m = maybe_alg (\n -> f m (k' f z m (Nat n))) z . natout

k'' :: (Maybe (a, b) -> a) -> b -> Nat -> a
k'' f x = maybe_alg (\n -> f $ Just (k'' f x (Nat n), x)) (f Nothing) . natout

k''' :: (Maybe (a, b) -> a) -> b -> Nat -> a
k''' f z = f . fmap (\x -> (x, z)) . fmap (k''' f z . Nat) . natout

k'''' :: (Maybe (b, a) -> a) -> (b, Nat) -> a
k'''' f = uncurry $ \z -> f . fmap (z,) . fmap (k'''' f . (z,) . Nat) . natout

h :: (b -> Maybe a -> a) -> b -> Nat -> a
h f x = natfold (f x)

-- k''''' :: (Maybe (b, a) -> a) -> (b, Nat) -> a
-- k''''' f = uncurry $ natfold h
           -- where h :: Maybe (b -> a) -> b -> a
                 -- h (Just k) = \b -> f $ Just (k b, b)
                 -- h Nothing  = \_ -> f Nothing


kmult :: Nat -> Nat -> Nat
kmult = k''' (maybe_alg (uncurry plus) zero)
        -- where f (Just (m, n)) = plus m n
              -- f Nothing       = zero

--h :: (b -> a -> a) -> a -> b -> Nat -> a
-- h f x m  = natfold' (\n -> f m (h f x m n)) x

inc :: Int -> Int
inc n = n + 1

nat_to_int :: Nat -> Int
nat_to_int = natfold (maybe_alg inc 0)
							  
instance Eq Nat where
  m == n = nat_to_int m == nat_to_int n

instance Num Nat where
  fromInteger x = if x == 0 then zero else succ $ fromInteger (x - 1)
  
  abs = id
  signum = id

  negate x = undefined
  x - y = undefined
  (*) = mult
  (+) = plus
  
binatfold' f x = natfold (maybe_alg (natfold f) x)

-- binatfold'' alg = natfold (maybe_alg (natfold alg)) (alg Nothing)

-- binatfold''' alg = natfold (\m -> case m of Just x -> (natfold (alg . Just)) x; Nothing -> (alg Nothing))


-- ack = binatfold () (succ zero)

-- fold m
	-- succ m -> fold n
	     -- succ n -> f
		 -- zero -> x
    -- zero -> y

-- ack :: Nat -> Nat -> Nat
-- ack 0 n               = 1
-- ack (succ m) 0        = ack m 1
-- ack (succ m) (succ n) = ack m (ack (succ m) n)

-- ack :: Nat -> Nat -> Nat
-- ack 0  = 1
-- ack m  = 0 	-> (m, 1)
--	      = n   -> (m, (succ m, n))

--ack = natfold' (\m -> iter (ack m)) succ
iter f = natfold' (f . iter f) (succ zero)

iter1 f = natfold' (f . iter1 f)
--iter1' f = fix (\r -> natfold' (f . r))

somef h f = natfold' (h f)
somei = somef (\f -> f . somei f)

somej h f = natfold (maybe_alg (h f) (f Nothing))

iter2 f = natfold (f . fmap (iter2 f))

iter3 f = natfold' (f . Just . iter3 f) (f Nothing)

iter4 f = natfold' f (succ zero)



-- ack 0 = succ
-- ack (m + 1) = iter (ack m)

-- iter f 0 = 1
-- iter f (n + 1) = f (iter f n)


-- ack m n = case m of
			-- 0 	     -> 1
			-- (succ m) -> case n of
							-- 0 		 -> 1
							-- (succ n) -> Least $ \k -> ack m (ack (succ m) n)
							-- (succ n) -> Least $ \k -> ack m (ack (succ m) n)

-- ack = 0, n           -> 1
	  -- succ m, 0      -> 1
	  -- succ m, succ n -> Least $ \k -> ack (m, ack (succ m, n))
					    -- Least $ \k -> ack m (ack (succ m) n)

bifold f x y = fold (\x' -> fold (f x') y) x
   
bifoldin f x y = iin (
                 fold (\x' ->
                 fold (\y' ->
			     f x' y') y) x
                 )
				 
-- ack = bifoldin (\m n -> maybe_alg (\m' -> maybe_alg (\n' -> ) (Just Nothing)) (Just Nothing) m "Nothing | Just")
				 
--List
newtype Sumprod a b = Sumprod (Maybe (a, b)) deriving (Functor, Show)
mapr f (a, b) = (a, f b)
unSumprod (Sumprod m) = m

newtype List a = List (Least (Sumprod a))
unList (List xs) = xs

instance Show a => Show (List a) where
    show xs = "[" ++ foldlist (\(x, s) -> show x ++ ", " ++ s) "[]" xs ++ "]"

instance Functor List where
    fmap f = foldlist (uncurry $ curry cons . f) nil

nil  = List . iin . Sumprod $ Nothing
cons = List. iin . Sumprod . Just . mapr unList


foldlist f x = fold (maybe_alg f x . unSumprod) . unList

foldlist' f = fold (f . unSumprod) . unList

append (xs, ys) = foldlist cons ys xs
xs +++ ys = append (xs, ys)

-- xxx = 

unit x = cons (x, nil)
join = foldlist append nil

partition :: (a -> Bool) -> List a -> (List a, List a)
partition p = foldlist (\(v, (xs, ys)) -> if p v then (cons (v, xs), ys) else (xs, cons (v, ys))) (nil, nil)
quicksort p = foldlist (\(x, xs) -> let (xs, ys) = partition (p x) xs in quicksort p xs +++ unit x +++ quicksort p ys) nil
-- quicksort p = foldlist (\(x, xs) -> let (List xs, List ys) = partition (p x) xs
--									   in fold (quicksort p) xs +++ unit x +++ fold (quicksort p) ys) nil

--Stream
newtype Pair a b = Pair (a, b) deriving (Functor, Show)
unPair (Pair x) = x
newtype Stream a = Stream (Greatest (Pair a))
unStream (Stream p) = p

head = fst . unPair . tout . unStream
tail = Stream . snd . unPair . tout . unStream

  
fork x = (x, x)

--head (Stream (x, xs)) = x
--tail (Stream (x, xs)) = xs

--data Stream a = Stream (a, Stream a)
--repeat x = Stream (x, repeat x)
--sequenceS (Stream (x, xs)) = do y  <- x
--                                ys <- sequenceS xs
--                                return $ Stream (y, ys)

-- sequenceS :: Monad m => Stream (m a) -> m (Stream a)
-- sequenceS (Stream (Greatest (f, x))) = let (Pair (a, b)) = f x in do y <- a; ys <- sequenceS b; return $ Stream (tin (Pair (y, unStream ys)))
