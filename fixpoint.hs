{-# LANGUAGE ImpredicativeTypes,
			 RankNTypes,
			 ExistentialQuantification,
			 UnicodeSyntax,
			 NoMonomorphismRestriction,
			 TypeFamilies,
			 DeriveFunctor,
			 GADTs,
			 TupleSections,
			 ScopedTypeVariables,
             MultiParamTypeClasses,
             FlexibleInstances,
             FlexibleContexts,
			 UndecidableInstances #-}

module Fixpoint where
import Prelude hiding (succ,repeat,head,tail,iterate,map) 

case_maybe f z m = case m of Nothing -> z; Just x -> f x
push x k = k x

map_right f (a, b) = (a, f b)
map_left f (a, b) = (f a, b)
fork x = (x, x)

extend f = fmap f . duplicate

class Functor w => Comonad w where
  extract :: w a -> a
  duplicate :: w a -> w (w a)

class Applicative f where
  ap :: f (a -> b) -> f a -> f b

instance Functor ((->) a) where
  fmap f g = f . g

-- instance GenFunctor (->) (->) ((->) a) where
  -- map f g = f . g

data Iso a b = Iso { to :: a -> b, from :: b -> a }

data Category h => GenIso h a b = GenIso { gto :: h a b, gfrom :: h b a }

class Canonical a b where iso :: Iso a b

class Category hom where
  idt :: hom a a
  (°) :: hom b c -> hom a b -> hom a c

instance Category (->) where
  idt = id
  f ° g = f . g

instance Category Iso where
  idt = Iso idt idt
  Iso f f' ° Iso g g' = Iso (f ° g) (g' ° f')

class (Category hom, Category hom') => GenFunctor hom hom' f where
  map :: hom a b -> hom' (f a) (f b)

instance Functor f => GenFunctor (->) (->) f where
  map = fmap

instance GenFunctor (->) (->) f => GenFunctor Iso Iso f where
  map (Iso f f') = Iso (map f) (map f')
  
instance Category i => Category (GenIso i) where
  idt = GenIso idt idt
  GenIso f f' ° GenIso g g' = GenIso (f ° g) (g' ° f')

instance (Category i, Category j, GenFunctor i j f) => GenFunctor (GenIso i) (GenIso j) f where
  map (GenIso f f') = GenIso (map f) (map f')

(<->) = GenIso

-- instance Functor f => GenFunctor Iso Iso f where
  -- map (Iso f f') = Iso (fmap f) (fmap f')

inverse (Iso f f') = Iso f' f

class Fixpoint fix where
  fixpoint :: Functor f => Iso (f (fix f)) (fix f)

xxx = (\s -> Least $ \alg -> (alg . fmap (fold alg)) s) <-> fold (fmap $ to fixpoint)
					
instance Fixpoint Least where
  fixpoint = Iso {  to   = \s -> Least $ \alg -> (alg . fmap (fold alg)) s  ,
                    from = fold (fmap $ to fixpoint)                        }

instance Fixpoint Greatest where
  fixpoint = Iso {  from = \(Greatest (coalg, x)) -> fmap (unfold coalg) (coalg x)  ,
                    to   = unfold (fmap $ from fixpoint)                            }

data Functor f => Least f = Least (forall x. (f x -> x) -> x)
-- un_least (Least f) = f
-- fold f = push f . un_least
fold f (Least k) = k f

data Functor f => Greatest f = forall x. Greatest (x -> f x, x)
unfold = curry Greatest

--data Greatest f where
--    Greatest :: Functor f => (x -> f x, x) -> Greatest f

--injective := domain = coimage
--surjective := codomain = image

--Natural numbers
newtype Nat = Nat {unNat::Least Maybe}

nat = nat ° fixpoint ° map (inverse nat)
      where nat = Iso Nat unNat

zero = to nat Nothing
succ = to nat . Just

fold_nat f = fold f . unNat
case_nat f x = fold_nat (case_maybe f x)

-- times :: (b -> a -> a) -> a -> b -> Nat -> a
-- times plus zero m = case_maybe (\n -> m `plus` times plus zero m n)) zero . from nat
-- times plus zero m = case_maybe (plus m) zero . fmap (times plus zero m) . from nat
-- times plus zero m = case_nat (plus m) zero
-- times plus m = case_nat (plus m . Just) (plus m Nothing)
-- times plus m = fold_nat $ plus m
-- times plus = fold_nat . plus

-- times :: Functor f => f (Maybe a -> a) -> f (Nat -> a)
times = fmap fold_nat

-- plus = case_nat succ
plus = times $ case_maybe succ
mult = times $ \m -> case_maybe (plus m) zero
-- mult = times $ flip case_maybe zero . plus

inc :: Int -> Int
inc n = n + 1

nat_to_int = case_nat inc 0
natural x = if x == 0 then zero else succ $ natural (x - 1)

instance Show Nat where
  show = show . nat_to_int

instance Eq Nat where
  m == n = nat_to_int m == nat_to_int n

instance Num Nat where
  fromInteger = natural
  
  (*) = mult
  (+) = plus

  abs = id
  signum = id
  negate x = undefined
  (-) = times $ case_maybe pred where pred = case_maybe id undefined . from nat
				 
--List
newtype Sumprod a b = Sumprod (Maybe (a, b)) deriving (Functor, Show)
un_sumprod (Sumprod m) = m

newtype List a = List (Least (Sumprod a))
un_list (List xs) = xs

instance Show a => Show (List a) where
    show xs = "[" ++ case_list (\(x, s) -> show x ++ ", " ++ s) "[]" xs ++ "]"

instance Functor List where
    fmap f = case_list (uncurry $ curry cons . f) nil

to_list = List . to fixpoint . Sumprod . fmap (map_right un_list)
from_list = fmap (map_right List) . un_sumprod . from fixpoint . un_list

nil  = to_list Nothing
cons = to_list . Just

case_list f x = fold (case_maybe f x . un_sumprod) . un_list

fold_list f = fold (f . un_sumprod) . un_list

append (xs, ys) = case_list cons ys xs
xs +++ ys = append (xs, ys)

unit x = cons (x, nil)
join = case_list append nil

--Stream
newtype Pair a b = Pair {unPair::(a, b)} deriving (Functor, Show)
newtype Stream a = Stream {unStream :: Greatest (Pair a)}

stream = stream ° fixpoint ° map (inverse stream) ° pair
         where pair   = Iso Pair unPair
               stream = Iso Stream unStream

head = fst . from stream
tail = snd . from stream

unfold_stream f = Stream . unfold (Pair . f)

iterate f = unfold_stream (map_right f . fork)
repeat = iterate id
tails  = iterate tail

instance Functor Stream  where
  fmap f = unfold_stream $ (map_left f) . from stream

instance Applicative Stream where
  ap = curry $ unfold_stream (\(xs, ys) -> (head xs (head ys), (tail xs, tail ys)))

instance Comonad Stream where
  extract   = head
  duplicate = tails
  
--sequenceS (Stream (x, xs)) = do y  <- x
--                                ys <- sequenceS xs
--                                return $ Stream (y, ys)

-- sequenceS :: Monad m => Stream (m a) -> m (Stream a)
-- sequenceS (Stream (Greatest (f, x))) = let (Pair (a, b)) = f x in do y <- a; ys <- sequenceS b; return $ Stream (to fixpoint (Pair (y, un_stream ys)))

partition :: (a -> Bool) -> List a -> (List a, List a)
partition p = case_list (\(v, (xs, ys)) -> if p v then (cons (v, xs), ys) else (xs, cons (v, ys))) (nil, nil)
quicksort p = case_list (\(x, xs) -> let (xs, ys) = partition (p x) xs in quicksort p xs +++ unit x +++ quicksort p ys) nil
-- quicksort p = case_list (\(x, xs) -> let (List xs, List ys) = partition (p x) xs
--									   in fold (quicksort p) xs +++ unit x +++ fold (quicksort p) ys) nil

ack = fold_nat k where k Nothing  = succ
                       k (Just f) = fold_nat iter where iter Nothing  = f (succ zero)
                                                        iter (Just n) = f n

-- ack = case_nat iter succ
         -- where iter f = iter f (f (succ zero))
		 
-- ack = case_nat (\f -> case_nat f (f (succ zero))) succ

-- ack' m = case from nat m of
            -- Just m' -> \n -> case from nat n of
                               -- Just n' -> ack' m' (ack' m n')
                               -- Nothing -> ack' m' (succ zero)
            -- Nothing -> succ

ack' m = case_maybe (\m' -> ack' m' . case_maybe (ack' m) (succ zero) . from nat) succ . from nat $ m

ack'' m = case_maybe (\m' -> ack'' m' . case_maybe (ack'' m) (succ zero) . from nat) succ . from nat $ m


ack''' m = case_maybe (uncurry ack'''.) succ . fmap (curry $ map_right $ case_maybe (ack''' m) (succ zero) . from nat) . from nat $ m

-- ack5 m n = case_nat (\m' -> ack5 m' . case_maybe (ack5 m) (succ zero) . from nat) (succ n) m