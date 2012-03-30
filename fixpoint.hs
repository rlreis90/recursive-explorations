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
             UndecidableInstances,
             TypeSynonymInstances,
             TypeOperators #-}

module Fixpoint where
import Prelude hiding (succ,repeat,head,tail,iterate,map,Monad,(>>=)) 

--General helpers
case_maybe f z m = case m of Nothing -> z; Just x -> f x
push x k = k x

map_right f (a, b) = (a, f b)
map_left f (a, b) = (f a, b)
fork x = (x, x)
--Hel


--Category theory basics
class Applicative f where
  ap :: f (a -> b) -> f a -> f b

class Category hom where
  idt :: hom a a
  (°) :: hom b c -> hom a b -> hom a c

class (Category hom, Category hom') => Functor' hom hom' f where
  map :: hom a b -> hom' (f a) (f b)

instance Functor f => Functor' (->) (->) f where
  map = fmap

class (Category i, Functor' i i w) => Comonad i w where
  extract :: i (w a) a
  duplicate :: i (w a) (w (w a))
  
class (Category i, Functor' i i m) => Monad i m where
  unit ::  i a (m a)
  join :: i (m (m a)) (m a) 

extend f = map f ° duplicate
bind f = join ° map f

m =>> f = extend f m
m >>= f = bind f m
	
instance Category (->) where
  idt = id
  f ° g = f . g

instance Functor ((->) a) where
  fmap f g = f . g

data Hask a b = Hask {unHask::a -> b}

data Op h a b = Op {unOp :: h b a}

instance Category h => Category (Op h) where
  idt = Op idt
  f ° g = Op (unOp g ° unOp f)

class (Functor' i i f) => Initial i f t where
  fold :: i (f x) x -> i (t f) x

class (Functor' i i f) => Terminal i f t where
  unfold_ :: i x (f x) -> i x t

instance Functor f => Initial (->) f Least where
  fold f (Least k) = k f

--Isomorphism stuff
data Category h => Iso h a b = Iso { to :: h a b, from :: h b a }
(<->) = Iso
inverse (Iso to from) = Iso from to

map_right_iso (Iso f g) = Iso (map_right f) (map_right g)

instance Category i => Category (Iso i) where
  idt = Iso idt idt
  Iso f f' ° Iso g g' = Iso (f ° g) (g' ° f')

instance (Functor' i j f) => Functor' (Iso i) (Iso j) f where
  map (Iso f f') = Iso (map f) (map f')



data (Category i, Functor' i i f) => Least' i f = Least' (forall x. i (i (f x) x) x)



class Category k => Fixpoint' fix k where
  fixpoint' :: (Functor f) => Iso k (f (fix f)) (fix f)

instance Fixpoint' (Least' (->)) (->) where
  fixpoint' = (\s -> Least' $ \alg -> (alg . fmap (fold' alg)) s)  <->  fold' (fmap $ to fixpoint')

fold' f (Least' k) = k f



class Category k => Fixpoint fix k where
  fixpoint :: (Functor f) => Iso k (f (fix f)) (fix f)


data Functor f => Least f = Least (forall x. (f x -> x) -> x)

instance Fixpoint Least (->) where
  fixpoint = (\s -> Least $ \alg -> (alg . fmap (fold alg)) s)  <->  fold (fmap $ to fixpoint)

--data Greatest f where
--    Greatest :: Functor f => (x -> f x, x) -> Greatest f
data Functor f => Greatest f = forall x. Greatest (x -> f x, x)
unfold = curry Greatest


instance Fixpoint Greatest (->) where
  fixpoint = unfold (fmap $ from fixpoint)  <->  \(Greatest (coalg, x)) -> fmap (unfold coalg) (coalg x)

--injective := domain = coimage
--surjective := codomain = image

--Natural numbers
newtype Nat = Nat {unNat::Least Maybe}

nat = nat ° fixpoint ° map (inverse nat)
      where nat = Nat <-> unNat

zero = to nat Nothing
succ = to nat . Just

fold_nat f = fold f . unNat
case_nat f x = fold_nat (case_maybe f x)

-- newtype Fixpoint f (->) => Nat' = Nat' {unNat'::f Maybe}
-- nat_const = Nat' <-> unNat'

-- nat' = nat_const ° fixpoint ° map (inverse nat_const)

-- zero' = to nat' Nothing
-- succ' = to nat' . Just

-- fold_nat' f = fold f . from nat_const
-- case_nat' f x = fold_nat (case_maybe f x)


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
newtype Sumprod a b = Sumprod {unSumprod::Maybe (a, b)} deriving (Functor, Show)
sumprod = Sumprod <-> unSumprod

newtype List a = List {unList::Least(Sumprod a)}

list = list ° fixpoint ° sumprod ° map (map_right_iso (inverse list))
       where list = List <-> unList

nil  = to list Nothing
cons = to list . Just

case_list f x = fold (case_maybe f x . unSumprod) . unList
fold_list f = fold (f . unSumprod) . unList

instance Show a => Show (List a) where
  show xs = "[" ++ case_list (\(x, s) -> show x ++ if s == "" then s else ", " ++ s) "" xs ++ "]"

instance Functor List where
  fmap f = case_list (uncurry $ curry cons . f) nil

-- instance Initial (->) (Sumprod a) Least where
  -- fold f = fold (f . unSumprod) . unList

append (xs, ys) = case_list cons ys xs
xs +++ ys = append (xs, ys)

instance Monad (->) List where
  unit x = cons (x, nil)
  join = case_list append nil

newtype List' f a = List' {unList'::f(Sumprod a)}
list_const = List' <-> unList'

-- colist = colist ° fixpoint ° sumprod ° map (map_right_iso (inverse colist))
         -- where colist = CoList <-> unCoList

list' = list_const ° fixpoint ° sumprod ° map (map_right_iso (inverse list_const))

nil' = to list' Nothing
cons' = to list' ° Just

unfold_list f = to list_const ° unfold (to sumprod ° f)
fold_list' f = fold' (f ° from sumprod) ° from list_const

-- instance Functor (CoList f) where
  -- fmap f = unfold_colist $ (fmap (map_left f)) . from colist

-- instance Applicative CoList where
  -- ap = curry $ unfold_colist (\(xs, ys) -> (head xs (head ys), (tail xs, tail ys)))

-- instance Monad (->) CoList where
  -- unit x = cocons (x, conil)
  -- join = tails

--Stream
newtype Pair a b = Pair {unPair::(a, b)} deriving (Functor, Show)
newtype Stream a = Stream {unStream :: Greatest (Pair a)}

stream = stream ° fixpoint ° map (inverse stream) ° pair
         where pair   = Pair <-> unPair
               stream = Stream <-> unStream

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

instance Comonad (->) Stream where
  extract   = head
  duplicate = tails
  
--sequenceS (Stream (x, xs)) = do y  <- x
--                                ys <- sequenceS xs
--                                return $ Stream (y, ys)

-- sequenceS :: Monad m => Stream (m a) -> m (Stream a)
-- sequenceS (Stream (Greatest (f, x))) = let (Pair (a, b)) = f x in do y <- a; ys <- sequenceS b; return $ Stream (legacyTo legacyFixpoint (Pair (y, un_stream ys)))

-- partition :: (a -> Bool) -> List a -> (List a, List a)
-- partition p = case_list (\(v, (xs, ys)) -> if p v then (cons (v, xs), ys) else (xs, cons (v, ys))) (nil, nil)
-- quicksort p = case_list (\(x, xs) -> let (xs, ys) = partition (p x) xs in quicksort p xs +++ unit x +++ quicksort p ys) nil
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


mapB f (a, b) = (f a, f b)

merge_sort k [] = []
merge_sort k [x] = [x]
merge_sort k xs = uncurry (merge k) $ mapB (merge_sort k) $ split xs
    where
      split xs = splitAt (floor (toRational (length xs) / toRational  2)) xs
      merge pred xs []         = xs
      merge pred [] ys         = ys
      merge pred (x:xs) (y:ys) | pred x y  = x: merge pred xs (y:ys)
                               | otherwise = y: merge pred (x:xs) ys
								
mergesort :: (a -> a -> Bool) -> [a] -> [a]
mergesort pred []   = []
mergesort pred [x]  = [x]
mergesort pred xs = merge pred (mergesort pred xs1) (mergesort pred xs2)
  where
    (xs1,xs2) = split xs
    split xs = splitAt (floor (toRational (length xs) / toRational  2)) xs
	
merge pred xs []         = xs
merge pred [] ys         = ys
merge pred (x:xs) (y:ys) | pred x y  = x: merge pred xs (y:ys)
                         | otherwise = y: merge pred (x:xs) ys


fromList (x:xs) = cons(x, fromList xs) 
fromList [] = nil

-- merge' l r = case from list l of
               -- Just (x,xs) ->
                   -- case from list r of
                      -- Just (y,ys) -> if x < y then common x y xs ys else common y x ys xs
                      -- Nothing     -> l
               -- Nothing     -> r
               -- where common l r ls rs = cons (l, merge' ls (cons (r, rs)))

-- merge'' xs ys = case_list (\(y, xs') -> ) xs ys

type (:+:) = Either

bool b = if b then Left () else Right ()

bimap f x = case x of Left a -> f a; Right b -> f b

partition :: Functor' (->) h f => (a -> Bool) -> h (f a) (f (a :+: a))
partition p = map (\v -> if p v then Left v else Right v)