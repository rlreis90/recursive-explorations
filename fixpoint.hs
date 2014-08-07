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
             TypeOperators,
             LiberalTypeSynonyms,
             ScopedTypeVariables,
             PolyKinds,
             FunctionalDependencies,
             LambdaCase             #-}

module Fixpoint where
import Prelude hiding (succ,repeat,head,tail,iterate,map,Monad,(>>=),(.),id, fst, snd) 

case_maybe f z m = case m of Nothing -> z; Just x -> f x
push x k = k x

map_right f (a, b) = (a, f b)
map_left f (a, b) = (f a, b)

data Top = forall c. TT c
data Bottom = FF (forall c. c)

truth c = TT c
falsehood (FF c) = c

-- type a :<->: b = ((a -> b) :&: (b -> a))
-- un :: (a :<->: b) -> (b :<->: a)
-- un x = snd x `sup` fst x
-- app :: (a :<->: b) -> (a -> b)
-- app = fst

-- p .:. q = q . p

type Not a = a -> Bottom
newtype a :&&: b = Sup' (Not (Not a :+: Not b))

dni :: a -> Not (Not a)
dni a = \k -> k a
-- dne :: Not (Not a) -> a
-- dne C[k] = k C

fst'' :: (a :&&: b) -> Not (Not a)
fst'' (Sup' k)  = \f -> k (Left f)
snd'' :: (a :&&: b) -> Not (Not b)
snd'' (Sup' k)  = \f -> k (Right f)

data a :&: b = Sup (forall c. ((a -> c) :+: (b -> c)) -> c)

class Monoid i or o z m | o -> z, z -> o where
  mult :: i (z `or` (m `o` m)) m

  
a `sup` b = Sup (\case Left k -> k a ; Right k -> k b)

class Prod i and where
  fst :: i (a `and` b) a
  snd :: i (a `and` b) b
  fuse :: (i a b `and` i a c) -> i a (b `and` c)

instance Prod (->) (:&:) where
  fst (Sup k) = k (Left id)
  snd (Sup k) = k (Right id)
  fuse        = \f x -> fst f x `sup` snd f x

class CoMonoid i and o z w
  | o -> z, z -> o
  , and -> i, i -> and
  where
  comult :: i w (z `and` (w `o` w))
  
-- create = mult . Left
-- merge = mult . Right
-- erase :: (Category i, CoMonoid i and op z w, Prod i and) => i w z
erase = fst . comult
copy  = snd . comult

instance CoMonoid (->) (:&:) (,) () w where
  comult x = () `sup` (x, x)

instance CoMonoid (->) (:&:) (:&:) Top w where
  comult x = truth x `sup` (x `sup` x)


newtype Trans i f g = Trans (forall a. i (f a) (g a))
newtype Compose f g a = Compose (f (g a))
newtype Identity x  = Identity x
newtype Product f g a = Product (f a :&: g a)

class (Functor w, CoMonoid (Trans (->)) Product Compose Identity w) => CoMonad w
instance (Functor w, CoMonoid (Trans (->)) Product Compose Identity w) => CoMonad w


--Category theory basics
class Applicative f where
  ap :: f (a -> b) -> f a -> f b

class Category hom where
  id :: hom a a
  (.) :: hom b c -> hom a b -> hom a c

class (Category hom, Category hom') => Functor' hom hom' f where
  map :: hom a b -> hom' (f a) (f b)

instance Functor f => Functor' (->) (->) f where
  map = fmap

class (Category i, Endofunctor i w) => Comonad i w where
  extract :: i (w a) a
  duplicate :: i (w a) (w (w a))
  
class (Category i, Functor' i i m) => Monad i m where
  unit ::  i a (m a)
  join :: i (m (m a)) (m a) 

extend f = map f . duplicate
bind f = join . map f

-- m =>> f = extend f m
-- m >>= f = bind f m
	
instance Category (->) where
  id = id
  f . g = f . g

data Hask a b = Hask {unHask::a -> b}

data Op h a b = Op {unOp :: h b a}

instance Category h => Category (Op h) where
  id = Op id
  f . g = Op (unOp g . unOp f)

class (Functor' i i f) => Initial i f t where
  fold :: i (f x) x -> i (t f) x

class (Functor' i i f) => Terminal i f t where
  unfold_ :: i x (f x) -> i x (t f)

instance Functor f => Initial (->) f Least where
  fold f (Least k) = k f

--Isomorphism stuff
data Iso h a b = Iso (h a b :&: h b a)

sym (Iso x) = Iso (swap x)

f <-> g = Iso (f `sup` g)

from (Iso x) = snd x
to (Iso x) = fst x
swap x = snd x `sup` fst x

map_right_iso (Iso x) = Iso (map_right (fst x) `sup` map_right (snd x))

instance Category i => Category (Iso i) where
  id = Iso (id `sup` id)
  Iso f . Iso g = Iso ((fst f . fst g) `sup` (snd g . snd f))

instance (Functor' i j f) => Functor' (Iso i) (Iso j) f where
  map (Iso f) = Iso (map (fst f) `sup` map (snd f))

class Functor' i i f => Endofunctor i f

instance Functor' i i f => Endofunctor i f


-- data (Category (>->), Functor' (>->) (>->) f) => Least' (>->) f = Least' (forall x. (f x >-> x) >-> x)
data Least' i f = Least' (forall x. i (i (f x) x) x)

class Category k => Fixpoint' fix k where
  roll' :: (Functor f) => Iso k (f (fix f)) (fix f)

instance Fixpoint' (Least' (->)) (->) where
  roll' = (\s -> Least' $ \alg -> (alg . fmap (fold' alg)) s) <-> fold' (fmap $ to roll')

fold' :: (f x -> x) -> Least' (->) f -> x
fold' f (Least' k) = k f

unfold = curry Greatest


class Category i => Fixpoint i fix where
  roll :: (Functor f) => Iso i (f (fix f)) (fix f)

data Least f = Least (forall x. (f x -> x) -> x)

--data Greatest f where
--    Greatest :: Functor f => (x -> f x, x) -> Greatest f
data Greatest f = forall x. Greatest (x -> f x, x)

instance Fixpoint (->) Least where
  roll = (\s -> Least $ (\alg -> (alg . fmap (fold alg)) s)) <->  fold (fmap $ to roll)

instance Fixpoint (->) Greatest where
  roll = unfold (fmap $ from roll)  <->  \(Greatest (coalg, x)) -> fmap (unfold coalg) (coalg x)


--Natural numbers
newtype Nat = Nat { unNat :: Least Maybe }

nat = trans (Nat <-> unNat)

trans nat = nat . roll . map (sym nat)

zero = to nat Nothing
succ = to nat . Just

fold_nat f = fold f . unNat
case_nat f x = fold_nat (case_maybe f x)

p :: Iso (->) (Nat -> a) (Stream a)
p = Iso ((\f -> fmap f (iterate succ zero)) `sup` (flip (case_nat (\f -> f . tail) head)))

-- newtype Fixpoint f (->) => Nat' = Nat' {unNat'::f Maybe}
-- nat_const = Nat' <-> unNat'

-- nat' = nat_const . roll . map (sym nat_const)

-- zero' = to nat' Nothing
-- succ' = to nat' . Just

-- fold_nat' f = fold f . from nat_const
-- case_nat' f x = fold_nat (case_maybe f x)


-- over :: (b -> a -> a) -> a -> b -> Nat -> a
-- over plus zero m = case_maybe (\n -> m `plus` over plus zero m n)) zero . from nat
-- over plus zero m = case_maybe (plus m) zero . fmap (over plus zero m) . from nat
-- over plus zero m = case_nat (plus m) zero
-- over plus m = case_nat (plus m . Just) (plus m Nothing)
-- over plus m = fold_nat $ plus m
-- over plus = fold_nat . plus

-- over :: Functor f => f (Maybe a -> a) -> f (Nat -> a)
over = fmap fold_nat

-- plus = case_nat succ
plus = over $ case_maybe succ
-- minus = over $ case_maybe pred where pred = case_maybe Just Nothing . from nat
multiply = over $ \m -> case_maybe (plus m) zero
-- mult = over $ flip case_maybe zero . plus



inc :: Int -> Int
inc n = n + 1

nat_to_int = case_nat inc 0
natural x = if x == 0 then zero else succ $ natural (x - 1)

case_pred f z = case_maybe f z . from nat

instance Show Nat where
  show = show . nat_to_int

instance Eq Nat where
  -- m == n = nat_to_int m == nat_to_int n
  (==) = case_nat (\p -> case_pred p False) (case_pred (const False) True)

instance Ord Nat where
  (>) = case_nat (\p -> case_pred p True) $ const False

instance Num Nat where
  fromInteger = natural

  (*) = multiply
  (+) = plus

  abs = id
  signum = id
  negate x = undefined
  (-) = over $ case_maybe pred where pred = case_maybe id undefined . from nat

--List
newtype Sumprod a b = Sumprod { unSumprod :: Maybe (a, b) } deriving (Functor, Show)
sumprod = Sumprod <-> unSumprod

newtype List a = List { unList :: Least (Sumprod a) }

list = list . roll . sumprod . map (map_right_iso (sym list))
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
  join   = case_list append nil

newtype List' f a = List' { unList':: f (Sumprod a) }
list_const = List' <-> unList'

-- colist = colist . roll . sumprod . map (map_right_iso (sym colist))
         -- where colist = CoList <-> unCoList

list' = list_const . roll . sumprod . map (map_right_iso (sym list_const))

nil'  = to list' Nothing
cons' = to list' . Just

unfold_list f = to list_const . unfold (to sumprod . f)
fold_list' f = fold' (f . from sumprod) . from list_const

-- instance Functor (CoList f) where
  -- fmap f = unfold_colist $ (fmap (map_left f)) . from colist

-- instance Applicative CoList where
  -- ap = curry $ unfold_colist (\(xs, ys) -> (head xs (head ys), (tail xs, tail ys)))

-- instance Monad (->) CoList where
  -- unit x = cocons (x, conil)
  -- join = tails

--Stream
newtype Pair a b = Pair { unPair :: (a :&: b) }
newtype Stream a = Stream { unStream :: Greatest (Pair a) }


instance Functor ((:&:) b) where
  fmap f x = fst x `sup` f (snd x)

instance Functor (Pair a) where
  fmap f (Pair x) = Pair (fmap f x)

stream = trans (Stream <-> unStream) . pair
         where pair   = Pair <-> unPair

head = fst . from stream
tail = snd . from stream

type CoAlgebra i f x = i x (f x)

unfold_stream :: (b -> (a :&: b)) -> b -> Stream a
unfold_stream f = Stream . unfold (Pair . f)

-- iterate :: CoMonoid (->) (,) () t => (t -> t) -> CoAlgebra Stream t
iterate f = unfold_stream (fmap f . copy)
repeat = iterate id
tails  = iterate tail

-- iso <: x = to iso x

-- recursor :: (Functor f) => (f (a :&: Least f) -> a) -> Least f -> (a :&: Least f)
recursor g = fold (fuse (g `sup` (to roll . fmap snd)))

instance Functor Stream  where
  fmap f = unfold_stream $ (swap . fmap f . swap) . from stream

-- instance Applicative Stream where
  -- ap = unfold_stream (\xs -> (head (fst xs) (head (snd xs)) `sup` (tail (fst xs), tail (snd xs))))

-- instance Comonad (->) Stream where
  -- extract   = head
  -- duplicate = tails
  
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

--type Lens b a = a :<->: (forall x. x, b)

newtype Store b a = Store (b, (b -> a))

-- trans = (Trans, (\(Trans p) -> p))

-- store = (Store, (\(Store p) -> p)) 

-- instance Functor (Store b) where
  -- fmap f = app store . fmap (fmap f) . app (un store)

-- instance CoMonoid (Trans (->)) Compose Identity (Store b) where
  -- comult = Trans (app (un store) .:. \(x, f) -> (Identity (f x), Compose (store <: (x, (\y -> store <: (y, f))))))

-- newtype Lens i b a = Lens (CoAlgebra i (Store b) a)

-- x |> f = f x

-- instance Category (Lens (->)) where
  -- id                  = Lens (\x -> store <: (x, id))
  -- (Lens f) . (Lens g) = Lens (\x -> let (y, fk) = un store <: f x in
                                    -- fmap fk (g y))

-- -- ahn :: CoMonad (Store x) => (Lens (->) b c) -> Lens (->) a b -> Lens (->) a c
-- ahn (Lens f) (Lens g) = Lens (\x -> (un store <: f x) |> \(y, k) -> erase (store <: (g y, fmap k)))