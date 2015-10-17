module demo where

data Bool : Set where
  true : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)

_*_ : Nat -> Nat -> Nat
zero * m = zero
suc n * m = m + (n * m)

_or_ : Bool -> Bool -> Bool
false or x = x
true or _ = true

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true then x else y = x
if false then x else y = y

infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix   5 if_then_else_

infixr 40 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

identity : (A : Set) -> A -> A
identity A x = x

id : {A : Set} -> A -> A
id x = x

map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

head : {A : Set}{n : Nat} -> Vec A (suc n) -> A
head (x :: xs) = x

vmap : {A B : Set}{n : Nat}-> (A -> B) -> Vec A n -> Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: (vmap f xs)

data Image_∍_ {A B : Set} (f : A -> B) : B -> Set where
  im : (x : A) -> Image f ∍ f x

inv : {A B : Set} (f : A -> B) -> (y : B) -> Image f ∍ y -> A
inv f _ (im x) = x

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

_!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
(x :: xs) ! fzero = x
(x :: xs) ! (fsuc i) = xs ! i

data False : Set where
record True : Set where

trivial : True
trivial = _

isTrue : Bool -> Set
isTrue true = True
isTrue false = False

_<_ : Nat -> Nat -> Bool
_ < zero = false
zero < suc n = true
suc m < suc n = m < n

length : {A : Set} -> List A -> Nat
length [] = zero
length (x :: xs) = suc (length xs)

lookup : {A : Set}(xs : List A)(n : Nat) ->
         isTrue (n < length xs) -> A
lookup [] n ()
lookup (x :: xs) zero p = x
lookup (x :: xs) (suc n) p = lookup xs n p

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x
