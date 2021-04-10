{- cabal:
build-depends: base, constraints
-}
{-# language TypeFamilies, TypeFamilyDependencies, ConstraintKinds, ScopedTypeVariables, NoStarIsType, TypeOperators, TypeApplications, GADTs, AllowAmbiguousTypes, FunctionalDependencies, UndecidableSuperClasses, UndecidableInstances, FlexibleInstances, QuantifiedConstraints, BlockArguments, RankNTypes, FlexibleContexts, StandaloneKindSignatures, DefaultSignatures  #-}

 -- ⊷, ≕, =∘, =◯ These choices all look like something out of Star Trek, so let's boldly go...

import Data.Constraint hiding (top, bottom, Bottom)
import Data.Kind
import Data.Some
import Data.Void
import Unsafe.Coerce

class (Not p ~ Never p) => Never p where 
  never :: p => Dict r
  
class (Prop (Not p), Not (Not p) ~ p) => Prop (p :: Constraint) where
  type Not p :: Constraint
  type Not p = Never p

  contradiction :: (p, Not p) => Dict r
  default contradiction :: (Not p ~ Never p, p, Not p) => Dict r
  contradiction = never @p

instance (Prop p, Not p ~ Never p) => Prop (Never p) where
  type Not (Never p) = p
  contradiction = never @p

instance Prop (Bounded a)
instance Prop (Num a)

instance Never (Bounded Void) where never = absurd minBound
instance Never (Num Void) where never = absurd (fromInteger 0)

class (p, q) => p * q
instance (p, q) => p * q

class (Not p => q, Not q => p) => p ⅋ q
instance (Not p => q, Not q => p) => p ⅋ q

instance (Prop p, Prop q) => Prop (p ⅋ q) where
  type Not (p ⅋ q) = Not p * Not q
  contradiction = contradiction @p

instance (Prop p, Prop q) => Prop (p * q) where
  type Not (p * q) = Not p ⅋ Not q
  contradiction = contradiction @p
 
infixr 0 ⊸
type (⊸) p = (⅋) (Not p)

fun :: (Prop p, Prop q, p) => (p ⊸ q) :- q
fun = Sub Dict

contra :: (Prop p, Prop q, Not q) => (p ⊸ q) :- Not p
contra = Sub Dict

class (p, q) => p & q
instance (p, q) => p & q

class p + q where
  runEither :: (p => Dict r) -> (q => Dict r) -> Dict r

data G p q k = G ((forall r. (p => Dict r) -> (q => Dict r) -> Dict r))

-- (Eq a + Ord [a]) :- Eq [a]
  
inl :: forall p q. p :- (p + q)
inl = Sub let
    go :: (p => Dict r) -> (q => Dict r) -> Dict r
    go pr _ = pr
  in unsafeCoerce (G go)

inr :: forall q p. q :- (p + q)
inr = Sub let
    go :: (p => Dict r) -> (q => Dict r) -> Dict r
    go _ qr = qr
  in unsafeCoerce (G go)

instance (Prop p, Prop q) => Prop (p & q) where
  type Not (p & q) = Not p + Not q
  contradiction = runEither @(Not p) @(Not q) (contradiction @p) (contradiction @q) 

instance (Prop p, Prop q) => Prop (p + q) where
  type Not (p + q) = Not p & Not q
  contradiction = runEither @p @q (contradiction @(Not p)) (contradiction @(Not q)) 

withL' :: (p & q) :- p
withL' = Sub Dict

withR' :: (p & q) :- q
withR' = Sub Dict

-- now we need to get into more serious dictionary manipulation

-- withL :: Dict (p & q ⊸ p)
-- withL = Dict


type (⊷) :: Constraint -> Constraint -> Type
data p ⊷ q = Lol (p :- q) (Not q :- Not p) -- should be a with, haskell side

embedLol :: forall p q. (Prop p, Prop q) => (p ⊸ q) => p ⊷ q
embedLol = Lol (Sub Dict) $ Sub case contra @p @q of
  Sub Dict -> Dict

{-

class Mk p q where runFun :: p => q
instance (p => q) => Mk p q where runFun = Dict

data Box p = Box p

lift :: (p :- Dict q) => 
lift 
  unsafeCoerce (Box (&)) :: Dict (Mk p)

  p -> (p -> r) -> r

projectLol :: forall p q. (Prop p, Prop q) => (p ⊷ q) -> Dict (p ⊸ q)
projectLol = error "TODO"

apply :: forall p q. (p => q) => (p :- q)
apply = Sub Dict
-}

{-
data Box a = Box a

class Top where
  top :: Some Dict

mkTop :: a => Dict Top
mkTop = a => unsafeCoerce (Box (Some (Dict @a))

top' :: a :- Top
top = 

instance Prop Top where
  type Not Top = Zero

instance Prop () where
  type Not () = Bot

class Zero where
  zero :: a

zero :: Dict (Zero ⊸ a)
zero = Sub Dict

instance Prop Zero where
  type Not Zero = Top

class Bot where
  --bot :: (forall r. Top => r) -> 
  
instance Prop Bottom where
  contradiction = _
-}

main = return ()

