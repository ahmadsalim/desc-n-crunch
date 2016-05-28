module Interfaces

import public Data.So
import public Syntax.PreorderReasoning

%default total
%access public export

postulate -- HOPEFULLY NOTHING GOES WRONG
   funext : {a,b : Type} -> {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

interface Eq a => VEq a where
  eqReflexive  : {x : a} -> So (x == x)
  eqSymmetric  : {x,y : a} -> So (y == x) -> So (x == y)
  eqTransitive : {x,y,z : a} -> So (x == z) -> So (z == y) -> So (x == y)

interface VEq a => SEq a where
  eqReflective : {x,y : a} -> So (x == y) -> x = y

interface Ord a => VOrd a where
  leqReflexive : {x : a} -> So (x <= x)
  leqTransitive : {x,y,z : a} -> So (x <= z) -> So (z <= y) -> So (x <= y)
  leqAntisymmetric : {x,y : a} -> So (x <= y) -> So (y <= x) -> So (x == y)
  leqTotal : {x, y: a} -> Either (So (x <= y)) (So (y <= x))

interface VOrd a => SOrd a where
  leqAntisymmetricReflective : {x, y: a} -> So (x <= y) -> So (y <= x) -> x = y

interface Functor f => VFunctor (f : Type -> Type) where
  mapId      : {a : Type} -> map (id {a = a}) = id {a = f a}
  mapCompose : {a,b,c : Type} -> {g : b -> c} -> {h : a -> b} -> map {f = f} (g . h) = map g . map h


interface (Applicative f) => VApplicative (f : Type -> Type) where
  applicativeId : {a : Type} -> {v : f a} -> pure Basics.id <*> v = v
  applicativeCompose : {a,b,c : Type} -> {u : f (b -> c)} -> {v : f (a -> b)} -> {w : f a} -> pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
  applicativeHomomorphism : {a,b : Type} -> {g : a -> b} -> {x : a} -> the (f b) $ pure g <*> pure x = pure (g x)
  applicativeInterchange : {a,b : Type} -> {u : f (a -> b)} -> {y : a} -> u <*> pure y = pure (\g => g y) <*> u

interface (VApplicative f, VApplicative g) => VApplicativeTransformer (f : Type -> Type) (g : Type -> Type) where
  transformA : {a: Type} -> f a -> g a
  transformAPure : {a : Type} -> {x : a} -> transformA (pure x) = pure x
  transformAAp   : {a,b : Type} -> {x : f (a -> b)} -> {y : f a} -> transformA (x <*> y) = transformA x <*> transformA y

using (a : Type)
  record Identity a where
    constructor MkIdentity
    runIdentity : a

implementation Functor Identity where
  map f (MkIdentity x) = MkIdentity (f x)

implementation VFunctor Identity where
  mapId = funext (\(MkIdentity x) => Refl)
  mapCompose = funext (\(MkIdentity x) => Refl)

implementation Applicative Identity where
  pure = MkIdentity
  (MkIdentity f) <*> (MkIdentity x) = MkIdentity (f x)

implementation VApplicative Identity where
  applicativeId {v = MkIdentity x} = Refl
  applicativeCompose {u = MkIdentity u'} {v = MkIdentity v'} {w = MkIdentity w'} = Refl
  applicativeHomomorphism = Refl
  applicativeInterchange {u = MkIdentity u'} = Refl

using (f : Type -> Type, g : Type -> Type, a : Type)
  record Compose (f : Type -> Type) (g : Type -> Type) a where
    constructor MkCompose
    runCompose : f (g a)

using (f : Type -> Type, g : Type -> Type)
  implementation (Functor f, Functor g) => Functor (Compose f g) where
    map h (MkCompose x) = MkCompose (map (map h) x)


  implementation (VFunctor f, VFunctor g) => VFunctor (Compose f g) where
    mapId {a = a} {f = f} {g = g} =
      funext (\(MkCompose x) =>
        (MkCompose (map (map id) x)) ={ cong {f = MkCompose} (replace {P = \w => map w x = map id x} (sym $ mapId {f = g}) Refl)}=
        (MkCompose (map id x)) ={ cong {f = MkCompose} (replace {P = \w => w x = x} (sym $ mapId {f = f}) Refl) }=
        (MkCompose x) QED)
    mapCompose {a = a} {f = f} {g = g} {g1 = gg} {h = h} =
      funext (\(MkCompose x) =>
        (MkCompose (map (map (gg . h)) x)) ={ cong {f = MkCompose} (replace {P = \w => map (map (gg . h)) x = map w x} (mapCompose {f = g} {g = gg} {h = h}) Refl) }=
        (MkCompose (map (map gg . map h) x)) ={ cong {f = MkCompose} (replace {P = \w => map (map gg . map h) x = w x} (mapCompose {f = f}) Refl) }=
        (MkCompose ((map (map gg)) . (map (map h)) $ x)) ={ cong {f = MkCompose} Refl }=
        (MkCompose (map (map gg) (map (map h) x))) QED)

  implementation (Applicative f, Applicative g) => Applicative (Compose f g) where
    pure x = MkCompose (pure (pure x))
    (MkCompose h) <*> (MkCompose x) = MkCompose (pure (<*>) <*> h <*> x)

  implementation (VApplicative f, VApplicative g) => VApplicative (Compose f g) where
    applicativeId {v = MkCompose x'} =
      (MkCompose (pure (<*>) <*> (pure (pure id)) <*> x'))
         ={ cong {f = MkCompose} (replace {P = \w => w <*> x' = pure (\x => pure id <*> x) <*> x'}
                 (sym $ applicativeHomomorphism {f = f} {g = (<*>)} {x = pure id}) Refl) }=
      (MkCompose (pure (\x => pure id <*> x) <*> x'))
         ={ cong {f = MkCompose} (cong {f = \w => pure w <*> x'}
                 (the ((\x : g a => pure id <*> x) = (\x : g a => x)) $ funext (\x => applicativeId {f = g}))) }=
      (MkCompose (pure (\x => x) <*> x'))
         ={ cong {f = MkCompose} (replace {P = \w => (pure w <*> x') = pure id <*> x'}
                  (the (id = (\x => x)) $ funext (\x => Refl)) Refl) }=
      (MkCompose (pure id <*> x'))
         ={ cong {f = MkCompose} (applicativeId {f = f} {v = x'}) }=
      (MkCompose x') QED
    applicativeCompose = ?p
    applicativeHomomorphism {f = f} {g = g} {g1 = h} {x = x} =
      (MkCompose (pure (<*>) <*> pure (pure h) <*> pure (pure x)))
        ={ cong {f = MkCompose} (cong {f = \w => w <*> pure {f = f} (pure {f = g} x)} (applicativeHomomorphism {f = f})) }=
      (MkCompose (pure (\x => pure h <*> x) <*> pure (pure x)))
        ={ cong {f = MkCompose} (applicativeHomomorphism {f = f}) }=
      (MkCompose (pure (pure h <*> pure x)))
        ={ cong {f = MkCompose} (cong {f = pure} (applicativeHomomorphism {f = g})) }=
      (MkCompose (pure (pure (h x)))) QED
    applicativeInterchange {f = f} {g = g} {a = a} {b = b} {u = MkCompose u'} {y = y} =
      (MkCompose u' <*> MkCompose (pure (pure y)))
        ={ Refl }=
      (MkCompose (pure (<*>) <*> u' <*> pure (pure y)))
        ={ ?p }=
      (MkCompose (pure (\h => h $ pure y) <*> (pure (<*>) <*> u')))
        ={ cong {f = MkCompose} ?p }=
      (MkCompose (pure (<*> pure y) <*> u'))
        ={ cong {f = MkCompose} (id (cong {f = \w => pure w <*> u'} {a = (\z => the (g b) $ z <*> pure {f = g} y)} {b = (\z => the (g b) $ pure {f = g} (\h => h y) <*> z)}
           (funext {f = (\z => the (g b) $ z <*> pure {f = g} y)} {g = (\z => pure {f = g} (\h => h y) <*> z)} (\x => applicativeInterchange {f = g}) )))}=
      (MkCompose (pure (\x => (pure (\h => h y)) <*> x) <*> u'))
       ={ Refl }=
      (MkCompose (pure ((<*>) (pure (\h => h y))) <*> u'))
        ={ cong {f = MkCompose} (cong {a = pure ((<*>) (pure (\h => h y))) } {f = \w => w <*> u'} (sym $ applicativeHomomorphism {f = f}) ) }=
      (MkCompose (pure (<*>) <*> (pure (pure (\h => h y))) <*> u'))
        ={ Refl }=
      (MkCompose (pure (pure (\h => h y))) <*> MkCompose u') QED

using (t : Type -> Type)
  interface (Traversable t) => VTraversable (t : Type -> Type) where
    traversableNatural : (Applicative f, Applicative g, VApplicativeTransformer f g) => {a, b : Type} -> {h : a -> f b} ->
                            transformA {f = f} {g = g} . traverse {t = t} h = traverse {t = t} (transformA {f = f} {g = g} . h)
    traversableIdentity : {a : Type} -> traverse {t = t} MkIdentity = MkIdentity {a = t a}
    traversableComposition : (Applicative f, Applicative g) => {a,b,c : Type} -> {h : a -> f b} -> {i : b -> g c} -> traverse {t = t} (MkCompose {f = f} {g = g} . map i . h) = MkCompose . map (traverse {t = t} i) . traverse {t = t} h
