module Interfaces

import public Data.So
import public Syntax.PreorderReasoning
import public Helper

%default total
%access public export

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
  mapId      : {a : Type} -> map (id {a}) = id {a = f a}
  mapCompose : {a,b,c : Type} -> {g : b -> c} -> {h : a -> b} -> map {f} (g . h) = map g . map h


interface (Applicative f, VFunctor f) => VApplicative (f : Type -> Type) where
  applicativeId : {a : Type} -> {v : f a} -> pure Basics.id <*> v = v
  applicativeCompose : {a,b,c : Type} -> {u : f (b -> c)} -> {v : f (a -> b)} -> {w : f a} -> pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
  applicativeHomomorphism : {a,b : Type} -> {g : a -> b} -> {x : a} -> (<*>) {f} (pure g) (pure x) = pure {f} (g x)
  applicativeInterchange : {a,b : Type} -> {u : f (a -> b)} -> {y : a} -> u <*> pure y = pure (\g => g y) <*> u
  applicativeMap : {a, b : Type} -> {u : a -> b} -> map {f} u = (<*>) (pure {f} u)

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
  mapId = funext (\(MkIdentity _) => Refl)
  mapCompose = funext (\(MkIdentity _) => Refl)

implementation Applicative Identity where
  pure = MkIdentity
  (MkIdentity f) <*> (MkIdentity x) = MkIdentity (f x)

implementation VApplicative Identity where
  applicativeId {v = MkIdentity _} = Refl
  applicativeCompose {u = MkIdentity _} {v = MkIdentity _} {w = MkIdentity _} = Refl
  applicativeHomomorphism = Refl
  applicativeInterchange {u = MkIdentity _} = Refl
  applicativeMap = funext (\(MkIdentity _) => Refl)

using (f : Type -> Type, g : Type -> Type, a : Type)
  record Compose (f : Type -> Type) (g : Type -> Type) a where
    constructor MkCompose
    runCompose : f (g a)

using (f : Type -> Type, g : Type -> Type)
  implementation (Functor f, Functor g) => Functor (Compose f g) where
    map h (MkCompose x) = MkCompose (map (map h) x)


  implementation (VFunctor f, VFunctor g) => VFunctor (Compose f g) where
    mapId {a} {f} {g} =
      funext (\(MkCompose x) =>
        (MkCompose (map (map id) x))
           ={ cong {f = MkCompose} (replace {P = \w => map w x = map id x} (sym $ mapId {f = g}) Refl)}=
        (MkCompose (map id x))
           ={ cong {f = MkCompose} (replace {P = \w => w x = x} (sym $ mapId {f}) Refl) }=
        (MkCompose x) QED)
    mapCompose {a} {f} {g} {g1 = gg} {h} =
      funext (\(MkCompose x) =>
        (MkCompose (map (map (gg . h)) x))
           ={ cong {f = MkCompose} (replace {P = \w => map (map (gg . h)) x = map w x} (mapCompose {f = g} {g = gg} {h}) Refl) }=
        (MkCompose (map (map gg . map h) x))
           ={ cong {f = MkCompose} (replace {P = \w => map (map gg . map h) x = w x} (mapCompose {f}) Refl) }=
        (MkCompose ((map (map gg)) . (map (map h)) $ x))
           ={ cong {f = MkCompose} Refl }=
        (MkCompose (map (map gg) (map (map h) x))) QED)

  implementation (Applicative f, Applicative g) => Applicative (Compose f g) where
    pure x = MkCompose (pure (pure x))
    (MkCompose h) <*> (MkCompose x) = MkCompose (pure (<*>) <*> h <*> x)

  implementation (VApplicative f, VApplicative g) => VApplicative (Compose f g) where
    applicativeId {v = MkCompose x'} =
      (MkCompose (pure (<*>) <*> (pure (pure id)) <*> x'))
         ={ cong {f = MkCompose} (replace {P = \w => w <*> x' = pure (\x => pure id <*> x) <*> x'}
                 (sym $ applicativeHomomorphism {f} {g = (<*>)} {x = pure id}) Refl) }=
      (MkCompose (pure (\x => pure id <*> x) <*> x'))
         ={ cong {f = MkCompose} (cong {f = \w => pure w <*> x'}
                 (the ((\x : g a => pure id <*> x) = (\x : g a => x)) $ funext (\x => applicativeId {f = g}))) }=
      (MkCompose (pure (\x => x) <*> x'))
         ={ cong {f = MkCompose} (replace {P = \w => (pure w <*> x') = pure id <*> x'}
                  (the (id = (\x => x)) $ funext (\x => Refl)) Refl) }=
      (MkCompose (pure id <*> x'))
         ={ cong {f = MkCompose} (applicativeId {f} {v = x'}) }=
      (MkCompose x') QED
    applicativeCompose {u = MkCompose u'} {v = MkCompose v'} {w = MkCompose w'} =
      (MkCompose $ pure (<*>) <*> (pure (<*>) <*> (pure (<*>) <*> pure (pure (.)) <*> u') <*> v') <*> w')
        ={ cong {f=\z=>MkCompose $ pure (<*>) <*> (pure (<*>) <*> (z <*> u') <*> v') <*> w'} $
           applicativeHomomorphism {g = (<*>)} {x = pure (.)} }=
      (MkCompose $ pure (<*>) <*> (pure (<*>) <*> (pure ((pure (.)) <*>) <*> u') <*> v') <*> w')
        ={ cong {f=\z=>MkCompose $ pure (<*>) <*> (z <*> v') <*> w'} $
           sym $ applicativeCompose {u = pure (<*>)} {v = pure ((pure (.)) <*>)} {w = u'} }=
      (MkCompose $ pure (<*>) <*> (pure (.) <*> pure (<*>) <*> pure ((pure (.)) <*>) <*> u' <*> v') <*> w')
        ={ cong {f=\z=>MkCompose $ pure (<*>) <*> (z <*> pure ((pure (.)) <*>) <*> u' <*> v') <*> w'} $
           applicativeHomomorphism {g = (.)} {x = (<*>)} }=
      (MkCompose $ pure (<*>) <*> (pure ((.) $ (<*>)) <*> pure ((pure (.)) <*>) <*> u' <*> v') <*> w')
        ={ cong {f=\z=>MkCompose $ pure (<*>) <*> (z <*> u' <*> v') <*> w'} $
           applicativeHomomorphism {g = ((.) $ (<*>))} {x = ((pure (.)) <*>)} }=
      (MkCompose $ pure (<*>) <*> (pure (((.) $ (<*>)) $ ((pure (.)) <*>)) <*> u' <*> v') <*> w')
        ={ cong {f=\z=>MkCompose $ z <*> w'} $
           sym $ applicativeCompose {u = pure (<*>)} {v = pure (((.) $ (<*>)) $ ((pure (.)) <*>)) <*> u'} {w = v'} }=
      (MkCompose $ pure (.) <*> pure (<*>) <*> (pure (((.) $ (<*>)) $ ((pure (.)) <*>)) <*> u') <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ z <*> (pure (((.) $ (<*>)) $ ((pure (.)) <*>)) <*> u') <*> v' <*> w'} $
           applicativeHomomorphism {g = (.)} {x = (<*>)} }=
      (MkCompose $ pure ((.) $ (<*>)) <*> (pure (((.) $ (<*>)) $ ((pure (.)) <*>)) <*> u') <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ z <*> v' <*> w'} $
           sym $ applicativeCompose {u = pure ((.) $ (<*>))} {v = pure (((.) $ (<*>)) $ ((pure (.)) <*>))} {w = u'} }=
      (MkCompose $ pure (.) <*> pure ((.) $ (<*>)) <*> pure (((.) $ (<*>)) $ ((pure (.)) <*>)) <*> u' <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ z <*> pure (((.) $ (<*>)) $ ((pure (.)) <*>)) <*> u' <*> v' <*> w'} $
           applicativeHomomorphism {g = (.)} {x = ((.) $ (<*>))} }=
      (MkCompose $ pure ((.) $ ((.) $ (<*>))) <*> pure (((.) $ (<*>)) $ ((pure (.)) <*>)) <*> u' <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ z <*> u' <*> v' <*> w'} $
           applicativeHomomorphism {g = ((.) $ ((.) $ (<*>)))} {x = (((.) $ (<*>)) $ ((pure (.)) <*>))} }=
      (MkCompose $ pure (((.) $ ((.) $ (<*>))) $ (((.) $ (<*>)) $ ((pure (.)) <*>))) <*> u' <*> v' <*> w')
        -- both of these should be equal to `pure (\x, y, z => pure (.) <*> x <*> y <*> z) <*> u <*> v <*> w`
        ={ ?abracadabra }=
      (MkCompose $ pure ((\q => q $ (<*>)) . (((.) $ (.)) $ (((.) $ (.)) $ (<*>)))) <*> u' <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ z u' <*> v' <*> w'} $
           sym $ applicativeMap {u = ((\q => q $ (<*>)) . (((.) $ (.)) $ (((.) $ (.)) $ (<*>))))} }=
      (MkCompose $ map ((\q => q $ (<*>)) . (((.) $ (.)) $ (((.) $ (.)) $ (<*>)))) u' <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ z u' <*> v' <*> w'} $
           mapCompose {g = (\q => q $ (<*>)) } {h = (((.) $ (.)) $ (((.) $ (.)) $ (<*>)))} }=
      (MkCompose $ map (\q => q $ (<*>)) (map (((.) $ (.)) $ (((.) $ (.)) $ (<*>))) u') <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ map (\q => q $ (<*>)) (z u') <*> v' <*> w'} $
           applicativeMap {u = (((.) $ (.)) $ (((.) $ (.)) $ (<*>)))} }=
      (MkCompose $ map (\q => q $ (<*>)) (pure (((.) $ (.)) $ (((.) $ (.)) $ (<*>))) <*> u') <*> v' <*> w')
        ={ ?prf }=
        -- DOESN'T WORK: Type mismatch between `g (a -> b1) -> g a -> g b1` and `f (a -> b) -> f a -> g b1`
        -- NEEDS FUNEXT?
        -- ={ cong {f=\z=>MkCompose $ z (pure (((.) $ (.)) $ (((.) $ (.)) $ (<*>))) <*> u') <*> v' <*> w'} $
        --    applicativeMap {u = (\q => q $ (<*>))} }=
      (MkCompose $ pure (\g => g $ (<*>)) <*> (pure (((.) $ (.)) $ (((.) $ (.)) $ (<*>))) <*> u') <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ z <*> v' <*> w'} $
           sym $ applicativeInterchange {u = pure (((.) $ (.)) $ (((.) $ (.)) $ (<*>))) <*> u'} {y = (<*>)} }=
      (MkCompose $ pure (((.) $ (.)) $ (((.) $ (.)) $ (<*>))) <*> u' <*> pure (<*>) <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ z <*> u' <*> pure (<*>) <*> v' <*> w'} $
           sym $ applicativeHomomorphism {g = ((.) $ (.))} {x = (((.) $ (.)) $ (<*>))} }=
      (MkCompose $ pure ((.) $ (.)) <*> pure (((.) $ (.)) $ (<*>)) <*> u' <*> pure (<*>) <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ z <*> pure (((.) $ (.)) $ (<*>)) <*> u' <*> pure (<*>) <*> v' <*> w'} $
           sym $ applicativeHomomorphism {g = (.)} {x = (.)} }=
      (MkCompose $ pure (.) <*> pure (.) <*> pure (((.) $ (.)) $ (<*>)) <*> u' <*> pure (<*>) <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ z <*> pure (<*>) <*> v' <*> w'} $
           applicativeCompose {u = pure (.)} {v = pure (((.) $ (.)) $ (<*>))} {w = u'} }=
      (MkCompose $ pure (.) <*> (pure (((.) $ (.)) $ (<*>)) <*> u') <*> pure (<*>) <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ pure (.) <*> (z <*> u') <*> pure (<*>) <*> v' <*> w'} $
           sym $ applicativeHomomorphism {g = ((.) $ (.))} {x = (<*>)} }=
      (MkCompose $ pure (.) <*> (pure ((.) $ (.)) <*> pure (<*>) <*> u') <*> pure (<*>) <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ pure (.) <*> (z <*> pure (<*>) <*> u') <*> pure (<*>) <*> v' <*> w'} $
           sym $ applicativeHomomorphism {g = (.)} {x = (.)} }=
      (MkCompose $ pure (.) <*> (pure (.) <*> pure (.) <*> pure (<*>) <*> u') <*> pure (<*>) <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ pure (.) <*> z <*> pure (<*>) <*> v' <*> w'} $
           applicativeCompose {u = pure (.)} {v = pure (<*>)} {w = u'} }=
      (MkCompose $ pure (.) <*> (pure (.) <*> (pure (<*>) <*> u')) <*> pure (<*>) <*> v' <*> w')
        ={ cong {f=\z=>MkCompose $ z <*> w'} $
           applicativeCompose {u = pure (.) <*> (pure (<*>) <*> u')} {v = pure (<*>)} {w = v'} }=
      (MkCompose $ pure (.) <*> (pure (<*>) <*> u') <*> (pure (<*>) <*> v') <*> w')
        ={ cong {f=MkCompose} $
           applicativeCompose {u = pure (<*>) <*> u'} {v = pure (<*>) <*> v'} {w = w'} }=
      (MkCompose $ pure (<*>) <*> u' <*> (pure (<*>) <*> v' <*> w'))
        QED
    applicativeHomomorphism {f} {g} {g1 = h} {x} =
      (MkCompose (pure (<*>) <*> pure (pure h) <*> pure (pure x)))
        ={ cong {f = MkCompose} (cong {f = \w => w <*> pure {f} (pure {f = g} x)} (applicativeHomomorphism {f})) }=
      (MkCompose (pure (\x => pure h <*> x) <*> pure (pure x)))
        ={ cong {f = MkCompose} (applicativeHomomorphism {f}) }=
      (MkCompose (pure (pure h <*> pure x)))
        ={ cong {f = MkCompose} (cong {f = pure} (applicativeHomomorphism {f = g})) }=
      (MkCompose (pure (pure (h x)))) QED
    applicativeInterchange {f} {g} {a} {b} {u = MkCompose u'} {y} =
      (MkCompose u' <*> MkCompose (pure (pure y)))
        ={ Refl }=
      (MkCompose (pure (<*>) <*> u' <*> pure (pure y)))
        ={ cong {f = MkCompose} applicativeInterchange }=
      (MkCompose (pure (\h => h $ pure y) <*> (pure (<*>) <*> u')))
        ={ cong {f = MkCompose} (fundet (sym applicativeMap) (pure (<*>) <*> u')) }=
      (MkCompose (map (\h => h $ pure y) (pure (<*>) <*> u')))
        ={ cong {f = MkCompose} (cong {f = map {f} (\h => h $ pure {f = g} y)} (fundet (sym applicativeMap) u') ) }=
      (MkCompose (map (\h => h $ pure y) (map (<*>) u')))
        ={ cong {f = MkCompose} (fundet (sym mapCompose) u') }=
      (MkCompose (map ((\h => h $ pure y) . (<*>)) u'))
        ={ cong {f = MkCompose} (fundet applicativeMap u') }=
      (MkCompose (pure (<*> pure y) <*> u'))
        ={ cong {f = MkCompose} (id (cong {f = \w => pure w <*> u'} {a = (\z => the (g b) $ z <*> pure {f = g} y)} {b = (\z => the (g b) $ pure {f = g} (\h => h y) <*> z)}
           (funext {f = (\z => the (g b) $ z <*> pure {f = g} y)} {g = (\z => pure {f = g} (\h => h y) <*> z)} (\x => applicativeInterchange {f = g}) )))}=
      (MkCompose (pure (\x => (pure (\h => h y)) <*> x) <*> u'))
       ={ Refl }=
      (MkCompose (pure ((<*>) (pure (\h => h y))) <*> u'))
        ={ cong {f = MkCompose} (cong {a = pure ((<*>) (pure (\h => h y)))} {f = \w => w <*> u'} (sym $ applicativeHomomorphism {f}) ) }=
      (MkCompose (pure (<*>) <*> (pure (pure (\h => h y))) <*> u'))
        ={ Refl }=
      (MkCompose (pure (pure (\h => h y))) <*> MkCompose u') QED
    applicativeMap {u} = funext (\(MkCompose w) =>
      (MkCompose (map (map u) w))
        ={ cong {f = MkCompose} (fundet applicativeMap w) }=
      (MkCompose (pure (map u) <*> w))
        ={ cong {f = (\r => MkCompose (pure r <*> w) )} applicativeMap }=
      (MkCompose (pure ((pure u) <*>) <*> w))
        ={ cong {f = (\r => MkCompose (r <*> w))} (sym applicativeHomomorphism) }=
      (MkCompose (pure (<*>) <*> pure (pure u) <*> w))
        QED)

using (t : Type -> Type)
  interface (Traversable t) => VTraversable (t : Type -> Type) where
    traversableNatural : (Applicative f, Applicative g, VApplicativeTransformer f g) => {a, b : Type} -> {h : a -> f b} ->
                            transformA {f} {g} . traverse {t} h = traverse {t} (transformA {f} {g} . h)
    traversableIdentity : {a : Type} -> traverse {t} MkIdentity = MkIdentity {a = t a}
    traversableComposition : (Applicative f, Applicative g) => {a,b,c : Type} -> {h : a -> f b} -> {i : b -> g c} ->
                            traverse {t} (MkCompose {f} {g} . map i . h) = MkCompose . map (traverse {t} i) . traverse {t} h
