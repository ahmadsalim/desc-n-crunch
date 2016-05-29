module Descriptions.Traversable

import Descriptions.Core
import Interfaces

%default total
%access export
%auto_implicits off

using (f: Type -> Type, g: Type -> Type)
  zipA : Applicative g => {a, b: _} -> g a -> g b -> g (x : a ** b)
  zipA {a} {b} x y = zipD <$> x <*> y
    where zipD : a -> b -> (x : a ** b)
          zipD x y = (x ** y)

  mutual
    gtraversed : Applicative g => {a,b,Ix: _} -> (dr: PDesc (S Z) Ix) -> (PConstraints1 VTraversable dr)
                                              -> (d: PDesc (S Z) Ix) -> (PConstraints1 VTraversable d) -> {ix : Ix}
                                              -> (k : g (PSynthesize d b (PData dr b) ix) -> g (PData dr b ix))
                                              -> (a -> g b) -> PSynthesize d a (PData dr a) ix -> g (PData dr b ix)
    gtraversed dr constraintsr (PRet ix) constraints k f Refl = k (pure Refl)
    gtraversed dr constraintsr (PArg A kdesc) constraints k f (arg ** rest) =
     gtraversed dr constraintsr (kdesc arg) (constraints arg) (\idm => k (MkDPair arg <$> idm)) f rest
    gtraversed dr constraintsr (PPar FZ kdesc) constraints k f (par ** rest) =
     gtraversed dr constraintsr kdesc constraints (\idm => k (zipA (f par) idm)) f rest
    gtraversed _ _ (PPar (FS FZ) _) _ _ _ _ impossible
    gtraversed _ _ (PPar (FS (FS _)) _) _ _ _ _ impossible
    gtraversed dr constraintsr (PMap g FZ kdesc) (trav, constraints) k f (targ ** rest) =
      gtraversed dr constraintsr kdesc constraints (\idm => k (zipA (traverse f targ) idm)) f rest
    gtraversed _ _ (PMap _ (FS FZ) _) _ _ _ _ impossible
    gtraversed _ _ (PMap _ (FS (FS _)) _) _ _ _ _ impossible
    gtraversed dr constraintsr (PRec ix kdesc) constraints k f (rec ** rest) =
      gtraversed dr constraintsr kdesc constraints (\idm => k (zipA (gtraverse dr constraintsr f rec) idm)) f rest

    gtraverse  : Applicative g => {a,b,Ix: _} -> (d: PDesc (S Z) Ix) -> (PConstraints1 VTraversable d) -> {ix : Ix}
                                              -> (a -> g b) -> PData d a ix -> g (PData d b ix)
    gtraverse d constraints f (Con x) = assert_total $ gtraversed d constraints d constraints (Con <$>) f x

  mutual
    gtraversabledIdentityH : {a,Ix: _} -> (dr: PDesc 1 Ix) -> (constraintsr: PConstraints1 VTraversable dr)
                                       -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                              -> {ix : Ix} -> (k : Identity (PSynthesize d a (PData dr a) ix) -> Identity (PData dr a ix))
                              -> (X : PSynthesize d a (PData dr a) ix) -> gtraversed dr constraintsr d constraints k MkIdentity X = k (MkIdentity X)
    gtraversabledIdentityH dr constraintsr (PRet ix) constraints k Refl = Refl
    gtraversabledIdentityH dr constraintsr (PArg A kdesc) constraints k (arg ** rest) =
      gtraversabledIdentityH dr constraintsr (kdesc arg) (constraints arg) (\idm => k (MkDPair arg <$> idm)) rest
    gtraversabledIdentityH dr constraintsr (PPar FZ kdesc) constraints k (par ** rest) =
      gtraversabledIdentityH dr constraintsr kdesc constraints (\idm => k (zipA (MkIdentity par) idm)) rest
    gtraversabledIdentityH _ _ (PPar (FS FZ) _) _ _ _ impossible
    gtraversabledIdentityH _ _ (PPar (FS (FS _)) _) _ _ _ impossible
    gtraversabledIdentityH {a = a} dr constraintsr (PMap f FZ kdesc) (vfuna, vfunr) k (ta ** rest) with (traversableIdentity @{vfuna} {a = a})
      gtraversabledIdentityH {a = a} dr constraintsr (PMap f FZ kdesc) (vfuna, vfunr) k (ta ** rest) | prf =
        let prf' = gtraversabledIdentityH {a = a} dr constraintsr kdesc vfunr (\idm => k (zipA (traverse MkIdentity ta) idm)) rest
        in replace {P = \w => (gtraversed {a = a} {b = a} dr constraintsr kdesc vfunr (\idm => k (zipA (traverse MkIdentity ta) idm)) MkIdentity rest) = k (zipA w (MkIdentity rest))} (fundet {f = traverse MkIdentity} {g = MkIdentity} prf ta) prf'
    gtraversabledIdentityH _ _ (PMap _ (FS FZ) _) _ _ _ impossible
    gtraversabledIdentityH _ _ (PMap _ (FS (FS _)) _) _ _ _ impossible
    gtraversabledIdentityH {a = a} dr constraintsr (PRec ix kdesc) constraints k (rec ** rest) with (gtraversableIdentityH dr constraintsr rec)
      gtraversabledIdentityH {a = a} dr constraintsr (PRec ix kdesc) constraints k (rec ** rest) | prf =
        let prf' = gtraversabledIdentityH {a = a} dr constraintsr kdesc constraints (\idm => k (zipA (gtraverse dr constraintsr MkIdentity rec) idm)) rest
        in replace {P = \w => (gtraversed dr constraintsr kdesc constraints (\idm => k (zipA (gtraverse dr constraintsr MkIdentity rec) idm)) MkIdentity rest) = k (zipA w (MkIdentity rest))} prf prf'

    gtraversableIdentityH : {a,Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                            -> {ix : Ix} -> (X : PData d a ix) -> gtraverse d constraints MkIdentity X = MkIdentity X
    gtraversableIdentityH d constraints (Con x) = assert_total $ gtraversabledIdentityH d constraints d constraints (Con <$>) x

  gtraversableIdentity : {Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                                   -> gtraverse d constraints MkIdentity = MkIdentity
  gtraversableIdentity d constraints = funext (gtraversableIdentityH d constraints)

  mutual
  {- Find correct specification
   gtraversabledCompositionH : (Applicative f, Applicative g) => {a,b,c,Ix: _} -> (dr: PDesc 1 Ix) -> (constraintsr: PConstraints1 VTraversable dr)
                              -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                              -> {ix : Ix} -> (k : Compose f g (PSynthesize d c (PData dr c) ix) -> Compose f g (PData dr c ix))
                              -> (kf : f (PSynthesize d b (PData dr b) ix) -> f (PData dr b ix))
                              -> (kg : g (PSynthesize d c (PData dr c) ix) -> g (PData dr c ix))
                              -> (h: a -> f b) -> (i : b -> g c) -> (X : PSynthesize d a (PData dr a) ix)
                              -> gtraversed dr constraintsr d constraints k (MkCompose {f = f} {g = g} . map {f = f} i . h) X = k (MkCompose . map {f = f} (gtraversed dr constraintsr d constraints kg i) . gtraversed dr constraintsr d constraints kf h $ X)
  -}
   gtraversableCompositionH :(Applicative f, Applicative g) => {a,b,c,Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                            -> (h : a -> f b) -> (i : b -> g c) -> {ix : Ix} -> (X : PData d a ix)
                            -> gtraverse d constraints (MkCompose {f = f} {g = g} . map i . h) X = MkCompose . map (gtraverse d constraints i) . gtraverse d constraints h $ X

  gtraversableComposition : (Applicative f, Applicative g) => {a, b, c, Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                           -> (h : a -> f b) -> (i : b -> g c) -> gtraverse d constraints (MkCompose {f = f} {g = g} . map i . h) = MkCompose . map (gtraverse d constraints i) . gtraverse d constraints h
  gtraversableComposition d constraints h i = funext (gtraversableCompositionH d constraints h i)
