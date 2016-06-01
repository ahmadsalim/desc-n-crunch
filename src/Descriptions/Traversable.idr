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
    gtraversed : Applicative g => {a,b,Ix: _} -> (dr: PDesc (S Z) Ix) -> (constraintsr: PConstraints1 VTraversable dr)
                                              -> (d: PDesc (S Z) Ix) -> (constraints: PConstraints1 VTraversable d) -> {ix : Ix}
                                              -> (f: a -> g b) -> PSynthesize d a (PData dr a) ix -> g (PSynthesize d b (PData dr b) ix)
    gtraversed dr constraintsr (PRet ix) constraints f Refl = pure Refl
    gtraversed dr constraintsr (PArg A kdesc) constraints f (arg ** rest) with (gtraversed dr constraintsr (kdesc arg) (constraints arg) f rest)
      gtraversed dr constraintsr (PArg A kdesc) constraints f (arg ** rest) | grest = pure (MkDPair arg) <*> grest
    gtraversed {a = a} dr constraintsr (PPar FZ kdesc) constraints f (p ** rest) with (gtraversed dr constraintsr kdesc constraints f rest)
      gtraversed {a = a} dr constraintsr (PPar FZ kdesc) constraints f (p ** rest) | grest = zipA (f p) grest
    gtraversed _ _ (PPar (FS FZ) _) _ _ _ impossible
    gtraversed _ _ (PPar (FS (FS _)) _) _ _ _ impossible
    gtraversed dr constraintsr (PMap g FZ kdesc) (vtrava, vtravr) f (ta ** rest) with (gtraversed dr constraintsr kdesc vtravr f rest)
      gtraversed dr constraintsr (PMap g FZ kdesc) (vtrava, vtravr) f (ta ** rest) | grest = zipA (traverse f ta) grest
    gtraversed _ _ (PMap _ (FS FZ) _) _ _ _ impossible
    gtraversed _ _ (PMap _ (FS (FS _)) _) _ _ _ impossible
    gtraversed dr constraintsr (PRec ix kdesc) constraints f (rec ** rest) with (gtraverse dr constraintsr f rec)
      gtraversed dr constraintsr (PRec ix kdesc) constraints f (rec ** rest) | grec with (gtraversed dr constraintsr kdesc constraints f rest)
        gtraversed dr constraintsr (PRec ix kdesc) constraints f (rec ** rest) | grec | grest = zipA grec grest


    gtraverse  : Applicative g => {a,b,Ix: _} -> (d: PDesc (S Z) Ix) -> (PConstraints1 VTraversable d) -> {ix : Ix}
                                              -> (f: a -> g b) -> PData d a ix -> g (PData d b ix)
    gtraverse d constraints f (Con x) = assert_total $ Con <$> gtraversed d constraints d constraints f x

  mutual
    gtraversabledIdentityH : {a,Ix: _} -> (dr: PDesc 1 Ix) -> (constraintsr: PConstraints1 VTraversable dr)
                                       -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                                      -> {ix : Ix} ->(X : PSynthesize d a (PData dr a) ix)
                                      -> gtraversed {g = Identity} dr constraintsr d constraints MkIdentity X = MkIdentity X
    gtraversabledIdentityH dr constraintsr (PRet ix) constraints Refl = Refl
    gtraversabledIdentityH {a = a} {ix = ix} dr constraintsr (PArg A kdesc) constraints (arg ** rest) with (gtraversabledIdentityH dr constraintsr (kdesc arg) (constraints arg) rest)
      gtraversabledIdentityH {a = a} {ix = ix} dr constraintsr (PArg A kdesc) constraints (arg ** rest) | prf =
        replace {P = \w => pure {f = Identity} (MkDPair {P = \ag => PSynthesize (kdesc ag) a (PData dr a) ix} arg) <*> w = MkIdentity (arg ** rest)} (sym prf) Refl
    gtraversabledIdentityH dr constraintsr (PPar FZ kdesc) constraints (p ** rest) with (gtraversabledIdentityH dr constraintsr kdesc constraints rest)
      gtraversabledIdentityH dr constraintsr (PPar FZ kdesc) constraints (p ** rest) | prf = rewrite prf in Refl
    gtraversabledIdentityH _ _ (PPar (FS FZ) _) _ _ impossible
    gtraversabledIdentityH _ _ (PPar (FS (FS _)) _) _ _ impossible
    gtraversabledIdentityH {a = a} dr constraintsr (PMap f FZ kdesc) (vtrava, vtravr) (ta ** rest) with (fundet (traversableIdentity {t = f} {a = a}) ta)
      gtraversabledIdentityH {a = a} dr constraintsr (PMap f FZ kdesc) (vtrava, vtravr) (ta ** rest) | prf with (gtraversabledIdentityH dr constraintsr kdesc vtravr rest)
        gtraversabledIdentityH {a = a} dr constraintsr (PMap f FZ kdesc) (vtrava, vtravr) (ta ** rest) | prf | prf' =
          rewrite prf' in (rewrite prf in Refl)
    gtraversabledIdentityH _ _ (PMap _ (FS FZ) _) _ _ impossible
    gtraversabledIdentityH _ _ (PMap _ (FS (FS _)) _) _ _ impossible
    gtraversabledIdentityH {a = a} {ix = ix} dr constraintsr (PRec jx kdesc) constraints (rec ** rest) with (gtraversableIdentityH {a = a} {ix = jx} dr constraintsr rec)
      gtraversabledIdentityH {a = a} {ix = ix} dr constraintsr (PRec jx kdesc) constraints (rec ** rest) | prf with (gtraversabledIdentityH {a = a} {ix = ix} dr constraintsr kdesc constraints rest)
        gtraversabledIdentityH {a = a} {ix = ix} dr constraintsr (PRec jx kdesc) constraints (rec ** rest) | prf | prf' =
          replace {P = \w => zipA w (gtraversed {a = a} {ix = ix} dr constraintsr kdesc constraints MkIdentity rest) = MkIdentity (rec ** rest)} (sym prf) $
            replace {P = \w => zipA (MkIdentity rec) w = MkIdentity (rec ** rest)} (sym prf') $ Refl


    gtraversableIdentityH : {a,Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                            -> {ix : Ix} -> (X : PData d a ix) -> gtraverse d constraints MkIdentity X = MkIdentity X
    gtraversableIdentityH d constraints (Con x) with (assert_total $ gtraversabledIdentityH d constraints d constraints x)
      gtraversableIdentityH d constraints (Con x) | prf = rewrite prf in Refl

  gtraversableIdentity : {Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                                   -> gtraverse d constraints MkIdentity = MkIdentity
  gtraversableIdentity d constraints = funext (gtraversableIdentityH d constraints)
{-
  mutual
  -- Find correct specification
   gtraversabledCompositionH : (Applicative f, Applicative g) => {a,b,c,Ix: _} -> (dr: PDesc 1 Ix) -> (constraintsr: PConstraints1 VTraversable dr)
                              -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                              -> {ix : Ix} -> (k : Compose f g (PSynthesize d c (PData dr c) ix) -> Compose f g (PData dr c ix))
                              -> (kf : f (PSynthesize d b (PData dr b) ix) -> f (PData dr b ix))
                              -> (h: a -> f b) -> (i : b -> g c)
                              -> (X : PSynthesize d a (PData dr a) ix)
                              -> gtraversed dr constraintsr d constraints k (MkCompose {f = f} {g = g} . map {f = f} i . h) X =
                                 MkCompose . map {f = f} (gtraverse dr constraintsr i) . gtraversed dr constraintsr d constraints kf h $ X
   gtraversabledCompositionH dr constraintsr (PRet ix) constraints k kf h i Refl = ?pp
   gtraversabledCompositionH dr constraintsr (PArg A kdesc) constraints k kf h i X = ?gtraversabledCompositionH_rhs_2
   gtraversabledCompositionH dr constraintsr (PPar FZ kdesc) constraints k kf h i X = ?gtraversabledCompositionH_rhs_6
   gtraversabledCompositionH _ _ (PPar (FS FZ) _) _ _ _ _ _ _ impossible
   gtraversabledCompositionH _ _ (PPar (FS (FS _)) _) _ _ _ _ _ _ impossible
   gtraversabledCompositionH dr constraintsr (PMap t FZ kdesc) constraints k kf h i X = ?gtraversabledCompositionH_rhs_3
   gtraversabledCompositionH _ _ (PMap _ (FS FZ) _) _ _ _ _ _ _ impossible
   gtraversabledCompositionH _ _ (PMap _ (FS (FS _)) _) _ _ _ _ _ _ impossible
   gtraversabledCompositionH dr constraintsr (PRec ix kdesc) constraints k kf h i X = ?gtraversabledCompositionH_rhs_5

   gtraversableCompositionH :(Applicative f, Applicative g) => {a,b,c,Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                            -> (h : a -> f b) -> (i : b -> g c) -> {ix : Ix} -> (X : PData d a ix)
                            -> gtraverse d constraints (MkCompose {f = f} {g = g} . map i . h) X = MkCompose . map (gtraverse d constraints i) . gtraverse d constraints h $ X
   gtraversableCompositionH d constraints h i (Con x) = ?p -- gtraversabledCompositionH d constraints d constraints (Con <$>) (Con <$>) h i x

  gtraversableComposition : (Applicative f, Applicative g) => {a, b, c, Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                           -> (h : a -> f b) -> (i : b -> g c) -> gtraverse d constraints (MkCompose {f = f} {g = g} . map i . h) = MkCompose . map (gtraverse d constraints i) . gtraverse d constraints h
  gtraversableComposition d constraints h i = funext (gtraversableCompositionH d constraints h i)
-}
