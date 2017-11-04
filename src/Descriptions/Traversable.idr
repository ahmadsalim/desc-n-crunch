module Descriptions.Traversable

import Descriptions.Core
import Interfaces
import Syntax.PreorderReasoning

%default total
%access export
%auto_implicits off

using (f: Type -> Type, g: Type -> Type)
  zipD : {a, b : _} -> a -> b -> (x : a ** b)
  zipD x y = (x ** y)

  zipA : Applicative g => {a, b: _} -> g a -> g b -> g (x : a ** b)
  zipA {a} {b} x y = zipD <$> x <*> y

  mutual
    gtraversed : Applicative g => {a,b,Ix: _} -> (dr: PDesc (S Z) Ix) -> (constraintsr: PConstraints1 VTraversable dr)
                                              -> (d: PDesc (S Z) Ix) -> (constraints: PConstraints1 VTraversable d) -> {ix : Ix}
                                              -> (f: a -> g b) -> PSynthesize d a (PData dr a) ix -> g (PSynthesize d b (PData dr b) ix)
    gtraversed _ _ (PRet _) _ _ Refl = pure Refl
    gtraversed dr constraintsr (PArg _ kdesc) constraints f (arg ** rest) with (gtraversed dr constraintsr (kdesc arg) (constraints arg) f rest)
      gtraversed dr constraintsr (PArg _ kdesc) constraints f (arg ** rest) | grest = pure (MkDPair arg) <*> grest
    gtraversed {a = a} dr constraintsr (PPar FZ kdesc) constraints f (p ** rest) with (gtraversed dr constraintsr kdesc constraints f rest)
      gtraversed {a = a} dr constraintsr (PPar FZ kdesc) constraints f (p ** rest) | grest = zipA (f p) grest
    gtraversed _ _ (PPar (FS FZ) _) _ _ _ impossible
    gtraversed _ _ (PPar (FS (FS _)) _) _ _ _ impossible
    gtraversed dr constraintsr (PMap _ FZ kdesc) (vtrava, vtravr) f (ta ** rest) with (gtraversed dr constraintsr kdesc vtravr f rest)
      gtraversed dr constraintsr (PMap _ FZ kdesc) (vtrava, vtravr) f (ta ** rest) | grest = zipA (traverse f ta) grest
    gtraversed _ _ (PMap _ (FS FZ) _) _ _ _ impossible
    gtraversed _ _ (PMap _ (FS (FS _)) _) _ _ _ impossible
    gtraversed dr constraintsr (PRec _ kdesc) constraints f (rec ** rest) with (gtraverse dr constraintsr f rec)
      gtraversed dr constraintsr (PRec _ kdesc) constraints f (rec ** rest) | grec with (gtraversed dr constraintsr kdesc constraints f rest)
        gtraversed dr constraintsr (PRec _ kdesc) constraints f (rec ** rest) | grec | grest = zipA grec grest


    gtraverse  : Applicative g => {a,b,Ix: _} -> (d: PDesc (S Z) Ix) -> (PConstraints1 VTraversable d) -> {ix : Ix}
                                              -> (f: a -> g b) -> PData d a ix -> g (PData d b ix)
    gtraverse d constraints f (Con x) = assert_total $ pure Con <*> gtraversed d constraints d constraints f x

{-
  mutual
    gtraversabledIdentityH : {a,Ix: _} -> (dr: PDesc 1 Ix) -> (constraintsr: PConstraints1 VTraversable dr)
                                       -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                                      -> {ix : Ix} ->(X : PSynthesize d a (PData dr a) ix)
                                      -> gtraversed {g = Identity} dr constraintsr d constraints MkIdentity X = MkIdentity X
    gtraversabledIdentityH dr constraintsr (PRet ix) constraints Refl = Refl
    gtraversabledIdentityH {a = a} {ix} dr constraintsr (PArg A kdesc) constraints (arg ** rest) with (gtraversabledIdentityH dr constraintsr (kdesc arg) (constraints arg) rest)
      gtraversabledIdentityH {a = a} {ix} dr constraintsr (PArg A kdesc) constraints (arg ** rest) | prf =
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
    gtraversabledIdentityH {a = a} {ix} dr constraintsr (PRec jx kdesc) constraints (rec ** rest) with (gtraversableIdentityH {a = a} {ix = jx} dr constraintsr rec)
      gtraversabledIdentityH {a = a} {ix} dr constraintsr (PRec jx kdesc) constraints (rec ** rest) | prf with (gtraversabledIdentityH {a = a} {ix} dr constraintsr kdesc constraints rest)
        gtraversabledIdentityH {a = a} {ix} dr constraintsr (PRec jx kdesc) constraints (rec ** rest) | prf | prf' =
          replace {P = \w => zipA w (gtraversed {a = a} {ix} dr constraintsr kdesc constraints MkIdentity rest) = MkIdentity (rec ** rest)} (sym prf) $
            replace {P = \w => zipA (MkIdentity rec) w = MkIdentity (rec ** rest)} (sym prf') $ Refl


    gtraversableIdentityH : {a,Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                            -> {ix : Ix} -> (X : PData d a ix) -> gtraverse d constraints MkIdentity X = MkIdentity X
    gtraversableIdentityH d constraints (Con x) with (assert_total $ gtraversabledIdentityH d constraints d constraints x)
      gtraversableIdentityH d constraints (Con x) | prf = rewrite prf in Refl

  gtraversableIdentity : {Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                                   -> gtraverse d constraints MkIdentity = MkIdentity
  gtraversableIdentity d constraints = funext (gtraversableIdentityH d constraints)
-}

{-
  composeTraverseConLemma : (VApplicative f, VApplicative g) => {a,b,c,Ix: _} ->
    (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d) ->
   {ix : Ix} -> (h: a -> f b) -> (i : b -> g c) -> (x : PSynthesize d a (PData d a) ix) ->
    (MkCompose {f} {g} (pure (<*>) <*> pure (pure Con) <*> map (gtraversed d constraints d constraints i) (gtraversed d constraints d constraints h x)) = MkCompose {f} {g} (map (gtraverse d constraints i) (pure (Con {ix}) <*> gtraversed d constraints d constraints h x)))
  composeTraverseConLemma d constraints {f} {g} {ix} h i x = ?p
     {-   (MkCompose {f} {g} (pure (<*>) <*> pure (pure Con) <*> map (gtraversed d constraints d constraints i) (gtraversed d constraints d constraints h x)))
          ={ cong {f = (\r => MkCompose (r <*>  map (gtraversed d constraints d constraints i) (gtraversed d constraints d constraints h x))) } applicativeHomomorphism }=
        (MkCompose {f} {g} (pure ((pure Con) <*>) <*> map (gtraversed {ix} d constraints d constraints i) (gtraversed {ix} d constraints d constraints h x)))
          ={ cong {f = (\r => MkCompose (r (map {f} (gtraversed d constraints d constraints i) (gtraversed d constraints d constraints h x) )) )} (sym applicativeMap) }=
        (MkCompose {f} {g} (map ((pure Con) <*>) (map (gtraversed {ix} d constraints d constraints i) (gtraversed {ix} d constraints d constraints h x))))
          ={ cong {f = MkCompose} (fundet (sym mapCompose) (gtraversed d constraints d constraints h x)) }=
        (MkCompose {f} {g} (map (((pure Con) <*>) . (gtraversed {ix} d constraints d constraints i)) (gtraversed {ix} d constraints d constraints h x)))
          ={ Refl }=
        (MkCompose {f} {g} (map (gtraverse {ix} d constraints i . Con {ix}) (gtraversed {ix} d constraints d constraints h x)))
          ={ cong {f = MkCompose} (fundet (mapCompose {f} {g = gtraverse {ix} d constraints i} {h = Con {ix}} ) ( (gtraversed {ix} d constraints d constraints h x) ) ) }=
        (MkCompose {f} {g} (map (gtraverse {ix} d constraints i) (map (Con {ix}) (gtraversed {ix} d constraints d constraints h x))))
          ={ cong {f = \r => MkCompose ((map (gtraverse d constraints i)) r) } (fundet applicativeMap (gtraversed {ix} d constraints d constraints h x)) }=
        (MkCompose {f} {g} (map (gtraverse {ix} d constraints i) (pure (Con {ix}) <*> gtraversed d constraints d constraints h x)))
          QED -}

  mutual
   gtraversabledCompositionH : (VApplicative f, VApplicative g) => {a,b,c,Ix: _} -> (dr: PDesc 1 Ix) -> (constraintsr: PConstraints1 VTraversable dr)
                              -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                              -> {ix : Ix} -> (h: a -> f b) -> (i : b -> g c)
                              -> (X : PSynthesize d a (PData dr a) ix)
                              -> gtraversed dr constraintsr d constraints (MkCompose {f} {g} . map {f} i . h) X =
                                 MkCompose . map {f} (gtraversed dr constraintsr d constraints i) . gtraversed dr constraintsr d constraints h $ X
   gtraversabledCompositionH {a} {b} {ix} {g} {f} dr constraintsr (PRet ix) constraints h i Refl with (applicativeMap {f} {a = PSynthesize (PRet {n = 1} ix) b (PData (PRet {n = 1} ix) b) ix} {u = gtraversed {ix} dr constraintsr (PRet ix) constraints i})
     gtraversabledCompositionH {a} {f} {g} {ix} dr constraintsr (PRet ix) constraints h i Refl | prf =
       replace {P = \r => MkCompose (pure {f} (pure {f = g} {a = (ix = ix)} Refl)) = MkCompose (r (pure Refl))} (sym prf)
        (replace {P = \r => MkCompose (pure {f} (pure {f = g} {a = (ix = ix)} Refl)) = MkCompose r} (sym (applicativeHomomorphism {f} {g = gtraversed dr constraintsr (PRet ix) constraints i} {x = Refl} )) Refl)
   gtraversabledCompositionH {c = c} {f} {g} {ix} dr constraintsr (PArg A kdesc) constraints h i (arg ** rest) with (gtraversabledCompositionH dr constraintsr (kdesc arg) (constraints arg) h i rest)
     gtraversabledCompositionH {c = c} {f} {g} {ix} dr constraintsr (PArg A kdesc) constraints h i (arg ** rest) | prf = ?admit
      {- replace {P = \r => (MkCompose {f} {g} (pure (pure (MkDPair {P = \arg => PSynthesize (kdesc arg) c (PData dr c) ix } arg)))) <*> r =
                              MkCompose (map {f} (gtraversed {g} dr constraintsr (PArg A kdesc) constraints i) (pure (MkDPair arg) <*>
                                          (gtraversed dr constraintsr (kdesc arg) (constraints arg) h rest)))} (sym prf) (
          (MkCompose {f} {g} (pure (<*>) <*>
                                            pure (pure (MkDPair arg)) <*>
                                                   map (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) i)
                                                        (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) h rest)))
            ={ cong {f = \r => MkCompose (r <*> (map (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) i)
                    (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) h rest))) } applicativeHomomorphism }=
          (MkCompose {f} {g} (pure ((pure (MkDPair arg)) <*>) <*>
                                                    map (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) i)
                                                    (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) h rest)))
            ={ cong {f = \r => MkCompose (r ( map (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) i)
                    (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) h rest) ))  } (sym applicativeMap) }=
          (MkCompose {f} {g} (map ((pure (MkDPair arg)) <*>) (
                                                    map (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) i)
                                                    (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) h rest))))

            ={ cong {f = MkCompose} (fundet (sym mapCompose) (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) h rest)) }=
          (MkCompose {f} {g} (map ( ((pure (MkDPair arg)) <*>) . gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) i)
                                                    (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) h rest)))
            ={ Refl }=
          (MkCompose {f} {g} (map (gtraversed {ix} dr constraintsr (PArg A kdesc) constraints i . MkDPair arg)
                                          (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) h rest)))
            ={ cong {f = MkCompose} (fundet mapCompose (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) h rest) ) }=
          (MkCompose {f} {g} (map (gtraversed {ix} dr constraintsr (PArg A kdesc) constraints i)
                                      (map (MkDPair arg) (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) h rest))))
            ={ cong {f = (\r => MkCompose ((map (gtraversed {ix} dr constraintsr (PArg A kdesc) constraints i) (r (gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) h rest)) ))) } applicativeMap }=
          (MkCompose {f} {g} (map (gtraversed {ix} dr constraintsr (PArg A kdesc) constraints i)
                                      (pure (MkDPair arg) <*> gtraversed {ix} dr constraintsr (kdesc arg) (constraints arg) h rest)))
            QED) -}
   gtraversabledCompositionH dr constraintsr (PPar FZ kdesc) constraints h i (par ** rest) with (gtraversabledCompositionH dr constraintsr kdesc constraints h i rest)
     gtraversabledCompositionH dr constraintsr (PPar FZ kdesc) constraints h i (par ** rest) | prf =
       rewrite prf in ?gtraversabledCompositionH_rhs
   gtraversabledCompositionH _ _ (PPar (FS FZ) _) _ _ _ _ impossible
   gtraversabledCompositionH _ _ (PPar (FS (FS _)) _) _ _ _ _ impossible
   gtraversabledCompositionH dr constraintsr (PMap f FZ kdesc) constraints h i X = ?gtraversabledCompositionH_rhs_3
   gtraversabledCompositionH _ _ (PMap _ (FS FZ) _) _ _ _ _ impossible
   gtraversabledCompositionH _ _ (PMap _ (FS (FS _)) _) _ _ _ _ impossible
   gtraversabledCompositionH dr constraintsr (PRec ix kdesc) constraints h i X = ?gtraversabledCompositionH_rhs_5

   gtraversableCompositionH :(VApplicative f, VApplicative g) => {a,b,c,Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d)
                            -> (h : a -> f b) -> (i : b -> g c) -> {ix : Ix} -> (X : PData d a ix)
                            -> gtraverse d constraints (MkCompose {f} {g} . map i . h) X = MkCompose . map (gtraverse d constraints i) . gtraverse d constraints h $ X
   gtraversableCompositionH {f} {g} {ix} d constraints h i (Con {ix} x) with (assert_total $ gtraversabledCompositionH d constraints d constraints h i x)
     gtraversableCompositionH {f} {g} {ix} d constraints h i (Con {ix} x) | prf =
       rewrite prf in composeTraverseConLemma d constraints h i x

  gtraversableComposition : (VApplicative f, VApplicative g) => {a, b, c, Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d) ->
                            (h : a -> f b) -> (i : b -> g c) ->
                            gtraverse d constraints (MkCompose {f} {g} . map i . h) = MkCompose . map (gtraverse d constraints i) . gtraverse d constraints h
  gtraversableComposition d constraints h i = funext (gtraversableCompositionH d constraints h i)
-}

  mutual
    gtraversabledNaturalityH : (VApplicativeTransformer f g) =>
                                  {a, b, Ix: _} ->
                                  (dr: PDesc 1 Ix) -> (constraintsr: PConstraints1 VTraversable dr) ->
                                  (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d) ->
                                  (h: a -> f b) -> {ix : Ix} -> (X : PSynthesize d a (PData dr a) ix) ->
                                  transformA {f} {g} (gtraversed dr constraintsr d constraints h X) =
                                    gtraversed {g = g} dr constraintsr d constraints (transformA {f} {g} . h) X
    gtraversabledNaturalityH {f = f} {g = g} dr constraintsr (PRet ix) constraints h Refl = transformAPure {f} {g} {a=(ix=ix)} {x=Refl}
    gtraversabledNaturalityH dr constraintsr (PArg A kdesc) constraints h X = ?gtraversableNaturalityH_rhs_3
    gtraversabledNaturalityH dr constraintsr (PPar k kdesc) constraints h X = ?gtraversableNaturalityH_rhs_4
    gtraversabledNaturalityH dr constraintsr (PMap f k kdesc) constraints h X = ?gtraversableNaturalityH_rhs_5
    gtraversabledNaturalityH dr constraintsr (PRec ix kdesc) constraints h X = ?gtraversableNaturalityH_rhs_6

    gtraversableNaturalityH : (VApplicativeTransformer f g) =>
                                {a, b, Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d) ->
                                (h: a -> f b) -> {ix : Ix} -> (X : PData d a ix) ->
                                transformA {f} {g} (gtraverse d constraints h X) = gtraverse d constraints (transformA {f} {g} . h) X
    gtraversableNaturalityH d constraints h X = ?gtraversableNaturalityH_rhs

  gtraversableNaturality : (VApplicativeTransformer f g) =>
                           {a, b, Ix: _} -> (d: PDesc 1 Ix) -> (constraints: PConstraints1 VTraversable d) -> (h: a -> f b) ->
                           transformA {f} {g} . gtraverse d constraints h = gtraverse d constraints (transformA {f} {g} . h)
  gtraversableNaturality {f} {g} d constraints h = funext (\X => gtraversableNaturalityH {f} {g} d constraints h X)
