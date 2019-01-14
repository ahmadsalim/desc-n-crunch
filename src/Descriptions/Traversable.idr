module Descriptions.Traversable

import Descriptions.Core
import Interfaces
import Syntax.PreorderReasoning

%default total
%access export
%auto_implicits off

using (f: Type -> Type, g: Type -> Type)
  vapt2apF : VApplicativeTransformer f g -> Applicative f
  vapt2apF vappt = %implementation

  vapt2apG : VApplicativeTransformer f g -> Applicative g
  vapt2apG vappt = %implementation

  vap2ap : VApplicative f -> Applicative f
  vap2ap vapp = %implementation

  ap2fun : Applicative f -> Functor f
  ap2fun ap = %implementation

  zipD : {a, b : _} -> a -> b -> (x : a ** b)
  zipD x y = (x ** y)

  zipA : Applicative g => {a, b: _} -> g a -> g b -> g (x : a ** b)
  zipA {a} {b} x y = zipD <$> x <*> y

  mutual
    gtraversed : Applicative g =>
                  {a,b,Ix: _} -> (dR: PDesc (S Z) Ix) -> (cstrsR: PConstraints1 VTraversable dR)
                              -> (d: PDesc (S Z) Ix) -> (cstrs: PConstraints1 VTraversable d)
                 -> {ix : Ix} -> (f: a -> g b) -> PSynthesize d a (PData dR a) ix
                              -> g (PSynthesize d b (PData dR b) ix)
    gtraversed _  _      (PRet _)               _                _ Refl          = pure Refl
    gtraversed dR cstrsR (PArg _ kdesc)         cstrs            f (arg ** rest) = pure (MkDPair arg) <*> (gtraversed dR cstrsR (kdesc arg) (cstrs arg) f rest)
    gtraversed dR cstrsR (PPar FZ kdesc)        cstrs            f (p ** rest)   = zipA (f p) (gtraversed dR cstrsR kdesc cstrs f rest)
    gtraversed _  _      (PPar (FS FZ)     _)   _                _ _ impossible
    gtraversed _  _      (PPar (FS (FS _)) _)   _                _ _ impossible
    gtraversed dR cstrsR (PMap _ FZ kdesc)      (vtrava, vtravr) f (ta ** rest)  = zipA (traverse f ta) (gtraversed dR cstrsR kdesc vtravr f rest)
    gtraversed _  _      (PMap _ (FS FZ)     _) _                _ _ impossible
    gtraversed _  _      (PMap _ (FS (FS _)) _) _                _ _ impossible
    gtraversed dR cstrsR (PRec _ kdesc)         cstrs            f (rec ** rest) = zipA (gtraverse dR cstrsR f rec) (gtraversed dR cstrsR kdesc cstrs f rest)

    gtraverse : Applicative g => {a,b,Ix: _} -> (d: PDesc (S Z) Ix) -> (PConstraints1 VTraversable d) -> {ix : Ix}
                                             -> (f: a -> g b) -> PData d a ix -> g (PData d b ix)
    gtraverse d cstrs f (Con x) = assert_total $ pure Con <*> gtraversed d cstrs d cstrs f x

  mutual
    gtraversabledIdentityH : {a,Ix: _} -> (dR: PDesc 1 Ix) -> (cstrsR: PConstraints1 VTraversable dR)
                                       -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VTraversable d)
                          -> {ix : Ix} -> (X : PSynthesize d a (PData dR a) ix)
                                       -> gtraversed {g = Identity} dR cstrsR d cstrs MkIdentity X = MkIdentity X
    gtraversabledIdentityH _ _ (PRet _) _ Refl = Refl
    gtraversabledIdentityH {a} {ix} dR cstrsR (PArg _ kdesc) cstrs (arg ** rest) with (gtraversabledIdentityH dR cstrsR (kdesc arg) (cstrs arg) rest)
      gtraversabledIdentityH {a} {ix} dR _ (PArg _ kdesc) _ (arg ** rest) | prf =
        replace {P = \w => pure {f = Identity} (MkDPair {P = \ag => PSynthesize (kdesc ag) a (PData dR a) ix} arg) <*> w = MkIdentity (arg ** rest)} (sym prf) Refl
    gtraversabledIdentityH dR cstrsR (PPar FZ kdesc) cstrs (p ** rest) with (gtraversabledIdentityH dR cstrsR kdesc cstrs rest)
      gtraversabledIdentityH _ _ (PPar FZ _) _ (_ ** _) | prf = rewrite prf in Refl
    gtraversabledIdentityH _ _ (PPar (FS FZ) _) _ _ impossible
    gtraversabledIdentityH _ _ (PPar (FS (FS _)) _) _ _ impossible
    gtraversabledIdentityH {a} dR cstrsR (PMap f FZ kdesc) (vtrava, vtravr) (ta ** rest) with (fundet (traversableIdentity {t = f} {a}) ta)
      gtraversabledIdentityH {a} dR cstrsR (PMap f FZ kdesc) (vtrava, vtravr) (ta ** rest) | prf with (gtraversabledIdentityH dR cstrsR kdesc vtravr rest)
        gtraversabledIdentityH {a} dR cstrsR (PMap f FZ kdesc) (vtrava, vtravr) (ta ** rest) | prf | prf' =
          rewrite prf' in
          rewrite prf in
          Refl
    gtraversabledIdentityH _ _ (PMap _ (FS FZ) _) _ _ impossible
    gtraversabledIdentityH _ _ (PMap _ (FS (FS _)) _) _ _ impossible
    gtraversabledIdentityH {a} {ix} dR cstrsR (PRec jx kdesc) cstrs (rec ** rest) with (gtraversableIdentityH {a} {ix = jx} dR cstrsR rec)
      gtraversabledIdentityH {a} {ix} dR cstrsR (PRec jx kdesc) cstrs (rec ** rest) | prf with (gtraversabledIdentityH {a} {ix} dR cstrsR kdesc cstrs rest)
        gtraversabledIdentityH {a} {ix} dR cstrsR (PRec jx kdesc) cstrs (rec ** rest) | prf | prf' =
          replace {P = \w => zipA w (gtraversed {a} {ix} dR cstrsR kdesc cstrs MkIdentity rest) = MkIdentity (rec ** rest)} (sym prf) $
          replace {P = \w => zipA (MkIdentity rec) w = MkIdentity (rec ** rest)} (sym prf') $
          Refl

    gtraversableIdentityH : {a,Ix: _} -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VTraversable d)
                         -> {ix : Ix} -> (X : PData d a ix)
                                      -> gtraverse d cstrs MkIdentity X = MkIdentity X
    gtraversableIdentityH d cstrs (Con x) with (assert_total $ gtraversabledIdentityH d cstrs d cstrs x)
      gtraversableIdentityH _ _ (Con _) | prf = rewrite prf in Refl

  gtraversableIdentity : {Ix: _} -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VTraversable d)
                                 -> gtraverse d cstrs MkIdentity = MkIdentity
  gtraversableIdentity d cstrs = funext (gtraversableIdentityH d cstrs)

  composeTraverseConLemma : (VApplicative f, VApplicative g) =>
                            {a,b,c,Ix: _} -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VTraversable d)
                         -> {ix : Ix} -> (h: a -> f b) -> (i : b -> g c) -> (x : PSynthesize d a (PData d a) ix)
                         -> MkCompose {f} {g} (pure (<*>) <*> pure (pure Con) <*> map (gtraversed d cstrs d cstrs i) (gtraversed d cstrs d cstrs h x)) =
                              MkCompose {f} {g} (map (gtraverse d cstrs i) (pure (Con {ix}) <*> gtraversed d cstrs d cstrs h x))
  composeTraverseConLemma d cstrs {f} {g} {ix} h i x =
    (MkCompose {f} {g} (pure (<*>) <*> pure (pure Con) <*> map (gtraversed d cstrs d cstrs i) (gtraversed d cstrs d cstrs h x)))
      ={ cong {f = (\r => MkCompose (r <*>  map (gtraversed d cstrs d cstrs i) (gtraversed d cstrs d cstrs h x))) } applicativeHomomorphism }=
    (MkCompose {f} {g} (pure ((pure Con) <*>) <*> map (gtraversed {ix} d cstrs d cstrs i) (gtraversed {ix} d cstrs d cstrs h x)))
      ={ cong {f = (\r => MkCompose (r (map {f} (gtraversed d cstrs d cstrs i) (gtraversed d cstrs d cstrs h x) )) )} (sym applicativeMap) }=
    (MkCompose {f} {g} (map ((pure Con) <*>) (map (gtraversed {ix} d cstrs d cstrs i) (gtraversed {ix} d cstrs d cstrs h x))))
      ={ cong {f = MkCompose} (fundet (sym mapCompose) (gtraversed d cstrs d cstrs h x)) }=
    (MkCompose {f} {g} (map (((pure Con) <*>) . (gtraversed {ix} d cstrs d cstrs i)) (gtraversed {ix} d cstrs d cstrs h x)))
      ={ Refl }=
    (MkCompose {f} {g} (map (gtraverse {ix} d cstrs i . Con {ix}) (gtraversed {ix} d cstrs d cstrs h x)))
      ={ cong {f = MkCompose} (fundet (mapCompose {f} {g = gtraverse {ix} d cstrs i} {h = Con {ix}} ) ( (gtraversed {ix} d cstrs d cstrs h x) ) ) }=
    (MkCompose {f} {g} (map (gtraverse {ix} d cstrs i) (map (Con {ix}) (gtraversed {ix} d cstrs d cstrs h x))))
      ={ cong {f = \r => MkCompose ((map (gtraverse d cstrs i)) r) } (fundet applicativeMap (gtraversed {ix} d cstrs d cstrs h x)) }=
    (MkCompose {f} {g} (map (gtraverse {ix} d cstrs i) (pure (Con {ix}) <*> gtraversed d cstrs d cstrs h x)))
      QED

  mutual
   gtraversabledCompositionH : (VApplicative f, VApplicative g) =>
                               {a,b,c,Ix: _} -> (dR: PDesc 1 Ix) -> (cstrsR: PConstraints1 VTraversable dR)
                                             -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VTraversable d)
                                -> {ix : Ix} -> (h: a -> f b) -> (i : b -> g c)
                                             -> (X : PSynthesize d a (PData dR a) ix)
                                             -> gtraversed dR cstrsR d cstrs (MkCompose {f} {g} . map {f} i . h) X =
                                                  MkCompose . map {f} (gtraversed dR cstrsR d cstrs i) . gtraversed dR cstrsR d cstrs h $ X
   gtraversabledCompositionH {a} {b} {ix} {g} {f} dR cstrsR (PRet ix) cstrs h i Refl with (applicativeMap {f} {a = PSynthesize (PRet {n=1} ix) b (PData (PRet {n=1} ix) b) ix} {u = gtraversed {ix} dR cstrsR (PRet ix) cstrs i})
     gtraversabledCompositionH {a} {f} {g} {ix} dR cstrsR (PRet ix) cstrs h i Refl | prf =
       replace {P = \r => MkCompose (pure {f} (pure {f=g} {a=(ix=ix)} Refl)) = MkCompose (r (pure Refl))} (sym prf) $
       replace {P = \r => MkCompose (pure {f} (pure {f=g} {a=(ix=ix)} Refl)) = MkCompose r} (sym $ applicativeHomomorphism {f} {g = gtraversed dR cstrsR (PRet ix) cstrs i} {x = Refl}) $
       Refl
   gtraversabledCompositionH {c} {f} {g} {ix} dR cstrsR (PArg a kdesc) cstrs h i (arg ** rest) with (gtraversabledCompositionH dR cstrsR (kdesc arg) (cstrs arg) h i rest)
     gtraversabledCompositionH {c} {f} {g} {ix} dR cstrsR (PArg a kdesc) cstrs h i (arg ** rest) | prf =
      replace {P = \r => (MkCompose {f} {g} (pure (pure (MkDPair {P = \arg => PSynthesize (kdesc arg) c (PData dR c) ix } arg)))) <*> r =
                          MkCompose (map {f} (gtraversed {g} dR cstrsR (PArg a kdesc) cstrs i)
                                       (pure (MkDPair arg) <*> (gtraversed dR cstrsR (kdesc arg) (cstrs arg) h rest)))} (sym prf) $
        (MkCompose {f} {g} $ pure (<*>) <*>
                               pure (pure (MkDPair arg)) <*>
                                 map (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) i)
                                   (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest))
          ={ cong {f = \r => MkCompose $ r <*> (map (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) i)
                                                  (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest)) } $
             applicativeHomomorphism }=
        (MkCompose {f} {g} (pure ((pure (MkDPair arg)) <*>) <*>
                              map (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) i)
                                (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest)))
          ={ cong {f = \r => MkCompose $ r (map (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) i)
                                             (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest))} $
             sym applicativeMap }=
        (MkCompose {f} {g} $ map ((pure (MkDPair arg)) <*>)
                               (map (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) i)
                                  (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest)))
          ={ cong {f = MkCompose} $
             fundet (sym mapCompose) (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest) }=
        (MkCompose {f} {g} $ map (((pure (MkDPair arg)) <*>) . gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) i)
                               (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest))
          ={ Refl }=
        (MkCompose {f} {g} $ map (gtraversed {ix} dR cstrsR (PArg a kdesc) cstrs i . MkDPair arg)
                               (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest))
          ={ cong {f = MkCompose} $
             fundet mapCompose (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest) }=
        (MkCompose {f} {g} $ map (gtraversed {ix} dR cstrsR (PArg a kdesc) cstrs i)
                               (map (MkDPair arg) (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest)))
          ={ cong {f = \r => MkCompose $ map (gtraversed {ix} dR cstrsR (PArg a kdesc) cstrs i)
                                            (r (gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest)) }
             applicativeMap }=
        (MkCompose {f} {g} $ map (gtraversed {ix} dR cstrsR (PArg a kdesc) cstrs i)
                               (pure (MkDPair arg) <*> gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest))
          QED
   gtraversabledCompositionH {f} {g} {c} @{af} @{ag} {ix} dR cstrsR (PPar FZ kdesc) cstrs h i (par ** rest) =
     ((<*>) @{the (Applicative (Compose f g)) %implementation}
            (MkCompose (map {f} @{ap2fun {f} $ vap2ap {f} af} (map {f=g} @{ap2fun {f=g} $ vap2ap {f=g} ag} zipD) (map i (h par))))
            (gtraversed {ix} dR cstrsR kdesc cstrs (\x => MkCompose {f} {g} (map i (h x))) rest))
       ={ cong {f=\z=> MkCompose (map {f} @{ap2fun {f} $ vap2ap {f} af} (map {f=g} @{ap2fun {f=g} $ vap2ap {f=g} ag} zipD) (map i (h par))) <*> z} $
          gtraversabledCompositionH dR cstrsR kdesc cstrs h i rest }=
     (MkCompose (pure (<*>) <*>
                   map {f} @{ap2fun {f} $ vap2ap {f} af} (map {f=g} @{ap2fun {f=g} $ vap2ap {f=g} ag} zipD) (map i (h par)) <*>
                     map (gtraversed {ix} dR cstrsR kdesc cstrs i) (gtraversed {ix} dR cstrsR kdesc cstrs h rest)))
        ={ rewrite sym $ applicativeVFunctorCoherence {f} in Refl }=
     (MkCompose (pure (<*>) <*>
                   map {f} (map {f=g} @{ap2fun {f=g} $ vap2ap {f=g} ag} zipD) (map i (h par)) <*>
                     map (gtraversed {ix} dR cstrsR kdesc cstrs i) (gtraversed {ix} dR cstrsR kdesc cstrs h rest)))
        ={ rewrite sym $ applicativeVFunctorCoherence {f=g} in Refl }=
     (MkCompose (pure (<*>) <*>
                   map {f} (map {f=g} zipD) (map i (h par)) <*>
                     map (gtraversed {ix} dR cstrsR kdesc cstrs i) (gtraversed {ix} dR cstrsR kdesc cstrs h rest)))
       ={ cong {f=\z=> MkCompose $ pure (<*>) <*>
                                     map {f} (map {f=g} zipD) (map i (h par)) <*>
                                       z (gtraversed {ix} dR cstrsR kdesc cstrs h rest)} $
          applicativeMap }=
     (MkCompose (pure (<*>) <*>
                   map {f} (map {f=g} zipD) (map i (h par)) <*>
                     (pure (gtraversed {ix} dR cstrsR kdesc cstrs i) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest)))
       ={ cong {f=\z=> MkCompose $ (<*>) {f} {b = g (x : c ** Synthesize (PDescToDesc $ PUnfold kdesc c) (Data $ PDescToDesc $ PUnfold dR c) ix)}
                                      (z $ map {f} (map {f=g} zipD) (map i (h par)))
                                      (pure (gtraversed {ix} dR cstrsR kdesc cstrs i) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest)} $
          sym $ applicativeMap {u=(<*>)} }=
     (MkCompose (map {f} (<*>) (map {f} (map {f=g} zipD) (map i (h par))) <*>
                   (pure (gtraversed {ix} dR cstrsR kdesc cstrs i) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest)))
       ={ cong {f=MkCompose} $
           sym $ applicativeCompose {u=map {f} (<*>) (map {f} (map {f=g} zipD) (map i (h par)))}
                                    {v=pure (gtraversed {ix} dR cstrsR kdesc cstrs i)}
                                    {w=gtraversed {ix} dR cstrsR kdesc cstrs h rest} }=
     (MkCompose (pure (.) <*>
                   map {f} (<*>) (map {f} (map {f=g} zipD) (map i (h par))) <*>
                     pure (gtraversed {ix} dR cstrsR kdesc cstrs i) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest))
       ={ cong {f=\z=> MkCompose $ z (map {f} (<*>) (map {f} (map {f=g} zipD) (map i (h par)))) <*>
                                     pure (gtraversed {ix} dR cstrsR kdesc cstrs i) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest} $
          sym $ applicativeMap {u=(.)} }=
     (MkCompose (map (.) (map {f} (<*>) (map {f} (map {f=g} zipD) (map i (h par)))) <*>
                     pure (gtraversed {ix} dR cstrsR kdesc cstrs i) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest))
       ={ cong {f=\z=> MkCompose $ z <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest} $
          applicativeInterchange {u=map (.) (map {f} (<*>) (map {f} (map {f=g} zipD) (map i (h par))))}
                                 {y=gtraversed {ix} dR cstrsR kdesc cstrs i} }=
     (MkCompose (pure (\g => g $ gtraversed {ix} dR cstrsR kdesc cstrs i) <*>
                   map (.) (map {f} (<*>) (map {f} (map {f=g} zipD) (map i (h par)))) <*>
                     gtraversed {ix} dR cstrsR kdesc cstrs h rest))
       ={ cong {f=\z=> MkCompose $ z (map (.) (map {f} (<*>) (map {f} (map {f=g} zipD) (map i (h par))))) <*>
                                    gtraversed {ix} dR cstrsR kdesc cstrs h rest} $
          sym $ applicativeMap {u=\g => g $ gtraversed {ix} dR cstrsR kdesc cstrs i} }=
     (MkCompose (map (\g => g $ gtraversed {ix} dR cstrsR kdesc cstrs i) (map (.) (map {f} (<*>) (map {f} (map {f=g} zipD) (map i (h par))))) <*>
                     gtraversed {ix} dR cstrsR kdesc cstrs h rest))
       ={ cong {f=\z=> MkCompose $ z (map {f} (<*>) (map {f} (map {f=g} zipD) (map i (h par)))) <*>
                                     gtraversed {ix} dR cstrsR kdesc cstrs h rest} $
          sym $ mapCompose {g=\g => g $ gtraversed {ix} dR cstrsR kdesc cstrs i} {h=(.)} }=
     (MkCompose (map ((\g => g $ gtraversed {ix} dR cstrsR kdesc cstrs i) . (.)) (map {f} (<*>) (map {f} (map {f=g} zipD) (map i (h par)))) <*>
                     gtraversed {ix} dR cstrsR kdesc cstrs h rest))
       ={ cong {f=\z=> MkCompose $ z (map {f} (map {f=g} zipD) (map i (h par))) <*>
                                     gtraversed {ix} dR cstrsR kdesc cstrs h rest} $
          sym $ mapCompose {g=(\g => g $ gtraversed {ix} dR cstrsR kdesc cstrs i) . (.)} {h=(<*>)} }=
     (MkCompose (map ((\g => g $ gtraversed {ix} dR cstrsR kdesc cstrs i) . (.) . (<*>)) (map {f} (map {f=g} zipD) (map i (h par))) <*>
                     gtraversed {ix} dR cstrsR kdesc cstrs h rest))
       ={ cong {f=\z=> MkCompose $ z (map i (h par)) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest} $
          sym $ mapCompose {g=(\g => g $ gtraversed {ix} dR cstrsR kdesc cstrs i) . (.) . (<*>)} {h=map {f=g} zipD} }=
     (MkCompose (map ((\g => g $ gtraversed {ix} dR cstrsR kdesc cstrs i) . (.) . (<*>) . (map {f=g} zipD)) (map i (h par)) <*>
                     gtraversed {ix} dR cstrsR kdesc cstrs h rest))
       ={ cong {f=\z=> MkCompose $ z (h par) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest} $
          sym $ mapCompose {g=(\g => g $ gtraversed {ix} dR cstrsR kdesc cstrs i) . (.) . (<*>) . (map {f=g} zipD)} {h=i} }=
     (MkCompose (map ((\g => g $ gtraversed {ix} dR cstrsR kdesc cstrs i) . (.) . (<*>) . (map {f=g} zipD) . i) (h par) <*>
                     gtraversed {ix} dR cstrsR kdesc cstrs h rest))
       ={ Refl }=
     (MkCompose (map (\p, r => map {f=g} zipD (i p) <*> gtraversed {ix} dR cstrsR kdesc cstrs i r) (h par) <*>
                     gtraversed {ix} dR cstrsR kdesc cstrs h rest))
       ={ ?gtraversabledCompositionH_rhs2 }=
     (MkCompose (pure (.) <*> pure (gtraversed {ix} dR cstrsR (PPar FZ kdesc) cstrs i) <*> map {f} @{ap2fun {f} $ vap2ap {f} af} zipD (h par) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest))
       ={ cong {f = MkCompose} applicativeCompose }=
     (MkCompose (pure (gtraversed {ix} dR cstrsR (PPar FZ kdesc) cstrs i) <*> (map {f} @{ap2fun {f} $ vap2ap {f} af} zipD (h par) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest)))
       ={ cong {f=\z => MkCompose (z (map {f} @{ap2fun {f} $ vap2ap {f} af} zipD (h par) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest))} $
          sym applicativeMap }=
     (MkCompose (map (gtraversed {ix} dR cstrsR (PPar FZ kdesc) cstrs i) (map {f} @{ap2fun {f} $ vap2ap {f} af} zipD (h par) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest)))
       QED
   gtraversabledCompositionH _ _ (PPar (FS FZ) _) _ _ _ _ impossible
   gtraversabledCompositionH _ _ (PPar (FS (FS _)) _) _ _ _ _ impossible
   gtraversabledCompositionH dR cstrsR (PMap f FZ kdesc) (vtrava, vtravr) h i (ta ** rest) = ?gtraversabledCompositionH_rhs_4
   gtraversabledCompositionH _ _ (PMap _ (FS FZ) _) _ _ _ _ impossible
   gtraversabledCompositionH _ _ (PMap _ (FS (FS _)) _) _ _ _ _ impossible
   gtraversabledCompositionH dR cstrsR (PRec ix kdesc) cstrs h i (rec ** rest) = ?gtraversabledCompositionH_rhs_5

   gtraversableCompositionH : (VApplicative f, VApplicative g) =>
                              {a,b,c,Ix: _} -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VTraversable d)
                                            -> (h : a -> f b) -> (i : b -> g c) -> {ix : Ix} -> (X : PData d a ix)
                                            -> gtraverse d cstrs (MkCompose {f} {g} . map i . h) X =
                                                 MkCompose . map (gtraverse d cstrs i) . gtraverse d cstrs h $ X
   gtraversableCompositionH {f} {g} {ix} d cstrs h i (Con {ix} x) with (assert_total $ gtraversabledCompositionH d cstrs d cstrs h i x)
     gtraversableCompositionH {f} {g} {ix} d cstrs h i (Con {ix} x) | prf =
       rewrite prf in composeTraverseConLemma d cstrs h i x

  gtraversableComposition : (VApplicative f, VApplicative g) =>
                            {a, b, c, Ix: _} -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VTraversable d)
                                             -> (h : a -> f b) -> (i : b -> g c)
                                             -> gtraverse d cstrs (MkCompose {f} {g} . map i . h) =
                                                  MkCompose . map (gtraverse d cstrs i) . gtraverse d cstrs h
  gtraversableComposition d cstrs h i = funext (gtraversableCompositionH d cstrs h i)

  mutual
    gtraversabledNaturalityH : (VApplicativeTransformer f g) =>
                               {a, b, Ix: _} -> (dR: PDesc 1 Ix) -> (cstrsR: PConstraints1 VTraversable dR)
                                             -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VTraversable d)
                                             -> (h: a -> f b)
                                -> {ix : Ix} -> (X : PSynthesize d a (PData dR a) ix)
                                             -> transformA {f} {g} (gtraversed dR cstrsR d cstrs h X) =
                                                  gtraversed {g} dR cstrsR d cstrs (transformA {f} {g} . h) X
    gtraversabledNaturalityH {f} {g} _ _ (PRet ix) _ _ Refl = transformAPure {f} {g} {a=(ix=ix)} {x=Refl}
    gtraversabledNaturalityH {f} {g} @{at} {ix} dR cstrsR (PArg a kdesc) cstrs h (arg ** rest) =
      (transformA {f} {g} @{at} (pure {f} (MkDPair arg) <*> gtraversed @{vapt2apF at} dR cstrsR (kdesc arg) (cstrs arg) h rest))
        ={ transformAAp {f} {g} {x=pure {f} @{vapt2apF at} (MkDPair arg)} {y=gtraversed @{vapt2apF at} dR cstrsR (kdesc arg) (cstrs arg) h rest} }=
      (transformA {f} {g} @{at} (pure {f} (MkDPair arg)) <*> transformA {f} {g} @{at} (gtraversed @{vapt2apF at} {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest))
        ={ cong {f = \r => r <*> transformA (gtraversed dR cstrsR (kdesc arg) (cstrs arg) h rest)} $
           transformAPure {f} {g} {x=MkDPair arg} }=
      (pure {f=g} (MkDPair arg) <*> transformA {f} {g} @{at} (gtraversed @{vapt2apF at} {ix} dR cstrsR (kdesc arg) (cstrs arg) h rest))
        ={ cong {f = \r => pure (MkDPair arg) <*> r} $
           gtraversabledNaturalityH {f} {g} dR cstrsR (kdesc arg) (cstrs arg) h rest }=
      (pure {f=g} (MkDPair arg) <*> gtraversed {ix} dR cstrsR (kdesc arg) (cstrs arg) (\x => transformA (h x)) rest)
        QED
    gtraversabledNaturalityH {f} {g} @{at} {ix} dR cstrsR (PPar FZ kdesc) cstrs h (par ** rest) =
      (transformA {f} {g} (map {f} @{ap2fun {f} $ vapt2apF at} zipD (h par) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest))
        ={ rewrite sym $ applicativeVFunctorCoherence {f} in Refl }=
      (transformA {f} {g} (map {f} zipD (h par) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest))
        ={ transformAAp {f} {g} {x = map {f} zipD (h par)} {y = gtraversed {ix} dR cstrsR kdesc cstrs h rest} }=
      (transformA {f} {g} (map {f} zipD (h par)) <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc cstrs h rest))
        ={ cong {f=\z=>z <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc cstrs h rest)} $
           transformAMap {h=zipD} {x=h par} }=
      (map {f=g} zipD (transformA {f} {g} (h par)) <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc cstrs h rest))
        ={ rewrite applicativeVFunctorCoherence {f=g} in Refl }=
      (map {f=g} @{ap2fun {f=g} $ vapt2apG at} zipD (transformA {f} {g} (h par)) <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc cstrs h rest))
        ={ cong {f=\z=> map {f=g} @{ap2fun {f=g} $ vapt2apG at} zipD (transformA {f} {g} (h par)) <*> z} $
           gtraversabledNaturalityH {f} {g} dR cstrsR kdesc cstrs h rest }=
      (map {f=g} @{ap2fun {f=g} $ vapt2apG at} zipD (transformA {f} {g} (h par)) <*> gtraversed {ix} dR cstrsR kdesc cstrs (\x => transformA (h x)) rest)
        QED
    gtraversabledNaturalityH _ _ (PPar (FS FZ) _)   _ _ _ impossible
    gtraversabledNaturalityH _ _ (PPar (FS (FS _)) _) _ _ _ impossible
    gtraversabledNaturalityH {f} {g} @{at} {ix} dR cstrsR (PMap _ FZ kdesc) (_, vtravr) h (ta ** rest) =
      (transformA {f} {g} (map {f} @{ap2fun {f} $ vapt2apF at} zipD (traverse h ta) <*> gtraversed {ix} dR cstrsR kdesc vtravr h rest))
         ={ rewrite sym $ applicativeVFunctorCoherence {f} in Refl }=
      (transformA {f} {g} (map {f} zipD (traverse h ta) <*> gtraversed {ix} dR cstrsR kdesc vtravr h rest))
         ={ transformAAp {f} {g} {x = map {f} zipD (traverse h ta)} {y = gtraversed {ix} dR cstrsR kdesc vtravr h rest} }=
      (transformA {f} {g} (map {f} zipD (traverse h ta)) <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc vtravr h rest))
         ={ cong {f=\z=>z <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc vtravr h rest)} $
            transformAMap {h=zipD} {x=traverse h ta} }=
      (map {f=g} zipD ((transformA {f} {g} . traverse h) ta) <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc vtravr h rest))
         ={ cong {f=\z=>map {f=g} zipD (z ta) <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc vtravr h rest)} $
            traversableNatural {h} }=
      (map {f=g} zipD (traverse (\x => transformA {f} {g} (h x)) ta) <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc vtravr h rest))
         ={ rewrite applicativeVFunctorCoherence {f=g} in Refl }=
      (map {f=g} @{ap2fun {f=g} $ vapt2apG at} zipD (traverse (\x => transformA {f} {g} (h x)) ta) <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc vtravr h rest))
         ={ cong {f=\z=>map {f=g} @{ap2fun {f=g} $ vapt2apG at} zipD (traverse (\x => transformA {f} {g} (h x)) ta) <*> z} $
           gtraversabledNaturalityH {f} {g} dR cstrsR kdesc vtravr h rest }=
      (map {f=g} @{ap2fun {f=g} $ vapt2apG at} zipD (traverse (\x => transformA {f} {g} (h x)) ta) <*> gtraversed {ix} dR cstrsR kdesc vtravr (\x => transformA (h x)) rest)
         QED
    gtraversabledNaturalityH _ _ (PMap _ (FS FZ) _) _ _ _ impossible
    gtraversabledNaturalityH _ _ (PMap _ (FS (FS _)) _) _ _ _ impossible
    gtraversabledNaturalityH {f} {g} @{at} {ix} dR cstrsR (PRec _ kdesc) cstrs h (rec ** rest) =
      (transformA {f} {g} (map @{ap2fun {f} $ vapt2apF at} zipD (gtraverse dR cstrsR h rec) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest))
        ={ rewrite sym $ applicativeVFunctorCoherence {f} in Refl }=
      (transformA {f} {g} (map zipD (gtraverse dR cstrsR h rec) <*> gtraversed {ix} dR cstrsR kdesc cstrs h rest))
        ={ transformAAp {f} {g} {x = map {f} zipD (gtraverse dR cstrsR h rec)} {y = gtraversed {ix} dR cstrsR kdesc cstrs h rest} }=
      (transformA {f} {g} (map zipD (gtraverse dR cstrsR h rec)) <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc cstrs h rest))
        ={ cong {f=\z=>z <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc cstrs h rest)} $
           transformAMap {h=zipD} {x=gtraverse dR cstrsR h rec} }=
      (map {f=g} zipD (transformA {f} {g} (gtraverse dR cstrsR h rec)) <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc cstrs h rest))
        ={ cong {f=\z=>map {f=g} zipD z <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc cstrs h rest)} $
           gtraversableNaturalityH dR cstrsR h rec }=
      (map {f=g} zipD (gtraverse dR cstrsR (\x => transformA (h x)) rec) <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc cstrs h rest))
        ={ rewrite applicativeVFunctorCoherence {f=g} in Refl }=
      (map {f=g} @{ap2fun {f=g} $ vapt2apG at} zipD (gtraverse dR cstrsR (\x => transformA (h x)) rec) <*> transformA {f} {g} (gtraversed {ix} dR cstrsR kdesc cstrs h rest))
        ={ cong {f=\z=>map {f=g} @{ap2fun {f=g} $ vapt2apG at} zipD (gtraverse dR cstrsR (\x => transformA (h x)) rec) <*> z} $
           gtraversabledNaturalityH {f} {g} dR cstrsR kdesc cstrs h rest }=
      (map {f=g} @{ap2fun {f=g} $ vapt2apG at} zipD (gtraverse dR cstrsR (\x => transformA (h x)) rec) <*> gtraversed {ix} dR cstrsR kdesc cstrs (\x => transformA (h x)) rest)
        QED

    gtraversableNaturalityH : (VApplicativeTransformer f g) =>
                              {a, b, Ix: _} -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VTraversable d) -> (h: a -> f b)
                               -> {ix : Ix} -> (X : PData d a ix)
                                            -> transformA {f} {g} (gtraverse d cstrs h X) =
                                                 gtraverse d cstrs (transformA {f} {g} . h) X
    gtraversableNaturalityH {f} {g} @{at} {ix} d cstrs h (Con x) =
      (transformA @{at} {f} {g} ((<*>) {f} (pure {f} @{vapt2apF at} Con) (gtraversed {g = f} @{vapt2apF at} {ix} d cstrs d cstrs h x)))
        ={ transformAAp {f} {g} @{at} }=
      ((<*>) {f = g} @{vapt2apG at} (transformA @{at} {f} {g} (pure {f} @{vapt2apF at} Con))
                           (transformA @{at} {f} {g} (gtraversed {g = f} @{vapt2apF at} {ix} d cstrs d cstrs h x)))
        ={ cong {f = \z => z <*> (transformA @{at} {f} {g} (gtraversed {g = f} @{vapt2apF at} {ix} d cstrs d cstrs h x))} $
           transformAPure {f} {g} @{at} }=
      ((<*>) {f = g} @{vapt2apG at} (pure {f = g} @{vapt2apG at} Con)
                           (transformA @{at} {f} {g} (gtraversed {g = f} @{vapt2apF at} {ix} d cstrs d cstrs h x)))
        ={ cong {f = \z => pure {f = g} @{vapt2apG at} Con <*> z } $
           gtraversabledNaturalityH @{at} d cstrs d cstrs h x }=
      ((<*>) @{vapt2apG at} (pure {f = g} @{vapt2apG at} Con) (gtraversed {g} @{vapt2apG at} {ix} d cstrs d cstrs (transformA @{at} {f} {g} . h) x))
        QED

  gtraversableNaturality : (VApplicativeTransformer f g) =>
                           {a, b, Ix: _} -> (d: PDesc 1 Ix) -> (cstrs: PConstraints1 VTraversable d) -> (h: a -> f b)
                                         -> transformA {f} {g} . gtraverse d cstrs h =
                                              gtraverse d cstrs (transformA {f} {g} . h)
  gtraversableNaturality {f} {g} d cstrs h = funext (\X => gtraversableNaturalityH {f} {g} d cstrs h X)
