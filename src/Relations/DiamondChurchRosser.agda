module Relations.DiamondChurchRosser where

open import Data.Nat as Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Product

open import Base
open import Relations.Base
open import Relation.Binary.PropositionalEquality as Cong using (_≡_)

data RelPosPow {A : Set} (R : Rel A) : ℕ → (Rel A) where
    inj : ∀{s t} → R s t → RelPosPow R 1 s t
    trans : ∀{u s t} → ∀{n} → R s u → RelPosPow R n u t → RelPosPow R (suc n) s t

data RelPow {A : Set} (R : Rel A) : ℕ → (Rel A) where
    refl : ∀{s} → RelPow R 0 s s
    pospow : ∀{s t} → ∀{n} → RelPosPow R n s t → RelPow R n s t

ZeroRightNeutral : ∀{m} → m + 0 ≡ m
ZeroRightNeutral {zero} = Cong.refl
ZeroRightNeutral {suc m} = Cong.cong suc (ZeroRightNeutral {m})

RelPosPowAppend : ∀{A} → (R : Rel A) → ∀{s u t} → ∀{m n} → RelPosPow R m s u → RelPosPow R n u t → RelPosPow R (m + n) s t
RelPosPowAppend _ (inj s_R_u) u_Rn_t = trans s_R_u u_Rn_t
RelPosPowAppend R (trans s_R_v v_Rm_u) u_Rn_t = trans s_R_v (RelPosPowAppend R v_Rm_u u_Rn_t)
RelPowAppend : ∀{A} → (R : Rel A) → ∀{s u t} → ∀{m n} → RelPow R m s u → RelPow R n u t → RelPow R (m + n) s t
RelPowAppend _ refl u_Rn_t = u_Rn_t
RelPowAppend _ s_Rm_u refl = Cong.subst (λ m → RelPow _ m _ _) (Cong.sym ZeroRightNeutral) s_Rm_u
RelPowAppend R (pospow s_Rm_u) (pospow u_Rn_t) = pospow (RelPosPowAppend R s_Rm_u u_Rn_t)

ReflTrans→RelPow : ∀{A} → (R : Rel A) → ∀{s t} → ReflTrans R s t → Σ[ n ∈ ℕ ] (RelPow R n s t)
ReflTrans→RelPow _ refl = 0 , refl
ReflTrans→RelPow _ (inj s_R_t) = 1 , pospow (inj s_R_t)
ReflTrans→RelPow R (trans s_RR_u u_RR_t) =
    let m , s_Rm_u = ReflTrans→RelPow R s_RR_u
        n , u_Rn_t = ReflTrans→RelPow R u_RR_t
    in m + n , RelPowAppend R s_Rm_u u_Rn_t

RelPosPow→ReflTrans : ∀{A} → (R : Rel A) → ∀{s t} → ∀{n} → RelPosPow R n s t → ReflTrans R s t
RelPosPow→ReflTrans _ (inj s_R_t) = inj s_R_t
RelPosPow→ReflTrans R (trans s_R_u u_Rn_t) = trans (inj s_R_u) (RelPosPow→ReflTrans R u_Rn_t)
RelPow→ReflTrans : ∀{A} → (R : Rel A) → ∀{s t} → ∀{n} → RelPow R n s t → ReflTrans R s t
RelPow→ReflTrans _ refl = refl
RelPow→ReflTrans R (pospow s_Rn_t) = RelPosPow→ReflTrans R s_Rn_t

Diamond→PosPowCR : ∀{A} → (R : Rel A) → Diamond R → ∀{s t₁ t₂} → ∀{m n}
    → RelPosPow R m s t₁
    → RelPosPow R n s t₂
    → Σ[ u ∈ A ] (RelPosPow R n t₁ u) × (RelPosPow R m t₂ u)
Diamond→PosPowCR R DiamR {s} {t₁} {t₂} (inj s_R_t₁) (inj s_R_t₂) =
    let v , (t₁_R_u , t₂_R_u) = DiamR s t₁ t₂ s_R_t₁ s_R_t₂
    in v , (inj t₁_R_u , inj t₂_R_u)
Diamond→PosPowCR R DiamR {s} {t₁} {_} (inj s_R_t₁) (trans {u} s_R_u u_Rn_t₂) =
    let u' , (t₁_R_u' , u_R_u') = DiamR s t₁ u s_R_t₁ s_R_u
        v , (u'_Rn_v , t₂_R1_v) = Diamond→PosPowCR R DiamR (inj u_R_u') u_Rn_t₂
    in v , (trans t₁_R_u' u'_Rn_v , t₂_R1_v)
Diamond→PosPowCR R DiamR {s} {_} {t₂} (trans {u} s_R_u u_Rm_t₁) (inj s_R_t₂) =
    let u' , (u_R_u' , t₂_R_u') = DiamR s u t₂ s_R_u s_R_t₂
        v , (t₁_R1_v , u'_Rm_v) = Diamond→PosPowCR R DiamR u_Rm_t₁ (inj u_R_u')
    in v , (t₁_R1_v , trans t₂_R_u' u'_Rm_v)
Diamond→PosPowCR R DiamR {s} (trans {u₁} s_R_u₁ u₁_Rm_t₁) (trans {u₂} s_R_u₂ u₂_Rn_t₂) =
    let u' , (u₁_R_u' , u₂_R_u') = DiamR s u₁ u₂ s_R_u₁ s_R_u₂
        v₁ , (t₁_R1_v₁ , u'_Rm_v₁) = Diamond→PosPowCR R DiamR u₁_Rm_t₁ (inj u₁_R_u')
        v₂ , (u'_Rn_v₂ , t₂_R1_v₂) = Diamond→PosPowCR R DiamR (inj u₂_R_u') u₂_Rn_t₂
        v , (v₁_Rn_v , v₂_Rm_v) = Diamond→PosPowCR R DiamR u'_Rm_v₁ u'_Rn_v₂
    in v , (RelPosPowAppend R t₁_R1_v₁ v₁_Rn_v , RelPosPowAppend R t₂_R1_v₂ v₂_Rm_v)
-- Should be possible to replace 2nd, 3rd, and 4th pattern by the following (+ symmetric) pattern, but I can't convince Agda that it terminates.
-- Diamond→PosPowCR R DiamR (trans s_R_u u_Rm_t₁) s_Rn_t₂ =
--     let u' , (u_Rn_u' , t₂_R1_u') = Diamond→PosPowCR R DiamR (inj s_R_u) s_Rn_t₂
--         v , (t₁_Rn_v , u'_Rm_v) = Diamond→PosPowCR R DiamR u_Rm_t₁ u_Rn_u'
--     in v , (t₁_Rn_v , RelPosPowAppend R t₂_R1_u' u'_Rm_v)
Diamond→PowCR : ∀{A} → (R : Rel A) → Diamond R → ∀{s t₁ t₂} → ∀{m n}
    → RelPow R m s t₁
    → RelPow R n s t₂
    → Σ[ u ∈ A ] (RelPow R n t₁ u) × (RelPow R m t₂ u)
Diamond→PowCR R DiamR {_} {t₁} {_} s_Rm_t₁ refl = t₁ , (refl , s_Rm_t₁)
Diamond→PowCR R DiamR {_} {_} {t₂} refl s_Rm_t₂ = t₂ , (s_Rm_t₂ , refl)
Diamond→PowCR R DiamR (pospow s_Rm_t₁) (pospow s_Rn_t₂) =
    let v , (t₁_Rn_v , t₂_Rm_v) = Diamond→PosPowCR R DiamR s_Rm_t₁ s_Rn_t₂
    in v , (pospow t₁_Rn_v , pospow t₂_Rm_v)
Diamond→CR : ∀{A} → (R : Rel A) → Diamond R → ChurchRosser R
Diamond→CR R DiamR s t₁ t₂ s_RR_t₁ s_RR_t₂ = 
    let m , s_Rm_t₁ = ReflTrans→RelPow R s_RR_t₁ 
        n , s_Rn_t₂ = ReflTrans→RelPow R s_RR_t₂
        u , (t₁_Rn_u , t₂_Rm_u) = Diamond→PowCR R DiamR s_Rm_t₁ s_Rn_t₂
    in u , (RelPow→ReflTrans R t₁_Rn_u , RelPow→ReflTrans R t₂_Rm_u)
