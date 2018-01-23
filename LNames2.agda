module LNames2 where

open import Data.Maybe
open import Data.Product
open import Data.Vec hiding (_>>=_)
open import Data.Nat hiding (_≤_ ; _≤?_ ; ≤-pred)
open import Relation.Binary.PropositionalEquality


open import TNames2 public




-- This View is used internally at a specific function. It is used to truck the arguments in the context of the function. (This is way, we
-- will prove that we pass arguments to a function that are not equal.

data LNames (tns : TNames) : Set where
  moreLN : ∀ tn → (mbel : Maybe (tn ∈ₜₙ tns)) → (lns : LNames tns) → LNames tns
  emptyLN : LNames tns


lnToVec : {tns : TNames} → LNames tns → ∃ λ l → Vec ℕ l
lnToVec (moreLN tn (just _) lvw) = suc (proj₁ is) , pos tn ∷ proj₂ is where
  is = lnToVec lvw
lnToVec (moreLN tn nothing lvw) = lnToVec lvw
lnToVec emptyLN = 0 , []


vwToLns : ∀{tns l} → {vc : Vec ASType l} → (vw : View tns vc) → LNames tns
vwToLns (moreVW tn bel vw) = moreLN tn (just bel) (vwToLns vw)
vwToLns emptyVW = emptyLN





lnToVec$vwToLns≡vwToVec-abs : ∀ {l} {tn : TName} {vc : Vec ASType l}
                                {tns} {vw : View tns vc} {w} {w1 : Vec ℕ w} →
                              Σ (w ≡ l) (λ leq → subst (Vec ℕ) leq w1 ≡ vwToVec vw) →
                              Σ (suc w ≡ suc l)
                              (λ leq → subst (Vec ℕ) leq (pos tn ∷ w1) ≡ pos tn ∷ vwToVec vw)
lnToVec$vwToLns≡vwToVec-abs {tn = tn} (refl , veq) = refl , (cong (_∷_ (pos tn)) veq)



lnToVec$vwToLns≡vwToVec : ∀{tns l} → {vc : Vec ASType l} → (vw : View tns vc) → Σ (proj₁ (lnToVec (vwToLns vw)) ≡ l) (λ leq → (subst (λ x → Vec ℕ x) leq (proj₂ (lnToVec (vwToLns vw)))) ≡ vwToVec vw)
lnToVec$vwToLns≡vwToVec (moreVW tn bel₁ vw) = lnToVec$vwToLns≡vwToVec-abs {tn = tn} {w = proj₁ (lnToVec (vwToLns vw))} {proj₂ (lnToVec (vwToLns vw))} (lnToVec$vwToLns≡vwToVec vw) where
  r = lnToVec$vwToLns≡vwToVec vw
lnToVec$vwToLns≡vwToVec emptyVW = refl , refl



lnToVec$vwToLns≡vwToVecP-abs : ∀ {tns} {l} {vc : Vec ASType l}
            {vw : View tns vc} {w} {w1 : Vec ℕ w} →
          Σ (w ≡ l) (λ leq → subst (Vec ℕ) leq w1 ≡ vwToVec vw)
          → {P : ({l : ℕ} → Vec ℕ l → Set)}
          → P (vwToVec vw) → P w1
lnToVec$vwToLns≡vwToVecP-abs (refl , refl) r = r

lnToVec$vwToLns≡vwToVecP : ∀{tns l} → {vc : Vec ASType l} → {vw : View tns vc}
      → {P : ({l : ℕ} → Vec ℕ l → Set)}
      → P (vwToVec vw)
      → P (proj₂ (lnToVec (vwToLns vw)))
lnToVec$vwToLns≡vwToVecP {vw = vw} {P = P} = lnToVec$vwToLns≡vwToVecP-abs {w = proj₁ (lnToVec (vwToLns vw))} {proj₂ (lnToVec (vwToLns vw))} (lnToVec$vwToLns≡vwToVec vw) {P = P}



record LName : Set where
  field
    pos : ℕ
    type : ASType

open LName

sucₗₙ : LName → LName
sucₗₙ ln = record {pos = suc (pos ln) ; type = type ln}

zeroₗₙ : ASType → LName
zeroₗₙ type = record {pos = zero ; type = type}

data _∈ₗₙ_ {tns} : LName → LNames tns → Set where
  instance
    there : ∀{ln tn lns} → {mbel : Maybe (tn ∈ₜₙ tns)} → {{bel : ln ∈ₗₙ lns}} → sucₗₙ ln ∈ₗₙ (moreLN tn mbel lns)
    here  : ∀{tn lns} → {belₜₙ : tn ∈ₜₙ tns} → (zeroₗₙ (type tn)) ∈ₗₙ (moreLN tn (just belₜₙ) lns)

∈ₗₙTo∈ₜₙ : ∀{ln tns} → {lns : LNames tns} → ln ∈ₗₙ lns → ∃ (λ n → record {pos = n ; type = type ln} ∈ₜₙ tns)
∈ₗₙTo∈ₜₙ (there {{bel}}) = ∈ₗₙTo∈ₜₙ bel
∈ₗₙTo∈ₜₙ (here {belₜₙ = bel}) = _ , bel



∈ₗₙTo∈ : ∀{tns ln} → {lns : LNames tns} → (bel : ln ∈ₗₙ lns) → (proj₁ (∈ₗₙTo∈ₜₙ bel)) ∈ (proj₂ (lnToVec lns))
∈ₗₙTo∈ {lns = moreLN _ (just x) lns} (there ⦃ bel = bel ⦄) = there (∈ₗₙTo∈ bel)
∈ₗₙTo∈ {lns = moreLN _ nothing lns} (there ⦃ bel = bel ⦄) = ∈ₗₙTo∈ bel
∈ₗₙTo∈ here = here



data LView {tns} (lns : LNames tns) : ∀{l} → (vc : Vec ASType l) → Set where
  moreLVW : ∀ ln → ∀{l} → {vc : Vec ASType l} → {{bel : ln ∈ₗₙ lns}} → LView lns vc → LView lns ((type ln) ∷ vc)
  emptyLVW : LView lns []

lvwToVec : {tns : TNames} → {lns : LNames tns} → ∀{l} → {vc : Vec ASType l} → LView lns vc → Vec ℕ l
lvwToVec emptyLVW = []
lvwToVec (moreLVW ln lvw) = pos ln ∷ r where
  r = lvwToVec lvw


lvwToVW : {tns : TNames} → {lns : LNames tns} → ∀{l} → {vc : Vec ASType l} → LView lns vc → View tns vc
lvwToVW (moreLVW ln {{lbel}} lvw) = moreVW _ (proj₂ (belₜₙ)) r where
  r = lvwToVW lvw
  belₜₙ = ∈ₗₙTo∈ₜₙ lbel
lvwToVW emptyLVW = emptyVW



lneqToNeq-lemma2 : ∀ {tnsi} {lnsi : LNames tnsi} {ln2 ln} →
                   NotEq (pos ln) (pos ln2) →
                   NotEqVVec (proj₂ (lnToVec lnsi)) →
                   (bel : ln ∈ₗₙ lnsi) (bel2 : ln2 ∈ₗₙ lnsi) →
                   NotEq (proj₁ (∈ₗₙTo∈ₜₙ bel)) (proj₁ (∈ₗₙTo∈ₜₙ bel2))
lneqToNeq-lemma2 {lnsi = moreLN _ (just x) lnsi} (predEq ⦃ neq ⦄) (vvi {{ieq = noteqi}}) (there ⦃ bel = bel ⦄) (there ⦃ bel = bel2 ⦄) = lneqToNeq-lemma2 neq noteqi bel bel2
lneqToNeq-lemma2 {lnsi = moreLN _ nothing lnsi} (predEq ⦃ neq ⦄) noteqi (there ⦃ bel = bel ⦄) (there ⦃ bel = bel2 ⦄) = lneqToNeq-lemma2 neq noteqi bel bel2
lneqToNeq-lemma2 neq (vvi {{noteq}}) (there {tn = tn} ⦃ bel = bel ⦄) here = notEq-sym (notEq-∈ (pos tn) (proj₁ (∈ₗₙTo∈ₜₙ bel)) (∈ₗₙTo∈ bel) noteq)
lneqToNeq-lemma2 neq (vvi {{noteq}}) here (there {tn = tn} ⦃ bel = bel ⦄) = notEq-∈ (pos tn) (proj₁ (∈ₗₙTo∈ₜₙ bel)) (∈ₗₙTo∈ bel) noteq


lneqToNeq-lemma : ∀ {tnsi} {lnsi : LNames tnsi} {l} {vc : Vec ASType l} {lvw : LView lnsi vc}
                    {ln} →
                  NotEqNVec (pos ln) (lvwToVec lvw) →
                  NotEqVVec (proj₂ (lnToVec lnsi)) →
                  {bel : ln ∈ₗₙ lnsi} →
                  NotEqNVec (proj₁ (∈ₗₙTo∈ₜₙ bel))
                  (vwToVec (lvwToVW lvw))
lneqToNeq-lemma {lvw = moreLVW ln2 {{bel2}} lvw} {ln} (nvi {{neq}} {{ieq}}) noteqi {bel} = nvi {{lneqToNeq-lemma2 neq noteqi bel bel2}} {{lneqToNeq-lemma {lvw = lvw} ieq noteqi {bel = bel}}}
lneqToNeq-lemma {lvw = emptyLVW} neq noteqi {bel} = nvl

-- Local Not Equality to Global Not Equality.
lneqToNeq : ∀{tnsi} (lnsi : LNames tnsi) (noteqi : NotEqVVec (proj₂ (lnToVec lnsi)))
      {l} {vc : Vec ASType l} (lvw : LView lnsi vc) (noteqLVW : NotEqVVec (lvwToVec lvw))
      → let vw = lvwToVW lvw in NotEqVVec (vwToVec vw)
lneqToNeq lnsi noteqi (moreLVW ln {{bel}} lvw) (vvi {{neq}} {{ieq}}) = vvi {{lneqToNeq-lemma {lvw = lvw} neq noteqi {bel} }} {{r}} where
  r = lneqToNeq lnsi noteqi lvw ieq
lneqToNeq lnsi noteqi emptyLVW noteqLVW = noteqLVW


-- Maximum size of the new LNames is len.
lnsCutToLen : ∀{tns} → (lns : LNames tns) → (len : ℕ) → LNames tns
lnsCutToLen lns zero = emptyLN
lnsCutToLen (moreLN tn mbel lns) (suc len) = moreLN tn mbel (lnsCutToLen lns len)
lnsCutToLen emptyLN (suc len) = emptyLN


-- We keep the length the same so as to preserve the lns but we flush the first part so that
-- no view can be created from the original arguments.
lnsCutToLenRem : ∀{tns} → (lns : LNames tns) → (len : ℕ) → LNames tns
lnsCutToLenRem lns zero = lns
lnsCutToLenRem (moreLN tn mbel lns) (suc len) = moreLN tn nothing (lnsCutToLenRem lns len)
lnsCutToLenRem emptyLN (suc len) = emptyLN
