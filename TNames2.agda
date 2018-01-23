module TNames2 where


open import Relation.Nullary
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Vec hiding (_>>=_)
open import Data.Product
open import Data.Nat hiding (_≤_ ; _≤?_ ; ≤-pred)
open import Data.Bool


open import ASType2 public
open import Nat2 public
open import NotEqM2 public


data TNames : Set where     
  moreTN : (type : ASType) → (exists : Bool) → TNames → TNames
  emptyTN : TNames


tns-length : TNames → ℕ
tns-length (moreTN type exists x) = suc (tns-length x)
tns-length emptyTN = 0



------------------
  -- Does a name belong to TNames? or has it being used?


record TName : Set where
  field
    pos : ℕ
    type : ASType

open TName public

sucₜₙ : TName → TName
sucₜₙ tn = record {pos = suc (pos tn) ; type = type tn}



data _∈ₜₙ_ : TName → TNames → Set where
  there : ∀{tn type exists tns} → (tn ∈ₜₙ tns) → sucₜₙ tn ∈ₜₙ (moreTN type exists tns)
  here  : ∀{type tns} → record {pos = zero ; type = type} ∈ₜₙ (moreTN type true tns)



∈ₙ-length : ∀{tn tns} → (bel : tn ∈ₜₙ tns) → pos (sucₜₙ tn) ≤ tns-length tns
∈ₙ-length (there bel) = s≤s {{∈ₙ-length bel}}
∈ₙ-length here = s≤s


--------------------------------
-- Operations on TNames.




remTN : ∀{tn} → (tns : TNames) → tn ∈ₜₙ tns → TNames
remTN (moreTN type exists tns) (there bel) = moreTN type exists (remTN tns bel)
remTN (moreTN type true tns) here = moreTN type false tns



-- We add a new name at the end so as to preserve the name conversions.
-- We get a ∈ₜₙ result that gives us proof that the name exists in tns.
-- We also get a proof that the length of the original list is less than the number ot tn.
-- We need to provide proofs that allow arguments provided are different than one other, and this will help in proving that.

record AddTN  (ptns : TNames) (type : ASType) : Set where
  field
    tns : TNames
    pos : ℕ
    bel : record {pos = pos ; type = type} ∈ₜₙ tns
    rel : tns-length ptns ≤ pos

open AddTN

addTN : (ptns : TNames) → (type : ASType) → AddTN ptns type
addTN (moreTN type₁ exists ptns) type = (record {tns = moreTN type₁ exists (tns is) ; pos = suc (pos is) ; bel = there (bel is) ; rel = s≤s {{rel is}}}) where
  is = addTN ptns type
addTN emptyTN type = record {tns = moreTN type true emptyTN ; pos = zero ; bel = here ; rel = z≤n}



--------------------------
-- Updating the proof of belonging after a change in TNames.

update-∈ₜₙ-remTN : ∀{tnᵣ tnₒ tns} → (belᵣ : tnᵣ ∈ₜₙ tns) → (belₒ : tnₒ ∈ₜₙ tns) → (neq : NotEq (pos tnᵣ) (pos tnₒ)) → tnₒ ∈ₜₙ (remTN tns belᵣ)
update-∈ₜₙ-remTN (there belr) (there belo) (predEq {{neq}}) = there (update-∈ₜₙ-remTN belr belo neq)
update-∈ₜₙ-remTN (there belr) here neq = here
update-∈ₜₙ-remTN here (there belo) neq = there belo
update-∈ₜₙ-remTN here here ()


update-∈ₜₙ-addTN : ∀{astₐ tn tns} → (bel : tn ∈ₜₙ tns) → tn ∈ₜₙ (AddTN.tns (addTN tns astₐ))
update-∈ₜₙ-addTN (there bel) = there (update-∈ₜₙ-addTN bel)
update-∈ₜₙ-addTN here = here


-------------------------------
-- The View is used as proof that the arguments that are passed to a function exist, they have
-- been created and not destroyed since then.


data View (tns : TNames) : ∀{l} → Vec ASType l → Set where
  moreVW : ∀{l} → ∀ tn → (bel : tn ∈ₜₙ tns) → ∀{vc : Vec ASType l} → (vw : View tns vc) → View tns ((type tn) ∷ vc)
  emptyVW : View tns []


vwToVec : {tns : TNames} → ∀{l} → {vc : Vec ASType l} → View tns vc → Vec ℕ l
vwToVec (moreVW tn bel vw) = pos tn ∷ vwToVec vw
vwToVec emptyVW = []


vw-len : {tns : TNames} → ∀{l} → {vc : Vec ASType l} → (vw : View tns vc) → ℕ
vw-len (moreVW tn bel₁ vw) = suc (vw-len vw)
vw-len emptyVW = zero


-- vec is the output of vwToVec from the original View itns vci.
data TNOp (tnsi : TNames) {l} (vec : Vec ℕ l) (tnso : TNames) : Set where
  addTNOp : {type : ASType} → TNOp (tns (addTN tnsi type)) vec tnso → TNOp _ _ _
  remTNOp : ∀{tn} → {bel : tn ∈ₜₙ tnsi} → TNOp (remTN tnsi bel) vec tnso → TNOp _ _ _
  idOp : TNOp _ _ _ 
