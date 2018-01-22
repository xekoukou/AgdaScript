module AgdaScript2 where



open import Data.Maybe
open import Data.Bool
open import Data.Nat hiding (_≤_ ; _≤?_ ; ≤-pred)
open import Data.Vec hiding (_>>=_)
open import Data.Product
open import Relation.Nullary
open import Data.Empty
-- open import Data.List

import Level using (zero)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality
open import Category.Monad


open import Nat2
open import NotEqM2
open import Common



open RawMonad (Data.Maybe.monad {Level.zero})

data ASType : Set where
  str    : ASType
  int32  : ASType
  uint32 : ASType


_AST≡?_ : (x : ASType) → (y : ASType) → Dec (x ≡ y)
str AST≡? str = yes refl
str AST≡? int32 = no (λ ())
str AST≡? uint32 = no (λ ())
int32 AST≡? str = no (λ ())
int32 AST≡? int32 = yes refl
int32 AST≡? uint32 = no (λ ())
uint32 AST≡? str = no (λ ())
uint32 AST≡? int32 = no (λ ())
uint32 AST≡? uint32 = yes refl


--- ? ?? --- Let us hope this works.
data EqVec : ∀{l r} → Vec ASType l → Vec ASType r → Set where
  instance 
    []-cong : EqVec [] []
    ∷-cong : ∀{l r x} → {xsₗ : Vec ASType l} → {xsᵣ : Vec ASType r} →  {{is : EqVec xsₗ xsᵣ}} →  EqVec (x ∷ xsₗ) (x ∷ xsᵣ)


eqVecTo≡-abs : ∀ {l x} {xsₗ : Vec ASType l} {r}
                 {xsᵣ : Vec ASType r} →
               Σ (l ≡ r) (λ leq → subst (Vec ASType) leq xsₗ ≡ xsᵣ) →
               Σ (suc l ≡ suc r)
               (λ leq → subst (Vec ASType) leq (x ∷ xsₗ) ≡ x ∷ xsᵣ)
eqVecTo≡-abs (refl , refl) = refl , refl

eqVecTo≡ : ∀{l r} → {lvc : Vec ASType l} → {rvc : Vec ASType r} → EqVec lvc rvc → Σ (l ≡ r) (λ leq → subst (Vec ASType) leq lvc ≡ rvc)
eqVecTo≡ []-cong = refl , refl
eqVecTo≡ (∷-cong {{eqvec}}) = eqVecTo≡-abs (eqVecTo≡ eqvec)



data TNames : Set where     
  moreTN : (type : ASType) → (exists : Bool) → TNames → TNames
  emptyTN : TNames


tn-length : TNames → ℕ
tn-length (moreTN type exists x) = suc (tn-length x)
tn-length emptyTN = 0



------------------
  -- Does a name belong to TNames? or has it being used?


record TName : Set where
  field
    pos : ℕ
    type : ASType

open TName

sucₜₙ : TName → TName
sucₜₙ tn = record {pos = suc (pos tn) ; type = type tn}



data _∈ₜₙ_ : TName → TNames → Set where
  there : ∀{tn type exists tns} → (tn ∈ₜₙ tns) → sucₜₙ tn ∈ₜₙ (moreTN type exists tns)
  here  : ∀{type tns} → record {pos = zero ; type = type} ∈ₜₙ (moreTN type true tns)



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
    rel : tn-length ptns ≤ pos

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



record LName : Set where
  field
    pos : ℕ

open LName

sucₗₙ : LName → LName
sucₗₙ ln = record {pos = suc (pos ln)}

zeroₗₙ : LName
zeroₗₙ = record {pos = zero}

data _∈ₗₙ_ {tns} : LName → LNames tns → Set where
  instance
    there : ∀{ln tn lns} → {mbel : Maybe (tn ∈ₜₙ tns)} → {{bel : ln ∈ₗₙ lns}} → sucₗₙ ln ∈ₗₙ (moreLN tn mbel lns)
    here  : ∀{tn lns} → {belₜₙ : tn ∈ₜₙ tns} → zeroₗₙ ∈ₗₙ (moreLN tn (just belₜₙ) lns)

∈ₗₙTo∈ₜₙ : ∀{ln tns} → {lns : LNames tns} → ln ∈ₗₙ lns → ∃ (λ tn → tn ∈ₜₙ tns)
∈ₗₙTo∈ₜₙ (there {{bel}}) = ∈ₗₙTo∈ₜₙ bel
∈ₗₙTo∈ₜₙ (here {belₜₙ = bel}) = _ , bel



∈ₗₙTo∈ : ∀{tns ln} → {lns : LNames tns} → (bel : ln ∈ₗₙ lns) → pos (proj₁ (∈ₗₙTo∈ₜₙ bel)) ∈ (proj₂ (lnToVec lns))
∈ₗₙTo∈ {lns = moreLN _ (just x) lns} (there ⦃ bel = bel ⦄) = there (∈ₗₙTo∈ bel)
∈ₗₙTo∈ {lns = moreLN _ nothing lns} (there ⦃ bel = bel ⦄) = ∈ₗₙTo∈ bel
∈ₗₙTo∈ here = here



data LView {tns} (lns : LNames tns) : Set where
  moreLVW : ∀ ln → {{bel : ln ∈ₗₙ lns}} → LView lns → LView lns
  emptyLVW : LView lns

lvwToVec : {tns : TNames} → {lns : LNames tns} → LView lns → ∃ λ l → Vec ℕ l
lvwToVec emptyLVW = zero , []
lvwToVec (moreLVW ln lvw) = suc (proj₁ r) , pos ln ∷ proj₂ r where
  r = lvwToVec lvw


lvwToVW : {tns : TNames} → {lns : LNames tns} → LView lns → ∃ (λ l → Σ (Vec ASType l) (λ vc → View tns vc))
lvwToVW (moreLVW ln {{lbel}} lvw) = (suc (proj₁ r)) , (_ , moreVW _ (proj₂ (belₜₙ)) (proj₂ (proj₂ r))) where
  r = lvwToVW lvw
  belₜₙ = ∈ₗₙTo∈ₜₙ lbel
lvwToVW emptyLVW = zero , [] , emptyVW



lneqToNeq-lemma2 : ∀ {tnsi} {lnsi : LNames tnsi} {ln2 ln} →
                   NotEq (pos ln) (pos ln2) →
                   NotEqVVec (proj₂ (lnToVec lnsi)) →
                   (bel : ln ∈ₗₙ lnsi) (bel2 : ln2 ∈ₗₙ lnsi) →
                   NotEq (pos (proj₁ (∈ₗₙTo∈ₜₙ bel))) (pos (proj₁ (∈ₗₙTo∈ₜₙ bel2)))
lneqToNeq-lemma2 {lnsi = moreLN _ (just x) lnsi} (predEq ⦃ neq ⦄) (vvi {{ieq = noteqi}}) (there ⦃ bel = bel ⦄) (there ⦃ bel = bel2 ⦄) = lneqToNeq-lemma2 neq noteqi bel bel2
lneqToNeq-lemma2 {lnsi = moreLN _ nothing lnsi} (predEq ⦃ neq ⦄) noteqi (there ⦃ bel = bel ⦄) (there ⦃ bel = bel2 ⦄) = lneqToNeq-lemma2 neq noteqi bel bel2
lneqToNeq-lemma2 neq (vvi {{noteq}}) (there {tn = tn} ⦃ bel = bel ⦄) here = notEq-sym (notEq-∈ (pos tn) (pos (proj₁ (∈ₗₙTo∈ₜₙ bel))) (∈ₗₙTo∈ bel) noteq)
lneqToNeq-lemma2 neq (vvi {{noteq}}) here (there {tn = tn} ⦃ bel = bel ⦄) = notEq-∈ (pos tn) (pos (proj₁ (∈ₗₙTo∈ₜₙ bel))) (∈ₗₙTo∈ bel) noteq


lneqToNeq-lemma : ∀ {tnsi} {lnsi : LNames tnsi} {lvw : LView lnsi}
                    {ln} →
                  NotEqNVec (pos ln) (proj₂ (lvwToVec lvw)) →
                  NotEqVVec (proj₂ (lnToVec lnsi)) →
                  {bel : ln ∈ₗₙ lnsi} →
                  NotEqNVec (pos (proj₁ (∈ₗₙTo∈ₜₙ bel)))
                  (vwToVec (proj₂ (proj₂ (lvwToVW lvw))))
lneqToNeq-lemma {lvw = moreLVW ln2 {{bel2}} lvw} {ln} (nvi {{neq}} {{ieq}}) noteqi {bel} = nvi {{lneqToNeq-lemma2 neq noteqi bel bel2}} {{lneqToNeq-lemma {lvw = lvw} ieq noteqi {bel = bel}}}
lneqToNeq-lemma {lvw = emptyLVW} neq noteqi {bel} = nvl

-- Local Not Equality to Global Not Equality.
lneqToNeq : ∀{tnsi} (lnsi : LNames tnsi) (noteqi : NotEqVVec (proj₂ (lnToVec lnsi)))
      (lvw : LView lnsi) (noteqLVW : NotEqVVec (proj₂ (lvwToVec lvw)))
      → let vw = proj₂ (proj₂ (lvwToVW lvw)) in NotEqVVec (vwToVec vw)
lneqToNeq lnsi noteqi (moreLVW ln {{bel}} lvw) (vvi {{neq}} {{ieq}}) = vvi {{lneqToNeq-lemma {lvw = lvw} neq noteqi {bel} }} {{r}} where
  r = lneqToNeq lnsi noteqi lvw ieq
lneqToNeq lnsi noteqi emptyLVW noteqLVW = noteqLVW



record FName : Set where
  field
    pos : ℕ

mutual


  data TFun : (len : ℕ) → Set where
    nextTF : ∀{len li lo loi} → {vci : Vec ASType li} → {vco : Vec ASType lo} → {vcoi : Vec ASType loi} → (tf : TFun len) → ASFunFT vci vco vcoi tf → TFun (suc len)
-- ? is this needed?  nextFunDef : ∀{n li lo} → {vci : Vec ASType (suc li)} → {vco : Vec ASType lo} → (tf : TFun n) → ? → TFun (suc n) -- Maybe here we need to have a (function) projection to the first two parts of the Sigma from ASFunFT
    emptyTF : TFun 0



  record ASFunF {len li lo loi} (vci : Vec ASType li) (vco : Vec ASType lo) (vcoi : Vec ASType loi) (tf : TFun len) {tnsi} (vwi : View tnsi vci) {noteqi : NotEqVVec (vwToVec vwi)} : Set where
    field
      tnso : TNames
      vwo : View tnso vco
      vwoi : View tnso vcoi
      noteqo : NotEqVVec ((vwToVec vwo) ++ (vwToVec vwoi))
      asf : ASFun vwi {noteqi} vwo {vcoi} {vwoi} {noteqo} tf


  ASFunFT : ∀{len li lo loi} → (vci : Vec ASType li) → (vco : Vec ASType lo) → (vcoi : Vec ASType loi) → (tf : TFun len) → Set
  ASFunFT {len} {li} {lo} vci vco vcoi tf = ∀{nni} → (vwi : View nni vci) → {noteqi : NotEqVVec (vwToVec vwi)} → ASFunF vci vco vcoi tf vwi {noteqi}


  fnToASFun : ∀{len} → (w : ℕ) → (tf : TFun len) → {{lt : suc w ≤ len}} → (∃ λ len → ∃ λ tf → ∃ λ li → ∃ λ lo → ∃ λ loi → ∃ λ vci → ∃ λ vco → ∃ λ vcoi → ASFunFT {len} {li} {lo} {loi} vci vco vcoi tf)
  fnToASFun zero (nextTF tf x) ⦃ lth ⦄ = _ , _ , _ , _ , _ , _ , _ , _ , x
  fnToASFun zero emptyTF ⦃ () ⦄
  fnToASFun (suc w) (nextTF tf x) ⦃ s≤s ⦄ = fnToASFun w tf



-- Check that this is necessary and there isn't an easier solution.
  applyArgs-abs : ∀ {tnsi len li lo loi ri} {vcri : Vec ASType ri}
                  (vwri : View tnsi vcri) {noteqri : NotEqVVec (vwToVec vwri)}
                  {vci : Vec ASType li} {vco : Vec ASType lo} {vcoi : Vec ASType loi} {tf : TFun len} →
                (∀ {nni} (vwi : View nni vci) {noteqi : NotEqVVec (vwToVec vwi)} →
                 ASFunF vci vco vcoi tf vwi {noteqi}) →
                Σ (ri ≡ li) (λ leq → subst (Vec ASType) leq vcri ≡ vci) →
                ASFunF vcri vco vcoi tf vwri {noteqri}
  applyArgs-abs vwri asft (refl , refl) = asft vwri


  applyArgs : ∀{tnsi len li lo loi ri} → {vcri : Vec ASType ri} → (vwri : View tnsi vcri) → {noteqri : NotEqVVec (vwToVec vwri)} → {vci : Vec ASType li}
              → EqVec vcri vci → {vco : Vec ASType lo} → {vcoi : Vec ASType loi} → {tf : TFun len} → ASFunFT vci vco vcoi tf → ASFunF vcri vco vcoi tf vwri {noteqri}
  applyArgs vwri eqvec asft = applyArgs-abs vwri asft (eqVecTo≡ eqvec)




  data LFun {len tnsi} (lnsi : LNames tnsi) {noteqi : NotEqVVec (proj₂ (lnToVec lnsi))} {tnso} (lnso : LNames tnso) {noteqo : NotEqVVec (proj₂ (lnToVec lnso))} (tf : TFun len) : Set where 
    call : (lvw : LView lnsi) → {{noteqLVW : NotEqVVec (proj₂ (lvwToVec lvw))}} 
           → (fn : FName) → {{flth : suc (len ∸ FName.pos fn) ≤ len}} → 
           let toVW = lvwToVW lvw
               vc = proj₁ (proj₂ toVW)
               vw = proj₂ (proj₂ toVW)
               gneq = lneqToNeq lnsi noteqi lvw noteqLVW
               toASF = fnToASFun (len ∸ FName.pos fn) tf
               asft = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ toASF)))))))
               vci = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ toASF)))))
           in {{iteq : EqVec vc vci}} →
           let asf = applyArgs vw {gneq} iteq asft
           in {!asf!}




  data ASFun {li lo loi nni nf} {vci : Vec ASType li} (vwi : View nni vci) {noteqi : NotEqVVec (vwToVec vwi)}
             {vco : Vec ASType lo} {nno} (vwo : View nno vco) {vcoi : Vec ASType loi} {vwoi : View nno vcoi} {noteqo : NotEqVVec ((vwToVec vwo) ++ (vwToVec vwoi))} (tf : TFun nf) : Set where
