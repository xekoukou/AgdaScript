module AgdaScript2 where



open import Data.Maybe
open import Data.Bool
open import Data.Nat hiding (_≤_ ; _≤?_ ; ≤-pred)
open import Data.Vec hiding (_>>=_)
open import Data.Product
open import Relation.Nullary
open import Data.Empty

import Level using (zero)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality
open import Category.Monad


open import Common

open import LNames2

open RawMonad (Data.Maybe.monad {Level.zero})





record FName : Set where
  field
    pos : ℕ

mutual


  data TFun : (len : ℕ) → Set where
    nextTF : ∀{len li lo loi} → {vci : Vec ASType li} → {vco : Vec ASType lo} → {vcoi : Vec ASType loi} → (tf : TFun len) → ASFunFT vci vco tf → TFun (suc len)
-- ? is this needed?  nextFunDef : ∀{n li lo} → {vci : Vec ASType (suc li)} → {vco : Vec ASType lo} → (tf : TFun n) → ? → TFun (suc n) -- Maybe here we need to have a (function) projection to the first two parts of the Sigma from ASFunFT
    emptyTF : TFun 0



  record ASFunF {len li lo} (vci : Vec ASType li) (vco : Vec ASType lo) (tf : TFun len) {tnsi} (vwi : View tnsi vci) {noteqi : NotEqVVec (vwToVec vwi)} : Set where
    field
      tnso : TNames
      vwo : View tnso vco
      lnso : LNames tnso
      noteqo : NotEqVVec (vwToVec vwo)
      asf : ASFun vwi {noteqi} vwo {noteqo} tf  {lnso}


  ASFunFT : ∀{len li lo} → (vci : Vec ASType li) → (vco : Vec ASType lo) → (tf : TFun len) → Set
  ASFunFT {len} {li} {lo} vci vco tf = ∀{nni} → (vwi : View nni vci) → {noteqi : NotEqVVec (vwToVec vwi)} → ASFunF vci vco tf vwi {noteqi}


  fnToASFun : ∀{len} → (w : ℕ) → (tf : TFun len) → {{lt : suc w ≤ len}} → (∃ λ len → ∃ λ tf → ∃ λ li → ∃ λ lo → ∃ λ vci → ∃ λ vco → ASFunFT {len} {li} {lo} vci vco tf)
  fnToASFun zero (nextTF tf x) ⦃ lth ⦄ = _ , _ , _ , _ , _ , _ , x
  fnToASFun zero emptyTF ⦃ () ⦄
  fnToASFun (suc w) (nextTF tf x) ⦃ s≤s ⦄ = fnToASFun w tf



-- Check that this is necessary and there isn't an easier solution.
  applyArgs-abs : ∀ {tnsi len li lo ri} {vcri : Vec ASType ri}
                  (vwri : View tnsi vcri) {noteqri : NotEqVVec (vwToVec vwri)}
                  {vci : Vec ASType li} {vco : Vec ASType lo} {tf : TFun len} →
                (∀ {nni} (vwi : View nni vci) {noteqi : NotEqVVec (vwToVec vwi)} →
                 ASFunF vci vco tf vwi {noteqi}) →
                Σ (ri ≡ li) (λ leq → subst (Vec ASType) leq vcri ≡ vci) →
                ASFunF vcri vco tf vwri {noteqri}
  applyArgs-abs vwri asft (refl , refl) = asft vwri


  applyArgs : ∀{tnsi len li lo ri} → {vcri : Vec ASType ri} → (vwri : View tnsi vcri) → {noteqri : NotEqVVec (vwToVec vwri)} → {vci : Vec ASType li}
              → EqVec vcri vci → {vco : Vec ASType lo} → {tf : TFun len} → ASFunFT vci vco tf → ASFunF vcri vco tf vwri {noteqri}
  applyArgs vwri eqvec asft = applyArgs-abs vwri asft (eqVecTo≡ eqvec)




  data LFun {len tnsi} (lnsi : LNames tnsi) {noteqi : NotEqVVec (proj₂ (lnToVec lnsi))} {tnso} (lnso : LNames tnso) {noteqo : NotEqVVec (proj₂ (lnToVec lnso))} (tf : TFun len) : Set where 
    call : (lvw : LView lnsi) → {{noteqLVW : NotEqVVec (proj₂ (lvwToVec lvw))}} 
           → (fn : FName) → {{flth : suc (len ∸ FName.pos fn) ≤ len}} → 
           let toVW = lvwToVW lvw
               vc = proj₁ (proj₂ toVW)
               vw = proj₂ (proj₂ toVW)
               gneq = lneqToNeq lnsi noteqi lvw noteqLVW
               toASF = fnToASFun (len ∸ FName.pos fn) tf
               asft = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ toASF)))))
               vci = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ toASF))))
           in {{iteq : EqVec vc vci}} →
           let asf = applyArgs vw {gneq} iteq asft
           in {!asf!}



  -- lnso here is the remaining input that can be reused in the ordered that it was received so as to be able to update the local names of the calling function
  -- by using it.
  data ASFun {li lo tnsi nf} {vci : Vec ASType li} (vwi : View tnsi vci) {noteqi : NotEqVVec (vwToVec vwi)}
             {vco : Vec ASType lo} {tnso} (vwo : View tnso vco) {noteqo : NotEqVVec (vwToVec vwo)} (tf : TFun nf) : {lnso : LNames tnso} → Set where
    asfCon : (lfun : LFun (vwToLns vwi) {lnToVec$vwToLns≡vwToVecP {vw = vwi} {P = NotEqVVec} noteqi} (vwToLns vwo) {lnToVec$vwToLns≡vwToVecP {vw = vwo} {P = NotEqVVec} noteqo} tf) → ASFun _ _ _ {{!!}}
