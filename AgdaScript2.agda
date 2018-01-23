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





mutual


  data TFun : (len : ℕ) → Set where
    nextTF : ∀{len li lo} → {vci : Vec ASType li} → {vco : Vec ASType lo} → (tf : TFun len) → ASFunFT vci vco tf → TFun (suc len)
-- ? is this needed?  nextFunDef : ∀{n li lo} → {vci : Vec ASType (suc li)} → {vco : Vec ASType lo} → (tf : TFun n) → ? → TFun (suc n) -- Maybe here we need to have a (function) projection to the first two parts of the Sigma from ASFunFT
    emptyTF : TFun 0



  record ASFunF {len li lo} (vci : Vec ASType li) (vco : Vec ASType lo) (tf : TFun len) {tnsi} (vwi : View tnsi vci) {noteqi : NotEqVVec (vwToVec vwi)} : Set where
    field
      tnso : TNames
      vwo : View tnso vco
      lnso : LNames tnso
      noteqo : NotEqVVec (vwToVec vwo)
      gtv : GT (tns-length tnsi) (vwToVec vwo)
      tnop : TNOp tnsi (vwToVec vwi) tnso
      asf : ASFun vwi {noteqi} vwo {noteqo} tf {gtv} {tnop} {lnso}


  ASFunFT : ∀{len li lo} → (vci : Vec ASType li) → (vco : Vec ASType lo) → (tf : TFun len) → Set
  ASFunFT {len} {li} {lo} vci vco tf = ∀{nni} → (vwi : View nni vci) → {noteqi : NotEqVVec (vwToVec vwi)} → ASFunF vci vco tf vwi {noteqi}

  record FName {li lo} (vci : Vec ASType li) (vco : Vec ASType lo) : Set where
    field
      pos : ℕ

-- ℕ here is the difference between pos fname and len as in LFun.
  data _⊂f_ {li lo} {vci : Vec ASType li} {vco : Vec ASType lo} : ∀{len} → FName vci vco → (tf : TFun len) → Set where
    instance
      there : {nf : FName vci vco} → ∀{ilen ili ilo} → {ivci : Vec ASType ili} → {ivco : Vec ASType ilo} → {itf : TFun ilen} → {asft : ASFunFT ivci ivco itf} → {{is : nf ⊂f itf}} → (record {pos = suc (FName.pos nf)}) ⊂f (nextTF itf asft)
      here : ∀{ilen} → {itf : TFun ilen} → {asft : ASFunFT vci vco itf} → (record {pos = zero}) ⊂f (nextTF itf asft)



  fnToASFun : ∀{len li lo} → {vci : Vec ASType li} → {vco : Vec ASType lo} → (cfn : FName vci vco) → (tf : TFun len) → {{sub : cfn ⊂f tf}} → (∃ λ len → ∃ λ tf → ASFunFT {len} {li} {lo} vci vco tf)
  fnToASFun _ (nextTF tf _) ⦃ there {nf}⦄ = fnToASFun nf tf
  fnToASFun _ (nextTF _ asft) ⦃ here ⦄ = _ , _ , asft




  data LFun {len tnsi} (lnsi : LNames tnsi) {noteqi : NotEqVVec (proj₂ (lnToVec lnsi))} {tnso} (lnso : LNames tnso) {noteqo : NotEqVVec (proj₂ (lnToVec lnso))} (tf : TFun len) : Set where 
    call : ∀{li} → {vci : Vec ASType li} → (lvw : LView lnsi vci) → {{noteqLVW : NotEqVVec (lvwToVec lvw)}} 
           → ∀{lo} → {vco : Vec ASType lo} → (fn : FName vci vco) →
           let cfname : FName vci vco
               cfname = record { pos = len ∸ (FName.pos fn)}
           in {{ fnExists : cfname ⊂f tf}} → 
           let vwi = lvwToVW lvw
               gneq = lneqToNeq lnsi noteqi lvw noteqLVW
               toASF = fnToASFun {vci = vci} {vco = vco} cfname tf
               asft = {!!} -- proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ toASF)))))
               asf = {!!}
           in LFun  {!!} {{!!}} lnso {noteqo} tf → LFun _ _ _
    id : LFun _ _ _



  -- lnso here is the remaining input that can be reused in the order that it was received so as to be able to update the local names of the calling function
  -- by using it.
  data ASFun {li lo tnsi nf} {vci : Vec ASType li} (vwi : View tnsi vci) {noteqi : NotEqVVec (vwToVec vwi)}
             {vco : Vec ASType lo} {tnso} (vwo : View tnso vco) {noteqo : NotEqVVec (vwToVec vwo)} (tf : TFun nf)
             {gtv : GT (tns-length tnsi) (vwToVec vwo)}
             {tnop : TNOp tnsi (vwToVec vwi) tnso} : {lnso : LNames tnso} → Set where

    asfCon : {lnsol : LNames tnso} → {noteqol : NotEqVVec (proj₂ (lnToVec lnsol))}
             → (lfun : LFun (vwToLns vwi) {lnToVec$vwToLns≡vwToVecP {vw = vwi} {P = NotEqVVec} noteqi} lnsol {noteqol} tf)
             → (lvwoRem : LView (lnsCutToLenRem lnsol (vw-len vwi)) vco)
             → {{vwoEq : vwo ≡ lvwToVW lvwoRem}} -- Theoretically this should be proved by instance resolution.
                                                              -- Let's see if it does.
             → ASFun _ _ _ {{!!}} {{!!}} {lnsCutToLen lnsol (vw-len vwi)}



-- bol : ∀{tnsi len li lo} → {lnsi : LNames tnsi} → (vci : Vec ASType li) → (lvw : LView lnsi vci) → (vco : Vec ASType lo) → {tf : TFun len} → (vwi : View tnsi vci) → {noteqi : NotEqVVec (vwToVec vwi)}
--       → (asf : ASFunF vci vco tf vwi {noteqi}) → {!!}
-- bol = {!!}
