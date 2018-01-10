module AgdaScript where


open import Data.Bool
open import Data.Nat hiding (_≤_ ; _≤?_ ; ≤-pred)
open import Data.Vec
open import Data.Product
open import Relation.Nullary
open import Data.Empty

import Level using (zero)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality

open import Common
open import Nat
open import NNotEqM




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


data TNames : Set where     
  icn : TNames → ASType → Bool → TNames
  ln : TNames


Tℕ : Set
Tℕ = ℕ × ASType

sucT : Tℕ → Tℕ
sucT (n , ast) = suc n , ast


noteq : ∀{n1 n2} → {ast1 ast2 : ASType} → suc n1 ≤ n2 → ¬ ((n1 , ast1) ≡ (n2 , ast2))
noteq {zero} {.0} () refl
noteq {suc n1} {.(suc n1)} {ast1} {ast2} (s≤s {{m≤n}}) refl = noteq {ast1 = ast1} {ast2} m≤n refl

-- This is generalizable
notsym :  ∀{n1 n2 : ℕ} → {ast1 ast2 : ASType} → ¬ ((n1 , ast1) ≡ (n2 , ast2)) → ¬ ((n2 , ast2) ≡ (n1 , ast1)) 
notsym neq refl = neq refl

data _∈ₙ_ : Tℕ → TNames → Set where
  instance
    icb : ∀{n nn b last} → {{beq : n ∈ₙ nn}} → sucT n ∈ₙ (icn nn last b)
    licb  : ∀{ast nn} → (zero , ast) ∈ₙ (icn nn ast true)


-- This required ASType Equality.
∈ₙ?-abs : ∀ {n ast nn} →
          Dec ((n , ast) ∈ₙ nn) → ∀ x y → Dec ((suc n , ast) ∈ₙ icn nn x y)
∈ₙ?-abs (yes p) x y = p asInst yes icb
∈ₙ?-abs (no ¬p) x y = no λ { (icb {{beq}}) → ¬p beq}


_∈ₙ?_ : (tn : Tℕ) → (nn : TNames) → Dec (tn ∈ₙ nn)
(zero , ast) ∈ₙ? icn nn x false = no λ ()
(zero , ast) ∈ₙ? icn nn x true with ast AST≡? x
((zero , ast) ∈ₙ? icn nn .ast true) | yes refl = yes licb
((zero , ast) ∈ₙ? icn nn x true) | no ¬p = no λ { licb → ¬p refl}
(zero , ast) ∈ₙ? ln = no (λ ())
(suc n , ast) ∈ₙ? icn nn x y = ∈ₙ?-abs ((n , ast) ∈ₙ? nn) x y
(suc n , ast) ∈ₙ? ln = no (λ ())



Name : ∀ n → {nn : TNames} → Set
Name n {nn} = n ∈ₙ nn


tpos : ∀{n nn} → Name n {nn} → Tℕ
tpos {n = n} x = n

pos : ∀{n nn} → Name n {nn} → ℕ
pos {n = n} x = proj₁ n

belongs : ∀{n nn} → (nm : Name n {nn}) → n ∈ₙ nn
belongs x = x

remN : ∀{n} → (nn : TNames) → Name n {nn} → TNames
remN {(zero , _)} (icn nn x₁ x₂) licb = icn nn x₁ false
remN {(suc n , ast)} (icn nn x₁ x₂) icb = icn (remN {(n , ast)} nn it) x₁ x₂

-- We add a new name at the end so as to preserve the name conversions.
addN : TNames → (ast : ASType) → Σ TNames (λ x → Σ _ (λ n → Name (n , ast) {x}))
addN (icn nn x x₁) ast = icn (proj₁ r) x x₁ , suc (proj₁ (proj₂ r)) , icb {{proj₂ (proj₂ r)}} where 
  r = addN nn ast
addN ln ast = icn ln ast true , zero , it




nmorph-r : ∀{nᵣ nₒ nn} → (inᵣ : Name nᵣ {nn}) → (inₒ : Name nₒ {nn}) → {{neq : NNotEq (pos inᵣ) (pos inₒ)}} → Name nₒ {remN nn inᵣ}
nmorph-r {zero , _} {zero , _} {icn nn x₁ x₂} inr ino ⦃ () ⦄
nmorph-r {zero , _} {suc n , _} {icn nn x₁ .true} licb icb = it
nmorph-r {suc n , _} {zero , _} {icn nn x₁ .true} icb licb = it
nmorph-r {suc n , _} {suc nₒ , _} {icn nn x₁ x₂} (icb {{inr}}) (icb {{ino}}) {{predNEq}}= r asInst icb  where
  r = nmorph-r {nn = nn} inr ino 
nmorph-r {zero , _} {zero , _} {ln} inr ino ⦃ () ⦄



nmorph-a : ∀{astₙ n nn} → (iin : Name n {nn}) → Name n {proj₁ (addN nn astₙ)}
nmorph-a {astₙ} {suc n , _} {icn nn x x₁} (icb {{iin}}) = r asInst icb  where
  r = nmorph-a {nn = nn} iin
nmorph-a {n = zero , _} {icn nn x .true} licb = it



mutual 

  data View (nn : TNames) : ∀{l} → Vec ASType l → Set where
    icv : ∀{l} → ∀ n → {{beq : n ∈ₙ nn}} → ∀{vc : Vec ASType l} → (vw : View nn vc) → {{neqv : NNotEqVec (proj₁ n) (vToVec vw)}} → View nn ((proj₂ n) ∷ vc)
    lv : View nn []


  vToVec : {nn : TNames} → ∀{l} → {vc : Vec ASType l} → View nn vc → Vec ℕ l
  vToVec (icv n vw) = proj₁ n ∷ (vToVec vw)
  vToVec lv = []



nnotEqVec?-abs : ∀ {l} {n₁ : Tℕ} {vc : Vec ASType l} {nn n}
                   {vw : View nn vc} →
                 Dec (NNotEq n (proj₁ n₁)) →
                 Dec (NNotEqVec n (vToVec vw)) →
                 Dec (NNotEqVec n (proj₁ n₁ ∷ vToVec vw))
nnotEqVec?-abs (yes p) (yes p₁) = yes (neicvec {{p}} {{p₁}})
nnotEqVec?-abs (yes p) (no ¬p) = no λ { neicvec → ¬p it}
nnotEqVec?-abs (no ¬p) deq1 = no λ { neicvec → ¬p it}

nnotEqVec? : ∀{nn} (n : ℕ) → ∀{l} → {vc : Vec ASType l} → (vw : View nn vc) → Dec (NNotEqVec n (vToVec vw))
nnotEqVec? n (icv n₁ vw) = nnotEqVec?-abs {n₁ = n₁} (nnotEq? n (proj₁ n₁)) (nnotEqVec? n vw)
nnotEqVec? n lv = yes nelvec



prepend-abs : ∀ {nn ll} {vcl : Vec ASType ll} (n : Tℕ) {{beq : n ∈ₙ nn}}
                (w : Σ ℕ (λ l → Σ (Vec ASType l) (λ vc → View nn (vc ++ vcl)))) →
              Dec (NNotEqVec (proj₁ n) (vToVec (proj₂ (proj₂ w)))) →
              Σ ℕ (λ l → Σ (Vec ASType l) (λ vc → View nn (vc ++ vcl)))
prepend-abs n r (yes p) = (suc (proj₁ r)) , ((proj₂ n ∷ (proj₁ (proj₂ r))) , icv n (proj₂ (proj₂ r)) {{p}})
prepend-abs n r (no ¬p) = r

-- We prepend all the elements that are not in the first view
_prepend_ : ∀{nn ll lr} → {vcl : Vec ASType ll} → {vcr : Vec ASType lr} → View nn vcl → View nn vcr → Σ _ (λ l → Σ (Vec ASType l) (λ vc → View nn (vc ++ vcl)))
vwl prepend icv n vwr = prepend-abs n r (nnotEqVec? (proj₁ n) (proj₂ (proj₂ r))) where
  r = vwl prepend vwr
vwl prepend lv = zero , [] , vwl




-- Instance resolution will fail if there are two arguments with the same name , aka having the name n in two names of a view.
-- Otherwise I assume that this will succeed.

data _∈ᵢ_ {nn} (n : Tℕ) : ∀{l} → {vc : Vec ASType l} → View nn vc → Set where
  instance
    icvb : ∀{nc l} → {vc : Vec ASType l} → {vw : View nn vc} → {{beq : nc ∈ₙ nn}} → {{neqv : NNotEqVec (proj₁ nc) (vToVec vw)}} → {{ieq : n ∈ᵢ vw}} → n ∈ᵢ (icv nc vw) 
    licvb : ∀{l} → {vc : Vec ASType l} → {vw : View nn vc} → {{beq : n ∈ₙ nn}} → {{neqv : NNotEqVec (proj₁ n) (vToVec vw)}} → n ∈ᵢ (icv n vw) 


∈¬∈⇒¬≡ : ∀ {nn nᵢ nₒ l} → {vc : Vec ASType l} → {vw : View nn vc} → {{eq : nᵢ ∈ᵢ vw}} → ¬ (nₒ ∈ᵢ vw) → ¬ (nᵢ ≡ nₒ)
∈¬∈⇒¬≡ {vw = icv n vw} {{icvb}} ¬eq = ∈¬∈⇒¬≡ λ {x → ¬eq (icvb {{ieq = x}})}
∈¬∈⇒¬≡ {vw = icv n vw} {{licvb}} ¬eq = λ { refl → ⊥-elim (¬eq licvb)}


-- 
-- remfVT : ∀{n nn l} → {vc : Vec ASType (suc l)} → (vw : View nn vc) → n ∈ᵢ vw → Vec ASType l
-- remfVT (icv _ {vc = vc} _) licvb = vc
-- remfVT (icv n vw@(icv _ _)) (icvb ⦃ ieq = ieq ⦄) = proj₂ n ∷ remfVT vw ieq
-- remfVT (icv n lv) (icvb ⦃ ieq = ieq ⦄) = []
-- 
-- remfV : ∀{n nn l} → {vc : Vec ASType (suc l)} → (vw : View nn vc) → (inv : n ∈ᵢ vw) → View nn (remfVT vw inv)
-- remfV (icv _ vw) licvb = vw
-- remfV (icv n vw@(icv _ _)) (icvb {{ieq = ieq}}) = icv n (remfV vw ieq)
-- remfV (icv n lv) icvb = lv
-- 
-- 
-- 
-- remfV-morph∈ : ∀{nr np nn l} → {vc : Vec ASType (suc l)} → (vw : View nn vc) → (invr : nr ∈ᵢ vw) → (invp : np ∈ᵢ vw) → ¬ (nr ≡ np) → np ∈ᵢ remfV vw invr
-- remfV-morph∈ .(icv _ _) licvb licvb neq = ⊥-elim (neq refl)
-- remfV-morph∈ .(icv _ _) licvb (icvb {{ieq = ieq}}) neq = ieq
-- remfV-morph∈ (icv _ (icv _ _)) icvb licvb neq = licvb
-- remfV-morph∈ (icv _ vw@(icv _ _)) (icvb {{ieq = ieqr}}) (icvb {{ieq = ieqp}}) neq = icvb {{ieq = remfV-morph∈ vw ieqr ieqp neq}}
-- remfV-morph∈ (icv _ lv) (icvb ⦃ ieq = () ⦄) invp neq
-- 
-- 


data _⊃ᵢ_ {nn} {ll} {vcl : Vec ASType ll} (vl : View nn vcl) : ∀{lr} → {vcr : Vec ASType lr} → View nn vcr → Set where
  instance
    icvvb : ∀{l n} → {vc : Vec ASType l} → {vw : View nn vc} → {{eq : n ∈ₙ nn}} → {{beq : n ∈ᵢ vl}} → {{neqv : NNotEqVec (proj₁ n) (vToVec vw)}} → {{ieq : vl ⊃ᵢ vw}} → vl ⊃ᵢ (icv n vw) 
    llvb : vl ⊃ᵢ lv 


data _⊃ₑᵢ_wt_ {nn} {ll} {vcl : Vec ASType ll} (vl : View nn vcl) : ∀{lr} → Vec ℕ lr → (vcr : Vec ASType lr) → Set where
  instance
    icvvbb : ∀{l n ast} → {vc : Vec ASType l} → {vw : Vec ℕ l} → {{beq : (n , ast) ∈ᵢ vl}} → {{ieq : vl ⊃ₑᵢ vw wt vc}} → vl ⊃ₑᵢ (n ∷ vw) wt (ast ∷ vc)
    llvbb : ∀{n ast} → {{beq : (n , ast) ∈ᵢ vl}} → vl ⊃ₑᵢ (n ∷ []) wt (ast ∷ []) 







belToName : ∀{n nn ll} {vcl : Vec ASType ll} {vl : View nn vcl} → (n ∈ᵢ vl) → Name n {nn}
belToName (icvb {{ieq = ieq}}) = belToName ieq
belToName licvb = it



supToView' : ∀{nn ll} {vcl : Vec ASType ll} {vl : View nn vcl} → ∀{lr} → {vcr : Vec ASType lr} → {vw : Vec ℕ lr} → {{ieq : NNotEqVVec vw}}
            → (sup : vl ⊃ₑᵢ vw wt vcr) → Σ (View nn vcr) (λ ivw → vw ⊃ (vToVec ivw))
supToView' {vcr = x ∷ vcr} {vw = nc ∷ vw} ⦃ neicvvec {{neq}}⦄ (icvvbb {n = n} {ast} ⦃ beq = beq ⦄ ⦃ ieq ⦄) = q , n∷⊃ nc (proj₂ is) where
  r = belToName beq
  is = supToView' ieq
  q = icv (n , ast) {{beq = r}} (proj₁ is) {{neqv = nnotEqVec-⊃ n (proj₂ is) neq}}
supToView' (llvbb {n} {ast} {{beq}}) = icv (n , ast) {{belToName beq}}  lv , ic⊃ here

supToView : ∀{nn ll} {vcl : Vec ASType ll} {vl : View nn vcl} → ∀{lr} → {vcr : Vec ASType lr} → {vw : Vec ℕ lr} → {{ieq : NNotEqVVec vw}}
            → (sup : vl ⊃ₑᵢ vw wt vcr) → (View nn vcr)
supToView sup = proj₁ (supToView' sup)






data PrimASFun : ∀{li lo nni} → {vci : Vec ASType li} → View nni vci → {vco : Vec ASType lo} → ∀{nno} → View nno vco → Set where
  _←+ₚ_ : ∀{nni} →  ∀ n1 n2 → {{eq1 : (n1 , int32) ∈ₙ nni}} → {{eq2 : (n2 , int32) ∈ₙ nni}} → {{neq : NNotEq (pos eq1) (pos eq2)}}
          → let k = remN nni eq1
                r = addN k int32
                g = nmorph-a {int32} (nmorph-r {nn = nni} eq1 eq2) in 
              PrimASFun {li = 2} {lo = 2} {nni} (icv (n1 , int32) (icv (n2 , int32) lv)) {nno = proj₁ r} (icv (tpos (proj₂ (proj₂ r))) {{beq = proj₂ (proj₂ r)}} (icv (n2 , _) {{beq = g}} lv {{nelvec}}) {{{!!}}})


mutual

  restV-morph-abs : ∀ {l} {vc : Vec ASType l} {nni nno} n →
                  Dec (n ∈ₙ nno) →
                  View nni vc → Σ ℕ (λ l₁ → Σ (Vec ASType l₁) (View nno))
  restV-morph-abs n (yes p) vw = suc rl , proj₂ n ∷ rvc , icv n {{beq = p}} rvw {{{!!}}} where
    r = restV-morph vw
    rl = proj₁ r
    rvc = proj₁ (proj₂ r)
    rvw = proj₂ (proj₂ r)
  restV-morph-abs n (no ¬p) vw = restV-morph vw

  restV-morph : ∀{li nni nno} {vci : Vec ASType li} (vwi : View nni vci) → Σ _ (λ l → Σ (Vec ASType l) (λ vc → View nno vc))
  restV-morph {nno = nno} (icv n vwi) = restV-morph-abs n (n ∈ₙ? nno) vwi
  restV-morph lv = zero , [] , lv


-- mutual 


--   data TFun : ℕ → Set where
--       icasf : ∀{n li lo} → {vci : Vec ASType li} → {vco : Vec ASType lo} → (tf : TFun n) → ASFunFT vci vco tf → TFun (suc n)
--       lf : TFun zero


--   ASFunFT : ∀{n li lo} → (vci : Vec ASType li) → (vco : Vec ASType lo) → (tf : TFun n) → Set
--   ASFunFT {n} {li} {lo} vci vco tf = ∀{nni} → (vwi : View nni vci) → Σ TNames (λ nno → Σ (View nno vco) (λ vwo → ASFun vwi vwo tf))



--   data _∈f_ {li lo} {vci : Vec ASType li} {vco : Vec ASType lo} : ∀{nf} → ℕ → TFun nf → Set where
--     instance
--       icb : ∀{n lli llo nf} → {lvci : Vec ASType lli} → {lvco : Vec ASType llo} → {tf : TFun nf} → {asf : ASFunFT lvci lvco tf} → _∈f_ {vci = vci} {vco = vco} n tf → (suc n) ∈f icasf tf asf 
--       ln : ∀{nf} → {tf : TFun nf} → {asf : ASFunFT vci vco tf} → zero ∈f icasf tf asf



--   outF : ∀{nni lli llo} {lvci : Vec ASType lli} (lvwi : View nni lvci) {lvco : Vec ASType llo} → ∀{nf} → {fnM : ℕ} → {tf : TFun nf} → (feq : _∈f_ {vci = lvci} {vco = lvco} fnM tf) → Σ TNames (λ nno → View nno lvco)
--   outF lvwi {nf = .(suc _)} {.(suc _)} (icb inf) = outF lvwi inf
--   outF lvwi {nf = .(suc _)} {.0} (ln {asf = asf}) = proj₁ (asf lvwi) , proj₁ (proj₂ (asf lvwi)) 



--   data ASFun {li lo nni nf} {vci : Vec ASType li} (vwi : View nni vci) {vco : Vec ASType lo} {nno} (vwo : View nno vco) (tf : TFun nf) : Set where
--     call : ∀{lli llo}
--            → {lvci : Vec ASType (suc lli)} → {lvco : Vec ASType llo}
--            → (lvwi : Vec ℕ (suc lli)) → {{neq : NNotEqVVec lvwi}}
--            → {{seq : vwi ⊃ₑᵢ lvwi wt lvci}}
--            → (fn : ℕ) → {{feq : _∈f_ {vci = lvci} {vco = lvco} (nf ∸ fn) tf}} → let outf = outF (supToView seq) feq in ASFun {nni = proj₁ outf} (proj₂ (proj₂ ((proj₂ outf) prepend (proj₂ (proj₂ (restV-morph vwi)))))) vwo tf → ASFun vwi vwo tf
--     primF : PrimASFun vwi vwo → ASFun vwi vwo tf
--     idF  : ASFun vwi vwo tf






-- addF : ∀{li lo nf} {vci : Vec ASType li} {vco : Vec ASType lo} (tf : TFun nf) (asf : ASFunFT vci vco tf) → ℕ × TFun (suc nf)
-- addF {nf = nf} tf as = nf , icasf tf as



