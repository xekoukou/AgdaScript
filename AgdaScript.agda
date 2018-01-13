module AgdaScript where


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
open import Nat
open import NNotEqM


open RawMonad (monad {Level.zero})


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


nn-len : TNames → ℕ
nn-len (icn tns x x₁) = suc (nn-len tns)
nn-len ln = zero

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


∈ₙ-len : ∀{n nn} → n ∈ₙ nn → suc (proj₁ n) ≤ nn-len nn
∈ₙ-len (icb {{beq}}) = s≤s {{∈ₙ-len beq}}
∈ₙ-len licb = s≤s


-- This required ASType Equality. This is ok because the types here are very basic.
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
addN : (pnn : TNames) → (ast : ASType) → Σ TNames (λ x → Σ _ (λ n → (Name (n , ast) {x} × (nn-len pnn ≤ n))))
addN (icn nn x x₁) ast = icn (proj₁ r) x x₁ , suc (proj₁ (proj₂ r)) , (icb {{proj₁ (proj₂ (proj₂ r))}}) , (s≤s {{proj₂ (proj₂ (proj₂ r))}}) where 
  r = addN nn ast
addN ln ast = icn ln ast true , zero , (it , z≤n)




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
    icv : ∀{l} → ∀ n → {{beq : n ∈ₙ nn}} → ∀{vc : Vec ASType (suc l)} → (vw : View nn vc) → {{neqv : NNotEqVec (proj₁ n) (vToVec vw)}} → View nn ((proj₂ n) ∷ vc)
    lv : ∀ n → {{beq : n ∈ₙ nn}} → View nn ((proj₂ n) ∷ [])


  vToVec : {nn : TNames} → ∀{l} → {vc : Vec ASType l} → View nn vc → Vec ℕ l
  vToVec (icv n vw) = proj₁ n ∷ (vToVec vw)
  vToVec (lv n) = proj₁ n ∷ []




nnotEqVec?-abs : ∀ {l} {n₁ : Tℕ} {n} → 
                 Dec (NNotEq n (proj₁ n₁)) →
                 {vec : Vec ℕ l} →
                 Dec (NNotEqVec n vec) →
                 Dec (NNotEqVec n (proj₁ n₁ ∷ vec))
nnotEqVec?-abs (yes p) (yes p₁) = yes (neicvec {{p}} {{p₁}})
nnotEqVec?-abs (yes p) (no ¬p) = no λ { (neicvec {{ieq = ieq}}) → ¬p ieq}
nnotEqVec?-abs (no ¬p) deq1 = no λ { neicvec → ¬p it}

nnotEqVec? : ∀{nn} (n : ℕ) → ∀{l} → {vc : Vec ASType l} → (vw : View nn vc) → Dec (NNotEqVec n (vToVec vw))
nnotEqVec? n (icv n₁ vw) = nnotEqVec?-abs {n₁ = n₁} (nnotEq? n (proj₁ n₁)) {vToVec vw} (nnotEqVec? n vw)
nnotEqVec? n (lv n₁) = nnotEqVec?-abs {n₁ = n₁} (nnotEq? n (proj₁ n₁)) {[]} (yes nelvec)




prepend-abs : ∀ {nn ll} {vcl : Vec ASType ll} (n : Tℕ) {{beq : n ∈ₙ nn}}
                (w : Σ ℕ (λ l → Σ (Vec ASType l) (λ vc → View nn (vc ++ vcl)))) →
              Dec (NNotEqVec (proj₁ n) (vToVec (proj₂ (proj₂ w)))) →
              Σ ℕ (λ l → Σ (Vec ASType l) (λ vc → View nn (vc ++ vcl)))
prepend-abs {vcl = []} n (zero , [] , vw) (yes p) = suc zero , (proj₂ n) ∷ [] , lv n
prepend-abs {vcl = vcl@(_ ∷ _)} n (zero , [] , vw) (yes p) = suc zero , (proj₂ n) ∷ [] , icv n vw {{p}}
prepend-abs n (suc l , vc , vw) (yes p) = (suc (suc l)) , (proj₂ n) ∷ vc , icv n vw {{p}}
prepend-abs n r (no ¬p) = r


-- We prepend all the elements that are not in the first view
_prepend_ : ∀{nn ll lr} → {vcl : Vec ASType ll} → {vcr : Vec ASType lr} → View nn vcl → View nn vcr → Σ _ (λ l → Σ (Vec ASType l) (λ vc → View nn (vc ++ vcl)))
vwl prepend icv n vwr = prepend-abs n r (nnotEqVec? (proj₁ n) (proj₂ (proj₂ r))) where
  r = vwl prepend vwr
vwl prepend (lv n) = prepend-abs n (0 , ([] , vwl)) (nnotEqVec? (proj₁ n) vwl)


_mprepend_ : ∀{nn ll} → {vcl : Vec ASType (suc ll)} → View nn vcl → Maybe (Σ _ (λ l → Σ (Vec ASType (suc l)) (λ vcr → View nn vcr))) → Σ _ (λ l → Σ (Vec ASType l) (λ vc → View nn (vc ++ vcl)))
vwl mprepend just (proj₃ , proj₄ , x) = vwl prepend x
vwl mprepend nothing = zero , [] , vwl

toNorm : ∀{nn ll} → {vcl : Vec ASType (suc ll)}
       → Σ _ (λ l → Σ (Vec ASType l) (λ vc → View nn (vc ++ vcl)))
       → Σ _ (λ l → Σ (Vec ASType (suc l)) (λ vc → View nn vc))
toNorm {ll = ll} {vcl} (zero , [] , y) = ll , vcl , y
toNorm {ll = ll} {vcl} (suc l , vc , vw) = l + suc ll , vc ++ vcl , vw


-- Instance resolution will fail if there are two arguments with the same name , aka having the name n in two names of a view.
-- Otherwise I assume that this will succeed.

data _∈ᵢ_ {nn} (n : Tℕ) : ∀{l} → {vc : Vec ASType l} → View nn vc → Set where
  instance
    icvb : ∀{nc l} → {vc : Vec ASType (suc l)} → {vw : View nn vc} → {{beq : nc ∈ₙ nn}} → {{neqv : NNotEqVec (proj₁ nc) (vToVec vw)}} → {{ieq : n ∈ᵢ vw}} → n ∈ᵢ (icv nc vw {{neqv = neqv}}) 
    licvb : ∀{l} → {vc : Vec ASType (suc l)} → {vw : View nn vc} → {{beq : n ∈ₙ nn}} → {{neqv : NNotEqVec (proj₁ n) (vToVec vw)}} → n ∈ᵢ (icv n vw {{neqv}}) 
    licvblv : {{beq : n ∈ₙ nn}} → n ∈ᵢ (lv n)



∈¬∈⇒¬≡ : ∀ {nn nᵢ nₒ l} → {vc : Vec ASType l} → {vw : View nn vc} → {{eq : nᵢ ∈ᵢ vw}} → ¬ (nₒ ∈ᵢ vw) → ¬ (nᵢ ≡ nₒ)
∈¬∈⇒¬≡ {vw = icv n vw} {{icvb}} ¬eq = ∈¬∈⇒¬≡ λ {x → ¬eq (icvb {{ieq = x}})}
∈¬∈⇒¬≡ {vw = icv n vw} {{licvb}} ¬eq = λ { refl → ⊥-elim (¬eq licvb)}
∈¬∈⇒¬≡ {vw = lv n} {{licvblv}} ¬eq = λ { refl → ⊥-elim (¬eq licvblv)}




data _⊃ᵢ_ {nn} {ll} {vcl : Vec ASType ll} (vl : View nn vcl) : ∀{lr} → {vcr : Vec ASType lr} → View nn vcr → Set where
  instance
    icvvb : ∀{l n} → {vc : Vec ASType (suc l)} → {vw : View nn vc} → {{eq : n ∈ₙ nn}} → {{beq : n ∈ᵢ vl}} → {{neqv : NNotEqVec (proj₁ n) (vToVec vw)}} → {{ieq : vl ⊃ᵢ vw}} → vl ⊃ᵢ (icv n vw {{neqv}}) 
    llvb : ∀{n} → {{eq : n ∈ₙ nn}} → {{beq : n ∈ᵢ vl}} → vl ⊃ᵢ (lv n) 


data _⊃ₑᵢ_wt_ {nn} {ll} {vcl : Vec ASType ll} (vl : View nn vcl) : ∀{lr} → Vec ℕ (suc lr) → (vcr : Vec ASType (suc lr)) → Set where
  instance
    icvvbb : ∀{l n ast} → {vc : Vec ASType (suc l)} → {vw : Vec ℕ (suc l)} → {{beq : (n , ast) ∈ᵢ vl}} → {{ieq : vl ⊃ₑᵢ vw wt vc}} → vl ⊃ₑᵢ (n ∷ vw) wt (ast ∷ vc)
    llvbb : ∀{n ast} → {{beq : (n , ast) ∈ᵢ vl}} → vl ⊃ₑᵢ (n ∷ []) wt (ast ∷ []) 







belToName : ∀{n nn ll} {vcl : Vec ASType ll} {vl : View nn vcl} → (n ∈ᵢ vl) → Name n {nn}
belToName (icvb {{ieq = ieq}}) = belToName ieq
belToName licvb = it
belToName licvblv = it

module _ where

  private
    tol : ∀{nn lr} → {vcr : Vec ASType (suc lr)} → {vw : Vec ℕ (suc lr)} → (vwr : View nn vcr) → Set
    tol {vw = vw} (icv n ivw) = vw ⊃ (vToVec ivw)
    tol {vw = vw} (lv n) = vw ⊃ []

  supToView' : ∀{nn ll} {vcl : Vec ASType ll} {vl : View nn vcl} → ∀{lr} → {vcr : Vec ASType (suc lr)} → {vw : Vec ℕ (suc lr)} → {{ieq : NNotEqVVec vw}}
              → (sup : vl ⊃ₑᵢ vw wt vcr) → Σ {b = Level.zero} (View nn vcr) (tol {vw = vw})
  supToView' {nn = nn} {vcr = x ∷ vcr} {vw = nc ∷ vw} ⦃ neicvvec {{neq}}⦄ (icvvbb {n = n} {ast} ⦃ beq = beq ⦄ ⦃ ieq ⦄) = q is , {!!} where -- n∷⊃ nc (proj₂ is) where
    r = belToName beq
    is = supToView' ieq
    q : Σ {b = Level.zero} (View nn vcr) tol → View nn (x ∷ vcr) 
    q (ivw@(icv _ _) , sup) = icv (n , ast) {{beq = r}} ivw {{neqv = {!nnotEqVec-⊃ n {{sup}} {{neq}}!}}}
    q (lv n , sup) = {!!} -- icv (n , ast) {{beq = r}} (proj₁ is) {{neqv = {!nnotEqVec-⊃ n {{proj₂ is}} {{neq}}!}}}
  supToView' (llvbb {n} {ast} {{beq}}) = lv (n , ast) {{belToName beq}} , ec⊃
  
  supToView : ∀{nn ll} {vcl : Vec ASType ll} {vl : View nn vcl} → ∀{lr} → {vcr : Vec ASType (suc lr)} → {vw : Vec ℕ (suc lr)} → {{ieq : NNotEqVVec vw}}
              → (sup : vl ⊃ₑᵢ vw wt vcr) → (View nn vcr)
  supToView sup = proj₁ (supToView' sup)
  



 
-- data PrimASFun {nni} : ∀{li lo} → {vci : Vec ASType li} → View nni vci → {vco : Vec ASType lo} → ∀{nno} → View nno vco → Set where
--   ←+ₚ : ∀ {n1 n2} → {{eq1 : (n1 , int32) ∈ₙ nni}} → {{eq2 : (n2 , int32) ∈ₙ nni}} → {{neq : NNotEqVec n1 (n2 ∷ [])}}
--           → let k = remN nni eq1
--                 r = addN k int32
--                 j = nmorph-r {nn = nni} eq1 eq2 {{elimNNotEqVec neq}}
--                 g = nmorph-a {int32} j in
--             PrimASFun (icv (n1 , int32) (lv (n2 , int32)) {{neq}}) (icv (tpos (proj₁ (proj₂ (proj₂ r)))) {{beq = proj₁ (proj₂ (proj₂ r))}} (lv (n2 , _) {{beq = g}})
--                       {{neicvec {{nnotEq-sym (slt⇒NNotEq (transitℕ (∈ₙ-len j) ((proj₂ (proj₂ (proj₂ r))))))}} {{nelvec}}}})


-- mutual

  
--   restV-morph'-abs : ∀ {l} {vc : Vec ASType (suc l)} {nni nno} n →
--                     Dec (n ∈ₙ nno) →
--                     (vwi : View nni vc) ⦃ neqv : NNotEqVec (proj₁ n) (vToVec vwi) ⦄ →
--                     Maybe
--                      (Σ ℕ
--                        (λ l₁ →
--                          Σ (Vec ASType (suc l₁))
--                           (λ vc₁ →
--                             Σ (View nno vc₁) (λ vw → (proj₁ n ∷ vToVec vwi) ⊃ vToVec vw))))
--   restV-morph'-abs {nno = nno} n (yes p) vwi ⦃ neqv ⦄
--       = (restV-morph' {nno = nno} vwi)
--         >>= λ { (rl , rvc , rvw , rsup) → just ((suc rl , proj₂ n ∷ rvc , icv n {{beq = p}} rvw {{nnotEqVec-⊃ (proj₁ n) {{rsup}} {{neqv}}}} , n∷⊃ (proj₁ n) rsup))}
--   restV-morph'-abs {nno = nno} n (no ¬p) vwi ⦃ neqv ⦄ = (restV-morph' vwi) >>= λ { (rl , rvc , rvw , rsup) → just (rl , rvc , rvw , ln∷⊃ (proj₁ n) rsup)}


--   restV-morph'-abs2 : ∀ {nno} n →
--                     Dec (n ∈ₙ nno) →
--                     Maybe 
--                      (Σ ℕ (λ l →
--                        Σ (Vec ASType (suc l))
--                        (λ vc → Σ (View nno vc) (λ vw → (proj₁ n ∷ []) ⊃ vToVec vw))))
--   restV-morph'-abs2 n (yes p) = just (p asInst 0 , (_ , ((lv n) , ic⊃)))
--   restV-morph'-abs2 n (no ¬p) = nothing 


--   restV-morph' : ∀{li nni nno} {vci : Vec ASType (suc li)} (vwi : View nni vci) → Maybe (Σ _ (λ l → Σ (Vec ASType (suc l)) (λ vc → Σ (View nno vc) (λ vw → (vToVec vwi) ⊃ (vToVec vw)))))
--   restV-morph' {nno = nno} (icv n vwi {{neqv}}) = restV-morph'-abs n (n ∈ₙ? nno) vwi {{neqv}}
--   restV-morph' {nno = nno} (lv n) = restV-morph'-abs2 n (n ∈ₙ? nno) 

-- restV-morph : ∀{li nni nno} {vci : Vec ASType (suc li)} (vwi : View nni vci) → Maybe (Σ _ (λ l → Σ (Vec ASType (suc l)) (λ vc → View nno vc)))
-- restV-morph vwi = (restV-morph' vwi)
--         >>= λ { (rl , rvc , rvw , _) → just (rl , rvc , rvw)}




-- mutual 


--   data TFun : ℕ → Set where
--       icasf : ∀{n li lo} → {vci : Vec ASType (suc li)} → {vco : Vec ASType lo} → (tf : TFun n) → ASFunFT vci vco tf → TFun (suc n)
--       lf : TFun zero


--   ASFunFT : ∀{n li lo} → (vci : Vec ASType (suc li)) → (vco : Vec ASType lo) → (tf : TFun n) → Set
--   ASFunFT {n} {li} {lo} vci vco tf = ∀{nni} → (vwi : View nni vci) → Σ TNames (λ nno → Σ (View nno vco) (λ vwo → ASFun vwi vwo tf))



--   data _∈f_ {li lo} {vci : Vec ASType (suc li)} {vco : Vec ASType lo} : ∀{nf} → ℕ → TFun nf → Set where
--     instance
--       icb : ∀{n lli llo nf} → {lvci : Vec ASType (suc lli)} → {lvco : Vec ASType llo} → {tf : TFun nf} → {asf : ASFunFT lvci lvco tf} → _∈f_ {vci = vci} {vco = vco} n tf → (suc n) ∈f icasf tf asf 
--       ln : ∀{nf} → {tf : TFun nf} → {asf : ASFunFT vci vco tf} → zero ∈f icasf tf asf



--   outF : ∀{nni lli llo} {lvci : Vec ASType (suc lli)} (lvwi : View nni lvci) {lvco : Vec ASType (suc llo)} → ∀{nf} → {fnM : ℕ} → {tf : TFun nf} → (feq : _∈f_ {vci = lvci} {vco = lvco} fnM tf) → Σ TNames (λ nno → View nno lvco)
--   outF lvwi {nf = .(suc _)} {.(suc _)} (icb inf) = outF lvwi inf
--   outF lvwi {nf = .(suc _)} {.0} (ln {asf = asf}) = proj₁ (asf lvwi) , proj₁ (proj₂ (asf lvwi)) 



--   data ASFun {li lo nni nf} {vci : Vec ASType (suc li)} (vwi : View nni vci) {vco : Vec ASType lo} {nno} (vwo : View nno vco) (tf : TFun nf) : Set where
--     call : ∀{lli llo}
--            → {lvci : Vec ASType (suc lli)} → {lvco : Vec ASType (suc llo)}
--            → (lvwi : Vec ℕ (suc lli)) → {{neq : NNotEqVVec lvwi}}
--            → {{seq : vwi ⊃ₑᵢ lvwi wt lvci}}
--            → (fn : ℕ) → {{feq : _∈f_ {vci = lvci} {vco = lvco} (nf ∸ fn) tf}}
--            → let outf = outF (supToView seq) feq 
--                  mpr = toNorm ((proj₂ outf) mprepend (restV-morph {nno = proj₁ outf} vwi)) in
--              ASFun {nni = proj₁ outf} (proj₂ (proj₂ mpr)) vwo tf 
--            → ASFun vwi vwo tf
--     primF : PrimASFun vwi vwo → ASFun vwi vwo tf
--     idF  : ASFun vwi vwo tf






-- addF : ∀{li lo nf} {vci : Vec ASType (suc li)} {vco : Vec ASType (suc lo)} (tf : TFun nf) (asf : ASFunFT vci vco tf) → ℕ × TFun (suc nf)
-- addF {nf = nf} tf as = nf , icasf tf as



