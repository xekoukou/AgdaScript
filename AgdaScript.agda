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

infixr 0 _asInst_

_asInst_ : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → ({{y : A}} → B y) → B x
x asInst f = f {{x}}

it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x



data _≤_ : Rel ℕ Level.zero where
  instance
    z≤n : ∀ {n}                 → zero  ≤ n
    s≤s : ∀ {m n} {{m≤n : m ≤ n}} → suc m ≤ suc n


≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred s≤s = it



transitℕ : ∀{a b c} → a ≤ b → b ≤ c → a ≤ c
transitℕ z≤n lt2 = z≤n
transitℕ (s≤s {{m≤n = lt1}}) (s≤s {{m≤n = lt2}}) = transitℕ lt1 lt2 asInst s≤s


more≤Ok : ∀{a b} → a ≤ b → a ≤ suc b
more≤Ok z≤n = z≤n
more≤Ok s≤s = s≤s {{m≤n = more≤Ok it}}


less≤Ok : ∀{a b} → suc a ≤ b → a ≤ b
less≤Ok s≤s = more≤Ok it

infix 4 _≤?_

_≤?_ : Decidable _≤_
zero  ≤? _     = yes z≤n
suc m ≤? zero  = no λ()
suc m ≤? suc n with m ≤? n
...            | yes m≤n = yes (m≤n asInst s≤s)
...            | no  m≰n = no  (m≰n ∘ ≤-pred)

neg-abs : (x : ℕ) → (y : ℕ) → Dec (x ≤ y) → (ℕ → ℕ)
neg-abs x y (yes p) = λ z → z + (y ∸ x)
neg-abs x y (no ¬p) = λ z → z ∸ (x ∸ y)

neg : ℕ → ℕ → (ℕ → ℕ)
neg x y = neg-abs x y (x ≤? y)


data VNO : ℕ → {se : ℕ} → Set where
  ivno : ∀{n se} → ∀ e → {lt : suc se ≤ e} → VNO n {se} → VNO (suc n) {e}
  evno : ∀ e → VNO (suc zero) {e}


toVNO-hf-abs : ∀ e (r : Σ _ (λ l → Σ _ (λ z → VNO l {z}))) →
               ∀{l se} → ∀ lt → VNO l {se} →
               Dec (suc (proj₁ (proj₂ r)) ≤ e) →
               Σ ℕ (λ l → Σ ℕ (λ z → VNO l {z}))
toVNO-hf-abs e r _ _ (yes p) = suc (proj₁ r) , e , ivno e {lt = p} (proj₂ (proj₂ r))
toVNO-hf-abs e r lt vno (no ¬p) = _ , _ , ivno e {lt} vno

toVNO-hf : ∀ {l se} → (n : ℕ) → Dec (suc se ≤ n) → VNO l {se} → Σ _ (λ l → Σ _ (λ z → VNO l {z}))
toVNO-hf n (yes p) vno = _ , n , ivno n {lt = p} vno
toVNO-hf n (no ¬p) (ivno {se = se} e {lt} vno) = toVNO-hf-abs e r lt vno (suc (proj₁ (proj₂ r)) ≤? e)  where
  r = toVNO-hf n (suc se ≤? n) vno
toVNO-hf n (no ¬p) (evno e) = _ , _ , evno e


toVNO-hf2 : ∀ {l se k} → Vec ℕ k → VNO l {se} → Σ _ (λ l → Σ _ (λ z → VNO l {z}))
toVNO-hf2 [] vno = _ , _ , vno
toVNO-hf2 {se = se} (x ∷ v) vno = toVNO-hf2 v (proj₂ (proj₂ (toVNO-hf x (suc se ≤? x) vno)))

toVNO : ∀ {n} → Vec ℕ (suc n) → Σ _ (λ l → Σ _ (λ z → VNO l {z}))
toVNO (x ∷ v) = toVNO-hf2 v (evno x)



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




nmorph-r : ∀{nᵣ nₒ nn} → (inᵣ : Name nᵣ {nn}) → (inₒ : Name nₒ {nn}) → ¬ ((pos inᵣ) ≡ (pos inₒ)) → Name nₒ {remN nn inᵣ}
nmorph-r {zero , _} {zero , _} {icn nn x₁ x₂} inr ino ¬eq = ⊥-elim (¬eq refl)
nmorph-r {zero , _} {suc n , _} {icn nn x₁ .true} licb icb ¬eq = it
nmorph-r {suc n , _} {zero , _} {icn nn x₁ .true} icb licb ¬eq = it
nmorph-r {suc n , _} {suc nₒ , _} {icn nn x₁ x₂} (icb {{inr}}) (icb {{ino}}) ¬eq = r asInst icb  where
  r = nmorph-r {nn = nn} inr ino (λ x → ¬eq (cong suc x))
nmorph-r {zero , _} {zero , _} {ln} inr ino ¬eq = ⊥-elim (¬eq refl)



nmorph-a : ∀{astₙ n nn} → (iin : Name n {nn}) → Name n {proj₁ (addN nn astₙ)}
nmorph-a {astₙ} {suc n , _} {icn nn x x₁} (icb {{iin}}) = r asInst icb  where
  r = nmorph-a {nn = nn} iin
nmorph-a {n = zero , _} {icn nn x .true} licb = it




-- A single name can be used multiple times in a view. Is this a feature or a bug? Probably it does not matter.
data View (nn : TNames) : ∀{l} → Vec ASType l → Set where
  icv : ∀{l} → ∀ n → {{beq : n ∈ₙ nn}} → ∀{vc : Vec ASType l} → View nn vc → View nn ((proj₂ n) ∷ vc)
  lv : View nn []




_∪ᵢ_ : ∀{nn ll lr} → {vcl : Vec ASType ll} → {vcr : Vec ASType lr} → View nn vcl → View nn vcr → View nn (vcl ++ vcr)
icv n vwl ∪ᵢ vwr = icv n (vwl ∪ᵢ vwr)
lv ∪ᵢ vwr = vwr


-- Instance resolution will fail if there are two arguments with the same name , aka having the name n in two names of a view.
-- Otherwise I assume that this will succeed.

data _∈ᵢ_ {nn} (n : Tℕ) : ∀{l} → {vc : Vec ASType l} → View nn vc → Set where
  instance
    icvb : ∀{nc l} → {vc : Vec ASType l} → {vw : View nn vc} → {{beq : nc ∈ₙ nn}} → {{ieq : n ∈ᵢ vw}} → n ∈ᵢ (icv nc vw) 
    licvb : ∀{l} → {vc : Vec ASType l} → {vw : View nn vc} → {{beq : n ∈ₙ nn}} → n ∈ᵢ (icv n vw) 


∈¬∈⇒¬≡ : ∀ {nn nᵢ nₒ l} → {vc : Vec ASType l} → {vw : View nn vc} → {{eq : nᵢ ∈ᵢ vw}} → ¬ (nₒ ∈ᵢ vw) → ¬ (nᵢ ≡ nₒ)
∈¬∈⇒¬≡ {vw = icv n vw} {{icvb}} ¬eq = ∈¬∈⇒¬≡ λ {x → ¬eq (icvb {{ieq = x}})}
∈¬∈⇒¬≡ {vw = icv n vw} {{licvb}} ¬eq = λ { refl → ⊥-elim (¬eq licvb)}



remfVT : ∀{n nn l} → {vc : Vec ASType (suc l)} → (vw : View nn vc) → n ∈ᵢ vw → Vec ASType l
remfVT (icv _ {vc = vc} _) licvb = vc
remfVT (icv n vw@(icv _ _)) (icvb ⦃ ieq = ieq ⦄) = proj₂ n ∷ remfVT vw ieq
remfVT (icv n lv) (icvb ⦃ ieq = ieq ⦄) = []

remfV : ∀{n nn l} → {vc : Vec ASType (suc l)} → (vw : View nn vc) → (inv : n ∈ᵢ vw) → View nn (remfVT vw inv)
remfV (icv _ vw) licvb = vw
remfV (icv n vw@(icv _ _)) (icvb {{ieq = ieq}}) = icv n (remfV vw ieq)
remfV (icv n lv) icvb = lv



remfV-morph∈ : ∀{nr np nn l} → {vc : Vec ASType (suc l)} → (vw : View nn vc) → (invr : nr ∈ᵢ vw) → (invp : np ∈ᵢ vw) → ¬ (nr ≡ np) → np ∈ᵢ remfV vw invr
remfV-morph∈ .(icv _ _) licvb licvb neq = ⊥-elim (neq refl)
remfV-morph∈ .(icv _ _) licvb (icvb {{ieq = ieq}}) neq = ieq
remfV-morph∈ (icv _ (icv _ _)) icvb licvb neq = licvb
remfV-morph∈ (icv _ vw@(icv _ _)) (icvb {{ieq = ieqr}}) (icvb {{ieq = ieqp}}) neq = icvb {{ieq = remfV-morph∈ vw ieqr ieqp neq}}
remfV-morph∈ (icv _ lv) (icvb ⦃ ieq = () ⦄) invp neq




data _⊃ᵢ_ {nn} {ll} {vcl : Vec ASType ll} (vl : View nn vcl) : ∀{lr} → {vcr : Vec ASType lr} → View nn vcr → Set where
  instance
    icvvb : ∀{l n} → {vc : Vec ASType l} → {vw : View nn vc} → {{eq : n ∈ₙ nn}} → {{beq : n ∈ᵢ vl}} → {{ieq : vl ⊃ᵢ vw}} → vl ⊃ᵢ (icv n vw) 
    llvb : vl ⊃ᵢ lv 


data _⊃ₑᵢ_wt_ {nn} {ll} {vcl : Vec ASType ll} (vl : View nn vcl) : ∀{lr se} → VNO lr {se} → (vcr : Vec ASType lr) → Set where
  instance
    icvvbb : ∀{l se n lt ast} → {vc : Vec ASType l} → {vw : VNO l {se}} → {{beq : (n , ast) ∈ᵢ vl}} → {{ieq : vl ⊃ₑᵢ vw wt vc}} → vl ⊃ₑᵢ (ivno n {lt = lt} vw) wt (ast ∷ vc)
    llvbb : ∀{n ast} → {{beq : (n , ast) ∈ᵢ vl}} → vl ⊃ₑᵢ (evno n) wt (ast ∷ []) 







belToView : ∀{n nn ll} {vcl : Vec ASType ll} {vl : View nn vcl} → (n ∈ᵢ vl) → Name n {nn}
belToView (icvb {{ieq = ieq}}) = belToView ieq
belToView licvb = it

supToView : ∀{nn ll} {vcl : Vec ASType ll} {vl : View nn vcl} → ∀{lr se} → {vcr : Vec ASType lr} → {vw : VNO lr {se}} → (sup : vl ⊃ₑᵢ vw wt vcr) → View nn vcr
supToView (icvvbb {{beq = beq}} {{ieq = ieq}}) = icv (tpos r) {{beq = r}} (supToView ieq) where
  r = belToView beq
supToView (llvbb {n} {ast} {{beq}}) = belToView beq asInst icv (n , ast) lv





remfV-morph⊃ : ∀{nn ll} {vcl : Vec ASType (suc ll)} {vl : View nn vcl}
               → ∀{lr se n ast} → (beq : (n , ast) ∈ᵢ vl) → (lt : suc se ≤ n)
               → {vcr : Vec ASType lr} → {vw : VNO lr {se}} → (sup : vl ⊃ₑᵢ vw wt vcr) → (remfV vl beq) ⊃ₑᵢ vw wt vcr
remfV-morph⊃ beq lt (icvvbb {lt = llt} {{beq = lbeq}} {{ieq = ieq}}) = icvvbb {{beq = remfV-morph∈ _ beq lbeq (notsym (noteq lt))}} {{ieq = remfV-morph⊃ beq (less≤Ok r) ieq}} where
  r = transitℕ (s≤s {{m≤n = llt}}) lt
remfV-morph⊃ beq lt (llvbb {{beq = lbeq}}) = llvbb {{beq = remfV-morph∈ _ beq lbeq (notsym (noteq lt))}}


remVT : ∀{nn ll} {vcl : Vec ASType (suc ll)} (vl : View nn vcl)
               → ∀{lr se} → {vcr : Vec ASType lr} → {vw : VNO lr {se}}
               → (sup : vl ⊃ₑᵢ vw wt vcr) → Σ ℕ (λ l → Vec ASType l)
remVT vl (llvbb {{beq = beq}}) = _ , remfVT vl beq
remVT vl@(icv _ (icv _ _)) (icvvbb {lt = lt} ⦃ beq = beq ⦄ ⦃ ieq ⦄) = remVT (remfV vl beq) (remfV-morph⊃ beq lt ieq)
remVT vl@(icv _ lv) (icvvbb ⦃ beq = beq ⦄ ⦃ ieq ⦄) = _ , remfVT vl beq 

remV : ∀{nn ll} {vcl : Vec ASType (suc ll)} (vl : View nn vcl)
               → ∀{lr se} → {vcr : Vec ASType lr} → {vw : VNO lr {se}}
               → (sup : vl ⊃ₑᵢ vw wt vcr) → View nn (proj₂ (remVT vl sup))
remV vl (llvbb {{beq = beq}}) = remfV vl beq
remV vl@(icv _ (icv _ _)) (icvvbb {lt = lt} ⦃ beq = beq ⦄ ⦃ ieq ⦄) = remV (remfV vl beq) (remfV-morph⊃ beq lt ieq)
remV vl@(icv _ lv) (icvvbb ⦃ beq = beq ⦄ ⦃ ieq ⦄) = remfV vl beq 



data PrimASFun : ∀{li lo nni} → {vci : Vec ASType li} → View nni vci → {vco : Vec ASType lo} → ∀{nno} → View nno vco → Set where
  ←+ₚ : ∀{nni n1 n2} → {{eq1 : (n1 , int32) ∈ₙ nni}} → {{eq2 : (n2 , int32) ∈ₙ nni}} → (neq : ¬ ((pos eq1) ≡ (pos eq2)))
          → let k = remN nni eq1
                r = addN k int32
                g = nmorph-a {int32} (nmorph-r {nn = nni} eq1 eq2 neq) in
              PrimASFun {li = 2} {lo = 2} {nni} (icv (n1 , int32) (icv (n2 , int32) lv)) {nno = proj₁ r} (icv (tpos (proj₂ (proj₂ r))) {{beq = proj₂ (proj₂ r)}} (icv (n2 , _) {{beq = g}} lv))




mutual 


  data TFun : ℕ → Set where
      icasf : ∀{n li lo} → {vci : Vec ASType li} → {vco : Vec ASType lo} → {fnno : FNNO vci} → {fvwo : FVWO vci vco fnno} → (tf : TFun n) → ASFunFT vci vco fvwo tf → TFun (suc n)
      lf : TFun zero


  FNNO : ∀{li} → (vci : Vec ASType li) → Set
  FNNO vci = ∀{nni} → View nni vci → TNames


  FVWO : ∀{li lo} → (vci : Vec ASType li) → (vco : Vec ASType lo) → FNNO vci → Set
  FVWO vci vco fnno = ∀{nni} → (vwi : View nni vci) → View (fnno vwi) vco


  ASFunFT : ∀{n li lo} → (vci : Vec ASType li) → (vco : Vec ASType lo) → {fnno : FNNO vci} → (fvwo : FVWO vci vco fnno) → (tf : TFun n) → Set
  ASFunFT {n} {li} {lo} vci vco fvwo tf = ∀{nni} → (vwi : View nni vci) → ASFun vwi (fvwo vwi) tf



  data _∈f_ {li lo} {vci : Vec ASType li} {vco : Vec ASType lo} {fnno : FNNO vci} {fvwo : FVWO vci vco fnno} : ∀{nf} → ℕ → TFun nf → Set where
    instance
      icb : ∀{n lli llo nf} → {lvci : Vec ASType lli} → {lvco : Vec ASType llo} → {lfnno : FNNO lvci} → {lfvwo : FVWO lvci lvco lfnno} → {tf : TFun nf} → {asf : ASFunFT lvci lvco lfvwo tf} → _∈f_ {vci = vci} {vco = vco} {fnno = fnno} {fvwo = fvwo} n tf → (suc n) ∈f icasf tf asf 
      ln : ∀{nf} → {tf : TFun nf} → {asf : ASFunFT vci vco fvwo tf} → zero ∈f icasf tf asf


   
  data ASFun {li lo nni nf} {vci : Vec ASType li} (vwi : View nni vci) {vco : Vec ASType lo} {nno} (vwo : View nno vco) (tf : TFun nf) : Set where
    call : ∀{lli se llo}
           → {lvci : Vec ASType lli} → {lvco : Vec ASType llo}
           → {fnno : FNNO lvci} → {fvwo : FVWO lvci lvco fnno} 
           → {lvwi : VNO lli {se}}
           → {{seq : vwi ⊃ₑᵢ lvwi wt lvci}}
           → (fn : ℕ × ℕ) → {{feq : _∈f_ {vci = lvci} {vco = lvco} {fnno = fnno} {fvwo = fvwo} ((proj₁ fn) + (nf ∸ (proj₂ fn))) tf}} → ASFun ((proj₂ (proj₂ (restV-morph vwi))) ∪ᵢ fvwo (supToView seq)) vwo tf → ASFun vwi vwo tf
    primF : PrimASFun vwi vwo → ASFun vwi vwo tf
    endF  : ASFun vwi vwo tf


  restV-morph-abs : ∀ {l} {vc : Vec ASType l} {nni nno} n →
                  Dec (n ∈ₙ nno) →
                  View nni vc → Σ ℕ (λ l₁ → Σ (Vec ASType l₁) (View nno))
  restV-morph-abs n (yes p) vw = suc rl , proj₂ n ∷ rvc , icv n {{beq = p}} rvw where
    r = restV-morph vw
    rl = proj₁ r
    rvc = proj₁ (proj₂ r)
    rvw = proj₂ (proj₂ r)
  restV-morph-abs n (no ¬p) vw = restV-morph vw

  restV-morph : ∀{li nni nno} {vci : Vec ASType li} (vwi : View nni vci) → Σ _ (λ l → Σ (Vec ASType l) (λ vc → View nno vc))
  restV-morph {nno = nno} (icv n vwi) = restV-morph-abs n (n ∈ₙ? nno) vwi
  restV-morph lv = zero , [] , lv




addF : ∀{li lo nf} {vci : Vec ASType li} {vco : Vec ASType lo} {fnno : FNNO vci} {fvwo : FVWO vci vco fnno} (tf : TFun nf) (asf : ASFunFT vci vco fvwo tf) → TFun (suc nf)
addF tf as = icasf tf as



