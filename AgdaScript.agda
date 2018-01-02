module AgdaScript where


open import Data.Bool
open import Data.Nat
open import Data.Vec
open import Data.Product
open import Relation.Nullary
open import Data.Empty
open import Relation.Binary.PropositionalEquality


it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x


  

data ASType : Set where
  str    : ASType
  int32  : ASType
  uint32 : ASType

data TNames : Set where     
  icn : TNames → ASType → Bool → TNames
  ln : TNames



data _∈ₙ_ {ast : ASType} : ℕ → TNames → Set where
  instance
    icb : ∀{n nn b last} → {{beq : _∈ₙ_ {ast = ast} n nn}} → suc n ∈ₙ (icn nn last b)
    licb  : ∀{nn} → zero ∈ₙ (icn nn ast true)


data Name (ast : ASType) {nn : TNames} : Set where
  nmc : (n : ℕ) → {{bel : _∈ₙ_ {ast = ast} n nn}} → Name ast {nn}

pos : ∀{ast nn} → Name ast {nn} → ℕ
pos (nmc n) = n

belongs : ∀{ast nn} → (nm : Name ast {nn}) → (_∈ₙ_ {ast = ast} (pos nm) nn)
belongs (nmc n) = it

remN : ∀{ast} → (nn : TNames) → Name ast {nn} → TNames
remN (icn nn x₁ x₂) (nmc zero {{licb}}) = icn nn x₁ false
remN {ast} (icn nn x₁ x₂) (nmc (suc n) {{icb}}) = icn (remN {ast} nn (nmc n)) x₁ x₂

-- We add a new name at the end so as to preserve the name conversions.
addN : TNames → ASType → TNames
addN (icn nn x x₁) ast = icn (addN nn ast) x x₁
addN ln ast = icn ln ast true


nmorph-r : ∀{astᵣ astₒ nn} → (nᵣ : Name astᵣ {nn}) → (nₒ : Name astₒ {nn}) → ¬ ((pos nᵣ) ≡ (pos nₒ)) → Name astₒ {remN nn nᵣ}
nmorph-r {astᵣ} {astₒ} {icn nn x₁ x₂} (nmc zero) (nmc zero) ¬eq = ⊥-elim (¬eq refl)
nmorph-r {.x₁} {astₒ} {icn nn x₁ .true} (nmc zero ⦃ licb ⦄) (nmc (suc n) ⦃ icb ⦄) ¬eq = nmc (suc n)
nmorph-r {astᵣ} {.x₁} {icn nn x₁ .true} (nmc (suc n) {{icb}}) (nmc zero {{licb}}) ¬eq = nmc zero
nmorph-r {astᵣ} {astₒ} {icn nn x₁ x₂} (nmc (suc n) {{icb}}) (nmc (suc n1) {{icb}}) ¬eq = nmc (suc (pos r)) {{icb {{belongs r}}}}  where
  r = nmorph-r {astᵣ} {astₒ} {nn} (nmc n) (nmc n1) (λ x → ¬eq (cong suc x))
nmorph-r {astᵣ} {astₒ} {ln} (nmc zero) (nmc zero) ¬eq = ⊥-elim (¬eq refl)
nmorph-r {astᵣ} {astₒ} {ln} (nmc zero) (nmc (suc n) {{()}}) ¬eq
nmorph-r {astᵣ} {astₒ} {ln} (nmc (suc n) {{()}}) o ¬eq



nmorph-a : ∀{astₙ ast nn} → (n : Name ast {nn}) → Name ast {addN nn astₙ}
nmorph-a {astₙ} {ast = ast} {icn nn x x₁} (nmc (suc n) ⦃ icb ⦄) = nmc (suc (pos r)) {{icb {{belongs r}}}}  where
  r = nmorph-a {nn = nn} (nmc n)
nmorph-a {ast = .x} {icn nn x .true} (nmc .0 ⦃ licb ⦄) = nmc 0




-- A single name can be used multiple times in a view. Is this a feature or a bug? Probably it does not matter.
data View (nn : TNames) : ∀{l} → Vec ASType l → Set where
  icv : ∀{l ast} → ∀ n → ∀{vc : Vec ASType l} → View nn vc → {{beq : _∈ₙ_ {ast = ast} n nn}} → View nn (ast ∷ vc)
  lv : View nn []




_∪ᵢ_ : ∀{nn ll lr} → {vcl : Vec ASType ll} → {vcr : Vec ASType lr} → View nn vcl → View nn vcr → View nn (vcl ++ vcr)
icv n vwl ∪ᵢ vwr = icv n (vwl ∪ᵢ vwr)
lv ∪ᵢ vwr = vwr


-- Instance resolution will fail if there are two arguments with the same name , aka having the name n in two names of a view.
-- Otherwise I assume that this will succeed.

data _∈ᵢ_ {nn} (n : ℕ) : ∀{l} → {vc : Vec ASType l} → View nn vc → Set where
  instance
    icvb : ∀{nc l ast} → {vc : Vec ASType l} → {vw : View nn vc} → {{beq : _∈ₙ_ {ast = ast} nc nn}} → {{ieq : n ∈ᵢ vw}} → n ∈ᵢ (icv {ast = ast} nc vw) 
    licvb : ∀{l ast} → {vc : Vec ASType l} → {vw : View nn vc} → {{beq : _∈ₙ_ {ast = ast} n nn}} → n ∈ᵢ (icv {ast = ast} n vw) 


∈¬∈⇒¬≡ : ∀ {nn nᵢ nₒ l} → {vc : Vec ASType l} → {vw : View nn vc} → {{eq : nᵢ ∈ᵢ vw}} → ¬ (nₒ ∈ᵢ vw) → ¬ (nᵢ ≡ nₒ)
∈¬∈⇒¬≡ {vw = icv n vw} {{icvb}} ¬eq = ∈¬∈⇒¬≡ λ {x → ¬eq (icvb {{ieq = x}})}
∈¬∈⇒¬≡ {vw = icv n vw} {{licvb}} ¬eq = λ { refl → ⊥-elim (¬eq licvb)}


data _⊃ᵢ_ {nn} {ll} {vcl : Vec ASType ll} (vl : View nn vcl) : ∀{lr} → {vcr : Vec ASType lr} → View nn vcr → Set where
  instance
    icvvb : ∀{l ast n} → {vc : Vec ASType l} → {vw : View nn vc} → {{eq : _∈ₙ_ {ast = ast} n nn}} → {{beq : n ∈ᵢ vl}} → vl ⊃ᵢ vw → vl ⊃ᵢ (icv {ast = ast} n vw) 
    llvb : vl ⊃ᵢ lv 



data primASFun : ∀{li lo nni nno} → {vci : Vec ASType li} → View nni vci → {vco : Vec ASType lo} → View nno vco → Set where
--   _←+ₚ_ :


mutual 

  data TFun : ℕ → Set where
      icasf : ∀{n li lo} → {vci : Vec ASType li} → {vco : Vec ASType lo} → (tf : TFun n) → (∀{nni nno} → (vwi : View nni vci) → (vwo : View nno vco) → ASFun vwi vwo tf) → TFun (suc n)
      lf : TFun zero


  data _∈f_ {li lo} {vci : Vec ASType li} {vco : Vec ASType lo} : ∀{nf} → ℕ → TFun nf → Set where
    instance
      icb : ∀{n lli llo nf} → {lvci : Vec ASType lli} → {lvco : Vec ASType llo} → {tf : TFun nf} → {asf : ∀{lnni lnno} → (lvwi : View lnni lvci) → (lvwo : View lnno lvco) → ASFun lvwi lvwo tf} → _∈f_ {vci = vci} {vco = vco} n tf → (suc n) ∈f icasf tf asf 
      ln : ∀{nf} → {tf : TFun nf} → {asf : ∀{nni nno} → (vwi : View nni vci) → (vwo : View nno vco) → ASFun vwi vwo tf} → zero ∈f icasf tf asf

   
  data ASFun {li lo nni nno nf} {vci : Vec ASType li} (vwi : View nni vci) {vco : Vec ASType lo} (vwo : View nno vco) (tf : TFun nf) : Set where
    call : ∀{lli llo lnno}
           → {lvci : Vec ASType lli} → {lvco : Vec ASType llo}
           → {lvwi : View nni lvci} → {lvwo : View lnno lvco}
           → {{seq : vwi ⊃ᵢ lvwi}}
           → (fn : ℕ × ℕ) → {{feq : _∈f_ {vci = lvci} {vco = lvco} ((proj₁ fn) + (nf ∸ (proj₂ fn))) tf}} → ASFun lvwo vwo tf → ASFun vwi vwo tf
    primF : primASFun vwi vwo → ASFun vwi vwo tf
    endF  : ASFun vwi vwo tf
  


addF : ∀{li lo nf} {vci : Vec ASType li} {vco : Vec ASType lo} (tf : TFun nf) (asf : ∀{nni nno} (vwi : View nni vci) (vwo : View nno vco) → ASFun vwi vwo tf) → TFun (suc nf)
addF tf as = icasf tf as



