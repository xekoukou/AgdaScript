module NNotEqM where


open import Data.Bool
open import Data.Nat hiding (_≤_ ; _≤?_ ; ≤-pred)
open import Data.Vec hiding (_∈_)
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


data NNotEq : (a b : ℕ) → Set where
  instance
    predNEq : ∀{a b} → {{ieq : NNotEq a b}} → NNotEq (suc a) (suc b)
    lt : ∀{b} → NNotEq 0 (suc b)
    gt : ∀{a} → NNotEq (suc a) 0



slt⇒NNotEq : ∀{a b} → suc a ≤ b → NNotEq a b
slt⇒NNotEq {zero} s≤s = lt
slt⇒NNotEq {suc a} s≤s = predNEq {{ieq = slt⇒NNotEq it}}


nnotEq?-abs : ∀ {a b} →
             Dec (NNotEq a b) → Dec (NNotEq (suc a) (suc b))
nnotEq?-abs (yes p) = p asInst yes it
nnotEq?-abs (no ¬p) = no (λ { predNEq → ¬p it})

nnotEq? : (a b : ℕ) → Dec (NNotEq a b)
nnotEq? zero zero = no (λ ())
nnotEq? zero (suc b) = yes lt
nnotEq? (suc a) zero = yes gt
nnotEq? (suc a) (suc b) = nnotEq?-abs (nnotEq? a b)


nnotEq-sym : ∀{a b} → NNotEq a b → NNotEq b a
nnotEq-sym (predNEq {{ieq}}) = predNEq {{nnotEq-sym ieq}}
nnotEq-sym lt = gt
nnotEq-sym gt = lt


data NNotEqVec (n : ℕ) : ∀{l} → Vec ℕ l → Set where
  neicvec : ∀{l nc} → {vw : Vec ℕ l} → {{neq : NNotEq n nc}} → {{ieq : NNotEqVec n vw}} → NNotEqVec n (nc ∷ vw)
  nelvec : NNotEqVec n []


elimNNotEqVec : ∀{n1 n2 l} → {vc : Vec ℕ l} → NNotEqVec n1 (n2 ∷ vc) → NNotEq n1 n2
elimNNotEqVec neicvec = it



data NNotEqVVec : ∀{l} → Vec ℕ l → Set where
  instance
    neicvvec : ∀{l nc} → {vw : Vec ℕ l} → {{neq : NNotEqVec nc vw}} → {{ieq : NNotEqVVec vw}} → NNotEqVVec (nc ∷ vw)
    nelvvec : NNotEqVVec []


infix 4 _∈_


data _∈_ {a} {A : Set a} : A → {n : ℕ} → Vec A n → Set a where
  instance
    here  : ∀ {n} {x}   {xs : Vec A n} → x ∈ x ∷ xs
    there : ∀ {n} {x y} {xs : Vec A n} {{x∈xs : x ∈ xs}} → x ∈ y ∷ xs



data _⊃_ {A} : ∀ {k} → (vl : Vec A (suc k)) → ∀{l} → {{lt : l ≤ k}} → Vec A l → Set where
  instance
    ic⊃ : ∀{k} → {vl : Vec A (suc (suc k))} → ∀{a l} → {vr : Vec A l} → {{lt : l ≤ k}} → {{ieq : _⊃_ vl {{more≤Ok lt}} vr}} → {{a∈vl : a ∈ vl}} → vl ⊃ (a ∷ vr)
    ec⊃ : ∀{k} → {vl : Vec A (suc k)} → vl ⊃ []



ln∷⊃ : ∀{k l A} → ∀ n → {vl : Vec A (suc k)} → {{lt : l ≤ k}} → {vr : Vec A l} → vl ⊃ vr → _⊃_ (n ∷ vl) {{more≤Ok lt}} vr
ln∷⊃ n ic⊃ = ic⊃ {{ieq = ln∷⊃ n it}}
ln∷⊃ n ec⊃ = ec⊃

n∷⊃ : ∀{k l A} → ∀ n → {vl : Vec A (suc k)} → {{lt : l ≤ k}} → {vr : Vec A l} → vl ⊃ vr → (n ∷ vl) ⊃ (n ∷ vr)
n∷⊃ n sup = ic⊃ {{ieq = ln∷⊃ n sup}}


nnotEq-∈ : ∀{k} → {vl : Vec ℕ k} → ∀ n a → a ∈ vl → NNotEqVec n vl → NNotEq n a
nnotEq-∈ n a here neicvec = it
nnotEq-∈ n a (there {{x}}) neicvec = nnotEq-∈ n a x it

instance
  nnotEqVec-⊃ : ∀{k l} → {vl : Vec ℕ (suc k)} → {{lt : l ≤ k}} → {vr : Vec ℕ l}
                → ∀ n → {{sup : vl ⊃ vr}} → {{neq : NNotEqVec n vl}} → NNotEqVec n vr
  nnotEqVec-⊃ n {{ic⊃ {{ieq = ieq}} {{x}}}} {{neq}} = neicvec {{nnotEq-∈ n _ x neq }} {{nnotEqVec-⊃ n {{ieq}} {{neq}}}} 
  nnotEqVec-⊃ n {{ec⊃}} = nelvec


nnotEqVec-∈ : ∀{k b n} → {vl : Vec ℕ k}
              → n ∈ vl → {{neq : NNotEqVVec (b ∷ vl)}} → NNotEqVec n vr
