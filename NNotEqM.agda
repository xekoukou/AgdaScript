module NNotEqM where


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


data NNotEq : (a b : ℕ) → Set where
  instance
    predNEq : ∀{a b} → {{ieq : NNotEq a b}} → NNotEq (suc a) (suc b)
    lt : ∀{b} → NNotEq 0 (suc b)
    gt : ∀{a} → NNotEq (suc a) 0



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
  instance
    neicvec : ∀{l nc} → {vw : Vec ℕ l} → {{neq : NNotEq n nc}} → {{ieq : NNotEqVec n vw}} → NNotEqVec n (nc ∷ vw)
    nelvec : NNotEqVec n []


data NNotEqVVec : ∀{l} → Vec ℕ l → Set where
  instance
    neicvvec : ∀{l nc} → {vw : Vec ℕ l} → {{neq : NNotEqVec nc vw}} → {{ieq : NNotEqVVec vw}} → NNotEqVVec (nc ∷ vw)
    nelvvec : NNotEqVVec []


-- Given that (a ∈ vl) is not an instance , instance will never succeed here.
data _⊃_ {A k} (vl : Vec A k) : ∀{l} → Vec A l → Set where
  instance
    ic⊃ : ∀{a l} → {vr : Vec A l} → {{ieq : vl ⊃ vr}} → (a ∈ vl) → vl ⊃ (a ∷ vr)
    ec⊃ : vl ⊃ []



ln∷⊃ : ∀{k l A} → ∀ n → {vl : Vec A k} → {vr : Vec A l} → vl ⊃ vr → (n ∷ vl) ⊃ vr
ln∷⊃ n (ic⊃ x) = ic⊃ {{ln∷⊃ n it}} (there x) 
ln∷⊃ n ec⊃ = ec⊃

n∷⊃ : ∀{k l A} → ∀ n → {vl : Vec A k} → {vr : Vec A l} → vl ⊃ vr → (n ∷ vl) ⊃ (n ∷ vr)
n∷⊃ n sup = ic⊃ {{ln∷⊃ n sup}} here


nnotEq-∈ : ∀{k} → {vl : Vec ℕ k} → ∀ n a → a ∈ vl → NNotEqVec n vl → NNotEq n a
nnotEq-∈ n a here neicvec = it
nnotEq-∈ n a (there bel) neicvec = nnotEq-∈ n a bel it

nnotEqVec-⊃ : ∀{k l} → {vl : Vec ℕ k} → {vr : Vec ℕ l} → ∀ n → vl ⊃ vr → NNotEqVec n vl → NNotEqVec n vr
nnotEqVec-⊃ n (ic⊃ {{ieq}} x) neq = nnotEq-∈ n _ x neq asInst nnotEqVec-⊃ n ieq neq asInst neicvec 
nnotEqVec-⊃ n ec⊃ neq = nelvec


