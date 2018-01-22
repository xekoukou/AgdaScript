module NotEqM2 where

open import Common

open import Data.Bool
open import Data.Nat
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


data NotEq : (a b : ℕ) → Set where
  instance
    predEq : ∀{a b} → {{ieq : NotEq a b}} → NotEq (suc a) (suc b)
    lt : ∀{b} → NotEq 0 (suc b)
    gt : ∀{a} → NotEq (suc a) 0


notEq-sym : ∀{a b} → NotEq a b → NotEq b a
notEq-sym (predEq {{ieq}}) = predEq {{notEq-sym ieq}}
notEq-sym lt = gt
notEq-sym gt = lt

data NotEqNVec (n : ℕ) : ∀{l} → Vec ℕ l → Set where
  instance
    nvi : ∀{l nc} → {vw : Vec ℕ l} → {{neq : NotEq n nc}} → {{ieq : NotEqNVec n vw}} → NotEqNVec n (nc ∷ vw)
    nvl : NotEqNVec n []



data NotEqVVec : ∀{l} → Vec ℕ l → Set where
  instance
    vvi : ∀{l nc} → {vw : Vec ℕ l} → {{neq : NotEqNVec nc vw}} → {{ieq : NotEqVVec vw}} → NotEqVVec (nc ∷ vw)
    vvl : NotEqVVec []



data _⊃_ {A k} (vl : Vec A k) : ∀{l} → Vec A l → Set where
  ⊃i : ∀{a l} → (a∈vl : a ∈ vl) → {vr : Vec A l} → (is : vl ⊃ vr) → vl ⊃ (a ∷ vr)
  ⊃l : vl ⊃ []


ln∷⊃ : ∀{k l A} → ∀ n → {vl : Vec A (suc k)} → {vr : Vec A l} → vl ⊃ vr → _⊃_ (n ∷ vl) vr
ln∷⊃ n (⊃i a∈vl sup) = ⊃i (there a∈vl) (ln∷⊃ n sup)
ln∷⊃ n ⊃l = ⊃l

n∷⊃ : ∀{k l A} → ∀ n → {vl : Vec A (suc k)} → {vr : Vec A l} → vl ⊃ vr → (n ∷ vl) ⊃ (n ∷ vr)
n∷⊃ n sup = ⊃i here (ln∷⊃ n sup)


notEq-∈ : ∀{k} → {vl : Vec ℕ k} → ∀ n a → a ∈ vl → NotEqNVec n vl → NotEq n a
notEq-∈ n a here nvi = it
notEq-∈ n a (there bel) (nvi {{neq}} {{ieq}}) = notEq-∈ n a bel ieq



notEqNVec-⊃ : ∀{k l} → {vl : Vec ℕ (suc k)} → {vr : Vec ℕ l}
             → ∀ n → (sup : vl ⊃ vr) → (neq : NotEqNVec n vl) → NotEqNVec n vr
notEqNVec-⊃ n (⊃i a∈vl sup) neq = nvi {{notEq-∈ n _ a∈vl neq}} {{notEqNVec-⊃ n sup neq}}
notEqNVec-⊃ n ⊃l neq = nvl


