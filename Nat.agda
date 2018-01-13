module Nat where


open import Common

open import Data.Bool
open import Data.Vec
open import Data.Product
open import Relation.Nullary
open import Data.Empty
open import Data.Nat hiding (_≤_ ; _≤?_ ; ≤-pred)
import Level using (zero)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality



+rsuc≡ : ∀ a b → a + suc b ≡ suc a + b
+rsuc≡ zero b = refl
+rsuc≡ (suc a) b = cong suc (+rsuc≡ a b)



data _≤_ : Rel ℕ Level.zero where
  instance
    z≤n : ∀ {n}                 → zero  ≤ n
    s≤s : ∀ {m n} {{m≤n : m ≤ n}} → suc m ≤ suc n


≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred s≤s = it

instance
  ≤-sym : ∀ {m} → m ≤ m
  ≤-sym {zero} = z≤n
  ≤-sym {suc m} = s≤s {{≤-sym}}

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


