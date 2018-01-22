module ASType2 where


open import Relation.Nullary
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Vec hiding (_>>=_)
open import Data.Product
open import Data.Nat hiding (_≤_ ; _≤?_ ; ≤-pred)


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


--- ? ?? --- Let us hope this works.
data EqVec : ∀{l r} → Vec ASType l → Vec ASType r → Set where
  instance 
    []-cong : EqVec [] []
    ∷-cong : ∀{l r x} → {xsₗ : Vec ASType l} → {xsᵣ : Vec ASType r} →  {{is : EqVec xsₗ xsᵣ}} →  EqVec (x ∷ xsₗ) (x ∷ xsᵣ)


eqVecTo≡-abs : ∀ {l x} {xsₗ : Vec ASType l} {r}
                 {xsᵣ : Vec ASType r} →
               Σ (l ≡ r) (λ leq → subst (Vec ASType) leq xsₗ ≡ xsᵣ) →
               Σ (suc l ≡ suc r)
               (λ leq → subst (Vec ASType) leq (x ∷ xsₗ) ≡ x ∷ xsᵣ)
eqVecTo≡-abs (refl , refl) = refl , refl

eqVecTo≡ : ∀{l r} → {lvc : Vec ASType l} → {rvc : Vec ASType r} → EqVec lvc rvc → Σ (l ≡ r) (λ leq → subst (Vec ASType) leq lvc ≡ rvc)
eqVecTo≡ []-cong = refl , refl
eqVecTo≡ (∷-cong {{eqvec}}) = eqVecTo≡-abs (eqVecTo≡ eqvec)

