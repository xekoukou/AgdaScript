module Test where

open import Common
open import AgdaScript
open import NNotEqM
open import Nat

open import Data.Vec hiding (_>>=_)
open import Data.Product
open import Data.Nat
open import Data.Empty
open import Relation.Nullary

open import Relation.Binary.PropositionalEquality


_>>=_ : TNames → (TNames → TNames) → TNames
nni >>= f = f nni

addNN : (ast : ASType) → TNames → TNames
addNN ast nn = proj₁ (addN nn ast)

←+ : ∀{n} → {tf : TFun n} → ASFunFT (int32 ∷ int32 ∷ []) (int32 ∷ int32 ∷ []) tf
←+ {nni = nni} (icv (n1 , _) (lv (n2 , _)))
  = _ , _ ,  primF ←+ₚ




tf1 : ℕ × TFun 1
tf1 = addF lf ←+



fun-fnno : ASFunFT (int32 ∷ int32 ∷ int32 ∷ []) (int32 ∷ []) (proj₂ tf1)
fun-fnno (icv (a , _) (icv (b , _) (lv (c , _)))) = {!!} where -- {!!} , ({!!} , call (a ∷ b ∷ []) {{neq = {!!}}} (proj₁ tf1) {!!}) where
  r : NNotEqVVec (a ∷ b ∷ c ∷ [])
  r = neicvvec {{neq = {!!}}} {{ieq = neicvvec}}
