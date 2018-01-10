module Test where

open import AgdaScript
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

tf1 : ℕ × TFun 1
tf1 = addF {vci = int32 ∷ int32 ∷ []} {vco = int32 ∷ int32 ∷ []} lf λ { (icv (n1 , _) (icv (n2 , _) lv)) → {!!} , ({!!} , {!primF (n1 ←+ₚ n2)!})}

fun-fnno : ∀{nni nf} → (vw : View nni (int32 ∷ int32 ∷ int32 ∷ [])) → {tf : TFun nf} → Σ TNames (λ nno → Σ (View nno (int32 ∷ [])) (λ vwo → ASFun vw vwo tf))
fun-fnno (icv (a , _) (icv (b , _) (icv (c , _) vw))) = {!!} , ({!!} , (call (a ∷ b ∷ []) {!!} {!!}))
