module Common where



infixr 0 _asInst_

_asInst_ : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → ({{y : A}} → B y) → B x
x asInst f = f {{x}}

it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x
