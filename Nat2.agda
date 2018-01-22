module Nat2 where


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



data _≤_ : Rel ℕ Level.zero where
  instance
    z≤n : ∀ {n}                 → zero  ≤ n
    s≤s : ∀ {m n} {{m≤n : m ≤ n}} → suc m ≤ suc n
