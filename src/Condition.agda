module Condition where

open import Prelude.Maybe
open import Prelude.Natural
open import Prelude.Path
open import Prelude.Monoidal

-- Forcing conditions are (finitary) partial functions between the natural numbers.
-- These can be thought of as partial observations of a choice sequence on the Baire
-- spread.
Condition : Set
Condition = Nat → Maybe Nat

-- The empty forcing condition
⟨⟩ : Condition
⟨⟩ _ = no

-- Extend a condition
_⌢_↝_ : Condition → Nat → Nat → Condition
(p ⌢ k ↝ i) k′ with k Nat.≟ k′
(p ⌢ k ↝ i) k′ | ⊕.inl _ = p k′
(p ⌢ k ↝ i) .k | ⊕.inr refl = so i


_∋_↝_ : Condition → Nat → Nat → Set
p ∋ k ↝ i = p k ≡ so i

_#_ : Nat → Condition → Set
k # p = p k ≡ no


snoc-nope
  : (p : Condition) (k : Nat) (k′ : Nat) {i : Nat}
  → (k ≡ k′ → 𝟘)
  → (p ⌢ k ↝ i) k′ ≡ p k′
snoc-nope p k k′ k≠k′ with k Nat.≟ k′
snoc-nope p k k′ k≠k′ | ⊕.inl x = refl
snoc-nope p k .k k≠k′ | ⊕.inr refl with k≠k′ refl
snoc-nope p k .k k≠k′ | ⊕.inr refl | ()

#-snoc : ∀ {p l k i} → k # p → (l ≡ k → 𝟘) → k # (p ⌢ l ↝ i)
#-snoc {p = p} {l = l} {k = k} {i = i} k#p k≠l rewrite snoc-nope p l k {i = i} k≠l = k#p

_≈_ : Condition → Condition → Set
p ≈ q = ∀ k → p k ≡ q k

≈-refl : ∀ {p} → p ≈ p
≈-refl i = refl

