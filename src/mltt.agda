module mltt where

open import Prelude.Maybe
open import Prelude.Natural
open import Prelude.List
open import Prelude.Path
open import Prelude.Finite
open import Prelude.Monoidal

open import Syntax
open import Condition
open import Machine

record PER (A : Set) : Set₁ where
  field
    rel : A → A → Set
    inv : ∀ m n → rel m n → rel n m
    seq : ∀ m n o → rel m n → rel n o → rel m o

open PER

mutual
  data _⊩_per (p : Condition) : Val 0 → Set where
    unit : p ⊩ unit per
    nat : p ⊩ nat per


  -- Types are objects that *locally* compute to PERs
  data _⊩_type (p : Condition) (A : Expr 0) : Set where
    now
      : ∀ A₀
      → p ⊩ A ⇓ A₀
      → p ⊩ A₀ per
      → p ⊩ A type

    later
      : ∀ k
      → p ⊩ A ⇑ k
      → (∀ i → (p ⌢ k ↝ i) ⊩ A type)
      → p ⊩ A type

  per-mono : ∀ {p A k i} → k # p → p ⊩ A per → (p ⌢ k ↝ i) ⊩ A per
  per-mono k#p unit = unit
  per-mono k#p nat = nat

  -- Typehood is monotone
  type-mono : ∀ {p A} k i → k # p → p ⊩ A type → (p ⌢ k ↝ i) ⊩ A type
  type-mono k i k#p (now A₀ ⇓A₀ D) = now A₀ (⇓-mono ⇓A₀ k#p) (per-mono k#p D)
  type-mono k i k#p (later k′ D E) with k Nat.≟ k′
  type-mono k i k#p (later k′ D E) | ⊕.inl k≠k′ = {!!}
  type-mono k i k#p (later .k D E) | ⊕.inr refl = E i

  -- Members are objects that *locally* compute to equal values
  data _⊩_≐_∈_⟨_⟩ (p : Condition) (M N : Expr 0) (A : Expr 0) : p ⊩ A type → Set where
    now
      : ∀ {M₀ N₀ A₀ 𝓓 𝓔}
      → p ⊩ M ⇓ M₀
      → p ⊩ N ⇓ N₀
      → rel ⟦ 𝓔 ⟧ M₀ N₀
      → p ⊩ M ≐ N ∈ A ⟨ now A₀ 𝓓 𝓔 ⟩

    later₀
      : ∀ {k 𝓓}
      → (𝓔 : p ⊩ M ⇑ k)
      → (∀ i → (p ⌢ k ↝ i) ⊩ M ≐ N ∈ A ⟨ type-mono _ i (⇑-lemma 𝓔) 𝓓 ⟩)
      → p ⊩ M ≐ N ∈ A ⟨ 𝓓 ⟩

    later₁
      : ∀ {k 𝓓}
      → (𝓔 : p ⊩ N ⇑ k)
      → (∀ i → (p ⌢ k ↝ i) ⊩ M ≐ N ∈ A ⟨ type-mono _ i (⇑-lemma 𝓔) 𝓓 ⟩)
      → p ⊩ M ≐ N ∈ A ⟨ 𝓓 ⟩


  data ⟦unit⟧ : Val 0 → Val 0 → Set where
    ax : ⟦unit⟧ ax ax

  data ⟦nat⟧ : Val 0 → Val 0 → Set where
    num : ∀ {k} → ⟦nat⟧ (num k) (num k)

  ⟦_⟧ : ∀ {p A} → p ⊩ A per → PER (Val 0)
  rel ⟦ unit ⟧ = ⟦unit⟧
  inv ⟦ unit ⟧ .ax .ax ax = ax
  seq ⟦ unit ⟧ .ax .ax .ax ax ax = ax
  rel ⟦ nat ⟧ = ⟦nat⟧
  inv ⟦ nat ⟧ _ _ num = num
  seq ⟦ nat ⟧ _ _ _ num num = num
