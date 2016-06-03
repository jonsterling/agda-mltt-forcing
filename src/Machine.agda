module Machine where

open import Prelude.Natural
open import Prelude.Path
open import Prelude.List
open import Prelude.Maybe
open import Prelude.Functor
open import Prelude.Monoidal
open import Syntax
open import Condition


-- We define a stack machine for MLTT's programming language.
record Machine : Set where
  constructor _∥_
  field
    control : Expr 0
    stack : Stack 0

open Machine public

infix 4 _∥_
infix 2 ok_

-- We intend to execute MLTT programs inside the "exception monad".
data Exn (A : Set) : Set where
  ok_ : A → Exn A
  raise : Nat → Exn A

raise-inj : ∀ {A : Set} {m n} → raise {A} m ≡ raise n → m ≡ n
raise-inj refl = refl

instance
  Exn-functor : Functor Exn
  Functor.map Exn-functor f (ok x) = ok (f x)
  Functor.map Exn-functor f (raise k) = raise k

infix 1 _⊩_⋄_↦_
infix 1 _⊩_↦_
infix 1 _⊩_⇒_
infix 1 _⊩_⇓_
infix 1 _⊩_⇑_

-- The critical cut rules, relative to a forcing condition.
data _⊩_⋄_↦_ (p : Condition) : Cont 0 → Val 0 → Exn (Expr 0) → Set where
  -•
    : ∀ {E F}
    → p ⊩ -• E ⋄ ƛ F ↦ ok F /ᵉ E

  π₁-
    : ∀ {E₁ E₂}
    → p ⊩ π₁- ⋄ ⟨ E₁ , E₂ ⟩ ↦ ok E₁

  π₂-
    : ∀ {E₁ E₂}
    → p ⊩ π₁- ⋄ ⟨ E₁ , E₂ ⟩ ↦ ok E₂

  -- If our current state of knowledge (forcing condition) includes the answer
  -- to a query, then return it.
  𝔣-ok
    : ∀ {k i}
    → p ∋ k ↝ i
    → p ⊩ 𝔣- ⋄ num k ↦ ok ` num i

  -- If the query is outside the current state of knowledge (forcing condition),
  -- then we raise an "exception".
  𝔣-raise
    : ∀ {k}
    → k # p
    → p ⊩ 𝔣- ⋄ num k ↦ raise k

-- Small-step machine transitions
data _⊩_↦_ (p : Condition) : Machine → Exn Machine → Set where
  ret
    : ∀ {M}
    → p ⊩ (` M) ∥ [] ↦ ok (` M) ∥ []

  cut
    : ∀ {M K S 𝓔 𝓔′}
    → map (_∥ S) 𝓔 ≡ 𝓔′
    → p ⊩ K ⋄ M ↦ 𝓔
    → p ⊩ (` M) ∥ K ∷ S ↦ 𝓔′

  peel
    : ∀ {K E S}
    → p ⊩ K [ E ] ∥ S ↦ ok (E ∥ K ∷ S)

-- Big-step machine evaluation
data _⊩_⇒_ (p : Condition) : Machine → Exn (Val 0) → Set where
  ret
    : ∀ {𝓜 M}
    → p ⊩ 𝓜 ↦ ok ` M ∥ []
    → p ⊩ 𝓜 ⇒ ok M

  raise
    : ∀ {𝓜 k}
    → p ⊩ 𝓜 ↦ raise k
    → p ⊩ 𝓜 ⇒ raise k

  go
    : ∀ {𝓜 𝓜′ 𝓔}
    → p ⊩ 𝓜 ↦ ok 𝓜′
    → p ⊩ 𝓜′ ⇒ 𝓔
    → p ⊩ 𝓜 ⇒ 𝓔

-- Expression converges to a value
_⊩_⇓_ : Condition → Expr 0 → Val 0 → Set
p ⊩ E ⇓ M = p ⊩ E ∥ [] ⇒ ok M

-- Expression raises an exception (query to the ambient choice sequence)
_⊩_⇑_ : Condition → Expr 0 → Nat → Set
p ⊩ E ⇑ k = p ⊩ E ∥ [] ⇒ raise k

_⇓_ : Expr 0 → Val 0 → Set
E ⇓ M = ⟨⟩ ⊩ E ⇓ M

_⇑_ : Expr 0 → Nat → Set
E ⇑ k = ⟨⟩ ⊩ E ⇑ k

-- If an exception is raised, it is because a query was made which could
-- not yet be answered. We prove this below by induction on the derivation of
-- divergence.

↦-raise-lemma : ∀ {p 𝓜 k} → p ⊩ 𝓜 ↦ raise k → k # p
↦-raise-lemma (cut () -•)
↦-raise-lemma (cut () π₁-)
↦-raise-lemma (cut () π₂-)
↦-raise-lemma (cut () (𝔣-ok _))
↦-raise-lemma (cut refl (𝔣-raise h)) = h

⇒-raise-lemma : ∀ {p 𝓜 k} → p ⊩ 𝓜 ⇒ raise k → k # p
⇒-raise-lemma (raise D) = ↦-raise-lemma D
⇒-raise-lemma (go _ D) = ⇒-raise-lemma D

⇑-lemma : ∀ {p E k} → p ⊩ E ⇑ k → k # p
⇑-lemma D = ⇒-raise-lemma D

-- TODO: prove that evaluation is monotone wrt. forcing conditions
↦-mono
  : ∀ {p k i 𝓜 𝓝}
  → p ⊩ 𝓜 ↦ ok 𝓝
  → k # p
  → (p ⌢ k ↝ i) ⊩ 𝓜 ↦ ok 𝓝
↦-mono ret _ = ret
↦-mono (cut h -•) _ = cut h -•
↦-mono (cut h π₁-) _ = cut h π₁-
↦-mono (cut h π₂-) _ = cut h π₂-
↦-mono {k = k} (cut refl (𝔣-ok {k = k′} h)) k#p with k Nat.≟ k′
↦-mono {k = k} (cut refl (𝔣-ok h)) k#p | ⊕.inl k≠k′ = cut refl (𝔣-ok (≡.cmp (h , (snoc-nope _ k _ k≠k′))))
↦-mono {k = ze} (cut refl (𝔣-ok D)) k#p | ⊕.inr refl with ≡.cmp (k#p , D ≡.⁻¹)
↦-mono {k = ze} (cut refl (𝔣-ok D)) k#p | ⊕.inr refl | ()
↦-mono (cut refl (𝔣-ok D)) k#p | ⊕.inr refl with ≡.cmp (k#p , D ≡.⁻¹ )
↦-mono (cut refl (𝔣-ok D)) k#p | ⊕.inr refl | ()
↦-mono (cut () (𝔣-raise _))
↦-mono peel _ = peel

⇒-mono
  : ∀ {p k i 𝓜 M}
  → p ⊩ 𝓜 ⇒ ok M
  → k # p
  → (p ⌢ k ↝ i) ⊩ 𝓜 ⇒ ok M
⇒-mono (ret D) k#p = ret (↦-mono D k#p)
⇒-mono (go D E) k#p = go (↦-mono D k#p) (⇒-mono E k#p)

⇓-mono
  : ∀ {p k i E M}
  → p ⊩ E ⇓ M
  → k # p
  → (p ⌢ k ↝ i) ⊩ E ⇓ M
⇓-mono = ⇒-mono


↦-raise-mono
  : ∀ {p k l i 𝓜}
  → p ⊩ 𝓜 ↦ raise l
  → (k ≡ l → 𝟘)
  → (p ⌢ k ↝ i) ⊩ 𝓜 ↦ raise l
↦-raise-mono (cut () -•) k≠l
↦-raise-mono (cut () π₁-) k≠l
↦-raise-mono (cut () π₂-) k≠l
↦-raise-mono (cut () (𝔣-ok x)) k≠l
↦-raise-mono (cut refl (𝔣-raise m#p)) k≠l = cut refl (𝔣-raise (#-snoc m#p k≠l))

⇒-raise-mono
  : ∀ {p k l i 𝓜}
  → p ⊩ 𝓜 ⇒ raise l
  → k # p
  → (k ≡ l → 𝟘)
  → (p ⌢ k ↝ i) ⊩ 𝓜 ⇒ raise l
⇒-raise-mono (raise D) k#p k≠l = raise (↦-raise-mono D k≠l)
⇒-raise-mono (go D E) k#p k≠l = go (↦-mono D k#p) (⇒-raise-mono E k#p k≠l)

⇑-mono
  : ∀ {p k l i E}
  → p ⊩ E ⇑ l
  → k # p
  → (k ≡ l → 𝟘)
  → (p ⌢ k ↝ i) ⊩ E ⇑ l
⇑-mono = ⇒-raise-mono
