module Syntax where

open import Prelude.Natural
open import Prelude.Finite
open import Prelude.List

mutual
  data Expr (n : Nat) : Set where
    ν_ : Fin n → Expr n
    `_ : Val n → Expr n
    _[_] : Cont n → Expr n → Expr n

  data Cont (n : Nat) : Set where
    -•_ : Expr n → Cont n
    π₁- : Cont n
    π₂- : Cont n
    S- : Cont n
    𝔣- : Cont n

  data Val (n : Nat) : Set where
    num : Nat → Val n
    nat unit ax : Val n
    ⟨_,_⟩ : Expr n → Expr n → Val n
    ƛ_ : Expr (su n) → Val n

Stack : Nat → Set
Stack n = List (Cont n)

mutual
  wkᵉ
    : ∀ {n}
    → Expr n
    → Expr (su n)
  wkᵉ (ν i) = ν (su i)
  wkᵉ (` M) = ` (wkᵛ M)
  wkᵉ (K [ E ]) = wkᵏ K [ wkᵉ E ]

  wkᵛ
    : ∀ {n}
    → Val n
    → Val (su n)
  wkᵛ (num n) = num n
  wkᵛ ax = ax
  wkᵛ unit = unit
  wkᵛ nat = nat
  wkᵛ ⟨ E , F ⟩ = ⟨ wkᵉ E , wkᵉ F ⟩
  wkᵛ (ƛ E) = ƛ (wkᵉ E)

  wkᵏ
    : ∀ {n}
    → Cont n
    → Cont (su n)
  wkᵏ (-• E) = -• (wkᵉ E)
  wkᵏ π₁- = π₁-
  wkᵏ π₂- = π₂-
  wkᵏ S- = S-
  wkᵏ 𝔣- = 𝔣-

  wkˢ
    : ∀ {n}
    → Stack n
    → Stack (su n)
  wkˢ =
    List.map wkᵏ

mutual
  _/ᵉ_
    : ∀ {n}
    → Expr (su n)
    → Expr n
    → Expr n
  (ν ze) /ᵉ E = E
  (ν (su x)) /ᵉ _ = ν x
  (` M) /ᵉ E = ` (M /ᵛ E)
  (K [ F ]) /ᵉ E = (K /ᵏ E) [ F /ᵉ E ]

  _/ᵛ_
    : ∀ {n}
    → Val (su n)
    → Expr n
    → Val n
  num x /ᵛ _ = num x
  ax /ᵛ _ = ax
  unit /ᵛ _ = nat
  nat /ᵛ _ = nat
  ⟨ F , G ⟩ /ᵛ E = ⟨ F /ᵉ E , G /ᵉ E ⟩
  (ƛ m) /ᵛ E = ƛ (m /ᵉ wkᵉ E)

  _/ᵏ_
    : ∀ {n}
    → Cont (su n)
    → Expr n
    → Cont n
  (-• F) /ᵏ E = -• (F /ᵉ E)
  π₁- /ᵏ _ = π₁-
  π₂- /ᵏ _ = π₂-
  S- /ᵏ _ = S-
  𝔣- /ᵏ _ = 𝔣-

  _/ˢ_
    : ∀ {n}
    → Stack (su n)
    → Expr n
    → Stack n
  S /ˢ E =
    List.map (_/ᵏ E) S

