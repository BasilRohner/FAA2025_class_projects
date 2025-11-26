/-
  Explicit Construction of Ramsey Graphs

  Authors: Flurin Steck, Basil Rohner
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic

notation "⟦"n"⟧" => Finset (Fin n)

namespace Families

class Family (n : ℕ) where
  elems : Finset ⟦n⟧
  card := elems.card

class L_Family (n s : ℕ) extends Family n where
  L : Finset ℕ
  L_size : L.card = s
  L_intersecting : ∀ F1 ∈ elems, ∀ F2 ∈ elems, F1 ≠ F2 → (F1 ∩ F2).card ∈ L

class k_L_Family (n s k : ℕ) extends L_Family n s where
  k_bounded : ∀ F ∈ elems, F.card = k

class L_p_Family (n : ℕ) extends Family n where
  L : Finset ℕ
  s := L.card
  p : ℕ
  p_prime : p.Prime
  p_neq_one : p ≠ 1
  L_p_intersecting :
    (∀ F ∈ elems, F.card.mod p ∉ L) ∧
    (∀ F1 ∈ elems, ∀ F2 ∈ elems, F1 ≠ F2 → (F1 ∩ F2).card.mod p ∈ L)

end Families

namespace Polynomials

-- add MLE polynomial results

end Polynomials

namespace Constructions

class Vec {α : Type*} (n : ℕ) where
  elem : Fin n → α

instance Char_Vec {R : Type*} [Semiring R] {n : ℕ} (S : ⟦n⟧) : @Vec R n where
  elem := fun i ↦ if i ∈ S then (1 : R) else (0 : R)

def vec_dot {R : Type*} [Semiring R] {n : ℕ} (v w : @Vec R n) : R :=
  ∑ i : Fin n, v.elem i * w.elem i

theorem char_vec_dot_inter {n : ℕ} (U W : ⟦n⟧) : vec_dot (Char_Vec U) (Char_Vec W) = (U ∩ W).card := by
  simp [Char_Vec, vec_dot, Finset.inter_comm]

end Constructions

namespace Lemmas

open Families
open Constructions

def f {n : ℕ} (F : L_p_Family n) (U V : ⟦n⟧) : ZMod F.p :=
  ∏ l ∈ F.L, (vec_dot (@Char_Vec (ZMod F.p) (by exact CommRing.toCommSemiring.toSemiring) n V) (@Char_Vec (ZMod F.p) (by exact CommRing.toCommSemiring.toSemiring) n U) - (l : ZMod F.p))

theorem Frankl_Wilson {n : ℕ} (F : L_p_Family n) : F.card ≤ ∑ i ∈ Finset.range (F.L.card + 1), n.choose i := by
  have : ∀ U ∈ F.elems, ∀ V ∈ F.elems, U ≠ V → f F U V = 0 := by
    intro U Uh V Vh UV
    simp [f, Char_Vec, vec_dot]
    have := F.L_p_intersecting.2 U Uh V Vh UV
    -- show that ZMod F.p is non-trivial
    have : Nontrivial (ZMod F.p) := by
      apply ZMod.nontrivial_iff.2
      exact F.p_neq_one
    -- show that ZMod F.p has no zero-divisors
    have : NoZeroDivisors (ZMod (L_p_Family.p n)) := by
      sorry
      /-
        ℤ/pℤ has no zero-divisors for p ∈ ℙ.
        Assume towrads a contradiction a,b ∈ ℤ/pℤ ∖ {0} and a · b = 0
        Then a · b = p and 1 ≤ a,b < p. This clearly doesn't work with primality of p. ∎
        Unsure how to bring this to lean tho...
      -/
    apply Finset.prod_eq_zero_iff.2
    use (U ∩ V).card.mod (F.p)
    constructor
    · assumption
    · sorry -- this is trivial but need to equate the coercion in ℤ/pℤ to modular reduction with p
  -- show that f is equivalent to a MLE on the hypercube
  -- bound the number of orthogonal possible MLE in n variables by the sum
  sorry
  -- might not be that much more effort for this simple lemma even

end Lemmas
