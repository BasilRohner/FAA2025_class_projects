/-
  Explicit Construction of Ramsey Graphs

  Authors: Flurin Steck, Basil Rohner
-/

/-
  "I don't make mistakes."
-/

-- todo: naming of the namespaces it terrible

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.MvPolynomial.Basic
-- set_option diagnostics true

set_option maxHeartbeats 400000

notation "⟦"n"⟧" => Finset (Fin n)

namespace Families

class Family (n : ℕ) where
  elems : Finset ⟦n⟧
  card := elems.card

class L_Family (n : ℕ) extends Family n where
  L : Finset ℕ
  s := L.card
  L_intersecting : ∀ F1 ∈ elems, ∀ F2 ∈ elems, F1 ≠ F2 → (F1 ∩ F2).card ∈ L

class k_L_Family (n : ℕ) extends L_Family n where
  k : ℕ
  k_bounded : ∀ F ∈ elems, F.card = k

-- Constructor for k_L_Family
def mk_k_L_Family {n : ℕ}
  (elems : Finset ⟦n⟧)
  (L : Finset ℕ)
  (k : ℕ)
  (hk : ∀ F ∈ elems, F.card = k)
  (hL : ∀ F1 ∈ elems, ∀ F2 ∈ elems, F1 ≠ F2 → (F1 ∩ F2).card ∈ L) :
  k_L_Family n :=
{ elems := elems,
  L := L,
  k := k,
  L_intersecting := hL,
  k_bounded := hk }


class L_p_Family (n : ℕ) extends Family n where
  L : Finset ℕ
  s := L.card
  p : ℕ
  p_prime : p.Prime
  p_neq_one : p ≠ 1
  L_p_intersecting :
    (∀ F ∈ elems, F.card.mod p ∉ L) ∧
    (∀ F1 ∈ elems, ∀ F2 ∈ elems, F1 ≠ F2 → (F1 ∩ F2).card.mod p ∈ L)

class k_L_p_Family (n : ℕ) extends L_p_Family n where
  k : ℕ
  k_bounded : ∀ F ∈ elems, (F.card.mod p) = (k.mod p)

end Families

namespace Polynomials

-- add MLE polynomial results

end Polynomials

namespace Constructions

structure Vec (n : ℕ) where
  elem : Fin n → ℝ

-- Characteristic Vector (assumes S is a Set (Fin n) for now, as ⟦n⟧ is not standard)
-- Note: We no longer need the Semiring R parameter, as R is fixed to ℝ.
@[simp]
def Char_Vec {n : ℕ} (S : Set (Fin n)) : Vec n where
  elem := fun i ↦ if i ∈ S then (1 : ℝ) else (0 : ℝ)

-- Dot Product
-- Note: We no longer need the Semiring R parameter.
@[simp]
def vec_dot {n : ℕ} (v w : Vec n) : ℝ :=
  -- The sum now operates on the components (ℝ)
  ∑ i : Fin n, v.elem i * w.elem i

end Constructions

namespace Lemmas

open Families
open Constructions

variable {n : ℕ} [CommRing ℝ]

def poly_B (L : Finset ℕ) (S : ⟦n⟧) : MvPolynomial (Fin n) ℝ :=
  Π i : L, vec_dot


@[simp]
theorem Ray_Chaudhuri_Wilson {n : ℕ} (F : k_L_Family n) : (∀ l ∈ F.L, l < F.k) → F.card ≤ n.choose F.s := by
  intro h
  -- Create Identity Vectors
  let vecs : Finset (Vec_R n):= (F.elems).image (fun i => Char_Vec_R i)
  -- Create Polynomials

  -- Take MLE

  -- Create Extra Polynomials (naturally as MLE)

  -- Bound Degrees of polynomials (via MLE)

  -- Show independece

  -- Show total max caridanlity via Dimension argument (hopefully some Lemma in Lean)

  -- Show cardinality of Extra Polynomails

  -- this implies : F.card = cardinality of Polynomials = ≤ Max Dim  - Card Extra ≤ n.choose F.s

  sorry
