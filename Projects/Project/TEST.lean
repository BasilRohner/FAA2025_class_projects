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
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
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

end Families

namespace Polynomials

-- add MLE polynomial results

end Polynomials

namespace Constructions

structure Vec (n : ℕ) where
  elem : Fin n → ℚ
  deriving DecidableEq

@[simp]
def Char_Vec {n : ℕ} (S : Finset (Fin n)) [DecidablePred (fun i => i ∈ S)]: Vec n where
  elem := fun i ↦ if i ∈ S then (1 : ℚ ) else (0 : ℚ )

@[simp]
def vec_dot {n : ℕ} (v w : Vec n) : ℚ :=
  ∑ i : Fin n, v.elem i * w.elem i

theorem char_vec_dot_inter {n : ℕ} (U W : ⟦n⟧) : vec_dot (Char_Vec U) (Char_Vec W) = (U ∩ W).card := by
  simp [Char_Vec, vec_dot, Finset.inter_comm]


end Constructions

namespace Lemmas

open Families
open Constructions

noncomputable def poly {n : ℕ} (v : Vec n) (L : Finset ℕ) :
    MvPolynomial (Fin n) ℚ :=
  Finset.prod L (fun l =>
    let P_dot : MvPolynomial (Fin n) ℚ :=
      ∑ i : Fin n,
        MvPolynomial.C (v.elem i) * MvPolynomial.X i;
    let P_l : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.C (l : ℚ);
    P_dot - P_l
  )

noncomputable def poly2 {n : ℕ} (I : Finset (Fin n)) (k : ℚ) :
    MvPolynomial (Fin n) ℚ :=
  let sumX : MvPolynomial (Fin n) ℚ :=
    ∑ i : Fin n, MvPolynomial.X i
  let prodI : MvPolynomial (Fin n) ℚ :=
    I.prod (fun i => MvPolynomial.X i)
  (sumX - MvPolynomial.C k) * prodI

open MvPolynomial

noncomputable def MLE {n : ℕ} (p : MvPolynomial (Fin n) ℚ) : MvPolynomial (Fin n) ℚ :=
  p.sum (fun m a =>
    let newMonomial := Finset.univ.prod (fun i =>
      if m i = 0 then 1 else X i)  -- cap degree at 1
    C a * newMonomial
  )



@[simp]
theorem total_degree_bound {n p : ℕ}
    (S : Finset (MvPolynomial (Fin n) ℚ))
    (h_multi : ∀ poly ∈ S, ∀ i, degreeOf i poly ≤ 1)
    (h_total : ∀ poly ∈ S, totalDegree poly ≤ p)
    (h_li : LinearIndependent ℚ (Subtype.val : S → MvPolynomial (Fin n) ℚ)):
    S.card ≤ ∑ k ∈  Finset.range (p + 1), Nat.choose n k := by
     sorry

-- Taking the MLE does not change the evaulation (for bitstrings)
theorem MLE_equal_on_boolean_cube {n : ℕ} (p : MvPolynomial (Fin n) ℚ) :  ∀ f : (Fin n) → ℚ, (∀ i : Fin n , f i = 0 ∨ f i = 1) → eval f p = eval f (MLE p) := by
  intros f hf
  unfold MLE
  grw[p.as_sum, map_sum, Finsupp.sum]
  simp
  apply Finset.sum_congr rfl
  intro x hx
  grw[eval_monomial, coeff]
  simp
  left
  apply Finset.prod_congr rfl
  intro y hy -- starting from here just tons of cases
  by_cases hs :x y = 0
  repeat simp[hs] -- case x y = 0 (handeled with just simp), else:
  by_cases hss : f y = 0 -- if f y = 0
  grw[hss, zero_pow hs]  -- (as x y ≠ 0, 0^(x y) = 0)
  by_cases hss2 : f y = 1 -- if f y = 1
  grw[hss2, one_pow] -- 1^xy = 1
  cases hf y <;> contradiction -- cleaned up by Gemini

-- MLE of any polynomial has degree ≤ 1 in any variable
theorem MLE_have_deg_1 {n : ℕ} (p : MvPolynomial (Fin n) ℚ) : ∀ i, degreeOf i (MLE p) ≤ 1 := by
  intro j
  grw[MLE, Finsupp.sum, degreeOf_sum_le]
  simp at *
  intros a b
  grw[degreeOf_C_mul_le, degreeOf_prod_le]
  rw [Finset.sum_eq_single j]
  split_ifs
  rw [← C_1]
  grw[degreeOf_C]
  omega
  rw [degreeOf_X, if_pos rfl]
  intro k _ h_neq
  split_ifs
  apply degreeOf_C
  rw [degreeOf_X, if_neg h_neq.symm]
  intro h
  exact (h (Finset.mem_univ j)).elim

-- taking the MLE of a polynomial does not increase its total degree
theorem MLE_total_deg_non_increasing {n k : ℕ} (p : MvPolynomial (Fin n) ℚ) (h : totalDegree p ≤ k) : totalDegree (MLE p) ≤ k := by
  unfold MLE
  simp
  grw[Finsupp.sum, totalDegree_finset_sum, Finset.sup_le]
  intro b hb
  grw[totalDegree_mul, totalDegree_C, totalDegree_finset_prod]
  simp
  simp[totalDegree_one, totalDegree_X, apply_ite totalDegree]
  apply le_trans _ h
  apply le_trans _ (le_totalDegree hb)
  rw [Finsupp.sum]
  rw [← Finset.sum_subset (Finset.subset_univ b.support)] -- some Gemini Magic
  apply Finset.sum_le_sum
  intros i hi
  cases b i
  repeat simp

-- the polynomials cooresponding to sets have degree ≤ k
theorem deg_main {n  k: ℕ} (v : Vec n) (L : Finset ℕ) (h: L.card ≤ k) : totalDegree (poly v L) ≤ k := by
  unfold poly
  apply le_trans (totalDegree_finset_prod _ _)
  apply le_trans _ h
  rw[Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro x hx
  grw[totalDegree_sub, totalDegree_C, totalDegree_finset_sum]
  simp
  intro b
  grw[totalDegree_mul,  totalDegree_C, totalDegree_X]

-- the polynomials we need to add to the set have degree ≤ k
theorem deg_extra {n kk : ℕ} (hn : n ≥ 1) (I : Finset (Fin n)) (h : I.card ≤ kk -1) (hh: kk ≥ 2): totalDegree (poly2 I kk) ≤ kk := by
  unfold poly2
  grw[totalDegree_mul, totalDegree_sub, totalDegree_C, totalDegree_finset_prod]
  simp
  grw[h, totalDegree_finset_sum]
  simp
  grw[Finset.univ.sup_const]
  omega
  rw [Finset.univ_nonempty_iff]
  exact ⟨0, hn⟩


@[simp]
theorem Ray_Chaudhuri_Wilson {n : ℕ} (F : k_L_Family n) : (∀ l ∈ F.L, l < F.k) → F.card ≤ n.choose F.s := by
  intro h
  -- Create Identity Vectors
  let vecs : Finset (Vec n):= (F.elems).image (fun i => Char_Vec i)
   -- Create Extra vectors
  let extras := (Finset.powerset Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card < F.s)

  let P1 := (vecs).image (fun i => poly i F.L)
  let P2 := (extras).image (fun i => poly2 i F.k)

  have h_union : (P1 ∪ P2).card ≤ ∑ j ∈  Finset.range (F.s + 1), Nat.choose n j := by
    sorry -- main proof (via polynomials and so on)


  have h_extra : P2.card = ∑ j ∈  Finset.range (F.s), Nat.choose n j  := by
    sorry -- injective

  have h_vec : P1.card =  n.choose F.s := by
    sorry -- algebra

  have hF : Family.card n = P1.card := by
    have hF2 : Family.card n = vecs.card := by
      unfold vecs
      grw[Finset.card_image_of_injective]
      sorry -- by definition (cant extract it right now)
      sorry -- injective
    grw[hF2]
    sorry



  grw[hF]
  omega
