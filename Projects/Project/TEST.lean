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
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Disjoint
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finrank
-- import Mathlib.LinearAlgebra.FiniteDimension.Basic
-- set_option diagnostics true

set_option maxHeartbeats 400000000

notation "⟦"n"⟧" => Finset (Fin n)

namespace Families

class Family (n : ℕ) where
  elems : Finset ⟦n⟧
  card := elems.card
  card_eq : card = elems.card := by rfl

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

open MvPolynomial

/-
 ∏ l ∈ L, (∑ i : Fin n, v[i] * x[i]) - l
-/
noncomputable def poly {n : ℕ} (v : Vec n) (L : Finset ℕ) :
    MvPolynomial (Fin n) ℚ :=
  ∏ l ∈ L, ((∑ i : Fin n, C (v.elem i) * X i) - C (l : ℚ))


/-
  (∑ i : Fin n, x[i] - k) * ∏ i ∈ I, x[i]
-/
noncomputable def poly2 {n : ℕ} (I : Finset (Fin n)) (k : ℚ) :
    MvPolynomial (Fin n) ℚ :=
  ((∑ i : Fin n, X i) - C k) * ∏ i ∈ I, X i


noncomputable def MLE {n : ℕ} (p : MvPolynomial (Fin n) ℚ) : MvPolynomial (Fin n) ℚ :=
  p.sum (fun m a ↦ C a * Finset.univ.prod (fun i ↦ if m i = 0 then 1 else X i))


/-
  THIS IS BY FAR THE MOST ANNOYING THING I DID THIS SEMESTER
-/
theorem total_degree_bound {n p : ℕ}
    (S : Finset (MvPolynomial (Fin n) ℚ))
    (h_multi : ∀ poly ∈ S, ∀ i, degreeOf i poly ≤ 1)
    (h_total : ∀ poly ∈ S, totalDegree poly ≤ p)
    (h_li : LinearIndependent ℚ (Subtype.val : S → MvPolynomial (Fin n) ℚ)):
    S.card ≤ ∑ k ∈ Finset.range (p + 1), Nat.choose n k := by

  -- Construct set of valid supports (subsets of variables with size ≤ p)
  let U : Finset (Finset (Fin n)) := (Finset.range (p + 1)).biUnion (fun k ↦ Finset.powersetCard k Finset.univ)

  -- Define mapping from a support set to a monomial
  let to_monomial (s : Finset (Fin n)) : MvPolynomial (Fin n) ℚ :=
    monomial (∑ i ∈ s, Finsupp.single i 1) 1

  -- Define the sapnning set of monomials M
  let M : Finset (MvPolynomial (Fin n) ℚ) := U.image to_monomial

-- |M| = ∑ k ∈ Finset.range (p + 1), n.choose k
  have h_card_M : M.card = ∑ k ∈ Finset.range (p + 1), n.choose k := by
    -- M = to_monomial(U)
    rw [Finset.card_image_of_injective]
    · -- Cardinality of U the same
      rw [Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro k _
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      · -- Show the union is disjoint, have different size so...
        intros i hi j hj hij
        rw [Function.onFun, Finset.disjoint_left]
        intros x hx hy
        rw [Finset.mem_powersetCard] at hx hy
        obtain ⟨h1, h2⟩ := hx
        obtain ⟨h3, h4⟩ := hy
        rw [h2] at h4
        contradiction
    · -- Prove injectivity of to_monomial
      intro s t hs
      unfold to_monomial at hs
      simp_all
      ext x
      have h := Finsupp.ext_iff.mp hs x
      simp [Finsupp.single_apply] at h
      split_ifs at h with h1 h2
      · grind
      · grind

  have h_span : Set.range (Subtype.val : S → MvPolynomial (Fin n) ℚ) ⊆
    Submodule.span ℚ (M : Set (MvPolynomial (Fin n) ℚ)) := by

    rw [Set.range_subset_iff]
    intro ⟨poly, h_poly_in_S⟩
    simp
    rw [as_sum poly]
    apply Submodule.sum_mem
    intros d hd_in_support
    -- Factor coef: monomial d c = c · monomial d 1
    rw [←mul_one (coeff d poly), ←smul_eq_mul, ←smul_monomial]
    apply Submodule.smul_mem
    -- Show base (monomial d 1) is in span {M}
    apply Submodule.subset_span
    rw [Finset.mem_coe, Finset.mem_image]
    -- use d.support as witness
    use d.support
    constructor
    · rw [Finset.mem_biUnion]
      use d.support.card
      constructor
      · rw [Finset.mem_range]
        have h_sum_eq_card : d.sum (fun _ k ↦ k) = d.support.card := by
          rw [Finsupp.sum]
          trans ∑ i ∈ d.support, 1
          · apply Finset.sum_congr rfl
            intro x hx
            have t1 := h_multi poly h_poly_in_S x
            have t2 := Finsupp.mem_support_iff.mp hx
            rw [degreeOf_le_iff] at t1
            have dx_le_one := t1 d hd_in_support
            grind
          · simp

        rw [← h_sum_eq_card]
        apply Nat.lt_succ_of_le
        have t1 := le_totalDegree hd_in_support
        have t2 := h_total poly h_poly_in_S
        exact le_trans t1 t2
      · rw [Finset.mem_powersetCard]
        constructor
        · simp
        · rfl
    · unfold to_monomial
      congr 1
      ext x
      simp
      have h_decomp : d = ∑ i ∈ d.support, Finsupp.single i 1 := by
        ext y
        simp [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
        split_ifs
        · assumption
        · simp_all
          -- Convert the coefficient condition to "d is in the support"
          have h_mem : d ∈ poly.support := Finsupp.mem_support_iff.mpr hd_in_support

          --Use the hypothesis that polynomials in S are multilinear (degree ≤ 1 per var)
          have h_deg : degreeOf y poly ≤ 1 := h_multi poly h_poly_in_S y

           -- Global degree bound implies local exponent d y is ≤ 1
          rw [degreeOf_le_iff] at h_deg
          have h_le : d y ≤ 1 := h_deg d h_mem
          grind
      rw [←h_decomp]

  -- Linear Independence Bound: |S| ≤ |M|
  have h_li_on : LinearIndepOn ℚ (id : MvPolynomial (Fin n) ℚ → MvPolynomial (Fin n) ℚ) S := by
    exact h_li
  rw [←h_card_M, ←Fintype.card_coe]
  rw [←finrank_span_eq_card h_li]
  apply le_trans (b := Module.finrank ℚ (Submodule.span ℚ (M : Set (MvPolynomial (Fin n) ℚ))))
  · sorry
  · sorry
  /-
  let VM := Submodule.span ℚ (M : Set (MvPolynomial (Fin n) ℚ))
  apply le_trans (b := Module.finrank ℚ VM)
  · sorry
  · exact finrank_span_le_card M
  -/

-- Taking the MLE does not change the evaulation (for bitstrings)
theorem MLE_equal_on_boolean_cube
  {n : ℕ}
  (p : MvPolynomial (Fin n) ℚ) :
    ∀ f : (Fin n) → ℚ, (∀ i : Fin n , f i = 0 ∨ f i = 1) → eval f p = eval f (MLE p) := by
  intro f hf
  unfold MLE
  grw[p.as_sum, map_sum, Finsupp.sum]
  simp
  apply Finset.sum_congr rfl
  intro x hx
  grw [eval_monomial, coeff]
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

-- the polynomials cooresponding to sets have degree ≤ size of set
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
theorem Ray_Chaudhuri_Wilson
  {n : ℕ}
  (F : k_L_Family n) :
    (∀ l ∈ F.L, l < F.k) → F.card ≤ n.choose F.s := by
  intro h
  -- Create Identity Vectors
  let vecs : Finset (Vec n):= (F.elems).image (fun i => Char_Vec i)
  -- Need this later to show that MLE of polynomials are different
  have h_vec : ∀ v ∈ vecs, ∀ i : Fin n, v.elem i = 0 ∨ v.elem i = 1 := by
  { intros v hv i
    unfold vecs at hv -- (aesop proof so could definetly be cleaner/shorter ....)
    simp_all only [Char_Vec, Finset.mem_image]
    obtain ⟨w, h_1⟩ := hv
    obtain ⟨left, right⟩ := h_1
    subst right
    simp_all only [ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one, Decidable.not_not]
    by_cases h : i ∈ w
    right
    assumption
    left
    assumption }

  let extras := (Finset.powerset Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card < F.k)

  let P1 := (vecs).image (fun i => MLE (poly i F.L))
  let P2 := (extras).image (fun i => MLE (poly2 i F.k))

  have h_union : P1.card + P2.card ≤ ∑ j ∈  Finset.range (F.s + 1), Nat.choose n j := by
     -- Main proof todo, but actually some of what we show below can be more or less copypasted
    -- To show Linear Independece and stuff like that
    sorry

  have h_extra : P2.card = ∑ j ∈  Finset.range (F.s), Nat.choose n j  := by
    have h_card : P2.card = extras.card := by -- this is due to an injective functions existing from extra into P2
      unfold P2
      grw[Finset.card_image_of_injOn]
      intros a1 ha1 a2 ha2 hh
      by_contra hx
      rw [Finset.ext_iff] at hx
      push_neg at hx
      obtain ⟨x, hx⟩ := hx
      cases hx -- there should be some wlog. here imo but probably a pita in lean
      expose_names
      let σ : Fin n →₀ ℚ  := ∑ i ∈  a1, Finsupp.single i 1
      replace ha := congr_arg (eval σ) hh
      rw [← MLE_equal_on_boolean_cube _ _,← MLE_equal_on_boolean_cube _ _, poly2, poly2, eval_mul] at ha
      dsimp[σ] at ha
      simp at ha
      cases ha
      expose_names
      sorry -- should  just be applying definitions correctly (one is one , one is zero)
      expose_names
      rw [Finset.sum_comm] at h_2
      simp only [Finsupp.single_apply] at h_2
      -- This  monstrosity below was generated by aesop :
      simp_all only [Finset.powerset_univ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Finset.sum_ite_eq,
        ↓reduceIte, Finset.sum_const, nsmul_eq_mul, mul_one, extras]
      clear *-  ha1 h_2  --- clean up this giant mess
      qify at ha1 -- bring equality into ℚ to be able to finish proof using some basic algebra
      linarith
      repeat{
      intro i
      dsimp[σ]
      rw [Finsupp.coe_finset_sum, Finset.sum_apply]
      simp_rw [Finsupp.single_apply]
      simp
      by_cases h : i ∈ a1
      right
      assumption
      left
      assumption
      }
      expose_names
      let σ : Fin n →₀ ℚ  := ∑ i ∈  a2, Finsupp.single i 1
      replace ha := congr_arg (eval σ) hh
      rw [← MLE_equal_on_boolean_cube _ _,← MLE_equal_on_boolean_cube _ _, poly2, poly2, eval_mul] at ha
      dsimp[σ] at ha
      simp at ha
      cases ha
      expose_names
      sorry --  should just be applying definitions correctly  (one is one one is zero)
      expose_names
      rw [Finset.sum_comm] at h_2
      simp only [Finsupp.single_apply] at h_2
      -- This  monstrosity below was generated by aesop :
      simp_all only [Finset.powerset_univ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Finset.sum_ite_eq,
        ↓reduceIte, Finset.sum_const, nsmul_eq_mul, mul_one, extras]
      clear *-  ha2 h_2  --- clean up this giant mess
      qify at ha2 -- bring equality into ℚ to be able to finish proof using some basic algebra
      linarith
      repeat{ -- some leftover shit
      dsimp[σ] at hh
      simp at ha
      intro i
      dsimp[σ]
      rw [Finsupp.coe_finset_sum, Finset.sum_apply]
      simp_rw [Finsupp.single_apply]
      simp
      by_cases h : i ∈ a2
      right
      assumption
      left
      assumption
      }
    grw[h_card]
    unfold extras
    grw[Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_powerset]
    -- Some things about cardianlity of powersets should be very doable
    --but annoying
    sorry

  have h_vec : P1.card ≤ n.choose F.s := by
    grw[h_extra, Finset.sum_range_succ, Nat.add_comm, Nat.add_le_add_iff_left] at h_union
    assumption


  have hF : Family.card n = P1.card := by
    rw[Family.card_eq]
    unfold P1
    unfold vecs
    grw[Finset.card_image_of_injOn]
    grw[Finset.card_image_of_injOn]
    · intros a1 ha1 a2 ha2 ha -- char_vec function is injective
      unfold Char_Vec at ha
      injection ha with h_func
      ext x
      replace h_func := congr_fun h_func x
      constructor
      intro ha1
      simp[ha1] at h_func
      exact h_func
      intro ha2
      simp[ha2] at h_func
      exact h_func
    intros a1 ha1 a2 ha2 ha
    -- Similar proof to above in concept might be more annoying when actually doing it
    sorry

  grw[hF]
  omega
