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
  L_card_eq : s = L.card := by rfl
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
  · sorr y
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
theorem deg_extra {n s kk : ℕ} (hn : n ≥ 1) (I : Finset (Fin n)) (h : I.card ≤ s -1) (hh: s ≥ 1): totalDegree (poly2 I kk) ≤ s := by
  unfold poly2
  grw[totalDegree_mul, totalDegree_sub, totalDegree_C, totalDegree_finset_prod]
  simp
  grw[h, totalDegree_finset_sum]
  simp
  grw[Finset.univ.sup_const]
  omega
  rw [Finset.univ_nonempty_iff]
  exact ⟨0, hn⟩

variable {n : ℕ} {ι : Type*} [LinearOrder ι]

theorem linearIndependent_of_triangle_eval
  (p : ι → MvPolynomial (Fin n) ℚ)
  (x : ι → (Fin n → ℚ))
  (h_tri : ∀ i j, i < j → eval (x j) (p i) = 0)
  (h_diag : ∀ i, eval (x i) (p i) ≠ 0) :
  LinearIndependent ℚ p := by
  rw [linearIndependent_iff']
  intros s g ha a hs
  let support_nz := s.filter (fun j => g j ≠ 0)
  by_contra hx
  push_neg at hx -- asume not all coefficents are zero
  have hx :  a ∈ support_nz := by grind
  have hx : support_nz.Nonempty := by grind
  let k := support_nz.max' hx
  let xx := x k -- take as an input the corresponding value for the highest non zero coefficent
  have h := congr_arg (eval xx) ha
  simp at h
  rw[<-Finset.sum_filter_add_sum_filter_not s (· < k)] at h -- split sum into smaller and ≥ k part
  have h_1 : ∑ x ∈ s with x < k, g x * (eval xx) (p x) = 0 := by --first part is zero by triangle condition
    rw[Finset.sum_eq_zero]
    intros x hx
    refine Rat.mul_eq_zero.mpr ?_
    right
    apply h_tri
    simp_all only [ne_eq, Finset.mem_filter, not_false_eq_true, and_self, not_lt, Finset.max'_le_iff, and_imp,
      support_nz, k, xx] -- aesop probably overkill
  rw[h_1] at h
  simp at h
  rw[<-Finset.sum_filter_add_sum_filter_not (s.filter (k ≤ ·)) (· = k)] at h

  have h_2 :  ∑ x ∈ {x ∈ s | k ≤ x} with ¬x = k, g x * (eval xx) (p x) = 0 := by  -- > k part is = 0 because of k choosen as max
    rw[Finset.sum_eq_zero]
    intros x hx
    simp at hx
    have hx : x > k := by grind
    refine Rat.mul_eq_zero.mpr ?_
    left
    have h_x : x ∉ support_nz := by
      rename_i hx_4
      simp_all only [ne_eq, Finset.mem_filter, not_false_eq_true, and_self, Finset.max'_le_iff, and_imp, gt_iff_lt,
        Finset.max'_lt_iff, true_and, Decidable.not_not, support_nz, k, xx]
      obtain ⟨left, right⟩ := hx_4
      obtain ⟨left, right_1⟩ := left
      by_contra hh
      apply hx at hh
      simp_all only [lt_self_iff_false]
      assumption
    grind

  rw[h_2] at h
  simp at h
  have h_set : (s.filter (k ≤ ·)).filter (· = k) = {k} := by
    sorry
  rw[h_set] at h
  simp at h
  cases h
  all_goals expose_names
  sorry
  specialize h_diag k
  simp at h_diag
  contradiction


@[simp]
theorem Ray_Chaudhuri_Wilson
  {n : ℕ}
  (F : k_L_Family n) :
    (∀ l ∈ F.L, l < F.k) → F.card ≤ n.choose F.s := by
  intro h

  -- Need this later
  have h_sk : F.s ≤ F.k := by
    grw[F.L_card_eq]
    have hL : F.L ⊆ Finset.range (F.k) := by
      rw[Finset.subset_iff]
      intros x hx
      apply h at hx
      simp
      assumption
    grw[hL]
    simp_all only [Finset.card_range, le_refl]

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

  let extras := (Finset.powerset Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card < F.s)

  let P1 := (vecs).image (fun i => MLE (poly i F.L))
  let P2 := (extras).image (fun i => MLE (poly2 i F.k))

  --- Needed for Linear Independece (1) / can also use for other shit
  have h_P1 : ∀ v ∈ vecs,  ∃ z : ((Fin n) → ℚ) , ∀ w ∈ vecs, ∀ i ∈ extras,
    let x := MLE (poly v F.L);
    let e := MLE (poly2 i F.k);
    (eval z x) ≠ 0 ∧ (eval z e) = 0 ∧
    let y := MLE (poly w F.L);
    x ≠ y → (eval z y) = 0 := by
    intros v a
    use (fun i ↦ v.elem i)
    intros w hw i hi x e
    constructor
    · simp_all only [Char_Vec, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one, Decidable.not_not, Finset.powerset_univ,
      Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, vecs, extras, x] -- let aesop clean up some expressions
      obtain ⟨w_1, h_1⟩ := a
      obtain ⟨w_2, h_2⟩ := hw
      obtain ⟨left, right⟩ := h_1
      obtain ⟨left_1, right_1⟩ := h_2
      subst right right_1
      simp_all only  --aesop end
      unfold poly
      grw[<-MLE_equal_on_boolean_cube, eval_prod]
      simp
      grw[Finset.prod_eq_zero_iff] -- only 0 if one term is 0 => |w_1| ∈ L contradiction
      simp
      intro l hl hh
      have hk : l = F.k := by
        grw[<-F.k_bounded w_1]
        qify
        linarith
        assumption
      apply h at hl
      omega
      grind
    · constructor
      · unfold e
        grw[<-MLE_equal_on_boolean_cube]
        unfold poly2
        grw[eval_mul]
        simp
        left
        -- AESOP blow up
        simp_all only [Char_Vec, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
          ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one, Decidable.not_not,
          Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and, vecs, extras]
        obtain ⟨w_1, h_1⟩ := a
        obtain ⟨w_2, h_2⟩ := hw
        obtain ⟨left, right⟩ := h_1
        obtain ⟨left_1, right_1⟩ := h_2
        subst right right_1
        simp_all only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
        norm_cast
        grw[<-F.k_bounded w_1, Int.subNat_eq_zero_iff]
        assumption
        grind
      · intros y hx
        unfold y
        grw[<-MLE_equal_on_boolean_cube]
        unfold poly
        simp
        simp_all only [Char_Vec, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
          ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one, Decidable.not_not,
          Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, vecs, extras, x, y]
        obtain ⟨w_1, h_1⟩ := a
        obtain ⟨w_2, h_2⟩ := hw
        obtain ⟨left, right⟩ := h_1
        obtain ⟨left_1, right_1⟩ := h_2
        subst right right_1
        simp_all only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          nsmul_eq_mul]
        grw[Finset.prod_eq_zero_iff] -- one term is 0, as w_1 ≠ w_2 and hence w_1 ∩ w_2 ∈ L
        use  ((w_1 ∩ w_2).card)
        constructor
        · apply F.L_intersecting
          assumption
          assumption
          by_contra hw  -- abstractly just show w1 ≠ w2 assuming f w1 ≠ f w2 (done by aesop)
          subst hw
          simp_all only [not_true_eq_false]
        · linarith
        grind

  --- Needed for Linear Independece (2) / can also use for other shit
  have h_P2 : ∀ i ∈ extras, ∃ z : ((Fin n) → ℚ), ∀ j ∈ extras,
    let x := MLE (poly2 i F.k);
    (eval z x) ≠  0 ∧
    let y := MLE (poly2 j F.k);
     x ≠ y ∧ i.card ≤ j.card →  (eval z y) = 0 := by
      intros i hi
      use (fun a ↦ if a ∈ i then 1 else 0)
      intro j hj x
      constructor
      · unfold x poly2
        grw[<-MLE_equal_on_boolean_cube]
        simp
        constructor
        norm_cast  -- i.card < s ≤ k
        grw[Int.subNat_eq_zero_iff]
        have hI : i.card < F.k := by
          grw[<-h_sk]
          unfold extras at hi
          grind
        omega
        grw[Finset.prod_eq_zero_iff] -- if every term is 1, Π cant be 0
        simp
        grind
      · intro y hh
        unfold y poly2
        grw[<-MLE_equal_on_boolean_cube]
        simp
        right
        grw[Finset.prod_eq_zero_iff] -- as |i| ≤ |j| and i ≠ j one term of the product should be 0
        have hJ : ∃ ele ∈ j, ele ∉ i := by
          by_contra he
          simp at he
          grw[<-Finset.subset_iff] at he
          apply Finset.eq_iff_card_le_of_subset at he -- does exactly what we need
          obtain ⟨hh1, hh2⟩ := hh
          obtain ⟨he1, he2⟩ := he
          apply he1 at hh2
          subst hh2
          contradiction
        obtain ⟨e, he1, he2 ⟩ := hJ
        use e
        constructor
        · assumption
        · simp
          assumption
        grind

  -- Essentially just instantiate the lemmas
  have h_MLE : ∀ poly ∈ P1 ∪ P2, ∀ (i : Fin n), degreeOf i poly ≤ 1 := by
  {
    intros pq hpq
    clear *- pq hpq -- make it readable
    grw[Finset.mem_union] at hpq
    cases hpq
    · all_goals expose_names
      unfold P1 at h
      intro i --aesop clean up start
      simp_all only [Char_Vec, Finset.mem_image, exists_exists_and_eq_and, vecs]
      obtain ⟨w, h⟩ := h
      obtain ⟨left, right⟩ := h
      subst right  --aesop clean up end
      apply MLE_have_deg_1
    · all_goals expose_names
      unfold P2 at h
      intro i --aesop clean up start
      simp_all only [Finset.powerset_univ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, extras]
      obtain ⟨w, h⟩ := h
      obtain ⟨left, right⟩ := h
      subst right --aesop clean up end
      apply MLE_have_deg_1
  }
  have h_max_deg : ∀ poly ∈ P1 ∪ P2, poly.totalDegree ≤ L_Family.s n := by
    have hL : (L_Family.L n).card = L_Family.s n := by
      grw[F.L_card_eq]
    grw[<-hL]
    intros pq hpq
    grw[Finset.mem_union] at hpq
    cases hpq
    · all_goals expose_names
      unfold P1 at h_1
      simp_all only [Char_Vec, Finset.mem_image, exists_exists_and_eq_and, vecs]
      obtain ⟨w, h_1⟩ := h_1
      obtain ⟨left, right⟩ := h_1
      subst right
      apply MLE_total_deg_non_increasing
      apply deg_main
      omega

    · all_goals expose_names
      unfold P2 at h_1
      simp_all only [Finset.powerset_univ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, extras]
      obtain ⟨w, h_1⟩ := h_1
      obtain ⟨left, right⟩ := h_1
      subst right
      apply MLE_total_deg_non_increasing
      apply deg_extra
      sorry --------------> NEED n ≥ 1 here
      omega
      omega

  have h_union : (P1 ∪ P2).card ≤ ∑ j ∈  Finset.range (F.s + 1), Nat.choose n j := by
    apply total_degree_bound
    assumption
    assumption
    sorry

  -- We show the sets are distinct
  have h_distinct : P1 ∩ P2 = ∅  := by
    by_contra hh
    change P1 ∩ P2 ≠ ∅ at hh
    rw [← Finset.nonempty_iff_ne_empty, Finset.Nonempty] at hh
    obtain ⟨x, hx⟩ := hh
    grw[Finset.mem_inter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    -- Again some Aesop "blow up"
    simp_all only [Char_Vec, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one, Decidable.not_not, Finset.powerset_univ,
      Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Finset.mem_union, exists_exists_and_eq_and, vecs, extras,
      P1, P2]
    obtain ⟨w, h_1⟩ := hx1
    obtain ⟨w_1, h_2⟩ := hx2
    obtain ⟨left, right⟩ := h_1
    obtain ⟨left_1, right_1⟩ := h_2
    subst right
    --  Aesop "blow up" end
    obtain ⟨z, hh ⟩ := h_P1 w left
    grind -- essentially just applying this giant lemma

  -- hence  the total size is equal to the sum
  have h_card : P1.card + P2.card = (P1 ∪ P2).card := by
    grw[Finset.card_union,h_distinct, Finset.card_empty, Nat.sub_zero]

  -- We can easily bound the extra polynomials we added
  have h_extra : P2.card = ∑ j ∈  Finset.range (F.s), Nat.choose n j  := by
    have h_card : P2.card = extras.card := by -- extra ≃ P2
      sorry
    grw[h_card]
    unfold extras
    sorry


  -- This implies what we want about P1 (using some algebra)
  have h_vec : P1.card ≤ n.choose F.s := by
    grw[<-h_card, h_extra, Finset.sum_range_succ, Nat.add_comm, Nat.add_le_add_iff_left] at h_union
    assumption

  -- Now we just need to show that 𝔽 ≃ P1
  have hF : Family.card n = P1.card := by
    have hv : Family.card n = vecs.card := by
      sorry
    sorry

  grw[hF]
  omega
