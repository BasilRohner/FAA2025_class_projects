/-
  Explicit Construction of Ramsey Graphs

  Authors: Flurin Steck, Basil Rohner
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Disjoint
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

set_option maxHeartbeats 400000000
set_option diagnostics true
open MvPolynomial

namespace Constructions

notation "⟦"n"⟧" => Finset (Fin n)

-- *THIS IS JUST NECESSARY TO HAVE*

lemma Zp_properties
    {p : ℕ}
    (hp : p.Prime) :
    Nontrivial (ZMod p) ∧ NoZeroDivisors (ZMod p) := by
  constructor
  · apply nontrivial_iff.2
    use 0
    use 1
    have : ZMod.val (0 : ZMod p) = 0 := by
      apply ZMod.val_zero
    have : ZMod.val (1 : ZMod p) = 1 := by
      have := Fact.mk hp.one_lt
      apply ZMod.val_one
    grind
  · have := Fact.mk hp
    exact inferInstance

-- Definition of Set Families

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

class L_p_Family (n : ℕ) extends Family n where
  L : Finset ℕ
  s := L.card
  s_eq : s = L.card := by rfl
  p : ℕ
  p_prime : p.Prime
  p_neq_one : p ≠ 1
  L_p_intersecting :
    (∀ F ∈ elems, F.card.mod p ∉ L) ∧
    (∀ F1 ∈ elems, ∀ F2 ∈ elems, F1 ≠ F2 → (F1 ∩ F2).card.mod p ∈ L)

class k_L_p_Family (n : ℕ) extends L_p_Family n where
  k : ℕ
  k_bounded : ∀ F ∈ elems, (F.card % p) = k
  k_not : ∀ l ∈ L , (l % p) ≠ k

-- Definition of MLE Polynomials

noncomputable def MLE
    {R : Type*}
    [CommSemiring R]
    {n : ℕ}
    (f : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R :=
  f.sum (fun m a ↦ C a * Finset.univ.prod (fun i ↦ if m i = 0 then 1 else X i))

lemma MLE_degreeOf_le
    {R : Type*}
    [CommSemiring R]
    [Nontrivial R]
    {n : ℕ}
    (f : MvPolynomial (Fin n) R)
    (i : Fin n) :
    degreeOf i (MLE f) ≤ 1 := by
  grw [MLE, Finsupp.sum, degreeOf_sum_le]
  simp
  intro a b
  grw [degreeOf_C_mul_le, degreeOf_prod_le]
  rw [Finset.sum_eq_single i]
  · split_ifs
    · rw [←C_1]
      grw [degreeOf_C]
      omega
    · rw [degreeOf_X, if_pos rfl]
  · intro k _ h_neq
    split_ifs
    · apply degreeOf_C
    · rw [degreeOf_X, if_neg h_neq.symm]
  · intro h
    exact h (Finset.mem_univ i)|>.elim

lemma MLE_totalDegree_le
    {R : Type*}
    [CommSemiring R]
    [Nontrivial R]
    {n : ℕ}
    (f: MvPolynomial (Fin n) R) :
    totalDegree (MLE f) ≤ n := by
  simp only [totalDegree, Finset.sup_le_iff, mem_support_iff, ne_eq]
  have h : ∀ b : Fin n →₀ ℕ, b ∈ (MLE f).support → ∀ i, b i ≤ 1 := by
    intro m hm i
    have := MLE_degreeOf_le f i
    simp_all only [mem_support_iff, ne_eq, degreeOf_eq_sup, Finset.sup_le_iff, not_false_eq_true]
  intro b hb
  have := h b (by simpa using hb)
  rw [Finsupp.sum_fintype]
  exact le_trans (Finset.sum_le_sum (fun i _ ↦ this i)) (by simp)
  intro i
  rfl

lemma MLE_equal_on_boolean_cube
    {R : Type*}
    [CommSemiring R]
    [Nontrivial R]
    {n : ℕ}
    (f : MvPolynomial (Fin n) R) :
    ∀ g : Fin n → R, (∀ i : Fin n, g i = 0 ∨ g i = 1) → eval g f = eval g (MLE f) := by
  intro g hg
  grw [MLE, f.as_sum, map_sum, Finsupp.sum]
  simp only [support_sum_monomial_coeff, map_sum, map_mul, eval_C, map_prod]
  apply Finset.sum_congr rfl
  intro x hx
  grw [eval_monomial, coeff]
  simp only [Finsupp.prod_pow]
  have h_prod_eq : ∀ i, g i ^x i = (if x i = 0 then 1 else g i) := by
    intro i
    specialize hg i
    simp_all only [mem_support_iff, ne_eq]
    cases hg with
    | inl h =>
      simp_all only
      split_ifs
      · simp_all only [pow_zero]
      · simp_all only [ne_eq, not_false_eq_true, zero_pow]
    | inr h_1 => simp_all only [one_pow, ite_self]
  exact congr_arg _ <| Finset.prod_congr rfl <| fun i _ ↦ by aesop

lemma MLE_totalDegree_non_increasing
    {R : Type*}
    [CommRing R]
    [Nontrivial R]
    {n k : ℕ}
    (p : MvPolynomial (Fin n) R)
    (h : totalDegree p ≤ k) :
    totalDegree (MLE p) ≤ k := by
  unfold MLE
  grw[Finsupp.sum, totalDegree_finset_sum, Finset.sup_le]
  intro b hb
  grw[totalDegree_mul, totalDegree_C, totalDegree_finset_prod]
  simp
  simp [totalDegree_one, totalDegree_X, apply_ite totalDegree]
  apply le_trans _ h
  apply le_trans _ (le_totalDegree hb)
  rw [Finsupp.sum]
  rw [← Finset.sum_subset <| Finset.subset_univ b.support] -- some Gemini Magic
  apply Finset.sum_le_sum
  intro i hi
  cases b i
  repeat simp

-- Relevant Polynomials and Vectors

structure Vec {α : Type*} (n : ℕ) where
  elem : Fin n → α
  deriving DecidableEq

@[simp]
def Char_Vec
    {R : Type*}
    [CommSemiring R]
    {n : ℕ}
    (S : Finset (Fin n))
    [DecidablePred (fun i ↦ i ∈ S)] :
    Vec (α := R) n where
  elem := fun i ↦ if i ∈ S then (1 : R) else (0 : R)

@[simp]
def vec_dot
    {R : Type*}
    [CommSemiring R]
    {n : ℕ}
    (v w : Vec (α := R) n) : R :=
  ∑ i : Fin n, v.elem i * w.elem i

theorem char_vec_dot_inter
    {R : Type*}
    [CommSemiring R]
    {n : ℕ}
    (U W : ⟦n⟧) :
    vec_dot (Char_Vec (R := R) U) (Char_Vec (R := R) W) = (U ∩ W).card := by
  simp [Finset.inter_comm]

-- Constructions of polynomials for the problem

noncomputable def poly_f_Zp
    {n p : ℕ}
    (v : Vec (α := ZMod p) n)
    (L : Finset ℕ) :
    MvPolynomial (Fin n) (ZMod p) :=
  ∏ l ∈ L, (∑ i : Fin n, C (v.elem i) * X i - C (l : ZMod p))

noncomputable def poly_f_Q
    {n : ℕ}
    (v : Vec (α := ℚ) n)
    (L : Finset ℕ) :
    MvPolynomial (Fin n) ℚ :=
  ∏ l ∈ L, (∑ i : Fin n, C (v.elem i) * X i - C (l : ℚ))

noncomputable def poly_g_Zp
    {n p : ℕ}
    (I : Finset (Fin n))
    (k : ZMod p) :
    MvPolynomial (Fin n) (ZMod p) :=
  (∑ i : Fin n, X i - C k) * ∏ i ∈ I, X i

noncomputable def poly_g_Q
    {n : ℕ}
    (I : Finset (Fin n))
    (k : ℚ) :
    MvPolynomial (Fin n) ℚ :=
  (∑ i : Fin n, X i - C k) * ∏ i ∈ I, X i

/-
  **TODO** THIS NEEDS POLISHING, terrible
-/
noncomputable def validExponents (n p : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finset.range (p + 1)).biUnion fun k => (Finset.univ : Finset (Fin n)).powersetCard k |>.image fun s => ∑ i ∈ s, Finsupp.single i 1

theorem card_validExponents (n p : ℕ) : (validExponents n p).card = ∑ i ∈ Finset.range (p + 1), Nat.choose n i := by
  erw [ Finset.card_biUnion ];
  · refine' Finset.sum_congr rfl fun i hi => _;
    rw [ Finset.card_image_of_injOn ];
    · simp +decide [ Finset.card_univ ];
    · intro s hs t ht h_eq; simp_all +decide [ Finset.ext_iff ] ;
      intro a; replace h_eq := congr_arg ( fun f => f a ) h_eq; simp_all +decide [ Finsupp.single_apply ] ;
      grind;
  · intros k hk l hl hkl; simp_all +decide [ Finset.disjoint_left ] ;
    intro a ha x hx H; replace H := congr_arg Finsupp.toMultiset H; simp_all +decide [ Finset.sum_apply' ] ;

theorem mem_span_validExponents {n p q : ℕ} (f : MvPolynomial (Fin n) (ZMod q))
    (h_multi : ∀ i, degreeOf i f ≤ 1)
    (h_total : totalDegree f ≤ p) :
    f ∈ Submodule.span (ZMod q) ((validExponents n p).image (fun m => monomial m (1 : ZMod q)) : Set (MvPolynomial (Fin n) (ZMod q))) := by
  -- For any `m` in the support of `f`:
  -- a. Since `degreeOf i f ≤ 1` for all `i`, and `degreeOf i f` is the maximum of `m i` for `m` in support, we have `m i ≤ 1` for all `i`. Thus `m` is a sum of `single i 1` for `i` in some set `s`.
  have h_m_valid : ∀ m ∈ f.support, m ∈ validExponents n p := by
    intro m hm; simp_all +decide [ MvPolynomial.degreeOf_eq_sup ] ;
    -- Since `m` is in the support of `f`, we have `m` is a sum of `single i 1` for some set `s` with `card s ≤ p`.
    obtain ⟨s, hs⟩ : ∃ s : Finset (Fin n), m = ∑ i ∈ s, Finsupp.single i 1 := by
      use Finset.univ.filter (fun i => m i = 1);
      ext i; specialize h_multi i m hm; interval_cases _ : m i <;> simp_all +decide [ Finsupp.single_apply ] ;
    -- Since `m` is in the support of `f`, we have `m` is a sum of `single i 1` for some set `s` with `card s ≤ p`. Therefore, `m` is in the image of `validExponents n p`.
    have h_card_s : s.card ≤ p := by
      have h_card_s : m.sum (fun i e => e) ≤ p := by
        exact le_trans ( Finset.le_sup ( f := fun m => m.sum fun i e => e ) ( Finsupp.mem_support_iff.mpr hm ) ) h_total;
      simp_all +decide [ Finsupp.sum_sum_index' ];
    exact Finset.mem_biUnion.mpr ⟨ s.card, Finset.mem_range.mpr ( Nat.lt_succ_of_le h_card_s ), Finset.mem_image.mpr ⟨ s, Finset.mem_powersetCard.mpr ⟨ Finset.subset_univ _, rfl ⟩, hs.symm ⟩ ⟩;
  convert ( Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ ( f.coeff m ) <| Submodule.subset_span <| Finset.mem_image_of_mem _ <| h_m_valid m hm ) using 1;
  simp +decide [ MvPolynomial.smul_monomial ]

theorem total_degree_bound_Zp
    {n p q : ℕ}
    (S : Finset (MvPolynomial (Fin n) (ZMod q)))
    (h_multi : ∀ poly ∈ S, ∀ i, degreeOf i poly ≤ 1)
    (h_total : ∀ poly ∈ S, totalDegree poly ≤ p)
    (h_li : LinearIndependent (ZMod q) (Subtype.val : S → MvPolynomial (Fin n) (ZMod q))) :
    S.card ≤ ∑ i ∈ Finset.range (p + 1), Nat.choose n i := by
  -- Let $B$ be the image of `validExponents n p` under `m ↦ monomial m 1`. `B` is a finite set of polynomials.
  set B := (validExponents n p).image (fun m => monomial m (1 : ZMod q)) with hB;
  by_contra h_contra;
  -- Since $S$ is linearly independent and nonempty, $ZMod q$ must be nontrivial (otherwise $1=0$ and $0$ cannot be in a linearly independent set). Thus $ZMod q$ satisfies the `StrongRankCondition`.
  have h_nontrivial : Nontrivial (ZMod q) := by
    rcases q with ( _ | _ | q ) <;> simp_all +decide [ ZMod ];
    · infer_instance;
    · have h_card_S : S.card ≤ 1 := by
        have h_card_S : ∀ poly ∈ S, poly = 0 := by
          intro poly hpoly; ext; simp +decide [ ZMod ] ;
          exact Subsingleton.elim _ _;
        exact Finset.card_le_one.mpr fun x hx y hy => h_card_S x hx ▸ h_card_S y hy ▸ rfl;
      linarith [ Nat.choose_pos ( show 0 ≤ n by norm_num ), Finset.single_le_sum ( fun i _ => Nat.zero_le ( Nat.choose n i ) ) ( Finset.mem_range.mpr ( Nat.succ_pos p ) ) ];
    · exact ⟨ 0, 1, by simp +decide ⟩
  have h_span : ∀ poly ∈ S, poly ∈ Submodule.span (ZMod q) B := by
    exact?;
  have h_card : S.card ≤ B.card := by
    have h_card : S.card ≤ Module.finrank (ZMod q) (Submodule.span (ZMod q) (B : Set (MvPolynomial (Fin n) (ZMod q)))) := by
      have h_card : Module.finrank (ZMod q) (Submodule.span (ZMod q) (S : Set (MvPolynomial (Fin n) (ZMod q)))) ≤ Module.finrank (ZMod q) (Submodule.span (ZMod q) (B : Set (MvPolynomial (Fin n) (ZMod q)))) := by
        apply_rules [ Submodule.finrank_mono ];
        exact Submodule.span_le.mpr h_span;
      convert h_card using 1;
      exact?;
    refine le_trans h_card ?_;
    refine' le_trans ( finrank_span_le_card _ ) _ ; aesop;
  refine h_contra <| h_card.trans ?_;
  exact Finset.card_image_le.trans ( by rw [ card_validExponents ] )


theorem total_degree_bound_Q
    {n p : ℕ}
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
  -- Since $S$ is linearly independent and spans the submodule generated by $M$, we have $S.card \leq M.card$.
  have h_card_le : S.card ≤ Module.finrank ℚ (↥(Submodule.span ℚ (M : Set (MvPolynomial (Fin n) ℚ)))) := by
  -- and to make everything worse the lean compiler needs type hints here, I fear that this has dammaged me irreversibly
    have h_card_le : S.card ≤ Module.finrank ℚ (↥(Submodule.span ℚ (Set.range (Subtype.val : S → MvPolynomial (Fin n) ℚ)))) := by
      rw [@finrank_span_set_eq_card] <;> aesop
    refine le_trans h_card_le ?_
    apply Submodule.finrank_mono
    exact Submodule.span_le.2 h_span
  refine le_trans h_card_le ?_
  refine' le_trans ( finrank_span_le_card _ ) _
  -- time for my daily aesop prayer
  aesop

theorem deg_main_Zp --degree bound fot poly_f_ℤ/pℤ
  {n p k : ℕ}
  (hp : p.Prime)
  (v : Vec n)
  (L : Finset ℕ)
  (h : L.card ≤ k) :
  totalDegree (poly_f_Zp (p := p) v L) ≤ k := by
  unfold poly_f_Zp
  apply le_trans (totalDegree_finset_prod _ _)
  apply le_trans _ h
  rw[Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro x hx
  grw[totalDegree_sub, totalDegree_C, totalDegree_finset_sum]
  simp
  intro b
  have : (Nontrivial (ZMod p)) := by
    apply nontrivial_iff.2
    use 0
    use 1
    have : ZMod.val (0 : ZMod p) = 0 := by
      apply ZMod.val_zero
    have : ZMod.val (1 : ZMod p) = 1 := by
      have := Fact.mk hp.one_lt
      apply ZMod.val_one
    grind
  grw[totalDegree_mul,  totalDegree_C, totalDegree_X]

theorem deg_main_Q --degree bound fot poly_f_ℤ/pℤ
  {n k : ℕ}
  (v : Vec n)
  (L : Finset ℕ)
  (h : L.card ≤ k) :
  totalDegree (poly_f_Q v L) ≤ k := by
  unfold poly_f_Q
  apply le_trans (totalDegree_finset_prod _ _)
  apply le_trans _ h
  rw[Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro x hx
  grw[totalDegree_sub, totalDegree_C, totalDegree_finset_sum]
  simp
  intro b
  grw[totalDegree_mul,  totalDegree_C, totalDegree_X]

theorem deg_extra_Zp
    {n p s k : ℕ}
    (hp : p.Prime)
    (hn : n ≥ 1)
    (I : Finset (Fin n))
    (h1 : I.card ≤ s - 1)
    (h2 : s ≥ 1) :
    totalDegree (poly_g_Zp (p := p) I k) ≤ s := by
  have ⟨hRl, hRr⟩ := Zp_properties hp
  unfold poly_g_Zp
  grw [totalDegree_mul, totalDegree_sub, totalDegree_C, totalDegree_finset_prod]
  simp
  grw [totalDegree_finset_sum]
  conv =>
    left
    left
    right
    intro i
    rw [totalDegree_X]
  grw [h1]
  apply le_trans (Nat.add_le_add_right (Finset.sup_le (fun _ _ => le_rfl)) _)
  rw [Nat.add_comm, Nat.sub_add_cancel h2]

theorem deg_extra_Q
    {n s k : ℕ}
    (hn : n ≥ 1)
    (I : Finset (Fin n))
    (h1 : I.card ≤ s - 1)
    (h2 : s ≥ 1) :
    totalDegree (poly_g_Q I k) ≤ s := by
  unfold poly_g_Q
  grw[totalDegree_mul, totalDegree_sub, totalDegree_C, totalDegree_finset_prod]
  simp
  grw[h1, totalDegree_finset_sum]
  simp
  grw[Finset.univ.sup_const]
  omega
  rw [Finset.univ_nonempty_iff]
  exact ⟨0, hn⟩

-- Helper Result to show [Nontrivial (ZMod p)] [NoZeroDivisors (ZMod p)]

lemma nontrivial_Zp {p : ℕ} (hp : p.Prime) : Nontrivial (ZMod p) := by
  apply nontrivial_iff.2
  use 0
  use 1
  have : ZMod.val (0 : ZMod p) = 0 := by apply ZMod.val_zero
  have : ZMod.val (1 : ZMod p) = 1 := by
    have := Fact.mk <| hp.one_lt
    apply ZMod.val_one
  grind

lemma nozerodiv_Zp {p : ℕ} (hp : p.Prime) : NoZeroDivisors (ZMod p) := by
  have := hp.ne_one
  have := Fact.mk hp
  exact inferInstance

def vec_f_Zp
    {n : ℕ}
    (F : k_L_p_Family n) :
    Finset (Vec (α := ZMod F.p) n) :=
  F.elems.image (fun s ↦ Char_Vec s)

def vec_g_Zp
    {n: ℕ}
    (s : ℕ) :
    (Finset (Finset (Fin n))) :=
  (Finset.powerset Finset.univ).filter (fun x ↦ x.card < s)

noncomputable def poly_f_family
    {n : ℕ}
    (F : k_L_p_Family n) :
    Finset (MvPolynomial (Fin n) (ZMod F.p)) :=
  (vec_f_Zp F).image (fun v ↦ MLE (poly_f_Zp v F.L))

noncomputable def poly_g_family
    {n : ℕ}
    (F : k_L_p_Family n) :
    Finset (MvPolynomial (Fin n) (ZMod F.p)) :=
  (vec_g_Zp F.s).image (fun v ↦ MLE (poly_g_Zp v (F.k : ZMod F.p)))

lemma eval_poly_f_Zp_self
    {n : ℕ}
    (F : k_L_p_Family n)
    (S : ⟦n⟧)
    (hS : S ∈ F.elems)
    (hL : ∀ l ∈ F.L, l < F.k) :
    eval (Char_Vec (R := ZMod F.p) S).elem (poly_f_Zp (Char_Vec (R := ZMod F.p) S) F.L) ≠ 0 := by
  have ⟨hpl, hpr⟩ := Zp_properties F.p_prime
  unfold poly_f_Zp
  simp
  push_neg
  apply Finset.prod_ne_zero_iff.mpr
  intro a ah
  rw [sub_ne_zero]
  have := F.L_p_intersecting.1 S hS
  have h_diff : (S.card % F.p : ℕ) ≠ a := by
    by_contra h_eq
    apply this
    rw [←h_eq] at ah
    assumption
  by_contra h_eq
  have h_a : a < F.p := by
    have h_k : F.k < F.p := by
      have := F.k_bounded S hS
      symm at this
      have := Nat.mod_lt S.card (F.p_prime.pos)
      expose_names
      rw [←this_2] at this
      assumption
    linarith [hL a ah]
  apply h_diff
  have := Nat.mod_eq_of_lt h_a
  rw [←this]
  apply (ZMod.natCast_eq_natCast_iff' S.card a F.p).1
  assumption

lemma eval_poly_f_Zp_other
    {n : ℕ}
    (F : k_L_p_Family n)
    (S T : ⟦n⟧)
    (hS : S ∈ F.elems)
    (hT : T ∈ F.elems)
    (hne : S ≠ T) :
    eval (Char_Vec S (R := ZMod F.p)).elem (poly_f_Zp (Char_Vec T (R := ZMod F.p)) F.L) = 0 := by
   -- TODO
    -- Since $S$ and $T$ are distinct elements of the family, their dot product modulo $p$ is in $L$.
  have h_dot_mod_p_in_L : (vec_dot (Char_Vec S) (Char_Vec T) : ℕ) % F.p ∈ F.L := by
    -- By definition of $F$, we know that $|S \cap T| \equiv l \pmod{p}$ for some $l \in L$.
    have h_inter_mod_p : (S ∩ T).card % F.p ∈ F.L := by
      -- Apply the hypothesis `hL` to the sets `S` and `T`.
      apply (F.L_p_intersecting).right S hS T hT hne;
    rwa [ char_vec_dot_inter ];
  unfold Constructions.poly_f_Zp;
  rw [ MvPolynomial.eval_prod, Finset.prod_eq_zero h_dot_mod_p_in_L ] ; aesop

lemma eval_poly_g_Zp_vecs
    {n : ℕ}
    (F : k_L_p_Family n)
    (i : Finset (Fin n))
    (hi : i ∈ vec_g_Zp F.s)
    (v : Vec (α := ZMod F.p) n)
    (hv : v ∈ vec_f_Zp F) :
    eval v.elem (poly_g_Zp i (F.k : ZMod F.p)) = 0 := by
  -- Since $v$ is in the image of $F.elems$ under the characteristic vector map, there exists some $S \in F.elems$ such that $v = \text{Char\_Vec } S$.
  obtain ⟨S, hS⟩ : ∃ S ∈ F.elems, v = Constructions.Char_Vec S := by
    unfold Constructions.vec_f_Zp at hv; aesop;
  -- Since $S$ is a $k$-set, we have $\sum_{i \in S} v_i = k$.
  have h_sum : ∑ i ∈ Finset.univ, (v.elem i) = F.k := by
    rw [ ← F.k_bounded S hS.1 ] ; aesop;
  unfold Constructions.poly_g_Zp; aesop;

lemma poly_f_family_card
    {n : ℕ}
    (F : k_L_p_Family n)
    (hl : ∀ l ∈ F.L, l < F.k) :
    (poly_f_family F).card = F.card := by
  -- TODO
  rw [ Constructions.poly_f_family, Finset.card_image_of_injOn ];
  · -- Since the characteristic vector function is injective, the cardinality of the image is equal to the cardinality of the domain.
    have h_inj : Function.Injective (fun S : Finset (Fin n) => Char_Vec (R := ZMod F.p) S) := by
      intro S T h_eq
      ext i
      simp [Constructions.Char_Vec] at h_eq;
      -- By evaluating the functions at i, we can see that if i is in S, then the function returns 1, and if i is in T, it also returns 1. Therefore, i must be in both S and T or neither.
      have h_eq_i : (if i ∈ S then 1 else 0 : ZMod F.p) = (if i ∈ T then 1 else 0 : ZMod F.p) := by
        exact congr_fun h_eq i;
      -- By splitting into cases based on whether i is in S or not, we can show that the if statements being equal implies that i is in S if and only if it's in T.
      by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;> simp +decide [ hiS, hiT ] at h_eq_i ⊢;
      · haveI := Fact.mk F.p_prime; simp_all +decide ;
      · exact absurd h_eq_i ( by haveI := Fact.mk F.p_prime; simp +decide );
    rw [ Constructions.vec_f_Zp, Finset.card_image_of_injective _ h_inj ];
    exact F.card_eq.symm;
  · -- To prove injectivity, assume two different characteristic vectors $v$ and $w$ map to the same polynomial under $MLE$.
    intro v hv w hw h_eq
    have h_eval : ∀ S : Finset (Fin n), S ∈ F.elems → eval (Char_Vec (R := ZMod F.p) S).elem (poly_f_Zp v F.L) = eval (Char_Vec (R := ZMod F.p) S).elem (poly_f_Zp w F.L) := by
      -- Since $v$ and $w$ are in the image of $vec_f_Zp F$, their evaluations at $Char_Vec S$ are equal.
      intros S hS
      have h_eval_eq : eval (Char_Vec (R := ZMod F.p) S).elem (poly_f_Zp v F.L) = eval (Char_Vec (R := ZMod F.p) S).elem (MLE (poly_f_Zp v F.L)) ∧ eval (Char_Vec (R := ZMod F.p) S).elem (poly_f_Zp w F.L) = eval (Char_Vec (R := ZMod F.p) S).elem (MLE (poly_f_Zp w F.L)) := by
        apply And.intro;
        · apply_rules [ MLE_equal_on_boolean_cube ];
          · exact fun i => by unfold Constructions.Char_Vec; by_cases hi : i ∈ S <;> simp +decide [ hi ] ;
          · haveI := Fact.mk ( F.p_prime ) ; infer_instance;
        · apply_rules [ Constructions.MLE_equal_on_boolean_cube ];
          · exact fun i => by unfold Constructions.Char_Vec; by_cases hi : i ∈ S <;> simp +decide [ hi ] ;
          · haveI := Fact.mk ( F.p_prime ) ; infer_instance;
      aesop;
    obtain ⟨S, hS⟩ : ∃ S ∈ F.elems, v = Char_Vec (R := ZMod F.p) S := by
      unfold Constructions.vec_f_Zp at hv; aesop;
    obtain ⟨T, hT⟩ : ∃ T ∈ F.elems, w = Char_Vec (R := ZMod F.p) T := by
      unfold Constructions.vec_f_Zp at hw; aesop;
    have h_eq : S = T := by
      contrapose! h_eval;
      have := eval_poly_f_Zp_self F S hS.1 hl; have := eval_poly_f_Zp_other F S T hS.1 hT.1 h_eval; aesop;
    aesop

lemma poly_f_family_linear_independence
    {n : ℕ}
    (F : k_L_p_Family n)
    (hl : ∀ l ∈ F.L, l < F.k) :
    ∀ v ∈ vec_f_Zp F, ∃ z : (Fin n → (ZMod F.p)),
      (eval z (MLE (poly_f_Zp v F.L)) ≠ 0) ∧
      (∀ i ∈ vec_g_Zp F.s, eval z (MLE (poly_g_Zp i (F.k : ZMod F.p))) = 0) ∧
      (∀ j ∈ vec_f_Zp F, MLE (poly_f_Zp v F.L) ≠ MLE (poly_f_Zp j F.L) → eval z (MLE (poly_f_Zp j F.L)) = 0) := by
  -- TODO
  intro v hv
  obtain ⟨S, hS⟩ : ∃ S ∈ F.elems, v = Char_Vec S := by
    unfold Constructions.vec_f_Zp at hv; aesop;
  use (Char_Vec S).elem
  simp [hS];
  -- By definition of $MLE$, we know that $MLE (poly_f_Zp v F.L)$ evaluates to $poly_f_Zp v F.L$ at $v$.
  have h_eval_f : ∀ v ∈ vec_f_Zp F, (MvPolynomial.eval (Char_Vec (R := ZMod F.p) S).elem (Constructions.MLE (Constructions.poly_f_Zp v F.L))) = (MvPolynomial.eval (Char_Vec (R := ZMod F.p) S).elem (Constructions.poly_f_Zp v F.L)) := by
    intros v hv
    apply Eq.symm;
    apply_rules [ MLE_equal_on_boolean_cube ];
    · exact fun i => by unfold Constructions.Char_Vec; by_cases hi : i ∈ S <;> simp +decide [ hi ] ;
    · exact nontrivial_Zp F.p_prime;
  refine' ⟨ _, _, _ ⟩;
  · convert eval_poly_f_Zp_self F S hS.1 hl using 1;
    convert Iff.rfl using 2 ; aesop ( simp_config := { singlePass := true } ) ;
  · intro i hi
    have h_eval_g : (MvPolynomial.eval (Char_Vec S (R := ZMod F.p)).elem (poly_g_Zp i (F.k : ZMod F.p))) = 0 := by
      have := eval_poly_g_Zp_vecs F i hi ( Char_Vec S ) ?_ <;> aesop;
    convert h_eval_g using 1;
    convert Constructions.MLE_equal_on_boolean_cube _ _ using 1;
    any_goals exact fun i => if i ∈ S then 1 else 0;
    any_goals exact MvPolynomial.C 0;
    · simp +decide [ Constructions.MLE ];
      simp +decide [ Finsupp.sum ];
      rw [ MvPolynomial.eval_eq' ];
      exact Finset.sum_congr rfl fun _ _ => by congr; ext; aesop;
    · infer_instance;
  · intro j hj hj_ne;
    obtain ⟨T, hT⟩ : ∃ T ∈ F.elems, j = Char_Vec T := by
      unfold Constructions.vec_f_Zp at hj; aesop;
    have h_eval_f : (MvPolynomial.eval (Char_Vec (R := ZMod F.p) S).elem (Constructions.poly_f_Zp (Char_Vec T) F.L)) = 0 := by
      apply eval_poly_f_Zp_other F S T hS.left hT.left;
      contrapose! hj_ne; aesop;
    aesop

lemma poly_g_family_linear_independence
    {n : ℕ}
    (F : k_L_p_Family n)
    (hl : ∀ l ∈ F.L, l < F.k) :
    ∀ i ∈ vec_g_Zp F.s, ∃ z : (Fin n → (ZMod F.p)),
      (eval z (MLE (poly_g_Zp i (F.k : ZMod F.p))) ≠ 0) ∧
      (∀ j ∈ vec_g_Zp F.s, MLE (poly_g_Zp i (F.k : ZMod F.p)) ≠ MLE (poly_g_Zp j (F.k : ZMod F.p)) ∧
        i.card ≤ j.card → eval z (MLE (poly_g_Zp j (F.k : ZMod F.p))) = 0) := by
  admit

lemma poly_g_poly_f_family_disjoint
    {n : ℕ}
    (F : k_L_p_Family n)
    (hl : ∀ l ∈ F.L, l < F.k) :
    Disjoint (poly_f_family F) (poly_g_family F) := by
  -- TODO
  unfold Constructions.poly_f_family Constructions.poly_g_family;
  -- To show disjointness, assume there exists an element in both images. This would imply that the polynomial from the L_p_family can be written as a linear combination of polynomials from the k_L_p_family, which contradicts the linear independence.
  by_contra h_not_disjoint;
  -- If there exists a polynomial in both images, then there exists a vector $v$ in the L_p_family and an $i$ in the k_L_p_family such that $MLE(poly_f_Zp v F.L) = MLE(poly_g_Zp i (F.k : ZMod F.p))$.
  obtain ⟨v, hv, i, hi, h_eq⟩ : ∃ v ∈ vec_f_Zp F, ∃ i ∈ vec_g_Zp F.s, MLE (poly_f_Zp v F.L) = MLE (poly_g_Zp i (F.k : ZMod F.p)) := by
    rw [ Finset.not_disjoint_iff ] at h_not_disjoint ; aesop;
  have := poly_f_family_linear_independence F hl v hv;
  obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := this; specialize hz₂ i hi; aesop;

lemma linear_independent_of_triangular_eval
    {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    {n : ℕ}
    (S : Finset (MvPolynomial (Fin n) R))
    (order : MvPolynomial (Fin n) R → ℕ)
    (h : ∀ p ∈ S, ∃ z : Fin n → R, (MvPolynomial.eval z p ≠ 0) ∧ (∀ q ∈ S, q ≠ p → order p ≤ order q → MvPolynomial.eval z q = 0)) :
    LinearIndependent R (Subtype.val : S → MvPolynomial (Fin n) R) := by
      rw [ Fintype.linearIndependent_iff ];
      intro g hg;
      by_contra h_nonzero;
      -- Let $i_0$ be an index such that $g(i_0) \neq 0$ and $order(i_0)$ is minimal among the indices where $g(i) \neq 0$.
      obtain ⟨i₀, hi₀⟩ : ∃ i₀ : { x : MvPolynomial (Fin n) R // x ∈ S }, g i₀ ≠ 0 ∧ ∀ i : { x : MvPolynomial (Fin n) R // x ∈ S }, g i ≠ 0 → order i₀ ≤ order i := by
        have h_min : ∃ i₀ ∈ {i : { x : MvPolynomial (Fin n) R // x ∈ S } | g i ≠ 0}, ∀ i ∈ {i : { x : MvPolynomial (Fin n) R // x ∈ S } | g i ≠ 0}, order i₀ ≤ order i := by
          apply_rules [ Set.exists_min_image ];
          · exact Set.toFinite _;
          · exact by push_neg at h_nonzero; exact h_nonzero.imp fun i hi => by simpa using hi;
        exact?;
      obtain ⟨ z, hz₁, hz₂ ⟩ := h i₀ i₀.2;
      replace hg := congr_arg ( MvPolynomial.eval z ) hg;
      simp +zetaDelta at *;
      rw [ Finset.sum_eq_single i₀ ] at hg <;> simp_all +decide;
      exact fun a ha ha' => Classical.or_iff_not_imp_left.2 fun ha'' => hz₂ a ha ( by simpa [ Subtype.ext_iff ] using ha' ) ( hi₀.2 a ha ha'' )

lemma poly_g_family_is_linear_independent
    {n : ℕ}
    (F : Constructions.k_L_p_Family n)
    (hl : ∀ l ∈ F.L, l < F.k) :
    LinearIndependent (ZMod F.p) (Subtype.val : Constructions.poly_g_family F → MvPolynomial (Fin n) (ZMod F.p)) := by
      convert linear_independent_of_triangular_eval ( poly_g_family F ) _ _;
      convert Zp_properties F.p_prime |>.1 using 1
      all_goals generalize_proofs at *;
      rotate_left;
      use fun p => if hp : p ∈ Constructions.poly_g_family F then Classical.choose ( Finset.mem_image.mp hp ) |> Finset.card else 0;
      · intro p hp
        obtain ⟨z, hz⟩ := Constructions.poly_g_family_linear_independence F hl (Classical.choose (Finset.mem_image.mp hp)) (Classical.choose_spec (Finset.mem_image.mp hp) |>.1);
        use z;
        refine' ⟨ _, _ ⟩;
        · have := Classical.choose_spec ( Finset.mem_image.mp hp ) ; aesop;
        · intro q hq hne hle;
          convert hz.2 ( Classical.choose ( Finset.mem_image.mp hq ) ) ( Classical.choose_spec ( Finset.mem_image.mp hq ) |>.1 ) _;
          · exact Classical.choose_spec ( Finset.mem_image.mp hq ) |>.2.symm;
          · have := Classical.choose_spec ( Finset.mem_image.mp hp ) |>.2; have := Classical.choose_spec ( Finset.mem_image.mp hq ) |>.2; aesop;
      · haveI := Fact.mk F.p_prime; infer_instance;

lemma linear_independent_union_with_evaluation_dual
    {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    {n : ℕ}
    (S1 S2 : Finset (MvPolynomial (Fin n) R))
    (h_disj : Disjoint S1 S2)
    (h_dual : ∀ p ∈ S1, ∃ z : Fin n → R, (MvPolynomial.eval z p ≠ 0) ∧ (∀ q ∈ S1, q ≠ p → MvPolynomial.eval z q = 0) ∧ (∀ r ∈ S2, MvPolynomial.eval z r = 0))
    (h_indep : LinearIndependent R (Subtype.val : S2 → MvPolynomial (Fin n) R)) :
    LinearIndependent R (Subtype.val : (↑S1 ∪ ↑S2 : Set (MvPolynomial (Fin n) R)) → MvPolynomial (Fin n) R) := by
      -- Apply the hypothesis `h_dual` to each polynomial in `S1` to construct the required vectors.
      have h_vectors : ∀ p ∈ S1, ∃ z : Fin n → R, (MvPolynomial.eval z p ≠ 0) ∧ (∀ q ∈ S1, q ≠ p → MvPolynomial.eval z q = 0) ∧ ∀ r ∈ S2, MvPolynomial.eval z r = 0 := by
        assumption;
      choose! z hz using h_vectors;
      -- Show that the polynomials in $S1$ are linearly independent.
      have h_S1_indep : LinearIndependent R (Subtype.val : S1 → MvPolynomial (Fin n) R) := by
        apply linear_independent_of_triangular_eval;
        exact fun p hp => ⟨ z p, hz p hp |>.1, fun q hq hne hle => hz p hp |>.2.1 q hq hne ⟩;
        exact fun _ => 0;
      rw [ linearIndependent_subtype_iff ] at *;
      convert h_S1_indep.union h_indep _ using 1;
      simp_all +decide [ Finset.disjoint_left, Submodule.disjoint_def ];
      intro x hx1 hx2
      obtain ⟨c, hc⟩ : ∃ c : MvPolynomial (Fin n) R →₀ R, x = ∑ p ∈ S1, c p • p := by
        rw [ Finsupp.mem_span_iff_linearCombination ] at hx1;
        obtain ⟨ l, rfl ⟩ := hx1;
        refine' ⟨ l.sum fun p hp => Finsupp.single p.val ( l p ), _ ⟩ ; simp +decide [ Finsupp.linearCombination_apply, Finsupp.sum_fintype ];
        refine' Finset.sum_bij ( fun x _ => x.val ) _ _ _ _ <;> simp +decide;
        simp +decide [ Finsupp.sum, Finsupp.single_apply ];
        intro a ha; rw [ Finset.sum_eq_single ⟨ a, ha ⟩ ] <;> simp +contextual [ Finsupp.single_apply ] ;
      obtain ⟨d, hd⟩ : ∃ d : MvPolynomial (Fin n) R →₀ R, x = ∑ p ∈ S2, d p • p := by
        rw [ Finsupp.mem_span_iff_linearCombination ] at hx2;
        obtain ⟨ l, hl ⟩ := hx2;
        refine' ⟨ l.sum fun p hp => Finsupp.single p.1 ( l p ), _ ⟩;
        simp +decide [ ← hl, Finsupp.linearCombination_apply, Finsupp.sum_fintype ];
        refine' Finset.sum_bij ( fun x _ => x.val ) _ _ _ _ <;> simp +decide;
        simp +decide [ Finsupp.sum ];
        intro a ha; rw [ Finset.sum_eq_single ⟨ a, ha ⟩ ] <;> simp +contextual [ Finsupp.single_apply ] ;
      -- By evaluating the sum at $z_p$, we can isolate the coefficient $c_p$.
      have h_eval : ∀ p ∈ S1, c p • MvPolynomial.eval (z p) p = 0 := by
        intro p hp
        have h_eval : MvPolynomial.eval (z p) x = 0 := by
          rw [ hd, map_sum ];
          exact Finset.sum_eq_zero fun q hq => by simp +decide [ hz p hp |>.2.2 q hq ] ;
        rw [ hc, map_sum ] at h_eval;
        rw [ Finset.sum_eq_single p ] at h_eval <;> simp_all +decide [ Algebra.smul_def ];
      simp_all +decide [ Finsupp.mem_support_iff ]

lemma poly_g_poly_f_family_linear_independence
    {n : ℕ}
    (F : k_L_p_Family n)
    (hl : ∀ l ∈ F.L, l < F.k) :
    LinearIndependent (ZMod F.p) (Subtype.val : (↑(poly_f_family F) ∪ ↑(poly_g_family F) : Set (MvPolynomial (Fin n) (ZMod F.p))) → MvPolynomial (Fin n) (ZMod F.p)) := by
  convert linear_independent_union_with_evaluation_dual ( Constructions.poly_f_family F ) ( Constructions.poly_g_family F ) _ _ _ using 1;
  · haveI := Fact.mk ( F.p_prime ) ; infer_instance;
  · haveI := Fact.mk ( F.p_prime ) ; infer_instance;
  · exact?;
  · rintro p hp;
    unfold Constructions.poly_f_family Constructions.poly_g_family at *;
    obtain ⟨ v, hv, rfl ⟩ := Finset.mem_image.mp hp;
    obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := Constructions.poly_f_family_linear_independence F hl v hv;
    simp +zetaDelta at *;
    exact ⟨ z, hz₁, fun a ha ha' => hz₃ a ha ( Ne.symm ha' ), hz₂ ⟩;
  · convert Constructions.poly_g_family_is_linear_independent F hl


@[simp]
theorem AlonBabaiSuzuki
    {n : ℕ}
    (hn : n ≥ 1) -- adding this shouldnt be harmful
    (F : k_L_p_Family n) :
    F.s ≤ F.p - 1 ∧ F.s + F.k ≤ n → F.card ≤ n.choose F.s := by

  intro ⟨h1, h2⟩
  let p := F.p
  let R := ZMod p
  let ⟨hRl, hRr⟩ := Zp_properties F.p_prime

  let vecs_f := vec_f_Zp F
  let vecs_g := vec_g_Zp (n := n) F.s
  let poly_f := vecs_f.image (fun i ↦ MLE (poly_f_Zp (p := p) i F.L))
  let poly_g := vecs_g.image (fun i ↦ MLE (poly_g_Zp (p := p) i F.k))

  -- Entries of the vector are in {0,1}
  have h_vecs : ∀ v ∈ vecs_f, ∀ i : Fin n, v.elem i = 0 ∨ v.elem i = 1 := by
    intro v hv i
    simp [vecs_f, vec_f_Zp] at hv
    obtain ⟨a, ⟨fal, far⟩⟩ := hv
    simp [←far]
    grind

  -- Linear independence for polynomials poly_f_Zp
  have h_poly_f :
    ∀ v ∈ vecs_f,
    ∃ z : (Fin n) → (ZMod p),
    ∀ w ∈ vecs_f,
    ∀ y ∈ vecs_g,
      let x1 := MLE (poly_f_Zp (p := p) v F.L)
      let x2 := MLE (poly_g_Zp (p := p) y F.k)
      let x3 := MLE (poly_f_Zp (p := p) w F.L)
      eval z x1 ≠ 0 ∧ eval z x2 = 0 ∧ x1 ≠ x3 → eval z x3 = 0 := by
    -- TODO
    field_simp;
    -- For each vector v in vecs_f, we can choose z to be v. This z will satisfy the conditions that eval z (MLE (poly_f_Zp v F.L)) is non-zero, eval z (MLE (poly_g_Zp y F.k)) is zero for all y in vecs_g, and if v and w are distinct, then eval z (MLE (poly_f_Zp w F.L)) is zero.
    intros v hv
    use v.elem;
    intro w hw y hy h; have := h.2.2; simp_all +decide [ MvPolynomial.eval_eq' ] ;
    -- Since $v \neq w$, we have $eval v (MLE (poly_f_Zp w F.L)) = 0$ by the properties of the polynomials.
    have h_eval_zero : MvPolynomial.eval v.elem (Constructions.poly_f_Zp w F.L) = 0 := by
      -- Since $v \neq w$, we have $eval v (poly_f_Zp w F.L) = 0$ by the properties of the polynomials.
      have h_eval_zero : ∀ S T : Finset (Fin n), S ∈ F.elems → T ∈ F.elems → S ≠ T → MvPolynomial.eval (Char_Vec S (R := ZMod p)).elem (Constructions.poly_f_Zp (Char_Vec T (R := ZMod p)) F.L) = 0 := by
        exact?;
      obtain ⟨ S, hS, rfl ⟩ := Finset.mem_image.mp hv; obtain ⟨ T, hT, rfl ⟩ := Finset.mem_image.mp hw; specialize h_eval_zero S T hS hT; aesop;
    convert h_eval_zero using 1;
    rw [ Constructions.MLE_equal_on_boolean_cube ];
    · rw [ MvPolynomial.eval_eq' ];
    · exact h_vecs v hv

  -- Linear independence for polynomials poly_g_Zp
  /-
    have h_P2 : ∀ i ∈ extras, ∃ z : ((Fin n) → ℚ), ∀ j ∈ extras,
    let x := MLE (poly_g_Q i F.k);
    (eval z x) ≠  0 ∧
    let y := MLE (poly_g_Q j F.k);
     x ≠ y ∧ i.card ≤ j.card →  (eval z y) = 0 := by
  -/
  have h_poly_g :
      ∀ v ∈ vecs_g,
      ∃ z : (Fin n) → (ZMod p),
      ∀ w ∈ vecs_g,
        let x1 := MLE (poly_g_Zp (p := p) v F.k)
        let x2 := MLE (poly_g_Zp (p := p) w F.k)
        eval z x1 ≠ 0 ∧ (x1 ≠ x2 ∧ v.card ≤ w.card → eval z x2 = 0) := by
    intros i hi
    use (fun a ↦ if a ∈ i then 1 else 0)
    intro j hj x1 x2
    constructor
    · admit
      /-
      grw[Int.subNat_eq_zero_iff]
      have hI : i.card < F.k := by
        grw[<-h_sk]
        unfold extras at hi
        grind
      omega
      grw[Finset.prod_eq_zero_iff] -- if every term is 1, Π cant be 0
      simp
      grind
      -/
    · intro hh
      unfold x2 poly_g_Zp
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

  have h_degreeOf :
      ∀ poly ∈ poly_f ∪ poly_g,
      ∀ i : Fin n,
        degreeOf i poly ≤ 1 := by
    intro poly h_poly i
    simp at h_poly
    cases h_poly <;> expose_names
    · simp [poly_f] at h
      obtain ⟨hl, ⟨hrl, hrr⟩⟩ := h
      rw [←hrr]
      exact MLE_degreeOf_le (poly_f_Zp hl F.L) i
    · simp [poly_g] at h
      obtain ⟨hl, ⟨hrl, hrr⟩⟩ := h
      rw [←hrr]
      exact MLE_degreeOf_le (poly_g_Zp hl (F.k : R)) i

  have h_totalDegree :
      ∀ poly ∈ poly_f ∪ poly_g,
      poly.totalDegree ≤ F.s := by
    intro poly h_poly
    simp at h_poly
    cases h_poly <;> expose_names
    · simp [poly_f] at h
      obtain ⟨hl, ⟨hrl, hrr⟩⟩ := h
      rw [←hrr]
      apply MLE_totalDegree_non_increasing
      apply deg_main_Zp
      exact F.p_prime
      grw [F.s_eq]
    · simp [poly_g] at h
      obtain ⟨hl, ⟨hrl, hrr⟩⟩ := h
      rw [←hrr]
      apply MLE_totalDegree_non_increasing
      apply deg_extra_Zp
      exact F.p_prime
      exact hn
      -- TODO
      obtain ⟨I, hI⟩ : ∃ I ∈ Finset.powerset Finset.univ, I.card < F.s ∧ hl = I := by
        exact ⟨ hl, Finset.mem_powerset.mpr ( Finset.subset_univ _ ), by simpa using Finset.mem_filter.mp hrl |>.2, rfl ⟩;
      exact hI.2.2.symm ▸ Nat.le_sub_one_of_lt hI.2.1
      -- Since $F$ is a $k_L_p_Family$, $L$ is a finite set of natural numbers. The problem states that $s$ is the cardinality of $L$. If $s$ were zero, then $L$ would be empty, which might not make sense in the context of the problem.
      by_contra h_contra;
      norm_num +zetaDelta at *;
      unfold Constructions.vec_g_Zp at hrl; aesop;

  have h_union : (poly_f ∪ poly_g).card ≤ ∑ j ∈ Finset.range (F.s + 1), Nat.choose n j := by
    sorry

  have h_disjoint : poly_f ∩ poly_g = ∅ := by
    by_contra hh
    change poly_f ∩ poly_g ≠ ∅ at hh
    rw [←Finset.nonempty_iff_ne_empty, Finset.Nonempty] at hh
    obtain ⟨x, hx⟩ := hh
    grw [Finset.mem_inter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    simp_all only [Char_Vec, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one, Decidable.not_not, Finset.powerset_univ,
      Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Finset.mem_union, exists_exists_and_eq_and, vecs_f, vecs_g,
      poly_f, poly_g]
    obtain ⟨w, h_1⟩ := hx1
    obtain ⟨w_1, h_2⟩ := hx2
    obtain ⟨left, right⟩ := h_1
    obtain ⟨left_1, right_1⟩ := h_2
    subst right
    --  Aesop "blow up" end
    obtain ⟨z, hh⟩ := h_poly_f w left
    admit

  have h_card : poly_f.card + poly_g.card = (poly_f ∪ poly_g).card := by
    grw [Finset.card_union, h_disjoint, Finset.card_empty, Nat.sub_zero]

  have h_poly_g_card : poly_g.card = ∑ j ∈ Finset.range (F.s), n.choose j := by
    admit

  have h_poly_f_card : poly_f.card ≤ n.choose F.s := by
    grw [←h_card, h_poly_g_card, Finset.sum_range_succ, Nat.add_comm, Nat.add_le_add_iff_left] at h_union
    assumption

  have h_F_card : F.card = poly_f.card := by
    have hv : F.card = vecs_f.card := by
      unfold vecs_f
      rw [vec_f_Zp, Finset.card_image_of_injective]
      · exact F.card_eq
      · intro i j hij
        ext a
        have := congr_arg (fun f ↦ f.elem a) hij
        simp at this
        -- TODO
        by_cases ha : a ∈ i <;> by_cases hb : a ∈ j <;> simp +decide [ ha, hb ] at this ⊢
    unfold poly_f
    unfold vecs_f
    unfold vec_f_Zp
    rw [Finset.image_image]
    rw [Finset.card_image_of_injective]
    · exact F.card_eq
    · intro i j hij
      clear *- hij
      simp at hij
      ext x
      by_contra!
      cases this <;> expose_names
      · admit
      · obtain ⟨h1, h2⟩ := h
        admit

  grw [h_F_card]
  omega
