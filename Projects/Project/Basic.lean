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
  s_eq : s = L.card
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

def vecs {n : ℕ} (F : k_L_Family n) : Finset (Vec (α := ℚ) n) :=
  (F.elems).image (fun S => Char_Vec S)

def extras {n : ℕ} (s : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.powerset Finset.univ).filter (fun x => x.card < s)

noncomputable def P1_family {n : ℕ} (F : k_L_Family n) : Finset (MvPolynomial (Fin n) ℚ) :=
  (vecs F).image (fun v => MLE (poly_f_Q v F.L))

noncomputable def P2_family {n : ℕ} (F : k_L_Family n) : Finset (MvPolynomial (Fin n) ℚ) :=
  (extras F.s).image (fun i => MLE (poly_g_Q i (F.k : ℚ)))

/-
  This type of thing is used often and should also be moved outside for FW
-/
theorem eval_poly_self {n : ℕ} (F : k_L_Family n) (S : ⟦n⟧) (hS : S ∈ F.elems)
    (hl : ∀ l ∈ F.L, l < F.k) :
    eval (Char_Vec S).elem (poly_f_Q (Char_Vec S) F.L) ≠ 0 := by
      unfold poly_f_Q; simp +decide [ Finset.prod_eq_zero_iff, sub_eq_zero ] ;
      exact fun h => not_le_of_gt ( hl _ h ) ( by simpa using F.k_bounded _ hS |> fun h' => h'.ge )


theorem eval_poly_other {n : ℕ} (F : k_L_Family n) (S T : ⟦n⟧) (hS : S ∈ F.elems) (hT : T ∈ F.elems) (hne : S ≠ T) :
    eval (Char_Vec S).elem (poly_f_Q (Char_Vec T) F.L) = 0 := by
      -- By the properties of the polynomial, if $S \ne T$, then $(\sum v_i x_i - l) = 0$ for some $l \in L$, making the product zero.
      have h_poly_zero : ∃ l ∈ F.L, (Finset.card (S ∩ T)) = l := by
        have := F.L_intersecting S hS T hT hne; aesop;
      simp [poly_f_Q];
      simp_all +decide [ Finset.inter_comm ];
      exact Finset.prod_eq_zero h_poly_zero <| sub_self _

lemma eval_poly2_on_vecs {n : ℕ} (F : k_L_Family n) (i : Finset (Fin n)) (hi : i ∈ extras F.s) (v : Vec n) (hv : v ∈ vecs F) :
    eval v.elem (poly_g_Q i (F.k : ℚ)) = 0 := by
      rcases F with ⟨ F, _ ⟩;
      unfold vecs at hv;
      unfold poly_g_Q; aesop;

-- starting to hit the head on the wall
lemma P1_card_eq {n : ℕ} (F : k_L_Family n) (hl : ∀ l ∈ F.L, l < F.k) :
  (P1_family F).card = F.card := by
    -- Since `vecs F` is the image of `F.elems` under `Char_Vec`, and `Char_Vec` is injective, the cardinality of `vecs F` is equal to the cardinality of `F.elems`.
    have h_vecs_card : (vecs F).card = (F.elems).card := by
      exact Finset.card_image_of_injective _ fun x y hxy => by ext i; replace hxy := congr_fun ( congr_arg Constructions.Vec.elem hxy ) i; aesop;
    -- Since `MLE (poly v F.L)` is unique for each `v` in `vecs F`, the cardinality of `P1_family F` is equal to the cardinality of `vecs F`.
    have h_P1_card : (P1_family F).card = (vecs F).card := by
      apply Finset.card_image_of_injOn;
      intro v hv w hw h_eq;
      -- By the properties of the polynomials and their evaluations, if MLE(poly v F.L) = MLE(poly w F.L), then v and w must be the smae vector.
      have h_eval_eq : ∀ z : (Fin n → ℚ), (∀ i : Fin n, z i = 0 ∨ z i = 1) → eval z (poly_f_Q v F.L) = eval z (poly_f_Q w F.L) := by
        intro z hz; have := MLE_equal_on_boolean_cube ( poly_f_Q v F.L ) z hz; have := MLE_equal_on_boolean_cube ( poly_f_Q w F.L ) z hz; aesop;
      -- Since $v$ and $w$ are char vectors of sets in $F$, and $F$ is a $k$-uniform family, $v$ and $w$ must be distinct sets.
      obtain ⟨S, hS⟩ : ∃ S ∈ F.elems, v = Char_Vec S := by
        unfold vecs at hv; aesop;
      obtain ⟨T, hT⟩ : ∃ T ∈ F.elems, w = Char_Vec T := by
        unfold vecs at hw; aesop;
      have h_distinct : S ≠ T → False := by
        intro hne
        have h_eval_S : eval (Char_Vec S).elem (poly_f_Q (Char_Vec T) F.L) = 0 := by
          apply eval_poly_other F S T hS.left hT.left hne;
        have h_eval_S_nonzero : eval (Char_Vec S).elem (poly_f_Q (Char_Vec S) F.L) ≠ 0 := by
          apply eval_poly_self F S hS.left hl;
        specialize h_eval_eq ( Char_Vec S |> Constructions.Vec.elem ) ; simp_all [ Constructions.vec_dot ] ;
      aesop;
    convert h_P1_card.trans h_vecs_card;
    exact?

-- The main helper Lemmas


theorem fankl_wilson
  {n : ℕ}
  (F : k_L_p_Family n) :
  F.card ≤ ∑ i : Fin (F.s + 1), n.choose i := by

  let p := F.p
  let R := ZMod p

  -- nontriviality
  have : (Nontrivial (ZMod p)) := by
    apply nontrivial_iff.2
    use 0
    use 1
    have : ZMod.val (0 : ZMod p) = 0 := by
      apply ZMod.val_zero
    have : ZMod.val (1 : ZMod p) = 1 := by
      have bound : 1 < p := by
        unfold p
        exact F.p_prime.one_lt
      have := Fact.mk bound
      apply ZMod.val_one
    grind

  -- nozerodiv
  have : (NoZeroDivisors (ZMod p)) := by
    have := F.p_neq_one
    have := F.p_prime
    have := Fact.mk this
    exact inferInstance

    -- set of characteristic vectors
  let vecs : Finset (Vec n) := F.elems.image (fun i ↦ Char_Vec (R := R) i)
  -- set of polynomial corresponding to characteristic vectors
  let P := vecs.image (fun i ↦ MLE (poly_f_Zp i F.L))

  -- the outputs are in {0,1}
  have h_vec : ∀ v ∈ vecs, ∀ i : Fin n, v.elem i = 0 ∨ v.elem i = 1 := by
    intro v hv i
    unfold vecs at hv
    simp_all
    obtain ⟨a, ⟨ahl, ahr⟩⟩ := hv
    subst ahr
    simp
    by_cases h : i ∈ a
    · right
      assumption
    · left
      assumption

  have help : ∀ v ∈ vecs, ∀ w ∈ vecs , v ≠ w → ∃ z : ((Fin n) → R),
    let p := MLE (poly_f_Zp v F.L);
    let q := MLE (poly_f_Zp w F.L);
    (eval z) p = 0 ∧ (eval z) q ≠ 0 := by
    intros v hv w hw hh
    use (fun i ↦ w.elem i)
    intros p q
    constructor
    rename_i p_1 this_1
    simp_all only [ge_iff_le, Char_Vec, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
       ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one, Decidable.not_not, ne_eq, p_1, R, vecs,
       p]
    obtain ⟨w_1, h⟩ := hv
    obtain ⟨w_2, h_1⟩ := hw
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right_1⟩ := h_1
    unfold poly_f_Zp
    grw[<-MLE_equal_on_boolean_cube, eval_prod]
    simp
    grw[Finset.prod_eq_zero_iff]
    use (w_2 ∩ w_1).card % (F.p)
    constructor
    · apply F.L_p_intersecting.right
      assumption
      assumption
      by_contra hw  -- abstractly just show w1 ≠ w2 assuming f w1 ≠ f w2 (done by aesop)
      subst hw
      simp_all only [not_true_eq_false]
    · subst right right_1
      simp
    swap
    rename_i p_1 this_1
    simp_all only [ge_iff_le, Char_Vec, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one, Decidable.not_not, ne_eq, p_1, R, vecs,
      q]
    obtain ⟨w_1, h⟩ := hv
    obtain ⟨w_2, h_1⟩ := hw
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right_1⟩ := h_1
    unfold poly_f_Zp
    subst right right_1
    simp_all only
    grw[<-MLE_equal_on_boolean_cube, eval_prod]
    simp
    grw[Finset.prod_eq_zero_iff]
    push_neg
    intros a ha hh
    have hK := F.k_not a  ha
    have hK2 := F.k_bounded w_2 left_1
    rw[<-hK2] at hK
    rw [sub_eq_zero] at hh
    rw[ZMod.natCast_eq_natCast_iff] at hh
    rw[hh] at hK
    contradiction
    intro i -- annoying should be much much simpler
    simp
    grind
    intro i
    rw[<-right_1]
    simp
    grind

  -- bound the size of the polynomials
  have : P.card ≤ ∑ i ∈ Finset.range (F.s+1), Nat.choose n i := by
    refine total_degree_bound_Zp P ?_ ?_ ?_
    · intro p hp i
      simp [P] at hp
      obtain ⟨a, ⟨hal, har⟩⟩ := hp
      rw [←har]
      apply MLE_degreeOf_le
    · intro p hp
      simp [P] at hp
      obtain ⟨a, ⟨hal, har⟩⟩ := hp
      rw [←har]
      have x := deg_main_Zp (p := F.p) (k := F.s) F.p_prime a F.L (show F.L.card ≤ F.s by simp [F.s_eq])
      exact MLE_totalDegree_non_increasing (R := R) (k := F.s) (poly_f_Zp a F.L) x
    · apply Fintype.linearIndependent_iff.2
      intro h hh j
      unfold P at j
      obtain ⟨a,b,c⟩ := Finset.mem_image.mp j.property
      apply_fun (fun g => eval (a.elem) g) at hh
      simp at hh
      symm
      expose_names
      have : ∑ x ∈ P.attach, h x * (eval a.elem) ↑x = h j * (eval a.elem) j := by
        rw [Finset.sum_eq_single j]
        · intro b hb hbb
          have : (eval a.elem) ↑b = 0 := by
            obtain ⟨a1,b1,c1⟩ := Finset.mem_image.mp b.property
            have : a1 ≠ a := by
              by_contra!
              rw [this] at c1
              rw [c] at c1
              apply hbb
              exact Subtype.eq c1.symm
            rw [←c1]
            expose_names
            have := MLE_equal_on_boolean_cube (poly_f_Zp a1 F.L) a.elem ?_  -- (h_vec a_1)
            · rw [←this]
              -- this is the result from the proof
              /-
                from rcw
                theorem eval_poly_self {n : ℕ} (F : k_L_Family n) (S : ⟦n⟧) (hS : S ∈ F.elems)
                (hl : ∀ l ∈ F.L, l < F.k) :
                    eval (Char_Vec S).elem (poly (Char_Vec S) F.L) ≠ 0 := by
                  unfold Lemmas.poly; simp +decide [ Finset.prod_eq_zero_iff, sub_eq_zero ] ;
                  exact fun h => not_le_of_gt ( hl _ h ) ( by simpa using F.k_bounded _ hS |> fun h' => h'.ge )

              -/
              unfold poly_f_Zp
              simp [Finset.prod_eq_zero_iff, sub_eq_zero]
              obtain ⟨x, hx_mem, hx_eq⟩ := Finset.mem_image.mp b_1
              obtain ⟨x1, hx1_mem, hx1_eq⟩ := Finset.mem_image.mp b1
              rw [←hx1_eq, ←hx_eq]
              rw [←vec_dot]
              have := char_vec_dot_inter (R := R) x1 x
              rw [this]
              use ((x1 ∩ x).card % F.p)
              constructor
              · have x_ne_x1 : x1 ≠ x := by
                  by_contra!
                  rw [this] at hx1_eq
                  rw [hx1_eq] at hx_eq
                  contradiction
                have := F.L_p_intersecting.2 x1 hx1_mem x hx_mem x_ne_x1
                assumption
              · rw [ZMod.natCast_mod]
            · intro i
              apply h_vec
              assumption
          rw [this]
          simp
        · intro a
          expose_names
          unfold P at a
          simp at a
      rw [this] at hh
      apply mul_eq_zero.1 at hh
      cases hh
      · symm
        assumption
      · expose_names
        have : (eval a.elem) j ≠ 0 := by
          rw [←c]
          simp
          have := MLE_equal_on_boolean_cube (poly_f_Zp a F.L) a.elem ?_
          · rw [←this]
            unfold poly_f_Zp
            simp
            rw [←vec_dot]
            obtain ⟨x, hx_mem, hx_eq⟩ := Finset.mem_image.mp b
            rw [←hx_eq]
            rw [char_vec_dot_inter (R := R) x x]
            simp
            push_neg
            rw [Finset.prod_ne_zero_iff]
            intro a ah
            rw [sub_ne_zero]
            have h2 := F.k_bounded x hx_mem
            have h3 := F.k_not a ah
            clear * - h2 h3
            suffices x.card % F.p ≠ a % F.p by
              clear * - this
              intro h
              apply this

              have t1 := ZMod.val_natCast p x.card
              have t2 := ZMod.val_natCast p a
              rw [←t1, ←t2]
              clear * - h
              grind
            by_contra!
            rw [this] at h2
            contradiction
            /-
            class k_L_p_Family (n : ℕ) extends L_p_Family n where
            k : ℕ
            k_bounded : ∀ F ∈ elems, (F.card % p) = k
            k_not : ∀ l ∈ L , (l % p) ≠ k
            -/
            -- apply the cast on the set instead of using it within the expression
          · intro i
            apply h_vec
            assumption
            /-
            simp [Finset.prod_ne_zero_iff, sub_ne_zero]
            obtain ⟨x, hx_mem, hx_eq⟩ := Finset.mem_image.mp b
            rw [←hx_eq, ←vec_dot]
            have := char_vec_dot_inter (R := R) x x
            rw [this]
            rw [show x ∩ x = x by grind]
            have := F.L_p_intersecting.1 x hx_mem
            intro a ah
            -/
        contradiction

  -- as many elements in the family as there are polynomials
  -- we leverage that (Inj, ∘) is a semi-group :cool:
  have hF : Family.card n = P.card := by
    have hv : P.card = vecs.card := by
      unfold P
      rw[Finset.card_image_of_injOn]
      unfold Set.InjOn
      intros x1 hx1 x2 hx2 h
      by_contra hh
      have h := help x1 hx1 x2 hx2 hh
      obtain ⟨z, hz1, hz2⟩ := h
      have h := congr_arg (eval z) h
      simp at h
      rw[h] at hz1
      contradiction
    rw [hv, Finset.card_image_of_injective]
    · exact F.card_eq
    · intro a b hab
      simp at hab
      ext x
      have h_eq := congr_fun hab x
      have : (1 : ZMod p) ≠ 0 := by
        intro h
        have h_val : (1 : ZMod p).val = (0 : ZMod p).val := by rw [h]
        rw [ZMod.val_zero] at h_val
        have : Fact (1 < p) := by
          exact { out := F.p_prime.one_lt }
        rw [ZMod.val_one p] at h_val
        contradiction
      split_ifs at h_eq <;> expose_names
      · grind
      · contradiction
      · have := Eq.symm h_eq
        contradiction
      · grind

  rw [hF]
  simpa only [ Finset.sum_range ] using this

lemma P1_linear_independence_condition {n : ℕ} (F : k_L_Family n)
    (hl : ∀ l ∈ F.L, l < F.k) :
  ∀ v ∈ vecs F, ∃ z : (Fin n → ℚ),
    (eval z (MLE (poly_f_Q v F.L)) ≠ 0) ∧
    (∀ i ∈ extras F.s, eval z (MLE (poly_g_Q i (F.k : ℚ))) = 0) ∧
    (∀ w ∈ vecs F, MLE (poly_f_Q v F.L) ≠ MLE (poly_f_Q w F.L) → eval z (MLE (poly_f_Q w F.L)) = 0) := by
      intro v hv;
      refine' ⟨ v.elem, _, _, _ ⟩;
      · rw [ MvPolynomial.eval_eq' ];
        -- Since $v \in \text{vecs } F$, there exists $S \in F.elems$ such that $v = \text{Char\_Vec } S$.
        obtain ⟨S, hS⟩ : ∃ S ∈ F.elems, v = Char_Vec S := by
          unfold vecs at hv; aesop;
        convert eval_poly_self F S hS.1 hl using 1;
        rw [ MLE_equal_on_boolean_cube ];
        · rw [ MvPolynomial.eval_eq' ];
          rw [ hS.2 ];
        · exact fun i => by unfold Constructions.Char_Vec; by_cases hi : i ∈ S <;> simp +decide [ hi ] ;
      · -- By Lemma 4, we know that $eval v (poly2 i k) = 0$ for any $i \in extras F.s$.
        have h_eval_poly2 : ∀ i ∈ extras F.s, eval v.elem (poly_g_Q i (F.k : ℚ)) = 0 := by
          intro i hi;
          exact?;
        intro i hi;
        convert h_eval_poly2 i hi using 1;
        convert MLE_equal_on_boolean_cube (R := ℚ) _ _;
        rotate_left;
        exact n;
        exact poly_g_Q i ( F.k : ℚ );
        exact v.elem;
        by_cases h : ∀ i : Fin n, v.elem i = 0 ∨ v.elem i = 1 <;> simp +decide [ h ];
        · rw [ eq_comm ];
        · unfold vecs at hv; aesop;
      · intro w hw hne
        obtain ⟨S, hS⟩ : ∃ S ∈ F.elems, v = Char_Vec S := by
          unfold vecs at hv; aesop;
        obtain ⟨T, hT⟩ : ∃ T ∈ F.elems, w = Char_Vec T := by
          unfold vecs at hw; aesop;
        have hST : S ≠ T := by
          aesop;
        convert eval_poly_other F S T hS.1 hT.1 hST using 1;
        rw [ ← MLE_equal_on_boolean_cube ] ; aesop;
        exact fun i => by rw [ hS.2 ] ; exact by unfold Char_Vec; by_cases hi : i ∈ S <;> simp +decide [ hi ] ;


lemma P2_linear_independence_condition {n : ℕ} (F : k_L_Family n)
    (hl : ∀ l ∈ F.L, l < F.k) :
  ∀ i ∈ extras F.s, ∃ z : (Fin n → ℚ),
    (eval z (MLE (poly_g_Q i (F.k : ℚ))) ≠ 0) ∧
    (∀ j ∈ extras F.s, MLE (poly_g_Q i (F.k : ℚ)) ≠ MLE (poly_g_Q j (F.k : ℚ)) ∧ i.card ≤ j.card → eval z (MLE (poly_g_Q j (F.k : ℚ))) = 0) := by
      intro i hi;
      refine' ⟨ fun x => if x ∈ i then 1 else 0, _, _ ⟩;
      · -- By definition of `poly_g_Q`, we know that `eval (Char_Vec i).elem (poly2 i (F.k : ℚ)) ≠ 0`.
        have h_poly2_eval : eval (fun x => if x ∈ i then 1 else 0) (poly_g_Q i (F.k : ℚ)) ≠ 0 := by
          simp_all +decide [ poly_g_Q ];
          rw [ sub_eq_zero ];
          norm_cast;
          -- Since $i \in extras F.s$, we have $i.card < F.s$.
          have h_card_lt_s : i.card < F.s := by
            exact Finset.mem_filter.mp hi |>.2;
          -- Since $F.s \leq F.k$, we have $i.card < F.k$.
          have h_s_le_k : F.s ≤ F.k := by
            have h_s_le_k : F.s ≤ F.L.card := by
              exact F.L_card_eq.le;
            exact h_s_le_k.trans ( le_trans ( Finset.card_le_card fun x hx => Finset.mem_range.mpr ( hl x hx ) ) ( by simpa ) );
          linarith;
        convert h_poly2_eval using 1;
        convert MLE_equal_on_boolean_cube (R := ℚ) _ _;
        rotate_left;
        exact n
        exact poly_g_Q i ( F.k : ℚ );
        exact fun x => if x ∈ i then 1 else 0;
        grind;
      · intro j hj h;
        have h_eval_zero : MvPolynomial.eval (fun x => if x ∈ i then 1 else 0) (poly_g_Q j (F.k : ℚ)) = 0 := by
          by_cases h_cases : j ⊆ i;
          · have := Finset.eq_of_subset_of_card_le h_cases ; aesop;
          · unfold poly_g_Q; simp_all +decide [ Finset.prod_ite ] ;
            exact Or.inr ( Finset.not_subset.mp h_cases );
        convert MLE_equal_on_boolean_cube (R := ℚ) _ _;
        rotate_left;
        exact n
        exact poly_g_Q j ( F.k : ℚ );
        exact fun x => if x ∈ i then 1 else 0;
        grind

lemma P1_P2_disjoint {n : ℕ} (F : k_L_Family n) (hl : ∀ l ∈ F.L, l < F.k) :
  Disjoint (P1_family F) (P2_family F) := by
    -- Assume that $p \in P1_family F \cap P2_family F$.
    by_contra h
    obtain ⟨v, hv⟩ : ∃ v ∈ vecs F, ∃ i ∈ extras F.s, MLE (poly_f_Q v F.L) = MLE (poly_g_Q i (F.k : ℚ)) := by
      unfold P1_family P2_family at h; erw [ Finset.not_disjoint_iff ] at h; aesop;
    -- Let $S$ be a set in $F$ such that $v$ is the characteristic vector of $S$.
    obtain ⟨S, hS⟩ : ∃ S ∈ F.elems, v = Char_Vec S := by
      unfold vecs at hv; aesop;
    have h_eval_S : eval (Char_Vec S).elem (poly_f_Q v F.L) ≠ 0 := by
      convert eval_poly_self F S hS.1 hl using 1;
      rw [ hS.2 ]
    have h_eval_S' : eval (Char_Vec S).elem (poly_g_Q hv.right.choose (F.k : ℚ)) = 0 := by
      apply_rules [ eval_poly2_on_vecs ];
      · exact hv.2.choose_spec.1;
      · aesop;
    have h_eval_S'' : eval (Char_Vec S).elem (MLE (poly_f_Q v F.L)) ≠ 0 ∧ eval (Char_Vec S).elem (MLE (poly_g_Q hv.right.choose (F.k : ℚ))) = 0 := by
      have h_eval_S'' : ∀ p : MvPolynomial (Fin n) ℚ, (∀ i : Fin n, (Char_Vec (R := ℚ) S).elem i = 0 ∨ (Char_Vec (R := ℚ) S).elem i = 1) → eval (Char_Vec (R := ℚ) S).elem p = eval (Char_Vec (R := ℚ) S).elem (MLE p) := by
        exact fun p a ↦ MLE_equal_on_boolean_cube (R := ℚ) p (Char_Vec S).elem a;
      exact ⟨ by rw [ ← h_eval_S'' _ fun i => by unfold Char_Vec; by_cases hi : i ∈ S <;> simp +decide [ hi ] ] ; exact h_eval_S, by rw [ ← h_eval_S'' _ fun i => by unfold Char_Vec; by_cases hi : i ∈ S <;> simp +decide [ hi ] ] ; exact h_eval_S' ⟩;
    exact h_eval_S''.1 ( by rw [ hv.2.choose_spec.2 ] ; exact h_eval_S''.2 )


theorem P1_P2_linear_independent {n : ℕ} (F : k_L_Family n) (hl : ∀ l ∈ F.L, l < F.k) :
    LinearIndependent ℚ (Subtype.val : (↑(P1_family F) ∪ ↑(P2_family F) : Set (MvPolynomial (Fin n) ℚ)) → MvPolynomial (Fin n) ℚ) := by
      by_contra h;
      -- Let $S = P_1 \cup P_2$. Suppose we have a linear combination $\sum_{p \in S} c_p p = 0$.
      obtain ⟨c, hc⟩ : ∃ c : MvPolynomial (Fin n) ℚ → ℚ, (∃ p ∈ P1_family F ∪ P2_family F, c p ≠ 0) ∧ (∑ p ∈ P1_family F ∪ P2_family F, c p • p) = 0 := by
        rw [ Fintype.linearIndependent_iff ] at h;
        norm_num +zetaDelta at *;
        obtain ⟨ c, hc₁, hc₂ ⟩ := h;
        refine' ⟨ fun p => if hp : p ∈ ( P1_family F : Finset ( MvPolynomial ( Fin n ) ℚ ) ) ∪ ( P2_family F : Finset ( MvPolynomial ( Fin n ) ℚ ) ) then c ⟨ p, by simpa using hp ⟩ else 0, _, _ ⟩ <;> simp_all +decide [ Finset.sum_ite ];
        convert hc₁ using 1;
        refine' Finset.sum_bij ( fun x hx => ⟨ x, by aesop ⟩ ) _ _ _ _ <;> aesop;
      -- First, consider $p \in P_1$. By `P1_linear_independence_condition`, there exists a point $z$ where $p(z) \neq 0$ but all other polynomials in $P_1$ and all polynomials in $P_2$ vanish.
      have h_P1 : ∀ p ∈ P1_family F, c p = 0 := by
        -- Fix an arbitrary polynomial $p \in P_1$
        intro p hp
        obtain ⟨z, hz⟩ : ∃ z : (Fin n → ℚ), (eval z p ≠ 0) ∧ (∀ q ∈ P1_family F ∪ P2_family F, q ≠ p → eval z q = 0) := by
          obtain ⟨v, hv⟩ : ∃ v ∈ vecs F, p = MLE (poly_f_Q v F.L) := by
            unfold P1_family at hp; aesop;
          obtain ⟨ z, hz1, hz2, hz3 ⟩ := P1_linear_independence_condition F hl v hv.1;
          use z;
          simp_all +decide [ P1_family, P2_family ];
          rintro q ( ⟨ w, hw, rfl ⟩ | ⟨ i, hi, rfl ⟩ ) hq <;> [ exact hz3 _ hw ( by aesop ) ; exact hz2 _ hi ];
        replace hc := congr_arg ( MvPolynomial.eval z ) hc.2; simp_all +decide [ Finset.sum_eq_single p ] ;
      -- Let $p \in P2_family F$ be a polynomial with non-zero coefficient corresponding to a set $I \in \text{extras}$ with minimal cardinality.
      obtain ⟨I, hI⟩ : ∃ I ∈ extras F.s, c (MLE (poly_g_Q I (F.k : ℚ))) ≠ 0 ∧ ∀ J ∈ extras F.s, J.card < I.card → c (MLE (poly_g_Q J (F.k : ℚ))) = 0 := by
        obtain ⟨I, hI⟩ : ∃ I ∈ extras F.s, c (MLE (poly_g_Q I (F.k : ℚ))) ≠ 0 := by
          obtain ⟨ p, hp₁, hp₂ ⟩ := hc.1; simp_all +decide [ Finset.mem_union, Finset.mem_image ] ;
          rcases hp₁ with ( hp₁ | hp₁ ) <;> [ exact False.elim ( hp₂ ( h_P1 p hp₁ ) ) ; exact by rcases Finset.mem_image.mp hp₁ with ⟨ I, hI₁, rfl ⟩ ; exact ⟨ I, hI₁, hp₂ ⟩ ];
        -- Let $I$ be a set in `extras` with minimal cardinality such that $c (MLE (poly2 I (F.k : ℚ))) ≠ 0$.
        obtain ⟨I, hI_min⟩ : ∃ I ∈ extras F.s, c (MLE (poly_g_Q I (F.k : ℚ))) ≠ 0 ∧ ∀ J ∈ extras F.s, c (MLE (poly_g_Q J (F.k : ℚ))) ≠ 0 → J.card ≥ I.card := by
          have h_min : ∃ m ∈ (Finset.image (fun J => J.card) (Finset.filter (fun J => c (MLE (poly_g_Q J (F.k : ℚ))) ≠ 0) (extras F.s))), ∀ j ∈ (Finset.image (fun J => J.card) (Finset.filter (fun J => c (MLE (poly_g_Q J (F.k : ℚ))) ≠ 0) (extras F.s))), m ≤ j := by
            exact ⟨ Finset.min' _ ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ hI.1, hI.2 ⟩ ) ⟩, Finset.min'_mem _ _, fun j hj => Finset.min'_le _ _ hj ⟩;
          grind;
        exact ⟨ I, hI_min.1, hI_min.2.1, fun J hJ hJ' => Classical.not_not.1 fun hJ'' => not_lt_of_ge ( hI_min.2.2 J hJ hJ'' ) hJ' ⟩;
      -- By `P2_linear_independence_condition`, there exits a point $z$ where $p(z) \neq 0$ but all polynomials in $P_2$ corresponding to sets $J$ with $|I| \le |J|$ (other than $p$ itself) vanish.
      obtain ⟨z, hz⟩ : ∃ z : (Fin n → ℚ), (eval z (MLE (poly_g_Q I (F.k : ℚ))) ≠ 0) ∧ (∀ J ∈ extras F.s, MLE (poly_g_Q I (F.k : ℚ)) ≠ MLE (poly_g_Q J (F.k : ℚ)) ∧ I.card ≤ J.card → eval z (MLE (poly_g_Q J (F.k : ℚ))) = 0) := by
        exact P2_linear_independence_condition F hl I hI.1;
      -- Evaluating the sum at $z$ implies $c_p = 0$ contradiction. That was very well done by me!
      have h_eval : ∑ p ∈ P2_family F, c p * eval z p = 0 := by
        have h_eval : ∑ p ∈ P1_family F ∪ P2_family F, c p * eval z p = 0 := by
          convert congr_arg ( MvPolynomial.eval z ) hc.2 using 1;
          simp +decide [ MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C ];
        rw [ Finset.sum_union ] at h_eval;
        · rw [ Finset.sum_eq_zero ] at h_eval <;> aesop;
        · exact?;
      rw [ Finset.sum_eq_single ( MLE ( poly_g_Q I ( F.k : ℚ ) ) ) ] at h_eval <;> simp_all +decide [ Finset.mem_image ];
      · simp_all +decide [ P2_family ];
        grind;
      · exact Finset.mem_image_of_mem _ hI.1

@[simp]
theorem Ray_Chaudhuri_Wilson
    {n : ℕ}
    (hn : n ≥ 1) -- adding this shouldnt be harmful
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
  let vecs : Finset (Vec n):= (F.elems).image (fun i ↦ Char_Vec (R := ℚ) i)


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

  let P1 := (vecs).image (fun i => MLE (poly_f_Q i F.L))
  let P2 := (extras).image (fun i => MLE (poly_g_Q i F.k))

  --- Needed for Linear Independece (1) / can also use for other shit
  have h_P1 : ∀ v ∈ vecs,  ∃ z : ((Fin n) → ℚ) , ∀ w ∈ vecs, ∀ i ∈ extras,
    let x := MLE (poly_f_Q v F.L);
    let e := MLE (poly_g_Q i F.k);
    (eval z x) ≠ 0 ∧ (eval z e) = 0 ∧
    let y := MLE (poly_f_Q w F.L);
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
      unfold poly_f_Q
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
        unfold poly_g_Q
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
        unfold poly_f_Q
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
    let x := MLE (poly_g_Q i F.k);
    (eval z x) ≠  0 ∧
    let y := MLE (poly_g_Q j F.k);
     x ≠ y ∧ i.card ≤ j.card →  (eval z y) = 0 := by
      intros i hi
      use (fun a ↦ if a ∈ i then 1 else 0)
      intro j hj x
      constructor
      · unfold x poly_g_Q
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
        unfold y poly_g_Q
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
      apply MLE_degreeOf_le
    · all_goals expose_names
      unfold P2 at h
      intro i --aesop clean up start
      simp_all only [Finset.powerset_univ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, extras]
      obtain ⟨w, h⟩ := h
      obtain ⟨left, right⟩ := h
      subst right --aesop clean up end
      apply MLE_degreeOf_le

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
      apply MLE_totalDegree_non_increasing
      apply deg_main_Q -- here need to the Q alternative
      omega

    · all_goals expose_names
      unfold P2 at h_1
      simp_all only [Finset.powerset_univ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, extras]
      obtain ⟨w, h_1⟩ := h_1
      obtain ⟨left, right⟩ := h_1
      subst right
      apply MLE_totalDegree_non_increasing
      apply deg_extra_Q
      exact hn
      omega
      omega

  have h_union : (P1 ∪ P2).card ≤ ∑ j ∈  Finset.range (F.s + 1), Nat.choose n j := by
    apply total_degree_bound_Q
    assumption
    assumption
    convert P1_P2_linear_independent F h;
    · ext; simp [P1, P2, P1_family, P2_family];
      bound;
    · ext; simp [P1, P2, P1_family, P2_family];
      congr!

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
      -- **todo** polish
      -- To prove injectivity, assume two different subsets J and K map to the same polynomial. Then their characteristic vectors must be the same, implying J = K.
      have h_inj : ∀ J K : Finset (Fin n), J ∈ extras → K ∈ extras → (MLE (poly_g_Q J (F.k : ℚ))) = (MLE (poly_g_Q K (F.k : ℚ))) → J = K := by
        intros J K hJ hK h_eq
        have h_char_vec : ∀ f : Fin n → ℚ, (∀ i, f i = 0 ∨ f i = 1) → (MLE (poly_g_Q J (F.k : ℚ))).eval f = (MLE (poly_g_Q K (F.k : ℚ))).eval f := by
          exact fun f hf => h_eq ▸ rfl;
        have h_char_vec_eq : ∀ f : Fin n → ℚ, (∀ i, f i = 0 ∨ f i = 1) → (poly_g_Q J (F.k : ℚ)).eval f = (poly_g_Q K (F.k : ℚ)).eval f := by
          intros f hf;
          convert h_char_vec f hf using 1 <;> rw [ MLE_equal_on_boolean_cube ];
          · exact hf;
          · exact hf;
        -- By choosing f to be the characteristic vector of J, we can show that K must be a subset of J.
        have h_subset_J : K ⊆ J := by
          intro i hi; specialize h_char_vec_eq ( fun j => if j ∈ J then 1 else 0 ) ; simp_all +decide [ Finset.prod_ite, Finset.filter_mem_eq_inter ] ;
          simp_all +decide [ poly_g_Q ];
          contrapose! h_char_vec_eq;
          rw [ Finset.prod_eq_zero hi ] <;> norm_num [ h_char_vec_eq ];
          exact ⟨ fun i => by tauto, sub_ne_zero_of_ne <| mod_cast ne_of_lt <| lt_of_lt_of_le ( Finset.mem_filter.mp hJ |>.2 ) h_sk ⟩;
        have h_subset_K : J ⊆ K := by
          intro i hi; specialize h_char_vec_eq ( fun j => if j ∈ K then 1 else 0 ) ; simp_all +decide [ Finset.subset_iff ] ;
          simp_all +decide [ poly_g_Q ];
          contrapose! h_char_vec_eq;
          -- Since $K$ is a subset of $J$ and $i \in J$ but $i \notin K$, the product $\prod_{j \in J} \mathbf{1}_{j \in K}$ is zero.
          have h_prod_zero : ∏ j ∈ J, (if j ∈ K then 1 else 0 : ℚ) = 0 := by
            rw [ Finset.prod_eq_zero hi ] ; aesop;
          simp_all +decide [ sub_eq_iff_eq_add ];
          exact ⟨ fun i => by tauto, by rw [ eq_sub_iff_add_eq ] ; norm_cast; linarith [ Finset.mem_filter.mp hK ] ⟩;
        exact subset_antisymm h_subset_K h_subset_J;
      exact Finset.card_image_of_injOn fun J hJ K hK hJK => h_inj J K hJ hK hJK
    grw[h_card]
    unfold extras
    -- The set of subsets with cardinality less than s is exactly the union of the sets of subsets with cardinality j for each j from 0 to s-1.
    have h_union : Finset.filter (fun s : Finset (Fin n) => s.card < F.s) (Finset.powerset (Finset.univ : Finset (Fin n))) = Finset.biUnion (Finset.range (F.s)) (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin n))) := by
      ext; simp [Finset.mem_biUnion, Finset.mem_powersetCard];
    rw [ h_union, Finset.card_biUnion ];
    · simp +decide [ Finset.card_univ ];
    · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by rw [ Finset.mem_powersetCard ] at hx₁ hx₂; aesop;

  -- This implies what we want about P1 (using some algebra)
  have h_vec : P1.card ≤ n.choose F.s := by
    grw[<-h_card, h_extra, Finset.sum_range_succ, Nat.add_comm, Nat.add_le_add_iff_left] at h_union
    assumption

  -- Now we just need to show that 𝔽 ≃ P1
  have hF : Family.card n = P1.card := by
    have hv : Family.card n = vecs.card := by
      rw [ Finset.card_image_of_injective ];
      · exact F.card_eq;
      · intro i j hij; ext a; replace hij := congr_arg ( fun f => f.elem a ) hij; aesop;
    rw [ hv, Finset.card_image_of_injective ];
    · convert hv using 1;
      · exact?;
      · convert P1_card_eq F h using 1;
        exact hv.symm;
    · intro i j hij; ext x; replace hij := congr_arg ( fun f => f.elem x ) hij; aesop;
  grw[hF]
  omega

@[simp]
theorem AlonBabaiSuzuki {n : ℕ} (F : k_L_p_Family n) : F.s ≤ F.p - 1 ∧ F.s + F.k ≤ n
  → F.card ≤ n.choose F.s := by
  intro h
  sorry

-- The main result

@[simp]
def Diagonal_Ramsey
    {α : Type*}
    [Fintype α]
    (G : SimpleGraph α)
    [DecidableRel G.Adj]
    (n k : ℕ) : Prop :=
  n = Fintype.card α ∧ (∀ S, ¬G.IsNClique k S) ∧ (∀ T, ¬Gᶜ.IsNClique k T)

@[simp]
def vertices (p : ℕ) : Type :=
  { A : Finset (Fin (p^3)) // A.card = p^2 - 1 }

@[simp]
instance (p : ℕ) : Fintype (vertices p) :=
  Subtype.fintype <| fun A : Finset (Fin (p^3)) ↦ A.card = p^2 - 1

@[simp]
def Explicit_Ramsey_Graph (p : ℕ) : SimpleGraph (vertices p) :=
  {
    Adj := fun A B ↦ (A.val ∩ B.val).card.mod p = p - 1 ∧ A.val ≠ B.val,
    symm := by
      intro V U h
      rw [Finset.inter_comm, ne_comm]
      assumption,
    loopless := by
      intro x
      simp
  }

@[simp]
instance (p : ℕ) : DecidableRel (Explicit_Ramsey_Graph p).Adj := by
  intro a b
  simp
  exact instDecidableAnd

lemma trivial_fact_1 (p : ℕ) (h : p ≥ 2) :  1 + p ≤ p * p := by
  induction' p with p ih
  · contradiction
  · grw [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

lemma trivial_fact_2 {α : Type*} [DecidableEq α] (A B : Finset α) : Finset.card A ≤ (A ∪ B).card := by
  apply Finset.card_mono
  simp

lemma trivial_fact_3 (p : ℕ) (h : p ≥ 2) : (p * p - 1).mod p = p - 1 := by
  apply Nat.mod_eq_iff.2
  right
  constructor
  · grind
  · use p-1
    simp [Nat.mul_sub]
    have eq_1 : p * p ≥ 1 := by simp ; grw [h] ; simp
    have eq_2 : p * p ≥ p := by induction' p <;> simp
    have eq_3 : p ≥ 1 := by grw [h] ; simp
    zify [eq_1, eq_2, eq_3]
    omega

lemma trivial_fact_4 (x p : ℕ) (hp : 1 ≤ p) (hpp: p-1 ≤ x) (h : Nat.ModEq p (p - 1) x) : ∃ a ≥ 1, p*a - 1 = x := by
  have ⟨k, hk⟩ : ∃ k : ℕ, x - (p-1) = p * k := by
    apply Nat.ModEq.dvd at h
    apply dvd_def.1
    zify [hpp]
    assumption
  use k+1
  simp [Nat.mul_add]
  rw [←hk]
  have : x - (p-1) + p ≥ 1 := by
    rw [hk]
    have : p * k ≥ 0 := by simp
    grw [this, hp]
    simp
  zify [this, hpp]
  omega

lemma trivial_fact_5 {α : Type*} [DecidableEq α] (k : ℕ) (A B : Finset α) (h1 : A.card = k) (h2 : B.card = k) (h3 : A ≠ B) : (A ∩ B).card < k := by
  by_cases A ⊆ B <;> expose_names
  · have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨h, h3⟩)
    grw [h1, h2] at this
    grind
  · have : A ∩ B ⊂ A := by
      apply Finset.ssubset_iff_subset_ne.2
      constructor
      · simp
      · simp
        assumption
    have := Finset.card_lt_card this
    rw [h1] at this
    assumption

lemma Prime_geq_2  (p : ℕ) (h : Nat.Prime p) :p ≥  2 := by  {
    cases p
    contradiction
    rename_i p2
    cases p2
    contradiction
    omega
  }

lemma No_clique
  (p : ℕ)
  (hhp : p ≥ 2)
  (hp2 : p > 0)
   (S : Finset { A : Finset (Fin (p ^ 3)) // A.card = p ^ 2 - 1 }) :
  ¬SimpleGraph.IsNClique
    { Adj := fun A B => (A.val ∩ B.val).card % p = p - 1 ∧ A.val ≠ B.val,
      symm := by
        intro V U h1
        rw [Finset.inter_comm, ne_comm]
        assumption,
      loopless := by
        intro x
        simp } ((p ^ 3).choose (p - 1) + 1) S := by
      set n := (p ^ 3).choose (p ^ 2 - 1)
      set k := (p ^ 3).choose (p - 1) + 1
      intro h
      grw[SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff] at h
      obtain ⟨h_clique, h_card⟩ := h

      let L : Finset ℕ := (Finset.range (p - 1)).image (fun i => (i + 1) * p - 1)

      let S_val : Finset (Finset (Fin (p^3))) := S.image Subtype.val

      let hk : ∀ F ∈ S_val, F.card = p^2 - 1 := by
        intro F hF
        grind

      let hL : ∀ F1 ∈ S_val, ∀ F2 ∈ S_val, F1 ≠ F2 → (F1 ∩ F2).card ∈ L := by
        intros F1 f1 F2 f2 hF
        simp_all only [ge_iff_le, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
              ne_eq, Finset.mem_range, S_val, L]
        obtain ⟨w, h⟩ := f1
        obtain ⟨w_1, h_1⟩ := f2
        have hF_inter_1 : (F1 ∩ F2).card.mod p = p - 1 := by -- one should be able to pull this out of the definition (just like for the IS but somehow I cant)
          simp[Set.Pairwise] at h_clique
          specialize h_clique F1 w
          apply h_clique at h
          specialize h F2 w_1
          apply h at h_1
          apply h_1 at hF
          obtain ⟨hh, _ ⟩ := hF
          assumption
        have hF_inter_2 :(F1 ∩ F2).card < p^2 - 1 := by --
          exact trivial_fact_5 (p^2 - 1) F1 F2 w w_1 hF
        have hF_inter_3 : ∃ a ≥ 1, p*a - 1 =  (F1 ∩ F2).card := by
          apply trivial_fact_4
          omega
          by_contra hp3 -- should be simpler
          have hp3 : (F1 ∩ F2).card < p -1 := by omega
          have hp4 : (F1 ∩ F2).card  < p := by omega
          have hp5 : (F1 ∩ F2).card.mod p < p -1 := by
            apply Nat.mod_lt_of_lt
            assumption
          omega
          simp[Nat.ModEq]
          symm
          assumption

        obtain ⟨w_2, h_2⟩ := hF_inter_3
        obtain ⟨h_3, h_2⟩ := h_2
        use (w_2 -1)
        constructor
        grw[<-h_2, Nat.pow_two, <-Nat.add_one_lt_add_one_iff, Nat.sub_add_cancel, Nat.sub_add_cancel, Nat.mul_lt_mul_left hp2] at hF_inter_2
        omega
        have wtf : p ≥ 1 := by omega
        grw[wtf]
        grw[h_3, Nat.mul_one]
        assumption
        grw[Nat.sub_add_cancel, Nat.mul_comm]
        assumption
        assumption


      let fam : k_L_Family (p^3) := by
        refine{
          elems := S_val,
          L := L,
          k := p^2 - 1,
          L_intersecting := hL,
          k_bounded := hk

        }

      have hf : (∀ l ∈ fam.L, l < fam.k) := by -- this should be MUCH easier imo
        intros l h
        dsimp[fam, L] at *
        obtain ⟨i, hi, hl⟩ := Finset.mem_image.mp h
        grw[<-hl]
        simp at hi
        grw[Nat.pow_two, Nat.sub_lt_iff_lt_add, Nat.sub_add_cancel]
        apply Nat.mul_lt_mul_of_pos_right
        omega -- a lot of annoying remainder facts
        assumption
        simp
        omega
        grw[Nat.add_mul]
        omega

      apply Ray_Chaudhuri_Wilson at hf
      dsimp[fam] at hf

      have hL : L.card = p - 1 := by
        have help : L.card = (Finset.range (p-1)).card  := by -- some odd Meta variable issue
          apply Finset.card_image_of_injective
          grw[Function.Injective]
          intros a_1 a_2 ha
          rw [Nat.sub_eq_iff_eq_add, Nat.sub_add_cancel, Nat.add_mul, Nat.add_mul, Nat.add_right_cancel_iff] at ha
          apply Nat.mul_right_cancel hp2 at ha
          assumption
          repeat {
            grw[Nat.add_mul]
            omega
          }
        grw[help]
        exact Finset.card_range (p - 1)
      have hS : S_val.card =  S.card := by
        apply Finset.card_image_of_injective
        exact Subtype.val_injective
      grw[hL, hS, h_card] at hf
      repeat omega
      sorry


lemma No_indset
  (p : ℕ) (hp : Nat.Prime p)
  (hhp : p ≥ 2)
  (hp2 : p > 0)
  (T : Finset { A : Finset (Fin (p ^ 3)) // A.card = p ^ 2 - 1 }) :
  ¬SimpleGraph.IsNIndepSet
      { Adj := fun A B => (A.val ∩ B.val).card % p = p - 1 ∧ A.val ≠ B.val,
        symm := by
          intro V U h1
          rw [Finset.inter_comm, ne_comm]
          assumption,
        loopless := by
          intro x
          simp } ((p ^ 3).choose (p - 1) + 1) T := by
    set n := (p ^ 3).choose (p ^ 2 - 1)
    set k := (p ^ 3).choose (p - 1) + 1
    intro h
    grw[SimpleGraph.isNIndepSet_iff, SimpleGraph.isIndepSet_iff] at h
    obtain ⟨h_ind, h_card⟩ := h
    let L : Finset ℕ := (Finset.univ : Finset (Fin (p-1))).image Fin.val
    let T_val : Finset (Finset (Fin (p^3))) := T.image Subtype.val
    let hk : ∀ F ∈ T_val, F.card.mod p = (p ^ 2 - 1).mod p := by
      intro F hF
      simp_all only [ge_iff_le, gt_iff_lt, not_and, Decidable.not_not, Finset.mem_image, Subtype.exists,
              exists_and_right, exists_eq_right, k, T_val, Set.Pairwise]
      simp at h_ind
      obtain ⟨w, h⟩ := hF
      simp_all only

    let hL : (∀ F ∈ T_val, F.card.mod p ∉ L) ∧ ∀ F1 ∈ T_val, ∀ F2 ∈ T_val, F1 ≠ F2 → (F1 ∩ F2).card.mod p ∈ L:= by
      constructor
      intro F hf
      refine Finset.forall_mem_not_eq'.mp ?_
      intro b hb hn
      simp_all [L, T_val, Finset.mem_image, Set.Pairwise]
      have hF : F.card.mod p = (p-1) := by
        subst hn
        simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, k, T_val, hk]
        obtain ⟨w, h⟩ := hf
        obtain ⟨w_1, h_1⟩ := hb
        grw[Nat.pow_two]
        apply trivial_fact_3 p hhp
      grind only
      intros F1 hF1 F2 hF2 hF
      refine mem_image_univ_iff_mem_range.mpr ?_
      simp_all [ T_val, Set.Pairwise]
      have h_max : (F1 ∩ F2).card.mod p < p := by -- somehow necessary
        apply Nat.mod_lt (F1 ∩ F2).card (by exact hp2)
      have h_uneq : (F1 ∩ F2).card.mod p ≠ p -1 := by
        simp_all only [ne_eq, k]
        obtain ⟨w, h⟩ := hF1
        obtain ⟨w_1, h_1⟩ := hF2
        apply Aesop.BuiltinRules.not_intro -- some AESOP magic
        intro a
        simp_all only [tsub_lt_self_iff, zero_lt_one, and_self]
        apply h_ind
        · exact h
        · exact h_1
        · simp_all only [not_false_eq_true]
        · exact a
      omega
    let fam : k_L_p_Family (p^3) := by
        refine {
          elems := T_val,
          L := L,
          s_eq := by rfl
          k := p^2 - 1,
          k_bounded := by exact hk,
          k_not := by sorry,
          p := p,
          p_prime := hp,
          p_neq_one := by linarith,
          L_p_intersecting := hL
            ,
        }
    have hL : L.card =  p-1 := by
      have help : L.card = (Finset.univ : Finset (Fin (p-1))).card  := by
          apply Finset.card_image_of_injective
          exact Fin.val_injective
      grw[help, Finset.card_univ, Fintype.card_fin]

    have hT : T_val.card =  T.card := by
      apply Finset.card_image_of_injective
      exact Subtype.val_injective

    have hf : T_val.card ≤ (p ^ 3).choose L.card := by
      apply AlonBabaiSuzuki fam
      constructor
      simp_all only [le_refl, k, L, T_val, fam]
      simp_all only [ k, L, T_val, fam] -- this below here is probably a one liner somehow
      apply Nat.le_of_succ_le
      apply  Nat.le_of_succ_le
      simp
      have help : p^3 = p * p * p := by linarith
      grw[Nat.add_comm, Nat.add_assoc, Nat.sub_add_cancel, <-Nat.add_assoc, Nat.add_sub_cancel', Nat.pow_two, help]
      nth_grw 1 [<-Nat.mul_one p]
      grw[<-Nat.mul_add]
      have help2 :  1 + p ≤ p*p :=  by exact trivial_fact_1 p hhp
      grw[help2]
      linarith
      grw[hhp]
      trivial
      grw[Nat.pow_two, hhp]
      trivial
    grw[hL, hT] at hf
    omega

theorem Explicit_Ramsey_Graph_Correctness
    (p : ℕ)
    (hp : p.Prime) :
    let n := (p^3).choose (p^2 - 1)
    let k := ((p^3).choose (p-1) + 1)
    Diagonal_Ramsey (Explicit_Ramsey_Graph p) n k := by
  have h₂ : 2 ≤ p := hp.two_le
  have h₁ : 0 < p := by omega
  intro n k
  simp
  constructor
  · rfl
  · constructor
    · intro S
      dsimp [k]
      exact No_clique p h₂ h₁ S
    · intro T
      dsimp [k]
      exact No_indset p hp h₂ h₁ T
