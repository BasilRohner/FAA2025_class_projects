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

open MvPolynomial

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
