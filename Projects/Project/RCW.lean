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
import Projects.Project.Families
import Projects.Project.MLE

set_option maxHeartbeats 400000000 -- Sadly needed
set_option linter.unusedSimpArgs false
open MvPolynomial

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

noncomputable def poly_f_Q
    {n : ℕ}
    (v : Vec (α := ℚ) n)
    (L : Finset ℕ) :
    MvPolynomial (Fin n) ℚ :=
  ∏ l ∈ L, (∑ i : Fin n, C (v.elem i) * X i - C (l : ℚ))

noncomputable def poly_g_Q
    {n : ℕ}
    (I : Finset (Fin n))
    (k : ℚ) :
    MvPolynomial (Fin n) ℚ :=
  (∑ i : Fin n, X i - C k) * ∏ i ∈ I, X i

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

def vecs {n : ℕ} (F : k_L_Family n) : Finset (Vec (α := ℚ) n) :=
  (F.elems).image (fun S => Char_Vec S)

def extras {n : ℕ} (s : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.powerset Finset.univ).filter (fun x => x.card < s)

noncomputable def P1_family {n : ℕ} (F : k_L_Family n) : Finset (MvPolynomial (Fin n) ℚ) :=
  (vecs F).image (fun v => MLE (poly_f_Q v F.L))

noncomputable def P2_family {n : ℕ} (F : k_L_Family n) : Finset (MvPolynomial (Fin n) ℚ) :=
  (extras F.s).image (fun i => MLE (poly_g_Q i (F.k : ℚ)))

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

lemma P1_card_eq {n : ℕ} (F : k_L_Family n) (hl : ∀ l ∈ F.L, l < F.k) :
  (P1_family F).card = F.card := by
    -- Since `vecs F` is the image of `F.elems` under `Char_Vec`, and `Char_Vec` is injective, the cardinality of `vecs F` is equal to the cardinality of `F.elems`.
    have h_vecs_card : (vecs F).card = (F.elems).card := by
      exact Finset.card_image_of_injective _ fun x y hxy => by ext i; replace hxy := congr_fun ( congr_arg Vec.elem hxy ) i; aesop;
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
        specialize h_eval_eq ( Char_Vec S |> Vec.elem ) ; simp_all [vec_dot ] ;
      aesop;
    convert h_P1_card.trans h_vecs_card;
    exact?

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
        · exact fun i => by unfold Char_Vec; by_cases hi : i ∈ S <;> simp +decide [ hi ] ;
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
        · exact P1_P2_disjoint F hl;
      rw [ Finset.sum_eq_single ( MLE ( poly_g_Q I ( F.k : ℚ ) ) ) ] at h_eval <;> simp_all +decide [ Finset.mem_image ];
      · simp_all +decide [ P2_family ];
        grind;
      · exact Finset.mem_image_of_mem _ hI.1

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
