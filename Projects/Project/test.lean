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

open MvPolynomial

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



noncomputable def poly_f_Zp
    {n p : ℕ}
    (v : Vec (α := ZMod p) n)
    (L : Finset ℕ) :
    MvPolynomial (Fin n) (ZMod p) :=
  ∏ l ∈ L, (∑ i : Fin n, C (v.elem i : ZMod p) * (X i) - C (l : ZMod p))

noncomputable def poly_g_Zp
    {n p : ℕ}
    (I : Finset (Fin n))
    (k : ZMod p) :
    MvPolynomial (Fin n) (ZMod p) :=
  (∑ i : Fin n, X i - C k) * ∏ i ∈ I, X i

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


@[simp]
theorem Test
    {n : ℕ}
    (hn : n ≥ 1) -- adding this shouldnt be harmful
    (F : k_L_p_Family n)
    (hp : F.p.Prime)
    (hL1 : ∀ l ∈ F.L, l < F.p) -- unnecessary but convinient
    (hL2 : ∀ l ∈ F.L, l % F.p ≠ F.s % F.p)
    (hL3 : F.s < F.k % F.p)
    : F.card ≤ n.choose F.s := by

    haveI : Nontrivial (ZMod (L_p_Family.p n)) := nontrivial_Zp hp
    haveI : NoZeroDivisors (ZMod (L_p_Family.p n)) := nozerodiv_Zp hp

    let vecs : Finset (Vec n):= (F.elems).image (fun i ↦ Char_Vec (R := ZMod F.p) i)
    let extras := (Finset.powerset Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card < F.s)

    let P1 := (vecs).image (fun i => MLE (poly_f_Zp i F.L))
    let P2 := (extras).image (fun i => MLE (poly_g_Zp i (F.k : ZMod (L_p_Family.p n)) ) )


    have h_P1 : ∀ v ∈ vecs,  ∃ z : ((Fin n) → (ZMod F.p)) , ∀ w ∈ vecs, ∀ i ∈ extras,
      let x := MLE (poly_f_Zp v F.L);
      let e := MLE (poly_g_Zp i F.k);
      (eval z x) ≠ 0 ∧ (eval z e) = 0 ∧
      let y := MLE (poly_f_Zp w F.L);
      x ≠ y → (eval z y) = 0 := by
      intros v a
      use (fun i ↦ v.elem i)
      intros w hw i hi x e
      constructor
      · simp_all only [Char_Vec, Finset.mem_image, Finset.powerset_univ,
        Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, vecs, extras, x] -- let aesop clean up some expressions
        obtain ⟨w_1, h_1⟩ := a
        obtain ⟨w_2, h_2⟩ := hw
        obtain ⟨left, right⟩ := h_1
        obtain ⟨left_1, right_1⟩ := h_2
        subst right right_1
        simp_all only  --aesop end
        unfold poly_f_Zp
        grw[<-MLE_equal_on_boolean_cube, eval_prod]
        simp
        grw[Finset.prod_eq_zero_iff] -- only 0 if one term is 0 => |w_1| ∈ L contradiction
        simp
        intro l hl hh
        rw [sub_eq_zero] at hh
        have := F.k_not l hl
        rw [←F.k_bounded w_1 left] at this
        rw [←ZMod.val_natCast] at this
        rw [←ZMod.val_natCast] at this
        symm at hh
        rw[hh] at this
        contradiction
        · intro i
          by_cases h_case : i ∈ w_1
          · right
            grind
          · left
            grind
      · constructor
        · unfold e
          grw[<-MLE_equal_on_boolean_cube]
          unfold poly_g_Zp
          grw[eval_mul]
          simp
          left
          -- AESOP blow up
          simp_all only [Char_Vec, Finset.mem_image,
            Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and, vecs, extras]
          obtain ⟨w_1, h_1⟩ := a
          obtain ⟨w_2, h_2⟩ := hw
          obtain ⟨left, right⟩ := h_1
          obtain ⟨left_1, right_1⟩ := h_2
          subst right right_1
          simp_all only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [sub_eq_zero] -- easy
          have := F.k_bounded w_1 left
          rw [ZMod.natCast_eq_natCast_iff']
          assumption
          -- rw [this]
          simp [vecs] at a
          obtain ⟨a, ahl, ahr⟩ := a
          rw [←ahr]
          simp
          intro i
          by_cases i ∈ a
          · right
            assumption
          · left
            assumption
        · intros y hx
          unfold y
          grw[<-MLE_equal_on_boolean_cube]
          unfold poly_f_Zp
          simp
          simp_all only [Char_Vec, Finset.mem_image,
            Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, vecs, extras, x, y]
          obtain ⟨w_1, h_1⟩ := a
          obtain ⟨w_2, h_2⟩ := hw
          obtain ⟨left, right⟩ := h_1
          obtain ⟨left_1, right_1⟩ := h_2
          subst right right_1
          simp_all only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
            nsmul_eq_mul]
          grw[Finset.prod_eq_zero_iff] -- one term is 0, as w_1 ≠ w_2 and hence w_1 ∩ w_2 ∈ L
          -- use  (Nat.cast (w_1 ∩ w_2).card)
          use ((w_1 ∩ w_2).card % F.p)
          constructor
          have := F.L_p_intersecting.2 w_1 left w_2 left_1
          apply this
          by_contra!
          apply hx
          rw [this]
          simp
          simp [vecs] at a
          obtain ⟨a, ahl, ahr⟩ := a
          rw [←ahr]
          simp
          intro i
          by_cases i ∈ a
          · right
            assumption
          · left
            assumption

    have h_P2 : ∀ i ∈ extras, ∃ z : ((Fin n) → ZMod F.p), ∀ j ∈ extras,
        let x := MLE (poly_g_Zp i F.k);
        (eval z x) ≠  0 ∧
        let y := MLE (poly_g_Zp j F.k);
        x ≠ y ∧ i.card ≤ j.card →  (eval z y) = 0 := by
          intros i hi
          use (fun a ↦ if a ∈ i then 1 else 0)
          intro j hj x
          constructor
          · unfold x poly_g_Zp
            grw[<-MLE_equal_on_boolean_cube]
            simp
            constructor
            push_neg
            by_contra ha
            simp [extras] at hi
            have := lt_trans hi hL3
            rw [sub_eq_zero] at ha
            rw [←ZMod.val_natCast] at this
            rw [←ha] at this
            rw [ZMod.val_natCast] at this
            have h_le := Nat.mod_le i.card F.p
            linarith
            intro h
            simp [extras] at hi
            sorry -- I'm not sure this can be shown
            intro i_1
            by_cases h_case : i_1 ∈ i
            · right
              grind
            · left
              grind
          · intro y hh
            unfold y poly_g_Zp
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

    have h_max_deg : ∀ poly ∈ P1 ∪ P2, poly.totalDegree ≤ F.s := by
      have hL : (F.L).card = F.s := by
        have := F.s_eq
        symm
        assumption
      grw[<-hL]
      intros pq hpq
      grw[Finset.mem_union] at hpq
      cases hpq
      · all_goals expose_names
        unfold P1 at h
        simp_all only [Char_Vec, Finset.mem_image, exists_exists_and_eq_and, vecs]
        obtain ⟨w, h⟩ := h
        obtain ⟨left, right⟩ := h
        subst right
        apply MLE_totalDegree_non_increasing
        apply deg_main_Zp
        omega
        simp_all
      · all_goals expose_names
        unfold P2 at h
        simp_all only [Finset.powerset_univ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, extras]
        obtain ⟨w, h⟩ := h
        obtain ⟨left, right⟩ := h
        subst right
        apply MLE_totalDegree_non_increasing
        apply deg_extra_Zp
        exact hp
        omega
        omega
        omega

    have h_union : (P1 ∪ P2).card ≤ ∑ j ∈  Finset.range (F.s + 1), Nat.choose n j := by
      apply total_degree_bound_Zp
      assumption
      assumption
      rw [linearIndependent_iff']
      clear * -
      intro s g h j hj
      rw [Finset.sum_eq_add_sum_diff_singleton hj (fun x ↦ g x • (x : MvPolynomial (Fin n) (ZMod F.p)))] at h
      sorry

    have h_distinct : P1 ∩ P2 = ∅  := by
      by_contra hh
      change P1 ∩ P2 ≠ ∅ at hh
      rw [← Finset.nonempty_iff_ne_empty, Finset.Nonempty] at hh
      obtain ⟨x, hx⟩ := hh
      grw[Finset.mem_inter] at hx
      obtain ⟨hx1, hx2⟩ := hx
      -- Again some Aesop "blow up"
      simp_all only [Char_Vec, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Finset.powerset_univ,
        Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Finset.mem_union, exists_exists_and_eq_and, vecs, extras,
        P1, P2]
      obtain ⟨w, h_1⟩ := hx1
      obtain ⟨w_1, h_2⟩ := hx2
      obtain ⟨left, right⟩ := h_1
      obtain ⟨left_1, right_1⟩ := h_2
      subst right
      --  Aesop "blow up" end
      obtain ⟨z, hh ⟩ := h_P1 w left
      grind

    have h_card : P1.card + P2.card = (P1 ∪ P2).card := by
      grw[Finset.card_union,h_distinct, Finset.card_empty, Nat.sub_zero]


    have h_extra : P2.card = ∑ j ∈  Finset.range (F.s), Nat.choose n j  := by
      -- should be doable by h_P2
      sorry

    have h_vec : P1.card ≤ n.choose F.s := by
      grw[<-h_card, h_extra, Finset.sum_range_succ, Nat.add_comm, Nat.add_le_add_iff_left] at h_union
      assumption

    have hF : Family.card n = P1.card := by
      --should be doable by h_P1
      sorry

    grw[hF]
    omega
