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

lemma nontrivial_Zp
  {p : ℕ}
  (hp : p.Prime) :
  Nontrivial (ZMod p) := by
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

lemma eval_poly_f_Zp_self
    {n : ℕ}
    (F : k_L_p_Family n)
    (S : ⟦n⟧)
    (hS : S ∈ F.elems) :
    eval (Char_Vec (R := ZMod F.p) S).elem (poly_f_Zp (Char_Vec (R := ZMod F.p) S) F.L) ≠ 0 := by
  have := nontrivial_Zp F.p_prime
  have := nozerodiv_Zp F.p_prime
  unfold poly_f_Zp
  simp
  push_neg
  apply Finset.prod_ne_zero_iff.2
  intro a ah
  rw [sub_ne_zero]
  by_contra!
  have h := ZMod.natCast_eq_natCast_iff' S.card a F.p
  apply h.1 at this
  rw [F.k_bounded S hS] at this
  have h' := F.k_not a ah
  symm at this
  contradiction

lemma eval_poly_f_Zp_other
    {n : ℕ}
    (F : k_L_p_Family n)
    (S T : ⟦n⟧)
    (hS : S ∈ F.elems)
    (hT : T ∈ F.elems)
    (hne : S ≠ T) :
    eval (Char_Vec (R := ZMod F.p) S).elem (poly_f_Zp (Char_Vec (R := ZMod F.p) T) F.L) = 0 := by
  have h : ∃ l ∈ F.L, (Finset.card (S ∩ T)).mod F.p = l := by
    have := F.L_p_intersecting.2 S hS T hT hne
    use (S ∩ T).card.mod F.p
  simp [poly_f_Zp]
  obtain ⟨l, hll, hlr⟩ := h
  apply Finset.prod_eq_zero hll
  rw [←hlr]
  have : (S ∩ T).card.mod F.p = (S ∩ T).card % F.p := by
    rfl
  rw [this, ZMod.natCast_mod, Finset.inter_comm]
  simp

/-
lemma eval_poly_g_Zp_self
    {n : ℕ}
    (F : k_L_p_Family n)
    (S : ⟦n⟧) :
    eval (Char_Vec (R := ZMod F.p) S).elem (poly_g_Zp S F.k) ≠ 0 := by
  admit

lemma eval_poly_g_Zp_card_lt
    {n : ℕ}
    (F : k_L_p_Family n)
    (S T : ⟦n⟧)
    (h_card : S.card ≤ T.card)
    (h_ne : ¬(S ⊆ T)) :
    eval (Char_Vec (R := ZMod F.p) S).elem (poly_g_Zp T F.k) = 0 := by
  admit
-/

@[simp]
theorem Test
    {n : ℕ}
    (F : k_L_p_Family n)
    (hn : n ≥ 1) -- adding this shouldnt be harmful
    (hp : F.p.Prime)
    (hL1 : ∀ l ∈ F.L, l < F.p) -- unnecessary but convinient
    (hL2 : ∀ l ∈ F.L, l % F.p ≠ F.s % F.p)
    (hL3 : F.s = F.k % F.p)
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
      v ≠ w → (eval z y) = 0 := by
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
            Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, vecs, extras]
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
        i ≠ j ∧ i.card ≤ j.card →  (eval z y) = 0 := by
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
            grw[hL3] at hi
            have hh: i.card % F.p = F.k % F.p := by
              rw [sub_eq_zero] at ha
              exact
                Eq.symm
                  ((fun a b c ↦ (ZMod.natCast_eq_natCast_iff' a b c).mp) (k_L_p_Family.k n) i.card
                    (L_p_Family.p n) (id (Eq.symm ha)))
            rw[<-hh] at hi
            exact Nat.lt_irrefl _ (lt_of_lt_of_le hi (Nat.mod_le _ _))
            by_contra h
            rw[Finset.prod_eq_zero_iff] at h
            obtain ⟨a, ha1, ha2⟩ := h
            simp[ha1] at ha2
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

    have h_union : (P1 ∪ P2).card ≤ ∑ j ∈  Finset.range (F.s + 1), Nat.choose n j := by
      apply total_degree_bound_Zp (P1 ∪ P2)
      assumption
      assumption
      by_contra h
      obtain ⟨c, hc⟩ : ∃ c : MvPolynomial (Fin n) (ZMod F.p) → (ZMod F.p), (∃ p ∈ P1 ∪ P2, c p ≠ 0) ∧ (∑ p ∈ P1 ∪ P2, c p • p) = 0 := by
        rw [Fintype.linearIndependent_iff] at h
        push_neg at h
        obtain ⟨c, hcl, ⟨i, hi⟩⟩ := h
        let c_ext : MvPolynomial (Fin n) (ZMod F.p) → ZMod F.p :=
          fun p ↦ if h : p ∈ P1 ∪ P2 then c ⟨p, h⟩ else 0
        use c_ext
        constructor
        · use i
          grind
        · rw [←hcl]
          -- **this is opaque**
          rw [←Finset.sum_attach]
          congr 1
          ext ⟨x,hx⟩
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_attach]
          unfold c_ext
          grind

      have h_P1 : ∀ p ∈ P1, c p = 0 := by
        intro p hp
        obtain ⟨z, hz⟩ : ∃ z : (Fin n → ZMod F.p), (eval z p ≠ 0) ∧ (∀ q ∈ P1 ∪ P2, q ≠ p → eval z q = 0) := by
          simp [P1] at hp
          obtain ⟨v, ⟨hvl, hvr⟩⟩ := hp
          use v.elem
          constructor
          · rw [←hvr]
            have := MLE_equal_on_boolean_cube (poly_f_Zp v F.L) v.elem ?_
            · rw [←this]
              simp [vecs] at hvl
              obtain ⟨a, ahl, ahr⟩ := hvl
              rw [←ahr, ←Char_Vec]
              exact eval_poly_f_Zp_self F a ahl
            · intro i
              simp [vecs] at hvl
              obtain ⟨a, ahl, ahr⟩ := hvl
              rw [←ahr]
              grind
          · intro q hq hpq
            simp at hq
            rcases hq with h1 | h2
            · simp [P1] at h1
              obtain ⟨a, hal, har⟩ := h1
              rw [←har]
              simp [vecs] at hal
              obtain ⟨b, hbl, hbr⟩ := hal
              simp [vecs] at hvl
              obtain ⟨c, hcl, hcr⟩ := hvl
              have := MLE_equal_on_boolean_cube (poly_f_Zp a F.L) v.elem ?_
              rw [←this, ←hbr, ←hcr, ←Char_Vec, ←Char_Vec]
              apply eval_poly_f_Zp_other F c b hcl hbl
              by_contra h_contra
              rw [h_contra] at hcr
              rw [hcr] at hbr
              rw [hbr] at hvr
              rw [har] at hvr
              contradiction
              intro i
              rw [←hcr]
              grind
            · simp [P2] at h2
              obtain ⟨a, hal, har⟩ := h2
              simp [extras] at hal
              rw [←har]
              have := MLE_equal_on_boolean_cube (poly_g_Zp a F.k) v.elem ?_
              rw [←this]
              simp [vecs] at hvl
              obtain ⟨b, hbl, hbr⟩ := hvl
              rw [←hbr, ←Char_Vec]
              simp [poly_g_Zp]
              left
              rw [sub_eq_zero]
              have := F.k_bounded b hbl
              rw [ZMod.natCast_eq_natCast_iff']
              assumption
              simp [vecs] at hvl
              obtain ⟨x, hxl, hxr⟩ := hvl
              rw [←hxr]
              grind
        have := congr_arg (eval z) hc.2
        simp at this
        simp_all +decide [Finset.sum_eq_single p]

      obtain ⟨hcl, hcr⟩ := hc
      have h_P2 : ∀ p ∈ P2, c p = 0 := by
        by_contra h_contra
        simp at h_contra
        obtain ⟨wit, hwitl, hwitr⟩ := h_contra
        have ⟨t, ht1, ht2, ht3, ht4⟩ : ∃ t ∈ extras,
          MLE (poly_g_Zp t (F.k : ZMod F.p)) ∈ P2 ∧
          c (poly_g_Zp t F.k |> MLE) ≠ 0 ∧ ∀ s ∈ extras, t ≠ s ∧
          c (poly_g_Zp s F.k |> MLE) ≠ 0 → t.card ≤ s.card := by
          simp [P2, Finset.mem_image] at hwitl
          obtain ⟨a, ahl, ahr⟩ := hwitl
          let witness := extras.filter (fun x ↦ c (MLE (poly_g_Zp x F.k)) ≠ 0)
          have witness_nonempty : witness.Nonempty := by
            use a
            rw [Finset.mem_filter]
            constructor
            · assumption
            · rw [ahr]
              assumption
          have := Finset.exists_min_image witness Finset.card witness_nonempty
          obtain ⟨min_wit, min_wit_hl, min_wit_hr⟩ := this
          use min_wit
          simp [witness] at min_wit_hl
          constructor
          · exact min_wit_hl.1
          · constructor
            · grind
            · constructor
              · exact min_wit_hl.2
              · intro s sh shh
                apply min_wit_hr
                simp [witness]
                constructor
                · assumption
                · exact shh.2
        have := ht4
        apply ht3
        have : ∑ p ∈ P2, c p • p = 0 := by
          rw [Finset.sum_union] at hcr
          have : ∑ p ∈ P1, c p • p = 0 := by
            apply Finset.sum_eq_zero
            intro x hx
            rw [h_P1 x]
            simp
            assumption
          rw [this] at hcr
          simp at hcr
          assumption
          exact Finset.disjoint_iff_inter_eq_empty.mpr h_distinct
        rw [Finset.sum_eq_add_sum_diff_singleton ht2] at this
        apply congr_arg (fun x ↦ eval (Char_Vec t).elem x) at this
        simp at this
        have : ∑ x ∈ P2 \ {poly_g_Zp t F.k |> MLE}, c x * (eval fun i ↦ if i ∈ t then 1 else 0) x = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          simp at hx
          obtain ⟨hx1, hx2⟩ := hx
          simp_all
          by_cases c x = 0
          · left
            assumption
          · right
            simp [P2] at hx1
            obtain ⟨o, oh1, oh2⟩ := hx1
            rw [←oh2]
            have := MLE_equal_on_boolean_cube (poly_g_Zp (p := F.p) o F.k) (fun i ↦ if i ∈ t then 1 else 0) ?_
            · rw [←this]
              simp [poly_g_Zp]
              right
              apply Finset.prod_eq_zero_iff.2
              simp
              by_contra h_contra
              simp at h_contra
              have : o ⊆ t := h_contra
              expose_names
              have t_ne_o : t ≠ o := by
                by_contra h_con
                rw [←h_con] at oh2
                apply hx2
                rw [←oh2]
              rw [←oh2] at h_1
              have := this_3 o oh1 t_ne_o h_1
              have : t = o := by
                expose_names
                have := (Finset.subset_iff_eq_of_card_le this).1 this_7
                symm
                assumption
              contradiction
            · grind
        expose_names
        rw [this] at this_5
        simp at this_5
        cases this_5
        · assumption
        · by_contra h_contra
          expose_names
          have := MLE_equal_on_boolean_cube (poly_g_Zp (p := F.p) t F.k) (fun i ↦ if i ∈ t then 1 else 0) ?_
          rw [←this] at h_1
          simp [poly_g_Zp] at h_1
          rcases h_1 with h_case_11 | h_case_h12
          · rw [sub_eq_zero] at h_case_11
            simp [extras] at ht1
            rw [hL3] at ht1
            have : t.card % F.p < F.k % F.p := by
              rw [Nat.mod_eq_of_lt]
              · exact ht1
              · apply lt_trans ht1
                apply Nat.mod_lt
                exact F.p_prime.pos
            have := ZMod.natCast_eq_natCast_iff' t.card F.k F.p
            expose_names
            apply this.1 at h_case_11
            grind
          · have : ∏ i ∈ t, (if i ∈ t then (1 : ZMod F.p) else 0) = 1 := by
              apply Finset.prod_eq_one
              intro x hx
              simp
              assumption
            rw [this] at h_case_h12
            have : (1 : ZMod F.p) ≠ 0 := one_ne_zero
            contradiction
          · intro i
            grind
      grind

    have h_card : P1.card + P2.card = (P1 ∪ P2).card := by
      grw[Finset.card_union, h_distinct, Finset.card_empty, Nat.sub_zero]


    have h_extra : P2.card = ∑ j ∈  Finset.range (F.s), Nat.choose n j  := by
      clear h_union h_distinct h_max_deg h_MLE h_card --clear some stuff to make it cleaner
      have h_card : P2.card = extras.card := by
        unfold P2
        rw [Finset.card_image_of_injOn]
        unfold Set.InjOn
        intro a1 ha1 a2 ha2 hhh
        by_contra hx
        simp at *
        by_cases hh: a1.card ≤ a2.card -- this is again a wlog. situation where I just do both cases instead
        have hP := h_P2 a1 ha1
        obtain ⟨z, hz ⟩ := hP
        have hz :=  hz a2 ha2
        obtain ⟨h1, h2⟩ := hz
        have h2 := h2 hx hh
        have h :=  congr_arg (eval z) hhh
        rw[h2] at h
        contradiction
        have hh : a2.card ≤ a1.card := by omega
        have hx : a2 ≠ a1 := by grind
        have hP := h_P2 a2 ha2
        obtain ⟨z, hz ⟩ := hP
        have hz :=  hz a1 ha1
        obtain ⟨h1, h2⟩ := hz
        have h2 := h2 hx hh
        have h := congr_arg (eval z) hhh
        rw[h2] at h
        symm at h
        contradiction
      rw[h_card]
      unfold extras
      have h_union : Finset.filter (fun s : Finset (Fin n) => s.card < F.s) (Finset.powerset (Finset.univ : Finset (Fin n))) = Finset.biUnion (Finset.range (F.s)) (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin n))) := by
        ext; simp [Finset.mem_biUnion, Finset.mem_powersetCard];
      rw [ h_union, Finset.card_biUnion ];
      · simp +decide [ Finset.card_univ ];
      · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by rw [ Finset.mem_powersetCard ] at hx₁ hx₂; aesop;


    have h_vec : P1.card ≤ n.choose F.s := by
      grw[<-h_card, h_extra, Finset.sum_range_succ, Nat.add_comm, Nat.add_le_add_iff_left] at h_union
      assumption

    have hF : Family.card n = P1.card := by
      --should be doable by h_P1
      have hv : Family.card n = vecs.card := by
        rw [Finset.card_image_of_injective]
        · exact F.card_eq
        · intro i j hij
          ext a
          apply congr_arg (·.elem a) at hij
          unfold Char_Vec at hij
          clear * - hij
          constructor
          · intro h
            simp [h] at hij
            assumption
          · intro h
            simp [h] at hij
            assumption
      rw [hv, Finset.card_image_of_injective]
      · convert hv using 1
        · symm
          exact F.card_eq
        · clear * -
          unfold P1
          apply Finset.card_image_of_injOn
          intro v hv w hw h_eq
          simp at h_eq
          simp [vecs] at hv hw
          obtain ⟨x, hxl, hxr⟩ := hv
          obtain ⟨y, hyl, hyr⟩ := hw
          suffices x = y by
            rw [this] at hxr
            rw [hxr] at hyr
            assumption
          by_contra!
          rw [←Char_Vec] at hyr
          rw [←Char_Vec] at hxr
          rw [←hxr] at h_eq
          rw [←hyr] at h_eq
          have this1 := MLE_equal_on_boolean_cube (poly_f_Zp w F.L) (Char_Vec x |> Vec.elem) ?_
          have this2 := MLE_equal_on_boolean_cube (poly_f_Zp v F.L) (Char_Vec x |> Vec.elem) ?_
          have h_eval_1 : eval (Char_Vec (R := ZMod F.p) x).elem (poly_f_Zp (Char_Vec y) F.L) = 0 := by
            exact eval_poly_f_Zp_other F x y hxl hyl this
          have h_eval_2 : eval (Char_Vec (R := ZMod F.p) x).elem (poly_f_Zp (Char_Vec x) F.L) ≠ 0 := by
            exact eval_poly_f_Zp_self F x hxl
          suffices (eval (Char_Vec x).elem) (poly_f_Zp (Char_Vec y) F.L) = (eval (Char_Vec x).elem) (poly_f_Zp (Char_Vec x) F.L) by
            rw [h_eval_1] at this
            rw [←this] at h_eval_2
            apply h_eval_2
            rfl
          rw [←hyr] at this1
          rw [←hxr] at this2
          rw [this1, this2, ←h_eq]
          · intro i
            unfold Char_Vec
            by_cases h_case : i ∈ x
            · simp [h_case]
            · simp [h_case]
          · intro i
            unfold Char_Vec
            by_cases h_case : i ∈ x
            · simp [h_case]
            · simp[h_case]
          -- apply congr_arg (fun k ↦ eval (Char_Vec x).elem k) at h_eq
      · intro i j hij
        ext a
        apply congr_arg (·.elem a) at hij
        unfold Char_Vec at hij
        clear * - hij
        constructor
        · intro h
          simp [h] at hij
          assumption
        · intro h
          simp [h] at hij
          assumption

    grw[hF]
    omega
