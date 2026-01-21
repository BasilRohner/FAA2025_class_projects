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

set_option maxHeartbeats 400000000
set_option linter.unusedSimpArgs false

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

noncomputable def poly_f_Zp
    {n p : ℕ}
    (v : Vec (α := ZMod p) n)
    (L : Finset ℕ) :
    MvPolynomial (Fin n) (ZMod p) :=
  ∏ l ∈ L, (∑ i : Fin n, C (v.elem i) * X i - C (l : ZMod p))

noncomputable def poly_g_Zp
    {n p : ℕ}
    (I : Finset (Fin n))
    (k : ZMod p) :
    MvPolynomial (Fin n) (ZMod p) :=
  (∑ i : Fin n, X i - C k) * ∏ i ∈ I, X i

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
