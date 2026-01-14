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
import Projects.Project.Families
import Projects.Project.MLE
import Projects.Project.RCW
import Projects.Project.ABS

set_option maxHeartbeats 400000000
-- The main result
set_option linter.unusedSimpArgs false

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
    Adj := fun A B ↦ (A.val ∩ B.val).card %p = p - 1 ∧ A.val ≠ B.val,
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

lemma trivial_fact_0 (p : ℕ) (h : p > 0) :  1 ≤ p^3 := by
  have hh : p ≥ 1 := by omega
  have h : 3 = 1 + 1 + 1 := by omega
  rw[h, Nat.pow_add, Nat.pow_add, Nat.pow_one]
  grw[hh]

lemma trivial_fact_1 (p : ℕ) (h : p ≥ 2) :  1 + p ≤ p * p := by
  induction' p with p ih
  · contradiction
  · grw [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

lemma trivial_fact_2 {α : Type*} [DecidableEq α] (A B : Finset α) : Finset.card A ≤ (A ∪ B).card := by
  apply Finset.card_mono
  simp

 lemma trivial_fact_3 (p : ℕ) (h : p ≥ 2) : (p * p - 1) %p = p - 1 := by
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
        have hF_inter_1 : (F1 ∩ F2).card %p = p - 1 := by -- one should be able to pull this out of the definition (just like for the IS but somehow I cant)
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
          have hp5 : (F1 ∩ F2).card %p < p -1 := by
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
      exact trivial_fact_0 p hhp

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
    let hk : ∀ F ∈ T_val, F.card %p = (p ^ 2 - 1) %p := by
      intro F hF
      simp_all only [ge_iff_le, gt_iff_lt, not_and, Decidable.not_not, Finset.mem_image, Subtype.exists,
              exists_and_right, exists_eq_right, k, T_val, Set.Pairwise]
      simp at h_ind
      obtain ⟨w, h⟩ := hF
      simp_all only

    let hL : (∀ F ∈ T_val, F.card %p ∉ L) ∧ ∀ F1 ∈ T_val, ∀ F2 ∈ T_val, F1 ≠ F2 → (F1 ∩ F2).card %p ∈ L:= by
      constructor
      intro F hf
      refine Finset.forall_mem_not_eq'.mp ?_
      intro b hb hn
      simp_all [L, T_val, Finset.mem_image, Set.Pairwise]
      have hF : F.card %p = (p-1) := by
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
      have h_max : (F1 ∩ F2).card %p < p := by -- somehow necessary
        apply Nat.mod_lt (F1 ∩ F2).card (by exact hp2)
      have h_uneq : (F1 ∩ F2).card %p ≠ p -1 := by
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
