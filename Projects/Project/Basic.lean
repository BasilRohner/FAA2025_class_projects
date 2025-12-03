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

-- set_option diagnostics true

set_option maxHeartbeats 400000

notation "⟦"n"⟧" => Finset (Fin n)

namespace Families

class Family (n : ℕ) where
  elems : Finset ⟦n⟧
  card := elems.card

class L_Family (n : ℕ) extends Family n where
  L : Finset ℕ
  s := L.card
  L_intersecting : ∀ F1 ∈ elems, ∀ F2 ∈ elems, F1 ≠ F2 → (F1 ∩ F2).card ∈ L

class k_L_Family (n : ℕ) extends L_Family n where
  k : ℕ
  k_bounded : ∀ F ∈ elems, F.card = k

-- Constructor for k_L_Family
def mk_k_L_Family {n : ℕ}
  (elems : Finset ⟦n⟧)
  (L : Finset ℕ)
  (k : ℕ)
  (hk : ∀ F ∈ elems, F.card = k)
  (hL : ∀ F1 ∈ elems, ∀ F2 ∈ elems, F1 ≠ F2 → (F1 ∩ F2).card ∈ L) :
  k_L_Family n :=
{ elems := elems,
  L := L,
  k := k,
  L_intersecting := hL,
  k_bounded := hk }


class L_p_Family (n : ℕ) extends Family n where
  L : Finset ℕ
  s := L.card
  p : ℕ
  p_prime : p.Prime
  p_neq_one : p ≠ 1
  L_p_intersecting :
    (∀ F ∈ elems, F.card.mod p ∉ L) ∧
    (∀ F1 ∈ elems, ∀ F2 ∈ elems, F1 ≠ F2 → (F1 ∩ F2).card.mod p ∈ L)

class k_L_p_Family (n : ℕ) extends L_p_Family n where
  k : ℕ
  k_bounded : ∀ F ∈ elems, (F.card.mod p) = (k.mod p)

end Families

namespace Polynomials

-- add MLE polynomial results

end Polynomials

namespace Constructions

class Vec {α : Type*} (n : ℕ) where
  elem : Fin n → α

@[simp]
instance Char_Vec {R : Type*} [Semiring R] {n : ℕ} (S : ⟦n⟧) : @Vec R n where
  elem := fun i ↦ if i ∈ S then (1 : R) else (0 : R)

@[simp]
def vec_dot {R : Type*} [Semiring R] {n : ℕ} (v w : @Vec R n) : R :=
  ∑ i : Fin n, v.elem i * w.elem i

@[simp]
theorem char_vec_dot_inter {n : ℕ} (U W : ⟦n⟧) : vec_dot (Char_Vec U) (Char_Vec W) = (U ∩ W).card := by
  simp [Char_Vec, vec_dot, Finset.inter_comm]

end Constructions

namespace Lemmas

open Families
open Constructions

@[simp]
def f {n : ℕ} (F : L_p_Family n) (U V : ⟦n⟧) : ZMod F.p :=
  ∏ l ∈ F.L, (vec_dot (@Char_Vec (ZMod F.p) (by exact CommRing.toCommSemiring.toSemiring) n V) (@Char_Vec (ZMod F.p) (by exact CommRing.toCommSemiring.toSemiring) n U) - (l : ZMod F.p))

@[simp]
theorem Frankl_Wilson {n : ℕ} (F : L_p_Family n) : F.card ≤ ∑ i ∈ Finset.range (F.L.card + 1), n.choose i := by
  have : ∀ U ∈ F.elems, ∀ V ∈ F.elems, U ≠ V → f F U V = 0 := by
    intro U Uh V Vh UV
    simp [f, Char_Vec, vec_dot]
    have := F.L_p_intersecting.2 U Uh V Vh UV
    -- show that ZMod F.p is non-trivial
    have : Nontrivial (ZMod F.p) := by
      apply ZMod.nontrivial_iff.2
      exact F.p_neq_one
    -- show that ZMod F.p has no zero-divisors
    have : NoZeroDivisors (ZMod (L_p_Family.p n)) := by
      sorry
      /-
        ℤ/pℤ has no zero-divisors for p ∈ ℙ.
        Assume towrads a contradiction a,b ∈ ℤ/pℤ ∖ {0} and a · b = 0
        Then a · b = p and 1 ≤ a,b < p. This clearly doesn't work with primality of p. ∎
        Unsure how to bring this to lean tho...
      -/
    apply Finset.prod_eq_zero_iff.2
    use (U ∩ V).card.mod (F.p)
    constructor
    · assumption
    · sorry -- this is trivial but need to equate the coercion in ℤ/pℤ to modular reduction with p
  -- show that f is equivalent to a MLE on the hypercube
  -- bound the number of orthogonal possible MLE in n variables by the sum
  sorry
  -- might not be that much more effort for this simple lemma even

@[simp]
theorem Ray_Chaudhuri_Wilson {n : ℕ} (F : k_L_Family n) : (∀ l ∈ F.L, l < F.k) → F.card ≤ n.choose F.s := by
  intro h
  -- very similar to the above
  sorry

@[simp]
theorem Alon_Babai_Suzuki {n : ℕ} (F : k_L_p_Family n) : F.s ≤ F.p - 1 ∧ F.s + F.k ≤ n
  → F.card ≤ n.choose F.s := by
  intro h
  obtain ⟨h1, h2, h3⟩ := h
  sorry

end Lemmas

namespace Graph

@[simp]
def Diagonal_Ramsey {α : Type*} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] (n k : ℕ) : Prop :=
  n = Fintype.card α
  ∧ (∀ S, ¬G.IsNClique k S)
  ∧ (∀ T, ¬Gᶜ.IsNClique k T)

end Graph

namespace Result

open Graph
open Set

@[simp]
def  vertices (p : ℕ) : Type :=
  { A : Finset (Fin (p^3)) // A.card = p^2 - 1 }

@[simp]
instance (p : ℕ) : Fintype (vertices p) :=
  Subtype.fintype (fun A : Finset (Fin (p^3)) => A.card = p^2 - 1)

@[simp]
def Explicit_Ramsey_Graph (p : ℕ) : SimpleGraph (vertices p) :=
  {
    Adj := fun A B => (A.val ∩ B.val).card.mod p = p - 1 ∧ A.val ≠ B.val,
    symm := by
      intro V U h1
      rw [Finset.inter_comm, ne_comm]
      assumption
    ,
    loopless := by
      intro x
      simp
  }

@[simp]
instance (p : ℕ) : DecidableRel (Explicit_Ramsey_Graph p).Adj := by
  intro a b
  simp [Explicit_Ramsey_Graph]
  exact instDecidableAnd



lemma trivial_fact_1 (p : ℕ) (h : p ≥ 2) :  1 + p ≤ p*p := by
  induction' p with p2 hp
  contradiction
  grw[Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

lemma trivial_fact_2 {α : Type*} [DecidableEq α] (A B :Finset α ) : Finset.card A ≤ (A ∪ B).card  := by
    have hS : A ⊆ A ∪ B := by simp_all only [Finset.subset_union_left]
    apply Finset.card_mono
    simp_all only [Finset.subset_union_left, Finset.le_eq_subset] -- whatever this is

lemma trivial_fact_3 (p : ℕ) (h : p ≥  2) : (p * p - 1).mod p = p - 1 := by
  sorry

lemma trivial_fact_4 (x p : ℕ) (h : (x).mod p = p - 1) : ∃ a ≥ 1, p*a -1 = x  := by
  sorry

lemma trivial_fact_5 {α : Type*} [DecidableEq α] (k : ℕ) (A B :Finset α ) (h1 : A.card = k) (h2 : B.card = k) (h3 : A ≠ B) : (A ∩ B).card < k := by
  sorry

lemma Prime_geq_2  (p : ℕ) (h : Nat.Prime p) :p ≥  2 := by  {
    cases p
    contradiction
    rename_i p2
    cases p2
    contradiction
    omega
  }

lemma No_clique
  (p : ℕ) (hp : Nat.Prime p)
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
        have hF_inter_1 : (F1 ∩ F2).card.mod p = p - 1 := by -- you should be able to pull this out of the definition imo
          sorry
        have hF_inter_2 :(F1 ∩ F2).card < p^2 - 1 := by --
          exact trivial_fact_5 (p^2 - 1) F1 F2 w w_1 hF
        apply trivial_fact_4 at hF_inter_1
        obtain ⟨w_2, h_2⟩ := hF_inter_1
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







      let fam : Families.k_L_Family (p^3) := by
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

      apply Lemmas.Ray_Chaudhuri_Wilson at hf
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
      omega


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
    let fam : Families.k_L_p_Family (p^3) := by
        refine{
          elems := T_val,
          L := L,
          k := p^2 - 1,
          k_bounded := hk,
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
      apply Lemmas.Alon_Babai_Suzuki fam
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

theorem Explicit_Ramsey_Graph_Correctness (p : ℕ) (hp : p.Prime) :
    Diagonal_Ramsey (Explicit_Ramsey_Graph p) ((p^3).choose (p^2 - 1)) ((p^3).choose (p-1) + 1) := by
  set n := (p^3).choose (p^2 - 1)
  set k := ((p^3).choose (p-1) + 1)
  have hhp : p ≥ 2 := by exact Prime_geq_2 p hp
  have hp2 : p > 0 := by omega -- makes a few things easier
  simp
  constructor
  · rfl
  · constructor
    · intro S
      dsimp[k]
      exact No_clique p hp hhp hp2 S

    · intros T
      dsimp[k]
      exact No_indset p hp hhp hp2 T
end Result
