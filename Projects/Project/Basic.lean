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
  (hL : ∀ F1 ∈ elems, ∀ F2 ∈ elems, F1 ≠ F2 → (F1 ∩ F2).card ∈ L)
  (hk : ∀ F ∈ elems, F.card = k) :
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
  k_bounded : ∀ F ∈ elems, F.card = k

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
theorem Alon_Babai_Suzuki {n : ℕ} (F : k_L_p_Family n) :
  (∀ U ∈ F.elems, U.card.mod F.p = F.k) ∧ F.k.mod F.p ∉ F.L ∧ F.s ≤ F.p - 1 ∧ F.s + F.k ≤ n
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


theorem Explicit_Ramsey_Graph_Correctness (p : ℕ) (hp : p.Prime) :
    Diagonal_Ramsey (Explicit_Ramsey_Graph p) ((p^3).choose (p^2 - 1)) ((p^3).choose (p-1) + 1) := by
  set n := (p^3).choose (p^2 - 1)
  set k := ((p^3).choose (p-1) + 1)
  have hhp : p ≥  2 := by  { -- Very ugly
    cases p
    contradiction
    rename_i p2
    cases p2
    contradiction
    omega
  }
  have hp2 : p > 0 := by omega -- makes a few things easier
  simp
  constructor
  · rfl
  · constructor
    · intro S h
      grw[SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff] at h
      obtain ⟨h_clique, h_card⟩ := h
      let L : Finset ℕ := (Finset.range (p - 1)).image (fun i => (i + 1) * p - 1)
      let S_val : Finset (Finset (Fin (p^3))) := S.image Subtype.val
      let fam : Families.k_L_Family (p^3) := by
        refine{
          elems := S_val,
          L := L,
          k := p^2 - 1,
          L_intersecting := by
            intros F1 f1 F2 f2 hF
            simp at h_clique
            sorry
          k_bounded := by
            intro F hF
            grind
        }
      have hf : (∀ l ∈ fam.L, l < fam.k) := by -- this should be MUCH easier imo
        intros l h
        dsimp[fam, L] at *
        obtain ⟨i, hi, hl⟩ := Finset.mem_image.mp h
        grw[<-hl]
        simp at hi


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
      grw[hL, hS] at hf
      omega


    · intros T h
      grw[SimpleGraph.isNIndepSet_iff, SimpleGraph.isIndepSet_iff] at h
      obtain ⟨h_ind, h_card⟩ := h
      let L : Finset ℕ := (Finset.univ : Finset (Fin (p-1))).image Fin.val
      let T_val : Finset (Finset (Fin (p^3))) := T.image Subtype.val
      let fam : Families.k_L_p_Family (p^3) := by
        refine{
          elems := T_val,
          L := L,
          k := p^2 - 1,
          L_p_intersecting := by
            sorry,
          k_bounded := by
            intro F hF
            grind,
          p := p,
          p_prime := hp,
          p_neq_one := by
            linarith
        }
      have hf : T_val.card ≤ (p ^ 3).choose L.card := by
        apply Lemmas.Alon_Babai_Suzuki fam
        constructor
        sorry
        constructor
        sorry
        constructor
        sorry
        sorry
      have hL : L.card =  p-1 := by
        have help : L.card = (Finset.univ : Finset (Fin (p-1))).card  := by
          apply Finset.card_image_of_injective
          exact Fin.val_injective
        grw[help, Finset.card_univ, Fintype.card_fin]
      have hT : T_val.card =  T.card := by
        apply Finset.card_image_of_injective
        exact Subtype.val_injective
      grw[hL, hT] at hf
      omega
end Result
