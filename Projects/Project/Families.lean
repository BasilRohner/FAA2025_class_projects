import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
-- File contains definitions of Families

notation "⟦"n"⟧" => Finset (Fin n)

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
  k_bounded : ∀ F ∈ elems, (F.card % p) = (k % p)
  k_not : ∀ l ∈ L , (l % p) ≠ (k % p)
