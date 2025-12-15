import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Set.Basic

open scoped Classical

/-!
# The 5/8 Theorem on Group Commutativity

This file formalizes the theorem stating that for a finite group G, 
if the probability that two randomly chosen elements commute is greater than 5/8, 
then G must be abelian. It also demonstrates that D₈ achieves exactly 5/8.

## Main definitions
* `commutingProbability G`: The ratio of commuting pairs to |G|².

## Main results
* `commutingProbability_dihedral_four`: The probability for D₈ is 5/8.
* `abelian_of_commutingProbability_gt_five_eighths`: The main theorem.
-/

open Fintype BigOperators

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The number of pairs (x, y) in G × G such that xy = yx. -/
def commutingPairsCount (G : Type*) [Group G] [Fintype G] [DecidableEq G] : ℕ :=
  (Finset.univ.filter (fun x : G × G => x.1 * x.2 = x.2 * x.1)).card

/-- The probability that two random elements in G commute. -/
def commutingProbability (G : Type*) [Group G] [Fintype G] [DecidableEq G] : ℚ :=
  (commutingPairsCount G) / ((card G) ^ 2 : ℚ)

namespace FrontierMath

/-- 
Task 1: Calculate the commuting probability for the Dihedral group D₈ (order 8).
Verify it equals exactly 5/8.
-/
theorem commutingProbability_dihedral_four : 
  commutingProbability (DihedralGroup 4) = 5/8 := by
  native_decide

lemma card_commutingPairs_eq_sum_card_centralizer :
  commutingPairsCount G = ∑ x : G, Nat.card (Subgroup.centralizer {x}) := by
  simp only [commutingPairsCount]
  rw [← Fintype.card_coe]
  rw [← Nat.card_eq_fintype_card]
  trans Nat.card ((x : G) × Subgroup.centralizer {x})
  · apply Nat.card_congr
    refine Equiv.mk (fun ⟨⟨a, b⟩, h⟩ => ⟨a, ⟨b, by
        rw [Subgroup.mem_centralizer_iff]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact h⟩⟩)
      (fun ⟨a, ⟨b, hb⟩⟩ => ⟨(a, b), by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Subgroup.mem_centralizer_iff] at hb
        specialize hb a (Set.mem_singleton a)
        exact hb⟩)
      (fun _ => rfl)
      (fun _ => rfl)
  · rw [Nat.card_sigma]

/-- 
Task 2: The 5/8 Theorem.
Prove that if the commuting probability is strictly greater than 5/8, the group is abelian.
-/
theorem abelian_of_commutingProbability_gt_five_eighths 
  (h : commutingProbability G > 5/8) : ∀ x y : G, x * y = y * x := by
  by_contra h_not_comm
  push_neg at h_not_comm
  have h_prob_le : commutingProbability G ≤ 5/8 := by
    let Z := Subgroup.center G
    have h_not_abelian : Z ≠ ⊤ := by
      intro hZ
      obtain ⟨x, y, hxy⟩ := h_not_comm
      have hx : x ∈ Z := by rw [hZ]; exact Subgroup.mem_top x
      rw [Subgroup.mem_center_iff] at hx
      specialize hx y
      rw [hx] at hxy
      contradiction
    
    have h_index : Z.index ≥ 4 := by
      by_contra! h_lt
      have : Z.index ≠ 0 := Subgroup.index_ne_zero_of_finite (H := Z)
      have : Z.index = 1 ∨ Z.index = 2 ∨ Z.index = 3 := by omega
      rcases this with h1 | h2 | h3
      · rw [Subgroup.index_eq_one] at h1
        rw [h1] at h_not_abelian
        contradiction
      · have h_card : Nat.card (G ⧸ Z) = 2 := by rw [← Subgroup.index_eq_card, h2]
        letI : IsCyclic (G ⧸ Z) := isCyclic_of_prime_card h_card
        have h_comm := commutative_of_cyclic_center_quotient (QuotientGroup.mk' Z) (le_of_eq (QuotientGroup.ker_mk' Z))
        apply h_not_abelian
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_center_iff]
        intro y
        exact (h_comm x y).symm
      · have h_card : Nat.card (G ⧸ Z) = 3 := by rw [← Subgroup.index_eq_card, h3]
        letI : IsCyclic (G ⧸ Z) := isCyclic_of_prime_card h_card
        have h_comm := commutative_of_cyclic_center_quotient (QuotientGroup.mk' Z) (le_of_eq (QuotientGroup.ker_mk' Z))
        apply h_not_abelian
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_center_iff]
        intro y
        exact (h_comm x y).symm

    rw [commutingProbability, card_commutingPairs_eq_sum_card_centralizer]
    
    -- Split sum based on center membership
    classical
    let S := Finset.univ.filter (· ∈ Z)
    let T := Finset.univ.filter (· ∉ Z)
    
    have h_split : ∑ x : G, (Nat.card (Subgroup.centralizer {x}) : ℚ) = 
                   Finset.sum S (fun x => (Nat.card (Subgroup.centralizer {x}) : ℚ)) + 
                   Finset.sum T (fun x => (Nat.card (Subgroup.centralizer {x}) : ℚ)) := by
      rw [← Finset.sum_union]
      · congr
        ext x
        simp only [S, T, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      · rw [Finset.disjoint_iff_ne]
        intro a ha b hb hab
        rw [Finset.mem_filter] at ha hb
        rw [← hab] at hb
        exact hb.2 ha.2

    -- Bound for center elements
    have hS : ∀ x ∈ S, Nat.card (Subgroup.centralizer {x}) = Nat.card G := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Subgroup.card_eq_iff_eq_top]
      rw [eq_top_iff]
      intro y _
      rw [Subgroup.mem_centralizer_iff]
      simp
      rw [Subgroup.mem_center_iff] at hx
      exact (hx.2 y).symm

    -- Bound for non-center elements
    have hT : ∀ x ∈ T, Nat.card (Subgroup.centralizer {x}) ≤ Nat.card G / 2 := by {
      intro x hx
      rw [Finset.mem_filter] at hx
      have h_not_center : x ∉ Z := hx.2
      have h_proper : Subgroup.centralizer {x} ≠ ⊤ := by
        intro h_top
        apply h_not_center
        rw [Subgroup.mem_center_iff]
        intro y
        have : y ∈ Subgroup.centralizer {x} := by rw [h_top]; exact Subgroup.mem_top y
        rw [Subgroup.mem_centralizer_iff] at this
        simp at this
        exact this.symm
      
      have h_index_ge_2 : Subgroup.index (Subgroup.centralizer {x}) ≥ 2 := by
         apply Subgroup.one_lt_index_of_ne_top h_proper
         
      -- card G = card H * index H
      have h_mul : Nat.card G = Nat.card (Subgroup.centralizer {x}) * Subgroup.index (Subgroup.centralizer {x}) := 
        (Subgroup.card_mul_index _).symm
        
      apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
      rw [h_mul]
      apply Nat.mul_le_mul_left
      exact h_index_ge_2
    }

    -- Final calculation
    simp only [Nat.cast_sum]
    rw [h_split]
    
    -- Substitution for S
    rw [Finset.sum_congr rfl (fun x hx => by 
      rw [hS x hx]
    )]
    simp only [Finset.sum_const, nsmul_eq_mul]

    -- Substitution for T inequality
    -- Bound T term
    let T_upper := ∑ x ∈ T, (Nat.card G / 2 : ℚ)
    have h_bound : ∑ x ∈ T, (Nat.card (Subgroup.centralizer {x}) : ℚ) ≤ T_upper := by
      apply Finset.sum_le_sum
      intro x hx
      apply le_trans (Nat.cast_le.mpr (hT x hx))
      -- ↑(n / k) ≤ ↑n / ↑k
      apply Nat.cast_div_le

    -- Step 1: Inequality substitution
    have h_ineq1 : (↑S.card * ↑(Nat.card G) + ∑ x ∈ T, (Nat.card (Subgroup.centralizer {x}) : ℚ)) / ↑(card G)^2 ≤ 
                   (↑S.card * ↑(Nat.card G) + T_upper) / ↑(card G)^2 := by
      apply div_le_div_of_nonneg_right
      · apply add_le_add_right
        exact h_bound
      · positivity

    apply le_trans h_ineq1
    
    -- Step 2: Simplification
    dsimp [T_upper]
    simp only [Finset.sum_const, nsmul_eq_mul]
    
    have h_card_S : S.card = Nat.card Z := by
      dsimp [S]
      rw [← Fintype.card_coe]
      trans Fintype.card {x // x ∈ Z}
      · apply Fintype.card_congr
        exact {
          toFun := fun ⟨x, h⟩ => ⟨x, by simpa using h⟩
          invFun := fun ⟨x, h⟩ => ⟨x, by simp; exact h⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
        }
      · rw [Nat.card_eq_fintype_card]

    have h_card_T : T.card = Nat.card G - Nat.card Z := by
      rw [← h_card_S]
      dsimp [T, S]
      rw [Finset.filter_not]
      rw [Finset.card_sdiff]
      · simp

    -- Algebra
    let k := Z.index
    have hk4 : 4 ≤ k := h_index
    have hG_eq : Nat.card G = Nat.card Z * k := 
      (Subgroup.card_mul_index Z).symm
    
    have hG_q : (Nat.card G : ℚ) = (Nat.card Z : ℚ) * k := by
      rw [hG_eq, Nat.cast_mul]
    
    rw [hG_q]
    
    have hZ_pos : 0 < (Nat.card Z : ℚ) := by
      rw [Nat.cast_pos, Nat.card_eq_fintype_card]
      apply Fintype.card_pos_iff.mpr
      use 1
      exact Subgroup.one_mem Z
      
    have hk_pos : 0 < (k : ℚ) := by
      rw [Nat.cast_pos]
      linarith

    -- Simplify the expression
    field_simp

    rw [h_card_S, h_card_T]
    rw [Nat.cast_sub (by rw [hG_eq]; apply Nat.le_mul_of_pos_right; linarith [hk4])]
    rw [← Nat.card_eq_fintype_card]
    rw [hG_q]
    suffices 8 * k + 8 * k^2 ≤ 10 * (k : ℚ)^2 by
      rw [← mul_le_mul_iff_of_pos_left (by positivity : 0 < (Nat.card Z : ℚ)^2)] at this
      convert this using 1 <;> ring
    have hk4_q : (4 : ℚ) ≤ k := Nat.cast_le.mpr hk4
    nlinarith
  linarith
