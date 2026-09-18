/-
Detour width and cycle structure for the Andrews–Curtis move graph.
Supplement to the competition's AC.lean.
-/

import AC
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace AC

/-! ## Length of a free-group word -/

noncomputable def wordLen {n : ℕ} (w : Word n) : ℕ :=
  w.norm

noncomputable def relLen {n : ℕ} (R : Relators n) : ℕ :=
  Finset.univ.sum (fun i => wordLen (R i))

/-! ## Paths as data -/

inductive MovePath {n : ℕ} : Relators n → Relators n → Type
  | nil (R : Relators n) : MovePath R R
  | cons {R S T : Relators n} (h : Step R S) (p : MovePath S T) : MovePath R T

namespace MovePath

noncomputable def maxRelLen {n : ℕ} {R S : Relators n} (p : MovePath R S) : ℕ :=
  match p with
  | .nil _ => relLen R
  | .cons _ q => max (relLen R) q.maxRelLen

def length {n : ℕ} {R S : Relators n} (p : MovePath R S) : ℕ :=
  match p with
  | .nil _ => 0
  | .cons _ q => q.length + 1

theorem reachable {n : ℕ} {R S : Relators n} (p : MovePath R S) :
    Reachable R S := by
  induction p with
  | nil _ => exact Relation.ReflTransGen.refl
  | cons h _ ih => exact Relation.ReflTransGen.head h ih

theorem relLen_le_maxRelLen {n : ℕ} {R S : Relators n} (p : MovePath R S) :
    relLen S ≤ p.maxRelLen := by
  induction p with
  | nil _ => exact le_rfl
  | cons _ _ ih =>
    simp only [maxRelLen]
    exact le_trans ih (le_max_right _ _)

theorem eq_of_length_eq_zero {n : ℕ} {R S : Relators n}
    (p : MovePath R S) (h : p.length = 0) : R = S := by
  cases p with
  | nil _ => rfl
  | cons _ _ => simp [length] at h

end MovePath

/-! ## Detour width and graph distance -/

noncomputable def detourWidth {n : ℕ} (R : Relators n) : ℕ :=
  sInf { m : ℕ | ∃ p : MovePath (standard n) R, p.maxRelLen ≤ m }

noncomputable def graphDist {n : ℕ} (R : Relators n) : ℕ :=
  sInf { k : ℕ | ∃ p : MovePath (standard n) R, p.length = k }

theorem detourWidth_le_of_path {n : ℕ} {R : Relators n} {m : ℕ}
    (p : MovePath (standard n) R) (h : p.maxRelLen ≤ m) :
    detourWidth R ≤ m := by
  unfold detourWidth
  exact Nat.sInf_le ⟨p, h⟩

theorem relLen_le_detourWidth {n : ℕ} (R : Relators n)
    (h : ∃ _ : MovePath (standard n) R, True) :
    relLen R ≤ detourWidth R := by
  obtain ⟨p, _⟩ := h
  unfold detourWidth
  apply le_csInf
  · exact ⟨p.maxRelLen, p, le_rfl⟩
  · intro m hm
    obtain ⟨q, hq⟩ := hm
    exact le_trans (MovePath.relLen_le_maxRelLen q) hq

theorem detourWidth_standard (n : ℕ) :
    detourWidth (standard n) = relLen (standard n) := by
  apply le_antisymm
  · apply detourWidth_le_of_path (MovePath.nil (standard n))
    exact le_of_eq rfl
  · exact relLen_le_detourWidth (standard n) ⟨MovePath.nil (standard n), trivial⟩

/-! ## Cycles and two-hump -/

structure Cycle {n : ℕ} (R S : Relators n) where
  path₁ : MovePath R S
  path₂ : MovePath R S

namespace Cycle

noncomputable def height {n : ℕ} {R S : Relators n} (c : Cycle R S) : ℕ :=
  max c.path₁.maxRelLen c.path₂.maxRelLen

theorem detourWidth_le_height {n : ℕ} {S : Relators n}
    (c : Cycle (standard n) S) :
    detourWidth S ≤ c.height := by
  unfold detourWidth height
  apply Nat.sInf_le
  by_cases h : c.path₁.maxRelLen ≤ c.path₂.maxRelLen
  · exact ⟨c.path₁, le_trans h (le_max_right _ _)⟩
  · push Not at h
    exact ⟨c.path₂, le_trans (le_of_lt h) (le_max_left _ _)⟩

end Cycle

def HasTwoHump {n : ℕ} (S : Relators n) : Prop :=
  ∃ c : Cycle (standard n) S, c.height > relLen S

/-! ## Witnesses at rank 2 -/

noncomputable def R₁ : Relators 2 :=
  Function.update (standard 2) 0 ((FreeGroup.of 0)⁻¹)

noncomputable def R₂ : Relators 2 :=
  Function.update (standard 2) 0 (FreeGroup.of 0 * FreeGroup.of 1)

noncomputable def path₁ : MovePath (standard 2) R₁ :=
  MovePath.cons (Step.inv (standard 2) 0) (MovePath.nil R₁)

noncomputable def path₂ : MovePath (standard 2) R₂ :=
  MovePath.cons
    (Step.mulRight (standard 2) 0 1 (by decide))
    (MovePath.nil R₂)

/-! ## Relator length computations -/

theorem relLen_standard_2 : relLen (standard 2) = 2 := by
  unfold relLen wordLen standard
  rw [Fin.sum_univ_two]
  simp [FreeGroup.norm_of]

theorem relLen_R₁ : relLen R₁ = 2 := by
  unfold relLen wordLen R₁
  rw [Fin.sum_univ_two]
  have h0 : (Function.update (standard 2) 0 ((FreeGroup.of 0)⁻¹) 0).norm = 1 := by
    simp [Function.update, FreeGroup.norm_inv_eq, FreeGroup.norm_of]
  have h1 : (Function.update (standard 2) 0 ((FreeGroup.of 0)⁻¹) 1).norm = 1 := by
    simp [Function.update, standard, FreeGroup.norm_of]
  rw [h0, h1]

theorem relLen_R₂ : relLen R₂ = 3 := by
  unfold relLen wordLen R₂
  rw [Fin.sum_univ_two]
  have hnorm : (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1).norm = 2 := by
    have h1 : (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1).toWord
              = [(0, true), (1, true)] := by
      rw [FreeGroup.toWord_mul, FreeGroup.toWord_of, FreeGroup.toWord_of]
      rfl
    show (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1).toWord.length = 2
    rw [h1]
    rfl
  have h0 : (Function.update (standard 2) 0
      (FreeGroup.of 0 * FreeGroup.of 1) 0).norm = 2 := by
    simp [Function.update, hnorm]
  have h1 : (Function.update (standard 2) 0
      (FreeGroup.of 0 * FreeGroup.of 1) 1).norm = 1 := by
    simp [Function.update, standard, FreeGroup.norm_of]
  rw [h0, h1]

/-! ## Distinctness -/

theorem R₁_ne_standard : R₁ ≠ standard 2 := by
  intro h
  have h0 : (FreeGroup.of (0 : Fin 2))⁻¹ = FreeGroup.of 0 := by
    have h' := congrFun h 0
    simp only [R₁, standard, Function.update] at h'
    exact h'
  have hto := congr_arg FreeGroup.toWord h0
  rw [FreeGroup.toWord_inv, FreeGroup.toWord_of] at hto
  -- hto : FreeGroup.invRev [(0, true)] = [(0, true)]
  have hne : FreeGroup.invRev ([(0, true)] : List (Fin 2 × Bool)) ≠ [(0, true)] := by
    decide
  exact hne hto

theorem R₂_ne_standard : R₂ ≠ standard 2 := by
  intro h
  have h0 : FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 = FreeGroup.of 0 := by
    have h' := congrFun h 0
    simp only [R₂, standard, Function.update] at h'
    exact h'
  have h2 : FreeGroup.of (1 : Fin 2) = 1 := by
    have h0' : FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 =
               FreeGroup.of (0 : Fin 2) * 1 := by
      rw [mul_one]
      exact h0
    exact mul_left_cancel h0'
  exact FreeGroup.of_ne_one 1 h2

/-! ## Detour widths of witnesses -/

theorem detourWidth_R₁ : detourWidth R₁ = 2 := by
  apply le_antisymm
  · apply detourWidth_le_of_path path₁
    change max (relLen (standard 2)) (relLen R₁) ≤ 2
    rw [relLen_standard_2, relLen_R₁]
    omega
  · have h := relLen_le_detourWidth R₁ ⟨path₁, trivial⟩
    rw [relLen_R₁] at h
    exact h

theorem detourWidth_R₂ : detourWidth R₂ = 3 := by
  apply le_antisymm
  · apply detourWidth_le_of_path path₂
    change max (relLen (standard 2)) (relLen R₂) ≤ 3
    rw [relLen_standard_2, relLen_R₂]
    omega
  · have h := relLen_le_detourWidth R₂ ⟨path₂, trivial⟩
    rw [relLen_R₂] at h
    exact h

/-! ## Graph distances of witnesses -/

theorem graphDist_R₁_le : graphDist R₁ ≤ 1 := by
  unfold graphDist
  apply Nat.sInf_le
  exact ⟨path₁, by simp [path₁, MovePath.length]⟩

theorem graphDist_R₁_ge : 1 ≤ graphDist R₁ := by
  unfold graphDist
  apply le_csInf
  · exact ⟨1, path₁, by simp [path₁, MovePath.length]⟩
  · intro k hk
    obtain ⟨p, hp⟩ := hk
    rw [← hp]
    by_contra h
    push Not at h
    have h0 : p.length = 0 := by omega
    exact R₁_ne_standard (MovePath.eq_of_length_eq_zero p h0).symm

theorem graphDist_R₁ : graphDist R₁ = 1 :=
  le_antisymm graphDist_R₁_le graphDist_R₁_ge

theorem graphDist_R₂_le : graphDist R₂ ≤ 1 := by
  unfold graphDist
  apply Nat.sInf_le
  exact ⟨path₂, by simp [path₂, MovePath.length]⟩

theorem graphDist_R₂_ge : 1 ≤ graphDist R₂ := by
  unfold graphDist
  apply le_csInf
  · exact ⟨1, path₂, by simp [path₂, MovePath.length]⟩
  · intro k hk
    obtain ⟨p, hp⟩ := hk
    rw [← hp]
    by_contra h
    push Not at h
    have h0 : p.length = 0 := by omega
    exact R₂_ne_standard (MovePath.eq_of_length_eq_zero p h0).symm

theorem graphDist_R₂ : graphDist R₂ = 1 :=
  le_antisymm graphDist_R₂_le graphDist_R₂_ge

/-! ## Independence -/

theorem detourWidth_independent_of_graphDist :
    ¬ ∃ f : ℕ → ℕ, ∀ {n : ℕ} (R : Relators n),
      (∃ _ : MovePath (standard n) R, True) →
      detourWidth R = f (graphDist R) := by
  intro ⟨f, hf⟩
  have h1 := hf R₁ ⟨path₁, trivial⟩
  have h2 := hf R₂ ⟨path₂, trivial⟩
  rw [detourWidth_R₁, graphDist_R₁] at h1
  rw [detourWidth_R₂, graphDist_R₂] at h2
  omega

end AC
