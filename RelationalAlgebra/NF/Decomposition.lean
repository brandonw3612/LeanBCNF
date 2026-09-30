import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra
import RelationalAlgebra.NF.FuncDep
import RelationalAlgebra.NF.Closure

import Mathlib.Data.Finset.Basic

import Architect

namespace RM

namespace NF

variable {α μ : Type} [DecidableEq α]

/--
  A decomposition of a schema into two subsets of attributes
  whose union covers the entire schema.
-/
@[
  blueprint "definition:decomposition"
]
structure Decomposition (R : Finset α) where
  left : Finset α
  right : Finset α
  cover : left ∪ right = R

/-- The left subset of a decomposition is a subset of the schema. -/
@[
  blueprint "theorem:decomposition-left-subset"
]
theorem Decomposition.left_subset {R : Finset α} {d : Decomposition R} {r : RelationInstance α μ} :
  r.schema = R → d.left ⊆ r.schema := by
  intro h_r
  simp [← d.cover, h_r]

/-- The right subset of a decomposition is a subset of the schema. -/
@[
  blueprint "theorem:decomposition-right-subset"
]
theorem Decomposition.right_subset {R : Finset α} {d : Decomposition R} {r : RelationInstance α μ} :
  r.schema = R → d.right ⊆ r.schema := by
  intro h_r
  simp [← d.cover, h_r]

/-- A decomposition is lossless if the original relation can be reconstructed by joining the projections on the left and right subsets. -/
@[
  blueprint "definition:decomposition-is-lossless"
]
def Decomposition.is_lossless {R : Finset α} (d : Decomposition R) (F : Finset (FunctionalDependency α)) : Prop :=
  ∀ {μ : Type} (r : RelationInstance α μ),
    (h_r : r.schema = R) → r.sat_res_imp F →
    r = join (projection r d.left (d.left_subset h_r)) (projection r d.right (d.right_subset h_r))

@[
  blueprint "definition:decomposition-tree"
]
inductive DecompositionTree : Finset α → Type where
  | leaf (R : Finset α) : DecompositionTree R
  | node {R : Finset α} (d : Decomposition R)
    (left : DecompositionTree d.left) (right : DecompositionTree d.right) : DecompositionTree R

@[
  blueprint "definition:decomposition-tree-leaves"
]
def DecompositionTree.leaves {R : Finset α} : DecompositionTree R → Finset (Finset α)
  | DecompositionTree.leaf R => {R}
  | DecompositionTree.node _ left right => left.leaves ∪ right.leaves

def DecompositionTree.reconstruct {R : Finset α} {μ : Type}
    (t : DecompositionTree R) (r : RelationInstance α μ) (h_r : r.schema = R)
    : RelationInstance α μ :=
  match t with
  | DecompositionTree.leaf _ => r
  | DecompositionTree.node d left right =>
    let r_left := projection r d.left (d.left_subset h_r)
    let r_right := projection r d.right (d.right_subset h_r)
    join (DecompositionTree.reconstruct left r_left (by simp [r_left, projection]))
         (DecompositionTree.reconstruct right r_right (by simp [r_right, projection]))

@[
  blueprint "definition:decomposition-tree-is-lossless"
]
def DecompositionTree.is_lossless {R : Finset α} (t : DecompositionTree R) (F : Finset (FunctionalDependency α)) : Prop :=
  ∀ {μ : Type} {r : RelationInstance α μ},
    (h_r : r.schema = R) → r.sat_res_imp F → r = t.reconstruct r h_r

def DecompositionTree.is_lossless_syn {R : Finset α} : DecompositionTree R → Finset (FunctionalDependency α) → Prop
  | .leaf _, _ => True
  | .node d left right, F => d.is_lossless F ∧ left.is_lossless F ∧ right.is_lossless F

theorem DecompositionTree.is_lossless_imp {R : Finset α} {t : DecompositionTree R} {F : Finset (FunctionalDependency α)} :
  t.is_lossless_syn F → t.is_lossless F := by
  induction t with
  | leaf R =>
    simp_all [DecompositionTree.is_lossless, DecompositionTree.reconstruct, DecompositionTree.is_lossless_syn]
  | node d left right ih_left ih_right => next R =>
    rw [DecompositionTree.is_lossless, DecompositionTree.is_lossless_syn]
    intro ⟨h_d, h_left, h_right⟩ _ r h_r h_sat
    simp [Decomposition.is_lossless] at h_d
    have h_d := h_d r h_r h_sat
    set r_left := projection r d.left (d.left_subset h_r)
    set r_right := projection r d.right (d.right_subset h_r)
    rw [DecompositionTree.is_lossless] at h_left h_right
    have h_left_schema : r_left.schema = d.left := by simp [r_left, projection]
    have h_right_schema : r_right.schema = d.right := by simp [r_right, projection]
    have h_left_sat : r_left.sat_res_imp F := sat_res_imp_proj (d.left_subset h_r) h_sat
    have h_right_sat : r_right.sat_res_imp F := sat_res_imp_proj (d.right_subset h_r) h_sat
    have h_left := h_left h_left_schema h_left_sat
    have h_right := h_right h_right_schema h_right_sat
    rw [DecompositionTree.reconstruct, ←h_left, ←h_right]
    exact h_d

end NF

namespace RM
