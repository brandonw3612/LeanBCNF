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
  blueprint "def:decomp"
  (title := /-- Binary Decomposition -/)
  (statement := /--
    A binary decomposition over a given schema $R$ is defined by two sub-schemas, \texttt{left} and
    \texttt{right}, and the proposition that they cover the original schema, \textit{i.e.},
    $\texttt{left} \cup \texttt{right} = R$.
  -/)
]
structure Decomposition (R : Finset α) where
  left : Finset α
  right : Finset α
  cover : left ∪ right = R

/-- The left subset of a decomposition is a subset of the schema. -/
@[
  blueprint "thm:decomp-left-subset"
  (title := /-- Left Sub-Schema is Subset -/)
  (statement := /--
    Given a schema $R$ and a valid binary decomposition $d$ over $R$, the left sub-schema is a
    subset of $R$ by definiton.
  -/)
]
theorem Decomposition.left_subset {R : Finset α} {d : Decomposition R} :
  d.left ⊆ R := by
  simp [← d.cover]

/-- The right subset of a decomposition is a subset of the schema. -/
@[
  blueprint "thm:decomp-right-subset"
  (title := /-- Right Sub-Schema is Subset -/)
  (statement := /--
    Given a schema $R$ and a valid binary decomposition $d$ over $R$, the right sub-schema is a
    subset of $R$ by definiton.
  -/)
]
theorem Decomposition.right_subset {R : Finset α} {d : Decomposition R}:
  d.right ⊆ R := by
  simp [← d.cover]

@[
  simp,
  blueprint "def:decomp-left-instance"
  (title := /-- Left Projection of a Decomposition -/)
  (statement := /--
    Given a schema $R$, a valid binary decomposition $d$ over $R$, and a relation instance $r$ with
    schema $R$, the left projection of $r$ with respect to $d$ is the projection of $r$ onto the
    left sub-schema of $d$.
  -/)
]
def Decomposition.left_instance {R : Finset α} {d : Decomposition R} {r : RelationInstance α μ}
  (h_r : r.schema = R) :=
  have h_sub : d.left ⊆ r.schema := by simp_all [d.left_subset]
  projection r d.left h_sub

@[
  simp,
  blueprint "def:decomp-right-instance"
  (title := /-- Right Projection of a Decomposition -/)
  (statement := /--
    Given a schema $R$, a valid binary decomposition $d$ over $R$, and a relation instance $r$ with
    schema $R$, the right projection of $r$ with respect to $d$ is the projection of $r$ onto the
    right sub-schema of $d$.
  -/)
]
def Decomposition.right_instance {R : Finset α} {d : Decomposition R} {r : RelationInstance α μ}
  (h_r : r.schema = R) :=
  have h_sub : d.right ⊆ r.schema := by simp_all [d.right_subset]
  projection r d.right h_sub

/-- A decomposition is lossless if the original relation can be reconstructed by joining the
    projections on the left and right subsets.
-/
@[
  blueprint "def:decomp-lossless"
  (title := /-- Decomposition Losslessness -/)
  (statement := /--
    A decomposition $d$ over a schema $R$ is lossless with respect to a relation instance $r$ with
    schema $R$, if the original relation can be reconstructed by joining the projections of $r$ onto
    the left and right sub-schemas of $d$.
  -/)
]
def Decomposition.is_lossless {R : Finset α} {r : RelationInstance α μ} (d : Decomposition R)
  (h_r : r.schema = R) : Prop :=
  r = join (d.left_instance h_r) (d.right_instance h_r)

@[
  blueprint "def:decomp-tree"
  (title := /-- Decomposition Tree -/)
  (statement := /--
    A decomposition tree is a recursive structure that represents a hierarchical decomposition of a
    schema into sub-schemas. Each node in the tree corresponds to a binary decomposition, and the
    leaves of the tree correspond to the final sub-schemas that are no longer decomposed.
  -/)
]
inductive DecompositionTree : Finset α → Type where
  | leaf (R : Finset α) : DecompositionTree R
  | node {R : Finset α} (d : Decomposition R)
    (left : DecompositionTree d.left) (right : DecompositionTree d.right) : DecompositionTree R

@[
  blueprint "def:decomp-tree-leaves"
  (title := /-- Leaves of a Decomposition Tree -/)
  (statement := /--
    The leaves of a decomposition tree are the final sub-schemas of the decomposition.
  -/)
]
def DecompositionTree.leaves {R : Finset α} : DecompositionTree R → Finset (Finset α)
  | DecompositionTree.leaf R => {R}
  | DecompositionTree.node _ left right => left.leaves ∪ right.leaves

@[
  blueprint "def:decomp-tree-reconstruct"
  (title := /-- Reconstructing a Relation from a Decomposition Tree -/)
  (statement := /--
    Given a schema $R$, a decomposition tree $t$ over $R$, and a relation instance $r$ with schema
    $R$, the reconstruction of $r$ from $t$ is defined recursively. If $t$ is a leaf, the
    reconstruction is simply $r$. If $t$ is a node, the reconstruction is the join of the
    reconstructions of the left and right subtrees, using the left and right projections of $r$ with
    respect to the decomposition at that node.
  -/)
]
def DecompositionTree.reconstruct {R : Finset α} {μ : Type}
    (t : DecompositionTree R) (r : RelationInstance α μ) (h_r : r.schema = R)
    : RelationInstance α μ :=
  match t with
  | DecompositionTree.leaf _ => r
  | DecompositionTree.node d left right =>
    join (DecompositionTree.reconstruct left (d.left_instance h_r) (by simp [projection]))
         (DecompositionTree.reconstruct right (d.right_instance h_r) (by simp [projection]))

@[
  blueprint "def:decomp-tree-lossless"
  (title := /-- Decomposition Tree Losslessness -/)
  (statement := /--
    A decomposition tree $t$ over a schema $R$ is lossless with respect to a relation instance $r$
    with schema $R$, if the original relation can be reconstructed by recursively joining the
    projections of $r$ onto the sub-schemas defined by the decomposition tree.
  -/)
]
def DecompositionTree.is_lossless {R : Finset α} {r : RelationInstance α μ} (h_r : r.schema = R)
  (t : DecompositionTree R) : Prop :=
  r = t.reconstruct r h_r

@[
  blueprint "def:decomp-tree-lossless-syn"
  (title := /-- Decomposition Tree Losslessness (Syntactic) -/)
  (statement := /--
    With the tree structure and losslessness of a binary decomposition (\cref{def:decomp-lossless}),
    we recursively define a syntactic notion of losslessness for a decomposition tree. If the tree
    is a leaf, it is syntactically lossless trivially. If the tree is a node, it is lossless if the
    decomposition at that node is lossless and both the left and right subtrees are also
    syntactically lossless.
  -/)
]
def DecompositionTree.is_lossless_syn {R : Finset α} {r : RelationInstance α μ}
  (h_r : r.schema = R) (t : DecompositionTree R) : Prop :=
  match t with
  | .leaf _ => True
  | .node d left right =>
    have h_sl : (d.left_instance h_r).schema = d.left := by simp [projection]
    have h_sr : (d.right_instance h_r).schema = d.right := by simp [projection]
    d.is_lossless h_r ∧ left.is_lossless_syn h_sl ∧ right.is_lossless_syn h_sr

@[
  blueprint "thm:decomp-tree-lossless-imp"
  (title := /-- Decomposition Tree Losslessness Implication -/)
  (statement := /--
    If a decomposition tree is syntactically lossless with respect to a relation instance, then
    it is also semantically lossless. This theorem establishes the connection between the syntactic
    definition of losslessness and the semantic notion of losslessness, ensuring that if the
    syntactic conditions are satisfied, the original relation can indeed be reconstructed from the
    projections defined by the decomposition tree.
  -/)
]
theorem DecompositionTree.is_lossless_imp {R : Finset α} {r : RelationInstance α μ}
  (h_r : r.schema = R) {t : DecompositionTree R} :
  t.is_lossless_syn h_r → t.is_lossless h_r := by
  induction t generalizing r with
  | leaf R =>
    simp_all [DecompositionTree.is_lossless, DecompositionTree.reconstruct, DecompositionTree.is_lossless_syn]
  | node d left right ih_left ih_right => next R =>
    rw [DecompositionTree.is_lossless, DecompositionTree.is_lossless_syn]
    intro ⟨h_d, h_left, h_right⟩
    unfold Decomposition.is_lossless at h_d
    set r_left := d.left_instance h_r
    set r_right := d.right_instance h_r
    have h_left_schema : r_left.schema = d.left := by simp [r_left, projection]
    have h_right_schema : r_right.schema = d.right := by simp [r_right, projection]
    have h_left := ih_left h_left_schema h_left
    have h_right := ih_right h_right_schema h_right
    rw [DecompositionTree.is_lossless] at h_left h_right
    rw [DecompositionTree.reconstruct, ←h_left, ←h_right]
    exact h_d

end NF

namespace RM
