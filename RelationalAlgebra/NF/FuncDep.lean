import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra

import Mathlib.Data.Finset.Basic

import Architect

namespace RM

variable {α μ : Type} [DecidableEq α]

namespace NF

/-- A functional dependency over attributes of type `α`. -/
@[
  blueprint "def:fd"
  (title := /-- Functional Dependency -/)
  (statement := /--
    A functional dependency over attributes of type $\alpha$ is a pair of
    finite sets of attributes, \textit{lhs} and \textit{rhs},
    written as \textit{lhs} $\rightarrow$ \textit{rhs}.
  -/)
]
structure FunctionalDependency (α : Type) where
  lhs : Finset α
  rhs : Finset α
deriving DecidableEq

/-- Notation for functional dependencies. -/
infix:50 " -> " => FunctionalDependency.mk

/-- A functional dependency holds on a relation instance. -/
@[
  blueprint "def:fd-holds"
  (title := /-- FD Holds -/)
  (statement := /--
    A functional dependency holds on a relation instance if, whenever two tuples
    agree on every attribute in the left-hand side (\textit{lhs}), they also agree
    on every attribute in the right-hand side (\textit{rhs}).
  -/)
]
def FunctionalDependency.holds (fd : FunctionalDependency α) (r : RelationInstance α μ) : Prop :=
  ∀ {t₁ t₂}, t₁ ∈ r.tuples → t₂ ∈ r.tuples →
    (∀ a ∈ fd.lhs, t₁ a = t₂ a) → (∀ b ∈ fd.rhs, t₁ b = t₂ b)

/-- A trivial functional dependency: the RHS is contained in the LHS. -/
@[
  blueprint "def:trivial-fd"
  (title := /-- Trivial FD -/)
  (statement := /--
    A functional dependency is trivial if every attribute in its right-hand side
    (\textit{rhs}) also appears in its left-hand side (\textit{lhs}).
  -/)
]
def FunctionalDependency.is_trivial (fd : FunctionalDependency α) : Prop :=
  fd.rhs ⊆ fd.lhs

end NF

/-- A relation instance satisfies a set of functional dependencies
    if it satisfies each dependency in the set. -/
@[
  blueprint "def:sat"
  (title := /-- Relation Instance Satisfies FDs -/)
  (statement := /--
    A relation instance $r$ satisfies a set of functional dependencies if every
    dependency in the set holds on $r$.
  -/)
]
def RelationInstance.sat (r : RelationInstance α μ) (F : Finset (NF.FunctionalDependency α)) : Prop :=
  ∀ {f}, f ∈ F → f.holds r

end RM

namespace Finset

variable {α : Type} [DecidableEq α]

/-- A set of attributes `S` is closed under a set of FDs `F` if, whenever a
    functional dependency `X -> Y` belongs to `F` and `X ⊆ S`, then `Y ⊆ S`.
-/
def is_closed_under (S : Finset α) (F : Finset (RM.NF.FunctionalDependency α)) : Prop :=
  ∀ fd ∈ F, fd.lhs ⊆ S → fd.rhs ⊆ S

end Finset
