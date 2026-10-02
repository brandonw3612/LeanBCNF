import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra
import RelationalAlgebra.NF.Closure
import RelationalAlgebra.NF.FuncDep

import Mathlib.Data.Finset.Basic

import Architect

namespace RM

namespace NF

variable {α μ : Type} [DecidableEq α]

/-- Superkey: equality on `K` implies equality on the whole schema. -/
@[
  blueprint "def:superkey"
  (title := /-- Superkey -/)
  (statement := /--
    A superkey $K$ over a relation instance $r$ is defined as a subset of the schema of $r$ such
    that if two tuples agree on the attributes in $K$, they must also agree on all attributes.
  -/)
]
def is_superkey (K : Finset α) (r : RelationInstance α μ) : Prop :=
  K ⊆ r.schema ∧ (
    ∀ {t₁ t₂}, t₁ ∈ r.tuples → t₂ ∈ r.tuples →
    (∀ a ∈ K, t₁ a = t₂ a) → (∀ a ∈ r.schema, t₁ a = t₂ a)
  )

/-- Candidate key: minimal superkey of which no strict subset is a superkey. -/
@[
  blueprint "def:candidate-key"
  (title := /-- Candidate Key -/)
  (statement := /--
    A candidate key $K$ over a relation instance $r$ is a superkey such that no strict subset of $K$
    is also a superkey.
  -/)
]
def is_candidate_key (K : Finset α) (r : RelationInstance α μ) : Prop :=
  is_superkey K r ∧
  ∀ K' ⊂ K, ¬ is_superkey K' r

@[
  blueprint "def:superkey-syn"
  (title := /-- Superkey (Syntactic) -/)
  (statement := /--
    We define the syntactic superkey on the schema level: A set of attributes $K$ is a superkey over
    a schema $R$ with respect to a set of functional dependencies $F$ if the closure of $K$ under
    $F$ restricted to $R$ is equal to $R$.
  -/)
]
def is_superkey_syn (K R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
  K ⊆ R ∧ res_attr_closure F K R = R

@[
  blueprint "thm:superkey-syn-imp-sem"
  (title := /-- Syntactic Superkey Implies Semantic Superkey -/)
  (statement := /--
    If a set of attributes $K$ is a syntactic superkey over a schema $R$ with respect to a set of
    functional dependencies $F$, then for any relation instance $r$ with schema $R$ that satisfies
    $F$, $K$ is also a semantic superkey over $r$.
  -/)
]
theorem superkey_syn_imp_sem {K R : Finset α} {F : Finset (FunctionalDependency α)} :
  is_superkey_syn K R F →
  ∀ {r : RelationInstance α μ}, (h_r : r.schema = R) → (h_sat : r.sat_res_imp F) → is_superkey K r := by
  simp_all [is_superkey, is_superkey_syn]
  intro h_K h_ac r h_r h_sat t₁ t₂
  let fd : FunctionalDependency α := K -> R
  simp [res_attr_closure] at h_ac
  have h_der : F ⊢ fd := Derives.trans attr_closure_sound (Derives.rfl h_ac)
  have h_res_imp : res_imp F fd r.schema := by
    simp [res_imp, fd, h_r]
    exact ⟨armstrong_correct.1 h_der, h_K⟩
  exact h_sat h_res_imp

end NF

end RM
