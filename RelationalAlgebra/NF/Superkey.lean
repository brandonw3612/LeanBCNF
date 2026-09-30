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
  blueprint "definition:superkey"
]
def is_superkey (K R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
  K ⊆ R ∧ res_imp F (K -> R) R

/-- Candidate key: minimal superkey of which no strict subset is a superkey. -/
@[
  blueprint "definition:candidate-key"
]
def is_candidate_key (K R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
  is_superkey K R F ∧
  ∀ K' ⊂ K, ¬ is_superkey K' R F

@[
  blueprint "definition:superkey-syn"
]
def is_superkey_syn (K R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
  K ⊆ R ∧ res_attr_closure F K R = R

@[
  blueprint "theorem:superkey-sem-eq-syn"
]
theorem superkey_sem_eq_syn {K R : Finset α} {F : Finset (FunctionalDependency α)} :
  is_superkey_syn K R F ↔ is_superkey K R F := by
  simp_all [is_superkey, is_superkey_syn, res_imp, res_attr_closure]
  rw [← armstrong_correct]
  intro h_k
  constructor
  · intro h_ac
    exact Derives.trans (attr_closure_sound) (Derives.rfl h_ac)
  · exact attr_closure_complete

end NF

end RM
