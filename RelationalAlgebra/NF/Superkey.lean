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
  K ⊆ R ∧ implies_proj F R (K -> R)

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
  K ⊆ R ∧ attr_closure_proj F K R = R

@[
  blueprint "theorem:superkey-sem-eq-syn"
]
theorem superkey_sem_eq_syn {K R : Finset α} {F : Finset (FunctionalDependency α)} :
  is_superkey_syn K R F ↔ is_superkey K R F := by
  rw [is_superkey, is_superkey_syn, attr_closure_proj, implies_proj]
  constructor
  · intro ⟨h_k, h_ac⟩
    constructor
    · exact h_k
    · constructor
      · apply armstrong_sound
        rw [Finset.inter_eq_right] at h_ac
        apply Derives.trans (attr_closure_sound) (Derives.rfl h_ac)
      simp
      trivial
  · intro ⟨h_k, ⟨h_imp, _⟩⟩
    constructor
    · exact h_k
    · rw [Finset.inter_eq_right]
      apply attr_closure_complete
      apply armstrong_complete
      exact h_imp

end NF

end RM
