import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra
import RelationalAlgebra.NF.FuncDep
import RelationalAlgebra.NF.Decomposition
import RelationalAlgebra.NF.Closure
import RelationalAlgebra.NF.Superkey

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Powerset

import Architect

namespace RM

namespace NF

variable {α μ : Type} [DecidableEq α]

@[
  blueprint "definition:BCNF"
]
def is_BCNF (R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
    ∀ {f}, implies_proj F R f → f.is_trivial ∨ is_superkey f.lhs R F

@[
  blueprint "definition:BCNF-syn"
]
def is_BCNF_syn (R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
    ∀ {X}, X ⊆ R → attr_closure_proj F X R = R ∨ attr_closure_proj F X R = X

@[
  blueprint "theorem:BCNF-sem-eq-syn"
]
theorem BCNF_sem_eq_syn {R : Finset α} {F : Finset (FunctionalDependency α)} :
  is_BCNF R F ↔ is_BCNF_syn R F := by
  rw [is_BCNF, is_BCNF_syn]
  constructor
  · intro h_sem X h_X
    have h_imp : implies_proj F R (X -> attr_closure_proj F X R) := by
      rw [implies_proj, attr_closure_proj]
      constructor
      · apply armstrong_sound
        exact Derives.trans attr_closure_sound (Derives.rfl Finset.inter_subset_left)
      · constructor
        · trivial
        · simp
    apply h_sem at h_imp
    simp [FunctionalDependency.is_trivial, is_superkey, implies_proj] at h_imp
    rcases h_imp with h_trivial | h_superkey
    · right
      rw [subset_antisymm_iff]
      constructor
      · trivial
      · exact Finset.subset_inter attr_closure_subset_impl h_X
    · left
      rcases h_superkey with ⟨_, ⟨h_imp, _⟩⟩
      rw [attr_closure_proj, Finset.inter_eq_right]
      apply attr_closure_complete
      apply armstrong_complete
      exact h_imp
  · intro h_syn f h_imp
    rw [implies_proj] at h_imp
    rcases h_imp with ⟨h_imp, ⟨h_lhs, h_rhs⟩⟩
    rcases h_syn h_lhs with h_rhs_eq_R | h_rhs_eq_lhs
    · right
      rw [is_superkey]
      constructor
      · trivial
      · constructor
        · rw [attr_closure_proj, Finset.inter_eq_right] at h_rhs_eq_R
          apply armstrong_sound
          apply Derives.trans attr_closure_sound (Derives.rfl h_rhs_eq_R)
        · simp_all
    · left
      rw [attr_closure_proj] at h_rhs_eq_lhs
      apply armstrong_complete at h_imp
      apply attr_closure_complete at h_imp
      have h_rhs_inter_r : f.rhs ∩ R = f.rhs := by simp_all
      have h_rhs_r_sub_ac_r : f.rhs ∩ R ⊆ attr_closure_impl F f.lhs ∩ R := Finset.inter_subset_inter_right h_imp
      rw [h_rhs_inter_r, h_rhs_eq_lhs] at h_rhs_r_sub_ac_r
      trivial

@[
  blueprint "definition:BCNF-violator"
]
def is_BCNF_violator (X R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
    X ⊆ R ∧ attr_closure_proj F X R ≠ R ∧ attr_closure_proj F X R ≠ X

instance decidable_is_BCNF_violator (X R : Finset α) (F : Finset (FunctionalDependency α)) :
  Decidable (is_BCNF_violator X R F) := by
  unfold is_BCNF_violator
  infer_instance

@[
  blueprint "definition:find-BCNF-violators"
]
def find_BCNF_violators (R : Finset α) (F : Finset (FunctionalDependency α)) : Finset (Finset α) :=
    R.powerset.filter (fun X => is_BCNF_violator X R F)

@[
  blueprint "lemma:decomposition-left-subset"
]
lemma R1_subset_R {X R : Finset α} {F : Finset (FunctionalDependency α)}
  (h_violator : is_BCNF_violator X R F) :
  attr_closure_proj F X R ⊂ R := by
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · exact attr_closure_proj_subset
  · rw [is_BCNF_violator] at h_violator
    rcases h_violator with ⟨_, h_xp_ne_R, _⟩
    trivial

@[
  blueprint "lemma:decomposition-right-subset"
]
lemma R2_subset_R {X R : Finset α} {F : Finset (FunctionalDependency α)}
  (h_violator : is_BCNF_violator X R F) :
  (R \ attr_closure_proj F X R) ∪ X ⊂ R := by
  rw [is_BCNF_violator] at h_violator
  rcases h_violator with ⟨h_X, _, h_xp_ne_X⟩
  rw [← Finset.sdiff_sdiff_eq_sdiff_union]
  · apply Finset.sdiff_ssubset
    · exact Finset.Subset.trans Finset.sdiff_subset attr_closure_proj_subset
    · rw [Finset.sdiff_nonempty]
      have h : X ⊂ attr_closure_proj F X R := by
        rw [Finset.ssubset_iff_subset_ne]
        constructor
        · exact subset_attr_closure_proj h_X
        · symm at h_xp_ne_X
          trivial
      rw [Finset.ssubset_def] at h
      rcases h with ⟨_, h⟩
      trivial
  · exact h_X

@[
  blueprint "definition:picker-valid"
]
def is_picker_valid (F : Finset (FunctionalDependency α)) (picker : Finset α → Option (Finset α)) : Prop :=
  ∀ {R : Finset α},
  let violators := find_BCNF_violators R F;
  violators = ∅ ∨ (∃ X, picker R = some X) ∧ (∀ {X}, picker R = some X → X ∈ violators)

@[
  blueprint "lemma:BCNF-step-cover"
]
lemma BCNF_step_cover {X R : Finset α} {F : Finset (FunctionalDependency α)}
  (h_violator : is_BCNF_violator X R F) :
  attr_closure_proj F X R ∪ ((R \ attr_closure_proj F X R) ∪ X) = R := by
  rw [Finset.union_comm, Finset.union_assoc]
  nth_rw 2 [Finset.union_comm]
  rw [← Finset.union_assoc, Finset.sdiff_union_self_eq_union, Finset.union_comm]
  have h_R_ac_eq_R : R ∪ attr_closure_proj F X R = R := by
    rw [Finset.union_eq_left]
    exact attr_closure_proj_subset
  rcases h_violator with ⟨h_X, _⟩
  rw [h_R_ac_eq_R, Finset.union_eq_right]
  trivial

@[
  blueprint "definition:BCNF-decompose"
]
def BCNF_decompose
  (R : Finset α) (F : Finset (FunctionalDependency α))
  (picker : Finset α → Option (Finset α)) : DecompositionTree R :=
    let violators := find_BCNF_violators R F
    if violators = ∅ then DecompositionTree.leaf R
    else match picker R with
      | none => DecompositionTree.leaf R
      | some X =>
        if h_X : X ∈ violators then
          have h_violator : is_BCNF_violator X R F := by
            dsimp [violators, find_BCNF_violators] at h_X
            exact (Finset.mem_filter.mp h_X).2
          let R₁ := attr_closure_proj F X R
          let R₂ := (R \ attr_closure_proj F X R) ∪ X
          DecompositionTree.node (Decomposition.mk R₁ R₂ (BCNF_step_cover h_violator)) (BCNF_decompose R₁ F picker) (BCNF_decompose R₂ F picker)
        else DecompositionTree.leaf R
termination_by R.card
decreasing_by
  · exact Finset.card_lt_card (R1_subset_R h_violator)
  · exact Finset.card_lt_card (R2_subset_R h_violator)

@[
  blueprint "lemma:BCNF-step-intersection"
]
lemma BCNF_step_intersection {X R : Finset α} {F : Finset (FunctionalDependency α)}
  (h_violator : is_BCNF_violator X R F) :
  attr_closure_proj F X R ∩ (X ∪ (R \ attr_closure_proj F X R)) = X := by
  rcases h_violator with ⟨h_X, _, _⟩
  rw [Finset.inter_union_distrib_left]
  have h_acX_eq_X : attr_closure_proj F X R ∩ X = X := by
    rw [Finset.inter_eq_right]
    exact subset_attr_closure_proj h_X
  rw [h_acX_eq_X, Finset.inter_sdiff_self]
  apply Finset.union_empty

@[
  blueprint "lemma:restrict-apply-mem"
]
lemma restrict_apply_mem {α : Type} (f : α →. μ) {S : Set α} {h_ST : S ⊆ f.Dom} {a : α} (h_a : a ∈ S) :
  f.restrict h_ST a = f a := by
  ext
  simp [PFun.mem_restrict, h_a]

@[
  blueprint "lemma:restrict-apply-non-mem"
]
lemma restrict_apply_non_mem {α : Type} (f : α →. μ) {S : Set α} {h_ST : S ⊆ f.Dom} {a : α} (h_a : a ∉ S) :
  f.restrict h_ST a = Part.none := by
  ext
  simp [PFun.mem_restrict, h_a]

@[
  blueprint "lemma:restrict-apply-correct"
]
lemma restrict_apply_correct {α : Type} (f : α →. μ) {S : Set α} (h_ST : S ⊆ f.Dom) :
  ∀ a : α, (a ∈ S → f.restrict h_ST a = f a) ∧ (a ∉ S → f.restrict h_ST a = Part.none) := by
  intro a
  constructor
  · intro h_a
    exact restrict_apply_mem f h_a
  · intro h_a
    exact restrict_apply_non_mem f h_a

@[
  blueprint "lemma:restrict-dom"
]
lemma restrict_dom {α μ : Type} (t : α →. μ) {S : Set α} (h_sub : S ⊆ t.Dom) :
    (t.restrict h_sub).Dom = S := by
    unfold PFun.restrict Part.restrict
    simp

@[
  blueprint "theorem:BCNF-decompose-step-is-lossless"
]
theorem BCNF_decompose_step_is_lossless {X R : Finset α} {F : Finset (FunctionalDependency α)}
  (h_violator : is_BCNF_violator X R F) :
  let d : Decomposition R := {
    left := attr_closure_proj F X R,
    right := (R \ attr_closure_proj F X R) ∪ X,
    cover := BCNF_step_cover h_violator
  };
  d.is_lossless F := by
  have h_X_subset_R₁ : X ⊆ attr_closure_proj F X R := subset_attr_closure_proj h_violator.1
  have h_X_subset_R₂ : X ⊆ (R \ attr_closure_proj F X R) ∪ X := Finset.subset_union_right
  simp [Decomposition.is_lossless]
  intro μ r h_r h_sat
  apply RelationInstance.ext
  · simp only [join, projection]
    rw [BCNF_step_cover h_violator, h_r]
  · apply Set.Subset.antisymm
    · rw [Set.subset_def]
      intro t h_t
      have h_R1_sub_R : ↑(attr_closure_proj F X R) ⊆ t.Dom := by
        rw [r.validSchema t h_t, Finset.coe_subset, h_r]
        exact attr_closure_proj_subset
      use t.restrict h_R1_sub_R
      constructor
      · use t
        constructor
        · trivial
        · exact restrict_apply_correct t h_R1_sub_R
      · have h_R2_sub_R : ↑((R \ attr_closure_proj F X R) ∪ X) ⊆ t.Dom := by
          rw [r.validSchema t h_t, Finset.coe_subset, h_r]
          exact Finset.union_subset Finset.sdiff_subset h_violator.1
        use t.restrict h_R2_sub_R
        constructor
        · use t
          constructor
          · trivial
          · exact restrict_apply_correct t h_R2_sub_R
        · intro a
          constructor
          · intro h_a
            symm
            exact restrict_apply_mem t h_a
          · constructor
            · intro h_a
              symm
              exact restrict_apply_mem t h_a
            · intro h_a
              rw [restrict_dom, restrict_dom, ← Finset.coe_union, BCNF_step_cover h_violator, ← h_r, ← r.validSchema t h_t] at h_a
              rw [Part.eq_none_iff']
              exact h_a
    · rw [Set.subset_def]
      intro t h_t
      simp only[join, projection] at h_t
      have h_X := h_violator.1
      rcases h_t with ⟨t₁, h_t₁, t₂, h_t₂, h_agree⟩
      have h_t₁_dom : t₁.Dom = attr_closure_proj F X R := by
        apply projectionDom r h_t₁
        rw [h_r]
        exact (R1_subset_R h_violator).1
      rcases h_t₁ with ⟨u, h_u, h_t₁_u⟩
      have h_t₂_dom : t₂.Dom = (R \ attr_closure_proj F X R) ∪ X := by
        apply projectionDom r h_t₂
        rw [h_r]
        exact (R2_subset_R h_violator).1
      rcases h_t₂ with ⟨v, h_v, h_t₂_v⟩
      rw [joinSingleT] at h_agree
      have h_agree_X : ∀ a ∈ X, u a = v a := by
        intro a h_a
        have h_a_in_R₁ := Finset.mem_of_subset h_X_subset_R₁ h_a
        have h_a_in_R₂ := Finset.mem_of_subset h_X_subset_R₂ h_a
        have h_t_eq : t₁ a = t₂ a := by
          rcases h_agree a with ⟨h_t₁_eq, h_t₂_eq, _⟩
          have h_a_in_dom₁ : a ∈ t₁.Dom := by simp_all
          have h_t₁_eq := h_t₁_eq h_a_in_dom₁
          have h_a_in_dom₂ : a ∈ t₂.Dom := by simp_all
          have h_t₂_eq := h_t₂_eq h_a_in_dom₂
          rw [← h_t₁_eq, ← h_t₂_eq]
        rcases h_t₁_u a with ⟨h_u_eq, _⟩
        rcases h_t₂_v a with ⟨h_v_eq, _⟩
        simp_all
      have h_f₁_dev : F ⊢ (X -> attr_closure_proj F X R) := by
        rw [attr_closure_proj]
        exact Derives.trans attr_closure_sound (Derives.rfl Finset.inter_subset_left)
      have h_f₁_imp : F ⊨ (X -> attr_closure_proj F X R) := armstrong_sound h_f₁_dev
      have h_f₁_holds : (X -> attr_closure_proj F X R : FunctionalDependency α).holds r := h_f₁_imp h_sat
      have h_agree_R₁ := h_f₁_holds h_u h_v h_agree_X
      have h_t_eq_v : t = v := by
        rw [PFun.ext_iff]
        intro a
        rw [← Part.ext_iff]
        by_cases h_a : a ∉ R
        · have h_a_not_in_doms : a ∉ t₁.Dom ∪ t₂.Dom := by simp_all [← Finset.coe_union, BCNF_step_cover h_violator]
          have h_t_none := (h_agree a).2.2 h_a_not_in_doms
          have h_a_not_in_v_dom : a ∉ v.Dom := by simp_all [r.validSchema v h_v]
          have h_v_none : v a = Part.none := Part.eq_none_iff'.mpr h_a_not_in_v_dom
          rw [h_v_none, h_t_none]
        · by_cases h_a' : a ∈ attr_closure_proj F X R
          · have h_a_in_dom₁ : a ∈ t₁.Dom := by simp_all
            have h_t_eq_t₁ := (h_agree a).1 h_a_in_dom₁
            have h_t₁_eq_u := (h_t₁_u a).1 h_a'
            have h_u_eq_v := h_agree_R₁ a h_a'
            rw [h_t_eq_t₁, h_t₁_eq_u, h_u_eq_v]
          · simp at h_a
            rw [← BCNF_step_cover h_violator, Finset.mem_union] at h_a
            have h_a' := h_a.resolve_left h_a'
            have h_a_in_dom₂ : a ∈ t₂.Dom := by simp_all
            have h_t_eq_t₂ := (h_agree a).2.1 h_a_in_dom₂
            have h_t₂_eq_v := (h_t₂_v a).1 h_a'
            simp_all
      simp_all

@[
  blueprint "theorem:BCNF-decompose-is-lossless"
]
theorem BCNF_decompose_is_lossless {R : Finset α} {F : Finset (FunctionalDependency α)}
  {picker : Finset α → Option (Finset α)}
  (h_picker_valid : is_picker_valid F picker) :
  (BCNF_decompose R F picker).is_lossless F := by
  induction R using BCNF_decompose.induct F picker with
  | case1 _ vlts =>
    unfold BCNF_decompose DecompositionTree.is_lossless
    simp_all [vlts]
  | case2 _ vlts =>
    unfold BCNF_decompose DecompositionTree.is_lossless
    simp_all [vlts]
  | case3 _ vlts _ _ _ _ h_X_vlt R₁ R₂ =>
    unfold BCNF_decompose DecompositionTree.is_lossless
    simp_all [vlts, R₁, R₂]
    exact BCNF_decompose_step_is_lossless h_X_vlt
  | case4 R _ h_vlt => next h_X' =>
    obtain ⟨_, h_X'⟩ := (h_picker_valid (R := R)).resolve_left h_vlt
    simp_all
    contradiction

@[
  blueprint "definition:all-are-BCNF"
]
def all_are_BCNF {R : Finset α} (T : DecompositionTree R) (F : Finset (FunctionalDependency α)) : Prop :=
  ∀ {L : Finset α}, L ∈ T.leaves → is_BCNF L F

@[
  blueprint "theorem:BCNF-decompose-leaves-are-BCNF"
]
theorem BCNF_decompose_leaves_are_BCNF {R : Finset α} {F : Finset (FunctionalDependency α)}
  {picker : Finset α → Option (Finset α)}
  (h_picker_valid : is_picker_valid F picker) :
  all_are_BCNF (BCNF_decompose R F picker) F := by
  induction R using BCNF_decompose.induct F picker with
  | case1 _ vlts => next h_no_vlt =>
    simp_all [vlts, all_are_BCNF, BCNF_decompose, DecompositionTree.leaves]
    rw [BCNF_sem_eq_syn]
    intro X h_X
    simp [find_BCNF_violators] at h_no_vlt
    have h_X_not_vlt := h_no_vlt h_X
    simp [is_BCNF_violator] at h_X_not_vlt
    apply h_X_not_vlt at h_X
    simp_all [imp_iff_not_or]
  | case2 _ vlts h_vlt => next h_pick_none =>
    simp_all [vlts]
    obtain ⟨h_pick_X, _⟩ := h_picker_valid.resolve_left h_vlt
    simp_all
  | case3 _ vlts =>
    simp_all [vlts]
    rw [BCNF_decompose, all_are_BCNF]
    simp_all
    intro L h_L
    rw [DecompositionTree.leaves, Finset.mem_union] at h_L
    rcases h_L with h_L₁ | h_L₂
    · next ih₁ _ =>
      rw [all_are_BCNF] at ih₁
      exact ih₁ h_L₁
    · next ih₂ =>
      rw [all_are_BCNF] at ih₂
      exact ih₂ h_L₂
  | case4 R _ h_vlt => next h_X' =>
    obtain ⟨_, h_X'⟩ := (h_picker_valid (R := R)).resolve_left h_vlt
    simp_all
    contradiction

end NF

end RM
