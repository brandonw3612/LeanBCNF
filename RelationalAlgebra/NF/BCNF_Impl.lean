import RelationalAlgebra.NF.FuncDep
import RelationalAlgebra.NF.Closure
import RelationalAlgebra.NF.BCNF

namespace RM.NF

variable {α μ : Type} [DecidableEq α]

def find_BCNF_violator_exec (R : List α) (F : Finset (FunctionalDependency α)) : Option (List α) :=
  R.sublists.find? (λ X => is_BCNF_violator X.toFinset R.toFinset F)

lemma find_BCNF_violator_exec_sound {R : List α} {F : Finset (FunctionalDependency α)} {X : List α}
  (h : find_BCNF_violator_exec R F = some X) :
  is_BCNF_violator X.toFinset R.toFinset F := by
  simp [find_BCNF_violator_exec] at h
  apply of_decide_eq_true
  have h := List.find?_some h
  trivial

def BCNF_decompose_exec_core (R_list : List α) (R_finset : Finset α) (h_R : R_list.toFinset = R_finset) (F : Finset (FunctionalDependency α)) : DecompositionTree R_finset :=
  match h_find : find_BCNF_violator_exec R_list F with
  | none => .leaf R_finset
  | some X =>
    have h_violator : is_BCNF_violator X.toFinset R_finset F := by
      rw [← h_R]
      exact find_BCNF_violator_exec_sound h_find
    let R₁_finset := attr_closure_proj F X.toFinset R_finset
    let R₂_finset := (R_finset \ attr_closure_proj F X.toFinset R_finset) ∪ X.toFinset
    let R₁_list := R_list.filter (λ a => a ∈ R₁_finset)
    let R₂_list := R_list.filter (λ a => a ∈ R₂_finset)
    have h_R₁ : R₁_list.toFinset = R₁_finset := by
      simp [R₁_list, h_R, Finset.filter_mem_eq_inter]
      exact attr_closure_proj_subset
    have h_R₂ : R₂_list.toFinset = R₂_finset := by
      simp [R₂_list, h_R, Finset.filter_mem_eq_inter]
      unfold R₂_finset
      apply Finset.union_subset
      · simp
      · simp [is_BCNF_violator] at h_violator
        exact h_violator.1
    .node (Decomposition.mk R₁_finset R₂_finset (BCNF_step_cover h_violator))
          (BCNF_decompose_exec_core R₁_list R₁_finset h_R₁ F)
          (BCNF_decompose_exec_core R₂_list R₂_finset h_R₂ F)
termination_by R_finset.card
decreasing_by
  · exact Finset.card_lt_card (R1_subset_R h_violator)
  · exact Finset.card_lt_card (R2_subset_R h_violator)

def BCNF_decompose_exec (R : List α) (F : Finset (FunctionalDependency α)) : DecompositionTree R.toFinset :=
  BCNF_decompose_exec_core R R.toFinset (by simp) F

lemma BCNF_decompose_exec_core_lossless {R_list : List α} {R_finset : Finset α} (h_R : R_list.toFinset = R_finset) {F : Finset (FunctionalDependency α)} :
  (BCNF_decompose_exec_core R_list R_finset h_R F).is_lossless F := by
  induction R_list, R_finset, h_R using BCNF_decompose_exec_core.induct F with
  | case1 _ h_none =>
    unfold DecompositionTree.is_lossless BCNF_decompose_exec_core
    split
    · trivial
    · next h =>
      split at h
      · contradiction
      · next heq =>
        rw [h_none] at heq
        contradiction
  | case2 _ _ h_find _ R₁_finset R₂_finset R₁_list R₂_list =>
    next ih₁ ih₂ =>
    rw [BCNF_decompose_exec_core]
    split
    · next h_none =>
      rw [h_find] at h_none
      contradiction
    · next X' h_find' =>
      rw [DecompositionTree.is_lossless]
      constructor
      · apply BCNF_decompose_step_is_lossless
        apply find_BCNF_violator_exec_sound
        exact h_find'
      · simp [h_find'] at h_find
        subst X'
        unfold R₁_finset R₁_list at ih₁
        unfold R₂_finset R₂_list at ih₂
        exact ⟨ih₁, ih₂⟩

theorem BCNF_decompose_exec_lossless {R : List α} {F : Finset (FunctionalDependency α)} :
  (BCNF_decompose_exec R F).is_lossless F := by
  unfold BCNF_decompose_exec
  apply BCNF_decompose_exec_core_lossless

lemma all_are_BCNF_recursive {R R₁ R₂ : Finset α} {LT : DecompositionTree R₁} {RT : DecompositionTree R₂} {F : Finset (FunctionalDependency α)}
  (h_cover : R₁ ∪ R₂ = R)
  (h_LT : all_are_BCNF LT F) (h_RT : all_are_BCNF RT F) :
  all_are_BCNF (DecompositionTree.node (Decomposition.mk R₁ R₂ h_cover) LT RT) F := by
  simp_all [all_are_BCNF]
  intro L h_L
  rw [DecompositionTree.leaves, Finset.mem_union] at h_L
  rcases h_L with h_L₁ | h_L₂
  · exact h_LT h_L₁
  · exact h_RT h_L₂

lemma BCNF_decompose_exec_core_leaves_are_BCNF {R_list : List α} {R_finset : Finset α} (h_R : R_list.toFinset = R_finset) {F : Finset (FunctionalDependency α)} :
  all_are_BCNF (BCNF_decompose_exec_core R_list R_finset h_R F) F := by
  induction R_list, R_finset, h_R using BCNF_decompose_exec_core.induct F with
  | case1 R_list h_none =>
    unfold all_are_BCNF BCNF_decompose_exec_core DecompositionTree.leaves
    simp_all
    split
    · simp [BCNF_sem_eq_syn, is_BCNF_syn]
      simp [find_BCNF_violator_exec] at h_none
      intro X h_X
      let x := R_list.filter (λ a => a ∈ X)
      have h_x : x.toFinset = X := by
        simp [x, Finset.filter_mem_eq_inter]
        exact h_X
      have h_sublist : x.Sublist R_list := by simp [x]
      apply h_none at h_sublist
      simp [is_BCNF_violator, h_x] at h_sublist
      tauto
    · next h =>
      split at h
      · contradiction
      · next h_find =>
        rw [h_none] at h_find
        contradiction
  | case2 _ _ h_find h_violator R₁_finset R₂_finset R₁_list R₂_list =>
    next ih₁ ih₂ =>
    unfold BCNF_decompose_exec_core
    split
    · next h_none =>
      rw [h_find] at h_none
      contradiction
    · next X' h_find' =>
      simp [h_find'] at h_find
      subst X'
      apply all_are_BCNF_recursive (h_cover := BCNF_step_cover h_violator)
      · unfold R₁_finset R₁_list at ih₁
        exact ih₁
      · unfold R₂_finset R₂_list at ih₂
        exact ih₂

end RM.NF
