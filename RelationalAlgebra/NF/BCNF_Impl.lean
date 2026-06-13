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

def sublist_via_subset (R : List α) (S : Finset α) : List α :=
  R.filter (λ a => a ∈ S)

lemma sublist_toFinset_eq_subset {R : List α} {R_sub : Finset α} (h_sub : R_sub ⊆ R.toFinset) :
  (sublist_via_subset R R_sub).toFinset = R_sub := by
  simp [sublist_via_subset, Finset.filter_mem_eq_inter]
  trivial

lemma BCNF_exec_step_cover {R X : List α} {F : Finset (FunctionalDependency α)}
  (h_vlt : is_BCNF_violator X.toFinset R.toFinset F) :
  have R₁ := sublist_via_subset R (attr_closure_proj F X.toFinset R.toFinset);
  have R₂ := sublist_via_subset R ((R.toFinset \ attr_closure_proj F X.toFinset R.toFinset) ∪ X.toFinset);
  R₁.toFinset ∪ R₂.toFinset = R.toFinset := by
  intro R₁ R₂
  rw [sublist_toFinset_eq_subset, sublist_toFinset_eq_subset]
  apply BCNF_step_cover
  · exact h_vlt
  · exact HasSSubset.SSubset.subset (R2_subset_R h_vlt)
  · exact HasSSubset.SSubset.subset (R1_subset_R h_vlt)

def BCNF_decompose_exec (R : List α) (F : Finset (FunctionalDependency α)) : DecompositionTree R.toFinset :=
  let R_finset := R.toFinset
  have h_R : R.toFinset = R_finset := by dsimp
  match h_find : find_BCNF_violator_exec R F with
  | none => .leaf R_finset
  | some X =>
    have h_violator : is_BCNF_violator X.toFinset R_finset F := by
      rw [← h_R]
      exact find_BCNF_violator_exec_sound h_find
    let R₁ := sublist_via_subset R (attr_closure_proj F X.toFinset R_finset)
    let R₂ := sublist_via_subset R ((R_finset \ attr_closure_proj F X.toFinset R_finset) ∪ X.toFinset)
    .node (Decomposition.mk R₁.toFinset R₂.toFinset (BCNF_exec_step_cover h_violator))
          (BCNF_decompose_exec R₁ F)
          (BCNF_decompose_exec R₂ F)
termination_by R.toFinset.card
decreasing_by
  · have h := R1_subset_R h_violator
    rw [← h_R] at h
    rw [sublist_toFinset_eq_subset (HasSSubset.SSubset.subset h)]
    exact Finset.card_lt_card h
  · have h := R2_subset_R h_violator
    rw [← h_R] at h
    rw [sublist_toFinset_eq_subset (HasSSubset.SSubset.subset h)]
    exact Finset.card_lt_card (R2_subset_R h_violator)

noncomputable def list_based_picker (Universe : List α) (F : Finset (FunctionalDependency α))
  (R_finset : Finset α) : Option (Finset α) :=
  if R_finset ⊆ Universe.toFinset then
    let R_cur_list := sublist_via_subset Universe R_finset
    (find_BCNF_violator_exec R_cur_list F).map List.toFinset
  else
    let violators := find_BCNF_violators R_finset F
    if h_no_vlts : violators = ∅ then none
    else some (Classical.choose (Finset.nonempty_of_ne_empty h_no_vlts))

lemma no_vlts_equiv {R : List α} {F : Finset (FunctionalDependency α)} :
  find_BCNF_violator_exec R F = none ↔ find_BCNF_violators R.toFinset F = ∅ := by
  constructor
  · intro h_exec_none
    unfold find_BCNF_violator_exec at h_exec_none
    rw [Finset.eq_empty_iff_forall_notMem]
    intro X h_X
    rw [find_BCNF_violators, Finset.mem_filter, Finset.mem_powerset] at h_X
    obtain ⟨h_sub, h_violator⟩ := h_X
    let X_list := R.filter (λ a => a ∈ X)
    have h_X_list_sublist : X_list.Sublist R := List.filter_sublist
    have h_mem_sublists : X_list ∈ R.sublists := List.mem_sublists.mpr h_X_list_sublist
    have h_X_list_eq : X_list.toFinset = X := sublist_toFinset_eq_subset h_sub
    have h_not_violator_bool := List.find?_eq_none.mp h_exec_none X_list h_mem_sublists
    have h_not_violator : ¬ is_BCNF_violator X_list.toFinset R.toFinset F := by
      apply of_decide_eq_false
      simp_all
    rw [h_X_list_eq] at h_not_violator
    contradiction
  · intro h_no_vlts
    simp [find_BCNF_violators, Finset.eq_empty_iff_forall_notMem] at h_no_vlts
    apply List.find?_eq_none.mpr
    intro X h_mem_sublists
    have h_sub : X.toFinset ⊆ R.toFinset := by
      rw [List.mem_sublists] at h_mem_sublists
      have h_sub' := h_mem_sublists.subset
      intro a ha
      simp_all [List.mem_toFinset]
      tauto
    simp_all

lemma list_based_picker_valid (Universe : List α) (F : Finset (FunctionalDependency α)):
  is_picker_valid F (list_based_picker Universe F) := by
  unfold is_picker_valid list_based_picker
  intro R_finset
  dsimp only
  split
  · next h_sub =>
    let R_list := sublist_via_subset Universe R_finset
    have h_R : R_list.toFinset = R_finset := by
      rw [sublist_toFinset_eq_subset h_sub]
    match h_find : find_BCNF_violator_exec R_list F with
    | none =>
      left
      rw [← h_R, ← no_vlts_equiv]
      trivial
    | some X_list =>
      right
      constructor
      · exact ⟨X_list.toFinset, rfl⟩
      · intro X h_eq
        simp only [Option.map_some, Option.some.injEq] at h_eq
        subst X
        have h_violator := find_BCNF_violator_exec_sound h_find
        simp only [find_BCNF_violators, Finset.mem_filter, Finset.mem_powerset]
        rw [h_R] at h_violator
        exact ⟨h_violator.1, h_violator⟩
  · next h_not_sub =>
    split
    · next h_empty =>
      left
      exact h_empty
    · next h_not_empty =>
      right
      have h_nonempty : (find_BCNF_violators R_finset F).Nonempty := Finset.nonempty_of_ne_empty h_not_empty
      constructor
      · exact ⟨Classical.choose h_nonempty, rfl⟩
      · intro X h_eq
        simp only [Option.some.injEq] at h_eq
        subst X
        exact Classical.choose_spec h_nonempty

lemma filter_subset_eq_filter {α : Type} [DecidableEq α] (L : List α) {S₁ S₂ : Finset α} (h_sub : S₂ ⊆ S₁) :
  (L.filter (λ a => a ∈ S₁)).filter (λ a => a ∈ S₂) = L.filter (λ a => a ∈ S₂) := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    by_cases h2 : hd ∈ S₂
    · have h1 : hd ∈ S₁ := h_sub h2
      simp [h1, h2, ih]
    · by_cases h1 : hd ∈ S₁
      · simp [h1, h2, ih]
      · simp [h1, h2, ih]

lemma sublist_eq_filter_toFinset {Universe R : List α}
  (h_eq : R = sublist_via_subset Universe R.toFinset)
  {S : Finset α} (hS : S ⊆ R.toFinset) :
  sublist_via_subset R S = sublist_via_subset Universe (sublist_via_subset R S).toFinset := by
  have h_finset : (sublist_via_subset R S).toFinset = S := sublist_toFinset_eq_subset hS
  rw [h_finset]
  calc sublist_via_subset R S
    _ = (Universe.filter (λ a => a ∈ R.toFinset)).filter (λ a => a ∈ S) := by
      unfold sublist_via_subset at *
      rw [← h_eq]
    _ = Universe.filter (λ a => a ∈ S) := filter_subset_eq_filter Universe hS
    _ = sublist_via_subset Universe S := by rfl

lemma BCNF_decompose_equiv_core {F : Finset (FunctionalDependency α)}
  (Universe R : List α) (h_sub : R.toFinset ⊆ Universe.toFinset)
  (h_eq : R = sublist_via_subset Universe R.toFinset) :
  let picker := list_based_picker Universe F;
  BCNF_decompose_exec R F = BCNF_decompose R.toFinset F picker := by
  intro picker
  induction R using BCNF_decompose_exec.induct F with
  | case1 R R_finset h_R h_none =>
    have h_exec : BCNF_decompose_exec R F = .leaf R.toFinset := by
      unfold BCNF_decompose_exec
      dsimp
      split
      · rfl
      · next X h_find =>
        rw [h_none] at h_find
        contradiction
    have h_thry : BCNF_decompose R.toFinset F picker = .leaf R.toFinset := by
      rw [no_vlts_equiv] at h_none
      unfold BCNF_decompose
      simp [h_none]
    rw [h_exec, h_thry]
  | case2 R R_finset h_R X h_find h_violator R₁ R₂ _ => next ih₁ ih₂ =>
    subst R_finset
    have h_exec : BCNF_decompose_exec R F =
      .node (Decomposition.mk R₁.toFinset R₂.toFinset (BCNF_exec_step_cover h_violator))
      (BCNF_decompose_exec R₁ F) (BCNF_decompose_exec R₂ F) := by
      rw [BCNF_decompose_exec]
      dsimp
      split
      · next h =>
        rw [h_find] at h
        contradiction
      · next X' h_find' =>
        simp [h_find] at h_find'
        subst X' R₁ R₂
        rfl
    have h_R₁ := HasSSubset.SSubset.subset (R1_subset_R h_violator)
    have h_R₂ := HasSSubset.SSubset.subset (R2_subset_R h_violator)
    have h_thry : BCNF_decompose R.toFinset F picker =
      .node (Decomposition.mk R₁.toFinset R₂.toFinset (BCNF_exec_step_cover h_violator))
      (BCNF_decompose R₁.toFinset F picker) (BCNF_decompose R₂.toFinset F picker) := by
      rw [BCNF_decompose]
      split
      · next h_vlts_empty =>
        rw [← no_vlts_equiv, h_find] at h_vlts_empty
        contradiction
      · next h_vlts =>
        have h_valid_vlt := (list_based_picker_valid Universe F).resolve_left h_vlts
        have h_picker : picker R.toFinset = some X.toFinset := by
          unfold picker list_based_picker
          simp [h_sub, ← h_eq, h_find]
        simp [h_picker, h_valid_vlt.2 h_picker]
        rw [sublist_toFinset_eq_subset h_R₁, sublist_toFinset_eq_subset h_R₂]
        trivial
    have h_R₁_sub_univ : R₁.toFinset ⊆ Universe.toFinset := by
      rw [sublist_toFinset_eq_subset h_R₁]
      exact Finset.Subset.trans h_R₁ h_sub
    have h_R₂_sub_univ : R₂.toFinset ⊆ Universe.toFinset := by
      rw [sublist_toFinset_eq_subset h_R₂]
      exact Finset.Subset.trans h_R₂ h_sub
    have h_R₁_eq_univ := sublist_eq_filter_toFinset h_eq h_R₁
    have h_R₂_eq_univ := sublist_eq_filter_toFinset h_eq h_R₂
    rw [h_exec, h_thry, ih₁ h_R₁_sub_univ h_R₁_eq_univ, ih₂ h_R₂_sub_univ h_R₂_eq_univ]

theorem BCNF_decompose_equiv
  {F : Finset (FunctionalDependency α)} {R : List α} :
  BCNF_decompose_exec R F = BCNF_decompose R.toFinset F (list_based_picker R F) := by
  apply BCNF_decompose_equiv_core R
  · exact Finset.Subset.refl _
  · unfold sublist_via_subset
    symm
    apply List.filter_eq_self.mpr
    intro a ha
    simp_all

theorem BCNF_decompose_exec_is_lossless {R : List α} {F : Finset (FunctionalDependency α)}
  : (BCNF_decompose_exec R F).is_lossless F := by
  rw [BCNF_decompose_equiv]
  apply BCNF_decompose_is_lossless
  exact list_based_picker_valid R F

theorem BCNF_decompose_exec_leaves_are_BCNF {R : List α} {F : Finset (FunctionalDependency α)} :
  all_are_BCNF (BCNF_decompose_exec R F) F := by
  rw [BCNF_decompose_equiv]
  apply BCNF_decompose_leaves_are_BCNF
  exact list_based_picker_valid R F

end RM.NF
