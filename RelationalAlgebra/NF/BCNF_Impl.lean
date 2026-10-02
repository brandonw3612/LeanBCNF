import RelationalAlgebra.NF.FuncDep
import RelationalAlgebra.NF.Closure
import RelationalAlgebra.NF.BCNF

namespace RM.NF

variable {α μ : Type} [DecidableEq α]

@[
  blueprint "def:find-bcnf-violator-exec"
  (title := /-- BCNF Violator Finder (Executable) -/)
  (statement := /--
    Given a list-based schema $R$ and a set of functional dependencies $F$, this function searches
    from the all sublists of $R$ to find a sublist $X$ that is a BCNF violator with respect to $R$
    and $F$. Since the computation of a list's sublists is deterministic, the result is also
    deterministic.
  -/)
]
def find_BCNF_violator_exec (R : List α) (F : Finset (FunctionalDependency α)) : Option (List α) :=
  R.sublists.find? (λ X => is_BCNF_violator X.toFinset R.toFinset F)

@[
  blueprint "def:find-bcnf-violators-exec-sound"
  (statement := /--
    If the executable BCNF violator finder returns a sublist $X$ of $R$, then $X$ is indeed a BCNF
    violator with respect to $R$ and $F$.
  -/)
]
lemma find_BCNF_violator_exec_sound {R : List α} {F : Finset (FunctionalDependency α)} {X : List α}
  (h : find_BCNF_violator_exec R F = some X) :
  is_BCNF_violator X.toFinset R.toFinset F := by
  simp [find_BCNF_violator_exec] at h
  apply of_decide_eq_true
  have h := List.find?_some h
  trivial

def sublist_via_subset (R : List α) (S : Finset α) : List α :=
  R.filter (λ a => a ∈ S)

lemma sublist_toFinset_eq_subset {R : List α} {S : Finset α} (h_sub : S ⊆ R.toFinset) :
  (sublist_via_subset R S).toFinset = S := by
  simp [sublist_via_subset, Finset.filter_mem_eq_inter]
  trivial

@[
  blueprint "lem:bcnf-exec-step-cover"
  (statement := /--
    The list-based version of \cref{lem:BCNF-step-cover}.
  -/)
]
lemma BCNF_exec_step_cover {R X : List α} {F : Finset (FunctionalDependency α)}
  (h_vlt : is_BCNF_violator X.toFinset R.toFinset F) :
  have R₁ := sublist_via_subset R (res_attr_closure F X.toFinset R.toFinset);
  have R₂ := sublist_via_subset R ((R.toFinset \ res_attr_closure F X.toFinset R.toFinset) ∪ X.toFinset);
  R₁.toFinset ∪ R₂.toFinset = R.toFinset := by
  intro R₁ R₂
  repeat rw [sublist_toFinset_eq_subset]
  apply BCNF_step_cover h_vlt
  · exact (R2_subset_R h_vlt).1
  · exact (R1_subset_R h_vlt).1

@[
  blueprint "def:bcnf-decomp-exec"
  (title := /-- BCNF Decomposition (Executable) -/)
  (statement := /--
    The executable list-based version of \cref{def:BCNF-decomp}. The only difference is that the
    BCNF violator picker is fixed to perform a deterministic search strategy described in
    \cref{def:find-bcnf-violator-exec}.
  -/)
]
def BCNF_decompose_exec (R : List α) (F : Finset (FunctionalDependency α)) :
  DecompositionTree R.toFinset :=
  let R_fs := R.toFinset
  match h_find : find_BCNF_violator_exec R F with
  | none => .leaf R_fs
  | some X =>
    let X_fs := X.toFinset
    have h_violator : is_BCNF_violator X.toFinset R_fs F := by
      simp [R_fs]
      exact find_BCNF_violator_exec_sound h_find
    let R₁ := sublist_via_subset R (res_attr_closure F X_fs R_fs)
    let R₂ := sublist_via_subset R ((R_fs \ res_attr_closure F X_fs R_fs) ∪ X_fs)
    let d := Decomposition.mk R₁.toFinset R₂.toFinset (BCNF_exec_step_cover h_violator)
    .node d (BCNF_decompose_exec R₁ F) (BCNF_decompose_exec R₂ F)
termination_by R.toFinset.card
decreasing_by
  · have h := R1_subset_R h_violator
    simp [R_fs] at h
    rw [sublist_toFinset_eq_subset h.1]
    exact Finset.card_lt_card h
  · have h := R2_subset_R h_violator
    simp [R_fs] at h
    rw [sublist_toFinset_eq_subset h.1]
    exact Finset.card_lt_card (R2_subset_R h_violator)

@[
  blueprint "def:list-based-picker"
  (title := /-- Deterministic BCNF Violator Picker -/)
  (statement := /--
    We define a deterministic BCNF violator picker that maps the strategy described in
    \cref{def:find-bcnf-violator-exec} to the general picker interface.
  -/)
]
noncomputable def list_based_picker (Universe : List α) (F : Finset (FunctionalDependency α))
  (R_finset : Finset α) : Option (Finset α) :=
  if R_finset ⊆ Universe.toFinset then
    let R_cur_list := sublist_via_subset Universe R_finset
    (find_BCNF_violator_exec R_cur_list F).map List.toFinset
  else
    let violators := find_BCNF_violators R_finset F
    if h_no_vlts : violators = ∅ then none
    else some (Classical.choose (Finset.nonempty_of_ne_empty h_no_vlts))

@[
  blueprint "lem:no-vlts-equiv"
  (title := /-- Equivalence of No Violators -/)
  (statement := /--
    The list-based finder returns no valid violators if and only if the set-based finder returns an
    empty set of violators.
  -/)
]
lemma no_vlts_equiv {R : List α} {F : Finset (FunctionalDependency α)} :
  find_BCNF_violator_exec R F = none ↔ find_BCNF_violators R.toFinset F = ∅ := by
  constructor
  · intro h_exec_none
    unfold find_BCNF_violator_exec at h_exec_none
    rw [Finset.eq_empty_iff_forall_notMem]
    intro X h_X
    rw [find_BCNF_violators, Finset.mem_filter, Finset.mem_powerset] at h_X
    obtain ⟨h_sub, h_violator⟩ := h_X
    let X_list := sublist_via_subset R X
    have h_mem_sublists : X_list ∈ R.sublists := List.mem_sublists.mpr List.filter_sublist
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

@[
  blueprint "lem:list-based-picker-valid"
  (title := /-- Deterministic BCNF Violator Picker Validity -/)
  (statement := /--
    The deterministic BCNF violator picker described in \cref{def:list-based-picker} is a valid
    picker according to \cref{def:picker-valid}.
  -/)
]
lemma list_based_picker_valid (Universe : List α) (F : Finset (FunctionalDependency α)):
  is_picker_valid F (list_based_picker Universe F) := by
  dsimp [is_picker_valid, list_based_picker]
  intro R_finset
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
        have h_X := Finset.Subset.trans h_violator.2.1 h_violator.1.1
        simp only [find_BCNF_violators, Finset.mem_filter, Finset.mem_powerset]
        rw [h_R] at h_violator h_X
        exact ⟨h_X, h_violator⟩
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

lemma sublist_eq_filter_toFinset {U R : List α}
  (h_eq : R = sublist_via_subset U R.toFinset)
  {S : Finset α} (hS : S ⊆ R.toFinset) :
  sublist_via_subset R S = sublist_via_subset U (sublist_via_subset R S).toFinset := by
  have h_finset : (sublist_via_subset R S).toFinset = S := sublist_toFinset_eq_subset hS
  rw [h_finset]
  calc sublist_via_subset R S
    _ = (U.filter (λ a => a ∈ R.toFinset)).filter (λ a => a ∈ S) := by
      unfold sublist_via_subset at *
      rw [← h_eq]
    _ = U.filter (λ a => a ∈ S) := filter_subset_eq_filter U hS
    _ = sublist_via_subset U S := by rfl

@[
  blueprint "lem:bcnf-decomp-equiv-core"
  (title := /-- Equivalence of BCNF Decomposition Implementations (Core) -/)
  (statement := /--
    Given a universe of attributes $U$ (usuallly the original schema at the beginning of the
    decomposition), a schema $R$ within $U$, and a set of functional dependencies $F$, the
    executable list-based BCNF decomposition algorithm is equivalent to the set-based BCNF
    decomposition algorithm, provided that the list-based picker (see \cref{def:list-based-picker})
    is used in the set-based algorithm. Throughout the set-based decomposition, the universe and the
    corresponding picker are globally fixed and the $R$, as the local schema to be decomposed,
    varies in the recursive calls.
  -/)
]
lemma BCNF_decompose_equiv_core {F : Finset (FunctionalDependency α)}
  (U R : List α) (h_sub : R.toFinset ⊆ U.toFinset)
  (h_eq : R = sublist_via_subset U R.toFinset) :
  let picker := list_based_picker U F;
  BCNF_decompose_exec R F = BCNF_decompose R.toFinset F picker := by
  intro picker
  induction R using BCNF_decompose_exec.induct F with
  | case1 R h_none =>
    have h_exec : BCNF_decompose_exec R F = .leaf R.toFinset := by
      unfold BCNF_decompose_exec
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
  | case2 R R_fs X h_find X_fs h_violator R₁ R₂ => next ih₁ ih₂ =>
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
    have h_R₁ := (R1_subset_R h_violator).1
    have h_R₂ := (R2_subset_R h_violator).1
    have h_thry : BCNF_decompose R.toFinset F picker =
      .node (Decomposition.mk R₁.toFinset R₂.toFinset (BCNF_exec_step_cover h_violator))
      (BCNF_decompose R₁.toFinset F picker) (BCNF_decompose R₂.toFinset F picker) := by
      rw [BCNF_decompose]
      split
      · next h_vlts_empty =>
        rw [← no_vlts_equiv, h_find] at h_vlts_empty
        contradiction
      · next h_vlts =>
        have h_valid_vlt := (list_based_picker_valid U F).resolve_left h_vlts
        have h_picker : picker R.toFinset = some X.toFinset := by
          unfold picker list_based_picker
          simp [h_sub, ← h_eq, h_find]
        simp [h_picker, h_valid_vlt.2 h_picker, BCNF_decompose_step]
        rw [sublist_toFinset_eq_subset h_R₁, sublist_toFinset_eq_subset h_R₂]
        trivial
    have h_R₁_sub_univ : R₁.toFinset ⊆ U.toFinset := by
      rw [sublist_toFinset_eq_subset h_R₁]
      exact Finset.Subset.trans h_R₁ h_sub
    have h_R₂_sub_univ : R₂.toFinset ⊆ U.toFinset := by
      rw [sublist_toFinset_eq_subset h_R₂]
      exact Finset.Subset.trans h_R₂ h_sub
    have h_R₁_eq_univ := sublist_eq_filter_toFinset h_eq h_R₁
    have h_R₂_eq_univ := sublist_eq_filter_toFinset h_eq h_R₂
    rw [h_exec, h_thry, ih₁ h_R₁_sub_univ h_R₁_eq_univ, ih₂ h_R₂_sub_univ h_R₂_eq_univ]

@[
  blueprint "thm:bcnf-decomp-equiv"
  (title := /-- Equivalence of BCNF Decomposition Implementations -/)
  (statement := /--
    Given a schema $R$ and a set of functional dependencies $F$, the executable list-based BCNF
    decomposition algorithm is equivalent to the set-based BCNF decomposition algorithm, provided
    that the list-based picker (see \cref{def:list-based-picker}) is used in the set-based algorithm.
  -/)
]
theorem BCNF_decompose_equiv
  {F : Finset (FunctionalDependency α)} {R : List α} :
  BCNF_decompose_exec R F = BCNF_decompose R.toFinset F (list_based_picker R F) := by
  apply BCNF_decompose_equiv_core R
  · exact Finset.Subset.refl _
  · unfold sublist_via_subset
    simp_all [List.filter_eq_self.mpr]

@[
  blueprint "thm:BCNF-decomp-exec-lossless"
  (title := /-- BCNF Decomposition Executable: Losslessness -/)
  (statement := /--
    The executable list-based BCNF decomposition algorithm is lossless, provided by the losslessness
    of the set-based algorithm (see \cref{thm:BCNF-decomp-lossless}) and the equivalence of the two
    implementations (see \cref{thm:bcnf-decomp-equiv}).
  -/)
]
theorem BCNF_decompose_exec_is_lossless {R : List α} {F : Finset (FunctionalDependency α)} :
  ∀ {r : RelationInstance α μ}, (h_r : r.schema = R.toFinset) → (h_sat : r.sat_res_imp F) →
  (BCNF_decompose_exec R F).is_lossless h_r := by
  rw [BCNF_decompose_equiv]
  apply BCNF_decompose_is_lossless
  exact list_based_picker_valid R F

@[
  blueprint "thm:BCNF-decompose-exec-leaves-BCNF"
  (title := /-- BCNF Decomposition Executable: BCNF Compliance -/)
  (statement := /--
    All terminal sub-schemas (leaves) in the executable list-based BCNF decomposition tree are in
    Boyce-Codd Normal Form (BCNF) with respect to the functional dependency set $F$, provided by the
    BCNF compliance of the set-based algorithm (see \cref{thm:BCNF-decompose-leaves-BCNF}) and the
    equivalence of the two implementations (see \cref{thm:bcnf-decomp-equiv}).
  -/)
]
theorem BCNF_decompose_exec_leaves_are_BCNF {R : List α} {F : Finset (FunctionalDependency α)} :
  ∀ {L : Finset α}, L ∈ (BCNF_decompose_exec R F).leaves → is_BCNF L F := by
  rw [BCNF_decompose_equiv]
  apply BCNF_decompose_leaves_are_BCNF
  exact list_based_picker_valid R F

end RM.NF
