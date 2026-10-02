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
  blueprint "def:BCNF"
  (title := /-- Boyce-Codd Normal Form -/)
  (statement := /--
    A schema is in Boyce-Codd Normal Form (BCNF) with respect to a functional dependency set $F$ if
    for every functional dependency $X \to Y$ that is implied by $F$ and whose attributes are in the
    schema, either the dependency is trivial or the left-hand side ($X$) is a superkey.
  -/)
]
def is_BCNF (R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
    ∀ {f}, res_imp F f R → f.is_trivial ∨ is_superkey_syn f.lhs R F

@[
  blueprint "def:BCNF-syn"
  (title := /-- Boyce-Codd Normal Form (Syntactic) -/)
  (statement := /--
    We translate the BCNF definition to a computable form: A schema is in Boyce-Codd Normal Form
    (BCNF) with respect to a functional dependency set $F$ if for every subset of attributes $X$ of
    the schema, the closure of $X$ under $F$ restricted to the schema $R$ is either the entire
    schema $R$ or $X$ itself.
  -/)
]
def is_BCNF_syn (R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
    ∀ {X}, X ⊆ R → res_attr_closure F X R = R ∨ res_attr_closure F X R = X

@[
  blueprint "thm:BCNF-sem-eq-syn"
  (title := /-- BCNF Semantic/Syntactic Equivalence -/)
  (statement := /--
    We establish the equivalence between the semantic and syntactic definitions of BCNF: A schema is
    in Boyce-Codd Normal Form (BCNF) with respect to a functional dependency set $F$ if and only if
    it satisfies the syntactic condition.
  -/)
]
theorem BCNF_sem_eq_syn {R : Finset α} {F : Finset (FunctionalDependency α)} :
  is_BCNF R F ↔ is_BCNF_syn R F := by
  rw [is_BCNF, is_BCNF_syn]
  constructor
  · intro h_sem X h_X
    have h_imp : res_imp F (X -> res_attr_closure F X R) R := by
      simp_all [res_imp, res_attr_closure, ← armstrong_correct]
      exact Derives.trans attr_closure_sound (Derives.rfl Finset.inter_subset_left)
    apply h_sem at h_imp
    simp [FunctionalDependency.is_trivial] at h_imp
    rcases h_imp with h_trivial | h_superkey
    · right
      rw [subset_antisymm_iff]
      simp_all [subset_res_attr_closure h_X]
    · left
      rw [is_superkey_syn] at h_superkey
      simp_all
  · intro h_syn f h_imp
    rw [res_imp] at h_imp
    rcases h_imp with ⟨h_imp, ⟨h_lhs, h_rhs⟩⟩
    rcases h_syn h_lhs with h_rhs_eq_R | h_rhs_eq_lhs
    · right
      simp_all [is_superkey_syn]
    · left
      rw [res_attr_closure] at h_rhs_eq_lhs
      rw [FunctionalDependency.is_trivial, ← h_rhs_eq_lhs, Finset.subset_inter_iff]
      exact ⟨attr_closure_complete (armstrong_complete h_imp), h_rhs⟩

@[
  blueprint "def:BCNF-violator"
  (title := /-- BCNF Violator -/)
  (statement := /--
    An attribute set $X$ is a BCNF violator for a schema $R$ with respect to a functional dependency
    set $F$ if $X$ is a proper subset of $R$, the attribute closure of $X$ under $F$ restricted to
    $R$ is a proper subset of $R$, and $X$ is a proper subset of the closure. Formally,
    \[
      X^+_R \subsetneq R \quad \text{and} \quad X \subsetneq X^+_R.
    \]
  -/)
]
def is_BCNF_violator (X R : Finset α) (F : Finset (FunctionalDependency α)) : Prop :=
    res_attr_closure F X R ⊂ R ∧ X ⊂ res_attr_closure F X R

instance decidable_is_BCNF_violator (X R : Finset α) (F : Finset (FunctionalDependency α)) :
  Decidable (is_BCNF_violator X R F) := by
  unfold is_BCNF_violator
  infer_instance

@[
  blueprint "def:find-BCNF-violators"
  (title := /-- Find BCNF Violators -/)
  (statement := /--
    This function takes a schema $R$ and a set of functional dependencies $F$ as input, and returns
    the set of all subsets of $R$ that are BCNF violators for $R$ with respect to $F$.
  -/)
]
def find_BCNF_violators (R : Finset α) (F : Finset (FunctionalDependency α)) : Finset (Finset α) :=
    R.powerset.filter (fun X => is_BCNF_violator X R F)

@[
  blueprint "lem:BCNF-iff-no-violators"
  (statement := /--
    A schema $R$ is in Boyce-Codd Normal Form (BCNF) with respect to a set of functional dependencies
    $F$ if and only if there are no BCNF violators for $R$ with respect to $F$.
  -/)
]
lemma BCNF_iff_no_violators (R : Finset α) (F : Finset (FunctionalDependency α)) :
  is_BCNF R F ↔ find_BCNF_violators R F = ∅ := by
  simp [BCNF_sem_eq_syn, is_BCNF_syn, find_BCNF_violators]
  constructor
  · intro h_bcnf X h_X
    rw [is_BCNF_violator]
    apply h_bcnf at h_X
    by_contra h_contra
    simp [Finset.ssubset_iff_subset_ne] at h_contra
    tauto
  · intro h_no_vlt X h_X
    have h_X_not_vlt := h_no_vlt h_X
    unfold is_BCNF_violator at h_X_not_vlt
    by_cases h : X = R
    · left
      apply Finset.Subset.antisymm
      · exact res_attr_closure_subset
      · nth_rw 1 [← h]
        exact subset_res_attr_closure h_X
    · by_contra h_contra
      push_neg at h_contra
      simp [Finset.ssubset_iff_subset_ne] at h_X_not_vlt
      have h := h_X_not_vlt res_attr_closure_subset h_contra.1 (subset_res_attr_closure h_X)
      tauto

@[
  blueprint "lem:BCNF-step-cover"
  (statement := /--
    In a bianry BCNF decomposition over a schema $R$ with respect to a functional dependency set
    $F$, if $X$ is found to be a BCNF violator, then the union of the left sub-schema $R_1 = X^+_R$
    and the right sub-schema $R_2 = (R \setminus X^+_R) \cup X$ is equal to the original schema $R$.
    Formally,
    \[
      R_1 \cup R_2 = X^+_R \cup ((R \setminus X^+_R) \cup X) = R.
    \]
  -/)
]
lemma BCNF_step_cover {X R : Finset α} {F : Finset (FunctionalDependency α)}
  (h_violator : is_BCNF_violator X R F) :
  res_attr_closure F X R ∪ ((R \ res_attr_closure F X R) ∪ X) = R := by
  rw [Finset.union_comm, Finset.union_assoc]
  nth_rw 2 [Finset.union_comm]
  rw [← Finset.union_assoc, Finset.sdiff_union_self_eq_union, Finset.union_comm]
  have h_R_ac_eq_R : R ∪ res_attr_closure F X R = R := by
    rw [Finset.union_eq_left]
    exact res_attr_closure_subset
  rw [h_R_ac_eq_R, Finset.union_eq_right]
  exact Finset.Subset.trans h_violator.2.1 h_violator.1.1

@[
  blueprint "def:BCNF-decomp-step"
  (title := /-- BCNF Decomposition: Single Step -/)
  (statement := /--
    When a BCNF violator $X$ is found in a schema $R$ with respect to a functional dependency set
    $F$, we can perform a single step of BCNF decomposition. This step produces two sub-schemas:
    the left sub-schema $R_1 = X^+_R$ and the right sub-schema $R_2 = (R \setminus X^+_R) \cup X$. This
    function returns a `Decomposition` object (see \cref{def:decomp}) describing the original schema
    and the decomposed sub-schemas.
  -/)
]
def BCNF_decompose_step (X R : Finset α) (F : Finset (FunctionalDependency α))
  (h_violator : is_BCNF_violator X R F) : Decomposition R :=
    let R₁ := res_attr_closure F X R
    let R₂ := (R \ res_attr_closure F X R) ∪ X
    Decomposition.mk R₁ R₂ (BCNF_step_cover h_violator)

@[
  blueprint "lem:BCNF-decomp-left-subset"
  (statement := /--
    The left sub-schema $R_1 = X^+_R$ is a subset of the original schema $R$ by definition of the BCNF
    decomposition step.
  -/)
]
lemma R1_subset_R {X R : Finset α} {F : Finset (FunctionalDependency α)}
  (h_violator : is_BCNF_violator X R F) :
  res_attr_closure F X R ⊂ R := h_violator.1

@[
  blueprint "lem:BCNF-decomp-right-subset"
  (statement := /--
    The right sub-schema $R_2 = (R \setminus X^+_R) \cup X$ is a subset of the original schema $R$
    by definition of the BCNF decomposition step.
  -/)
]
lemma R2_subset_R {X R : Finset α} {F : Finset (FunctionalDependency α)}
  (h_violator : is_BCNF_violator X R F) :
  (R \ res_attr_closure F X R) ∪ X ⊂ R := by
  rw [is_BCNF_violator] at h_violator
  have ⟨_, h_xp_ne_X⟩ := h_violator
  have h_X := Finset.Subset.trans h_violator.2.1 h_violator.1.1
  rw [← Finset.sdiff_sdiff_eq_sdiff_union h_X]
  apply Finset.sdiff_ssubset
  · exact Finset.Subset.trans Finset.sdiff_subset res_attr_closure_subset
  · rw [Finset.sdiff_nonempty]
    rw [Finset.ssubset_def] at h_xp_ne_X
    exact h_xp_ne_X.2

@[
  blueprint "lem:BCNF-decomp-step-intersection"
  (statement := /--
    In a binary BCNF decomposition over a schema $R$ with respect to a functional dependency set
    $F$, if $X$ is found to be a BCNF violator, then the intersection of the left sub-schema $R_1 =
    X^+_R$ and the right sub-schema $R_2 = (R \setminus X^+_R) \cup X$ is equal to the original
    violator $X$. Formally,
    \[
      R_1 \cap R_2 = X^+_R \cap ((R \setminus X^+_R) \cup X) = X.
    \]
  -/)
]
lemma BCNF_step_intersection {X R : Finset α} {F : Finset (FunctionalDependency α)}
  (h_violator : is_BCNF_violator X R F) :
  let d := BCNF_decompose_step X R F h_violator;
  d.left ∩ d.right = X := by
  have h_X := Finset.Subset.trans h_violator.2.1 h_violator.1.1
  dsimp [BCNF_decompose_step]
  rw [Finset.inter_union_distrib_left]
  have h_acX_eq_X : res_attr_closure F X R ∩ X = X := by
    rw [Finset.inter_eq_right]
    exact subset_res_attr_closure h_X
  rw [h_acX_eq_X, Finset.inter_sdiff_self]
  simp

lemma restrict_apply_correct {α : Type} {f : α →. μ} {S : Set α} (h_ST : S ⊆ f.Dom) :
  ∀ (a : α), (a ∈ S → f.restrict h_ST a = f a) ∧ (a ∉ S → f.restrict h_ST a = Part.none) := by
  intro a
  constructor <;>
  {
    intro h_a
    ext
    simp [PFun.mem_restrict, h_a]
  }

lemma restrict_dom {α μ : Type} (t : α →. μ) {S : Set α} (h_sub : S ⊆ t.Dom) :
    (t.restrict h_sub).Dom = S := by
    unfold PFun.restrict Part.restrict
    simp

@[
  blueprint "thm:BCNF-decomp-step-lossless"
  (title := /-- BCNF Decomposition: Single Step Losslessness-/)
  (statement := /--
    The binary decomposition $d$ generated by a single step of BCNF decomposition is lossless with
    respect to any relation instance $r$ with schema $R$ that satisfies the functional dependency
    set $F$.
  -/)
]
theorem BCNF_decompose_step_is_lossless {X R : Finset α} {F : Finset (FunctionalDependency α)}
  (h_violator : is_BCNF_violator X R F) :
  ∀ {r : RelationInstance α μ}, (h_r : r.schema = R) → (h_sat : r.sat_res_imp F) →
  (BCNF_decompose_step X R F h_violator).is_lossless h_r := by
  set R₁ := res_attr_closure F X R
  set R₂ := (R \ res_attr_closure F X R) ∪ X
  dsimp [BCNF_decompose_step, Decomposition.is_lossless]
  have h_X := Finset.Subset.trans h_violator.2.1 h_violator.1.1
  have h_X_subset_R₁ : X ⊆ R₁ := subset_res_attr_closure h_X
  have h_X_subset_R₂ : X ⊆ R₂ := Finset.subset_union_right
  intro r h_r h_sat
  apply RelationInstance.ext
  · simp [join, projection]
    rw [BCNF_step_cover h_violator, h_r]
  · apply Set.Subset.antisymm
    · rw [Set.subset_def]
      intro t h_t
      have h_R1_sub_R : ↑R₁ ⊆ t.Dom := by
        rw [r.validSchema t h_t, Finset.coe_subset, h_r]
        exact res_attr_closure_subset
      let t1 := t.restrict h_R1_sub_R
      have h_R2_sub_R : ↑R₂ ⊆ t.Dom := by
        rw [r.validSchema t h_t, Finset.coe_subset, h_r]
        exact Finset.union_subset Finset.sdiff_subset h_X
      let t2 := t.restrict h_R2_sub_R
      use t1
      constructor
      · use t
        constructor
        · trivial
        · exact restrict_apply_correct h_R1_sub_R
      · use t2
        constructor
        · use t
          constructor
          · trivial
          · exact restrict_apply_correct h_R2_sub_R
        · intro a
          constructor
          · intro h_a
            symm
            exact ((restrict_apply_correct h_R1_sub_R) a).1 h_a
          · constructor
            · intro h_a
              symm
              exact ((restrict_apply_correct h_R2_sub_R) a).1 h_a
            · intro h_a
              repeat rw [restrict_dom] at h_a
              rw [← Finset.coe_union, BCNF_step_cover h_violator, ← h_r, ← r.validSchema t h_t] at h_a
              rw [Part.eq_none_iff']
              exact h_a
    · rw [Set.subset_def]
      intro t h_t
      simp only[join, projection] at h_t
      have h_X := Finset.Subset.trans h_violator.2.1 h_violator.1.1
      rcases h_t with ⟨t₁, h_t₁, t₂, h_t₂, h_agree⟩
      have h_t₁_dom : t₁.Dom = R₁ := by
        apply projectionDom r h_t₁
        rw [h_r]
        exact (R1_subset_R h_violator).1
      rcases h_t₁ with ⟨u, h_u, h_t₁_u⟩
      have h_t₂_dom : t₂.Dom = R₂ := by
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
        rw [← h_u_eq h_a_in_R₁, ← h_v_eq h_a_in_R₂]
        exact h_t_eq
      set f : FunctionalDependency α := X -> R₁
      have h_f_dev : F ⊢ f := by
        unfold f R₁ res_attr_closure
        exact Derives.trans attr_closure_sound (Derives.rfl Finset.inter_subset_left)
      have h_f_imp : F ⊨ f := armstrong_sound h_f_dev
      have h_f_res_imp : res_imp F f r.schema := by
        simp_all [res_imp, f, R₁]
        exact (R1_subset_R h_violator).1
      have h_f₁_holds : f.holds r := h_sat h_f_res_imp
      have h_agree_R₁ := h_f₁_holds h_u h_v h_agree_X
      have h_t_eq_v : t = v := by
        rw [PFun.ext_iff]
        intro a
        rw [← Part.ext_iff]
        by_cases h_a : a ∉ R
        · have h_a_not_in_doms : a ∉ t₁.Dom ∪ t₂.Dom := by
            simp_all [← Finset.coe_union, BCNF_step_cover h_violator, R₁, R₂]
          have h_t_none := (h_agree a).2.2 h_a_not_in_doms
          have h_a_not_in_v_dom : a ∉ v.Dom := by simp_all [r.validSchema v h_v]
          have h_v_none : v a = Part.none := Part.eq_none_iff'.mpr h_a_not_in_v_dom
          rw [h_v_none, h_t_none]
        · by_cases h_a' : a ∈ res_attr_closure F X R
          · have h_a_in_dom₁ : a ∈ t₁.Dom := by simp_all [R₁]
            have h_t_eq_t₁ := (h_agree a).1 h_a_in_dom₁
            have h_t₁_eq_u := (h_t₁_u a).1 h_a'
            have h_u_eq_v := h_agree_R₁ a h_a'
            rw [h_t_eq_t₁, h_t₁_eq_u, h_u_eq_v]
          · simp at h_a
            rw [← BCNF_step_cover h_violator, Finset.mem_union] at h_a
            have h_a' := h_a.resolve_left h_a'
            have h_a_in_dom₂ : a ∈ t₂.Dom := by simp_all [R₂]
            have h_t_eq_t₂ := (h_agree a).2.1 h_a_in_dom₂
            have h_t₂_eq_v := (h_t₂_v a).1 h_a'
            simp_all
      simp_all

@[
  blueprint "def:picker-valid"
  (statement := /--
    For a given BCNF violator picker function, we define a validity condition that ensures the
    picker function always returns a valid BCNF violator from the set of violators when there are
    any.
  -/)
]
def is_picker_valid (F : Finset (FunctionalDependency α)) (picker : Finset α → Option (Finset α)) : Prop :=
  ∀ {R : Finset α},
  let violators := find_BCNF_violators R F;
  violators = ∅ ∨ (∃ X, picker R = some X) ∧ (∀ {X}, picker R = some X → X ∈ violators)

@[
  blueprint "def:BCNF-decompose"
  (title := /-- BCNF Decomposition -/)
  (statement := /--
    We describe the complete BCNF decomposition algorithm as a recursive function that takes a
    schema $R$, a set of functional dependencies $F$ and a picker function $p$ as input. The
    function checks for BCNF violators in the schema $R$ with respect to $F$. If there are no
    violators, it returns a leaf node that contains the entire schema $R$ as the final decomposition
    tree. Otherwise, if the picker selects a valid BCNF violator $X$, it performs a single step of
    the procedure to obtain a binary decomposition object and recursively decomposes the left and
    right sub-schemas to obtain two sub-trees. These artifacts are then combined into a
    decomposition tree node, which is returned as the final result. We provide a termination
    measure based on the cardinality of the schema $R$ to ensure that the recursive calls eventually
    reach a base case, guaranteeing that the algorithm terminates. The decreasing measure is based
    on the fact that the left and right sub-schemas are proper subsets of the input schema.
  -/)
]
def BCNF_decompose (R : Finset α) (F : Finset (FunctionalDependency α))
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
          let R₁ := res_attr_closure F X R
          let R₂ := (R \ res_attr_closure F X R) ∪ X
          let d := BCNF_decompose_step X R F h_violator
          DecompositionTree.node d (BCNF_decompose R₁ F picker) (BCNF_decompose R₂ F picker)
        else DecompositionTree.leaf R
termination_by R.card
decreasing_by
  · exact Finset.card_lt_card (R1_subset_R h_violator)
  · exact Finset.card_lt_card (R2_subset_R h_violator)

@[
  blueprint "thm:BCNF-decomp-lossless-syn"
  (statement := /--
    We prove that the BCNF decomposition algorithm is lossless syntactically (see
    \cref{def:decomp-tree-lossless-syn}) by showing that all binary decomposition nodes throughout
    the entire decomposition tree are lossless with respect to any relation instance $r$ with schema
    $R$ that satisfies the functional dependency set $F$.
  -/)
]
theorem BCNF_decompose_is_lossless_syn {R : Finset α} {F : Finset (FunctionalDependency α)}
  {picker : Finset α → Option (Finset α)} (h_picker_valid : is_picker_valid F picker) :
  ∀ {r : RelationInstance α μ}, (h_r : r.schema = R) → (h_sat : r.sat_res_imp F) →
  (BCNF_decompose R F picker).is_lossless_syn h_r := by
  intro r h_r h_sat
  induction R using BCNF_decompose.induct F picker generalizing r with
  | case1 _ vlts =>
    unfold BCNF_decompose DecompositionTree.is_lossless_syn
    simp_all [vlts]
  | case2 _ vlts =>
    unfold BCNF_decompose DecompositionTree.is_lossless_syn
    simp_all [vlts]
  | case3 R vlts _ X _ _ h_X_vlt R₁ R₂ => next ih₁ ih₂ =>
    unfold BCNF_decompose DecompositionTree.is_lossless_syn
    simp_all [vlts, R₁, R₂]
    set t₁ := BCNF_decompose (res_attr_closure F X R) F picker
    set t₂ := BCNF_decompose ((R \ res_attr_closure F X R) ∪ X) F picker
    set r₁ := projection r R₁ (by simp [R₁, h_r, (R1_subset_R h_X_vlt).1])
    set r₂ := projection r R₂ (by simp [R₂, h_r, (R2_subset_R h_X_vlt).1])
    have h_r₁ : r₁.schema = R₁ := by simp [r₁, projection]
    have h_r₂ : r₂.schema = R₂ := by simp [r₂, projection]
    have h_r₁_sat : r₁.sat_res_imp F := by
      apply sat_res_imp_proj
      exact h_sat
    have h_r₂_sat : r₂.sat_res_imp F := by
      apply sat_res_imp_proj
      exact h_sat
    have ih₁ := ih₁ h_r₁ h_r₁_sat
    have ih₂ := ih₂ h_r₂ h_r₂_sat
    exact ⟨BCNF_decompose_step_is_lossless h_X_vlt h_r h_sat, ⟨ih₁, ih₂⟩⟩
  | case4 R _ h_vlt => next h_X' =>
    obtain ⟨_, h_X'⟩ := (h_picker_valid (R := R)).resolve_left h_vlt
    simp_all
    contradiction

@[
  blueprint "thm:BCNF-decomp-lossless"
  (title := /-- BCNF Decomposition: Losslessness -/)
  (statement := /--
    Using \cref{thm:decomp-tree-lossless-imp} as a bridge, we prove that the BCNF decomposition
    algorithm is lossless (see \cref{def:decomp-tree-lossless}). That is, for any relation instance
    $r$ with schema $R$ that satisfies the functional dependency set $F$, as we reconstruct from all
    terminal sub-instances in the decomposition according to the tree structure, we always obtain
    the original relation instance $r$.
  -/)
]
theorem BCNF_decompose_is_lossless {R : Finset α} {F : Finset (FunctionalDependency α)}
  {picker : Finset α → Option (Finset α)} (h_picker_valid : is_picker_valid F picker) :
  ∀ {r : RelationInstance α μ}, (h_r : r.schema = R) → (h_sat : r.sat_res_imp F) →
  (BCNF_decompose R F picker).is_lossless h_r := by
  intro r h_r h_sat
  exact DecompositionTree.is_lossless_imp h_r (BCNF_decompose_is_lossless_syn h_picker_valid h_r h_sat)

@[
  blueprint "thm:BCNF-decompose-leaves-BCNF"
  (title := /-- BCNF Decomposition: BCNF Compliance -/)
  (statement := /--
    All terminal sub-schemas (leaves) in the BCNF decomposition tree are in Boyce-Codd Normal Form
    (BCNF) with respect to the functional dependency set $F$.
  -/)
]
theorem BCNF_decompose_leaves_are_BCNF {R : Finset α} {F : Finset (FunctionalDependency α)}
  {picker : Finset α → Option (Finset α)}
  (h_picker_valid : is_picker_valid F picker) :
  ∀ {L : Finset α}, L ∈ (BCNF_decompose R F picker).leaves → is_BCNF L F := by
  induction R using BCNF_decompose.induct F picker with
  | case1 R vlts => next h_no_vlt =>
    simp_all [vlts, BCNF_decompose, DecompositionTree.leaves]
    rw [← BCNF_iff_no_violators] at h_no_vlt
    trivial
  | case2 _ vlts h_vlt => next h_pick_none =>
    simp_all [vlts]
    obtain ⟨h_pick_X, _⟩ := h_picker_valid.resolve_left h_vlt
    simp_all
  | case3 _ vlts =>
    rw [BCNF_decompose]
    simp_all [vlts]
    intro L h_L
    rw [DecompositionTree.leaves, Finset.mem_union] at h_L
    rcases h_L with h_L₁ | h_L₂
    · next ih₁ _ => exact ih₁ h_L₁
    · next ih₂ => exact ih₂ h_L₂
  | case4 R _ h_vlt => next h_X' =>
    obtain ⟨_, h_X'⟩ := (h_picker_valid (R := R)).resolve_left h_vlt
    simp_all
    contradiction

end NF

end RM
