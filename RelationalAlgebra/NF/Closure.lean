import RelationalAlgebra.NF.FuncDep

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold

import Mathlib.Data.PFun

import Architect

namespace RM

variable {α μ : Type} [dec_eq : DecidableEq α]

namespace NF

/-- A functional dependency `f` is implied by a set of functional dependencies `F` if every relation
    instance satisfying all dependencies in `F` also satisfies `f`.
-/
@[
  blueprint "def:fd-imp"
  (title := /-- FD Implication -/)
  (statement := /--
    A functional dependency $f$ is implied by a set of functional dependencies $F$ if every relation
    instance satisfying all dependencies in $F$ also satisfies $f$, written as $F \vDash f$.
  -/)
]
def implies (F : Finset (FunctionalDependency α)) (f : FunctionalDependency α) : Prop :=
  ∀ {μ : Type} {r : RelationInstance α μ}, r.sat F → f.holds r

/-- Notation for implication of functional dependencies. -/
infix:50 " ⊨ " => implies

/-- A functional dependency `f` is implied by `F` restricted to schema `R`, if `F ⊨ f` and every
    attribute in the left-hand side and right-hand side of `f` belongs to `R`. -/
@[
  blueprint "def:res-imp"
  (title := /-- Restricted FD Implication -/)
  (statement := /--
    A functional dependency $f$ is implied by $F$ restricted to schema $R$, if $F \vDash f$ and
    every attribute in the left-hand side and right-hand side of $f$ belongs to $R$, written as
    $F \vDash_R f$.
  -/)
]
def res_imp (F : Finset (FunctionalDependency α)) (f : FunctionalDependency α)
  (R : Finset α) : Prop :=
  F ⊨ f ∧ f.lhs ⊆ R ∧ f.rhs ⊆ R

end NF

/-- A relation instance `r` satisfies the restricted implications of `F` on its schema if it
    satisfies every dependency `f` such that `F ⊨ f` and both sides of `f` are contained in
    `r`'s schema. -/
@[
  blueprint "def:sat-res-imp"
  (title := /-- Relation Instance Satisfies Restricted Implications -/)
  (statement := /--
    A relation instance $r$ satisfies the restricted implications of $F$ on its schema if it
    satisfies every dependency $f$ such that $F \vDash f$ and both sides of $f$ are contained in
    $r$'s schema.
  -/)
]
def RelationInstance.sat_res_imp (r : RelationInstance α μ)
  (F : Finset (NF.FunctionalDependency α)) : Prop :=
  ∀ {f}, NF.res_imp F f r.schema → f.holds r

namespace NF

omit dec_eq in
/-- If a relation instance `r` satisfies every dependency implied by `F` restricted to its schema,
    then its projection onto any subschema `S` also satisfies every dependency implied by `F`
    restricted to `S`. -/
@[
  blueprint "lem:sat-res-imp-proj"
  (title := /-- Restricted Satisfaction Is Preserved by Projection -/)
  (statement := /--
    If a relation instance $r$ satisfies every dependency implied by $F$ restricted to its schema,
    then its projection onto any subschema $S$ also satisfies every dependency implied by $F$
    restricted to $S$.
  -/)
  (proof := /--
    Let $r$ be a relation instance with schema $R$ and let $S \subseteq R$. Assume that $r$
    satisfies all restricted implications induced by $F$ on its own schema. We show that the
    projection $r|_S$ satisfies all restricted implications induced by $F$ on $S$.

    Take an arbitrary functional dependency $f : X \to Y$ such that $F \vDash_S f$. To prove that
    $f$ holds in the projected relation $r|_S$, let $t_1, t_2$ be tuples of $r|_S$ such that they
    agree on the left-hand side of $f$. Because $S \subseteq R$, each tuple in the projection comes
    from some tuple in $r$. We write these preimages as $\bar t_1, \bar t_2$. For every attribute
    $a \in X$, since $a \in S$, the projected tuples agree on $a$ exactly when the original tuples
    agree on $a$. Therefore, $\bar t_1|_X = \bar t_2|_X$.

    Now the hypothesis that $r$ satisfies restricted implications says that every dependency implied
    by $F$ whose attributes lie in $R$ holds on $r$. Since $X \subseteq S \subseteq R$ and
    $Y \subseteq S \subseteq R$, the dependency $f$ is applicable to $r$. Hence,
    $\bar t_1|_Y = \bar t_2|_Y$.

    Finally, because $Y \subseteq S$, the agreement of the original tuples on the right-hand side
    transfers directly to the projected tuples. Thus, $t_1|_Y = t_2|_Y$. So $f$ holds in $r|_S$.
  -/)
]
lemma sat_res_imp_proj {r : RelationInstance α μ} {F : Finset (NF.FunctionalDependency α)}
  {S : Finset α} (h_sub : S ⊆ r.schema) :
  r.sat_res_imp F → (projection r S h_sub).sat_res_imp F := by
  unfold projection RelationInstance.sat_res_imp
  intro h_r f h_f t₁ t₂ h_t₁ h_t₂ h_eq
  simp at h_t₁ h_t₂ h_f
  intro b h_b
  obtain ⟨tt₁, ⟨h_tt₁, h_t₁⟩⟩ := h_t₁
  obtain ⟨tt₂, ⟨h_tt₂, h_t₂⟩⟩ := h_t₂
  have h_b' := Finset.mem_of_subset h_f.2.2 h_b
  rw [(h_t₁ b).1 h_b', (h_t₂ b).1 h_b']
  have h_match : ∀ a ∈ f.lhs, tt₁ a = tt₂ a := by
    intro a h_a
    have h_eq := h_eq a h_a
    have h_a' := Finset.mem_of_subset h_f.2.1 h_a
    rw [← (h_t₁ a).1 h_a', ← (h_t₂ a).1 h_a', h_eq]
  have h_f_r : res_imp F f r.schema := by
    obtain ⟨h_imp, h_lhs, h_rhs⟩ := h_f
    exact ⟨
      h_imp,
      fun a h_a => h_sub (h_lhs h_a),
      fun a h_a => h_sub (h_rhs h_a)
    ⟩
  exact h_r h_f_r h_tt₁ h_tt₂ h_match b h_b

/-- Armstrong's Axioms for derivation of functional dependencies. -/
@[
  blueprint "def:armstrong"
  (title := /-- Armstrong's Axioms -/)
  (statement := /--
    The derivation of functional dependencies is denoted by $F \vdash f$.
    Armstrong's axioms for functional dependencies consist of the following inference rules:
    \begin{itemize}
      \item \textit{Membership}: if a functional dependency is in the set, then it can be derived
            immediately.
      \item \textit{Reflexivity}: if $Y \subseteq X$, then $F \vdash X \rightarrow Y$.
      \item \textit{Augmentation}: if $F \vdash X \rightarrow Y$, then $F \vdash XZ \rightarrow YZ$
            for any $Z$.
      \item \textit{Transitivity}: if $F \vdash X \rightarrow Y$ and $F \vdash Y \rightarrow Z$,
            then $F \vdash X \rightarrow Z$.
    \end{itemize}
  -/)
]
inductive Derives (F : Finset (FunctionalDependency α)) : FunctionalDependency α → Prop where
  /-- Membership: If a functional dependency is in the set, then it can be derived. -/
  | mem : ∀ {f}, f ∈ F → Derives F f
  /-- Reflexivity: if `Y` is a subset of `X`, then `F ⊢ X -> Y`. -/
  | rfl : ∀ {X Y : Finset α}, Y ⊆ X → Derives F (X -> Y)
  /-- Augmentation: if `F ⊢ X -> Y`, then `F ⊢ XZ -> YZ` for any `Z`. -/
  | aug : ∀ {X Y Z : Finset α}, Derives F (X -> Y) → Derives F (X ∪ Z -> Y ∪ Z)
  /-- Transitivity: if `F ⊢ X -> Y` and `F ⊢ Y -> Z`, then `F ⊢ X -> Z`. -/
  | trans : ∀ {X Y Z : Finset α}, Derives F (X -> Y) → Derives F (Y -> Z) → Derives F (X -> Z)

/-- Notation for derivation of functional dependencies. -/
infix:50 " ⊢ " => Derives

/-- Armstrong's axioms additional rule: union.
    If `F ⊢ X -> Y` and `F ⊢ X -> Z`, then `F ⊢ X -> YZ`.
-/
@[
  blueprint "thm:der-union"
  (title := /-- Armstrong's Axioms Additional Rule: Union -/)
  (statement := /--
    If $F \vdash X \rightarrow Y$ and $F \vdash X \rightarrow Z$, then $F \vdash X \rightarrow YZ$.
  -/)
  (proof := /--
    \begin{enumerate}
        \item Apply the \textit{augmentation} rule to $F \vdash X \rightarrow Y$ with $X$ to obtain
              $F \vdash X \rightarrow XY$.
        \item Apply the \textit{augmentation} rule to $F \vdash X \rightarrow Z$ with $Y$ to obtain
              $F \vdash XY \rightarrow YZ$.
        \item Apply the \textit{transitivity} rule to the two derived dependencies to obtain
              $F \vdash X \rightarrow YZ$.
    \end{enumerate}
  -/)
]
theorem derives_union {F : Finset (FunctionalDependency α)} {X Y Z : Finset α} :
  F ⊢ (X -> Y) → F ⊢ (X -> Z) → F ⊢ (X -> Y ∪ Z) := by
  intro h_der_x_y h_der_x_z
  have h_der_x_xx_xy : F ⊢ (X ∪ X -> Y ∪ X) := Derives.aug h_der_x_y
  rw [Finset.union_idempotent X] at h_der_x_xx_xy
  have h_der_x_xy_yz : F ⊢ (Y ∪ X -> Y ∪ Z) := by
    apply Derives.aug (Z := Y) at h_der_x_z
    simp_all [Finset.union_comm]
  exact Derives.trans h_der_x_xx_xy h_der_x_xy_yz

/-- Armstrong's axioms additional rule: decomposition.
    If `F ⊢ X -> YZ`, then `F ⊢ X -> Y` and `F ⊢ X -> Z`.
-/
@[
  blueprint "thm:der-decomp"
  (title := /-- Armstrong's Axioms Additional Rule: Decomposition -/)
  (statement := /--
    If $F \vdash X \rightarrow YZ$, then $F \vdash X \rightarrow Y$ and $F \vdash X \rightarrow Z$.
  -/)
  (proof := /--
    Using the \textit{reflexivity} rule, we derive $F \vdash YZ \rightarrow Y$ and
    $F \vdash YZ \rightarrow Z$ because $Y$ and $Z$ are subsets of $YZ$. Then we apply the
    \textit{transitivity} rule to obtain $F \vdash X \rightarrow Y$ and $F \vdash X \rightarrow Z$
    from $F \vdash X \rightarrow YZ$.
  -/)
]
theorem derives_decomposition {F : Finset (FunctionalDependency α)} {X Y Z : Finset α} :
  F ⊢ (X -> Y ∪ Z) → F ⊢ (X -> Y) ∧ F ⊢ (X -> Z) := by
  intro h_der_x_yz
  constructor
  · have h_der_yz_y : F ⊢ (Y ∪ Z -> Y) := Derives.rfl Finset.subset_union_left
    exact Derives.trans h_der_x_yz h_der_yz_y
  · have h_der_yz_z : F ⊢ (Y ∪ Z -> Z) := Derives.rfl Finset.subset_union_right
    exact Derives.trans h_der_x_yz h_der_yz_z

/-- Armstrong's axioms additional rule: pseudotransitivity.
    If `F ⊢ X -> Y` and `F ⊢ YZ -> W`, then `F ⊢ XZ -> W`.
-/
@[
  blueprint "thm:der-psdtran"
  (title := /-- Armstrong's Axioms Additional Rule: Pseudotransitivity -/)
  (statement := /--
    If $F \vdash X \rightarrow Y$ and $F \vdash YZ \rightarrow W$, then $F \vdash XZ \rightarrow W$.
  -/)
  (proof := /--
    Apply the \textit{augmentation} rule to $F \vdash X \rightarrow Y$ with $Z$ to obtain
    $F \vdash XZ \rightarrow YZ$. Then apply the \textit{transitivity} rule to this derived
    functional dependency and $F \vdash YZ \rightarrow W$ to get $F \vdash XZ \rightarrow W$.
  -/)
]
theorem derives_pseudotransitivity {F : Finset (FunctionalDependency α)} {X Y Z W : Finset α} :
  F ⊢ (X -> Y) → F ⊢ (Y ∪ Z -> W) → F ⊢ (X ∪ Z -> W) := by
  intro h_der_x_y h_der_yz_w
  apply Derives.aug at h_der_x_y
  exact Derives.trans h_der_x_y h_der_yz_w

/-- Soundness of Armstrong's Axioms: if `F ⊢ f`, then `F ⊨ f`. -/
@[
  blueprint "thm:arms-sound"
  (title := /-- Soundness of Armstrong's Axioms -/)
  (statement := /--
    If a functional dependency $f$ can be derived from a set of functional dependencies $F$ using
    Armstrong's axioms, then $f$ is implied by $F$.
  -/)
  (proof := /--
    By induction on the derivation of $f$ from $F$ using Armstrong's axioms, we show case by case in
    this proof that if $F \vdash f$, then $F \vDash f$. Specifically in each case, with the
    precondition that the functional dependency $f$ can be derived from FD set $F$ ($F \vdash f$),
    we unfold the definition of implication ($F \vDash f$) and show that for any relation instance
    $r$ that satisfies all dependencies in $F$, $f$ also holds on $r$.
    \begin{itemize}
      \item \textit{Membership}:
            As $f$ is in $F$, and $r$ satisfies all dependencies in $F$, $f$ must hold on $r$.
      \item \textit{Reflexivity}:
            Since $Y$ is a subset of $X$, for any two tuples that agree on $X$, they must also agree
            on $Y$. Thus, $f$ holds on $r$.
      \item \textit{Augmentation}:
            With precondition that $X \rightarrow Y$ holds on $r$, we split the membership of
            attribute $s$ in the target set $YZ$ into two cases: $s$ is in $Y$ or $s$ is in $Z$.
            \begin{itemize}
              \item If $s$ is in $Y$, to show the agreement of tuples on $s$, we apply the
                    precondition that $X \rightarrow Y$ holds on $r$. Now we need to show that the
                    tuples agree on all attributes in $X$. Since in the precondition we have that
                    the tuples agree on $XZ$, they must also agree on $X$ as $X$ is a subset of $XZ$.
                    Thus, we conclude that the tuples agree on $s$.
              \item If $s$ is in $Z$, we apply the precondition that the tuples agree on $XZ$ again
                    to conclude that they also agree on $Z$, and thus they agree on $s$.
            \end{itemize}
      \item \textit{Transitivity}:
            To show that the tuples agree on $Z$, we apply the precondition that $Y \rightarrow Z$
            holds on $r$. Now we need to show that the tuples agree on $Y$. We apply the
            precondition that $X \rightarrow Y$ holds on $r$ to align the objective with the
            precondition that the tuples agree on $X$.
    \end{itemize}
  -/)
]
theorem armstrong_sound {F : Finset (FunctionalDependency α)} {f : FunctionalDependency α} :
  F ⊢ f → F ⊨ f := by
  intro h_der μ r h_sat
  induction h_der with
  | mem h_in => exact h_sat h_in
  | rfl h_y_subset_x =>
    intro t₁ t₂ h_t₁ h_t₂ h_eq_x s h_s_in_y
    have h_s_in_x := h_y_subset_x h_s_in_y
    exact h_eq_x s h_s_in_x
  | aug h_der_xy h_xy_holds =>
    intro _ _ h_t₁ h_t₂ h_eq_xz s h_s_in_yz
    cases Finset.mem_union.mp h_s_in_yz with
    | inl h_s_in_y =>
      apply h_xy_holds h_t₁ h_t₂
      repeat simp_all
    | inr h_s_in_z =>
      apply h_eq_xz
      simp_all
  | trans h_der_xy h_der_yz h_xy_holds h_yz_holds =>
    intro t₁ t₂ h_t₁ h_t₂ h_eq_x s h_s_in_z
    apply h_yz_holds h_t₁ h_t₂
    · intro a h_a_in_y
      exact h_xy_holds h_t₁ h_t₂ h_eq_x a h_a_in_y
    · trivial

/-- `X⁺`: the closure of an attribute set `X` with respect to an FD set `F`.
    This is the weak set-based definition.
-/
@[
  blueprint "def:attr-clsr-weak"
  (title := /-- Attribute Closure (Weak) -/)
  (statement := /--
    The closure of an attribute set $X$, denoted by $X^+$, with respect to a set of functional
    dependencies $F$, is the set of all attributes that can be functionally determined by $X$ using
    the dependencies in $F$. Formally,
    \[
        X^+ = \left\{ a \mid F \vDash X \rightarrow \left\{ a \right\} \right\}.
    \]
  -/)
]
def attr_closure_weak (F : Finset (FunctionalDependency α)) (X : Finset α) : Set α :=
  {a | F ⊨ (X -> {a})}

/-- The filtered set of FDs whose left-hand sides are subsets of `X`. -/
@[
  blueprint "def:left-filter"
  (title := /-- Left-Filter of FD Set -/)
  (statement := /--
    We define a function $L(X)$ on a given attribute set $X$ by filtering the FD set $F$ to keep
    exactly those dependencies whose left-hand side is a subset of $X$. Formally,
    \[
        L(X) = \left\{ fd \in F \mid fd.lhs \subseteq X \right\}.
    \]
  -/)
]
def left_filter (F : Finset (FunctionalDependency α)) (X : Finset α)
  : Finset (FunctionalDependency α) :=
  {fd ∈ F | fd.lhs ⊆ X}

/--
  A single step in the iterative computation of attribute-set closure.
  For each FD in the left-filtered set, we add its right-hand side to the current set.
  (If `α -> β ∈ F` and `α ⊆ X`, then we may add `β` to `X`.)
-/
@[
  blueprint "def:attr-clsr-step"
  (title := /-- Attribute Closure (Single Step) -/)
  (statement := /--
    A single step in the iterative computation of attribute-set closure. For every FD in the
    left-filtered set, we add its right-hand side to the attribute set. Formally,
    \[
        X' = X \cup \bigcup_{\alpha \rightarrow \beta \in F, \alpha \subseteq X} \beta.
    \]
  -/)
]
def attr_closure_impl_step (F : Finset (FunctionalDependency α)) (X : Finset α) : Finset α :=
  X ∪ (left_filter F X).sup (λ fd => fd.rhs)

/-- Auxiliary definition for iterating the closure step. -/
@[
  blueprint "def:attr-clsr-iter"
  (title := /-- Attribute Closure (Iteration) -/)
  (statement := /--
    We iterate the single closure step to compute the full closure. This is written as $X^n$, where
    $n$ is the number of iterations and $X^0 = X$.
  -/)
]
def ac_seq (F : Finset (FunctionalDependency α)) (X : Finset α) (n : ℕ) : Finset α :=
  (attr_closure_impl_step F)^[n] X

/-- Simply unfold the iteration by one layer. -/
@[
  blueprint "lem:attr-clsr-iter-succ"
  (title := /-- Attribute Closure (Iteration Successor) -/)
  (statement := /--
    Unfolding the iteration of attribute closure sequence by one layer, we have:
    \[
        X^{n+1} = X^n \cup \bigcup_{\alpha \rightarrow \beta \in F, \alpha \subseteq X^n} \beta.
    \]
  -/)
  (proof := /-- This proof is trivial. -/)
]
lemma ac_seq_succ (F : Finset (FunctionalDependency α)) (X : Finset α) (n : ℕ) :
  ac_seq F X (n + 1) = attr_closure_impl_step F (ac_seq F X n) := by
  simp [ac_seq, Function.iterate_succ_apply']

/-- Implementation of the attribute closure algorithm, where we iterate the single step |F| times
    (in the worst case).
-/
@[
  blueprint "def:attr-clsr-impl"
  (title := /-- Attribute Closure (Full Implementation) -/)
  (statement := /--
    We iterate the single step of the attribute closure algorithm $|F|$ times (in the worst case) to
    obtain the full closure. Formally, we have:
    \[
        X^+ = X^{|F|}.
    \]
  -/)
]
def attr_closure_impl (F : Finset (FunctionalDependency α)) (X : Finset α) : Finset α :=
  ac_seq F X F.card

/-- Soundness of a single step of the attribute set closure computation. -/
@[
  blueprint "lem:attr-clsr-step-sound"
  (title := /-- Attribute Closure (Step Soundness) -/)
  (statement := /--
    Every single step iterated in the attribute closure algorithm is sound. Formally,
    \[
        F \vdash (X \to X').
    \]
  -/)
  (proof := /--
    First, we apply the \textit{union} rule of Armstrong's axioms to split the result of the single
    step into two parts: the original attribute set $X$ and the union of the right-hand sides of the
    dependencies in the left-filtered set. Then, we show that both parts can be derived from $F$:
    \begin{itemize}
      \item For $X$, we can derive $X \to X$ using the \textit{reflexivity} rule, trivially.
      \item For $\bigcup_{\alpha \rightarrow \beta \in F, \alpha \subseteq X} \beta$, we first
            unfold the filter to show that the filter is a subset of $F$. Next, we show that for any
            subset $S'$ of the filtered set $S$, we can derive
            $X \rightarrow \bigcup_{\alpha \rightarrow \beta \in S'} \beta$. To prove this, we use
            induction on $S'$.

            In the base case where $S'$ is empty, we can derive $X \rightarrow \emptyset$ using the
            \textit{reflexivity} rule, trivially.

            In the inductive case, we have that the target holds for a strict subset $S''$ of $S'$,
            and we need to show that as we introduce a new FD $fd \in S$ into $S''$, the target
            still holds for the updated $S''$.

            We again apply the \textit{union} rule to split the target into two parts: the
            right-hand side of $fd$ and the union of the right-hand sides of the dependencies in the
            original $S''$.

            For the first part, we can derive $X \rightarrow fd.rhs$ using the \textit{transitivity}
            rule by introducing the left-hand side of $fd$ as the bridge. Specifically, since $fd$
            is in the left-filtered set, its left-hand side is a subset of $X$, so we can derive
            $X \rightarrow fd.lhs$ using the \textit{reflexivity} rule. Then, $fd$ itself can also
            be derived from $F$ since it is in $F$.

            The second part is exactly the inductive hypothesis, so it is proved trivially.

            Finally, we apply the above result to $S$ to conclude this case.
    \end{itemize}
    With both parts derived, we arrive at the conclusion that $F \vdash (X \to X')$.
  -/)
]
lemma attr_closure_step_sound {F : Finset (FunctionalDependency α)} {X : Finset α} :
  F ⊢ (X -> attr_closure_impl_step F X) := by
  unfold attr_closure_impl_step
  apply derives_union
  · apply Derives.rfl
    simp
  · set S := left_filter F X
    have h_s_subset_F : S ⊆ F := by simp [left_filter, S]
    have h_s'_sup : ∀ S' ⊆ S, F ⊢ (X -> S'.sup (λ fd => fd.rhs)) := by
      intro s' h_s'_sub_s
      induction s' using Finset.induction with
      | empty => simp [Derives.rfl]
      | insert fd S'' h_fd_not_in_s'' h_ih =>
        simp [Finset.sup_insert]
        obtain ⟨h_fd, h_s''⟩ := Finset.insert_subset_iff.mp h_s'_sub_s
        apply derives_union
        · simp [S, left_filter] at h_fd
          apply Derives.trans
          · exact Derives.rfl h_fd.2
          · exact Derives.mem h_fd.1
        · exact h_ih h_s''
    apply h_s'_sup S
    simp

/-- Soundness of the attribute closure algorithm full implementation. -/
@[
  blueprint "thm:attr-clsr-impl-sound"
  (title := /-- Attribute Closure (Full Implementation Soundness) -/)
  (statement := /--
    The full implementation of the attribute closure algorithm is sound. Formally,
    \[
        F \vdash (X \to X^+).
    \]
  -/)
  (proof := /--
    With the soundness proof of a single step of the attribute closure algorithm, we show the
    soundness of the full implementation by induction on the number of iterations \textit{i.e.}, the
    cardinality of the FD set $F$.

    In the base case where $F = \emptyset$, the closure of any attribute set is itself, and we can
    derive $X \to X$ using the \textit{reflexivity} rule, trivially.

    In the inductive case, we assume that the attribute closure implementation is sound for any FD
    set with $|F| = n$, and we apply the single step soundness to show that the attribute closure
    implementation is also sound for any FD set with $|F| = n + 1$.
  -/)
]
theorem attr_closure_sound {F : Finset (FunctionalDependency α)} {X : Finset α} :
  F ⊢ (X -> attr_closure_impl F X) := by
  unfold attr_closure_impl
  induction F.card with
  | zero => simp [ac_seq, Derives.rfl]
  | succ n ih =>
    apply Derives.trans
    · exact ih
    · simp [ac_seq_succ,attr_closure_step_sound]

/-- An attribute set is a subset of its closure. -/
@[
  blueprint "lem:subset-attr-clsr-impl"
  (title := /-- Subset of Attribute Closure (Full Implementation) -/)
  (statement := /--
    An attribute set is a subset of its closure. Formally,
    \[
        X \subseteq X^+.
    \]
  -/)
  (proof := /--
    With the subset relation between an attribute set and its single-step closure, we can show that
    the attribute set is also a subset of the full closure by induction on the number of iterations
    in the full implementation.

    In the base case where $F = \emptyset$, the closure of any attribute set is itself, so the
    subset relation holds trivially.

    In the inductive case, we assume that $X \subseteq X^n$ for any FD set with $|F| = n$, and we
    apply the subset relation for a single step to show that $X \subseteq X^{n+1}$ for any FD set
    with $|F| = n + 1$.
  -/)
]
lemma attr_closure_subset_impl {F : Finset (FunctionalDependency α)} {X : Finset α} :
  X ⊆ attr_closure_impl F X := by
  unfold attr_closure_impl
  induction F.card with
    | zero => exact fun a ha => ha
    | succ n ih =>
      simp [ac_seq_succ, attr_closure_impl_step]
      exact Finset.Subset.trans ih Finset.subset_union_left

/--
  When the closure set stablizes at some point, it remains the same for all subsequent iterations.
-/
@[
  blueprint "lem:stab-attr-clsr-iter"
  (title := /-- Stability of Attribute Closure Iteration -/)
  (statement := /--
    When the closure set stablizes at some point, it remains the same for all subsequent iterations.
    Formally, if $X^{k+1} = X^k$ for some $k$, then $X^n = X^k$ for all $n \geq k$.
  -/)
  (proof := /--
    With $n \geq k$, we can express $n$ as $k + d$ for some $d \geq 0$. We show the stability of the
    closure set by induction on $d$.

    In the base case where $d = 0$, we have $n = k$, so the stability holds trivially.

    In the inductive case, we assume that $X^{k+d} = X^k$ for some $d \geq 0$, and we need to show
    that $X^{k+(d+1)} = X^k$. Here, we use $X^{k+d}$ as the bridge to connect $X^{k+(d+1)}$ and
    $X^k$. Combining the inductive hypothesis and the pre-condition that $X^{k+1} = X^k$, we show
    that $X^{k+(d+1)}$ is equal to $X^k$.
  -/)
]
lemma seq_fixed_of_eq {F : Finset (FunctionalDependency α)} {X : Finset α} {k n : ℕ}
  (h : ac_seq F X (k + 1) = ac_seq F X k) (h_n : k ≤ n) :
  ac_seq F X n = ac_seq F X k := by
  have h_step : attr_closure_impl_step F (ac_seq F X k) = ac_seq F X k := by simp_all [← ac_seq_succ]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h_n
  induction d with
  | zero => rfl
  | succ d ih =>
    have heq : k + (d + 1) = k + d + 1 := by omega
    simp [heq, ac_seq_succ, ih, h_step]

/-- The set of filtered dependencies cannot grow indefinitely. -/
@[
  blueprint "lem:fixed-point-left-filter"
  (title := /-- Existence of Fixed Point on Left-Filter -/)
  (statement := /--
    The set of filtered dependencies cannot grow indefinitely. Formally, if the left-filtered set is
    non-empty at the beginning, then there exists some $k < |F|$ such that the left-filtered set at
    step $k$ is the same as the left-filtered set at step $k + 1$:
    \[
        L(X) \neq \emptyset \implies \exists k < |F|, L(X^k) = L(X^{k+1}).
    \]
  -/)
  (proof := /--
    We prove this by contradiction. In this proof, we assume for the sake of contradiction that for
    every step $k < |F|$, the left-filtered set at step $k$ is different from the left-filtered set
    at step $k + 1$, \textit{i.e.}, $L(X^k) ≠ L(X^{k+1})$.

    First, we prove that for every $i < |F|$, $L(X^i) \subset L(X^{i+1})$. Specifically, if
    $fd \in L(X^i)$, then $fd.lhs \subseteq X^i \subseteq X^{i+1}$. Hence, $fd \in L(X^{i+1})$.
    Combining this with the contradiction assumption that $L(X^k) ≠ L(X^{k+1})$ for all $k < |F|$,
    we conclude that $L(X^i) \subset L(X^{i+1})$ for every $i < |F|$.

    Next, having the strict subset relation between the left-filtered sets for every step, we show
    that the cardinality of the left-filtered set at each step is strictly increasing,
    \textit{i.e.}, $|L(X)| = |L(X^0)| < |L(X^1)| < |L(X^2)| < \cdots < |L(X^{|F|})|$.

    By induction on $|F|$, we show that $|L(X^{|F|})|$ is at least $|F| + 1$ using the inequality
    chain above. However, for every $i \leq |F|$, $L(X^i)$ is a subset of $F$, so $|L(X^i)|$ is at
    most $|F|$. This leads to a contradiction, and we conclude that there must exist some $k < |F|$
    such that $L(X^k) = L(X^{k+1})$.
  -/)
]
lemma exists_filtered_eq {F : Finset (FunctionalDependency α)} {X : Finset α}
  (h_pos : 0 < (left_filter F (ac_seq F X 0)).card) :
  ∃ k < F.card, left_filter F (ac_seq F X k) = left_filter F (ac_seq F X (k + 1)) := by
  by_contra h_contra
  push_neg at h_contra
  have h_strict
    : ∀ i < F.card, left_filter F (ac_seq F X i) ⊂ left_filter F (ac_seq F X (i + 1)) := by
    intro i hi
    have h_ne := h_contra i hi
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro fd hfd
      simp_all [left_filter]
      obtain ⟨_, h⟩ := hfd
      rw [ac_seq_succ, attr_closure_impl_step]
      exact Finset.Subset.trans h Finset.subset_union_left
    · exact h_ne
  have h_le : (left_filter F (ac_seq F X F.card)).card ≤ F.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h_bound : F.card + 1 ≤ (left_filter F (ac_seq F X F.card)).card := by
    induction F.card with
    | zero => tauto
    | succ k ih =>
      have hk : k < F.card := by
        apply Nat.lt_of_succ_le
        apply Nat.le_trans ih
        apply Finset.card_le_card
        exact Finset.filter_subset _ _
      have h_sub := h_strict k hk
      have h_lt := Finset.card_lt_card h_sub
      omega
  omega

/-- The closure reaches a fixed point at step `|F|`. -/
@[
  blueprint "lem:fixed-point-attr-clsr-iter"
  (title := /-- Fixed Point of Attribute Closure Iteration -/)
  (statement := /--
    The closure reaches a fixed point at (or before) step $|F|$. Formally,
    \[
        X^{|F|+n} = X^{|F|}.
    \]
  -/)
  (proof := /--
    We prove this by case analysis on whether the left-filtered set is empty at the beginning or not.

    In the first case where the left-filtered set is empty, we show that the closure does not change
    after the first step ($X^1 = X^0$). Next, using \cref{lem:stab-attr-clsr-iter}, we show that for
    all $n \geq 0$, $X^n = X^0$. Therefore, we conclude that $X^{|F|+n} = X^0 = X^{|F|}$.

    In the second case where the left-filtered set is non-empty, we apply
    \cref{lem:fixed-point-left-filter} to show that there exists some $k < |F|$ such that
    $L(X^k) = L(X^{k+1})$. We put these terms in $X^{k+1}$ and $X^{k+2}$ to obtain
    $X^{k+2} = X^{k+1}$, and then we apply \cref{lem:stab-attr-clsr-iter} to show that for all
    $n \geq k + 1$, $X^n = X^{k+1}$. Finally, we show that $k + 1 \leq |F| \leq |F| + n$, and that
    $X^{|F|+n} = X^{k+1} = X^{|F|}$.
  -/)
]
lemma seq_stabilizes {F : Finset (FunctionalDependency α)} {X : Finset α} {n : ℕ} :
  ac_seq F X (F.card + n) = ac_seq F X F.card := by
  by_cases h_zero : (left_filter F (ac_seq F X 0)).card = 0
  · have h_empty : left_filter F (ac_seq F X 0) = ∅ := Finset.card_eq_zero.mp h_zero
    have h_eq : ac_seq F X 1 = ac_seq F X 0 := by
      change attr_closure_impl_step F X = X
      rw [ac_seq, Function.iterate_zero, id, left_filter] at h_empty
      simp [attr_closure_impl_step, left_filter, h_empty]
    have h_all : ∀ n ≥ 0, ac_seq F X n = ac_seq F X 0 := by
      intro n hn
      exact seq_fixed_of_eq h_eq hn
    rw [h_all (F.card + n) (Nat.zero_le _), h_all F.card (Nat.zero_le _)]
  · have h_pos : 0 < (left_filter F (ac_seq F X 0)).card := Nat.pos_of_ne_zero h_zero
    obtain ⟨k, hk_lt, hk_eq⟩ := exists_filtered_eq h_pos
    have h_eq : ac_seq F X (k + 2) = ac_seq F X (k + 1) := by
      simp_all [ac_seq_succ]
      nth_rw 1 [attr_closure_impl_step]
      rw [← hk_eq]
      simp [attr_closure_impl_step]
    have h_all : ∀ n ≥ k + 1, ac_seq F X n = ac_seq F X (k + 1) := by
      intro n hn
      exact seq_fixed_of_eq h_eq hn
    have h1 : k + 1 ≤ F.card := hk_lt
    have h2 : k + 1 ≤ F.card + n := by omega
    rw [h_all (F.card + n) h2, h_all F.card h1]

/-- The computed closure is closed under `F`. -/
@[
  blueprint "lem:attr-clsr-impl-closed"
  (title := /-- Attribute Closure Is Closed -/)
  (statement := /--
    The computed closure is closed under the set of functional dependencies $F$: for every
    functional dependency $X \to Y$ in $F$, if $X \subseteq X^+$, then $Y \subseteq X^+$.
  -/)
  (proof := /--
    Let $X \to Y$ be a functional dependency in $F$. We have $X^{|F| + 1} = X^{|F|} = X^+$ by
    \cref{lem:fixed-point-attr-clsr-iter}. If $X \subseteq X^+$, then we have that
    $X^{|F|+1} = X^+ \cup \bigcup_{\alpha \rightarrow \beta \in L(X^+)} \beta$, where $Y$ is a
    subset of the second term in the union. Hence, we show that $Y \subseteq X^{|F|+1} = X^+$.
  -/)
]
lemma impl_closed {F : Finset (FunctionalDependency α)} {X : Finset α} :
  (attr_closure_impl F X).is_closed_under F := by
  set XP := attr_closure_impl F X
  intro fd hfd h_lhs
  have h_fixed_point : attr_closure_impl_step F XP = XP := by
    simp [XP, attr_closure_impl, ← ac_seq_succ]
    exact seq_stabilizes
  have h_step : fd.rhs ⊆ attr_closure_impl_step F XP := by
    intro a ha
    simp [attr_closure_impl_step, left_filter, Finset.mem_union, Finset.mem_sup]
    exact Or.inr ⟨fd, ⟨hfd, h_lhs⟩, ha⟩
  rw [h_fixed_point] at h_step
  exact h_step

/-- First row: all attributes in the tuple are true. -/
def t_all_true (U : Finset α) : α →. Bool :=
  fun a => {
    Dom := a ∈ U
    get := fun _ => true
  }

/-- Second row: only attributes in the closure S are true. -/
def t_closure (U S : Finset α) : α →. Bool :=
  fun a => {
    Dom := a ∈ U
    get := fun _ => decide (a ∈ S)
  }

/-- A counterexample relation instance that satisfies all FDs in `F` but violates the FD `X -> Y`
    when `Y` is not a subset of the closure of `X`.
-/
@[
  blueprint "def:ctrex"
  (title := /-- Counterexample Relation Instance -/)
  (statement := /--
    A counterexample relation instance that satisfies all functional dependencies in $F$ but
    violates the functional dependency $X \to Y$ when $Y$ is not a subset of the closure of $X$.
    Formally, we define a relation instance $r$ with schema $U$, a subschema $S$, and two tuples:
    \[
        r = \left\{ t_{\text{all true}}, t_{\text{closure}} \right\},
    \]
    where $t_{\text{all true}}(a) = \text{true}$ for all $a \in U$,
    and $t_{\text{closure}}(a) = \text{true}$ if and only if $a \in S$.
  -/)
]
def counterexample_relation (U S : Finset α) : RelationInstance α Bool where
  schema := U
  tuples := {t_all_true U, t_closure U S}
  validSchema := by
    intro t ht
    simp [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    ext x
    rcases ht with rfl | rfl;
    · rfl
    · rfl

/-- If `F` is a set of FDs such that all FDs in `F` have their attributes contained in `U`, and `S`
    is closed under `F`, then the counterexample relation instance satisfies all FDs in `F`.
-/
@[
  blueprint "lem:ctrex-sat"
  (title := /-- Counterexample Relation Instance Satisfies FD Set -/)
  (statement := /--
    Given attribute sets $U$ and $S$, and a set of functional dependencies $F$ such that all FDs in
    $F$ have their attributes contained in $U$, and $S$ is closed under $F$, then the counterexample
    relation instance satisfies all FDs in $F$.
  -/)
]
lemma counterexample_sat {U S : Finset α} {F : Finset (FunctionalDependency α)}
  (h_F_sub_U : ∀ fd ∈ F, fd.lhs ⊆ U ∧ fd.rhs ⊆ U) (h_closed : S.is_closed_under F) :
  (counterexample_relation U S).sat F := by
  intro fd hfd
  have hU := h_F_sub_U fd hfd
  intro t1 t2 ht1 ht2 h_agree_lhs
  simp [counterexample_relation, Set.mem_insert_iff, Set.mem_singleton_iff] at ht1 ht2
  rcases ht1 with rfl | rfl <;> rcases ht2 with rfl | rfl
  -- Case 1: t1 = t_all_true, t2 = t_all_true
  · simp
  -- Case 2: t1 = t_all_true, t2 = t_closure
  · have h_lhs_sub_S : fd.lhs ⊆ S := by
      intro a ha
      have h_eq := h_agree_lhs a ha
      simp [t_all_true, t_closure] at h_eq
      have h_val := congr_fun h_eq (hU.1 ha)
      exact of_decide_eq_true h_val.symm
    have h_rhs_sub_S : fd.rhs ⊆ S := h_closed fd hfd h_lhs_sub_S
    intro a ha
    simp [t_all_true, t_closure, h_rhs_sub_S ha]
  -- Case 3: t1 = t_closure, t2 = t_all_true
  · have h_lhs_sub_S : fd.lhs ⊆ S := by
      intro a ha
      have h_eq := h_agree_lhs a ha
      simp [t_all_true, t_closure] at h_eq
      have h_val := congr_fun h_eq (hU.1 ha)
      exact of_decide_eq_true h_val
    have h_rhs_sub_S : fd.rhs ⊆ S := h_closed fd hfd h_lhs_sub_S
    intro a ha
    simp [t_all_true, t_closure, h_rhs_sub_S ha]
  -- Case 4: t1 = t_closure, t2 = t_closure
  · simp

/-- If the FD X -> Y holds on the counterexample relation instance, then Y must be a subset of S. -/
@[
  blueprint "lem:subset-closure-if-fd-holds"
  (statement := /--
    If the functional dependency $X \to Y$ holds on the counterexample relation instance and
    $X \subseteq S$, then $Y \subseteq S$.
  -/)
]
lemma subset_closure_if_holds {U X Y S : Finset α}
  (h_X_sub_S : X ⊆ S) (h_Y_sub_U : Y ⊆ U)
  (h_holds : (X -> Y : FunctionalDependency α).holds (counterexample_relation U S)) :
  Y ⊆ S := by
  let t₁ := t_all_true U
  let t₂ := t_closure U S
  have h_t₁ : t₁ ∈ (counterexample_relation U S).tuples := Set.mem_insert _ _
  have h_t₂ : t₂ ∈ (counterexample_relation U S).tuples := Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have h_agree_on_x : ∀ a ∈ X, t₁ a = t₂ a := by
    intro a ha_in_x
    simp [t₁, t₂, t_all_true, t_closure, h_X_sub_S ha_in_x]
  have h_agree_on_y : ∀ b ∈ Y, t₁ b = t₂ b := h_holds h_t₁ h_t₂ h_agree_on_x
  intro y hy
  have h_y_in_u := h_Y_sub_U hy
  have h_eq := h_agree_on_y y hy
  simp [t₁, t₂, t_all_true, t_closure] at h_eq
  have h_val := congr_fun h_eq h_y_in_u
  exact of_decide_eq_true h_val.symm

/-- If F ⊢ X -> Y, then Y is a subset of the closure of X. -/
@[
  blueprint "thm:attr-closure-impl-completeness"
  (title := /-- Attribute Closure (Full Implementation Completeness) -/)
  (statement := /--
    The computed attribute closure is complete. Formally,
    \[
      F \vdash (X \to Y) \implies Y \subseteq X^+.
    \]
  -/)
]
theorem attr_closure_complete {F : Finset (FunctionalDependency α)} {X Y : Finset α} :
  F ⊢ (X -> Y) → Y ⊆ attr_closure_impl F X := by
  intro h_der
  set S := attr_closure_impl F X
  set U := X ∪ Y ∪ F.sup (fun fd => fd.lhs ∪ fd.rhs)
  have h_Y_sub_U : Y ⊆ U := by
    intro a ha
    apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr; right
    exact ha
  have h_F_sub_U : ∀ fd ∈ F, fd.lhs ⊆ U ∧ fd.rhs ⊆ U := by
    intro fd hfd
    constructor
    · intro a ha
      apply Finset.mem_union.mpr; right
      simp [Finset.mem_sup, Finset.mem_union]
      exact ⟨fd, hfd, Or.inl ha⟩
    · intro a ha
      apply Finset.mem_union.mpr; right
      simp [Finset.mem_sup, Finset.mem_union]
      exact ⟨fd, hfd, Or.inr ha⟩
  have h_implies : F ⊨ (X -> Y) := armstrong_sound h_der
  have h_sat : (counterexample_relation U S).sat F :=
    counterexample_sat h_F_sub_U impl_closed
  have h_holds : (X -> Y : FunctionalDependency α).holds (counterexample_relation U S) :=
    h_implies h_sat
  exact subset_closure_if_holds attr_closure_subset_impl h_Y_sub_U h_holds

/-- Completeness of Armstrong's Axioms: if F ⊨ f, then F ⊢ f. -/
@[
  blueprint "theorem:armstrong-completeness"
  (title := /-- Armstrong's Axioms Completeness -/)
  (statement := /--
    The Armstrong's Axioms are complete, \textit{i.e.}, any functional dependency implied by FD set
    $F$ can be derived using Armstrong's Axioms. Formally,
    \[
      F \vDash f \implies F \vdash f.
    \]
  -/)
]
theorem armstrong_complete {F : Finset (FunctionalDependency α)} {f : FunctionalDependency α} :
  F ⊨ f → F ⊢ f := by
  intro h_implies
  -- Step 0: Rename f: X -> Y
  set X := f.lhs
  set Y := f.rhs
  -- Step 1: Let S be the attribute closure of f.lhs.
  set S := attr_closure_impl F X
  -- Prove that S is closed under F.
  have h_closed : S.is_closed_under F := impl_closed
  -- Step 2: Define a universe U that contains all attributes from f and F.
  set U := X ∪ Y ∪ F.sup (fun fd => fd.lhs ∪ fd.rhs)
  have h_Y_sub_U : Y ⊆ U := by
    unfold U
    intro a ha
    simp_all
  have h_F_sub_U : ∀ fd ∈ F, fd.lhs ⊆ U ∧ fd.rhs ⊆ U := by
    intro fd hfd
    constructor
    · intro a ha
      apply Finset.mem_union.mpr
      right
      simp [Finset.mem_sup, Finset.mem_union]
      exact ⟨fd, hfd, Or.inl ha⟩
    · intro a ha
      apply Finset.mem_union.mpr
      right
      simp [Finset.mem_sup, Finset.mem_union]
      exact ⟨fd, hfd, Or.inr ha⟩
  -- Step 3: Instantiate the counterexample relation.
  set r := counterexample_relation U S
  have h_sat : r.sat F := counterexample_sat h_F_sub_U h_closed
  -- Because F ⊨ f, the counterexample relation must satisfy f.
  have h_f_holds : f.holds r :=  h_implies h_sat
  -- Step 4: Prove X is a subset of its own closure S.
  have h_X_sub_S : X ⊆ S := attr_closure_subset_impl
  -- Because f holds on the relation, and Y ⊆ U, it must be that Y ⊆ S.
  have h_Y_sub_S : Y ⊆ S := subset_closure_if_holds h_X_sub_S h_Y_sub_U h_f_holds
  -- Step 5: Derive f from the fact that its RHS is in the closure of its LHS.
  have h_S_sound : F ⊢ (X -> S) := attr_closure_sound
  have h_Y_ref : F ⊢ (S -> Y) := Derives.rfl h_Y_sub_S
  exact Derives.trans h_S_sound h_Y_ref

/-- Armstrong's axioms are correct, i.e., a functional dependency can be derived using Armstrong's
    axioms if and only if it is implied by `F`. -/
@[
  blueprint "thm:armstrong-correct"
  (title := /-- Armstrong's Axioms Correctness -/)
  (statement := /--
    Armstrong's Axioms are correct, \textit{i.e.}, a functional dependency can be derived using
    Armstrong's axioms if and only if it is implied by $F$:
    \[
      F \vdash f \Leftrightarrow F \vDash f.
    \]
  -/)
]
theorem armstrong_correct {F : Finset (FunctionalDependency α)} {f : FunctionalDependency α} :
  F ⊢ f ↔ F ⊨ f := by
  constructor
  · exact armstrong_sound
  · exact armstrong_complete

/-- Prove that the computed attribute closure is correct with respect to the semantic definition of
    attribute closure.
-/
@[
  blueprint "thm:attr-clsr-impl-correct"
  (title := /-- Attribute Closure Implementation Correctness -/)
  (statement := /--
    The computed attribute closure is equivalent to its weak definition.
  -/)
]
theorem attr_closure_impl_correct {F : Finset (FunctionalDependency α)} {X : Finset α} :
  attr_closure_impl F X = attr_closure_weak F X := by
  ext x
  simp [attr_closure_weak, Set.mem_setOf_eq]
  constructor
  · intro h_x_in_impl
    apply armstrong_sound
    apply Derives.trans attr_closure_sound
    apply Derives.rfl
    simp [h_x_in_impl]
  · intro h_x_in_attr_closure
    rw [← Finset.singleton_subset_iff]
    exact attr_closure_complete (armstrong_complete h_x_in_attr_closure)

@[
  blueprint "def:res-attr-clsr"
  (title := /-- Restricted Attribute Closure -/)
  (statement := /--
    The attribute closure of an attribute set $X$ restricted to a universe of attributes $R$,
    written as $X^+_R$, is the intersection of the attribute closure (\cref{def:attr-clsr-impl}) and
    $R$. Formally,
    \[
      X^+_R = X^+ \cap R.
    \]
  -/)
]
def res_attr_closure (F : Finset (FunctionalDependency α)) (X R : Finset α) : Finset α :=
  attr_closure_impl F X ∩ R

@[
  blueprint "thm:subset-res-attr-clsr"
  (title := /-- Subset of Restricted Attribute Closure -/)
  (statement := /--
    If the input attribute set $X$ is a subset of the given attribute universe $R$, it is a subset
    of its attribute closure restricted to $R$. Formally,
    \[
      X \subseteq R \implies X \subseteq X^+_R.
    \]
  -/)
]
theorem subset_res_attr_closure {F : Finset (FunctionalDependency α)} {X R : Finset α} :
  X ⊆ R → X ⊆ res_attr_closure F X R := by
  unfold res_attr_closure
  intro h_X
  apply Finset.subset_inter
  · exact attr_closure_subset_impl
  · trivial

@[
  blueprint "thm:res-attr-clsr-subset"
  (title := /-- Restricted Attribute Closure is Subset -/)
  (statement := /--
    The attribute closure of a set of attributes $X$ restricted to a universe of attributes $R$ is
    the subset of $R$.
  -/)
]
theorem res_attr_closure_subset {F : Finset (FunctionalDependency α)} {X R : Finset α} :
  res_attr_closure F X R ⊆ R := by
  unfold res_attr_closure
  apply Finset.inter_subset_right

end NF

end RM
