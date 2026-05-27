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

namespace NF

variable {α μ : Type} [DecidableEq α]

/-- A functional dependency `f` is implied by a set of functional dependencies `F`,
    if every relation instance that satisfies all dependencies in `F` also satisfies `f`.
-/
@[
  blueprint "definition:fd-imp"
  (title := /-- FD Implication -/)
  (statement := /--
    A functional dependency $f$ is implied by a set of functional dependencies $F$,
    if every relation instance that satisfies all dependencies in $F$ also satisfies $f$,
    denoted as $F \vDash f$.
  -/)
]
def implies (F : Finset (FunctionalDependency α)) (f : FunctionalDependency α) : Prop :=
  ∀ {μ : Type} {r : RelationInstance α μ}, r.satisfies F → f.holds r

/-- Notation for implication of functional dependencies. -/
infix:50 " ⊨ " => implies

@[
  blueprint "definition:fd-imp-proj"
  (title := /-- Projection of FD Implication -/)
  (statement := /--
    When projected onto a schema $R$, a functional dependency $f$ is implied by
    a set of functional dependencies $F$, if $F \vDash f$ and both
    the left-hand side and right-hand side of $f$ are subsets of $R$.
  -/)
]
def implies_proj (F : Finset (FunctionalDependency α)) (R : Finset α) (f : FunctionalDependency α) : Prop :=
  implies F f ∧ f.lhs ⊆ R ∧ f.rhs ⊆ R

/-- Armstrong's axioms for functional dependencies. -/
@[
  blueprint "definition:der-armstrong"
  (title := /-- Armstrong's Axioms -/)
  (statement := /--
    The derivation of functional dependencies are denoted as $F \vdash f$.
    Armstrong's axioms for functional dependencies consist of the following inference rules:
    \begin{itemize}
      \item \textit{Membership}: If a functional dependency is in the set,
            then it can be derived by nature.
      \item \textit{Reflexivity}: if $Y \subseteq X$, then $F \vdash X \rightarrow Y$.
      \item \textit{Augmentation}: if $F \vdash X \rightarrow Y$,
            then $F \vdash XZ \rightarrow YZ$ for any $Z$.
      \item \textit{Transitivity}: if $F \vdash X \rightarrow Y$ and $F \vdash Y \rightarrow Z$,
            then $F \vdash X \rightarrow Z$.
    \end{itemize}
  -/)
]
inductive Derives (F : Finset (FunctionalDependency α)) : FunctionalDependency α → Prop where
  /-- Membership: If a functional dependency is in the set, then it can be derived. -/
  | member : ∀ {f}, f ∈ F → Derives F f
  /-- Reflexivity: if `Y` is a subset of `X`, then `F ⊢ X -> Y`. -/
  | reflexivity : ∀ {X Y : Finset α}, Y ⊆ X → Derives F (X -> Y)
  /-- Augmentation: if `F ⊢ X -> Y`, then `F ⊢ XZ -> YZ` for any `Z`. -/
  | augmentation : ∀ {X Y Z : Finset α}, Derives F (X -> Y) → Derives F (X ∪ Z -> Y ∪ Z)
  /-- Transitivity: if `F ⊢ X -> Y` and `F ⊢ Y -> Z`, then `F ⊢ X -> Z`. -/
  | transitivity : ∀ {X Y Z : Finset α}, Derives F (X -> Y) → Derives F (Y -> Z) → Derives F (X -> Z)

/-- Notation for derivation of functional dependencies. -/
infix:50 " ⊢ " => Derives

/-- Armstrong' Axioms Additional Rule - Union:
    if `F ⊢ X -> Y` and `F ⊢ X -> Z`, then `F ⊢ X -> YZ`.
-/
@[
  blueprint "theorem:der-union"
  (title := /-- Armstrong' Axioms Additional Rule: Union -/)
  (statement := /--
    If $F \vdash X \rightarrow Y$ and $F \vdash X \rightarrow Z$,
    then $F \vdash X \rightarrow YZ$.
  -/)
  (proof := /--
    \begin{enumerate}
        \item Apply \textit{augmentation} rule to $F \vdash X \rightarrow Y$ with $X$
              to get $F \vdash X \rightarrow XY$.
        \item Apply \textit{augmentation} rule to $F \vdash X \rightarrow Z$ with $Y$
              to get $F \vdash XY \rightarrow YZ$.
        \item Apply \textit{transitivity} rule to the two derived dependencies
              to get $F \vdash X \rightarrow YZ$.
    \end{enumerate}
  -/)
]
theorem derives_union {F : Finset (FunctionalDependency α)} {X Y Z : Finset α} :
  F ⊢ (X -> Y) → F ⊢ (X -> Z) → F ⊢ (X -> Y ∪ Z) := by
  intro h_der_x_y h_der_x_z
  have h_der_x_xx_xy : F ⊢ (X ∪ X -> Y ∪ X) := Derives.augmentation h_der_x_y
  rw [Finset.union_idempotent X] at h_der_x_xx_xy
  have h_der_x_xy_yz : F ⊢ (Y ∪ X -> Y ∪ Z) := by
    apply Derives.augmentation at h_der_x_z
    rw [Finset.union_comm X Y, Finset.union_comm Z Y] at h_der_x_z
    exact h_der_x_z
  exact Derives.transitivity h_der_x_xx_xy h_der_x_xy_yz

/-- Armstrong' Axioms Additional Rule - Decomposition:
    if `F ⊢ X -> YZ`, then `F ⊢ X -> Y` and `F ⊢ X -> Z`.
-/
@[
  blueprint "theorem:der-decomposition"
  (title := /-- Armstrong' Axioms Additional Rule: Decomposition -/)
  (statement := /--
    If $F \vdash X \rightarrow YZ$, then $F \vdash X \rightarrow Y$
    and $F \vdash X \rightarrow Z$.
  -/)
  (proof := /--
    Using the \textit{reflexivity} rule, we derive $F \vdash YZ \rightarrow Y$
    and $F \vdash YZ \rightarrow Z$ since $Y$ and $Z$ are subsets of $YZ$.
    Then, we apply the \textit{transitivity} rule to obtain $F \vdash X \rightarrow Y$
    and $F \vdash X \rightarrow Z$ from $F \vdash X \rightarrow YZ$.
  -/)
]
theorem derives_decomposition {F : Finset (FunctionalDependency α)} {X Y Z : Finset α} :
  F ⊢ (X -> Y ∪ Z) → F ⊢ (X -> Y) ∧ F ⊢ (X -> Z) := by
  intro h_der_x_yz
  constructor
  · have h_der_yz_y : F ⊢ (Y ∪ Z -> Y) := Derives.reflexivity Finset.subset_union_left
    exact Derives.transitivity h_der_x_yz h_der_yz_y
  · have h_der_yz_z : F ⊢ (Y ∪ Z -> Z) := Derives.reflexivity Finset.subset_union_right
    exact Derives.transitivity h_der_x_yz h_der_yz_z

/-- Armstrong' Axioms Additional Rule - Pseudotransitivity:
    if `F ⊢ X -> Y` and `F ⊢ YZ -> W`, then `F ⊢ XZ -> W`.
-/
@[
  blueprint "theorem:der-pseudotransitivity"
  (title := /-- Armstrong' Axioms Additional Rule: Pseudotransitivity -/)
  (statement := /--
    If $F \vdash X \rightarrow Y$ and $F \vdash YZ \rightarrow W$,
    then $F \vdash XZ \rightarrow W$.
  -/)
  (proof := /--
    Apply the \textit{augmentation} rule to $F \vdash X \rightarrow Y$ with $Z$ to get
    $F \vdash XZ \rightarrow YZ$. Then, apply the \textit{transitivity} rule to the derived
    functional dependency and $F \vdash YZ \rightarrow W$ to get $F \vdash XZ \rightarrow W$.
  -/)
]
theorem derives_pseudotransitivity {F : Finset (FunctionalDependency α)} {X Y Z W : Finset α} :
  F ⊢ (X -> Y) → F ⊢ (Y ∪ Z -> W) → F ⊢ (X ∪ Z -> W) := by
  intro h_der_x_y h_der_yz_w
  have h_der_xz_yz : F ⊢ (X ∪ Z -> Y ∪ Z) := by simpa using Derives.augmentation h_der_x_y
  exact Derives.transitivity h_der_xz_yz h_der_yz_w

/-- Soundness of Armstrong's Axioms: if `F ⊢ f`, then `F ⊨ f`. -/
@[
  blueprint "theorem:armstrong-soundness"
  (title := /-- Soundness of Armstrong's Axioms -/)
  (statement := /--
    If a functional dependency $f$ can be derived from a set of functional dependencies $F$
    using Armstrong's axioms, then $f$ is implied by $F$.
  -/)
  (proof := /--
    By induction on the derivation of $f$ from $F$ using Armstrong's axioms,
    we show case by case in this proof that if $F \vdash f$, then $F \vDash f$.
    Specifically in each case, with the precondition that the functional dependency $f$ can be
    derived from FD set $F$ ($F \vdash f$), we unfold the definition of implication
    ($F \vDash f$) and show that for any relation instance $r$ that satisfies all dependencies
    in $F$, $f$ also holds on $r$.
    \begin{itemize}
      \item \textit{Membership}:
            As $f$ is in $F$, and $r$ satisfies all dependencies in $F$,
            $f$ must hold on $r$.
      \item \textit{Reflexivity}:
            Since $Y$ is a subset of $X$, for any two tuples that agree on $X$,
            they must also agree on $Y$. Thus, $f$ holds on $r$.
      \item \textit{Augmentation}:
            With precondition that $X \rightarrow Y$ holds on $r$, we split the membership of
            attribute $s$ in the target set $YZ$ into two cases: $s$ is in $Y$ or $s$ is in $Z$.
            \begin{itemize}
              \item If $s$ is in $Y$, to show the agreement of tuples on $s$, we apply
                    the precondition that $X \rightarrow Y$ holds on $r$. Now we need to show that
                    the tuples agree on all attributes in $X$. Since in the precondition we have that
                    the tuples agree on $XZ$, they must also agree on $X$ as $X$ is a subset of $XZ$.
                    Thus, we conclude that the tuples agree on $s$.
              \item If $s$ is in $Z$, we apply the precondition that the tuples agree on $XZ$ again
                    to conclude that they also agree on $Z$, and thus they agree on $s$.
            \end{itemize}
      \item \textit{Transitivity}:
            To show that the tuples agree on $Z$, we apply the precondition that
            $Y \rightarrow Z$ holds on $r$. Now we need to show that the tuples agree on $Y$.
            We apply the precondition that $X \rightarrow Y$ holds on $r$ to align the objective with
            the precondition that the tuples agree on $X$.
    \end{itemize}
  -/)
]
theorem armstrong_sound {F : Finset (FunctionalDependency α)} {f : FunctionalDependency α} :
  F ⊢ f → F ⊨ f := by
  intro h_der μ r h_sat
  induction h_der with
  | member h_in => exact h_sat h_in
  | reflexivity h_y_subset_x =>
    intro t₁ t₂ h_t₁ h_t₂ h_eq_x s h_s_in_y
    have h_s_in_x := h_y_subset_x h_s_in_y
    exact h_eq_x s h_s_in_x
  | augmentation h_der_xy h_xy_holds =>
    intro _ _ h_t₁ h_t₂ h_eq_xz s h_s_in_yz
    cases Finset.mem_union.mp h_s_in_yz with
    | inl h_s_in_y =>
      apply h_xy_holds h_t₁ h_t₂
      repeat simp_all
    | inr h_s_in_z =>
      apply h_eq_xz
      simp_all
  | transitivity h_der_xy h_der_yz h_xy_holds h_yz_holds =>
    intro t₁ t₂ h_t₁ h_t₂ h_eq_x s h_s_in_z
    apply h_yz_holds h_t₁ h_t₂
    · intro a h_a_in_y
      exact h_xy_holds h_t₁ h_t₂ h_eq_x a h_a_in_y
    · trivial

/-- `F⁺`: Closure of an FD set $F$. -/
@[
  blueprint "definition:fd-closure"
  (title := /-- Functional Dependency Closure -/)
  (statement := /--
    The closure of a functional dependencies set $F$, denoted as $F^+$,
    is the set of all functional dependencies that can be implied by $F$.
  -/)
]
def func_dep_closure (F : Finset (FunctionalDependency α)) : Set (FunctionalDependency α) :=
  {f | F ⊨ f}

/-- Projection of the closure of an FD set $F$ onto a schema $R$. -/
@[
  blueprint "definition:fd-closure-proj"
  (title := /-- Functional Dependency Closure Projection -/)
  (statement := /--
    The projection of the closure of a set of functional dependencies $F$
    onto a schema $R$ is the set of all functional dependencies
    that can be implied by $F$ and whose left-hand side and right-hand side
    are both subsets of $R$.
  -/)
]
def func_dep_closure_proj (F : Finset (FunctionalDependency α)) (R : Finset α) : Set (FunctionalDependency α) :=
  {f | F ⊨ f ∧ f.lhs ⊆ R ∧ f.rhs ⊆ R}

/-- `X⁺`: Closure of an attribute set `X` with respect to an FD set, `F`. (Weak definition as a Set.) -/
@[
  blueprint "definition:attr-closure-weak"
  (title := /-- Attribute Closure (Weak) -/)
  (statement := /--
    The closure of an attribute set $X$, denoted as $X^+$,
    with respect to a set of functional dependencies $F$,
    is the set of all attributes that can be functionally determined by $X$ using the dependencies in $F$.
    Formally,
    \[
        X^+ = \left\{ a | F \vDash X \rightarrow \left\{ a \right\} \right\}.
    \]
  -/)
]
def attr_closure_weak (F : Finset (FunctionalDependency α)) (X : Finset α) : Set α :=
  {a | (X -> {a} : FunctionalDependency α) ∈ func_dep_closure F}

/-- Filtered set of FDs where `lhs` are subsets of `X`. -/
@[
  blueprint "definition:left-filter"
  (title := /-- Left-Filter of FD Set -/)
  (statement := /--
    We define a function $F_L(X)$ over a given attribute set $X$,
    where we filter the set of functional dependencies $F$ to only include
    those whose left-hand side is a subset of $X$. Formally,
    \[
        F_L(X) = \left\{ fd \in F \mid fd.lhs \subseteq X \right\}.
    \]
  -/)
]
def left_filter (F : Finset (FunctionalDependency α)) (X : Finset α) : Finset (FunctionalDependency α) :=
  {fd ∈ F | fd.lhs ⊆ X}

/--
  Single step iteration for computing the attribute set closure.
  For every FD in the left-filtered set, we add its right-hand side to the attribute set.
  (If `α -> β ∈ F` and `α ⊆ X`, then we can add `β` to `X`.)
-/
@[
  blueprint "definition:attr-closure-impl-step"
  (title := /-- Attribute Closure (Single Step) -/)
  (statement := /--
    A single step iteration for computing the attribute set closure.
    For every FD in the left-filtered set, we add its right-hand side to the attribute set.
    Formally, we have:
    \[
        X'_F = X \cup \bigcup_{\alpha \rightarrow \beta \in F, \alpha \subseteq X} \beta.
    \]
  -/)
]
def attr_closure_impl_step (F : Finset (FunctionalDependency α)) (X : Finset α) : Finset α :=
  X ∪ (left_filter F X).sup (λ fd => fd.rhs)

/-- Auxiliary definition for iterating the closure step. -/
@[
  blueprint "definition:attr-closure-impl-iter"
  (title := /-- Attribute Closure (Iteration) -/)
  (statement := /--
    We iterate the single step of attribute closure computation to compute the full closure.
    This is denoted as $X^n_F$, where $n$ is the number of iterations and $X^0_F = X$.
  -/)
]
def ac_seq (F : Finset (FunctionalDependency α)) (X : Finset α) (n : ℕ) : Finset α :=
  (attr_closure_impl_step F)^[n] X

/-- Simply unfold the iteration by one layer. -/
@[
  blueprint "lemma:attr-closure-iter-succ"
  (title := /-- Attribute Closure (Iteration Successor) -/)
  (statement := /--
    Unfolding the iteration of attribute closure sequence by one layer, we have:
    \[
        X^{n+1}_F = X^n_F \cup \bigcup_{\alpha \rightarrow \beta \in F, \alpha \subseteq X^n_F} \beta.
    \]
  -/)
  (proof := /-- This proof is trivial. -/)
]
lemma ac_seq_succ (F : Finset (FunctionalDependency α)) (X : Finset α) (n : ℕ) :
  ac_seq F X (n + 1) = attr_closure_impl_step F (ac_seq F X n) := by
  simp [ac_seq, Function.iterate_succ_apply']

/-- Implementation of the attribute closure algorithm,
    where we iterate the single step |F| times (in the worst case).
-/
@[
  blueprint "definition:attr-closure-impl"
  (title := /-- Attribute Closure (Full Implementation) -/)
  (statement := /--
    We iterate the single step of the attribute closure algorithm $|F|$ times
    (in the worst case) to obtain the full closure.
    Formally, we have:
    \[
        X^+ = X^{|F|}_F.
    \]
  -/)
]
def attr_closure_impl (F : Finset (FunctionalDependency α)) (X : Finset α) : Finset α :=
  ac_seq F X F.card

/-- Soundness of a single step of the attribute set closure computation. -/
@[
  blueprint "lemma:attr-closure-step-soundness"
  (title := /-- Attribute Closure (Step Soundness) -/)
  (statement := /--
    Every single step iterated in the attribute closure algorithm is sound. Formally,
    \[
        F \vdash (X \to X'_F).
    \]
  -/)
  (proof := /--
    First, we apply the \textit{union} rule of Armstrong's axioms to split the result of
    the single step into two parts: the original attribute set $X$ and
    the union of the right-hand sides of the dependencies in the left-filtered set.
    Then, we show that both parts can be derived from $F$:
    \begin{itemize}
      \item For $X$, we can derive $X \to X$ using the \textit{reflexivity} rule, trivially.
      \item For $\bigcup_{\alpha \rightarrow \beta \in F, \alpha \subseteq X} \beta$,
            we first unfold the filter to show that the filter is a subset of $F$.
            Next, we show that for any subset $S'$ of the filtered set $S$, we can derive
            $X \rightarrow \bigcup_{\alpha \rightarrow \beta \in S'} \beta$.
            To prove this, we use induction on $S'$.

            In the base case where $S'$ is empty, we can derive $X \rightarrow \emptyset$
            using the \textit{reflexivity} rule, trivially.

            In the inductive case, we have that the target holds for a strict subset $S''$ of $S'$,
            and we need to show that as we introduce a new FD $fd \in S$ into $S''$,
            the target still holds for the updated $S''$.

            We again apply the \textit{union} rule to split the target into two parts:
            the right-hand side of $fd$ and the union of the right-hand sides of
            the dependencies in the original $S''$.

            For the first part, we can derive $X \rightarrow fd.rhs$ using the \textit{transitivity} rule
            by introducing the left-hand side of $fd$ as the bridge.
            Specifically, since $fd$ is in the left-filtered set, its left-hand side is a subset of $X$,
            so we can derive $X \rightarrow fd.lhs$ using the \textit{reflexivity} rule.
            Then, $fd$ itself can also be derived from $F$ since it is in $F$.

            The second part is exactly the inductive hypothesis, so it is proved trivially.

            Finally, we apply the above result to $S$ to conclude this case.
    \end{itemize}
    With both parts derived, we arrive at the conclusion that $F \vdash (X \to X'_F)$.
  -/)
]
lemma attr_closure_step_sound {F : Finset (FunctionalDependency α)} {X : Finset α} :
  F ⊢ (X -> attr_closure_impl_step F X) := by
  simp [attr_closure_impl_step]
  apply derives_union
  · apply Derives.reflexivity
    simp
  · set S := left_filter F X
    have h_s_subset_F : S ⊆ F := by simp [left_filter, S]
    have h_s'_sup : ∀ S' ⊆ S, F ⊢ (X -> S'.sup (λ fd => fd.rhs)) := by
      intro s' h_s'_sub_s
      induction s' using Finset.induction with
      | empty => simp [Derives.reflexivity]
      | insert fd S'' h_fd_not_in_s'' h_ih =>
        simp [Finset.sup_insert]
        obtain ⟨h_fd, h_s''⟩ := Finset.insert_subset_iff.mp h_s'_sub_s
        apply derives_union
        · simp [S, left_filter] at h_fd
          apply Derives.transitivity
          · exact Derives.reflexivity h_fd.2
          · exact Derives.member h_fd.1
        · exact h_ih h_s''
    apply h_s'_sup S
    simp

/-- Soundness of the attribute closure algorithm full implementation. -/
@[
  blueprint "theorem:attr-closure-impl-soundness"
  (title := /-- Attribute Closure (Full Implementation Soundness) -/)
  (statement := /--
    The full implementation of the attribute closure algorithm is sound. Formally,
    \[
        F \vdash (X \to X^+).
    \]
  -/)
  (proof := /--
    With the soundness proof of a single step of the attribute closure algorithm,
    we show the soundness of the full implementation by induction on the number of iterations
    \textit{i.e.}, the cardinality of the FD set $F$.

    In the base case where $F = \emptyset$, the closure of any attribute set is itself,
    and we can derive $X \to X$ using the \textit{reflexivity} rule, trivially.

    In the inductive case, we assume that the attribute closure implementation is sound
    for any FD set with $|F| = n$, and we apply the single step soundness to show that
    the attribute closure implementation is also sound for any FD set with $|F| = n + 1$.
  -/)
]
theorem attr_closure_sound {F : Finset (FunctionalDependency α)} {X : Finset α} :
  F ⊢ (X -> attr_closure_impl F X) := by
  simp [attr_closure_impl]
  induction F.card with
  | zero => simp [ac_seq, Derives.reflexivity]
  | succ n ih =>
    apply Derives.transitivity
    · exact ih
    · simp [ac_seq_succ,attr_closure_step_sound]

/-- An attribute set is a subset of its closure. -/
@[
  blueprint "lemma:subset-attr-closure-impl"
  (title := /-- Subset of Attribute Closure (Full Implementation) -/)
  (statement := /--
    An attribute set is a subset of its closure. Formally,
    \[
        X \subseteq X^+.
    \]
  -/)
  (proof := /--
    With the subset relation between an attribute set and its single-step closure,
    we can show that the attribute set is also a subset of the full closure by induction
    on the number of iterations in the full implementation.

    In the base case where $F = \emptyset$, the closure of any attribute set is itself,
    so the subset relation holds trivially.

    In the inductive case, we assume that $X \subseteq X^n_F$ for any FD set with $|F| = n$,
    and we apply the subset relation for a single step to show that $X \subseteq X^{n+1}_F$
    for any FD set with $|F| = n + 1$.
  -/)
]
lemma attr_closure_subset_impl {F : Finset (FunctionalDependency α)} {X : Finset α} :
  X ⊆ attr_closure_impl F X := by
  rw [attr_closure_impl]
  induction F.card with
    | zero => exact fun a ha => ha
    | succ n ih =>
      intro a ha
      simp [ac_seq_succ, attr_closure_impl_step]
      left
      exact Finset.mem_of_subset ih ha

/-- When the closure set stablizes at some point, it remains the same for all subsequent iterations. -/
@[
  blueprint "lemma:stability-on-attr-closure-impl-iter"
  (title := /-- Stability of Attribute Closure Iteration -/)
  (statement := /--
    When the closure set stablizes at some point, it remains the same for all subsequent iterations.
    Formally, if $X^{k+1}_F = X^k_F$ for some $k$, then $X^n_F = X^k_F$ for all $n \geq k$.
  -/)
  (proof := /--
    With $n \geq k$, we can express $n$ as $k + d$ for some $d \geq 0$.
    We show the stability of the closure set by induction on $d$.

    In the base case where $d = 0$, we have $n = k$, so the stability holds trivially.

    In the inductive case, we assume that $X^{k+d}_F = X^k_F$ for some $d \geq 0$,
    and we need to show that $X^{k+(d+1)}_F = X^k_F$.
    Here, we use $X^{k+d}$ as the bridge to connect $X^{k+(d+1)}$ and $X^k$.
    Combining the inductive hypothesis and the pre-condition that $X^{k+1}_F = X^k_F$,
    we show that $X^{k+(d+1)}_F$ is equal to $X^k_F$.
  -/)
]
lemma seq_fixed_of_eq {F : Finset (FunctionalDependency α)} {X : Finset α} {k n : ℕ}
  (h : ac_seq F X (k + 1) = ac_seq F X k) (hn : k ≤ n) :
  ac_seq F X n = ac_seq F X k := by
  have h_step : attr_closure_impl_step F (ac_seq F X k) = ac_seq F X k := by simp_all [← ac_seq_succ]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero => rfl
  | succ d ih =>
    have heq : k + (d + 1) = k + d + 1 := by omega
    simp [heq, ac_seq_succ, ih, h_step]

/-- The set of filtered dependencies cannot grow indefinitely. -/
@[
  blueprint "lemma:exists-fixed-point-on-left-filter"
  (title := /-- Existence of Fixed Point on Left-Filter -/)
  (statement := /--
    The set of filtered dependencies cannot grow indefinitely. Formally, if the left-filtered set
    is non-empty at the beginning, then there exists some $k < |F|$ such that
    the left-filtered set at step $k$ is the same as the left-filtered set at step $k + 1$:
    \[
        L_F(X) \neq \emptyset \implies \exists k < |F|, L_F(X^k_F) = L_F(X^{k+1}_F).
    \]
  -/)
  (proof := /--
    We prove this by contradiction. In this proof, we assume for the sake of contradiction that for every step $k < |F|$,
    the left-filtered set at step $k$ is different from the left-filtered set at step $k + 1$,
    \textit{i.e.}, $L_F(X^k_F) ≠ L_F(X^{k+1}_F)$.

    First, we prove that for every $i < |F|$, $L_F(X^i_F) \subset L_F(X^{i+1}_F)$.
    Specifically, if $fd \in L_F(X^i_F)$, then $fd.lhs \subseteq X^i_F \subseteq X^{i+1}_F$. Hence, $fd \in L_F(X^{i+1}_F)$.
    Combining this with the contradiction assumption that $L_F(X^k_F) ≠ L_F(X^{k+1}_F)$ for all $k < |F|$,
    we conclude that $L_F(X^i_F) \subset L_F(X^{i+1}_F)$ for every $i < |F|$.

    Next, having the strict subset relation between the left-filtered sets for every step,
    we show that the cardinality of the left-filtered set at each step is strictly increasing,
    \textit{i.e.}, $|L_F(X)| = |L_F(X^0_F)| < |L_F(X^1_F)| < |L_F(X^2_F)| < \cdots < |L_F(X^{|F|}_F)|$.

    By induction on $|F|$, we show that $|L_F(X^{|F|}_F)|$ is at least $|F| + 1$ using the inequality chain above. However,
    for every $i \leq |F|$, $L_F(X^i_F)$ is a subset of $F$, so $|L_F(X^i_F)|$ is at most $|F|$.
    This leads to a contradiction, and we conclude that there must exist some $k < |F|$ such that $L_F(X^k_F) = L_F(X^{k+1}_F)$.
  -/)
]
lemma exists_filtered_eq (F : Finset (FunctionalDependency α)) (X : Finset α)
  (h_pos : 0 < (left_filter F (ac_seq F X 0)).card) :
  ∃ k < F.card, left_filter F (ac_seq F X k) = left_filter F (ac_seq F X (k + 1)) := by
  by_contra h_contra
  push_neg at h_contra
  have h_strict : ∀ i < F.card, left_filter F (ac_seq F X i) ⊂ left_filter F (ac_seq F X (i + 1)) := by
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
  have h_le : (left_filter F (ac_seq F X F.card)).card ≤ F.card := Finset.card_le_card (Finset.filter_subset _ _)
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
  blueprint "lemma:fixed-point-on-attr-closure-impl-iter"
  (title := /-- Fixed Point of Attribute Closure Iteration -/)
  (statement := /--
    The closure reaches a fixed point at (or before) step $|F|$. Formally,
    \[
        X^{|F|+1}_F = X^{|F|}_F.
    \]
  -/)
  (proof := /--

  -/)
]
lemma seq_stabilizes (F : Finset (FunctionalDependency α)) (X : Finset α) :
  ac_seq F X (F.card + 1) = ac_seq F X F.card := by
  by_cases h_zero : (left_filter F (ac_seq F X 0)).card = 0
  · have h_empty : left_filter F (ac_seq F X 0) = ∅ := Finset.card_eq_zero.mp h_zero
    have h_eq : ac_seq F X 1 = ac_seq F X 0 := by
      change attr_closure_impl_step F X = X
      rw [ac_seq, Function.iterate_zero, id, left_filter] at h_empty
      simp [attr_closure_impl_step, left_filter, h_empty]
    have h_all : ∀ n ≥ 0, ac_seq F X n = ac_seq F X 0 := fun n hn => seq_fixed_of_eq h_eq hn
    rw [h_all (F.card + 1) (Nat.zero_le _), h_all F.card (Nat.zero_le _)]
  · have h_pos : 0 < (left_filter F (ac_seq F X 0)).card := Nat.pos_of_ne_zero h_zero
    obtain ⟨k, hk_lt, hk_eq⟩ := exists_filtered_eq F X h_pos
    rw [ac_seq_succ] at hk_eq
    have h_eq : ac_seq F X (k + 2) = ac_seq F X (k + 1) := by
      simp [ac_seq_succ]
      nth_rw 1 [attr_closure_impl_step]
      rw [← hk_eq]
      simp [attr_closure_impl_step]
    have h_all : ∀ n ≥ k + 1, ac_seq F X n = ac_seq F X (k + 1) := fun n hn => seq_fixed_of_eq h_eq hn
    have h1 : k + 1 ≤ F.card := hk_lt
    have h2 : k + 1 ≤ F.card + 1 := by omega
    rw [h_all (F.card + 1) h2, h_all F.card h1]

/-- The computed closure is closed under `F`: if an FD's LHS is in the closure, its RHS is also included. -/
@[
  blueprint "lemma:attr-closure-impl-closed"
]
lemma impl_closed {F : Finset (FunctionalDependency α)} {X : Finset α} :
  (attr_closure_impl F X).is_closed_under F := by
  set XP := attr_closure_impl F X
  intro fd hfd h_lhs
  have h_fixed_point : attr_closure_impl_step F XP = XP := by
    simp [XP, attr_closure_impl, ← ac_seq_succ]
    exact seq_stabilizes F X
  have h_step : fd.rhs ⊆ attr_closure_impl_step F XP := by
    intro a ha
    simp [attr_closure_impl_step, left_filter, Finset.mem_union, Finset.mem_sup]
    exact Or.inr ⟨fd, ⟨hfd, h_lhs⟩, ha⟩
  rw [h_fixed_point] at h_step
  exact h_step

/-- All attributes in the tuple are true. -/
@[
  blueprint "definition:counterexample-t-all-true"
]
def t_all_true (U : Finset α) : α →. Bool :=
  fun a => {
    Dom := a ∈ U
    get := fun _ => true
  }

/-- Only attributes in the closure S are true. -/
@[
  blueprint "definition:counterexample-t_closure"
]
def t_closure (U S : Finset α) : α →. Bool :=
  fun a => {
    Dom := a ∈ U
    get := fun _ => decide (a ∈ S)
  }

/-- A counterexample relation instance that satisfies all FDs in F but violates the FD X -> Y when Y is not a subset of the closure of X. -/
@[
  blueprint "definition:counterexample"
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

/-- If F is a set of FDs such that all FDs in F have their attributes contained in U, and S is closed under F, then the counterexample relation instance satisfies all FDs in F. -/
@[
  blueprint "lemma:counterexample-sat-F"
]
lemma counterexample_sat_F {U S : Finset α} {F : Finset (FunctionalDependency α)}
  (h_F_sub_U : ∀ fd ∈ F, fd.lhs ⊆ U ∧ fd.rhs ⊆ U) (h_closed : S.is_closed_under F) :
  (counterexample_relation U S).satisfies F := by
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
  blueprint "lemma:subset-of-closure-if-fd-holds"
]
lemma subset_of_closure_if_holds {U X Y S : Finset α}
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
  blueprint "theorem:attr-closure-impl-completeness"
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
  have h_sat : (counterexample_relation U S).satisfies F :=
    counterexample_sat_F h_F_sub_U impl_closed
  have h_holds : (X -> Y : FunctionalDependency α).holds (counterexample_relation U S) :=
    h_implies h_sat
  exact subset_of_closure_if_holds attr_closure_subset_impl h_Y_sub_U h_holds

/-- Completeness of Armstrong's Axioms: if F ⊨ f, then F ⊢ f. -/
@[
  blueprint "theorem:armstrong-completeness"
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
  have h_sat : r.satisfies F := counterexample_sat_F h_F_sub_U h_closed
  -- Because F ⊨ f, the counterexample relation must satisfy f.
  have h_f_holds : f.holds r :=  h_implies h_sat
  -- Step 4: Prove X is a subset of its own closure S.
  have h_X_sub_S : X ⊆ S := attr_closure_subset_impl
  -- Because f holds on the relation, and Y ⊆ S, it must be that Y ⊆ S.
  have h_Y_sub_S : Y ⊆ S := subset_of_closure_if_holds h_X_sub_S h_Y_sub_U h_f_holds
  -- Step 5: Derive f from the fact that its RHS is in the closure of its LHS.
  have h_S_sound : F ⊢ (X -> S) := attr_closure_sound
  have h_Y_ref : F ⊢ (S -> Y) := Derives.reflexivity h_Y_sub_S
  exact Derives.transitivity h_S_sound h_Y_ref

/-- Armstrong's axioms are correct, given their soundness and completeness. -/
@[
  blueprint "theorem:armstrong-correctness"
]
theorem armstrong_correct {F : Finset (FunctionalDependency α)} {f : FunctionalDependency α} :
  F ⊢ f ↔ F ⊨ f := by
  constructor
  · exact armstrong_sound
  · exact armstrong_complete

/-- Prove that the computed attribute closure is correct with respect to the semantic definition of attribute closure. -/
@[
  blueprint "theorem:attr-closure-impl-correctness"
]
theorem attr_closure_impl_correct {F : Finset (FunctionalDependency α)} {X : Finset α} :
  attr_closure_impl F X = attr_closure_weak F X := by
  ext x
  simp [attr_closure_weak, func_dep_closure, Set.mem_setOf_eq]
  constructor
  · intro h_x_in_impl
    apply armstrong_sound
    apply Derives.transitivity attr_closure_sound
    apply Derives.reflexivity
    simp [h_x_in_impl]
  · intro h_x_in_attr_closure
    rw [← Finset.singleton_subset_iff]
    exact attr_closure_complete (armstrong_complete h_x_in_attr_closure)

/-- A strong definition of attribute closure, which is a finite set. -/
@[
  blueprint "definition:attr-closure-strong"
]
def attr_closure (F : Finset (FunctionalDependency α)) (X : Finset α) : Finset α :=
  attr_closure_impl F X

/-- Prove that the strong definition of attribute closure is equivalent to the weak definition via the implementation. -/
@[
  blueprint "theorem:attr-closure-strong-correctness"
]
theorem attr_closure_strong_correct {F : Finset (FunctionalDependency α)} {X : Finset α} :
  attr_closure F X = attr_closure_weak F X := by
  simp [attr_closure, attr_closure_impl_correct]

@[
  blueprint "definition:attr-closure-proj"
]
def attr_closure_proj (F : Finset (FunctionalDependency α)) (X R : Finset α) : Finset α :=
  attr_closure_impl F X ∩ R

@[
  blueprint "theorem:subset-attr-closure-proj"
]
theorem subset_attr_closure_proj {F : Finset (FunctionalDependency α)} {X R : Finset α} :
  X ⊆ R → X ⊆ attr_closure_proj F X R := by
  rw [attr_closure_proj]
  intro h_X
  apply Finset.subset_inter
  · exact attr_closure_subset_impl
  · trivial

@[
  blueprint "theorem:attr-closure-proj-subset"
]
theorem attr_closure_proj_subset {F : Finset (FunctionalDependency α)} {X R : Finset α} :
  attr_closure_proj F X R ⊆ R := by
  rw [attr_closure_proj]
  apply Finset.inter_subset_right

/--
  Application: Testing FDs
  S -> T ∈ F⁺ **iff** T ⊆ S⁺.
-/
theorem func_dep_valid_via_attr_closure {F : Finset (FunctionalDependency α)} {fd : FunctionalDependency α} :
  fd ∈ func_dep_closure F ↔ fd.rhs ⊆ attr_closure F fd.lhs := by
  simp [attr_closure, func_dep_closure]
  set lc := attr_closure_impl F fd.lhs
  rw [← armstrong_correct]
  constructor
  · exact attr_closure_complete
  · intro h_t_subset_closure
    apply Derives.transitivity attr_closure_sound
    apply Derives.reflexivity h_t_subset_closure

end NF

end RM
