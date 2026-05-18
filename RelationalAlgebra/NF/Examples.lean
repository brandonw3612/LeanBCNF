import RelationalAlgebra.RelationalModel
import RelationalAlgebra.RA.RelationalAlgebra
import RelationalAlgebra.NF.FuncDep
import RelationalAlgebra.NF.BCNF
import RelationalAlgebra.NF.BCNF_Impl

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Dedup

import Init.Data.Format.Basic

open RM

open RM.NF

syntax "singleton_relation" : tactic

macro_rules
  | `(tactic| singleton_relation) => `(tactic|
    simp;
    split_ands;
    all_goals (
      ext;
      simp;
      split;
      all_goals (simp; try grind)
    )
  )

section Repr

instance : Repr (FunctionalDependency String) where
  reprPrec fd _ := repr fd.lhs.sort ++ " -> " ++ repr fd.rhs.sort

instance {R : Finset String} : Repr (Decomposition R) where
  reprPrec d _ := "Decomposition { left := " ++ repr d.left.sort ++
    ", right := " ++ repr d.right.sort ++ " }"

def formatTree {R : Finset String} : DecompositionTree R → Std.Format
  | .leaf r => f!"leaf {repr r.sort}"
  | .node d left right =>
    Std.Format.join [
      f!"node ({repr d})",
      Std.Format.nest 2 (Std.Format.line ++ formatTree left),
      Std.Format.nest 2 (Std.Format.line ++ formatTree right)
    ]

instance {R : Finset String} : Repr (DecompositionTree R) where
  reprPrec tree _ := formatTree tree

end Repr

def exampleSchemaList : List String := ["A", "B", "C", "D", "E"]

def exampleRelation : RelationInstance String String := ⟨
  {"A", "B", "C", "D", "E"},
  {
    λ a => match a with
    | "A" => .some "a1"
    | "B" => .some "b1"
    | "C" => .some "c1"
    | "D" => .some "d1"
    | "E" => .some "e1"
    | _ => .none,
    λ a => match a with
    | "A" => .some "a2"
    | "B" => .some "b2"
    | "C" => .some "c1"
    | "D" => .some "d1"
    | "E" => .some "e1"
    | _ => .none,
    λ a => match a with
    | "A" => .some "a3"
    | "B" => .some "b3"
    | "C" => .some "c2"
    | "D" => .some "d2"
    | "E" => .some "e2"
    | _ => .none,
    λ a => match a with
    | "A" => .some "a4"
    | "B" => .some "b4"
    | "C" => .some "c2"
    | "D" => .some "d2"
    | "E" => .some "e2"
    | _ => .none,
    λ a => match a with
    | "A" => .some "a5"
    | "B" => .some "b5"
    | "C" => .some "c1"
    | "D" => .some "d4"
    | "E" => .some "e1"
    | _ => .none
  },
  by singleton_relation
⟩

def exampleFDs : Finset (FunctionalDependency String) := {
  ⟨{"A", "B"}, {"C", "D", "E"}⟩,
  ⟨{"B", "C"}, {"A", "D", "E"}⟩,
  ⟨{"D"}, {"E"}⟩,
  ⟨{"E"}, {"C"}⟩
}

#eval find_BCNF_violator_exec exampleSchemaList exampleFDs

#eval BCNF_decompose_exec exampleSchemaList exampleFDs

def exampleClassicSchema : List String := ["Student", "Course", "Instructor"]

def exampleClassicFDs : Finset (FunctionalDependency String) := {
  ⟨{"Student", "Course"}, {"Instructor"}⟩,
  ⟨{"Instructor"}, {"Course"}⟩
}

#eval find_BCNF_violator_exec exampleClassicSchema exampleClassicFDs

#eval BCNF_decompose_exec exampleClassicSchema exampleClassicFDs
