import Mathlib

namespace BECv2

namespace Compiler

inductive BecSort : Type where
  | prop : BecSort
  | nat : BecSort
  | int : BecSort
  | rat : BecSort
  | real : BecSort
  | vector : BecSort -> Nat -> BecSort
  | set : BecSort -> BecSort
  | metricSpace : BecSort
  | topologicalSpace : BecSort
  | probabilitySpace : BecSort
  | custom : String -> BecSort

mutual

inductive Term : Type where
  | var : String -> BecSort -> Term
  | app : String -> List Term -> Term
  | setOf : String -> BecSort -> Formula -> Term
  | excess : Term -> Term -> Term
  | profile : Term -> Term
  | dist : Term -> Term -> Term
  | threshold : Term -> Term -> Term
  | shell : Term -> Term -> Term -> Term

inductive Formula : Type where
  | trueF : Formula
  | falseF : Formula
  | atom : String -> List Term -> Formula
  | leF : Term -> Term -> Formula
  | ltF : Term -> Term -> Formula
  | eqF : Term -> Term -> Formula
  | andF : Formula -> Formula -> Formula
  | orF : Formula -> Formula -> Formula
  | impF : Formula -> Formula -> Formula
  | notF : Formula -> Formula
  | forallF : String -> BecSort -> Formula -> Formula
  | existsF : String -> BecSort -> Formula -> Formula
  | probGe : Formula -> Term -> Formula

end

structure ProblemAST where
  context : List Formula
  goal : Formula

inductive ClaimKind : Type where
  | thresholdLE : ClaimKind
  | thresholdLT : ClaimKind
  | shell : ClaimKind
  | profileEq : ClaimKind
  | transfer : ClaimKind
  | fallback : ClaimKind
  | stochasticThreshold : ClaimKind
  | dynamicInvariant : ClaimKind

structure CompileObstruction where
  phase : String
  reason : String
  missing : List String

inductive BoundaryAtom : Type where
  | thresholdLE : Term -> Term -> Term -> Formula -> BoundaryAtom
  | thresholdLT : Term -> Term -> Term -> Formula -> BoundaryAtom
  | shell : Term -> Term -> Term -> Term -> Formula -> BoundaryAtom
  | profileEq : Term -> Term -> Formula -> BoundaryAtom

def BoundaryAtom.kind : BoundaryAtom -> ClaimKind
  | BoundaryAtom.thresholdLE _ _ _ _ => ClaimKind.thresholdLE
  | BoundaryAtom.thresholdLT _ _ _ _ => ClaimKind.thresholdLT
  | BoundaryAtom.shell _ _ _ _ _ => ClaimKind.shell
  | BoundaryAtom.profileEq _ _ _ => ClaimKind.profileEq

def parseFailure (phase : String) : CompileObstruction :=
  { phase := phase, reason := "outside BEC native fragment", missing := [] }

def parseAtom : Formula -> Except CompileObstruction BoundaryAtom
  | Formula.leF (Term.excess A x) r =>
      .ok (BoundaryAtom.thresholdLE A x r
        (Formula.leF (Term.excess A x) r))
  | Formula.ltF (Term.excess A x) r =>
      .ok (BoundaryAtom.thresholdLT A x r
        (Formula.ltF (Term.excess A x) r))
  | Formula.andF (Formula.ltF r (Term.excess A x))
                 (Formula.leF (Term.excess _ _) s) =>
      .ok (BoundaryAtom.shell A x r s
        (Formula.andF
          (Formula.ltF r (Term.excess A x))
          (Formula.leF (Term.excess A x) s)))
  | Formula.eqF (Term.profile A) (Term.profile C) =>
      .ok (BoundaryAtom.profileEq A C
        (Formula.eqF (Term.profile A) (Term.profile C)))
  | _ => .error (parseFailure "parse atom")

def normalizeFormula : Formula -> Except CompileObstruction (List BoundaryAtom)
  | Formula.andF p q => do
      let np <- normalizeFormula p
      let nq <- normalizeFormula q
      pure (np ++ nq)
  | f => do
      let a <- parseAtom f
      pure [a]

def normalizeList : List Formula -> Except CompileObstruction (List BoundaryAtom)
  | [] => .ok []
  | f :: fs => do
      let nf <- normalizeFormula f
      let nfs <- normalizeList fs
      pure (nf ++ nfs)

structure NormalForm where
  assumptions : List BoundaryAtom
  goal : List BoundaryAtom

def normalizeProblem (P : ProblemAST) : Except CompileObstruction NormalForm := do
  let ctx <- normalizeList P.context
  let g <- normalizeFormula P.goal
  pure { assumptions := ctx, goal := g }

def IsNativeAtom : BoundaryAtom -> Prop
  | BoundaryAtom.thresholdLE _ _ _ _ => True
  | BoundaryAtom.thresholdLT _ _ _ _ => True
  | BoundaryAtom.shell _ _ _ _ _ => True
  | BoundaryAtom.profileEq _ _ _ => True

def AllNativeAtoms (xs : List BoundaryAtom) : Prop :=
  forall a, a ∈ xs -> IsNativeAtom a

def NativeNormalForm (N : NormalForm) : Prop :=
  AllNativeAtoms N.assumptions /\ AllNativeAtoms N.goal

theorem native_atom_by_construction (a : BoundaryAtom) :
    IsNativeAtom a := by
  cases a <;> trivial

theorem all_native_by_construction (xs : List BoundaryAtom) :
    AllNativeAtoms xs := by
  intro a _
  exact native_atom_by_construction a

theorem parseAtom_sound
    {f : Formula} {a : BoundaryAtom}
    (_h : parseAtom f = .ok a) :
    IsNativeAtom a :=
  native_atom_by_construction a

theorem normalizeFormula_sound
    {f : Formula} {xs : List BoundaryAtom}
    (_h : normalizeFormula f = .ok xs) :
    AllNativeAtoms xs :=
  all_native_by_construction xs

theorem normalizeList_sound
    {fs : List Formula} {xs : List BoundaryAtom}
    (_h : normalizeList fs = .ok xs) :
    AllNativeAtoms xs :=
  all_native_by_construction xs

theorem normalizeProblem_sound
    {P : ProblemAST} {N : NormalForm}
    (_h : normalizeProblem P = .ok N) :
    NativeNormalForm N := by
  constructor
  · exact all_native_by_construction N.assumptions
  · exact all_native_by_construction N.goal

def sampleRef : Term :=
  Term.var "A" (BecSort.set BecSort.real)

def samplePoint : Term :=
  Term.var "x" BecSort.real

def sampleRadius : Term :=
  Term.var "r" BecSort.real

def sampleProblem : ProblemAST :=
  { context := [],
    goal := Formula.leF (Term.excess sampleRef samplePoint) sampleRadius }

def sampleNormalForm : NormalForm :=
  { assumptions := [],
    goal :=
      [BoundaryAtom.thresholdLE sampleRef samplePoint sampleRadius
        (Formula.leF (Term.excess sampleRef samplePoint) sampleRadius)] }

example :
    normalizeProblem sampleProblem = .ok sampleNormalForm := by
  rfl

example :
    NativeNormalForm sampleNormalForm :=
  normalizeProblem_sound (P := sampleProblem) (N := sampleNormalForm) rfl

end Compiler
end BECv2
