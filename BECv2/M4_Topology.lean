import Mathlib

namespace BECv2
namespace TopologyFragment

universe u

inductive BoolV : Type where
  | zero : BoolV
  | one : BoolV
  deriving DecidableEq

namespace BoolV

def le : BoolV -> BoolV -> Prop
  | zero, _ => True
  | one, one => True
  | one, zero => False

def lt (x y : BoolV) : Prop :=
  le x y /\ Not (le y x)

def op : BoolV -> BoolV -> BoolV
  | zero, y => y
  | x, zero => x
  | one, one => one

theorem le_refl (x : BoolV) : le x x := by
  cases x <;> trivial

theorem le_trans {x y z : BoolV} :
    le x y -> le y z -> le x z := by
  intro hxy hyz
  cases x <;> cases y <;> cases z <;> trivial

theorem le_antisymm {x y : BoolV} :
    le x y -> le y x -> x = y := by
  intro hxy hyx
  cases x <;> cases y <;> try rfl
  · cases hyx
  · cases hxy

theorem zero_le (x : BoolV) : le zero x := by
  cases x <;> trivial

theorem le_one (x : BoolV) : le x one := by
  cases x <;> trivial

theorem op_assoc (x y z : BoolV) :
    op (op x y) z = op x (op y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem zero_op (x : BoolV) : op zero x = x := by
  cases x <;> rfl

theorem op_zero (x : BoolV) : op x zero = x := by
  cases x <;> rfl

theorem op_comm (x y : BoolV) : op x y = op y x := by
  cases x <;> cases y <;> rfl

theorem op_le_op_left {x y : BoolV}
    (hxy : le x y) (z : BoolV) :
    le (op z x) (op z y) := by
  cases x <;> cases y <;> cases z <;> trivial

end BoolV

structure KuratowskiClosure (X : Type u) where
  cl : Set X -> Set X
  cl_empty : cl ∅ = ∅
  subset_cl : forall A : Set X, A ⊆ cl A
  cl_idem : forall A : Set X, cl (cl A) = cl A
  cl_union : forall A B : Set X, cl (A ∪ B) = cl A ∪ cl B

noncomputable def booleanExcess
    {X : Type u} (C : KuratowskiClosure X)
    (A : Set X) (x : X) : BoolV := by
  classical
  exact if x ∈ C.cl A then BoolV.zero else BoolV.one

def booleanThreshold
    {X : Type u} (C : KuratowskiClosure X)
    (A : Set X) (r : BoolV) : Set X :=
  {x | BoolV.le (booleanExcess C A x) r}

theorem boolean_excess_eq_zero_of_mem
    {X : Type u} (C : KuratowskiClosure X) (A : Set X) (x : X)
    (hx : x ∈ C.cl A) :
    booleanExcess C A x = BoolV.zero := by
  classical
  unfold booleanExcess
  simp [hx]

theorem boolean_excess_eq_one_of_not_mem
    {X : Type u} (C : KuratowskiClosure X) (A : Set X) (x : X)
    (hx : x ∉ C.cl A) :
    booleanExcess C A x = BoolV.one := by
  classical
  unfold booleanExcess
  simp [hx]

theorem boolean_threshold_zero_eq_closure
    {X : Type u} (C : KuratowskiClosure X) (A : Set X) :
    booleanThreshold C A BoolV.zero = C.cl A := by
  ext x
  constructor
  · intro hx
    change BoolV.le (booleanExcess C A x) BoolV.zero at hx
    by_contra hnot
    rw [boolean_excess_eq_one_of_not_mem C A x hnot] at hx
    change False at hx
    exact hx
  · intro hx
    change BoolV.le (booleanExcess C A x) BoolV.zero
    rw [boolean_excess_eq_zero_of_mem C A x hx]
    trivial

theorem boolean_threshold_one_eq_univ
    {X : Type u} (C : KuratowskiClosure X) (A : Set X) :
    booleanThreshold C A BoolV.one = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    change BoolV.le (booleanExcess C A x) BoolV.one
    cases h : booleanExcess C A x <;> trivial

theorem closure_subset_threshold_one
    {X : Type u} (C : KuratowskiClosure X) (A : Set X) :
    C.cl A ⊆ booleanThreshold C A BoolV.one := by
  intro x _
  rw [boolean_threshold_one_eq_univ]
  trivial

theorem threshold_zero_subset_threshold_one
    {X : Type u} (C : KuratowskiClosure X) (A : Set X) :
    booleanThreshold C A BoolV.zero ⊆ booleanThreshold C A BoolV.one := by
  intro x _
  rw [boolean_threshold_one_eq_univ]
  trivial

theorem point_in_closure_iff_zero_threshold
    {X : Type u} (C : KuratowskiClosure X) (A : Set X) (x : X) :
    x ∈ C.cl A <-> x ∈ booleanThreshold C A BoolV.zero := by
  constructor
  · intro hx
    rw [boolean_threshold_zero_eq_closure]
    exact hx
  · intro hx
    rw [boolean_threshold_zero_eq_closure] at hx
    exact hx

structure BooleanClosureBEC (X : Type u) where
  closure : KuratowskiClosure X

noncomputable def BooleanClosureBEC.excess
    {X : Type u} (M : BooleanClosureBEC X) :
    Set X -> X -> BoolV :=
  booleanExcess M.closure

def BooleanClosureBEC.threshold
    {X : Type u} (M : BooleanClosureBEC X) :
    Set X -> BoolV -> Set X :=
  fun A r => booleanThreshold M.closure A r

theorem BooleanClosureBEC.threshold_zero_eq_closure
    {X : Type u} (M : BooleanClosureBEC X) (A : Set X) :
    M.threshold A BoolV.zero = M.closure.cl A :=
  boolean_threshold_zero_eq_closure M.closure A

end TopologyFragment
end BECv2
