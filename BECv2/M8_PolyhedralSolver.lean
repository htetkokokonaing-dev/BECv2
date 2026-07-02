import Mathlib

namespace BECv2
namespace PolyhedralSolver

def dot {n : Nat} (a x : Fin n -> Rat) : Rat :=
  Finset.univ.sum fun i => a i * x i

structure Polyhedron (n m : Nat) where
  M : Fin m -> Fin n -> Rat
  b : Fin m -> Rat

def Polyhedron.mem {n m : Nat} (P : Polyhedron n m) (y : Fin n -> Rat) : Prop :=
  forall j : Fin m, dot (P.M j) y <= P.b j

inductive NormKind : Type where
  | linf : NormKind
  | l1 : NormKind

structure LInfSlackCert {n m : Nat}
    (P : Polyhedron n m) (x : Fin n -> Rat) (r : Rat) where
  y : Fin n -> Rat
  u : Fin n -> Rat
  poly_mem : P.mem y
  u_nonneg : forall i : Fin n, 0 <= u i
  left_bound : forall i : Fin n, x i - y i <= u i
  right_bound : forall i : Fin n, y i - x i <= u i
  radius_bound : forall i : Fin n, u i <= r

theorem linf_left_radius_bound
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (C : LInfSlackCert P x r) :
    forall i : Fin n, x i - C.y i <= r := by
  intro i
  exact le_trans (C.left_bound i) (C.radius_bound i)

theorem linf_right_radius_bound
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (C : LInfSlackCert P x r) :
    forall i : Fin n, C.y i - x i <= r := by
  intro i
  exact le_trans (C.right_bound i) (C.radius_bound i)

theorem linf_abs_coordinate_bound
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (C : LInfSlackCert P x r) :
    forall i : Fin n, |x i - C.y i| <= r := by
  intro i
  have h_abs : |x i - C.y i| <= C.u i := by
    apply abs_le.mpr
    constructor
    · linarith [C.right_bound i]
    · exact C.left_bound i
  exact le_trans h_abs (C.radius_bound i)

structure L1SlackCert {n m : Nat}
    (P : Polyhedron n m) (x : Fin n -> Rat) (r : Rat) where
  y : Fin n -> Rat
  u : Fin n -> Rat
  poly_mem : P.mem y
  u_nonneg : forall i : Fin n, 0 <= u i
  left_bound : forall i : Fin n, x i - y i <= u i
  right_bound : forall i : Fin n, y i - x i <= u i
  sum_bound : (Finset.univ.sum fun i : Fin n => u i) <= r

theorem l1_abs_coordinate_bound
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (C : L1SlackCert P x r) :
    forall i : Fin n, |x i - C.y i| <= C.u i := by
  intro i
  apply abs_le.mpr
  constructor
  · linarith [C.right_bound i]
  · exact C.left_bound i

theorem l1_abs_sum_le_radius
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (C : L1SlackCert P x r) :
    (Finset.univ.sum fun i : Fin n => |x i - C.y i|) <= r := by
  calc
    (Finset.univ.sum fun i : Fin n => |x i - C.y i|)
        <= (Finset.univ.sum fun i : Fin n => C.u i) := by
          apply Finset.sum_le_sum
          intro i _
          exact l1_abs_coordinate_bound C i
    _ <= r := C.sum_bound

inductive LinearRel : Type where
  | le : LinearRel
  | lt : LinearRel
  | eq : LinearRel

structure LinearIneq (n : Nat) where
  coeff : Fin n -> Rat
  rhs : Rat
  rel : LinearRel

structure PolyhedralThresholdProblem (n m : Nat) where
  poly : Polyhedron n m
  point : Fin n -> Rat
  radius : Rat
  norm : NormKind

inductive EncodedConstraint (n : Nat) : Type where
  | linear : LinearIneq n -> EncodedConstraint n
  | nonneg : (Fin n -> Rat) -> EncodedConstraint n
  | sumLe : (Fin n -> Rat) -> Rat -> EncodedConstraint n

structure LInfEncoding {n m : Nat}
    (P : Polyhedron n m) (x : Fin n -> Rat) (r : Rat) where
  cert : LInfSlackCert P x r

structure L1Encoding {n m : Nat}
    (P : Polyhedron n m) (x : Fin n -> Rat) (r : Rat) where
  cert : L1SlackCert P x r

def PolyhedralThresholdProblem.certType
    {n m : Nat} (Q : PolyhedralThresholdProblem n m) : Type :=
  match Q.norm with
  | NormKind.linf => LInfEncoding Q.poly Q.point Q.radius
  | NormKind.l1 => L1Encoding Q.poly Q.point Q.radius

structure CheckedBackendResult where
  backendName : String
  checked : Bool
  checked_eq_true : checked = true

structure SolverSoundnessBridge
    {n m : Nat} (Q : PolyhedralThresholdProblem n m) where
  accept : CheckedBackendResult -> Q.certType

def bridge_accept
    {n m : Nat} {Q : PolyhedralThresholdProblem n m}
    (B : SolverSoundnessBridge Q)
    (R : CheckedBackendResult) :
    Q.certType :=
  B.accept R

def bridge_accepts_checked_result
    {n m : Nat} {Q : PolyhedralThresholdProblem n m}
    (B : SolverSoundnessBridge Q)
    (R : CheckedBackendResult) :
    Q.certType :=
  bridge_accept B R

end PolyhedralSolver
end BECv2
