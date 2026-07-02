import Mathlib

namespace BECv2
namespace BackendImporter

def dot {n : Nat} (a x : Fin n -> Rat) : Rat :=
  Finset.univ.sum fun i => a i * x i

structure Polyhedron (n m : Nat) where
  M : Fin m -> Fin n -> Rat
  b : Fin m -> Rat

def Polyhedron.mem {n m : Nat} (P : Polyhedron n m) (y : Fin n -> Rat) : Prop :=
  forall j : Fin m, dot (P.M j) y <= P.b j

inductive SolverStatus : Type where
  | optimal : SolverStatus
  | feasible : SolverStatus
  | infeasible : SolverStatus
  | unbounded : SolverStatus
  | unknown : SolverStatus

def SolverStatus.accepted : SolverStatus -> Prop
  | SolverStatus.optimal => True
  | SolverStatus.feasible => True
  | SolverStatus.infeasible => False
  | SolverStatus.unbounded => False
  | SolverStatus.unknown => False

inductive BackendNorm : Type where
  | linf : BackendNorm
  | l1 : BackendNorm

structure SolverExport (n : Nat) where
  solverName : String
  sourceHash : String
  status : SolverStatus
  norm : BackendNorm
  y : Fin n -> Rat
  u : Fin n -> Rat
  objective : Rat
  radius : Rat

structure ImportMetadata where
  solverName : String
  sourceHash : String
  status : SolverStatus
  accepted : SolverStatus.accepted status

structure LInfSlackCert {n m : Nat}
    (P : Polyhedron n m) (x : Fin n -> Rat) (r : Rat) where
  y : Fin n -> Rat
  u : Fin n -> Rat
  poly_mem : P.mem y
  u_nonneg : forall i : Fin n, 0 <= u i
  left_bound : forall i : Fin n, x i - y i <= u i
  right_bound : forall i : Fin n, y i - x i <= u i
  radius_bound : forall i : Fin n, u i <= r

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

structure LInfImportWitness {n m : Nat}
    (P : Polyhedron n m) (x : Fin n -> Rat) (r : Rat)
    (R : SolverExport n) where
  tag : Unit
  accepted : SolverStatus.accepted R.status
  norm_ok : R.norm = BackendNorm.linf
  radius_ok : R.radius = r
  poly_mem : P.mem R.y
  u_nonneg : forall i : Fin n, 0 <= R.u i
  left_bound : forall i : Fin n, x i - R.y i <= R.u i
  right_bound : forall i : Fin n, R.y i - x i <= R.u i
  radius_bound : forall i : Fin n, R.u i <= r

structure L1ImportWitness {n m : Nat}
    (P : Polyhedron n m) (x : Fin n -> Rat) (r : Rat)
    (R : SolverExport n) where
  tag : Unit
  accepted : SolverStatus.accepted R.status
  norm_ok : R.norm = BackendNorm.l1
  radius_ok : R.radius = r
  poly_mem : P.mem R.y
  u_nonneg : forall i : Fin n, 0 <= R.u i
  left_bound : forall i : Fin n, x i - R.y i <= R.u i
  right_bound : forall i : Fin n, R.y i - x i <= R.u i
  sum_bound : (Finset.univ.sum fun i : Fin n => R.u i) <= r

def importLInfMeta
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (R : SolverExport n)
    (W : LInfImportWitness P x r R) :
    ImportMetadata :=
  { solverName := R.solverName
    sourceHash := R.sourceHash
    status := R.status
    accepted := W.accepted }

def importLInfCert
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (R : SolverExport n)
    (W : LInfImportWitness P x r R) :
    LInfSlackCert P x r :=
  { y := R.y
    u := R.u
    poly_mem := W.poly_mem
    u_nonneg := W.u_nonneg
    left_bound := W.left_bound
    right_bound := W.right_bound
    radius_bound := W.radius_bound }

def importL1Meta
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (R : SolverExport n)
    (W : L1ImportWitness P x r R) :
    ImportMetadata :=
  { solverName := R.solverName
    sourceHash := R.sourceHash
    status := R.status
    accepted := W.accepted }

def importL1Cert
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (R : SolverExport n)
    (W : L1ImportWitness P x r R) :
    L1SlackCert P x r :=
  { y := R.y
    u := R.u
    poly_mem := W.poly_mem
    u_nonneg := W.u_nonneg
    left_bound := W.left_bound
    right_bound := W.right_bound
    sum_bound := W.sum_bound }

theorem import_linf_status_accepted
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (R : SolverExport n) (W : LInfImportWitness P x r R) :
    SolverStatus.accepted (importLInfMeta R W).status :=
  (importLInfMeta R W).accepted

theorem import_l1_status_accepted
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (R : SolverExport n) (W : L1ImportWitness P x r R) :
    SolverStatus.accepted (importL1Meta R W).status :=
  (importL1Meta R W).accepted

theorem import_linf_norm_agrees
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (R : SolverExport n) (W : LInfImportWitness P x r R) :
    R.norm = BackendNorm.linf :=
  W.norm_ok

theorem import_l1_norm_agrees
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (R : SolverExport n) (W : L1ImportWitness P x r R) :
    R.norm = BackendNorm.l1 :=
  W.norm_ok

theorem import_linf_radius_agrees
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (R : SolverExport n) (W : LInfImportWitness P x r R) :
    R.radius = r :=
  W.radius_ok

theorem import_l1_radius_agrees
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (R : SolverExport n) (W : L1ImportWitness P x r R) :
    R.radius = r :=
  W.radius_ok

theorem imported_linf_abs_bound
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (R : SolverExport n) (W : LInfImportWitness P x r R) :
    forall i : Fin n, |x i - (importLInfCert R W).y i| <= r :=
  linf_abs_coordinate_bound (importLInfCert R W)

theorem imported_l1_abs_sum_bound
    {n m : Nat} {P : Polyhedron n m} {x : Fin n -> Rat} {r : Rat}
    (R : SolverExport n) (W : L1ImportWitness P x r R) :
    (Finset.univ.sum fun i : Fin n =>
      |x i - (importL1Cert R W).y i|) <= r :=
  l1_abs_sum_le_radius (importL1Cert R W)

structure BackendImportContract (n m : Nat) where
  poly : Polyhedron n m
  point : Fin n -> Rat
  radius : Rat
  solverExport : SolverExport n

def contractImportLInfCert
    {n m : Nat} (C : BackendImportContract n m)
    (W : LInfImportWitness C.poly C.point C.radius C.solverExport) :
    LInfSlackCert C.poly C.point C.radius :=
  importLInfCert C.solverExport W

def contractImportL1Cert
    {n m : Nat} (C : BackendImportContract n m)
    (W : L1ImportWitness C.poly C.point C.radius C.solverExport) :
    L1SlackCert C.poly C.point C.radius :=
  importL1Cert C.solverExport W

end BackendImporter
end BECv2
