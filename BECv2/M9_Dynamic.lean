import Mathlib

namespace BECv2
namespace Dynamic

universe u v w

structure CutLocusCertificate (Time : Type u) (State : Type v) where
  smoothRegion : Time -> Set State
  localTimeCorrection : Time -> State -> Real
  correction_nonneg : forall t x, 0 <= localTimeCorrection t x

structure BoundaryProcess where
  Time : Type u
  State : Type v
  RefAt : Time -> Type w
  boundary : (t : Time) -> RefAt t
  excessT : (t : Time) -> RefAt t -> State -> Real
  phi : Time -> State -> Real
  cutCert : CutLocusCertificate Time State

def boundaryValue (D : BoundaryProcess.{u, v, w})
    (t : D.Time) (x : D.State) : Real :=
  D.excessT t (D.boundary t) x

structure GeneratorBound (D : BoundaryProcess.{u, v, w}) where
  kappa : Real
  c : Real
  generator : D.Time -> D.State -> Real
  timeDerivative : D.Time -> D.State -> Real
  kappa_nonneg : 0 <= kappa
  bound :
    forall t x,
      timeDerivative t x + generator t x <=
        -kappa * D.phi t x + c

theorem generator_bound_at
    {D : BoundaryProcess.{u, v, w}}
    (G : GeneratorBound D)
    (t : D.Time) (x : D.State) :
    G.timeDerivative t x + G.generator t x <=
      -G.kappa * D.phi t x + G.c :=
  G.bound t x

structure MomentEnvelope where
  initial : Real
  driftCap : Real
  horizonWeight : Real
  value : Real
  value_eq : value = initial + driftCap * horizonWeight

structure DynamicRiskCertificate (D : BoundaryProcess.{u, v, w}) where
  horizon : D.Time
  radius : Real
  alpha : Real
  momentBound : Real
  radius_pos : 0 < radius
  moment_nonneg : 0 <= momentBound
  safetyInequality : alpha <= 1 - momentBound / radius
  generatorBound : GeneratorBound D

theorem dynamic_certificate_safety
    {D : BoundaryProcess.{u, v, w}}
    (C : DynamicRiskCertificate D) :
    C.alpha <= 1 - C.momentBound / C.radius :=
  C.safetyInequality

theorem radius_nonzero
    {D : BoundaryProcess.{u, v, w}}
    (C : DynamicRiskCertificate D) :
    C.radius ≠ 0 := by
  exact ne_of_gt C.radius_pos

theorem moment_ratio_nonneg
    {D : BoundaryProcess.{u, v, w}}
    (C : DynamicRiskCertificate D) :
    0 <= C.momentBound / C.radius := by
  exact div_nonneg C.moment_nonneg (le_of_lt C.radius_pos)

theorem safety_upper_bound
    {D : BoundaryProcess.{u, v, w}}
    (C : DynamicRiskCertificate D) :
    C.alpha + C.momentBound / C.radius <= 1 := by
  linarith [C.safetyInequality]

structure LocalTimeBound (D : BoundaryProcess.{u, v, w}) where
  correctionBound : Real
  correctionBound_nonneg : 0 <= correctionBound
  bound :
    forall t x,
      D.cutCert.localTimeCorrection t x <= correctionBound

theorem local_time_correction_nonneg
    {D : BoundaryProcess.{u, v, w}}
    (t : D.Time) (x : D.State) :
    0 <= D.cutCert.localTimeCorrection t x :=
  D.cutCert.correction_nonneg t x

theorem local_time_correction_interval
    {D : BoundaryProcess.{u, v, w}}
    (L : LocalTimeBound D)
    (t : D.Time) (x : D.State) :
    0 <= D.cutCert.localTimeCorrection t x /\
      D.cutCert.localTimeCorrection t x <= L.correctionBound := by
  constructor
  · exact local_time_correction_nonneg t x
  · exact L.bound t x

structure DynamicCertificatePackage (D : BoundaryProcess.{u, v, w}) where
  risk : DynamicRiskCertificate D
  localTime : LocalTimeBound D

theorem package_safety
    {D : BoundaryProcess.{u, v, w}}
    (P : DynamicCertificatePackage D) :
    P.risk.alpha <= 1 - P.risk.momentBound / P.risk.radius :=
  dynamic_certificate_safety P.risk

theorem package_local_time_bound
    {D : BoundaryProcess.{u, v, w}}
    (P : DynamicCertificatePackage D)
    (t : D.Time) (x : D.State) :
    D.cutCert.localTimeCorrection t x <= P.localTime.correctionBound :=
  P.localTime.bound t x

structure DiscreteTimeState where
  value : Real

def toyCutCert : CutLocusCertificate Unit DiscreteTimeState where
  smoothRegion := fun _ => Set.univ
  localTimeCorrection := fun _ _ => 0
  correction_nonneg := by
    intro t x
    norm_num

def toyProcess : BoundaryProcess where
  Time := Unit
  State := DiscreteTimeState
  RefAt := fun _ => Unit
  boundary := fun _ => ()
  excessT := fun _ _ x => x.value
  phi := fun _ x => x.value
  cutCert := toyCutCert

def toyGeneratorBound : GeneratorBound toyProcess where
  kappa := 0
  c := 0
  generator := fun _ _ => 0
  timeDerivative := fun _ _ => 0
  kappa_nonneg := by
    norm_num
  bound := by
    intro t x
    simp

def toyRiskCertificate : DynamicRiskCertificate toyProcess where
  horizon := ()
  radius := 1
  alpha := 0
  momentBound := 0
  radius_pos := by
    norm_num
  moment_nonneg := by
    norm_num
  safetyInequality := by
    norm_num
  generatorBound := toyGeneratorBound

example :
    toyRiskCertificate.alpha <=
      1 - toyRiskCertificate.momentBound / toyRiskCertificate.radius :=
  dynamic_certificate_safety toyRiskCertificate

end Dynamic
end BECv2
