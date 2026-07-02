import Mathlib

namespace BECv2
namespace Foundation

universe u v w z

class BoundaryTypeTheory where
  Ctx : Type u
  Ty : Type v
  Elem : Ty -> Type w
  Ref : Ty -> Type w
  Boundary : {A : Ty} -> Ref A -> Type w

  Assump : Type z
  hasAssump : Ctx -> Assump -> Prop

  ExcessVal : Type z
  le : ExcessVal -> ExcessVal -> Prop
  zero : ExcessVal
  top : ExcessVal
  excess : {A : Ty} -> Ref A -> Elem A -> ExcessVal

  Form : Type z
  holds : Ctx -> Form -> Prop

  Cert : Ctx -> Form -> Type z
  Obstruction : Ctx -> Form -> Type z

  Route : Form -> Form -> Type z
  requires : {phi psi : Form} -> Route phi psi -> Set Assump

  cert_sound : forall {Gamma : Ctx} {phi : Form}, Cert Gamma phi -> holds Gamma phi

  obstruction_of_missing :
    forall {Gamma : Ctx} {phi psi : Form} (rho : Route phi psi),
      (exists a : Assump, a ∈ requires rho /\ Not (hasAssump Gamma a)) ->
        Obstruction Gamma psi

inductive PrimitiveJudgment
    (BT : BoundaryTypeTheory.{u, v, w, z}) :
    Type (max (max u v) (max w z)) where
  | isType :
      BT.Ctx -> BT.Ty -> PrimitiveJudgment BT
  | isRef :
      (Gamma : BT.Ctx) -> (A : BT.Ty) -> BT.Ref A -> PrimitiveJudgment BT
  | isBoundary :
      (Gamma : BT.Ctx) -> {A : BT.Ty} -> (R : BT.Ref A) ->
        BT.Boundary R -> PrimitiveJudgment BT
  | isElem :
      (Gamma : BT.Ctx) -> (A : BT.Ty) -> BT.Elem A -> PrimitiveJudgment BT
  | hasExcess :
      (Gamma : BT.Ctx) -> {A : BT.Ty} -> (R : BT.Ref A) ->
        BT.Elem A -> BT.ExcessVal -> PrimitiveJudgment BT
  | thresholdMem :
      (Gamma : BT.Ctx) -> {A : BT.Ty} -> (R : BT.Ref A) ->
        BT.Elem A -> BT.ExcessVal -> PrimitiveJudgment BT
  | hasCert :
      (Gamma : BT.Ctx) -> (phi : BT.Form) ->
        BT.Cert Gamma phi -> PrimitiveJudgment BT
  | hasObstruction :
      (Gamma : BT.Ctx) -> (phi : BT.Form) ->
        BT.Obstruction Gamma phi -> PrimitiveJudgment BT

def thresholdPred
    (BT : BoundaryTypeTheory.{u, v, w, z})
    {A : BT.Ty} (R : BT.Ref A) (r : BT.ExcessVal) :
    BT.Elem A -> Prop :=
  fun x => BT.le (BT.excess R x) r

def shellPred
    (BT : BoundaryTypeTheory.{u, v, w, z})
    {A : BT.Ty} (R : BT.Ref A)
    (r s : BT.ExcessVal)
    (lt : BT.ExcessVal -> BT.ExcessVal -> Prop) :
    BT.Elem A -> Prop :=
  fun x => lt r (BT.excess R x) /\ BT.le (BT.excess R x) s

structure ConservativeInterpretation
    (BT : BoundaryTypeTheory.{u, v, w, z}) where
  interpTy : BT.Ty -> Type w
  interpForm : BT.Form -> Prop
  soundCert :
    forall {Gamma : BT.Ctx} {phi : BT.Form},
      BT.Cert Gamma phi -> interpForm phi

structure BTTLogic
    (BT : BoundaryTypeTheory.{u, v, w, z}) where
  B1_zero_le : forall x : BT.ExcessVal, BT.le BT.zero x
  B1_le_top : forall x : BT.ExcessVal, BT.le x BT.top

  B2_threshold_intro :
    forall {A : BT.Ty} (R : BT.Ref A) (r : BT.ExcessVal) (x : BT.Elem A),
      BT.le (BT.excess R x) r -> thresholdPred BT R r x

  B3_shell_intro :
    forall {A : BT.Ty} (R : BT.Ref A) (r s : BT.ExcessVal)
      (lt : BT.ExcessVal -> BT.ExcessVal -> Prop) (x : BT.Elem A),
      lt r (BT.excess R x) ->
      BT.le (BT.excess R x) s ->
      shellPred BT R r s lt x

  B4_profile_extensionality :
    forall {A : BT.Ty} (R S : BT.Ref A),
      (forall x : BT.Elem A, BT.excess R x = BT.excess S x) ->
        Prop

  B5_certificate_sound :
    forall {Gamma : BT.Ctx} {phi : BT.Form},
      BT.Cert Gamma phi -> BT.holds Gamma phi

  B6_obstruction_honesty :
    forall {Gamma : BT.Ctx} {phi psi : BT.Form} (rho : BT.Route phi psi),
      (exists a : BT.Assump,
        a ∈ BT.requires rho /\ Not (BT.hasAssump Gamma a)) ->
        BT.Obstruction Gamma psi

  B7_route_available :
    forall phi psi : BT.Form, BT.Route phi psi -> Prop

  B8_conservative_interpretation :
    Nonempty (ConservativeInterpretation BT)

theorem btt_cert_sound
    (BT : BoundaryTypeTheory.{u, v, w, z})
    {Gamma : BT.Ctx} {phi : BT.Form}
    (C : BT.Cert Gamma phi) :
    BT.holds Gamma phi :=
  BT.cert_sound C

def btt_obstruction_honesty
    (BT : BoundaryTypeTheory.{u, v, w, z})
    {Gamma : BT.Ctx} {phi psi : BT.Form}
    (rho : BT.Route phi psi)
    (h : exists a : BT.Assump,
      a ∈ BT.requires rho /\ Not (BT.hasAssump Gamma a)) :
    BT.Obstruction Gamma psi :=
  BT.obstruction_of_missing rho h

theorem conservative_certificate_sound
    {BT : BoundaryTypeTheory.{u, v, w, z}}
    (I : ConservativeInterpretation BT)
    {Gamma : BT.Ctx} {phi : BT.Form}
    (C : BT.Cert Gamma phi) :
    I.interpForm phi :=
  I.soundCert C

@[reducible] def TrivialBTT : BoundaryTypeTheory where
  Ctx := Unit
  Ty := Unit
  Elem := fun _ => Unit
  Ref := fun _ => Unit
  Boundary := fun _ => Unit
  Assump := Empty
  hasAssump := fun _ a => nomatch a
  ExcessVal := Unit
  le := fun _ _ => True
  zero := ()
  top := ()
  excess := fun _ _ => ()
  Form := Unit
  holds := fun _ _ => True
  Cert := fun _ _ => Unit
  Obstruction := fun _ _ => Unit
  Route := fun _ _ => Unit
  requires := fun _ => ∅
  cert_sound := by
    intro Gamma phi C
    trivial
  obstruction_of_missing := by
    intro Gamma phi psi rho h
    exact ()

def TrivialInterpretation : ConservativeInterpretation TrivialBTT where
  interpTy := fun _ => Unit
  interpForm := fun _ => True
  soundCert := by
    intro Gamma phi C
    trivial

example :
    TrivialBTT.holds () () :=
  btt_cert_sound TrivialBTT (Gamma := ()) (phi := ()) ()

example :
    TrivialInterpretation.interpForm () :=
  conservative_certificate_sound
    (BT := TrivialBTT)
    TrivialInterpretation
    (Gamma := ())
    (phi := ())
    ()

end Foundation
end BECv2
