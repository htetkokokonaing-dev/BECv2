import Mathlib

/-!
# BEC v2.0 Minimum Mathlib Check Kernel

Self-contained compile target for the BEC v2.0 universe, graph layer,
licensed routes, and obstruction extraction.

Clean placeholder scan target.
-/

namespace BECv2

universe u v w a c

class ExcessValue (V : Type u) where
  le : V -> V -> Prop
  lt : V -> V -> Prop
  zero : V
  top : V
  op : V -> V -> V
  le_refl : forall x : V, le x x
  le_trans : forall {x y z : V}, le x y -> le y z -> le x z
  le_antisymm : forall {x y : V}, le x y -> le y x -> x = y
  lt_iff_le_not_le : forall {x y : V}, lt x y <-> le x y /\ Not (le y x)
  zero_le : forall x : V, le zero x
  le_top : forall x : V, le x top
  op_assoc : forall x y z : V, op (op x y) z = op x (op y z)
  zero_op : forall x : V, op zero x = x
  op_zero : forall x : V, op x zero = x
  op_comm : forall x y : V, op x y = op y x
  op_le_op_left : forall {x y : V}, le x y -> forall z : V, le (op z x) (op z y)

structure BECUniverse where
  X : Type u
  Ref : Type v
  V : Type w
  instV : ExcessValue V
  E : Ref -> X -> V
  Assump : Type a
  Claim : Type c
  Cert : Claim -> Type c

def threshold (B : BECUniverse.{u, v, w, a, c}) (A : B.Ref) (r : B.V) : Set B.X :=
  {x | B.instV.le (B.E A x) r}

def strictThreshold (B : BECUniverse.{u, v, w, a, c}) (A : B.Ref) (r : B.V) : Set B.X :=
  {x | B.instV.lt (B.E A x) r}

def shell (B : BECUniverse.{u, v, w, a, c}) (A : B.Ref) (r s : B.V) : Set B.X :=
  {x | B.instV.lt r (B.E A x) /\ B.instV.le (B.E A x) s}

def profile (B : BECUniverse.{u, v, w, a, c}) (A : B.Ref) : B.X -> B.V :=
  fun x => B.E A x

def zeroLocus (B : BECUniverse.{u, v, w, a, c}) (A : B.Ref) : Set B.X :=
  {x | B.E A x = B.instV.zero}

theorem threshold_mono
    (B : BECUniverse.{u, v, w, a, c}) (A : B.Ref) {r s : B.V}
    (hrs : B.instV.le r s) :
    threshold B A r ⊆ threshold B A s := by
  intro x hx
  exact B.instV.le_trans hx hrs

theorem shell_subset_threshold
    (B : BECUniverse.{u, v, w, a, c}) (A : B.Ref) (r s : B.V) :
    shell B A r s ⊆ threshold B A s := by
  intro x hx
  exact hx.2

theorem zeroLocus_subset_threshold
    (B : BECUniverse.{u, v, w, a, c}) (A : B.Ref) (r : B.V)
    (h0r : B.instV.le B.instV.zero r) :
    zeroLocus B A ⊆ threshold B A r := by
  intro x hx
  change B.instV.le (B.E A x) r
  rw [hx]
  exact h0r

structure Obstruction (B : BECUniverse.{u, v, w, a, c}) where
  attempted : B.Claim
  missing : Set B.Assump
  fallback : Option B.Claim

structure BoundaryThresholdGraph (B : BECUniverse.{u, v, w, a, c}) where
  N : Set B.Claim
  EG : Set (B.Claim × B.Claim)
  edge_source_mem : forall {p q : B.Claim}, (p, q) ∈ EG -> p ∈ N
  edge_target_mem : forall {p q : B.Claim}, (p, q) ∈ EG -> q ∈ N
  ell : {e : B.Claim × B.Claim // e ∈ EG} -> Nat
  gamma : {e : B.Claim × B.Claim // e ∈ EG} -> Set B.Assump
  omega : {e : B.Claim × B.Claim // e ∈ EG} -> Obstruction B

namespace BoundaryThresholdGraph

def Edge {B : BECUniverse.{u, v, w, a, c}} (G : BoundaryThresholdGraph B) :=
  {e : B.Claim × B.Claim // e ∈ G.EG}

def edgeSource {B : BECUniverse.{u, v, w, a, c}} (G : BoundaryThresholdGraph B)
    (e : Edge G) : B.Claim :=
  e.val.1

def edgeTarget {B : BECUniverse.{u, v, w, a, c}} (G : BoundaryThresholdGraph B)
    (e : Edge G) : B.Claim :=
  e.val.2

def licensedEdge {B : BECUniverse.{u, v, w, a, c}} (G : BoundaryThresholdGraph B)
    (Gamma : Set B.Assump) (e : Edge G) : Prop :=
  G.gamma e ⊆ Gamma

end BoundaryThresholdGraph

structure EdgeRealizer {B : BECUniverse.{u, v, w, a, c}}
    (G : BoundaryThresholdGraph B) where
  mapCert :
    (e : BoundaryThresholdGraph.Edge G) ->
      B.Cert (BoundaryThresholdGraph.edgeSource G e) ->
      B.Cert (BoundaryThresholdGraph.edgeTarget G e)

namespace Route

inductive RawRoute
    {B : BECUniverse.{u, v, w, a, c}}
    (G : BoundaryThresholdGraph B) :
    B.Claim -> B.Claim -> Type (max (max (max (max u v) w) a) c) where
  | refl (p : B.Claim) :
      RawRoute G p p
  | step {q : B.Claim}
      (e : BoundaryThresholdGraph.Edge G)
      (tail :
        RawRoute G
          (BoundaryThresholdGraph.edgeTarget G e)
          q) :
      RawRoute G
        (BoundaryThresholdGraph.edgeSource G e)
        q

inductive LicensedRoute
    {B : BECUniverse.{u, v, w, a, c}}
    (G : BoundaryThresholdGraph B)
    (Gamma : Set B.Assump) :
    B.Claim -> B.Claim -> Type (max (max (max (max u v) w) a) c) where
  | refl (p : B.Claim) :
      LicensedRoute G Gamma p p
  | step {q : B.Claim}
      (e : BoundaryThresholdGraph.Edge G)
      (hlic : BoundaryThresholdGraph.licensedEdge G Gamma e)
      (tail :
        LicensedRoute G Gamma
          (BoundaryThresholdGraph.edgeTarget G e)
          q) :
      LicensedRoute G Gamma
        (BoundaryThresholdGraph.edgeSource G e)
        q

def licensedRouteTransport
    {B : BECUniverse.{u, v, w, a, c}}
    {G : BoundaryThresholdGraph B}
    {Gamma : Set B.Assump}
    (R : EdgeRealizer G) :
    {p q : B.Claim} ->
      LicensedRoute G Gamma p q ->
      B.Cert p ->
      B.Cert q
  | _, _, LicensedRoute.refl _, cert => cert
  | _, _, LicensedRoute.step e _ tail, cert =>
      licensedRouteTransport R tail (R.mapCert e cert)

def licensedRouteSound
    {B : BECUniverse.{u, v, w, a, c}}
    {G : BoundaryThresholdGraph B}
    {Gamma : Set B.Assump}
    (R : EdgeRealizer G)
    {p q : B.Claim}
    (rho : LicensedRoute G Gamma p q)
    (cert : B.Cert p) :
    B.Cert q :=
  licensedRouteTransport R rho cert

def missingAssumptions
    {B : BECUniverse.{u, v, w, a, c}}
    {G : BoundaryThresholdGraph B}
    (Gamma : Set B.Assump)
    (e : BoundaryThresholdGraph.Edge G) :
    Set B.Assump :=
  G.gamma e \ Gamma

def edgeObstruction
    {B : BECUniverse.{u, v, w, a, c}}
    {G : BoundaryThresholdGraph B}
    (Gamma : Set B.Assump)
    (e : BoundaryThresholdGraph.Edge G) :
    Obstruction B :=
  {
    attempted := BoundaryThresholdGraph.edgeTarget G e
    missing := missingAssumptions Gamma e
    fallback := (G.omega e).fallback
  }

theorem edge_obstruction_missing_eq
    {B : BECUniverse.{u, v, w, a, c}}
    {G : BoundaryThresholdGraph B}
    (Gamma : Set B.Assump)
    (e : BoundaryThresholdGraph.Edge G) :
    (edgeObstruction Gamma e).missing = G.gamma e \ Gamma :=
  rfl

inductive HasUnlicensedEdge
    {B : BECUniverse.{u, v, w, a, c}}
    (G : BoundaryThresholdGraph B)
    (Gamma : Set B.Assump) :
    {p q : B.Claim} ->
      RawRoute G p q ->
      Type (max (max (max (max u v) w) a) c) where
  | head {q : B.Claim}
      (e : BoundaryThresholdGraph.Edge G)
      (tail :
        RawRoute G
          (BoundaryThresholdGraph.edgeTarget G e)
          q)
      (hbad :
        Not (BoundaryThresholdGraph.licensedEdge G Gamma e)) :
      HasUnlicensedEdge G Gamma (RawRoute.step e tail)
  | tail {q : B.Claim}
      (e : BoundaryThresholdGraph.Edge G)
      (tailRoute :
        RawRoute G
          (BoundaryThresholdGraph.edgeTarget G e)
          q)
      (h :
        HasUnlicensedEdge G Gamma tailRoute) :
      HasUnlicensedEdge G Gamma (RawRoute.step e tailRoute)

def obstructionOfUnlicensedRoute
    {B : BECUniverse.{u, v, w, a, c}}
    {G : BoundaryThresholdGraph B}
    {Gamma : Set B.Assump} :
    {p q : B.Claim} ->
      {rho : RawRoute G p q} ->
      HasUnlicensedEdge G Gamma rho ->
      Obstruction B
  | _, _, _, HasUnlicensedEdge.head e _ _ =>
      edgeObstruction Gamma e
  | _, _, _, HasUnlicensedEdge.tail _ _ h =>
      obstructionOfUnlicensedRoute h

theorem obstruction_completeness
    {B : BECUniverse.{u, v, w, a, c}}
    {G : BoundaryThresholdGraph B}
    {Gamma : Set B.Assump}
    {p q : B.Claim}
    {rho : RawRoute G p q}
    (h : HasUnlicensedEdge G Gamma rho) :
    Nonempty (Obstruction B) :=
  ⟨obstructionOfUnlicensedRoute h⟩

end Route
end BECv2
