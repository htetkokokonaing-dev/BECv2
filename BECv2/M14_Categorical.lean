import Mathlib

namespace BECv2
namespace Categorical

universe u v w u₂ v₂ w₂ u₃ v₃ w₃

structure ClaimKernel where
  Claim : Type u
  Cert : Claim -> Type v
  Route : Claim -> Claim -> Type w
  idRoute : (p : Claim) -> Route p p
  compRoute : {p q r : Claim} -> Route p q -> Route q r -> Route p r
  transport : {p q : Claim} -> Route p q -> Cert p -> Cert q
  transport_id : forall {p : Claim} (c : Cert p),
    transport (idRoute p) c = c
  transport_comp :
    forall {p q r : Claim} (rho : Route p q) (sigma : Route q r)
      (c : Cert p),
      transport (compRoute rho sigma) c =
        transport sigma (transport rho c)

theorem transport_id_apply
    (K : ClaimKernel.{u, v, w})
    {p : K.Claim} (c : K.Cert p) :
    K.transport (K.idRoute p) c = c :=
  K.transport_id c

theorem transport_comp_apply
    (K : ClaimKernel.{u, v, w})
    {p q r : K.Claim}
    (rho : K.Route p q) (sigma : K.Route q r)
    (c : K.Cert p) :
    K.transport (K.compRoute rho sigma) c =
      K.transport sigma (K.transport rho c) :=
  K.transport_comp rho sigma c

structure KernelMorphism
    (K : ClaimKernel.{u, v, w})
    (L : ClaimKernel.{u₂, v₂, w₂}) where
  mapClaim : K.Claim -> L.Claim
  mapRoute : {p q : K.Claim} ->
    K.Route p q -> L.Route (mapClaim p) (mapClaim q)
  mapCert : {p : K.Claim} ->
    K.Cert p -> L.Cert (mapClaim p)
  naturality :
    forall {p q : K.Claim} (rho : K.Route p q) (c : K.Cert p),
      mapCert (K.transport rho c) =
        L.transport (mapRoute rho) (mapCert c)

namespace KernelMorphism

def id (K : ClaimKernel.{u, v, w}) :
    KernelMorphism K K where
  mapClaim := fun p => p
  mapRoute := fun rho => rho
  mapCert := fun c => c
  naturality := by
    intro p q rho c
    rfl

def comp
    {K : ClaimKernel.{u, v, w}}
    {L : ClaimKernel.{u₂, v₂, w₂}}
    {M : ClaimKernel.{u₃, v₃, w₃}}
    (F : KernelMorphism K L) (G : KernelMorphism L M) :
    KernelMorphism K M where
  mapClaim := fun p => G.mapClaim (F.mapClaim p)
  mapRoute := fun rho => G.mapRoute (F.mapRoute rho)
  mapCert := fun c => G.mapCert (F.mapCert c)
  naturality := by
    intro p q rho c
    calc
      G.mapCert (F.mapCert (K.transport rho c))
          = G.mapCert
              (L.transport (F.mapRoute rho) (F.mapCert c)) := by
            rw [F.naturality rho c]
      _ = M.transport (G.mapRoute (F.mapRoute rho))
              (G.mapCert (F.mapCert c)) := by
            rw [G.naturality (F.mapRoute rho) (F.mapCert c)]

theorem preserves_transport
    {K : ClaimKernel.{u, v, w}}
    {L : ClaimKernel.{u₂, v₂, w₂}}
    (F : KernelMorphism K L)
    {p q : K.Claim} (rho : K.Route p q) (c : K.Cert p) :
    L.transport (F.mapRoute rho) (F.mapCert c) =
      F.mapCert (K.transport rho c) :=
  (F.naturality rho c).symm

end KernelMorphism

structure LaxComparison
    (K : ClaimKernel.{u, v, w})
    (L : ClaimKernel.{u₂, v₂, w₂}) extends KernelMorphism K L where
  routeUnit :
    forall p : K.Claim, L.Route (mapClaim p) (mapClaim p)
  routeComp :
    forall {p q r : K.Claim},
      K.Route p q -> K.Route q r ->
        L.Route (mapClaim p) (mapClaim r)
  unit_sound :
    forall p : K.Claim,
      routeUnit p = L.idRoute (mapClaim p)
  comp_sound :
    forall {p q r : K.Claim}
      (rho : K.Route p q) (sigma : K.Route q r),
      routeComp rho sigma = mapRoute (K.compRoute rho sigma)

theorem lax_unit_is_identity
    {K : ClaimKernel.{u, v, w}}
    {L : ClaimKernel.{u₂, v₂, w₂}}
    (F : LaxComparison K L) (p : K.Claim) :
    F.routeUnit p = L.idRoute (F.mapClaim p) :=
  F.unit_sound p

theorem lax_comp_sound
    {K : ClaimKernel.{u, v, w}}
    {L : ClaimKernel.{u₂, v₂, w₂}}
    (F : LaxComparison K L)
    {p q r : K.Claim}
    (rho : K.Route p q) (sigma : K.Route q r) :
    F.routeComp rho sigma = F.mapRoute (K.compRoute rho sigma) :=
  F.comp_sound rho sigma

theorem lax_comp_transport
    {K : ClaimKernel.{u, v, w}}
    {L : ClaimKernel.{u₂, v₂, w₂}}
    (F : LaxComparison K L)
    {p q r : K.Claim}
    (rho : K.Route p q) (sigma : K.Route q r)
    (c : K.Cert p) :
    F.mapCert (K.transport (K.compRoute rho sigma) c) =
      L.transport (F.mapRoute (K.compRoute rho sigma))
        (F.mapCert c) :=
  F.naturality (K.compRoute rho sigma) c

structure ConservativeComparison
    (K : ClaimKernel.{u, v, w})
    (L : ClaimKernel.{u₂, v₂, w₂}) extends KernelMorphism K L where
  reflectCert : {p : K.Claim} ->
    L.Cert (mapClaim p) -> K.Cert p

def ConservativeComparison.pullbackCert
    {K : ClaimKernel.{u, v, w}}
    {L : ClaimKernel.{u₂, v₂, w₂}}
    (F : ConservativeComparison K L)
    {p : K.Claim} :
    L.Cert (F.mapClaim p) -> K.Cert p :=
  F.reflectCert

structure BoundaryGraph where
  Node : Type u
  Edge : Node -> Node -> Type v

inductive Path (G : BoundaryGraph.{u, v}) :
    G.Node -> G.Node -> Type (max u v) where
  | nil (p : G.Node) : Path G p p
  | cons {p q r : G.Node} :
      G.Edge p q -> Path G q r -> Path G p r

namespace Path

def append {G : BoundaryGraph.{u, v}}
    {p q r : G.Node} :
    Path G p q -> Path G q r -> Path G p r
  | Path.nil _, tau => tau
  | Path.cons e rho, tau => Path.cons e (append rho tau)

def length {G : BoundaryGraph.{u, v}}
    {p q : G.Node} : Path G p q -> Nat
  | Path.nil _ => 0
  | Path.cons _ rho => Nat.succ (length rho)

theorem length_nil {G : BoundaryGraph.{u, v}} (p : G.Node) :
    length (Path.nil p) = 0 :=
  rfl

theorem length_cons {G : BoundaryGraph.{u, v}}
    {p q r : G.Node} (e : G.Edge p q) (rho : Path G q r) :
    length (Path.cons e rho) = Nat.succ (length rho) :=
  rfl

end Path

structure GraphTransport
    (G : BoundaryGraph.{u, v}) where
  Cert : G.Node -> Type w
  edgeTransport : {p q : G.Node} ->
    G.Edge p q -> Cert p -> Cert q

def GraphTransport.pathTransport
    {G : BoundaryGraph.{u, v}}
    (T : GraphTransport.{u, v, w} G)
    {p q : G.Node} :
    Path G p q -> T.Cert p -> T.Cert q
  | Path.nil _, c => c
  | Path.cons e rho, c =>
      T.pathTransport rho (T.edgeTransport e c)

theorem path_transport_nil
    {G : BoundaryGraph.{u, v}}
    (T : GraphTransport.{u, v, w} G)
    {p : G.Node} (c : T.Cert p) :
    T.pathTransport (Path.nil p) c = c :=
  rfl

def UnitKernel : ClaimKernel where
  Claim := Unit
  Cert := fun _ => Unit
  Route := fun _ _ => Unit
  idRoute := fun _ => ()
  compRoute := fun _ _ => ()
  transport := fun _ _ => ()
  transport_id := by
    intro p c
    cases c
    rfl
  transport_comp := by
    intro p q r rho sigma c
    cases c
    rfl

def UnitMorphism : KernelMorphism UnitKernel UnitKernel :=
  KernelMorphism.id UnitKernel

example : UnitKernel.Cert () :=
  ()

example :
    UnitKernel.transport (UnitKernel.idRoute ()) () = () :=
  transport_id_apply UnitKernel ()

end Categorical
end BECv2
