import Mathlib

namespace BECv2
namespace Prob

universe u

structure ProbKernel (Omega : Type u) where
  prob : Set Omega -> Real
  mono : forall {A B : Set Omega}, A ⊆ B -> prob A <= prob B
  inter_lower : forall A B : Set Omega, prob A + prob B - 1 <= prob (A ∩ B)

theorem union_bound_transfer
    {Omega : Type u}
    (K : ProbKernel Omega)
    (P Q R : Set Omega)
    {alpha beta : Real}
    (hPQ : P ∩ Q ⊆ R)
    (hP : alpha <= K.prob P)
    (hQ : beta <= K.prob Q) :
    alpha + beta - 1 <= K.prob R := by
  calc
    alpha + beta - 1 <= K.prob P + K.prob Q - 1 := by
      linarith
    _ <= K.prob (P ∩ Q) := K.inter_lower P Q
    _ <= K.prob R := K.mono hPQ

structure StochasticThreshold where
  alpha : Real
  radius : Real
  eventProb : Real
  licensed : alpha <= eventProb

theorem stochastic_threshold_weaken
    (C : StochasticThreshold)
    {beta : Real}
    (hbeta : beta <= C.alpha) :
    beta <= C.eventProb := by
  exact le_trans hbeta C.licensed

noncomputable def hoeffdingFailure (n : Nat) (eps : Real) : Real :=
  2 * Real.exp (-2 * (n : Real) * eps ^ 2)

noncomputable def hoeffdingConfidence (n : Nat) (eps : Real) : Real :=
  1 - hoeffdingFailure n eps

structure HoeffdingCertificate where
  n : Nat
  phat : Real
  eps : Real
  alpha : Real
  eps_nonneg : 0 <= eps
  empirical_margin : alpha <= phat - eps
  failure : Real
  failure_eq : failure = hoeffdingFailure n eps
  confidence : Real
  confidence_eq : confidence = hoeffdingConfidence n eps

theorem empirical_lower_bound
    {phat p eps alpha : Real}
    (hdev : |phat - p| <= eps)
    (hmargin : alpha <= phat - eps) :
    alpha <= p := by
  have hright : phat - p <= eps := (abs_le.mp hdev).2
  linarith

theorem empirical_certificate_sound
    (C : HoeffdingCertificate)
    {p : Real}
    (hdev : |C.phat - p| <= C.eps) :
    C.alpha <= p :=
  empirical_lower_bound hdev C.empirical_margin

theorem hoeffding_confidence_identity
    (n : Nat) (eps : Real) :
    hoeffdingConfidence n eps =
      1 - 2 * Real.exp (-2 * (n : Real) * eps ^ 2) := by
  rfl

structure EmpiricalBoundaryClaim where
  n : Nat
  radius : Real
  alpha : Real
  phat : Real
  eps : Real
  lowerBound : Real
  lower_eq : lowerBound = phat - eps
  lower_licenses : alpha <= lowerBound

theorem empirical_claim_to_margin
    (C : EmpiricalBoundaryClaim) :
    C.alpha <= C.phat - C.eps := by
  rw [← C.lower_eq]
  exact C.lower_licenses

theorem empirical_claim_sound
    (C : EmpiricalBoundaryClaim)
    {p : Real}
    (hdev : |C.phat - p| <= C.eps) :
    C.alpha <= p := by
  exact empirical_lower_bound hdev (empirical_claim_to_margin C)

structure CompositionCertificate
    {Omega : Type u}
    (K : ProbKernel Omega)
    (P Q R : Set Omega) where
  alpha : Real
  beta : Real
  transfer : P ∩ Q ⊆ R
  p_bound : alpha <= K.prob P
  q_bound : beta <= K.prob Q

theorem composition_certificate_sound
    {Omega : Type u}
    {K : ProbKernel Omega}
    {P Q R : Set Omega}
    (C : CompositionCertificate K P Q R) :
    C.alpha + C.beta - 1 <= K.prob R :=
  union_bound_transfer K P Q R C.transfer C.p_bound C.q_bound

end Prob
end BECv2
