import HigherDimLQGContinuity.Core.Interfaces

/-!
# Interface `Lemma43Confine` (orchestrator-owned; ruling N23)

Lemma 4.3(a) of [C] (Part B `b:lem43`(a)): the confinement of a geodesic segment of the modified primary metric between
its first and last visits to the collector annulus `C`. The text is the interface audit's (IA1, MINOR-1; type-checked in
its probe `V2Consumer.lean`), frozen so that the upper count (packet Q9) can run in parallel with its producer (packet
Q6). Hypotheses: those of `Lemma43Forcing` without the trigger. Producer: Q6 (`lemma43_confine`, adapted to this
statement by the orchestrator if its binders differ); consumer: Q9.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- **Lemma 4.3(a)** (confinement; Part B `b:lem43`(a), steps (0)–(2) of its proof). -/
def Lemma43Confine (d : ℕ) : Prop :=
  ∀ {D E D' E' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ η M θ h δsep ε₀ εnet εatt aout H b v d₀ Ω : ℝ},
    ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ →
    IsWeylInternal ξ (-f) D D' → IsWeylInternal η (-f) E E' →
    0 ≤ ξ → 0 ≤ η → 0 < d₀ → |η - ξ| * M ≤ Ω → 0 < v → v ≤ 1 / 100 → Ω ≤ v / 100 →
    3 * ε₀ < 2 * aout → εnet ≤ ε₀ → 4 * h ≤ δsep → 2 * εatt + εnet < H⁻¹ * (δsep / 2) ^ b →
    ∀ (P : ℝ → Rd d) (a c : ℝ), IsGeodSeg D' P a c → P a ∉ siteB d → P c ∉ siteB d →
    (∃ t ∈ Icc a c, P t ∈ siteC d) →
      a < firstVisit P a c (siteC d) ∧ lastVisit P a c (siteC d) < c ∧
      D'.len P (firstVisit P a c (siteC d)) (lastVisit P a c (siteC d)) ≤ ENNReal.ofReal (3 * ε₀) ∧
      ∀ τ ∈ Icc (firstVisit P a c (siteC d)) (lastVisit P a c (siteC d)), P τ ∈ siteA d

end HigherDimLQGContinuity
