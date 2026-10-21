import SmallGammaGeodesics.Upper.Interfaces
import SmallGammaGeodesics.Core.Setup
import SmallGammaGeodesics.Variance.Clock

/-!
# Shared definitions of the §5–§6 chain (blueprint `s5-upper.tex`, `s6-tightness.tex`; BP2's planned declarations)

Orchestrator-owned and read-only for the workers. These are the objects that the §5 packets (`P-U0`–`P-U3`) and
the §6 packet (`P-T1`) share:
- the scale `δ = ξ^{2/3}`, the logarithm `L = log(1/ξ)`, the top level `J`, the constant `c_β`;
- the imaginary part of a path, the probe grid of mesh `ℓ_j/3`;
- the good event `𝒢 = {Δ₈ ≤ ξ^{99/100}}` (G23), the band event;
- the field normalization `g ↦ g − g₁(0)`, the field-level residual `Z_b`, and the probe pairing `G_θ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open LQGMetric GaussianLQG

/-- `δ = ξ^{2/3}`. -/
def dlt (γ : ℝ) : ℝ := xiGamma γ ^ (2 / 3 : ℝ)

/-- `L = log(1/ξ)`. -/
def Lg (γ : ℝ) : ℝ := Real.log (xiGamma γ)⁻¹

/-- The top probe level `J = ⌈(3/8) log₂(1/ξ)⌉`, so that `ℓ_J ≍ ξ^{3/8}`. -/
def Jxi (ξ : ℝ) : ℕ := ⌈(3 / 8 : ℝ) * Real.logb 2 ξ⁻¹⌉₊

/-- `J` as a function of `γ`. -/
def Jg (γ : ℝ) : ℕ := Jxi (xiGamma γ)

/-- `c_β = (1 − 2^{−1/8})/8`, so that `2 c_β Σ_j ℓ_j^{1/8} ≤ 1/4`. -/
def cBeta : ℝ := (1 - (2 : ℝ) ^ (-(1 / 8 : ℝ))) / 8

/-- The imaginary part of a path, as a function on `ℝ` (constant outside `[0,1]`). -/
def yPath (η : C(unitInterval, ℂ)) (t : ℝ) : ℝ := (η (Set.projIcc 0 1 zero_le_one t)).im

/-- The probe grid of mesh `ℓ_j/3` on `[0,1]` (the grid of P-B1's `lemma41_sampling`). -/
def probeGrid (j : ℕ) : Finset ℝ :=
  (Finset.range (3 * 2 ^ j + 1)).image fun i : ℕ => (i : ℝ) / (3 * 2 ^ j)

/-- The additive Euclidean error of the metric `e^{−b} d` on `B̄_R`; `S.euclidErr γ R ω = euclidErrF (S.b γ) R (S.D γ ω)`. -/
def euclidErrF (b R : ℝ) (d : ContMetric) : ℝ≥0∞ :=
  ⨆ z ∈ Metric.closedBall (0 : ℂ) R, ⨆ w ∈ Metric.closedBall (0 : ℂ) R,
    ENNReal.ofReal |Real.exp (-b) * d.1 (z, w) - ‖z - w‖|

/-- The good event `𝒢 = {Δ₈ ≤ ξ^{99/100}}` (rulings G16, G23). -/
def goodEv (G : GSetup) (γ : ℝ) (ω : Coord) : Prop :=
  G.S.euclidErr γ 8 ω ≤ ENNReal.ofReal (xiGamma γ ^ (99 / 100 : ℝ))

/-- The band event at scale `R`: some probe band at a grid point exceeds `c_β R ℓ_j^{1/8}`. -/
def bandEv (γ R : ℝ) (η : C(unitInterval, ℂ)) : Prop :=
  ∃ j ≤ Jg γ, ∃ a ∈ probeGrid j, cBeta * R * ell j ^ (1 / 8 : ℝ) < |band (yPath η) j a|

/-- The normalization modulo constants `g ↦ g − g₁(0)`. -/
def nrmF (g : DistC) : DistC := addConst g (-circleAvg g 1 0)

/-- The field-level residual `Z_b(g) = log D_g(0,1) − b − ξ (g, λ)`. -/
def Zf (γ b : ℝ) (D : DistC → ContMetric) (g : DistC) : ℝ :=
  Real.log ((D g).1 (0, 1)) - b - xiGamma γ * measPairing g (segMeasure 0 1)

/-- The probe pairing `G_θ(g) = (g, ψ_*λ − λ)`. -/
def probePair (j : ℕ) (a θ : ℝ) (g : DistC) : ℝ :=
  measPairing g ((segMeasure 0 1).map (probeInv j a θ)) - measPairing g (segMeasure 0 1)

end SmallGammaGeodesics
