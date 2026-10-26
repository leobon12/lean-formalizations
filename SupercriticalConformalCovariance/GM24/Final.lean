import SupercriticalConformalCovariance.GM24.Main
import SupercriticalConformalCovariance.GM24.Meas

/-! Normalized IG4 interface retained for the input-free GM (2.6) proof. The superseded
conditional route is in `SupercriticalConformalCovariance.GM24.Superseded`. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter Topology
open scoped ENNReal
open LQGMetric QuantumZipper SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GM24

open SupercriticalConformalCovariance.ZBConformal
open SmallGammaGeodesics.CC (confPullOnCLM coe_confPullOnCLM testOnOfSupp)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- **IG4 Prop 2.10(i) on normalized fields**, uniform form: for every `ε > 0` there is `ρ` such that
zero-boundary GFFs on bounded domains containing `B ∪ B̄_ρ` have normalized restrictions to `B` within
TV distance `ε` of the whole-plane one. Discharged by the total-variation module's theorem `ig4NrmInput_of_TV1` in `IG4Bridge.lean`. -/
def IG4NrmInput {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC) (B : Opens ℂ)
    (fr : TestOn B) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, ∀ (V : Opens ℂ) (hBV : B ≤ V),
    Bornology.IsBounded (V : Set ℂ) → closedBall (0 : ℂ) ρ ⊆ V →
    ∀ z : Ω → DistOn V, IsZeroBoundaryGFF V z P →
      TV.tvDist (P.map (nrm fr ∘ fun ω => restrictDist hBV (z ω)))
        (P.map (nrm fr ∘ fun ω => restrictTo B (h ω))) ≤ ε

end SupercriticalConformalCovariance.GM24
