import LQGMetric.Statement.Thm12

/-!
# Frozen definition: `IsCanonicalLQGMetric`

Anchor of the main theorem's constitutional surface (manifest `GaussianLQG/Frozen/frozen-anchors.json`).
Blueprint v3, Definition `def:metric` (ruling R3): for `γ ∈ (0,2)`, `D^γ_h` is the γ-LQG metric of
Gwynne–Miller (arXiv:1905.00383v3), Theorems 1.1–1.2, the limit in probability, for the local uniform
topology, of `𝔞_ε⁻¹ D^ε_h` as `ε → 0`, where `𝔞_ε` is the lower median of the unrestricted left–right
crossing distance of LFPP for the normalized field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology

namespace GaussianLQG

/-- **The canonical γ-LQG metric** (blueprint Definition `def:metric`; the existence clause of
GM Theorem 1.2, `LQGMetric.theorem12Shape`): a strong γ-LQG metric `D` such that for every
whole-plane GFF plus a bounded continuous function `h`, `𝔞_ε⁻¹ D^ε_h → D_h` in probability for
the local uniform topology on `ℂ × ℂ` as `ε → 0⁺`. -/
def IsCanonicalLQGMetric (γ : ℝ) (D : LQGMetric.DistC → LQGMetric.ContMetric) : Prop :=
  LQGMetric.IsStrongLQGMetric γ D ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC), LQGMetric.IsGFFPlusBddCont h P →
    LQGMetric.TendstoInProbLU P
      (fun ε ω => (LQGMetric.aEps (LQGMetric.xiGamma γ) ε)⁻¹ •
        LQGMetric.lfppDist (LQGMetric.xiGamma γ) ε (h ω))
      (𝓝[>] 0) (fun ω => (D (h ω)).1)

end GaussianLQG
