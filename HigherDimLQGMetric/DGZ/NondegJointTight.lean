import HigherDimLQGMetric.DGZ.NondegJoint

/-!
# Tightness of the DGZ joint metric laws

The whole-space coordinate and every internal coordinate have tight laws by DGZ Proposition 6.3.
Countable-product tightness makes the laws of the complete state tight.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

/-- The measurable joint laws satisfy the uniform tightness needed for Prokhorov. -/
theorem nd_isTightMeasureSet_joint {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) :
    ∃ q₀ : ℝ≥0∞, 0 < q₀ ∧ q₀ < 1 ∧ ∀ q : ℝ≥0∞, q₀ ≤ q → q < 1 →
      ∀ (r : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        IsDyadicRealization κ P W H →
          IsTightMeasureSet {μ : Measure (nd_Joint d r) |
            ∃ n : ℕ, μ = P.map (nd_jointSample P H ξ q r n)} := by
  obtain ⟨q₀, hq₀0, hq₀1, hwhole⟩ :=
    isTightMeasureSet_normMetricC (cor52Shape d κ ξ Q) h
  obtain ⟨q₁, hq₁0, hq₁1, hlocal⟩ :=
    isTightMeasureSet_internalMetricC_sub (cor52Shape d κ ξ Q) h
  refine ⟨max q₀ q₁, lt_of_lt_of_le hq₀0 (le_max_left _ _),
    max_lt hq₀1 hq₁1, ?_⟩
  intro q hq hq1 r Ω _ P W H hH
  let S : Set (Measure (nd_Joint d r)) :=
    {μ | ∃ n : ℕ, μ = P.map (nd_jointSample P H ξ q r n)}
  change IsTightMeasureSet S
  have hS0 : IsTightMeasureSet (Measure.fst '' S) := by
    refine (hwhole q (le_trans (le_max_left _ _) hq) hq1).subset ?_
    rintro ν ⟨μ, ⟨n, rfl⟩, rfl⟩
    refine ⟨Ω, _, P, W, H, hH, n, ?_⟩
    change (P.map (nd_jointSample P H ξ q r n)).map Prod.fst = _
    exact (Measure.map_map (measurable_fst) (nd_measurable_jointSample hH ξ q r n))
  have hS1 : IsTightMeasureSet (Measure.snd '' S) := by
    apply nd_isTightMeasureSet_pi
    intro i
    refine (hlocal q (le_trans (le_max_right _ _) hq) hq1 (nd_domain r i.1)
      (nd_isOpen_domain r i.1) (nd_isConnected_domain r i.1) i.2).subset ?_
    rintro ν ⟨μ, ⟨ν₀, ⟨n, rfl⟩, rfl⟩, rfl⟩
    refine ⟨Ω, _, P, W, H, hH, n, ?_⟩
    let F := nd_jointSample P H ξ q r n
    have hF : Measurable F := nd_measurable_jointSample hH ξ q r n
    change ((P.map F).map Prod.snd).map (fun f => f i) = _
    calc
      _ = P.map (fun ω => (F ω).2 i) := by
        rw [Measure.map_map (measurable_pi_apply i) measurable_snd,
          Measure.map_map ((measurable_pi_apply i).comp measurable_snd) hF]
        rfl
      _ = _ := rfl
  exact IsTightMeasureSet.prodMk hS0 hS1

end HigherDimLQGMetric.DGZ
