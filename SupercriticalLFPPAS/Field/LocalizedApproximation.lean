import SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedApprox
import SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF

/-!
# Localized heat fields converge uniformly on compact sets

The pinned polylogarithmic-localization library proves the compact-uniform approximation for
cutoff radius `ε (log ε⁻¹)^q`.  The manuscript's cutoff is exactly its `q = 1` case, including
the normalized convolution by the cutoff mass.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open LQGMetric (DistC heatMollify)
open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF)
open SupercriticalLQGUniqueness.B2.Polylog (plMollify)

namespace SupercriticalLFPPAS.Field

/-- The manuscript's localized heat field at radius `δ log(δ⁻¹)`. This is the `q = 1`
specialization of the pinned PL definition, including its normalizing mass. -/
def localizedHeatField (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) (h : DistC) (z : ℂ) : ℝ :=
  plMollify 1 δ hδ h z

/-- The exponent that makes the PL cutoff radius equal to `δ L`. -/
def uniformLocalizationExponent (δ L : ℝ) : ℝ :=
  Real.log L / Real.log (Real.log δ⁻¹)

/-- The normalized localized field with cutoff radius `δ L`, encoded using the PL family. -/
def uniformLocalizedHeatField (δ L : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (h : DistC) (z : ℂ) : ℝ :=
  plMollify (uniformLocalizationExponent δ L) δ hδ h z

/-- The `q = 1` PL radius is exactly the manuscript's `δ log(δ⁻¹)` radius. -/
theorem plRad_one_eq_localizedRadius (δ : ℝ) :
    SupercriticalLQGUniqueness.B2.Polylog.plRad 1 δ = δ * Real.log δ⁻¹ := by
  simp [SupercriticalLQGUniqueness.B2.Polylog.plRad, Real.rpow_one]

/-- The variable-exponent PL field above has cutoff radius exactly `δ L`. -/
theorem plRad_uniform_eq (δ L : ℝ)
    (ht : 1 < Real.log δ⁻¹) (hL : Real.log δ⁻¹ ≤ L) :
    SupercriticalLQGUniqueness.B2.Polylog.plRad (uniformLocalizationExponent δ L) δ = δ * L := by
  have htpos : 0 < Real.log δ⁻¹ := lt_trans (by norm_num) ht
  have hLpos : 0 < L := lt_of_lt_of_le htpos hL
  have hlogt : Real.log (Real.log δ⁻¹) ≠ 0 := (Real.log_pos ht).ne'
  have hlogt' : Real.log (Real.log (1 / δ)) ≠ 0 := by simpa [one_div] using hlogt
  rw [SupercriticalLQGUniqueness.B2.Polylog.plRad,
    uniformLocalizationExponent, Real.rpow_def_of_pos htpos]
  congr 1
  rw [show Real.log (Real.log δ⁻¹) *
        (Real.log L / Real.log (Real.log δ⁻¹)) = Real.log L by
          field_simp [hlogt']]
  exact Real.exp_log hLpos

/-- For a normalized whole-plane GFF, the manuscript's localized field with cutoff radius
`ε log ε⁻¹` converges to the heat field uniformly on each compact set, almost surely. -/
theorem ae_localizedHeat_tendsto_uniform_on_compact {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (K : Set ℂ) (hK : IsCompact K) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1, ∀ z ∈ K,
        |heatMollify ε (h ω) z - localizedHeatField ε hε (h ω) z| ≤ η := by
  filter_upwards
    [SupercriticalLQGUniqueness.B2.Polylog.lem_localized_approx_sup
      hh.1 (q := 1) (U := K) (by norm_num) hK.isBounded] with ω hω
  intro η hη
  filter_upwards [hω η hη] with ε hεU
  intro hε z hz
  obtain ⟨_, happrox⟩ := hεU hε z (subset_closure hz)
  simpa [localizedHeatField] using happrox

end SupercriticalLFPPAS.Field
