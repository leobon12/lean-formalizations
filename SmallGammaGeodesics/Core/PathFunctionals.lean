import SmallGammaGeodesics.Frozen.MaxDev
import SmallGammaGeodesics.Frozen.RescaledPath
import SmallGammaGeodesics.Frozen.HorizDev
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Basic properties of the path functionals `maxDev`, `rescaledPath`, `horizDev`

`maxDev` is 1-Lipschitz for the uniform distance (planning audit GA1, (c2)); `rescaledPath s` is
continuous.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace SmallGammaGeodesics

theorem bddAbove_infDist (η : C(unitInterval, ℂ)) :
    BddAbove (range fun t : unitInterval => Metric.infDist (η t) (segment ℝ (0 : ℂ) 1)) :=
  (isCompact_range ((Metric.continuous_infDist_pt _).comp η.continuous)).bddAbove

theorem le_maxDev (η : C(unitInterval, ℂ)) (t : unitInterval) :
    Metric.infDist (η t) (segment ℝ (0 : ℂ) 1) ≤ maxDev η :=
  le_ciSup (bddAbove_infDist η) t

/-- `M` is 1-Lipschitz for the uniform distance, hence continuous and Borel. -/
theorem maxDev_le_add (η η' : C(unitInterval, ℂ)) : maxDev η ≤ maxDev η' + dist η η' := by
  unfold maxDev
  refine ciSup_le fun t => ?_
  calc Metric.infDist (η t) (segment ℝ (0 : ℂ) 1)
      ≤ Metric.infDist (η' t) (segment ℝ (0 : ℂ) 1) + dist (η t) (η' t) :=
        Metric.infDist_le_infDist_add_dist
    _ ≤ (⨆ s : unitInterval, Metric.infDist (η' s) (segment ℝ (0 : ℂ) 1)) + dist η η' :=
        add_le_add (le_ciSup (bddAbove_infDist η') t) (ContinuousMap.dist_apply_le_dist t)

theorem lipschitzWith_maxDev : LipschitzWith 1 maxDev :=
  LipschitzWith.of_le_add maxDev_le_add

theorem measurable_maxDev_comp {Ω : Type*} [MeasurableSpace Ω] {η : Ω → C(unitInterval, ℂ)}
    (hη : Measurable η) : Measurable fun ω => maxDev (η ω) :=
  lipschitzWith_maxDev.continuous.measurable.comp hη

theorem maxDev_nonneg (η : C(unitInterval, ℂ)) : 0 ≤ maxDev η :=
  (Metric.infDist_nonneg).trans (le_maxDev η 0)

theorem continuous_rescaledPath (s : ℝ) : Continuous (rescaledPath s) := by
  have : rescaledPath s =
      fun η => (s : ℂ)⁻¹ • (η - ⟨fun t => ((t : ℝ) : ℂ), by fun_prop⟩) := by
    funext η; ext t; simp [rescaledPath, div_eq_inv_mul]
  rw [this]
  fun_prop

end SmallGammaGeodesics
