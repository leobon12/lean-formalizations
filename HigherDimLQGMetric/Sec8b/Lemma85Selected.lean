import HigherDimLQGMetric.Sec8b.Lemma85Det
import HigherDimLQGMetric.Sec8b.Lemma85Uniform

/-! The original selected path is a geodesic on one almost-sure event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_selected_geod_ae {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (hd : 3 ≤ d) {ξ Q : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (x y : Rd d) :
    ∀ᵐ ω ∂P,
      let path := s7b_realPath (sec8Sel x y (D (h ω)).1)
      IsGeod (D (h ω)) path ∧ path 0 = x ∧ path 1 = y := by
  filter_upwards [hD.length P h hh.isLGFPlusCont,
    lemma27_proper hd hξ hQ hD P h hh] with ω hlen hproper
  letI : ProperSpace (D (h ω)).Space := hproper
  have hsel : IsConstSpeedGeod (D (h ω)) x y
      (sec8Sel x y (D (h ω)).1) :=
    ((exists_measurable_geodSelector x y).choose_spec.2 _
      (sec8_exists_constSpeedGeod (D (h ω)) hlen x y)).1
  exact ⟨s7b_constSpeed_isGeod (D (h ω)) x y _ hsel,
    by simpa only [s7b_realPath_zero] using hsel.1,
    by simpa only [s7b_realPath_one] using hsel.2.1⟩

end HigherDimLQGMetric
