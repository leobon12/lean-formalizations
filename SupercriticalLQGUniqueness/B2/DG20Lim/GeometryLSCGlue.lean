import SupercriticalLQGUniqueness.B2.DG20Lim.CoupledGeometry
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLSCMetric
import SupercriticalLQGUniqueness.B2.LscTop.Limits

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.DfromR_eq_of_across {R S : RData}
    (h : R.across = S.across) : R.DfromR = S.DfromR := by
  funext x y
  simp only [RData.DfromR, h]

theorem RData.toLSCFun_eq_of_across {R S : RData}
    (h : R.across = S.across)
    (htri : ∀ x y z : ℂ,
      R.DfromR x z ≤ R.DfromR x y + R.DfromR y z) :
    (R.toLSCMetric htri).toLSCFun.1 = S.toLSCFun.1 := by
  funext p
  change (R.DfromR p.1 p.2 : EReal) = (S.DfromR p.1 p.2 : EReal)
  rw [RData.DfromR_eq_of_across h]

theorem ae_geometry_lsc_glue
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω' → (CoordJ → ℝ) × RatCoords)
    (hLSC : ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 ∧
      LSCTendsto
        (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1))
        R.toLSCFun.1)
    (hGeom : ∀ᵐ ω ∂P', ∃ (R : RData)
      (htri : ∀ x y z : ℂ,
        R.DfromR x z ≤ R.DfromR x y + R.DfromR y z),
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 ∧
      (R.toLSCMetric htri).IsLengthSpace ∧
      (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (R.toLSCMetric htri).1 (u, v) < ENNReal.ofReal η →
          dist u v < δ) ∧
      (∀ u v : ℂ, (R.toLSCMetric htri).1 (u, v) < ∞ →
        ∃ (γ : ℝ → ℂ) (a b : ℝ),
          (R.toLSCMetric htri).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
            (R.toLSCMetric htri).len γ a b = (R.toLSCMetric htri).1 (u, v))) :
    ∀ᵐ ω ∂P', ∃ L : LSCMetric,
      LSCTendsto
        (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1))
        L.toLSCFun.1 ∧
      L.IsLengthSpace ∧
      (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, L.1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
      (∀ u v : ℂ, L.1 (u, v) < ∞ →
        ∃ (γ : ℝ → ℂ) (a b : ℝ),
          L.IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
            L.len γ a b = L.1 (u, v)) := by
  filter_upwards [hLSC, hGeom] with ω hLω hGω
  obtain ⟨S, hSa, _, hT⟩ := hLω
  obtain ⟨R, htri, hRa, _, hLength, hEuclid, hGeo⟩ := hGω
  refine ⟨R.toLSCMetric htri, ?_, hLength, hEuclid, hGeo⟩
  rw [RData.toLSCFun_eq_of_across (hRa.trans hSa.symm)]
  exact hT

end SupercriticalLQGUniqueness.B2.DG20Lim
