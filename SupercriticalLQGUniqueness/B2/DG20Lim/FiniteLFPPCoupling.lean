import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLFPP

 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
def finiteMetricE (D : ContMetric) (p : ℂ × ℂ) : EReal :=
  ((ENNReal.ofReal (D.1 p) : ℝ≥0∞) : EReal)

theorem continuous_finiteMetricE (D : ContMetric) : Continuous (finiteMetricE D) := by
  change Continuous (fun p => ((ENNReal.ofReal (D.1 p) : ℝ≥0∞) : EReal))
  exact
  continuous_coe_ennreal_ereal.comp
    (ENNReal.continuous_ofReal.comp D.1.continuous)

theorem measurable_finiteMetricE : Measurable finiteMetricE := by
  apply measurable_pi_iff.mpr
  intro p
  have hEval : Measurable (fun D : ContMetric => D.1 p) :=
    (continuous_eval_const p).measurable.comp measurable_subtype_coe
  exact continuous_coe_ennreal_ereal.measurable.comp
    (ENNReal.continuous_ofReal.measurable.comp hEval)

 

theorem joint_law_rescaledLFPP_of_finite_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    (h : Ω → DistC) (hh : Measurable h) (D : Ω → ContMetric)
    (hD : AEMeasurable D P)
    (Y : Ω' → (CoordJ → ℝ) × RatCoords) (hY : Measurable Y)
    (hlaw : P'.map (fun ω => decodeFinitePair (Y ω)) =
      P.map (fun ω => (h ω, D ω)))
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ))
    (hDX : ∀ ω, D ω = normalizedContLFPP ξ a (X ω)) :
    P'.map (fun ω =>
      (pairJInv ⊤ (Y ω).1, finiteMetricE (circleCoordsInv (Y ω).2.1))) =
      P.map (fun ω => (h ω, rescaledLFPP ξ a (X ω))) := by
  let T : DistC × ContMetric → DistC × (ℂ × ℂ → EReal) :=
    fun q => (q.1, finiteMetricE q.2)
  have hT : Measurable T :=
    measurable_fst.prodMk (measurable_finiteMetricE.comp measurable_snd)
  have hDec : Measurable (fun ω => decodeFinitePair (Y ω)) :=
    measurable_decodeFinitePair.comp hY
  have hSource : AEMeasurable (fun ω => (h ω, D ω)) P :=
    hh.aemeasurable.prodMk hD
  have hpoint : ∀ ω, T (h ω, D ω) =
      (h ω, rescaledLFPP ξ a (X ω)) := by
    intro ω
    apply Prod.ext
    · rfl
    · funext p
      rw [hDX ω]
      exact normalizedContLFPP_to_rescaledLFPP ξ a (X ω) p
  calc
    P'.map (fun ω =>
        (pairJInv ⊤ (Y ω).1, finiteMetricE (circleCoordsInv (Y ω).2.1))) =
        (P'.map (fun ω => decodeFinitePair (Y ω))).map T := by
          exact (Measure.map_map hT hDec).symm
    _ = (P.map (fun ω => (h ω, D ω))).map T := by rw [hlaw]
    _ = P.map (fun ω => T (h ω, D ω)) := by
      exact AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hSource
    _ = P.map (fun ω => (h ω, rescaledLFPP ξ a (X ω))) := by
      exact Measure.map_congr (Filter.Eventually.of_forall hpoint)

end SupercriticalLQGUniqueness.B2.DG20Lim
