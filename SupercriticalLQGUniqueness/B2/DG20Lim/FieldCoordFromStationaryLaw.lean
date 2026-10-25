import SupercriticalLQGUniqueness.B2.DG20Lim.FieldCoordConvergence
import SupercriticalLQGUniqueness.B2.PfeAxioms.JointLawLimit

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric
open SupercriticalLQGUniqueness.B2.PfeAxioms

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_decoded_field_coords_tendsto_of_stationary_laws
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω' → (CoordJ → ℝ) × RatCoords)
    (V : ℕ → Ω → RatCoords)
    (hY : ∀ n, Measurable (Y n)) (hYlim : Measurable Ylim)
    (hV : ∀ n, Measurable (V n))
    (hLaw : ∀ n, P'.map (Y n) =
      P.map (fun ω => (pairJ ⊤ (h ω), V n ω)))
    (hConv : ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) :
    ∀ᵐ ω ∂P',
      Tendsto (fun n => pairJ ⊤ (pairJInv ⊤ (Y n ω).1)) atTop
        (𝓝 (pairJ ⊤ (pairJInv ⊤ (Ylim ω).1))) := by
  have hFinite (n : ℕ) :
      P'.map (fun ω => (Y n ω).1) = P.map (fun ω => pairJ ⊤ (h ω)) := by
    have hm : Measurable (fun ω => (pairJ ⊤ (h ω), V n ω)) :=
      ((measurable_pairJ ⊤).comp hh).prodMk (hV n)
    calc
      P'.map (fun ω => (Y n ω).1) = (P'.map (Y n)).map Prod.fst :=
        (Measure.map_map measurable_fst (hY n)).symm
      _ = (P.map (fun ω => (pairJ ⊤ (h ω), V n ω))).map Prod.fst := by
        rw [hLaw n]
      _ = P.map (fun ω => pairJ ⊤ (h ω)) := by
        rw [Measure.map_map measurable_fst hm]
        rfl
  have hLimit :
      P'.map (fun ω => (Ylim ω).1) = P.map (fun ω => pairJ ⊤ (h ω)) := by
    symm
    apply (joint_limit_law_eq_of_finite_laws P P'
      (fun _ ω => pairJ ⊤ (h ω))
      (fun n ω => (Y n ω).1)
      (fun ω => pairJ ⊤ (h ω))
      (fun ω => (Ylim ω).1))
    · intro n
      exact ((measurable_pairJ ⊤).comp hh).aemeasurable
    · intro n
      exact (measurable_fst.comp (hY n)).aemeasurable
    · exact ((measurable_pairJ ⊤).comp hh).aemeasurable
    · exact (measurable_fst.comp hYlim).aemeasurable
    · intro n
      exact (hFinite n).symm
    · exact Filter.Eventually.of_forall fun _ => tendsto_const_nhds
    · exact Filter.Eventually.of_forall fun ω =>
        (continuous_fst.tendsto (Ylim ω)).comp (hConv ω)
  have hAll : ∀ᵐ ω ∂P', ∀ n,
      pairJ ⊤ (pairJInv ⊤ (Y n ω).1) = (Y n ω).1 := by
    apply ae_all_iff.mpr
    intro n
    exact ae_pairJ_pairJInv_eq_of_law P' P
      (fun ω => (Y n ω).1) (measurable_fst.comp (hY n))
      h hh (hFinite n)
  have hLim : ∀ᵐ ω ∂P',
      pairJ ⊤ (pairJInv ⊤ (Ylim ω).1) = (Ylim ω).1 :=
    ae_pairJ_pairJInv_eq_of_law P' P
      (fun ω => (Ylim ω).1) (measurable_fst.comp hYlim)
      h hh hLimit
  filter_upwards [hAll, hLim] with ω hω hωlim
  simp_rw [hω]
  rw [hωlim]
  exact (continuous_fst.tendsto (Ylim ω)).comp (hConv ω)

end SupercriticalLQGUniqueness.B2.DG20Lim
