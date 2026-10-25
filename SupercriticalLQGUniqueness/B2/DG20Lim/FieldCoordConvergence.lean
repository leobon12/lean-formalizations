import SupercriticalLQGUniqueness.B2.DG20Lim.Section51
import LQGMetric.Field.StandardBorelRange

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem ae_pairJ_pairJInv_eq_of_law
    {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    (P : Measure Ω) (P₀ : Measure Ω₀)
    (Y : Ω → CoordJ → ℝ) (hY : Measurable Y)
    (g : Ω₀ → DistC) (hg : Measurable g)
    (hLaw : P.map Y = P₀.map (fun ω => pairJ ⊤ (g ω))) :
    ∀ᵐ ω ∂P, pairJ ⊤ (pairJInv ⊤ (Y ω)) = Y ω := by
  have hRange : MeasurableSet (Set.range (pairJ ⊤)) :=
    measurableSet_range_pairJ ⊤
  have hSource : Measurable (fun ω => pairJ ⊤ (g ω)) :=
    (measurable_pairJ ⊤).comp hg
  have hSourceRange :
      ∀ᵐ x ∂P₀.map (fun ω => pairJ ⊤ (g ω)),
        x ∈ Set.range (pairJ ⊤) :=
    (ae_map_iff hSource.aemeasurable hRange).2
      (Filter.Eventually.of_forall fun ω => ⟨g ω, rfl⟩)
  have hTargetRange : ∀ᵐ ω ∂P, Y ω ∈ Set.range (pairJ ⊤) :=
    (ae_map_iff hY.aemeasurable hRange).1 (hLaw ▸ hSourceRange)
  filter_upwards [hTargetRange] with ω ⟨g', hg'⟩
  rw [← hg', pairJInv_pairJ]

 

theorem ae_pairJ_tendsto_of_joint_coord_coupling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω → (CoordJ → ℝ) × RatCoords)
    (hY : ∀ n, Measurable (Y n)) (hYlim : Measurable Ylim)
    (hLaw : ∀ n, P.map (fun ω => (Y n ω).1) =
      normGFFLaw.map (pairJ ⊤))
    (hLimLaw : P.map (fun ω => (Ylim ω).1) =
      normGFFLaw.map (pairJ ⊤))
    (hConv : ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => pairJ ⊤ (pairJInv ⊤ (Y n ω).1)) atTop
        (𝓝 (pairJ ⊤ (pairJInv ⊤ (Ylim ω).1))) := by
  have hFinite : ∀ n,
      ∀ᵐ ω ∂P, pairJ ⊤ (pairJInv ⊤ (Y n ω).1) = (Y n ω).1 := by
    intro n
    exact ae_pairJ_pairJInv_eq_of_law P normGFFLaw
      (fun ω => (Y n ω).1) (measurable_fst.comp (hY n))
      id measurable_id (hLaw n)
  have hAll : ∀ᵐ ω ∂P, ∀ n,
      pairJ ⊤ (pairJInv ⊤ (Y n ω).1) = (Y n ω).1 :=
    ae_all_iff.mpr hFinite
  have hLim : ∀ᵐ ω ∂P,
      pairJ ⊤ (pairJInv ⊤ (Ylim ω).1) = (Ylim ω).1 :=
    ae_pairJ_pairJInv_eq_of_law P normGFFLaw
      (fun ω => (Ylim ω).1) (measurable_fst.comp hYlim)
      id measurable_id hLimLaw
  filter_upwards [hAll, hLim] with ω hω hωlim
  simp_rw [hω]
  rw [hωlim]
  exact (continuous_fst.tendsto (Ylim ω)).comp (hConv ω)

end SupercriticalLQGUniqueness.B2.DG20Lim
