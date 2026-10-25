import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLiminfLocalized
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLocalizedMeasurable

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS.L217

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

def lowerLocalizedNeighborhoodObservable
    (ξ : Set.Ioi (0 : ℝ)) (ε a : ℕ → Set.Ioi (0 : ℝ))
    {V : Set ℂ} (x y : V) (g : DistC) : ℝ≥0∞ :=
  lowerNeighborhoodObservable
    (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (a n)
      (locMollifyC (ε n : ℝ) (ε n).property g)) V x y

 

theorem measurable_lowerLocalizedNeighborhoodObservable
    (ξ : Set.Ioi (0 : ℝ)) (ε a : ℕ → Set.Ioi (0 : ℝ))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (x y : V) :
    Measurable (lowerLocalizedNeighborhoodObservable ξ ε a x y) := by
  unfold lowerLocalizedNeighborhoodObservable lowerNeighborhoodObservable
  apply Measurable.iSup
  intro k
  apply Measurable.liminf
  intro n
  exact measurable_normalizedLocalizedLFPP_neighborhood (ξ : ℝ) (a n)
    (ε n : ℝ) (ε n).property hV hVb x y _

 

theorem lowerLocalizedNeighborhoodObservable_congr
    (ξ : Set.Ioi (0 : ℝ)) (ε a : ℕ → Set.Ioi (0 : ℝ))
    {V : Set ℂ} (hV : IsOpen V) (x y : V)
    (O : TopologicalSpace.Opens ℂ)
    (hVO : ∀ᶠ n in atTop,
      ∀ z ∈ V, Metric.closedBall z (Real.sqrt (ε n : ℝ)) ⊆ O)
    {g g' : DistC} (he : restrictTo O g = restrictTo O g') :
    lowerLocalizedNeighborhoodObservable ξ ε a x y g =
      lowerLocalizedNeighborhoodObservable ξ ε a x y g' := by
  unfold lowerLocalizedNeighborhoodObservable lowerNeighborhoodObservable
  apply iSup_congr
  intro k
  apply liminf_congr
  filter_upwards [hVO] with n hn
  exact normalizedLocalizedLFPP_neighborhood_congr
    ξ (ε n) (a n) hV O hn he x y _

 

theorem comap_lowerLocalizedNeighborhoodObservable_le_fieldSigma
    {Ω : Type} [MeasurableSpace Ω]
    (ξ : Set.Ioi (0 : ℝ)) (ε a : ℕ → Set.Ioi (0 : ℝ))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (O : TopologicalSpace.Opens ℂ)
    (hVO : ∀ᶠ n in atTop,
      ∀ z ∈ V, Metric.closedBall z (Real.sqrt (ε n : ℝ)) ⊆ O)
    (x y : V) (Y : Ω → DistC) :
    MeasurableSpace.comap
      (fun ω => lowerLocalizedNeighborhoodObservable ξ ε a x y (Y ω))
      inferInstance ≤ LQGMetric.Blueprint.fieldSigma Y O := by
  exact comap_le_fieldSigma_of_local
    (measurable_lowerLocalizedNeighborhoodObservable ξ ε a hV hVb x y)
    O (fun g g' he =>
      lowerLocalizedNeighborhoodObservable_congr ξ ε a hV x y O hVO he) Y

 

theorem eventually_closedBall_sqrt_subset_of_compact
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    {V : Set ℂ} (hV : IsCompact (closure V))
    (O : TopologicalSpace.Opens ℂ) (hVO : closure V ⊆ O) :
    ∀ᶠ n in atTop,
      ∀ z ∈ V, Metric.closedBall z (Real.sqrt (ε n : ℝ)) ⊆ O := by
  obtain ⟨δ, hδ, hthick⟩ := hV.exists_cthickening_subset_open O.isOpen hVO
  have hs : Tendsto (fun n => Real.sqrt (ε n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hε
  have hev : ∀ᶠ n in atTop, Real.sqrt (ε n : ℝ) < δ :=
    hs.eventually (eventually_lt_nhds hδ)
  filter_upwards [hev] with n hn z hz
  exact (Metric.closedBall_subset_cthickening (subset_closure hz) _).trans
    ((Metric.cthickening_mono hn.le _).trans hthick)

 
theorem comap_lowerLocalizedNeighborhoodObservable_le_fieldSigma_of_compact
    {Ω : Type} [MeasurableSpace Ω]
    (ξ : Set.Ioi (0 : ℝ)) (ε a : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hVc : IsCompact (closure V))
    (O : TopologicalSpace.Opens ℂ) (hVO : closure V ⊆ O)
    (x y : V) (Y : Ω → DistC) :
    MeasurableSpace.comap
      (fun ω => lowerLocalizedNeighborhoodObservable ξ ε a x y (Y ω))
      inferInstance ≤ LQGMetric.Blueprint.fieldSigma Y O := by
  exact comap_lowerLocalizedNeighborhoodObservable_le_fieldSigma
    ξ ε a hV hVb O
    (eventually_closedBall_sqrt_subset_of_compact ε hε hVc O hVO) x y Y

end SupercriticalLQGUniqueness.B2.PfeAxioms
