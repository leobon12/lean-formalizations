import HigherDimLQGMetric.Thm13.LocalCore
import HigherDimLQGMetric.Field.StandardBorel
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! Measurable factorization of the local formula through field restriction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l8_comap_le_fieldSigma_of_local
    {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {β : Type*}
    [mβ : MeasurableSpace β] {Φ : DistRd d → β}
    (hΦ : Measurable Φ) (U : Opens (Rd d))
    (hloc : ∀ g g' : DistRd d,
      restrictTo U g = restrictTo U g' → Φ g = Φ g')
    (Y : Ω → DistRd d) :
    MeasurableSpace.comap (fun ω => Φ (Y ω)) mβ ≤
      fieldSigmaRd Y U := by
  rintro _ ⟨s, hs, rfl⟩
  set R : DistRd d → (CoordJ → ℝ) :=
    fun g => pairJ U (restrictTo U g) with hR
  have hRm : Measurable R :=
    (measurable_pairJ U).comp (measurable_restrictTo U)
  set A := Φ ⁻¹' s
  have hA : MeasurableSet A := hΦ hs
  have h1 : AnalyticSet (R '' A) := hA.analyticSet_image hRm
  have h2 : AnalyticSet (R '' Aᶜ) := hA.compl.analyticSet_image hRm
  have hdisj : Disjoint (R '' A) (R '' Aᶜ) := by
    rw [Set.disjoint_left]
    rintro _ ⟨g, hg, rfl⟩ ⟨g', hg', he⟩
    have he' : restrictTo U g' = restrictTo U g :=
      injective_pairJ U he
    exact hg' (show Φ g' ∈ s by rw [hloc g' g he']; exact hg)
  obtain ⟨u, hAu, hdu, hu⟩ := h1.measurablySeparable h2 hdisj
  refine ⟨pairJ U ⁻¹' u, measurable_pairJ U hu, ?_⟩
  ext ω
  simp only [mem_preimage]
  refine ⟨fun h => ?_, fun h => hAu ⟨Y ω, h, rfl⟩⟩
  by_contra hn
  exact Set.disjoint_left.1 hdu ⟨Y ω, hn, rfl⟩ h

theorem l8_exists_localFormula_factor
    {d : ℕ} {κ : Rd d → ℝ}
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Filter.Tendsto εs Filter.atTop (𝓝 0))
    (U : Opens (Rd d)) :
    ∃ F : DistOn U → (Rd d → Rd d → ℝ≥0∞),
      Measurable F ∧
      ∀ g : DistRd d,
        l8_localFormula hd hκ ξ εs hεs U g = F (restrictTo U g) := by
  have H : ∀ u v : Rd d,
      ∃ k : DistOn U → ℝ≥0∞, Measurable k ∧
        (fun g : DistRd d =>
          l8_localFormula hd hκ ξ εs hεs U g u v) =
          k ∘ restrictTo U := by
    intro u v
    have hc := l8_comap_le_fieldSigma_of_local
      (l8_measurable_localFormula hd hκ ξ εs hεs U u v) U
      (fun g g' heq => congrFun
        (congrFun (l8_localFormula_congr_of_restrictTo
          hd hκ ξ εs hεs hεt U heq) u) v)
      (id : DistRd d → DistRd d)
    exact (measurable_iff_comap_le.mpr hc).exists_eq_measurable_comp
  choose k hk hkeq using H
  refine ⟨fun x u v => k u v x,
    Measurable.of_eval (fun u => Measurable.of_eval (fun v => hk u v)), ?_⟩
  intro g
  funext u v
  exact congrFun (hkeq u v) g

end HigherDimLQGMetric
