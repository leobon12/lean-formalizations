import HigherDimLQGMetric.Thm13.LocalWeyl
import HigherDimLQGMetric.Thm13.GoodWeyl
import HigherDimLQGMetric.Thm13.Decomp

/-! Axiom II from the simultaneous L6c event and the local internal formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l8_ae_normalized_local_good
    (h36 : L8Lemma36TruncInput)
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (hN : L8NormalizedGood hd hκ ξ εs hεs)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∃ hD :
      (l8_patch hd hκ ξ εs hεs (h ω)).IsLength,
      (∀ f : C(Rd d, ℝ),
        l8_patch hd hκ ξ εs hεs (addFun (h ω) f) =
          weylMetric ξ f (l8_patch hd hκ ξ εs hεs (h ω)) hD) ∧
      (∀ f' : C(Rd d, ℝ),
        (∃ M : ℝ, ∀ x, |f' x| ≤ M) →
        Tendsto (fun n =>
          (l8_truncScaledMetric hd hκ ξ (hεs n)
            (addFun (h ω) f')).1)
          atTop (𝓝 (weylMetric ξ f'
            (l8_patch hd hκ ξ εs hεs (h ω)) hD).1)) := by
  let Dh : Ω → ContMetric d := fun ω =>
    l8_patch hd hκ ξ εs hεs (h ω)
  obtain ⟨hgood, hae, hweyl⟩ := hN P h hh
  have hlim : ∀ᵐ ω ∂P, (Dh ω).IsLength ∧ IsProperFn (Dh ω).1 ∧
      ∀ R : ℝ, 0 < R → TendstoUniformlyOn
        (fun n => ⇑(lfppSeq κ ξ εs (h ω) n))
        ⇑(Dh ω).1 atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
    filter_upwards [hgood, hae] with ω hω ht
    refine ⟨hω.1, hω.2, fun R _ => ?_⟩
    exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht) _
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hevent := h36 hd κ hκ ξ l2c_trunc εs hεs hεt P h Dh hh hlim
  filter_upwards [hweyl, hevent] with ω ⟨hD, hw⟩ he
  exact ⟨hD, hw,
    l8_bounded_limits_of_lemma36_event hd hκ ξ εs hεs
      (h ω) (Dh ω) hD he⟩

theorem l8_locality_of_normalized_good
    (h36 : L8Lemma36TruncInput)
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (hN : L8NormalizedGood hd hκ ξ εs hεs)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsLGFPlusCont h P) (U : TopologicalSpace.Opens (Rd d)) :
    ∃ F : DistOn U → (Rd d → Rd d → ℝ≥0∞), Measurable F ∧
      ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
        (l8_patch hd hκ ξ εs hεs (h ω)).internal U z w =
          F (restrictTo U (h ω)) z w := by
  obtain ⟨F, hFm, hFeq⟩ :=
    l8_exists_localFormula_factor hd hκ ξ εs hεs hεt U
  obtain ⟨h₀, g, hh₀, _, hdec⟩ := l8_lgfPlusCont_decomp hd P h hh
  have hlocal := l8_ae_normalized_local_good h36 hd κ hκ ξ
    εs hεs hεt hN P h₀ hh₀
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hlocal] with ω ⟨hD, hw, hB⟩
  intro z _ w _
  calc
    (l8_patch hd hκ ξ εs hεs (h ω)).internal U z w =
        (weylMetric ξ (g ω)
          (l8_patch hd hκ ξ εs hεs (h₀ ω)) hD).internal U z w := by
      rw [hdec ω, hw (g ω)]
    _ = l8_localFormula hd hκ ξ εs hεs U
          (addFun (h₀ ω) (g ω)) z w :=
      (l8_localFormula_eq_weyl_internal_of_bounded_limits
        hd hκ ξ εs hεs hεt (h₀ ω)
        (l8_patch hd hκ ξ εs hεs (h₀ ω)) hD hB
        (g ω) U z w).symm
    _ = F (restrictTo U (h ω)) z w := by
      rw [← hdec ω, hFeq (h ω)]

end HigherDimLQGMetric
