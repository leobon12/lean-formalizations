import SupercriticalConformalCovariance.Transport.Locality

/-! Exact scaling of the target domain metric under a constant field shift. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric (DistC)
open SupercriticalLQGUniqueness (LSCMetric)
open SupercriticalConformalCovariance (domainMetric weylScaleOn)

namespace SupercriticalConformalCovariance.Transport

/-- The domain metric scales exactly, including infinite distances, when the continuous correction
is increased by a constant. -/
theorem domainMetric_add_const (ξ : ℝ) (hξ : 0 ≤ ξ) (D : DistC → LSCMetric)
    (V : Opens ℂ) (h₀ : DistC) (f : C(V, ℝ)) (c : ℝ) :
    domainMetric ξ D V h₀ (f + ContinuousMap.const V c) =
      fun p => ENNReal.ofReal (Real.exp (ξ * c)) * domainMetric ξ D V h₀ f p := by
  funext p
  apply le_antisymm
  · exact SupercriticalConformalCovariance.Domain.weylScaleOn_add_le hξ f (ContinuousMap.const V c)
      (fun z => le_rfl) p
  · exact SupercriticalConformalCovariance.Domain.le_weylScaleOn_add hξ f (ContinuousMap.const V c)
      (fun z => le_rfl) p

/-- Both source and target domain metrics acquire the same exact Weyl factor under a samplewise
constant shift of their continuous corrections. No finiteness of the distances is needed. -/
theorem simultaneous_domain_shift (ξ : ℝ) (hξ : 0 ≤ ξ)
    (D : DistC → LSCMetric) (U V : Opens ℂ)
    {Ω : Type*} (h₀ k₀ : Ω → DistC) (f : Ω → C(U, ℝ))
    (g : Ω → C(V, ℝ)) (c : Ω → ℝ) (ω : Ω) :
    (domainMetric ξ D U (h₀ ω) (f ω + ContinuousMap.const U (c ω)) =
        fun p => ENNReal.ofReal (Real.exp (ξ * c ω)) * domainMetric ξ D U (h₀ ω) (f ω) p) ∧
    (domainMetric ξ D V (k₀ ω) (g ω + ContinuousMap.const V (c ω)) =
        fun p => ENNReal.ofReal (Real.exp (ξ * c ω)) * domainMetric ξ D V (k₀ ω) (g ω) p) :=
  ⟨domainMetric_add_const ξ hξ D U (h₀ ω) (f ω) (c ω),
    domainMetric_add_const ξ hξ D V (k₀ ω) (g ω) (c ω)⟩

theorem resC_add_const {U V : Set ℂ} (hUV : U ⊆ V)
    (f : C(V, ℝ)) (c : ℝ) :
    SupercriticalConformalCovariance.Domain.resC hUV (f + ContinuousMap.const V c) =
      SupercriticalConformalCovariance.Domain.resC hUV f + ContinuousMap.const U c := by
  ext z
  rfl

end SupercriticalConformalCovariance.Transport
