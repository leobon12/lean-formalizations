import HigherDimLQGContinuity.Norm.Pin
import HigherDimLQGMetric.Sphere.Avg
import HigherDimLQGMetric.Sphere.Var

/-!
# Sphere averages under the pinned laws (packet P2; companion of `a:lem-pinlaw`, `a:lem-pin`)

The scale factor `scaleS d ξ s r z g = r^{ϕ(ξ)} e^{ξ g_{sr}(z)}` of `rho_scaling` contains the sphere average `g_ρ(z)` of
the pinned field. Under `pinLaw d s₀` this is a centred Gaussian (`g_ρ(z) = h_ρ(z) - h_{s₀}(0)` for `h ∼ normLGFLaw d`):

* `hasGaussianLaw_sphereAvg_pinLaw`: Gaussian law and mean zero;
* `exists_variance_sphereAvg_pinLaw_le`: the variance bounds of [8]'s `exists_variance_sphereAvg_sub_le`, with one
  constant `K_d` uniform in `(s₀, ρ, z)`;
* `integral_exp_mul_sphereAvg_pinLaw`: `E e^{t g_ρ(z)} = e^{t² Var g_ρ(z) / 2}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Under `pinLaw d s₀`, `g_ρ(z) - g_{s₀}(0) = g_ρ(z)` almost surely. -/
theorem ae_sphereAvg_sub_pinLaw (hd : 2 ≤ d) {s₀ : ℝ} (hs₀ : 0 < s₀) (ρ : ℝ) (z : Rd d) :
    (fun g : DistRd d => sphereAvg (id g) ρ z - sphereAvg (id g) s₀ 0) =ᵐ[pinLaw d s₀]
      fun g => sphereAvg g ρ z := by
  filter_upwards [(isWholeSpaceLGF_pinLaw hd hs₀).2] with g hg
  rw [id, hg, sub_zero]

/-- Under `pinLaw d s₀`, `g_ρ(z)` is a centred Gaussian (`s₀, ρ > 0`). -/
theorem hasGaussianLaw_sphereAvg_pinLaw (hd : 2 ≤ d) {s₀ ρ : ℝ} (hs₀ : 0 < s₀) (hρ : 0 < ρ) (z : Rd d) :
    HasGaussianLaw (fun g : DistRd d => sphereAvg g ρ z) (pinLaw d s₀) ∧
      ∫ g, sphereAvg g ρ z ∂(pinLaw d s₀) = 0 := by
  obtain ⟨hG, h0⟩ := (isWholeSpaceLGF_pinLaw hd hs₀).1.hasGaussianLaw_sphereAvg_sub hd hρ hs₀ z 0
  have e := ae_sphereAvg_sub_pinLaw hd hs₀ ρ z
  exact ⟨hG.congr e, (integral_congr_ae e).symm.trans h0⟩

/-- Variance bounds for `g_ρ(z)` under `pinLaw d s₀`, with one constant `K` for all `s₀, ρ > 0` and `z`. -/
theorem exists_variance_sphereAvg_pinLaw_le (hd : 2 ≤ d) :
    ∃ K : ℝ, ∀ {s₀ ρ : ℝ}, 0 < s₀ → 0 < ρ → ∀ z : Rd d,
      (ρ ≤ s₀ → Var[fun g : DistRd d => sphereAvg g ρ z; pinLaw d s₀] ≤
        Real.log (s₀ / ρ) + 2 * max 0 (Real.log (‖z‖ / s₀)) + K) ∧
      (s₀ ≤ ρ → Var[fun g : DistRd d => sphereAvg g ρ z; pinLaw d s₀] ≤
        Real.log (ρ / s₀) + 2 * max 0 (Real.log (‖z‖ / ρ)) + K) := by
  obtain ⟨K, hK⟩ := exists_variance_sphereAvg_sub_le (d := d) hd
  refine ⟨K, fun {s₀ ρ} hs₀ hρ z => ?_⟩
  rw [← variance_congr (ae_sphereAvg_sub_pinLaw hd hs₀ ρ z)]
  have h := hK (isWholeSpaceLGF_pinLaw hd hs₀).1 hρ hs₀ z 0
  rw [sub_zero] at h
  exact h

/-- `E e^{t g_ρ(z)} = e^{t² Var g_ρ(z) / 2}` under `pinLaw d s₀`. -/
theorem integral_exp_mul_sphereAvg_pinLaw (hd : 2 ≤ d) {s₀ ρ : ℝ} (hs₀ : 0 < s₀) (hρ : 0 < ρ) (z : Rd d)
    (t : ℝ) :
    ∫ g, Real.exp (t * sphereAvg g ρ z) ∂(pinLaw d s₀) =
      Real.exp (Var[fun g : DistRd d => sphereAvg g ρ z; pinLaw d s₀] * t ^ 2 / 2) := by
  obtain ⟨hG, h0⟩ := hasGaussianLaw_sphereAvg_pinLaw hd hs₀ hρ z
  have hmap := hG.map_eq_gaussianReal
  rw [h0] at hmap
  have hlaw : HasLaw (fun g : DistRd d => sphereAvg g ρ z)
      (gaussianReal 0 (Var[fun g : DistRd d => sphereAvg g ρ z; pinLaw d s₀]).toNNReal) (pinLaw d s₀) :=
    ⟨hG.aemeasurable, hmap⟩
  have hm := mgf_gaussianReal hlaw t
  rw [mgf, Real.coe_toNNReal _ (variance_nonneg _ _), zero_mul, zero_add] at hm
  exact hm

end HigherDimLQGContinuity
