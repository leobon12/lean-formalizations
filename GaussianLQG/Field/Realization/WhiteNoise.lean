import GaussianLQG.Field.Realization.Series
import LQGMetric.Field.WhiteNoise

/-!
# The coordinate white noise of a Hilbert basis (blueprint Appendix B, remark after Lemma B.3)

For a Hilbert basis `b` of `L²(ℝ × ℂ)` the coordinate series
`W f (ω) = ∑_k ω_k ⟪f, b_k⟫` converges almost surely for every `f` (Parseval: the coefficients are
square-summable), and `W` is a white noise in the sense of `LQGMetric`
(`isWhiteNoise_wnOf`): finite combinations are centered Gaussians with variance
`‖∑ c_i f_i‖²`. The value is a junk `limUnder` off the convergence set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped RealInnerProductSpace

namespace GaussianLQG
namespace Realization

variable (b : HilbertBasis ℕ ℝ WNSpace)

/-- The coefficients `⟪f, b_k⟫` of `f` in the basis `b`. -/
def coef (f : WNSpace) (k : ℕ) : ℝ := ⟪f, b k⟫

lemma hasSum_coef_mul (f g : WNSpace) :
    HasSum (fun k => coef b f k * coef b g k) ⟪f, g⟫ := by
  have h := b.hasSum_inner_mul_inner f g
  refine h.congr_fun fun k => ?_
  simp only [coef]
  rw [real_inner_comm (b k) g]

lemma hasSum_coef_sq (f : WNSpace) : HasSum (fun k => coef b f k ^ 2) (‖f‖ ^ 2) := by
  have h := hasSum_coef_mul b f f
  rw [real_inner_self_eq_norm_sq] at h
  exact h.congr_fun fun k => sq _

lemma summable_coef_sq (f : WNSpace) : Summable fun k => coef b f k ^ 2 :=
  (hasSum_coef_sq b f).summable

lemma tsum_coef_sq (f : WNSpace) : ∑' k, coef b f k ^ 2 = ‖f‖ ^ 2 :=
  (hasSum_coef_sq b f).tsum_eq

lemma coef_sub (f g : WNSpace) (k : ℕ) : coef b (f - g) k = coef b f k - coef b g k := by
  simp only [coef, inner_sub_left]

lemma coef_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → WNSpace) (k : ℕ) :
    coef b (∑ i ∈ s, c i • f i) k = ∑ i ∈ s, c i * coef b (f i) k := by
  simp only [coef, sum_inner, inner_smul_left, conj_trivial]

/-- The coordinate white noise `W f (ω) = ∑_k ω_k ⟪f, b_k⟫`. -/
def wnOf (f : WNSpace) (ω : Coord) : ℝ := seriesLim (coef b f) ω

lemma measurable_wnOf (f : WNSpace) : Measurable (wnOf b f) := measurable_seriesLim _

theorem ae_tendsto_wnOf (f : WNSpace) :
    ∀ᵐ ω ∂stdP, Tendsto (fun n => psum (coef b f) n ω) atTop (𝓝 (wnOf b f ω)) :=
  ae_tendsto_seriesLim (summable_coef_sq b f)

lemma psum_coef_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → WNSpace) (n : ℕ)
    (ω : Coord) :
    psum (coef b (∑ i ∈ s, c i • f i)) n ω = ∑ i ∈ s, c i * psum (coef b (f i)) n ω := by
  unfold psum
  simp_rw [coef_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- **The coordinate white noise is a white noise.** -/
theorem isWhiteNoise_wnOf : LQGMetric.WhiteNoise.IsWhiteNoise stdP (wnOf b) where
  measurable := measurable_wnOf b
  hasLaw := by
    intro ι _ f c
    set g : WNSpace := ∑ i, c i • f i with hg
    have hL := hasLaw_seriesLim (summable_coef_sq b g)
    rw [tsum_coef_sq] at hL
    refine hL.congr ?_
    have hall : ∀ᵐ ω ∂stdP, ∀ i, Tendsto (fun n => psum (coef b (f i)) n ω) atTop
        (𝓝 (wnOf b (f i) ω)) := ae_all_iff.mpr fun i => ae_tendsto_wnOf b (f i)
    filter_upwards [hall, ae_tendsto_wnOf b g] with ω hω hg'
    have h1 : Tendsto (fun n => psum (coef b g) n ω) atTop
        (𝓝 (∑ i, c i * wnOf b (f i) ω)) := by
      simp_rw [hg, psum_coef_sum]
      exact tendsto_finsetSum _ fun i _ => (hω i).const_mul (c i)
    exact (tendsto_nhds_unique hg' h1).symm

end Realization
end GaussianLQG
