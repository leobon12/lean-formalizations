import QuantumZipper.Proofs.Thm18.G1Side3SC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (7): the two pulled-back fields agree on small interior circles

Let `x = coordChange (rescale w Q s) ψ Q` (the pulled-back canonical field, RC3 at every circle)
and `y = coordChange w (s ψ) Q`. If, at every centre `v` of a closed set `U ⊂ ℍ` and every radius
`ρ < ρ₀`, the free continuum limit on `(sψ)_* fc(v, ρ)` exists, then `x` and `y` have the same raw
values on these circles (`G1Side.raw_rescale_eq`), hence the same dyadic averages at the points of
`U` at distance `> δ` from its complement, hence the same regularized values on circles inside that
region, and `evalReg y (fc(z, r)) = y (fc(z, r))` there (`evalReg_y_eq`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

theorem radius_eventually_lt {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ j in atTop, radius j < δ :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num)).eventually (gt_mem_nhds hδ) |>.mono fun j hj => by
      simpa [radius, one_div, inv_pow] using hj

variable {Q : ℝ} {x0 : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {ψ : ℂ → ℂ} {s : ℝ}

/-- **Equality of the dyadic averages on the inner region.** -/
theorem avgReg_eq_inner (hgood : WedgeTK.GoodRad x0 F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x0 (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (hW : IsRegularSample (wedgeField (lateralPart x0) A Q))
    (hψm : Measurable ψ) (hs : 0 < s) {U : Set ℂ} {ρ₀ δ : ℝ} (hδ : 0 < δ)
    (hU : ∀ v ∈ U, ∀ ρ, 0 < ρ → ρ < ρ₀ →
      ρ < v.im ∧ ContinuousOn ψ (closedBall v ρ) ∧ MapsTo ψ (closedBall v ρ) H ∧
      (∀ᵐ u ∂foldedCircle v ρ, deriv ψ u ≠ 0) ∧
      Integrable (fun u => Real.log ‖deriv ψ u‖) (foldedCircle v ρ) ∧
      ∃ Y : ℝ, Tendsto (fun σ => ∫ u, F (u, σ)
        ∂((foldedCircle v ρ).map fun u => (s : ℂ) * ψ u)) (𝓝[>] 0) (𝓝 Y))
    {u : ℂ} (hu : closedBall u δ ⊆ U) {j : ℕ} (hj : radius j < ρ₀) :
    avgReg (coordChange (rescale (wedgeField (lateralPart x0) A Q) Q s) ψ Q) j u =
      avgReg (coordChange (wedgeField (lateralPart x0) A Q) (fun u => (s : ℂ) * ψ u) Q) j u := by
  unfold avgReg
  refine limUnder_congr_side ?_
  have hn : ∀ᶠ n : ℕ in atTop, dyadicRoundC n u ∈ U := by
    have ht : Tendsto (fun n : ℕ => 2 * (1 / 2 ^ n : ℝ)) atTop (𝓝 (2 * 0)) := by
      refine tendsto_const_nhds.mul ?_
      simp_rw [one_div, ← inv_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    rw [mul_zero] at ht
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with n hn
    refine hu (mem_closedBall.2 ?_)
    rw [dist_eq_norm]
    exact (CircleCont.norm_dyadicRoundC_sub_le n u).trans hn.le
  filter_upwards [hn] with n hnU
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hU _ hnU _ (radius_pos j) hj
  exact raw_rescale_eq hgood hraw hA hW hψm (radius_pos j) h1 h2 h3 h4 h5 hs h6

/-- **The regularized value of `y` on an inner circle is its raw value.** -/
theorem evalReg_y_eq (hgood : WedgeTK.GoodRad x0 F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x0 (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (hW : IsRegularSample (wedgeField (lateralPart x0) A Q))
    (hψm : Measurable ψ) (hs : 0 < s) {U : Set ℂ} {ρ₀ δ : ℝ} (hρ₀ : 0 < ρ₀) (hδ : 0 < δ)
    (hU : ∀ v ∈ U, ∀ ρ, 0 < ρ → ρ < ρ₀ →
      ρ < v.im ∧ ContinuousOn ψ (closedBall v ρ) ∧ MapsTo ψ (closedBall v ρ) H ∧
      (∀ᵐ u ∂foldedCircle v ρ, deriv ψ u ≠ 0) ∧
      Integrable (fun u => Real.log ‖deriv ψ u‖) (foldedCircle v ρ) ∧
      ∃ Y : ℝ, Tendsto (fun σ => ∫ u, F (u, σ)
        ∂((foldedCircle v ρ).map fun u => (s : ℂ) * ψ u)) (𝓝[>] 0) (𝓝 Y))
    (hRC3 : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (coordChange (rescale (wedgeField (lateralPart x0) A Q) Q s) ψ Q)
          (foldedCircle d r) =
        coordChange (rescale (wedgeField (lateralPart x0) A Q) Q s) ψ Q (foldedCircle d r))
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hrρ : r < ρ₀) (hz : closedBall z (r + δ) ⊆ U) :
    evalReg (coordChange (wedgeField (lateralPart x0) A Q) (fun u => (s : ℂ) * ψ u) Q)
        (foldedCircle z r) =
      coordChange (wedgeField (lateralPart x0) A Q) (fun u => (s : ℂ) * ψ u) Q
        (foldedCircle z r) := by
  have hzU : z ∈ U := hz (mem_closedBall_self (by linarith))
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hU z hzU r hr hrρ
  have hzH : z ∈ Hbar := by show (0 : ℝ) ≤ z.im; linarith
  have hraw_eq := raw_rescale_eq hgood hraw hA hW hψm hr h1 h2 h3 h4 h5 hs h6
  rw [← hraw_eq, ← hRC3 z hzH r hr]
  -- the regularized values agree
  unfold evalReg
  refine limUnder_congr_side ?_
  filter_upwards [radius_eventually_lt hρ₀] with j hj
  refine integral_congr_ae ?_
  filter_upwards [ae_fc_mem_closedBall hzH hr.le] with u hu
  refine (avgReg_eq_inner hgood hraw hA hW hψm hs hδ hU (fun v hv => hz ?_) hj).symm
  rw [mem_closedBall] at hu hv ⊢
  linarith [dist_triangle v u z]

end G1Side
end QuantumZipper
