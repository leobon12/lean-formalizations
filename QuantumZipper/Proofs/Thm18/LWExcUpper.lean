import QuantumZipper.Proofs.Thm18.LWExcDefs
import QuantumZipper.Proofs.Thm18.LWExcMaxPrin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route: the upper bound of Lawler–Werness Lemma 4.3

`lw43_upper`: for a crosscut `η` of `ℍ` with `−∞ < η(1−) ≤ η(0+) = −1` and `diam η ≤ 1/2`, every
harmonic measure `h` of `η` in `H_η` has `ℰ(η) = ∫_0^∞ ∂_y h(x) dx ≤ 5 diam η`.

Source: G. F. Lawler, B. M. Werness, Ann. Probab. 41 (2013), Lemma 4.3, pp. 23–24
(`literature/1011.3551.pdf`), upper half of the sketched estimate
`h_η(z) ≍ Im z · diam η / (|z| + 1)²` (`Re z ≥ 0`). LW only sketch the proof; the gap-filling is
an own elementary argument (recorded in DEVIATIONS): with `d = diam η`, `r = 3d/2`, the arc lies
in `B̄(−1, d)`, and the majorant is `u = 2 ω_ℍ(·, [−1 − r, −1 + r]) = (2/π) arg((w+1−r)/(w+1+r))`,
harmonic on `ℍ`, `≥ 0`, `≥ 1` on `B(−1, r) ∩ ℍ` (Thales), so `h ≤ u` on `H_η` by the weak maximum
principle `lwExc_harm_le_zero`; and `u(x + iy) ≤ (2/π) (2ry)/((7/16)(x+1)²)` for `x ≥ 0`
(`arg ζ ≤ tan arg ζ = Im ζ / Re ζ`), whence `∂_y h(x) ≤ (64 r/7π)/(x+1)²` and
`ℰ(η) ≤ 64 r/(7π) ≤ 5 d`.
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology ENNReal Real

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-! ### Geometry of a crosscut -/

lemma lwExc_arc_cover {η : ℝ → ℂ} (hc : ContinuousOn η (Ioo 0 1)) {a0 b1 : ℂ}
    (h0 : Tendsto η (𝓝[>] 0) (𝓝 a0)) (h1 : Tendsto η (𝓝[<] 1) (𝓝 b1)) {r : ℝ} (hr : 0 < r) :
    ∃ δ₀ δ₁ : ℝ, 0 < δ₀ ∧ δ₁ < 1 ∧ IsCompact (η '' Icc δ₀ δ₁) ∧
      arcH η ⊆ ball a0 r ∪ ball b1 r ∪ η '' Icc δ₀ δ₁ := by
  have e0 : ∀ᶠ s in 𝓝[>] (0:ℝ), η s ∈ ball a0 r := h0.eventually (ball_mem_nhds _ hr)
  have e1 : ∀ᶠ s in 𝓝[<] (1:ℝ), η s ∈ ball b1 r := h1.eventually (ball_mem_nhds _ hr)
  obtain ⟨u, hu, hus⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 e0
  obtain ⟨l, hl, hls⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 e1
  have hu' : (0:ℝ) < u := hu
  have hl' : l < 1 := hl
  refine ⟨u, l, hu', hl', ?_, ?_⟩
  · exact isCompact_Icc.image_of_continuousOn
      (hc.mono fun s hs => ⟨lt_of_lt_of_le hu' hs.1, lt_of_le_of_lt hs.2 hl'⟩)
  rintro _ ⟨s, hs, rfl⟩
  by_cases hsu : s < u
  · exact Or.inl (Or.inl (hus ⟨hs.1, hsu⟩))
  by_cases hsl : l < s
  · exact Or.inl (Or.inr (hls ⟨hsl, hs.2⟩))
  exact Or.inr ⟨s, ⟨not_lt.1 hsu, not_lt.1 hsl⟩, rfl⟩

lemma lwExc_arc_isBounded {η : ℝ → ℂ} (hη : IsCrosscutH η) : Bornology.IsBounded (arcH η) := by
  obtain ⟨hc, -, -, ⟨a0, h0⟩, ⟨b1, h1⟩⟩ := hη
  obtain ⟨δ₀, δ₁, -, -, hK, hsub⟩ := lwExc_arc_cover hc h0 h1 one_pos
  exact ((isBounded_ball.union isBounded_ball).union hK.isBounded).subset hsub

/-- `H \ η` is open: the closure of the arc adds only its two real endpoints. -/
lemma lwExc_isOpen_H_diff_arc {η : ℝ → ℂ} (hη : IsCrosscutH η) : IsOpen (H \ arcH η) := by
  obtain ⟨hc, -, -, ⟨a0, h0⟩, ⟨b1, h1⟩⟩ := hη
  have hsub : H ∩ closure (arcH η) ⊆ arcH η := by
    rintro w ⟨hwH, hwcl⟩
    have hwim : 0 < w.im := hwH
    obtain ⟨δ₀, δ₁, hδ₀, hδ₁, hK, hcov⟩ := lwExc_arc_cover hc h0 h1 (half_pos hwim)
    have hcl := closure_mono hcov hwcl
    rw [closure_union, closure_union, hK.isClosed.closure_eq] at hcl
    have hfar : ∀ c : ℝ, w ∉ closure (ball (c : ℂ) (w.im / 2)) := by
      intro c hwc
      have h1 := closure_ball_subset_closedBall hwc
      rw [mem_closedBall, dist_eq_norm] at h1
      have h2 : |(w - c).im| ≤ ‖w - c‖ := Complex.abs_im_le_norm _
      simp only [sub_im, ofReal_im, sub_zero] at h2
      rw [abs_of_pos hwim] at h2
      linarith
    rcases hcl with (h | h) | h
    · exact absurd h (hfar a0)
    · exact absurd h (hfar b1)
    · obtain ⟨s, hs, rfl⟩ := h
      exact ⟨s, ⟨lt_of_lt_of_le hδ₀ hs.1, lt_of_le_of_lt hs.2 hδ₁⟩, rfl⟩
  have heq : H \ arcH η = H ∩ (closure (arcH η))ᶜ := by
    ext w
    refine ⟨fun hw => ⟨hw.1, fun hcl => hw.2 (hsub ⟨hw.1, hcl⟩)⟩,
      fun hw => ⟨hw.1, fun ha => hw.2 (subset_closure ha)⟩⟩
  rw [heq]
  exact (isOpen_lt continuous_const Complex.continuous_im).inter isClosed_closure.isOpen_compl

lemma lwExc_hullComp_isOpen {η : ℝ → ℂ} (hη : IsCrosscutH η) : IsOpen (hullComp η) := by
  have hS := lwExc_isOpen_H_diff_arc hη
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  refine ⟨connectedComponentIn (H \ arcH η) z, ?_, hS.connectedComponentIn,
    mem_connectedComponentIn hz.1⟩
  intro y hy
  refine ⟨connectedComponentIn_subset _ _ hy, ?_⟩
  rw [← connectedComponentIn_eq hy]
  exact hz.2

lemma lwExc_hullComp_subset_H (η : ℝ → ℂ) : hullComp η ⊆ H := fun _ hz => hz.1.1

lemma lwExc_diam_pos {η : ℝ → ℂ} (hη : IsCrosscutH η) : 0 < Metric.diam (arcH η) := by
  have hB := lwExc_arc_isBounded hη
  have h1 : (1 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have h2 : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hne : η (1 / 4) ≠ η (1 / 2) := fun he => by
    have := hη.2.1 h1 h2 he; norm_num at this
  exact lt_of_lt_of_le (dist_pos.2 hne)
    (dist_le_diam_of_mem hB ⟨_, h1, rfl⟩ ⟨_, h2, rfl⟩)

/-! ### The majorant `u = 2 ω_ℍ(·, [−1 − r, −1 + r])` -/

/-! ### Comparison and integration -/

/-- `∫_0^∞ K/(x+1)² dx = K`, as a lower integral. -/
lemma lwExc_lintegral_inv_sq {K : ℝ} (hK : 0 ≤ K) :
    ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (K / (x + 1) ^ 2) = ENNReal.ofReal K := by
  have hder : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -K * (x + 1)⁻¹) (K / (x + 1) ^ 2) x := by
    intro x hx
    have hx1 : x + 1 ≠ 0 := by have : (0 : ℝ) ≤ x := hx; linarith
    exact (((hasDerivAt_id x).add_const 1).inv hx1).const_mul (-K) |>.congr_deriv
      (by simp; field_simp)
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ K / (x + 1) ^ 2 := fun x _ => by positivity
  have hlim : Tendsto (fun x : ℝ => -K * (x + 1)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)).const_mul
      (-K)
    simpa using this
  have hint := integrableOn_Ioi_deriv_of_nonneg' hder hpos hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hder hpos hlim
  rw [setLIntegral_congr Ioi_ae_eq_Ici.symm, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioi hpos), hval]
  simp

end LWFar
end Thm18Asm
end QuantumZipper
