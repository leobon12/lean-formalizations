import QuantumZipper.Proofs.Thm18.G1ProfileInt
import QuantumZipper.Proofs.Thm18.G1RegLogDeriv
import QuantumZipper.Proofs.GFF.CoordRegPush
import QuantumZipper.Proofs.Complex.KoebeCovering

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PROFILE-CONV (1): deterministic estimates for the profile part along `ψ_* fc(d, r)`

For `ψ` injective and holomorphic on `ℍ` with `ψ(ℍ) ⊆ ℍ` and bounded on bounded sets (the
inverse of a normalized uniformizer of a side component), this file proves:

* `abs_log_norm_le_of_injOn`: `|log ‖ψ z‖| ≤ K + (1 + C₂) |log Im z|` on bounded parts of `ℍ`.
  Lower bound: Koebe's covering estimate on the disc `B(z, Im z) ⊆ ℍ`
  (`CA.Koebe.koebeCovConst_mul_le_infDist`; Garnett–Marshall, *Harmonic Measure*, Ch. I,
  Thm 4.3, p. 21, non-sharp constant) gives `c · Im z · ‖ψ'(z)‖ ≤ dist(ψ z, ∂ψ(B)) ≤ ‖ψ z‖`
  because `0 ∉ ψ(B) ⊆ ℍ`; then the Bloch bound for `log ‖ψ'‖` (`G1.abs_log_norm_deriv_le_of_injOn`,
  Koebe distortion, Garnett–Marshall Thm I.4.5). No boundary (Beurling/Hölder) regularity is
  needed: the singularity of `log ‖ψ‖` at the boundary point `0` is controlled by `log Im`, which
  is integrable on every folded circle (`TwoPoint.integrable_log_im_foldedCircle`).
* `tendsto_smoothFun_rp_nhdsGT`, `abs_smoothFun_rp_le`: vanishing circle smoothing of a radial
  profile `rp g` with a logarithmic bound, pointwise away from `0` and with a uniform
  logarithmic majorant (from `F1.RC3Two.abs_smoothFun_rp_sub_le`).
* `tendsto_profile_psi`: dominated convergence along `ψ_* fc(d, r)`.

Own elementary assembly (AGENT_GUIDE cost rule) of the cited Koebe estimates and dominated
convergence.
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open F1.RC3Two CA.Koebe

theorem ne_zero_of_mem_H' {z : ℂ} (hz : z ∈ H) : z ≠ 0 := fun h => by
  have : 0 < z.im := hz
  rw [h] at this
  simp at this

/-- The disc `B(z, Im z)` lies in `ℍ`. -/
theorem ball_im_subset_H' (z : ℂ) : ball z z.im ⊆ H := by
  intro u hu
  rw [mem_ball, dist_eq_norm] at hu
  have h1 := Complex.abs_im_le_norm (u - z)
  rw [Complex.sub_im] at h1
  show 0 < u.im
  have := neg_abs_le (u.im - z.im)
  linarith

/-- **Logarithmic bound for `log ‖ψ‖`** on bounded parts of `ℍ` (Koebe covering + distortion). -/
theorem abs_log_norm_le_of_injOn {ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ ψ H) (hinj : InjOn ψ H)
    (hmaps : MapsTo ψ H H) {R M : ℝ} (hR : 0 < R) (hM : ∀ z ∈ H, ‖z‖ ≤ R → ‖ψ z‖ ≤ M) :
    ∃ K : ℝ, ∀ z ∈ H, ‖z‖ ≤ R →
      |Real.log ‖ψ z‖| ≤ K + (1 + koebeDistExp) * |Real.log z.im| := by
  obtain ⟨K₁, hK₁⟩ := G1.abs_log_norm_deriv_le_of_injOn hd hinj hR
  refine ⟨|Real.log M| + |K₁| + |Real.log koebeCovConst|, fun z hz hzR => ?_⟩
  have hzim : 0 < z.im := hz
  have hB := ball_im_subset_H' z
  have hcov := koebeCovConst_mul_le_infDist hzim (hd.mono hB) (hinj.mono hB)
  have h0 : (0 : ℂ) ∈ (ψ '' ball z z.im)ᶜ := by
    rintro ⟨u, hu, hu0⟩
    exact ne_zero_of_mem_H' (hmaps (hB hu)) hu0
  have hle : infDist (ψ z) (ψ '' ball z z.im)ᶜ ≤ ‖ψ z‖ := by
    have := infDist_le_dist_of_mem h0 (x := ψ z)
    rwa [dist_zero_right] at this
  have hψ0 : 0 < ‖ψ z‖ := norm_pos_iff.2 (ne_zero_of_mem_H' (hmaps hz))
  have hd0 : 0 < ‖deriv ψ z‖ := norm_pos_iff.2 (deriv_ne_zero_of_injOn isOpen_H hd hinj hz)
  have hκ := koebeCovConst_pos
  have hlow : koebeCovConst * z.im * ‖deriv ψ z‖ ≤ ‖ψ z‖ := hcov.trans hle
  have hlog1 := Real.log_le_log (by positivity) hlow
  rw [Real.log_mul (by positivity) hd0.ne', Real.log_mul hκ.ne' hzim.ne'] at hlog1
  have hup := Real.log_le_log hψ0 (hM z hz hzR)
  have e1 := abs_le.1 (hK₁ z hz hzR)
  have hC := koebeDistExp_pos
  have a1 := le_abs_self (Real.log M)
  have a2 := le_abs_self K₁
  have a0 := abs_nonneg (Real.log M)
  have a9 : (1 + koebeDistExp) * |Real.log z.im| = |Real.log z.im| + koebeDistExp * |Real.log z.im| :=
    by ring
  have a3 := neg_abs_le (Real.log koebeCovConst)
  have a4 := neg_abs_le (Real.log z.im)
  have a5 := abs_nonneg K₁
  have a6 := abs_nonneg (Real.log koebeCovConst)
  have a7 := abs_nonneg (Real.log z.im)
  have a8 := mul_nonneg hC.le a7
  rw [abs_le]
  constructor <;> linarith

/-- A radial profile with a logarithmic bound near `0` is logarithmically bounded on `(0, T]`. -/
theorem abs_le_log_of_bd {g : ℝ → ℝ} {C : ℝ} (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) (T : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ t, 0 < t → t ≤ T → |g t| ≤ B + C * |Real.log t| := by
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hgc.mono fun t (ht : t ∈ Icc (1 : ℝ) T) => (show t ∈ Ioi (0 : ℝ) from
      lt_of_lt_of_le one_pos ht.1))
  have hC := nonneg_of_bd hbd
  refine ⟨|B₀| + C, by positivity, fun t ht htT => ?_⟩
  rcases le_total t 1 with h1 | h1
  · have h2 := hbd t ht h1
    have hl : Real.log t ≤ 0 := Real.log_nonpos ht.le h1
    rw [abs_of_nonpos hl]
    have := abs_nonneg B₀
    nlinarith
  · have h2 := hB₀ t ⟨h1, htT⟩
    rw [Real.norm_eq_abs] at h2
    have := le_abs_self B₀
    have := mul_nonneg hC (abs_nonneg (Real.log t))
    linarith

/-- A folded circle about a point of `Hbar` stays within its radius. -/
theorem foldedCircle_ae_dist_le' {c : ℂ} (hc : c ∈ Hbar) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ᵐ u ∂foldedCircle c ρ, dist u c ≤ ρ := by
  unfold foldedCircle
  refine (ae_map_iff (p := fun u => dist u c ≤ ρ) measurable_foldH.aemeasurable
    (measurableSet_closedBall (x := c) (ε := ρ))).2 ?_
  filter_upwards [CoordReg.ae_mem_closedBall_circleUnif c hρ] with z hz
  have hfc : foldH c = c := by
    have : 0 ≤ c.im := hc
    simp [foldH, this]
  have h := TwoPoint.norm_foldH_sub_le z c
  rw [hfc] at h
  rw [mem_closedBall, dist_eq_norm] at hz
  rw [dist_eq_norm]
  linarith

variable {g : ℝ → ℝ} {C : ℝ}

/-- **Vanishing circle smoothing away from `0`.** -/
theorem tendsto_smoothFun_rp_nhdsGT (hgm : Measurable g) (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) {c : ℂ} (hc : c ∈ Hbar)
    (hc0 : c ≠ 0) :
    Tendsto (fun ρ => GoodSample.smoothFun (rp g) c ρ) (𝓝[>] 0) (𝓝 (rp g c)) := by
  have hcont : ContinuousAt (rp g) c :=
    (hgc.continuousAt (Ioi_mem_nhds (norm_pos_iff.2 hc0))).comp continuous_norm.continuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
  have hI := (abs_smoothFun_rp_sub_le hgm hgc hbd (s := 1 / 2) (by norm_num) (by norm_num) c
    hρ.1).1
  rw [Real.dist_eq]
  have e : GoodSample.smoothFun (rp g) c ρ - rp g c =
      ∫ u, (rp g u - rp g c) ∂foldedCircle c ρ := by
    rw [integral_sub hI (integrable_const _)]
    simp [GoodSample.smoothFun]
  rw [e, ← Real.norm_eq_abs]
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le_const (C := ε / 2) ?_) ?_
  · filter_upwards [foldedCircle_ae_dist_le' hc hρ.1.le] with u hu
    rw [← dist_eq_norm]
    exact (hδε (lt_of_le_of_lt hu hρ.2)).le
  · simp only [probReal_univ, mul_one]
    linarith

/-- **Uniform logarithmic majorant** of the smoothed profile. -/
theorem abs_smoothFun_rp_le (hgm : Measurable g) (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) (R₀ : ℝ) :
    ∃ B : ℝ, ∀ c : ℂ, ‖c‖ ≤ R₀ → c ≠ 0 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      |GoodSample.smoothFun (rp g) c ρ| ≤ B + 8 * C * |Real.log ‖c‖| := by
  have hC := nonneg_of_bd hbd
  set R := |R₀| + 1 with hRdef
  have hR1 : 1 ≤ R := by have := abs_nonneg R₀; linarith
  have hT := continuous_rpT hgc (δ := (1 / 2 : ℝ) ^ 2) (by positivity)
  obtain ⟨B₁, hB₁⟩ :=
    (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hT.continuousOn
  refine ⟨|B₁| + 8 * C * (|Real.log (1 / 2)| + |Real.log R|),
    fun c hc hc0 ρ hρ hρ1 => ?_⟩
  have h := (abs_smoothFun_rp_sub_le hgm hgc hbd (s := 1 / 2) (by norm_num) (by norm_num) c
    hρ).2
  have hsupp : ∀ᵐ u ∂foldedCircle c ρ, ‖u‖ ≤ R := by
    filter_upwards [TwoPoint.foldedCircle_ae_norm_le c hρ.le] with u hu
    linarith [le_abs_self R₀]
  have h1 : |GoodSample.smoothFun (rpT g ((1 / 2) ^ 2)) c ρ| ≤ |B₁| := by
    have := norm_integral_le_of_norm_le_const (μ := foldedCircle c ρ)
      (f := rpT g ((1 / 2) ^ 2)) (C := |B₁|) (by
        filter_upwards [hsupp] with u hu
        exact (hB₁ u (mem_closedBall_zero_iff.2 hu)).trans (le_abs_self _))
    simpa [GoodSample.smoothFun] using this
  have h2 : GoodSample.smoothFun (Ls (1 / 2)) c ρ ≤ |Real.log (1 / 2)| + |Real.log R| := by
    have := norm_integral_le_of_norm_le_const (μ := foldedCircle c ρ)
      (f := Ls (1 / 2)) (C := |Real.log (1 / 2)| + |Real.log R|) (by
        filter_upwards [hsupp] with u hu
        rw [Real.norm_eq_abs]
        have hm0 : (0 : ℝ) < max (1 / 2) ‖u‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
        have hmR : max (1 / 2) ‖u‖ ≤ R := max_le (by linarith) hu
        have l1 := Real.log_le_log hm0 hmR
        have l2 := Real.log_le_log (by norm_num) (le_max_left (1 / 2 : ℝ) ‖u‖)
        have := le_abs_self (Real.log R)
        have := neg_abs_le (Real.log (1 / 2))
        have := abs_nonneg (Real.log R)
        have := abs_nonneg (Real.log (1 / 2))
        unfold Ls
        rw [abs_le]
        constructor <;> linarith)
    simp only [probReal_univ, mul_one] at this
    exact (le_abs_self _).trans (by simpa [GoodSample.smoothFun] using this)
  have h3 : -Real.log (max ρ ‖c‖) ≤ |Real.log ‖c‖| := by
    have := Real.log_le_log (norm_pos_iff.2 hc0) (le_max_right ρ ‖c‖)
    linarith [neg_abs_le (Real.log ‖c‖)]
  have tri := abs_sub_abs_le_abs_sub (GoodSample.smoothFun (rp g) c ρ)
    (GoodSample.smoothFun (rpT g ((1 / 2) ^ 2)) c ρ)
  have h4 := mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by positivity : (0 : ℝ) ≤ 8 * C)
  have e : (1 / 2 : ℝ) ^ 2 = (1 / 2) ^ 2 := rfl
  nlinarith

/-- **Dominated convergence along a pushed measure.** If `f` maps `μ`-a.e. point into a bounded
part of `ℍ` and `log ‖f‖` is `μ`-integrable, the smoothed profile along `f` converges to the
profile along `f`. -/
theorem tendsto_integral_smoothFun_comp (hgm : Measurable g) (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) {μ : Measure ℂ}
    [IsProbabilityMeasure μ] {f : ℂ → ℂ} (hf : Measurable f) (hfH : ∀ᵐ z ∂μ, f z ∈ H)
    {R₀ : ℝ} (hfR : ∀ᵐ z ∂μ, ‖f z‖ ≤ R₀) (hlog : Integrable (fun z => Real.log ‖f z‖) μ)
    {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝[>] 0)) :
    Tendsto (fun k => ∫ z, GoodSample.smoothFun (rp g) (f z) (ρ k) ∂μ) atTop
      (𝓝 (∫ z, rp g (f z) ∂μ)) := by
  obtain ⟨B, hB⟩ := abs_smoothFun_rp_le hgm hgc hbd R₀
  have hρev : ∀ᶠ k in atTop, ρ k ∈ Ioo (0 : ℝ) 1 := hρ (Ioo_mem_nhdsGT one_pos)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => B + 8 * C * |Real.log ‖f z‖|) ?_ ?_ ?_ ?_
  · filter_upwards [hρev] with k hk
    exact ((continuous_smoothFun_rp hgm hgc hbd hk.1).measurable.comp hf).aestronglyMeasurable
  · filter_upwards [hρev] with k hk
    filter_upwards [hfH, hfR] with z hz hzR
    rw [Real.norm_eq_abs]
    exact hB (f z) hzR (ne_zero_of_mem_H' hz) (ρ k) hk.1 hk.2.le
  · exact (integrable_const B).add (hlog.abs.const_mul (8 * C))
  · filter_upwards [hfH] with z hz
    exact (tendsto_smoothFun_rp_nhdsGT hgm hgc hbd (H_subset_Hbar hz)
      (ne_zero_of_mem_H' hz)).comp hρ

end G1RC
end Thm18Asm
end QuantumZipper
