import QuantumZipper.Proofs.Thm18.G3Za2
import QuantumZipper.Proofs.Thm18.LWFarPocketFar
import Mathlib.Analysis.Complex.RemovableSingularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-A, item (a), layer 3: the harmonic remainder of a log-singular profile through `Φ`

For a local conformal map `Φ` at `0` with `Φ 0 = 0` (`PullData`, `LocConf`: reflection
symmetric) and a profile `f = γ(−log ‖·‖) + h` near `0`, with `h` harmonic and
conjugation-invariant there, `f ∘ Φ = γ(−log ‖·‖) + remK γ Φ h` near `0` where

  `remK γ Φ h u = γ(−log ‖dslope Φ 0 u‖) + h (Φ u)`

(`Φ u = u · dslope Φ 0 u`; `dslope Φ 0` is holomorphic and zero-free on the bi-Lipschitz disc),
and `remK γ Φ h ∘ foldH` is harmonic near `0` (`harmonicOnNhd_remK_foldH`): this is the harmonic
part `g` of the D3⁺ model in the Palm case `α = γ`. Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace G3Za

open G3Cv InnerProductSpace

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

/-- `PullData` survives shrinking the bi-Lipschitz radius. -/
theorem PullData.shrink (hD : PullData Φ b r₀ ρ r₁ m M) {ρ' r₁' : ℝ} (hr₁' : 0 ≤ r₁')
    (hr₁ρ' : r₁' < ρ') (hρ' : ρ' ≤ ρ) : PullData Φ b r₀ ρ' r₁' m M := by
  refine ⟨hD.conf, by linarith, lt_of_le_of_lt hρ' hD.hρr, ⟨hD.bl.1, hD.bl.2.1, fun z hz w hw =>
    hD.bl.2.2 z (closedBall_subset_closedBall hρ' hz) w (closedBall_subset_closedBall hρ' hw)⟩,
    hr₁ρ', fun z hz => hD.up z ⟨closedBall_subset_closedBall hρ' hz.1, hz.2⟩⟩

/-- The harmonic remainder of `f ∘ Φ`. -/
def remK (γ : ℝ) (Φ : ℂ → ℂ) (h : ℂ → ℝ) (u : ℂ) : ℝ :=
  γ * -Real.log ‖dslope Φ 0 u‖ + h (Φ u)

theorem norm_dslope_pos (hD : PullData Φ 0 r₀ ρ r₁ m M) (hΦ0 : Φ 0 = 0) {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) ρ) : 0 < ‖dslope Φ 0 u‖ := by
  by_cases hu0 : u = 0
  · subst hu0
    rw [dslope_same]
    exact norm_pos_iff.2 (hD.conf.deriv_ne 0 (by simpa using hD.conf.pos))
  · have h00 : ((0 : ℝ) : ℂ) ∈ closedBall ((0 : ℝ) : ℂ) ρ := mem_closedBall_self hD.hρ.le
    have hb := (hD.bl.2.2 u (by simpa using hu) _ h00).1
    simp only [Complex.ofReal_zero, sub_zero, hΦ0] at hb
    have e := sub_smul_dslope Φ 0 u
    rw [sub_zero, hΦ0, sub_zero, smul_eq_mul] at e
    have hΦu : ‖Φ u‖ = ‖u‖ * ‖dslope Φ 0 u‖ := by rw [← e, norm_mul]
    have hpos : 0 < m * ‖u‖ := mul_pos hD.bl.1 (norm_pos_iff.2 hu0)
    rw [hΦu] at hb
    by_contra hc
    have : ‖dslope Φ 0 u‖ = 0 := le_antisymm (not_lt.1 hc) (norm_nonneg _)
    rw [this, mul_zero] at hb
    linarith

/-- **`f ∘ Φ = γ(−log ‖·‖) + remK` near `0`.** -/
theorem comp_eq_remK (hD : PullData Φ 0 r₀ ρ r₁ m M) (hΦ0 : Φ 0 = 0) {γ ρf : ℝ}
    {f h : ℂ → ℝ} (hf : ∀ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar, f u = γ * -Real.log ‖u‖ + h u)
    (hMρ : M * ρ ≤ ρf) {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) ρ ∩ Hbar) (hu0 : u ≠ 0) :
    f (Φ u) = γ * -Real.log ‖u‖ + remK γ Φ h u := by
  have h00 : ((0 : ℝ) : ℂ) ∈ closedBall ((0 : ℝ) : ℂ) ρ := mem_closedBall_self hD.hρ.le
  have hb := hD.bl.2.2 u (by simpa using hu.1) _ h00
  simp only [Complex.ofReal_zero, sub_zero, hΦ0] at hb
  have hun : ‖u‖ ≤ ρ := by simpa using hu.1
  have hmem : Φ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar := by
    refine ⟨?_, hD.up u (by simpa using hu)⟩
    rw [mem_closedBall, dist_zero_right]
    nlinarith [hD.bl.2.1]
  rw [hf _ hmem, remK]
  have e := sub_smul_dslope Φ 0 u
  rw [sub_zero, hΦ0, sub_zero, smul_eq_mul] at e
  have hd := norm_dslope_pos hD hΦ0 hu.1
  rw [← e, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hu0) hd.ne']
  ring

/-- `remK` is invariant under conjugation near `0`. -/
theorem remK_conj (hD : PullData Φ 0 r₀ ρ r₁ m M) (hΦ0 : Φ 0 = 0) {γ ρf : ℝ} {h : ℂ → ℝ}
    (hhc : ∀ u ∈ ball (0 : ℂ) ρf, h (conj u) = h u) (hMρ : M * ρ < ρf) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) ρ) : remK γ Φ h (conj u) = remK γ Φ h u := by
  have hr : u ∈ ball ((0 : ℝ) : ℂ) r₀ := by
    have := ball_subset_ball hD.hρr.le hu; simpa using this
  have hsym := hD.conf.symm u hr
  have h00 : ((0 : ℝ) : ℂ) ∈ closedBall ((0 : ℝ) : ℂ) ρ := mem_closedBall_self hD.hρ.le
  have hb := hD.bl.2.2 u (by simpa using ball_subset_closedBall hu) _ h00
  simp only [Complex.ofReal_zero, sub_zero, hΦ0] at hb
  have hΦb : Φ u ∈ ball (0 : ℂ) ρf := by
    rw [mem_ball, dist_zero_right]
    have : ‖u‖ < ρ := by simpa using hu
    nlinarith [hD.bl.2.1]
  unfold remK
  rw [hsym, hhc _ hΦb]
  congr 3
  by_cases hu0 : u = 0
  · subst hu0; simp
  · have hc0 : conj u ≠ 0 := by simpa using hu0
    rw [dslope_of_ne _ hc0, dslope_of_ne _ hu0, slope_def_module, slope_def_module, hsym, hΦ0]
    simp only [sub_zero, smul_eq_mul, norm_mul, norm_inv, Complex.norm_conj]

/-- **The remainder is harmonic after folding.** -/
theorem harmonicOnNhd_remK_foldH (hD : PullData Φ 0 r₀ ρ r₁ m M) (hΦ0 : Φ 0 = 0) {γ ρf : ℝ}
    {h : ℂ → ℝ} (hhh : HarmonicOnNhd h (ball (0 : ℂ) ρf))
    (hhc : ∀ u ∈ ball (0 : ℂ) ρf, h (conj u) = h u) (hMρ : M * ρ < ρf) :
    HarmonicOnNhd (fun z => remK γ Φ h (foldH z)) (ball (0 : ℂ) ρ) := by
  intro z hz
  have hsub : ball (0 : ℂ) ρ ⊆ ball ((0 : ℝ) : ℂ) r₀ := by
    have := ball_subset_ball (x := ((0 : ℝ) : ℂ)) hD.hρr.le; simpa using this
  have hdiff : DifferentiableOn ℂ Φ (ball ((0 : ℝ) : ℂ) r₀) := hD.conf.diff
  have hA : ∀ w ∈ ball (0 : ℂ) ρ, AnalyticAt ℂ Φ w := fun w hw =>
    hdiff.analyticAt (isOpen_ball.mem_nhds (hsub hw))
  have hdd : DifferentiableOn ℂ (dslope Φ 0) (ball ((0 : ℝ) : ℂ) r₀) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (by simpa using hD.conf.pos))).2 hdiff
  have hH : ∀ w ∈ ball (0 : ℂ) ρ, HarmonicAt (remK γ Φ h) w := by
    intro w hw
    have hdA : AnalyticAt ℂ (dslope Φ 0) w := hdd.analyticAt (isOpen_ball.mem_nhds (hsub hw))
    have h1 := (hdA.harmonicAt_log_norm
      (norm_pos_iff.1 (norm_dslope_pos hD hΦ0 (ball_subset_closedBall hw)))).const_smul
      (c := -γ)
    have h00 : ((0 : ℝ) : ℂ) ∈ closedBall ((0 : ℝ) : ℂ) ρ := mem_closedBall_self hD.hρ.le
    have hb := hD.bl.2.2 w (by simpa using ball_subset_closedBall hw) _ h00
    simp only [Complex.ofReal_zero, sub_zero, hΦ0] at hb
    have hΦb : Φ w ∈ ball (0 : ℂ) ρf := by
      rw [mem_ball, dist_zero_right]
      have : ‖w‖ < ρ := by simpa using hw
      nlinarith [hD.bl.2.1]
    have h2 := Thm18Asm.LWFar.pocket_harmonicAt_comp (hA w hw) (hhh _ hΦb)
    convert h1.add h2 using 1
    funext v
    simp only [remK, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp]
    ring
  have hev : (fun z => remK γ Φ h (foldH z)) =ᶠ[𝓝 z] remK γ Φ h := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    unfold foldH
    split_ifs
    · rfl
    · exact remK_conj hD hΦ0 hhc hMρ hw
  exact (harmonicAt_congr_nhds hev).2 (hH z hz)

end G3Za
end QuantumZipper
