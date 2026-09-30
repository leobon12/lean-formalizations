import QuantumZipper.Proofs.Zipper.WedgeShiftInt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# WEDGE-RC3ALL2 (1): circle smoothing of radial profiles with a logarithmic singularity

Deterministic input for `F1.WedgeRC3AllStmt` on folded circles through `0`.

Let `g : ℝ → ℝ` be measurable, continuous on `(0, ∞)`, with `|g t| ≤ C (1 − log t)` on `(0, 1]`,
and `p = g ∘ ‖·‖` (`rp g`). Then

* `continuous_smoothFun_rp`: the circle average `c ↦ ∫ p d fc(c, r)` is continuous on all of `ℂ`
  (also at centres `c` with `‖c‖ = r`, where the circle passes through the singularity);
* `tendsto_integral_smoothFun_rp`: for every folded circle `fc(w, ρ)` (also through `0`),
  `∫∫ p d fc(u, 2^{-k}) d fc(w, ρ)(u) → ∫ p d fc(w, ρ)`.

Route (**own elementary argument**, AGENT_GUIDE cost rule; no source was searched for beyond the
repository, the statement being a routine truncation estimate). Truncate `p` at modulus `δ = s²`
(`rpT g δ = g (max ‖·‖ δ)`, continuous on `ℂ`); the error is bounded pointwise by
`8C (log max(s, ‖v‖) − log ‖v‖)` (`abs_rp_sub_rpT_le`). The only external input is the classical
circle mean of the logarithm `∫ log ‖v‖ d fc(c, r) = log max(r, ‖c‖)`
(`CoordReg.integral_log_norm_foldedCircle`, the mean value property of `log |·|`), which makes the
smoothed error bound `smoothFun (Ls s) c r − log max(r, ‖c‖)` continuous in `(c, r)` and gives,
by dominated convergence, that it tends to `0` as `s → 0` (`tendsto_integral_Ls_sub`). An
abstract ε/3 argument (`tendsto_of_approx`) concludes.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace F1
namespace RC3Two

/-! ## 0. An abstract approximation lemma -/

/-- If `a` is approximated by `aj j` up to `K · d j` and `b` by `bj j` up to `K · dj j`, with
`aj j → bj j`, `d j → dj j` and `dj → 0`, then `a → b`. -/
theorem tendsto_of_approx {ι : Type*} {l : Filter ι} {a : ι → ℝ} {b : ℝ}
    (aj : ℕ → ι → ℝ) (bj : ℕ → ℝ) (d : ℕ → ι → ℝ) (dj : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h1 : ∀ j, Tendsto (aj j) l (𝓝 (bj j)))
    (h2 : ∀ j i, |a i - aj j i| ≤ K * d j i)
    (h3 : ∀ j, |b - bj j| ≤ K * dj j)
    (h4 : ∀ j, Tendsto (d j) l (𝓝 (dj j)))
    (h5 : Tendsto dj atTop (𝓝 0)) : Tendsto a l (𝓝 b) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η := ε / (4 * (K + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hKη : K * η * 4 < ε := by
    have e : K * η * 4 = ε * (K / (K + 1)) := by rw [hη]; field_simp
    rw [e]
    exact mul_lt_of_lt_one_right hε ((div_lt_one (by linarith)).2 (by linarith))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h5 η hη0
  have hj := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at hj
  filter_upwards [Metric.tendsto_nhds.1 (h1 N) (ε / 4) (by positivity),
    Metric.tendsto_nhds.1 (h4 N) η hη0] with i hi1 hi2
  rw [Real.dist_eq] at hi1 hi2 ⊢
  have hd : d N i ≤ 2 * η := by
    linarith [(abs_lt.1 hi2).2, le_abs_self (dj N)]
  have hdj : dj N ≤ η := (le_abs_self _).trans hj.le
  have A1 : K * d N i ≤ K * (2 * η) := mul_le_mul_of_nonneg_left hd hK
  have A2 : K * dj N ≤ K * η := mul_le_mul_of_nonneg_left hdj hK
  have t1 := abs_sub_le (a i) (aj N i) b
  have t2 := abs_sub_le (aj N i) (bj N) b
  rw [abs_sub_comm (bj N) b] at t2
  have := h2 N i
  have := h3 N
  nlinarith

/-! ## 1. Radial profiles, truncations and the logarithmic error bound -/

/-- `L_s(z) = log max(s, ‖z‖)`. -/
def Ls (s : ℝ) : ℂ → ℝ := fun z => Real.log (max s ‖z‖)

/-- The radial profile `g ∘ ‖·‖`. -/
def rp (g : ℝ → ℝ) : ℂ → ℝ := fun z => g ‖z‖

/-- The radial profile truncated at modulus `δ`. -/
def rpT (g : ℝ → ℝ) (δ : ℝ) : ℂ → ℝ := fun z => g (max ‖z‖ δ)

/-- The truncation scales `s_j = 2^{-(j+1)}`. -/
def sj (j : ℕ) : ℝ := radius (j + 1)

theorem continuous_Ls {s : ℝ} (hs : 0 < s) : Continuous (Ls s) :=
  CoordReg.continuous_log_max_norm hs

theorem continuous_rpT {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (rpT g δ) :=
  hg.comp_continuous (continuous_norm.max continuous_const) fun _ =>
    lt_of_lt_of_le hδ (le_max_right _ _)

theorem sj_pos (j : ℕ) : 0 < sj j := radius_pos _

theorem sj_le_half (j : ℕ) : sj j ≤ 1 / 2 := by
  unfold sj radius
  rw [pow_succ]
  have : (2 : ℝ)⁻¹ ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem tendsto_sj : Tendsto sj atTop (𝓝 0) :=
  (tendsto_nhds_of_tendsto_nhdsWithin RegClosure.tendsto_radius_nhdsGT).comp
    (tendsto_add_atTop_nat 1)

variable {g : ℝ → ℝ} {C : ℝ}

theorem nonneg_of_bd (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) : 0 ≤ C := by
  have := hbd 1 one_pos le_rfl
  rw [Real.log_one, sub_zero, mul_one] at this
  exact (abs_nonneg _).trans this

/-- **Pointwise error of the truncation.** -/
theorem abs_rp_sub_rpT_le (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t))
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) {v : ℂ} (hv : v ≠ 0) :
    |rp g v - rpT g (s ^ 2) v| ≤ 8 * C * (Ls s v - Real.log ‖v‖) := by
  have hC := nonneg_of_bd hbd
  have ht : 0 < ‖v‖ := norm_pos_iff.2 hv
  unfold rp rpT Ls
  have hLs : Real.log ‖v‖ ≤ Real.log (max s ‖v‖) := Real.log_le_log ht (le_max_right _ _)
  by_cases h : s ^ 2 ≤ ‖v‖
  · rw [max_eq_left h, sub_self, abs_zero]
    exact mul_nonneg (by positivity) (by linarith)
  · push Not at h
    have hss : s ^ 2 ≤ s := by nlinarith
    rw [max_eq_right h.le, max_eq_left (h.le.trans hss)]
    have hs2pos : 0 < s ^ 2 := by positivity
    have hlt : Real.log ‖v‖ < Real.log (s ^ 2) := Real.log_lt_log ht h
    have hq : s ^ 2 ≤ Real.exp (-1) := by
      have := Real.exp_neg_one_gt_d9; nlinarith
    have hle1 : Real.log ‖v‖ ≤ -1 := by
      have := Real.log_le_log hs2pos hq
      rw [Real.log_exp] at this; linarith
    rw [Real.log_pow] at hlt
    have b1 := hbd ‖v‖ ht (by nlinarith)
    have b2 := hbd (s ^ 2) hs2pos (by nlinarith)
    rw [Real.log_pow] at b2
    have tri := abs_sub (g ‖v‖) (g (s ^ 2))
    push_cast at hlt b2
    have key : 0 ≤ C * (8 * (Real.log s - Real.log ‖v‖) -
        ((1 - Real.log ‖v‖) + (1 - 2 * Real.log s))) :=
      mul_nonneg hC (by linarith)
    nlinarith

/-- **Smoothed error of the truncation** (and integrability of the profile on every folded
circle). -/
theorem abs_smoothFun_rp_sub_le (hgm : Measurable g) (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t))
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (rp g) (foldedCircle c r) ∧
      |GoodSample.smoothFun (rp g) c r - GoodSample.smoothFun (rpT g (s ^ 2)) c r| ≤
        8 * C * (GoodSample.smoothFun (Ls s) c r - Real.log (max r ‖c‖)) := by
  have hL : Integrable (Ls s) (foldedCircle c r) :=
    RegClosure.integrable_fc (continuous_Ls hs).continuousOn c hr.le
  have hlog := CoordReg.integrable_log_norm_foldedCircle c r
  have hD : Integrable (fun v => Ls s v - Real.log ‖v‖) (foldedCircle c r) := hL.sub hlog
  have hT : Integrable (rpT g (s ^ 2)) (foldedCircle c r) :=
    RegClosure.integrable_fc (continuous_rpT hgc (by positivity)).continuousOn c hr.le
  have hae : ∀ᵐ v ∂foldedCircle c r,
      ‖rp g v - rpT g (s ^ 2) v‖ ≤ 8 * C * (Ls s v - Real.log ‖v‖) :=
    (ae_ne_zero_fc c hr).mono fun v hv => by
      rw [Real.norm_eq_abs]; exact abs_rp_sub_rpT_le hbd hs hs2 hv
  have hm : AEStronglyMeasurable (rp g) (foldedCircle c r) :=
    (hgm.comp measurable_norm).aestronglyMeasurable
  have hI : Integrable (rp g) (foldedCircle c r) := by
    refine (hT.norm.add (hD.const_mul (8 * C))).mono' hm ?_
    filter_upwards [hae] with v hv
    rw [Real.norm_eq_abs] at hv ⊢
    have := abs_sub_abs_le_abs_sub (rp g v) (rpT g (s ^ 2) v)
    show |rp g v| ≤ ‖rpT g (s ^ 2) v‖ + 8 * C * (Ls s v - Real.log ‖v‖)
    rw [Real.norm_eq_abs]
    linarith
  refine ⟨hI, ?_⟩
  unfold GoodSample.smoothFun
  rw [← integral_sub hI hT]
  have := norm_integral_le_of_norm_le (hD.const_mul (8 * C)) hae
  rw [integral_const_mul, integral_sub hL hlog, CoordReg.integral_log_norm_foldedCircle c hr,
    Real.norm_eq_abs] at this
  exact this

/-- **The smoothed error bound vanishes as `s → 0`** (dominated convergence). -/
theorem tendsto_integral_Ls_sub (c : ℂ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun j : ℕ => ∫ v, (Ls (sj j) v - Real.log ‖v‖) ∂foldedCircle c r) atTop (𝓝 0) := by
  have hlog := CoordReg.integrable_log_norm_foldedCircle c r
  have hL1 : Integrable (Ls 1) (foldedCircle c r) :=
    RegClosure.integrable_fc (continuous_Ls one_pos).continuousOn c hr.le
  have h := tendsto_integral_of_dominated_convergence (μ := foldedCircle c r)
    (F := fun (j : ℕ) (v : ℂ) => Ls (sj j) v - Real.log ‖v‖) (f := fun _ => (0 : ℝ))
    (fun v => Ls 1 v - Real.log ‖v‖)
    (fun j => ((continuous_Ls (sj_pos j)).measurable.sub
      (Real.measurable_log.comp measurable_norm)).aestronglyMeasurable)
    (hL1.sub hlog) (fun j => ?_) ?_
  · simpa using h
  · filter_upwards [ae_ne_zero_fc c hr] with v hv
    have ht : 0 < ‖v‖ := norm_pos_iff.2 hv
    have a1 : Real.log ‖v‖ ≤ Ls (sj j) v := Real.log_le_log ht (le_max_right _ _)
    have a2 : Ls (sj j) v ≤ Ls 1 v :=
      Real.log_le_log (lt_of_lt_of_le (sj_pos j) (le_max_left _ _))
        (max_le_max (by linarith [sj_le_half j]) le_rfl)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  · filter_upwards [ae_ne_zero_fc c hr] with v hv
    have ht : 0 < ‖v‖ := norm_pos_iff.2 hv
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_sj.eventually (ge_mem_nhds ht)] with j hj
    simp only [Ls, max_eq_right hj, sub_self]

/-! ## 2. Continuity of the circle average of the profile -/

/-- **Continuity in the centre** of `∫ p d fc(c, r)`, also across centres with `‖c‖ = r`. -/
theorem continuous_smoothFun_rp (hgm : Measurable g) (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) {r : ℝ} (hr : 0 < r) :
    Continuous fun c => GoodSample.smoothFun (rp g) c r := by
  have hC := nonneg_of_bd hbd
  refine continuous_iff_continuousAt.2 fun c₀ => ?_
  refine tendsto_of_approx (fun j c => GoodSample.smoothFun (rpT g (sj j ^ 2)) c r)
    (fun j => GoodSample.smoothFun (rpT g (sj j ^ 2)) c₀ r)
    (fun j c => GoodSample.smoothFun (Ls (sj j)) c r - Real.log (max r ‖c‖))
    (fun j => GoodSample.smoothFun (Ls (sj j)) c₀ r - Real.log (max r ‖c₀‖))
    (K := 8 * C) (by positivity)
    (fun j => ((GoodSample.continuous_smoothFun
      (continuous_rpT hgc (pow_pos (sj_pos j) 2)).continuousOn r).tendsto c₀))
    (fun j c => (abs_smoothFun_rp_sub_le hgm hgc hbd (sj_pos j) (sj_le_half j) c hr).2)
    (fun j => (abs_smoothFun_rp_sub_le hgm hgc hbd (sj_pos j) (sj_le_half j) c₀ hr).2)
    (fun j => (((GoodSample.continuous_smoothFun (continuous_Ls (sj_pos j)).continuousOn r).sub
      (CoordReg.continuous_log_max_norm hr)).tendsto c₀)) ?_
  refine (tendsto_integral_Ls_sub c₀ hr).congr fun j => ?_
  rw [integral_sub (RegClosure.integrable_fc (continuous_Ls (sj_pos j)).continuousOn c₀ hr.le)
    (CoordReg.integrable_log_norm_foldedCircle c₀ r),
    CoordReg.integral_log_norm_foldedCircle c₀ hr]
  rfl

/-! ## 3. Vanishing circle smoothing on a folded circle -/

/-- Dominated convergence `∫ log max(2^{-k}, ‖u‖) d fc(w, ρ) → ∫ log ‖u‖ d fc(w, ρ)`. -/
theorem tendsto_integral_log_max_fc (w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun k => ∫ u, Real.log (max (radius k) ‖u‖) ∂foldedCircle w ρ) atTop
      (𝓝 (∫ u, Real.log ‖u‖ ∂foldedCircle w ρ)) := by
  have hint := CoordReg.integrable_log_norm_foldedCircle w ρ
  have hne := ae_ne_zero_fc w hρ
  refine tendsto_integral_of_dominated_convergence (fun z => |Real.log ‖z‖|)
    (fun k => (CoordReg.continuous_log_max_norm (radius_pos k)).aestronglyMeasurable) hint.abs
    (fun k => ?_) ?_
  · filter_upwards [hne] with z hz
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hr1 : radius k ≤ 1 := by unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)
    rw [Real.norm_eq_abs]
    rcases le_total (radius k) ‖z‖ with h1 | h1
    · rw [max_eq_right h1]
    · rw [max_eq_left h1]
      have a1 := Real.log_le_log hz0 h1
      have a2 := Real.log_nonpos (radius_pos k).le hr1
      rw [abs_of_nonpos a2, abs_of_nonpos (a1.trans a2)]
      linarith
  · filter_upwards [hne] with z hz
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hev : ∀ᶠ k in atTop, radius k ≤ ‖z‖ :=
      ((RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
        (ge_mem_nhds hz0))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with k hk
    rw [max_eq_right hk]

/-- Vanishing smoothing of a continuous function on a folded circle. -/
theorem tendsto_integral_smoothFun_fc {φ : ℂ → ℝ} (hφ : Continuous φ) (w : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    Tendsto (fun k => ∫ u, GoodSample.smoothFun φ u (radius k) ∂foldedCircle w ρ) atTop
      (𝓝 (GoodSample.smoothFun φ w ρ)) := by
  have h := ((GoodSample.gs_tluo_smooth_continuous hφ.continuousOn).tendsto_at
    (a := (foldH w, ρ)) ⟨CircleFubini.foldH_mem_Hbar' w, hρ⟩).comp
      RegClosure.tendsto_radius_nhdsGT
  have e2 : ∫ v, φ v ∂foldedCircle (foldH w) ρ = GoodSample.smoothFun φ w ρ :=
    RegClosure.integral_fc_foldH hφ.continuousOn w ρ
  rw [e2] at h
  refine h.congr fun k => ?_
  exact RegClosure.integral_fc_foldH
    (GoodSample.continuous_smoothFun hφ.continuousOn _).continuousOn w ρ

/-- **Main deterministic lemma.** For every folded circle `fc(w, ρ)` (also through `0`),
`∫∫ p d fc(u, 2^{-k}) d fc(w, ρ)(u) → ∫ p d fc(w, ρ)`. -/
theorem tendsto_integral_smoothFun_rp (hgm : Measurable g) (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) (w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun k => ∫ u, GoodSample.smoothFun (rp g) u (radius k) ∂foldedCircle w ρ) atTop
      (𝓝 (∫ v, rp g v ∂foldedCircle w ρ)) := by
  have hC := nonneg_of_bd hbd
  refine tendsto_of_approx
    (fun j k => ∫ u, GoodSample.smoothFun (rpT g (sj j ^ 2)) u (radius k) ∂foldedCircle w ρ)
    (fun j => GoodSample.smoothFun (rpT g (sj j ^ 2)) w ρ)
    (fun j k => ∫ u, (GoodSample.smoothFun (Ls (sj j)) u (radius k) -
      Real.log (max (radius k) ‖u‖)) ∂foldedCircle w ρ)
    (fun j => GoodSample.smoothFun (Ls (sj j)) w ρ - Real.log (max ρ ‖w‖))
    (K := 8 * C) (by positivity)
    (fun j => tendsto_integral_smoothFun_fc (continuous_rpT hgc (pow_pos (sj_pos j) 2)) w hρ)
    (fun j k => ?_)
    (fun j => (abs_smoothFun_rp_sub_le hgm hgc hbd (sj_pos j) (sj_le_half j) w hρ).2)
    (fun j => ?_) ?_
  · have i1 := RegClosure.integrable_fc
      (continuous_smoothFun_rp hgm hgc hbd (radius_pos k)).continuousOn w hρ.le
    have i2 := RegClosure.integrable_fc (GoodSample.continuous_smoothFun
      (continuous_rpT hgc (pow_pos (sj_pos j) 2)).continuousOn (radius k)).continuousOn w hρ.le
    have i3 := RegClosure.integrable_fc ((GoodSample.continuous_smoothFun
      (continuous_Ls (sj_pos j)).continuousOn (radius k)).sub
        (CoordReg.continuous_log_max_norm (radius_pos k))).continuousOn w hρ.le
    rw [← integral_sub i1 i2, ← integral_const_mul]
    have := norm_integral_le_of_norm_le (i3.const_mul (8 * C)) (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact (abs_smoothFun_rp_sub_le hgm hgc hbd (sj_pos j) (sj_le_half j) u
        (radius_pos k)).2)
    rwa [Real.norm_eq_abs] at this
  · have h := (tendsto_integral_smoothFun_fc (continuous_Ls (sj_pos j)) w hρ).sub
      (tendsto_integral_log_max_fc w hρ)
    rw [CoordReg.integral_log_norm_foldedCircle w hρ] at h
    refine h.congr fun k => (integral_sub ?_ ?_).symm
    · exact RegClosure.integrable_fc (GoodSample.continuous_smoothFun
        (continuous_Ls (sj_pos j)).continuousOn (radius k)).continuousOn w hρ.le
    · exact RegClosure.integrable_fc
        (CoordReg.continuous_log_max_norm (radius_pos k)).continuousOn w hρ.le
  · refine (tendsto_integral_Ls_sub w hρ).congr fun j => ?_
    rw [integral_sub (RegClosure.integrable_fc (continuous_Ls (sj_pos j)).continuousOn w hρ.le)
      (CoordReg.integrable_log_norm_foldedCircle w ρ),
      CoordReg.integral_log_norm_foldedCircle w hρ]
    rfl

end RC3Two
end F1
end QuantumZipper
