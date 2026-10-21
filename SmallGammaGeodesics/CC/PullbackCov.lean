import SmallGammaGeodesics.CC.PullbackZoom
import LQGMetric.Field.HeatMollifyVar
import LQGMetric.Field.HeatMollifyPoint
import LQGMetric.Field.GFFInvariance

/-!
# Continuity of `logCov` under uniform convergence (track CC, packet CC1; [3] (2.5))

Source: Gwynne–Miller arXiv:1905.00384 ([3]) Lemma 2.4, (2.5), in the `L²` form used by
`planning/audits/CC0-conformal-covariance-plan.md`, Details (a) D9 step 3: for test functions with
supports in one ball `B̄_R`, `logCov φ ψ ≤ C_R ‖φ‖_∞ ‖ψ‖_∞`, so `logCov (g_n − g) (g_n − g) → 0`
when `g_n → g` uniformly; for mean-zero test functions this is `E⟨h, g_n − g⟩² → 0` for a
whole-plane GFF.

The bound is LQGMetric's `abs_logCov_le` (`Field/HeatMollifyVar.lean`), and the variance identity is
`IsWholePlaneGFF.integral_sq` (`Field/HeatMollifyPoint.lean`).

* `abs_logCov_le_const`: `|logCov φ ψ| ≤ M N C_R` with `C_R = logCovConst R`;
* **T7** `tendsto_logCov_of_tendstoUniformly_zero`, `tendsto_logCov_sub_of_tendstoUniformly`;
* **T7, GFF form** `tendsto_integral_sq_sub_of_tendstoUniformly`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Function

namespace SmallGammaGeodesics.CC

open LQGMetric

/-- the constant `C_R = πR² (2R · πR² + ∫_{B̄_1} |log|u||)` of `LQGMetric.abs_logCov_le` -/
def logCovConst (R : ℝ) : ℝ := Real.pi * R ^ 2 * (2 * R * (Real.pi * R ^ 2) + logBallConst)

theorem logCovConst_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ logCovConst R := by
  have := logBallConst_nonneg
  unfold logCovConst
  positivity

/-- **The crude `logCov` bound**: `|logCov φ ψ| ≤ M N C_R` for `|φ| ≤ M`, `|ψ| ≤ N` vanishing off
`B̄_R(0)`. -/
theorem abs_logCov_le_const {φ ψ : ℂ → ℝ} {R M N : ℝ} (hR : 0 ≤ R) (hφ : ∀ x, |φ x| ≤ M)
    (hψ : ∀ y, |ψ y| ≤ N) (hφR : ∀ x, R < ‖x‖ → φ x = 0) (hψR : ∀ y, R < ‖y‖ → ψ y = 0) :
    |logCov φ ψ| ≤ M * N * logCovConst R := by
  have h := abs_logCov_le hR hφ hψ hφR hψR
  unfold logCovConst
  calc |logCov φ ψ| ≤ M * N * (Real.pi * R ^ 2) * (2 * R * (Real.pi * R ^ 2) + logBallConst) := h
    _ = M * N * (Real.pi * R ^ 2 * (2 * R * (Real.pi * R ^ 2) + logBallConst)) := by ring

section Tendsto

variable {ι : Type*} {l : Filter ι}

/-- **T7** ([3] (2.5), `L²` form): `logCov (d i) (e i) → 0` when `d i → 0` uniformly, the `e i` are
eventually uniformly bounded, and all supports eventually lie in one ball `B̄_R(0)`. -/
theorem tendsto_logCov_of_tendstoUniformly_zero {d e : ι → ℂ → ℝ} {R N : ℝ}
    (hd : TendstoUniformly d (fun _ => 0) l) (he : ∀ᶠ i in l, ∀ y, |e i y| ≤ N)
    (hdR : ∀ᶠ i in l, ∀ x, R < ‖x‖ → d i x = 0) (heR : ∀ᶠ i in l, ∀ y, R < ‖y‖ → e i y = 0) :
    Tendsto (fun i => logCov (d i) (e i)) l (𝓝 0) := by
  set R' : ℝ := max R 0
  have hR' : 0 ≤ R' := le_max_right _ _
  set C : ℝ := logCovConst R'
  have hC : 0 ≤ C := logCovConst_nonneg hR'
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / ((|N| + 1) * (C + 1))
  have hδ : 0 < δ := by positivity
  filter_upwards [Metric.tendstoUniformly_iff.1 hd δ hδ, he, hdR, heR] with i hdi hei hdRi heRi
  have hd' : ∀ x, |d i x| ≤ δ := fun x => by
    have := hdi x
    rw [Real.dist_eq, zero_sub, abs_neg] at this
    exact this.le
  have hdR' : ∀ x, R' < ‖x‖ → d i x = 0 := fun x hx => hdRi x ((le_max_left R 0).trans_lt hx)
  have heR' : ∀ y, R' < ‖y‖ → e i y = 0 := fun y hy => heRi y ((le_max_left R 0).trans_lt hy)
  have hb := abs_logCov_le_const hR' hd' hei hdR' heR'
  rw [Real.dist_eq, sub_zero]
  have hN : N ≤ |N| := le_abs_self N
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hei 0)
  calc |logCov (d i) (e i)| ≤ δ * N * C := hb
    _ ≤ δ * |N| * C := by gcongr
    _ < δ * ((|N| + 1) * (C + 1)) := by
        have : |N| * C < (|N| + 1) * (C + 1) := by nlinarith [abs_nonneg N]
        rw [mul_assoc]
        exact mul_lt_mul_of_pos_left this hδ
    _ = ε := by
        rw [div_mul_cancel₀]
        positivity

/-- **T7** ([3] (2.5)): if `g i → g₀` uniformly and all supports eventually lie in `B̄_R(0)`, then
`logCov (g i − g₀) (g i − g₀) → 0`. -/
theorem tendsto_logCov_sub_of_tendstoUniformly {g : ι → ℂ → ℝ} {g₀ : ℂ → ℝ} {R : ℝ}
    (hu : TendstoUniformly g g₀ l) (hgR : ∀ᶠ i in l, ∀ x, R < ‖x‖ → g i x = 0)
    (hg₀R : ∀ x, R < ‖x‖ → g₀ x = 0) :
    Tendsto (fun i => logCov (g i - g₀) (g i - g₀)) l (𝓝 0) := by
  have hd : TendstoUniformly (fun i => g i - g₀) (fun _ => 0) l := by
    rw [Metric.tendstoUniformly_iff] at hu ⊢
    intro ε hε
    filter_upwards [hu ε hε] with i hi x
    have := hi x
    rw [dist_comm, Real.dist_eq] at this
    rw [Real.dist_eq, zero_sub, abs_neg, Pi.sub_apply]
    exact this
  have he : ∀ᶠ i in l, ∀ y, |(g i - g₀) y| ≤ 1 := by
    filter_upwards [Metric.tendstoUniformly_iff.1 hd 1 one_pos] with i hi y
    have := hi y
    rw [Real.dist_eq, zero_sub, abs_neg] at this
    exact this.le
  have hdR : ∀ᶠ i in l, ∀ x, R < ‖x‖ → (g i - g₀) x = 0 := by
    filter_upwards [hgR] with i hi x hx
    rw [Pi.sub_apply, hi x hx, hg₀R x hx, sub_zero]
  exact tendsto_logCov_of_tendstoUniformly_zero hd he hdR hdR

/-- the difference of two mean-zero test functions, as a mean-zero test function -/
def testSub0 (φ ψ : TestC0) : TestC0 :=
  ⟨φ.1 - ψ.1, by
    show ∫ x, (φ.1 x - ψ.1 x) = 0
    rw [integral_sub (GFFInv.integrable_test φ.1) (GFFInv.integrable_test ψ.1), φ.2, ψ.2,
      sub_zero]⟩

theorem testSub0_coe (φ ψ : TestC0) : ((testSub0 φ ψ).1 : ℂ → ℝ) = ⇑φ.1 - ⇑ψ.1 :=
  rfl

/-- **T7, GFF form** ([3] (2.5)): for a whole-plane GFF `h` and mean-zero test functions
`φ i → φ₀` uniformly with supports eventually in one ball, `E⟨h, φ i − φ₀⟩² → 0`. -/
theorem tendsto_integral_sq_sub_of_tendstoUniformly {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {φ : ι → TestC0} {φ₀ : TestC0}
    {R : ℝ} (hu : TendstoUniformly (fun i x => (φ i).1 x) (fun x => φ₀.1 x) l)
    (hR : ∀ᶠ i in l, ∀ x, R < ‖x‖ → (φ i).1 x = 0) (hR₀ : ∀ x, R < ‖x‖ → φ₀.1 x = 0) :
    Tendsto (fun i => ∫ ω, (h ω (φ i).1 - h ω φ₀.1) ^ 2 ∂P) l (𝓝 0) := by
  have e : ∀ i, ∫ ω, (h ω (φ i).1 - h ω φ₀.1) ^ 2 ∂P =
      logCov ((fun x => (φ i).1 x) - fun x => φ₀.1 x)
        ((fun x => (φ i).1 x) - fun x => φ₀.1 x) := by
    intro i
    have h1 : ∀ ω, h ω (φ i).1 - h ω φ₀.1 = h ω (testSub0 (φ i) φ₀).1 := fun ω =>
      (map_sub (h ω) (φ i).1 φ₀.1).symm
    simp_rw [h1]
    rw [hh.integral_sq (testSub0 (φ i) φ₀), testSub0_coe]
  simp_rw [e]
  exact tendsto_logCov_sub_of_tendstoUniformly hu hR hR₀

end Tendsto

end SmallGammaGeodesics.CC
