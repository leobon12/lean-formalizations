import QuantumZipper.Proofs.GFF.SmoothingConvergence
import QuantumZipper.Proofs.LQG.RegularSample
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# PAIR-LIM, part 1: the smoothing family `η ↦ η ∗ fc(·, s)` and its increment variances

For a measure `η` with density at most `M`, supported in `closedBall 0 R ∩ Hbar` and at height
`≥ δ` (`IsGoodSC`), put `μ_s = η.bind (foldedCircle · s)` (`μ_0 = η`). This file proves the
deterministic input of the continuum-limit theorem `PairLim.ae_tendsto_integral_evalReg_fc`
(`PairLim.lean`): for `0 ≤ s' ≤ s ≤ 1`

  `sup_x |Π_{μ_s}(x) - Π_{μ_{s'}}(x)| ≤ 8 π M (s - s')`,   `Π_μ(x) = ∫ neumannH x y dμ(y)`,

hence `Var(X μ_s - X μ_{s'}) ≤ 16 π M η(ℂ) |s - s'|` for a free boundary GFF modulo constants,
and the sixteenth-moment bound of the dyadic Kolmogorov criterion `KolmD`.

The pointwise input is `0 ≤ log max(s,d) - log max(s',d) ≤ min((s - s')/s', log⁺(s/d))`
(and `= 0` for `d ≥ s`), integrated against a density bounded by `M` (volume of a disk and the
logarithmic bound `lintegral_neg_log_norm_sub_div_le`).

Sources: this is the standard "circle average process is continuous in the radius" estimate
(Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), §3.1,
Prop. 3.1, whose proof bounds the variance of increments of `h_ε(z)` by the kernel and applies
the Kolmogorov–Čentsov criterion), here for circle averages integrated against a bounded density
(own elementary proof of the variance bound, cost rule of AGENT_GUIDE).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace PairLim

open SmoothConv

/-! ## 1. Pointwise estimates for `log max` -/

theorem logmax_sub_nonneg {s s' d : ℝ} (hs' : s' ≤ s) (hd : 0 < d) :
    0 ≤ Real.log (max s d) - Real.log (max s' d) := by
  have h1 : 0 < max s' d := lt_of_lt_of_le hd (le_max_right _ _)
  have := Real.log_le_log h1 (max_le_max hs' le_rfl)
  linarith

theorem logmax_sub_eq_zero {s s' d : ℝ} (hs' : s' ≤ s) (hsd : s ≤ d) :
    Real.log (max s d) - Real.log (max s' d) = 0 := by
  rw [max_eq_right hsd, max_eq_right (hs'.trans hsd), sub_self]

theorem logmax_sub_le_neglog {s s' d : ℝ} (hs' : s' ≤ s) (hd : 0 < d) (hs : 0 < s) :
    Real.log (max s d) - Real.log (max s' d) ≤ max (-Real.log (d / s)) 0 := by
  rcases le_total s d with h | h
  · rw [logmax_sub_eq_zero hs' h]; exact le_max_right _ _
  · refine le_trans ?_ (le_max_left _ _)
    rw [max_eq_left h, Real.log_div hd.ne' hs.ne']
    have := Real.log_le_log hd (le_max_right s' d)
    linarith

theorem logmax_sub_le_ratio {s s' d : ℝ} (hs'0 : 0 < s') (hs' : s' ≤ s) :
    Real.log (max s d) - Real.log (max s' d) ≤ (s - s') / s' := by
  rcases le_total s d with h | h
  · rw [logmax_sub_eq_zero hs' h]; exact div_nonneg (by linarith) hs'0.le
  · rw [max_eq_left h]
    have h1 := Real.log_le_log hs'0 (le_max_left s' d)
    have h2 : Real.log s - Real.log s' ≤ s / s' - 1 := by
      rw [← Real.log_div (by linarith) hs'0.ne']
      exact Real.log_le_sub_one_of_pos (div_pos (by linarith) hs'0)
    have h3 : s / s' - 1 = (s - s') / s' := by field_simp
    linarith

theorem measurable_logmax (s : ℝ) (c : ℂ) :
    Measurable fun w : ℂ => Real.log (max s ‖w - c‖) :=
  Real.measurable_log.comp (measurable_const.max (measurable_id.sub_const c).norm)

/-! ## 2. The integrated estimate against a bounded density -/

theorem measure_singleton_of_le {η : Measure ℂ} {M : ℝ≥0} (hη : η ≤ (M : ℝ≥0∞) • volume)
    (c : ℂ) : η {c} = 0 :=
  le_antisymm ((Measure.le_iff'.1 hη {c}).trans (by simp)) zero_le

theorem lintegral_logmax_sub_le {η : Measure ℂ} {M : ℝ≥0} (hη : η ≤ (M : ℝ≥0∞) • volume)
    (c : ℂ) {s s' : ℝ} (hs'0 : 0 ≤ s') (hs' : s' ≤ s) (hs : 0 < s) :
    ∫⁻ w, ENNReal.ofReal (Real.log (max s ‖w - c‖) - Real.log (max s' ‖w - c‖)) ∂η ≤
      (M : ℝ≥0∞) * ENNReal.ofReal (4 * π * s * (s - s')) := by
  have hne : ∀ᵐ w ∂η, w ≠ c := by
    rw [ae_iff]; simpa using measure_singleton_of_le hη c
  have hπ := Real.pi_pos
  by_cases hcase : s / 2 ≤ s'
  · have hs'p : 0 < s' := by linarith
    calc ∫⁻ w, ENNReal.ofReal (Real.log (max s ‖w - c‖) - Real.log (max s' ‖w - c‖)) ∂η
        ≤ ∫⁻ w, (Metric.closedBall c s).indicator
            (fun _ => ENNReal.ofReal (2 * (s - s') / s)) w ∂η := by
          refine lintegral_mono fun w => ?_
          by_cases hw : w ∈ Metric.closedBall c s
          · rw [indicator_of_mem hw]
            apply ENNReal.ofReal_le_ofReal
            refine (logmax_sub_le_ratio hs'p hs').trans ?_
            rw [div_le_div_iff₀ hs'p hs]; nlinarith
          · rw [indicator_of_notMem hw]
            have : s < ‖w - c‖ := by
              simpa [Metric.mem_closedBall, dist_eq_norm] using hw
            rw [logmax_sub_eq_zero hs' this.le]; simp
      _ = ENNReal.ofReal (2 * (s - s') / s) * η (Metric.closedBall c s) :=
          lintegral_indicator_const measurableSet_closedBall _
      _ ≤ ENNReal.ofReal (2 * (s - s') / s) *
            ((M : ℝ≥0∞) * volume (Metric.closedBall c s)) := by
          gcongr
          have := Measure.le_iff'.1 hη (Metric.closedBall c s)
          rwa [Measure.smul_apply, smul_eq_mul] at this
      _ = (M : ℝ≥0∞) * (ENNReal.ofReal (2 * (s - s') / s) * ENNReal.ofReal (s ^ 2) *
            ENNReal.ofReal π) := by
          rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow hs.le,
            show ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal π by
              rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]]
          ring
      _ = (M : ℝ≥0∞) * ENNReal.ofReal (2 * (s - s') / s * s ^ 2 * π) := by
          rw [← ENNReal.ofReal_mul (by apply div_nonneg <;> linarith),
            ← ENNReal.ofReal_mul (by positivity)]
      _ = (M : ℝ≥0∞) * ENNReal.ofReal (2 * π * s * (s - s')) := by
          congr 2; field_simp
      _ ≤ (M : ℝ≥0∞) * ENNReal.ofReal (4 * π * s * (s - s')) := by
          gcongr; nlinarith [mul_nonneg (mul_nonneg hπ.le hs.le) (sub_nonneg.2 hs')]
  · push_neg at hcase
    calc ∫⁻ w, ENNReal.ofReal (Real.log (max s ‖w - c‖) - Real.log (max s' ‖w - c‖)) ∂η
        ≤ ∫⁻ w, ENNReal.ofReal (-Real.log (‖w - c‖ / s)) ∂η := by
          refine lintegral_mono_ae ?_
          filter_upwards [hne] with w hw
          have hd : 0 < ‖w - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
          have h := logmax_sub_le_neglog (d := ‖w - c‖) hs' hd hs
          refine ENNReal.ofReal_le_ofReal_iff'.2 ?_
          rcases le_total (-Real.log (‖w - c‖ / s)) 0 with h0 | h0
          · right; rwa [max_eq_right h0] at h
          · left; rwa [max_eq_left h0] at h
      _ ≤ (M : ℝ≥0∞) * ENNReal.ofReal (2 * π * s ^ 2) :=
          lintegral_neg_log_norm_sub_div_le hη c hs
      _ ≤ (M : ℝ≥0∞) * ENNReal.ofReal (4 * π * s * (s - s')) := by
          exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
            (by nlinarith [mul_pos (mul_pos hπ hs) (show 0 < s - 2 * s' by linarith)])) _

/-! ## 3. Potentials of the smoothed measures -/

/-- The potential of `η` smoothed at radius `s`: `x ↦ ∫ Nr s w x dη(w)`. -/
def Pot (η : Measure ℂ) (s : ℝ) (x : ℂ) : ℝ := ∫ w, Nr s w x ∂η

theorem Nr_zero (w x : ℂ) : Nr 0 w x = neumannH w x := by
  unfold Nr neumannH
  rw [max_eq_right (norm_nonneg _), max_eq_right (norm_nonneg _)]

theorem integrable_Nr {M : ℝ≥0} {R s : ℝ} {η : Measure ℂ} (hs : 0 ≤ s)
    (h : IsGoodSC M R η) (x : ℂ) : Integrable (fun w => Nr s w x) η := by
  rcases hs.eq_or_lt with h0 | h0
  · subst h0; simp only [Nr_zero]; exact integrable_neumannH_left_sc h x
  · exact integrable_Nr_left h0 h x

theorem Nr_sub_eq (s s' : ℝ) (w x : ℂ) :
    Nr s' w x - Nr s w x =
      (Real.log (max s ‖w - x‖) - Real.log (max s' ‖w - x‖)) +
        (Real.log (max s ‖w - conj x‖) - Real.log (max s' ‖w - conj x‖)) := by
  unfold Nr; ring

/-- **Lipschitz bound for the potentials in the smoothing radius.** -/
theorem abs_Pot_sub_le {M : ℝ≥0} {R : ℝ} {η : Measure ℂ} (h : IsGoodSC M R η) (x : ℂ)
    {s s' : ℝ} (hs'0 : 0 ≤ s') (hs' : s' ≤ s) (hs1 : s ≤ 1) :
    |Pot η s x - Pot η s' x| ≤ 8 * π * M * (s - s') := by
  have hπ := Real.pi_pos
  rcases (hs'0.trans hs').eq_or_lt with h0 | hs
  · have : s' = 0 := le_antisymm (h0 ▸ hs') hs'0
    subst this; rw [← h0]; simp
  have := h.isFiniteMeasure
  set f : ℂ → ℂ → ℝ := fun c w => Real.log (max s ‖w - c‖) - Real.log (max s' ‖w - c‖)
    with hf
  have hfm : ∀ c, Measurable (f c) := fun c =>
    (measurable_logmax s c).sub (measurable_logmax s' c)
  have hne : ∀ c, ∀ᵐ w ∂η, w ≠ c := fun c => by
    rw [ae_iff]; simpa using h.measure_singleton c
  set g : ℂ → ℝ := fun w => Nr s' w x - Nr s w x with hg
  have hgf : ∀ w, g w = f x w + f (conj x) w := fun w => Nr_sub_eq s s' w x
  have hgi : Integrable g η := (integrable_Nr hs'0 h x).sub (integrable_Nr hs.le h x)
  have hgnn : 0 ≤ᵐ[η] g := by
    filter_upwards [hne x, hne (conj x)] with w h1 h2
    rw [hgf]
    exact add_nonneg (logmax_sub_nonneg hs' (norm_pos_iff.2 (sub_ne_zero.2 h1)))
      (logmax_sub_nonneg hs' (norm_pos_iff.2 (sub_ne_zero.2 h2)))
  have hPot : Pot η s' x - Pot η s x = ∫ w, g w ∂η := by
    unfold Pot; rw [integral_sub (integrable_Nr hs'0 h x) (integrable_Nr hs.le h x)]
  have hlin : ∫⁻ w, ENNReal.ofReal (g w) ∂η ≤
      2 * ((M : ℝ≥0∞) * ENNReal.ofReal (4 * π * s * (s - s'))) := by
    calc ∫⁻ w, ENNReal.ofReal (g w) ∂η
        ≤ ∫⁻ w, (ENNReal.ofReal (f x w) + ENNReal.ofReal (f (conj x) w)) ∂η :=
          lintegral_mono fun w => by rw [hgf]; exact ENNReal.ofReal_add_le
      _ = ∫⁻ w, ENNReal.ofReal (f x w) ∂η + ∫⁻ w, ENNReal.ofReal (f (conj x) w) ∂η :=
          lintegral_add_left (hfm x).ennreal_ofReal _
      _ ≤ _ := by
          rw [two_mul]
          exact add_le_add (lintegral_logmax_sub_le h.1 x hs'0 hs' hs)
            (lintegral_logmax_sub_le h.1 (conj x) hs'0 hs' hs)
  have hint0 : 0 ≤ ∫ w, g w ∂η := integral_nonneg_of_ae hgnn
  have hle : ∫ w, g w ∂η ≤ 2 * (M * (4 * π * s * (s - s'))) := by
    rw [integral_eq_lintegral_of_nonneg_ae hgnn hgi.1]
    refine (ENNReal.toReal_mono (by finiteness) hlin).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (by positivity) (sub_nonneg.2 hs'))]
    simp
  rw [abs_sub_comm, abs_of_nonneg (by rw [hPot]; exact hint0), hPot]
  refine hle.trans ?_
  have hM : (0 : ℝ) ≤ M := M.coe_nonneg
  have h1 : 0 ≤ s - s' := by linarith
  have : 2 * (↑M * (4 * π * s * (s - s'))) = 8 * π * M * (s - s') * s := by ring
  rw [this]
  exact mul_le_of_le_one_right (by positivity) hs1

/-! ## 4. The smoothed family `μ_s = η.bind (foldedCircle · s)` -/

/-- `η` smoothed at radius `s` (folded circles). -/
def smooth (η : Measure ℂ) (s : ℝ) : Measure ℂ := η.bind fun w => foldedCircle w s

theorem smooth_zero {η : Measure ℂ} (hη : ∀ᵐ w ∂η, w ∈ Hbar) : smooth η 0 = η := by
  unfold smooth
  simp_rw [RegSample.fc_zero]
  rw [Measure.bind_dirac_eq_map _ measurable_foldH]
  conv_rhs => rw [← Measure.map_id (μ := η)]
  exact Measure.map_congr (hη.mono fun w hw => CircleFubini.foldH_of_mem' hw)

theorem smooth_univ (η : Measure ℂ) (s : ℝ) : smooth η s univ = η univ := bind_fc_univ η s

/-- Standing hypotheses on `η`: density `≤ M`, support in `closedBall 0 R ∩ Hbar`, height `≥ δ`,
with `0 < δ ≤ 1`. -/
structure Setup (M : ℝ≥0) (R δ : ℝ) (η : Measure ℂ) : Prop where
  good : IsGoodSC M R η
  pos : 0 < δ
  le_one : δ ≤ 1
  im : ∀ᵐ w ∂η, δ ≤ w.im

variable {M : ℝ≥0} {R δ : ℝ} {η : Measure ℂ}

theorem Setup.smooth_good (hS : Setup M R δ η) {s : ℝ} (hs0 : 0 ≤ s) (hsδ : s ≤ δ) :
    IsGoodSC M (R + 1) (smooth η s) :=
  hS.good.bind_fc hs0 (hsδ.trans hS.le_one) (hS.im.mono fun _ hw => hsδ.trans hw)

theorem Setup.integral_neumannH_smooth (hS : Setup M R δ η) {s : ℝ} (hs0 : 0 ≤ s)
    (hsδ : s ≤ δ) (x : ℂ) : ∫ y, neumannH x y ∂smooth η s = Pot η s x := by
  have := hS.good.isFiniteMeasure
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    rw [smooth_zero (hS.good.ae_mem.mono fun w hw => hw.2)]
    unfold Pot
    simp_rw [Nr_zero]
    exact integral_congr_ae (ae_of_all _ fun w => neumannH_symm x w)
  · exact integral_bind_neumannH h0 x (integrable_neumannH_right_sc (hS.smooth_good hs0 hsδ) x)

theorem Setup.integrable_Pot (hS : Setup M R δ η) {a b : ℝ} (ha0 : 0 ≤ a) (haδ : a ≤ δ)
    (hb0 : 0 ≤ b) (hbδ : b ≤ δ) : Integrable (Pot η b) (smooth η a) :=
  have := (hS.smooth_good hb0 hbδ).isFiniteMeasure
  (integrable_neumannH_prod_sc (hS.smooth_good ha0 haδ) (hS.smooth_good hb0 hbδ)).integral_prod_left
    |>.congr (ae_of_all _ fun x => hS.integral_neumannH_smooth hb0 hbδ x)

theorem Setup.abs_Pot_sub_le' (hS : Setup M R δ η) {a b : ℝ} (ha0 : 0 ≤ a) (haδ : a ≤ δ)
    (hb0 : 0 ≤ b) (hbδ : b ≤ δ) (x : ℂ) :
    |Pot η a x - Pot η b x| ≤ 8 * π * M * |a - b| := by
  rcases le_total b a with hab | hab
  · rw [abs_of_nonneg (sub_nonneg.2 hab)]
    exact abs_Pot_sub_le hS.good x hb0 hab (haδ.trans hS.le_one)
  · rw [abs_sub_comm, abs_sub_comm a, abs_of_nonneg (sub_nonneg.2 hab)]
    exact abs_Pot_sub_le hS.good x ha0 hab (hbδ.trans hS.le_one)

/-! ## 5. Gaussian moments and the Kolmogorov moment bound -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem Setup.map_diff_eq_gaussianReal (hS : Setup M R δ η) (hX : IsFreeGFFModConstH X P)
    {a b : ℝ} (ha0 : 0 ≤ a) (haδ : a ≤ δ) (hb0 : 0 ≤ b) (hbδ : b ≤ δ) :
    P.map (fun ω => X ω (smooth η a) - X ω (smooth η b)) =
      gaussianReal 0
        (kernelCov2 neumannH (smooth η a, smooth η b) (smooth η a, smooth η b)).toNNReal := by
  have hadz := (hS.smooth_good ha0 haδ).isAdmissibleH
  have hadw := (hS.smooth_good hb0 hbδ).isAdmissibleH
  have hmass : smooth η a univ = smooth η b univ := by rw [smooth_univ, smooth_univ]
  have hG : HasGaussianLaw (fun ω => X ω (smooth η a) - X ω (smooth η b)) P :=
    hX.gaussian.hasGaussianLaw_eval ⟨(smooth η a, smooth η b), hadz, hadw, hmass⟩
  have hm : AEMeasurable (fun ω => X ω (smooth η a) - X ω (smooth η b)) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  have hc : P[fun ω => X ω (smooth η a) - X ω (smooth η b)] = 0 := hX.centered _ _ hadz hadw hmass
  have hcov : cov[fun ω => X ω (smooth η a) - X ω (smooth η b),
      fun ω => X ω (smooth η a) - X ω (smooth η b); P] =
      kernelCov2 neumannH (smooth η a, smooth η b) (smooth η a, smooth η b) :=
    hX.covariance_eq (smooth η a, smooth η b) (smooth η a, smooth η b) hadz hadw hmass hadz hadw
      hmass
  rw [hG.map_eq_gaussianReal, hc, ← covariance_self hm, hcov]

/-- The radius parameter: `q ↦ min |q 0| δ`. -/
def sR (δ : ℝ) (q : Fin 1 → ℝ) : ℝ := min |q 0| δ

end PairLim
end QuantumZipper
