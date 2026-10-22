import HigherDimLQGContinuity.ConvTransfer.Chain

/-!
# Deterministic envelope transfer from a dyadic local modulus
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd)
open HigherDimLQGMetric.DGZ

/-- A local dyadic estimate controls the rational envelope of any bounded
real-cutoff perturbation after the similarity change of variables. -/
theorem convEnv_model_envelope_bound {d : ℕ} {ξ σ R r Γ H a : ℝ}
    (hσ : 0 ≤ σ) (hr : 1 / 2 < r)
    (hH : 0 ≤ H) (ha : 0 ≤ a)
    {Φ ψ : Rd d → ℝ} (hΦ : Continuous Φ) (hψ : Continuous ψ)
    (hDiff : ∀ z ∈ closedBall (0 : Rd d) (2 * R + 12),
      |Φ (r • z) - ψ z| ≤ Γ)
    (hLocal : ∀ z ∈ closedBall (0 : Rd d) (2 * R + 6),
      ∀ s ∈ Ioc (0 : ℝ) 1, ∀ x ∈ ball z s, ∀ y ∈ ball z s,
        HigherDimLFPP.lfppDistOn ξ ψ (ball z (3 / 2 * s)) x y ≤ H * s ^ σ * a) :
    ratEnvelope ξ σ R ⟨Φ, hΦ⟩ ≤
      ENNReal.ofReal (20 * r * Real.exp (|ξ| * Γ) * H * a) := by
  have hr0 : 0 < r := by linarith
  apply iSup_le
  intro i
  let w : Rd d := HigherDimLFPP.ratPt i.1.1
  let t : ℝ := i.1.2
  have ht : 0 < t := i.2.2.1
  have ht2 : t ≤ 2 := i.2.2.2
  have hw : w ∈ closedBall (0 : Rd d) (R + 1) := i.2.1
  let w' : Rd d := r⁻¹ • w
  let t' : ℝ := t / r
  have ht' : 0 < t' := div_pos ht hr0
  have ht'4 : t' ≤ 4 := by dsimp [t']; apply (div_le_iff₀ hr0).2; nlinarith
  have hrw : r • w' = w := by
    simp only [w', smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
  have hrt : r * t' = t := by dsimp [t']; field_simp
  have hw' : w' ∈ closedBall (0 : Rd d) ((2 * R + 6) - 4) := by
    have hwi : ‖w‖ ≤ R + 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    have hri : r⁻¹ ≤ 2 := by
      rw [← one_div]
      exact (div_le_iff₀ hr0).2 (by linarith)
    have hn : ‖w'‖ ≤ 2 * (R + 1) := by
      dsimp [w']
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
      exact mul_le_mul hri hwi (norm_nonneg _) (by linarith)
    change dist w' 0 ≤ (2 * R + 6) - 4
    rw [dist_zero_right]
    linarith
  let F : Rd d → ℝ := fun z => Φ (r • z)
  have hFc : Continuous F := hΦ.comp (continuous_id.const_smul r)
  have hU : (fun z : Rd d => (0 : Rd d) + r • (LinearIsometryEquiv.refl ℝ (Rd d)) z) ''
      ball w' t' = ball w t := by
    simpa only [zero_add, LinearIsometryEquiv.coe_refl, id, hrw, hrt] using
      (image_ball_sim (O := LinearIsometryEquiv.refl ℝ (Rd d))
        (x₀ := (0 : Rd d)) hr0 w' t')
  have hV : (fun z : Rd d => (0 : Rd d) + r • (LinearIsometryEquiv.refl ℝ (Rd d)) z) ''
      ball w' (29 / 20 * t') = ball w (29 / 20 * t) := by
    have he : r * (29 / 20 * t') = 29 / 20 * t := by rw [← hrt]; ring
    simpa only [zero_add, LinearIsometryEquiv.coe_refl, id, hrw, he] using
      (image_ball_sim (O := LinearIsometryEquiv.refl ℝ (Rd d))
        (x₀ := (0 : Rd d)) hr0 w' (29 / 20 * t'))
  have hScale : lfppDiam ξ Φ (ball w t) (ball w (29 / 20 * t)) =
      r * lfppDiam ξ F (ball w' t') (ball w' (29 / 20 * t')) := by
    rw [← hU, ← hV]
    simpa only [zero_add, LinearIsometryEquiv.coe_refl, id, F] using
      (lfppDiam_sim (O := LinearIsometryEquiv.refl ℝ (Rd d))
        (x₀ := (0 : Rd d)) (ξ := ξ) (φ := Φ) hr0
        (ball w' t') (ball w' (29 / 20 * t')))
  have hUV : ball w' t' ⊆ ball w' (29 / 20 * t') :=
    ball_subset_ball (by nlinarith)
  have hK : closedBall w' t' ⊆ ball w' (29 / 20 * t') :=
    closedBall_subset_ball (by nlinarith)
  have hbdd := bddAbove_lfppDiam_of_isCompact isOpen_ball
    (convex_ball _ _).isPreconnected hψ ξ
    (isCompact_closedBall w' t') hK ball_subset_closedBall
  have hVball : ball w' (29 / 20 * t') ⊆
      closedBall (0 : Rd d) (2 * R + 12) := by
    intro z hz
    have hz' : dist z w' < 29 / 20 * t' := hz
    have hzw := dist_triangle z w' (0 : Rd d)
    have hwi : dist w' 0 ≤ 2 * R + 2 := by
      have hraw : dist w' 0 ≤ (2 * R + 6) - 4 :=
        Metric.mem_closedBall.mp hw'
      linarith
    change dist z 0 ≤ 2 * R + 12
    linarith
  have hcomp : lfppDiam ξ F (ball w' t') (ball w' (29 / 20 * t')) ≤
      Real.exp (|ξ| * Γ) * lfppDiam ξ ψ (ball w' t') (ball w' (29 / 20 * t')) :=
    lfppDiam_le_exp_mul hFc hψ (fun z hz => hDiff z (hVball hz)) hbdd
  have hdyad : lfppDiam ξ ψ (ball w' t') (ball w' (29 / 20 * t')) ≤
      20 * H * (t' / 5) ^ σ * a :=
    convEnv_diam_of_local hψ ht' ht'4 hH ha hw' hLocal
  have hτt : t' / 5 ≤ t := by
    dsimp [t']
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).2
    apply (div_le_iff₀ hr0).2
    nlinarith
  have hpow : (t' / 5) ^ σ ≤ t ^ σ :=
    Real.rpow_le_rpow (by positivity) hτt hσ
  have hdiam : lfppDiam ξ Φ (ball w t) (ball w (29 / 20 * t)) ≤
      20 * r * Real.exp (|ξ| * Γ) * H * a * t ^ σ := by
    rw [hScale]
    calc
      r * lfppDiam ξ F (ball w' t') (ball w' (29 / 20 * t')) ≤
          r * (Real.exp (|ξ| * Γ) * lfppDiam ξ ψ
            (ball w' t') (ball w' (29 / 20 * t'))) :=
              mul_le_mul_of_nonneg_left hcomp hr0.le
      _ ≤ r * (Real.exp (|ξ| * Γ) * (20 * H * (t' / 5) ^ σ * a)) := by
        gcongr
      _ ≤ 20 * r * Real.exp (|ξ| * Γ) * H * a * t ^ σ := by
        have hfac : 0 ≤ 20 * r * Real.exp (|ξ| * Γ) * H * a := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hpow hfac]
  have hterm : t ^ (-σ) * lfppDiam ξ Φ (ball w t) (ball w (29 / 20 * t)) ≤
      20 * r * Real.exp (|ξ| * Γ) * H * a := by
    have hpow0 : 0 ≤ t ^ (-σ) := Real.rpow_nonneg ht.le _
    have hp : t ^ (-σ) * t ^ σ = 1 := by
      rw [Real.rpow_neg ht.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos ht σ).ne']
    calc
      t ^ (-σ) * lfppDiam ξ Φ (ball w t) (ball w (29 / 20 * t)) ≤
          t ^ (-σ) * (20 * r * Real.exp (|ξ| * Γ) * H * a * t ^ σ) :=
            mul_le_mul_of_nonneg_left hdiam hpow0
      _ = (20 * r * Real.exp (|ξ| * Γ) * H * a) * (t ^ (-σ) * t ^ σ) := by ring
      _ = 20 * r * Real.exp (|ξ| * Γ) * H * a := by rw [hp, mul_one]
  exact ENNReal.ofReal_le_ofReal hterm

/-- The model envelope is controlled by the dyadic local factor and the
Gaussian correction on the full W1 good event. -/
theorem convEnv_model_bound {d : ℕ} {κ : Rd d → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ b σ R r : ℝ} (hd : 2 ≤ d) (hξ : 0 < ξ) (hξb : ξ ≤ b)
    (hσ : 0 ≤ σ) (hR : 1 ≤ R) (hr : 1 / 2 < r) (hr1 : r ≤ 1)
    {W : HigherDimLFPP.WN d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H)
    (N : ℕ) {T I Φ : Rd d → Ω → ℝ}
    (hTc : ∀ ω, Continuous fun z => T z ω)
    (hIc : ∀ ω, Continuous fun z => I z ω)
    (hΦc : ∀ ω, Continuous fun z => Φ z ω)
    (m : Ω → ℝ)
    (hΦeq : ∀ z ω, Φ (r • z) ω = H N z ω + T z ω - m ω + I (r • z) ω)
    (Hr : Ω → ℝ) (hHr : ∀ ω, 1 ≤ Hr ω)
    (hGood : ∀ᵐ ω ∂P, ∀ z ∈ closedBall (0 : Rd d) (2 * R + 6),
      ∀ s ∈ Ioc (0 : ℝ) 1, ∀ x ∈ ball z s, ∀ y ∈ ball z s,
        HigherDimLFPP.lfppDistOn ξ (fun w => H N w ω) (ball z (3 / 2 * s)) x y ≤
          Hr ω * s ^ σ * aQ P H ξ N 2⁻¹) :
    ∀ᵐ ω ∂P, ratEnvelope ξ σ R ⟨fun z => Φ z ω, hΦc ω⟩ ≤
      ENNReal.ofReal (20 * r * Real.exp (b * convModelGamma R T I m ω) *
        Hr ω * aQ P H ξ N 2⁻¹) := by
  have ha : 0 ≤ aQ P H ξ N 2⁻¹ :=
    (tight_aQ_pos (by omega : 0 < d)
      hH ξ N (by norm_num) (by norm_num)).le
  filter_upwards [hGood] with ω hω
  have hΓ : 0 ≤ convModelGamma R T I m ω := by
    have h0 : (0 : Rd d) ∈ closedBall 0 (2 * R + 12) :=
      mem_closedBall_self (by linarith)
    exact (abs_nonneg _).trans
      (convModelGamma_bound (R := R) (r := r) (by linarith : 0 ≤ R)
        (by linarith : 0 ≤ r) hr1 hTc hIc m ω h0)
  have hDiff : ∀ z ∈ closedBall (0 : Rd d) (2 * R + 12),
      |Φ (r • z) ω - H N z ω| ≤ convModelGamma R T I m ω := by
    intro z hz
    rw [hΦeq z ω]
    have heq : H N z ω + T z ω - m ω + I (r • z) ω - H N z ω =
        T z ω + I (r • z) ω - m ω := by ring
    simpa only [heq] using
      (convModelGamma_bound (R := R) (r := r) (by linarith : 0 ≤ R)
        (by linarith : 0 ≤ r) hr1 hTc hIc m ω hz)
  have hHr0 : 0 ≤ Hr ω := (show (0 : ℝ) ≤ 1 by norm_num).trans (hHr ω)
  have hE := convEnv_model_envelope_bound hσ hr hHr0 ha
    (hΦc ω) ((hH.band N).continuous ω) hDiff hω
  have hExp : Real.exp (|ξ| * convModelGamma R T I m ω) ≤
      Real.exp (b * convModelGamma R T I m ω) := by
    rw [abs_of_pos hξ]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hξb hΓ)
  exact hE.trans (ENNReal.ofReal_le_ofReal (by gcongr))

/-- Divide the model envelope estimate by any normalizer bounded below by
the real-cutoff dyadic median. -/
theorem convEnv_model_ratio_bound {d : ℕ} {κ : Rd d → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ b σ R r c Aeps : ℝ}
    (hd : 2 ≤ d) (hξ : 0 < ξ) (hξb : ξ ≤ b)
    (hσ : 0 ≤ σ) (hR : 1 ≤ R) (hr : 1 / 2 < r) (hr1 : r ≤ 1)
    (hc : 0 < c)
    {W : HigherDimLFPP.WN d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H)
    (N : ℕ) (hAeps : c * r * aQ P H ξ N 2⁻¹ ≤ Aeps)
    {T I Φ : Rd d → Ω → ℝ}
    (hTc : ∀ ω, Continuous fun z => T z ω)
    (hIc : ∀ ω, Continuous fun z => I z ω)
    (hΦc : ∀ ω, Continuous fun z => Φ z ω)
    (m : Ω → ℝ)
    (hΦeq : ∀ z ω, Φ (r • z) ω = H N z ω + T z ω - m ω + I (r • z) ω)
    (Hr : Ω → ℝ) (hHr : ∀ ω, 1 ≤ Hr ω)
    (hGood : ∀ᵐ ω ∂P, ∀ z ∈ closedBall (0 : Rd d) (2 * R + 6),
      ∀ s ∈ Ioc (0 : ℝ) 1, ∀ x ∈ ball z s, ∀ y ∈ ball z s,
        HigherDimLFPP.lfppDistOn ξ (fun w => H N w ω) (ball z (3 / 2 * s)) x y ≤
          Hr ω * s ^ σ * aQ P H ξ N 2⁻¹) :
    ∀ᵐ ω ∂P,
      (ratEnvelope ξ σ R ⟨fun z => Φ z ω, hΦc ω⟩).toReal / Aeps ≤
        (20 / c) * Real.exp (b * convModelGamma R T I m ω) * Hr ω := by
  have haQ : 0 < aQ P H ξ N 2⁻¹ :=
    tight_aQ_pos (by omega : 0 < d) hH ξ N (by norm_num) (by norm_num)
  have hr0 : 0 < r := by linarith
  have hAeps0 : 0 < Aeps :=
    lt_of_lt_of_le (mul_pos (mul_pos hc hr0) haQ) hAeps
  filter_upwards [convEnv_model_bound hd hξ hξb hσ hR hr hr1 hH N
    hTc hIc hΦc m hΦeq Hr hHr hGood] with ω hEnv
  let E : ℝ≥0∞ := ratEnvelope ξ σ R ⟨fun z => Φ z ω, hΦc ω⟩
  let Γ : ℝ := convModelGamma R T I m ω
  have hfac : 0 ≤ Real.exp (b * Γ) * Hr ω :=
    mul_nonneg (Real.exp_pos _).le ((show (0 : ℝ) ≤ 1 by norm_num).trans (hHr ω))
  have hQ : 0 ≤ 20 * r * Real.exp (b * Γ) * Hr ω * aQ P H ξ N 2⁻¹ := by
    have h20r : 0 ≤ 20 * r := mul_nonneg (by norm_num) hr0.le
    have := mul_nonneg (mul_nonneg h20r hfac) haQ.le
    nlinarith
  have hEreal : E.toReal ≤ 20 * r * Real.exp (b * Γ) * Hr ω * aQ P H ξ N 2⁻¹ := by
    change E ≤ ENNReal.ofReal (20 * r * Real.exp (b * Γ) * Hr ω *
      aQ P H ξ N 2⁻¹) at hEnv
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEnv
    rwa [ENNReal.toReal_ofReal hQ] at h
  have hbase : 20 * (r * aQ P H ξ N 2⁻¹) ≤
      (20 / c) * Aeps := by
    rw [show (20 / c) * Aeps = (20 * Aeps) / c by ring]
    apply (le_div_iff₀ hc).2
    have h := mul_le_mul_of_nonneg_left hAeps (by norm_num : (0 : ℝ) ≤ 20)
    nlinarith [h]
  have hle : E.toReal ≤ ((20 / c) * Real.exp (b * Γ) * Hr ω) * Aeps := by
    calc
      E.toReal ≤ (Real.exp (b * Γ) * Hr ω) *
          (20 * (r * aQ P H ξ N 2⁻¹)) := by
            convert hEreal using 1
            ring
      _ ≤ (Real.exp (b * Γ) * Hr ω) * ((20 / c) * Aeps) :=
        mul_le_mul_of_nonneg_left hbase hfac
      _ = ((20 / c) * Real.exp (b * Γ) * Hr ω) * Aeps := by ring
  exact (div_le_iff₀ hAeps0).2 hle

end HigherDimLQGContinuity
