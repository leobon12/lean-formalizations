import QuantumZipper.Proofs.Zipper.JointModRandom
import QuantumZipper.Proofs.Zipper.RegUnif

/-!
# JOINTMOD, step 5: assembly of `JointModStmt`

The raw values of the unzipped field split as (`ae_raw_eq`, a.s. at each parameter)

`y_t(fc(c,r)) = Zr(pr4 (t,c,r)) + Ddet κ γ W (t,(c,r))`,

with `Zr` the continuous modification of the free-field part (`ae_contMod_evalReg`) and the
deterministic part `Ddet κ γ W (t,(c,r)) = (2/√κ)∫ log‖z‖ dν_t(c,r) + Q ∫ log‖(ψ_t)'‖ dfc(c,r)`
(`h⁰` term and coordinate-change term). Hence (`jointModCore_of_detCont`) a continuous
modification of the raw values exists once `Ddet` is jointly continuous for every continuous
driver with `W 0 = 0` (`DetContStmt`, proved in `JointModDetCont`). The circle commutation and
`JointModStmt` itself: `JointModComm`, `JointModFinal`.

Sources: see `JointModRandom`; the splitting of `evalReg` is that of
`RegCont.continuousOn_evalReg_of_uc` (Frostman truncation `RegCont.integral_log_max_sub_le`).
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

open CharFun TwoPoint UnzipInvariance RegCont KolmD RegSample

/-! ## The deterministic part -/

/-- The deterministic part of the raw value `y_t(fc(c,r))`. -/
def Ddet (κ γ : ℝ) (W : ℝ → ℝ) (p : ℝ × (ℂ × ℝ)) : ℝ :=
  2 / Real.sqrt κ * (∫ z, Real.log ‖z‖ ∂νT W p.2.1 p.2.2 p.1) +
    Qc γ * ∫ u, Real.log ‖deriv (fwdMapInv W p.1) u‖ ∂foldedCircle p.2.1 p.2.2

/-- **Deterministic input** (proved: `detContStmt_holds`). The deterministic part is jointly
continuous in `(t, c, r) ∈ [0,T] × Hbar × (0,∞)` for every continuous driver with `W 0 = 0`. -/
def DetContStmt (κ γ T : ℝ) : Prop :=
  ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → ContinuousOn (Ddet κ γ W) (parSet T)

/-- **Splitting of the regularized value** of `h⁰ + x` against an unzipped circle. -/
theorem evalReg_h0rev_add_of_tendsto {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (w : ℂ) {r : ℝ} (hr : 0 < r) (κ : ℝ) {x : FieldSample} (hx : RegAvgGood x)
    {L : ℝ} (hL : Tendsto (fun k => ∫ z, avgReg x k z ∂νT W w r t) atTop (𝓝 L)) :
    evalReg (ofFun (h0rev κ) + x) (νT W w r t) =
      2 / Real.sqrt κ * (∫ z, Real.log ‖z‖ ∂νT W w r t) + L := by
  obtain ⟨C, B, hC, hB, hfacts⟩ := νT_facts hW hW0 t w hr
  obtain ⟨hP, hF, hae⟩ := hfacts t ⟨ht, le_rfl⟩
  have hK : IsCompact (Metric.closedBall (0 : ℂ) B ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hνK : νT W w r t (Metric.closedBall (0 : ℂ) B ∩ Hbar)ᶜ = 0 := by
    have h1 : ∀ᵐ z ∂νT W w r t, z ∈ Metric.closedBall (0 : ℂ) B ∩ Hbar :=
      hae.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
    exact ae_iff.1 h1
  have hint : ∀ G : ℂ → ℝ, ContinuousOn G Hbar → Integrable G (νT W w r t) := fun G hG =>
    FrostmanReg.integrable_of_continuousOn_frostman hK inter_subset_right hνK hG
  have e : ∀ k, ∫ z, avgReg (ofFun (h0rev κ) + x) k z ∂νT W w r t =
      2 / Real.sqrt κ * (∫ z, Real.log (max (radius k) ‖z‖) ∂νT W w r t) +
        ∫ z, avgReg x k z ∂νT W w r t := by
    intro k
    rw [integral_congr_ae (hae.mono fun z hz =>
        avgReg_h0rev_add κ hx k ((show (0 : ℝ) < z.im from hz.1).le)),
      integral_add ((hint _ (Continuous.log (continuous_const.max continuous_norm) fun d =>
        ((radius_pos k).trans_le (le_max_left _ _)).ne').continuousOn).const_mul _)
        (hint _ (hx k).1), integral_const_mul]
  have hlog : Tendsto (fun k => ∫ z, Real.log (max (radius k) ‖z‖) ∂νT W w r t) atTop
      (𝓝 (∫ z, Real.log ‖z‖ ∂νT W w r t)) := by
    have ht3 := (tendsto_rpow_radius_zero (a := 1 / 3) (by norm_num)).const_mul (3 * C)
    rw [mul_zero] at ht3
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
      (fun k => ?_) ht3)
    rw [Real.norm_eq_abs]
    exact (integral_log_max_sub_le hF (hae.mono fun z hz h => by subst h; simp [H] at hz)
      (hae.mono fun z hz => hz.2) (radius_pos k) (radius_le_one k)).2
  unfold evalReg
  simp_rw [e]
  exact ((hlog.const_mul _).add hL).limUnder_eq

/-! ## Parameters -/

/-- The parameter `q = (Re c, Im c, log₂ r, t)`. -/
def pr4 (p : ℝ × (ℂ × ℝ)) : Fin 4 → ℝ := pr p.2.1 p.2.2 p.1

theorem ν4_pr4 {T : ℝ} (W : ℝ → ℝ) {p : ℝ × (ℂ × ℝ)} (hp : p ∈ parSet T) :
    ν4 W T (pr4 p) = νT W p.2.1 p.2.2 p.1 := by
  obtain ⟨ht, hc, hr⟩ := hp
  have htP : tP T (pr4 p) = p.1 := by
    show max (min p.1 T) 0 = p.1
    rw [min_eq_left ht.2, max_eq_left ht.1]
  show νT W (cen (pr4 p)) (rad (pr4 p)) (tP T (pr4 p)) = _
  rw [htP]
  unfold pr4
  rw [cen_pr hc, rad_pr _ hr]

theorem continuousOn_pr4 (T : ℝ) : ContinuousOn pr4 (parSet T) :=
  continuousOn_pr.comp (f := fun p : ℝ × (ℂ × ℝ) => (p.2, p.1))
    (continuous_snd.prodMk continuous_fst).continuousOn fun _ hp => hp.2.2

/-! ## The raw identity and the assembly -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem ae_drive_good {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ : ℝ) :
    ∀ᵐ ω ∂P, Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0 := by
  obtain ⟨B', -, hB'c, hB'eq⟩ := exists_good_version hB
  filter_upwards [hB'eq, hB.eval_zero_ae_eq_zero] with ω heq h0
  have hdrive : drive κ B ω = drive κ B' ω := funext fun t => by simp [drive, heq]
  refine ⟨?_, ?_⟩
  · rw [hdrive]; exact continuous_const.mul ((hB'c ω).comp continuous_real_toNNReal)
  · simp [drive, h0]

/-- **The raw identity** at a parameter of `[0,T] × Hbar × (0,∞)`. -/
theorem ae_raw_eq [IsProbabilityMeasure P] (κ γ : ℝ) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) {T : ℝ} {Zr : (Fin 4 → ℝ) → Ω → ℝ}
    (hZr : ∀ q, ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, avgReg (X ω) k z ∂ν4 (drive κ B ω) T q) atTop
      (𝓝 (Zr q ω)))
    {p : ℝ × (ℂ × ℝ)} (hp : p ∈ parSet T) :
    ∀ᵐ ω ∂P, unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) p.1
      (foldedCircle p.2.1 p.2.2) = Zr (pr4 p) ω + Ddet κ γ (drive κ B ω) p := by
  have hreg : ∀ᵐ ω ∂P, RegAvgGood (X ω) :=
    ae_all_iff.2 fun k => FrostmanReg.ae_circleAvg_tendsto_frostman hX k
  filter_upwards [hZr (pr4 p), hreg, ae_drive_good hB κ] with ω h1 h2 h3
  rw [ν4_pr4 _ hp] at h1
  simp only [unzippedField, coordChange, Ddet]
  rw [evalReg_h0rev_add_of_tendsto h3.1 h3.2 hp.1.1 p.2.1 hp.2.2 κ h2 h1]
  ring

end RegUnif
end QuantumZipper
