import QuantumZipper.Proofs.LQG.CoordChangeKernel
import QuantumZipper.Proofs.GFF.Regularization

/-!
# M4-T4, step 1: regularization at pushed-forward semicircles

The per-measure smoothing identity of `SmoothingConvergence` / `Regularization` is stated for
measures with bounded Lebesgue density away from `ℝ`. Here it is extended to the curve measures
`pc ψ s r = ψ_* fc(s, r)`, which touch `ℝ` (the risk named in blueprint M4-T4).

* `abs_kernelCov2_bind_le`: for an admissible probability `η`, the smoothing variance
  `Var[X(η * fc_ρ) − X(η)]` is bounded by any uniform bound on the smoothing defects
  `∫ Lr ρ (·) x dη`, `x ∈ Hbar`.
* `integral_Lr_pc_bounds`: for `η = pc ψ s r` this defect is at most `16 ρ / (m r)` (a
  one-dimensional Frostman-type bound, proved with the exact circle averages of `log|· − y|`).
* `ae_evalReg_pc`: almost surely `evalReg (X ω) (pc ψ s r) = X ω (pc ψ s r)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace CoordChange

open SmoothConv CircleFubini

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Generic tools -/

theorem ae_tendsto_zero_of_summable_sq {P : Measure Ω} {D : ℕ → Ω → ℝ}
    (hD : ∀ k, AEMeasurable (D k) P) (hint : ∀ k, Integrable (fun ω => D k ω ^ 2) P)
    (hs : Summable fun k => ∫ ω, D k ω ^ 2 ∂P) :
    ∀ᵐ ω ∂P, Tendsto (fun k => D k ω) atTop (𝓝 0) := by
  set f : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (D k ω ^ 2)
  have hfm : ∀ k, AEMeasurable (f k) P := fun k => ((hD k).pow_const 2).ennreal_ofReal
  have hsum : ∫⁻ ω, ∑' k, f k ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum hfm]
    have e : ∀ k, ∫⁻ ω, f k ω ∂P = ENNReal.ofReal (∫ ω, D k ω ^ 2 ∂P) := fun k =>
      (ofReal_integral_eq_lintegral_ofReal (hint k) (ae_of_all _ fun ω => sq_nonneg _)).symm
    simp_rw [e]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun ω => sq_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hfm) hsum
  filter_upwards [hae] with ω hω
  have h1 : Tendsto (fun k => f k ω) atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact ENNReal.tendsto_cofinite_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun k => D k ω ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [f, Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have h4 := (Real.continuous_sqrt.tendsto 0).comp h2
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h4
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h4

theorem integral_sq_pair_eq {P : Measure Ω} {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {p₁ p₂ : Measure ℂ} (h₁ : IsAdmissibleH p₁) (h₂ : IsAdmissibleH p₂)
    (hm : p₁ univ = p₂ univ) :
    Integrable (fun ω => (X ω p₁ - X ω p₂) ^ 2) P ∧
      ∫ ω, (X ω p₁ - X ω p₂) ^ 2 ∂P = kernelCov2 neumannH (p₁, p₂) (p₁, p₂) := by
  refine ⟨(memLp_pair_sc hX h₁ h₂ hm).integrable_sq, ?_⟩
  have c1 := hX.covariance_eq (p₁, p₂) (p₁, p₂) h₁ h₂ hm h₁ h₂ hm
  dsimp only at c1
  have hmean := hX.centered _ _ h₁ h₂ hm
  rw [← c1]
  unfold covariance
  rw [hmean]
  simp only [sub_zero, sq]

/-! ### The smoothing defect -/

/-- `ell ρ d = log⁺ (ρ / d)`, written without division. -/
def ell (ρ d : ℝ) : ℝ := Real.log (max ρ d) - Real.log d

theorem ell_nonneg {ρ d : ℝ} (hd : 0 < d) : 0 ≤ ell ρ d :=
  sub_nonneg.2 (Real.log_le_log hd (le_max_right _ _))

theorem ell_anti {ρ d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (h : d₁ ≤ d₂) : ell ρ d₂ ≤ ell ρ d₁ := by
  have hd₂ : 0 < d₂ := hd₁.trans_le h
  unfold ell
  rcases le_total ρ d₁ with h1 | h1
  · rw [max_eq_right (h1.trans h), max_eq_right h1]; simp
  · rw [max_eq_left h1]
    rcases le_total ρ d₂ with h2 | h2
    · rw [max_eq_right h2]; linarith [Real.log_le_log hd₁ h1]
    · rw [max_eq_left h2]; linarith [Real.log_le_log hd₁ h]

theorem ell_mul {ρ l d : ℝ} (hl : 0 < l) (hd : 0 < d) : ell ρ (l * d) = ell (ρ / l) d := by
  unfold ell
  have e : max ρ (l * d) = l * max (ρ / l) d := by
    rw [mul_max_of_nonneg _ _ hl.le, mul_div_cancel₀ _ hl.ne']
  rw [e, Real.log_mul hl.ne' (hd.trans_le (le_max_right _ _)).ne', Real.log_mul hl.ne' hd.ne']
  ring

theorem Lr_eq_ell (ρ : ℝ) (w x : ℂ) : Lr ρ w x = ell ρ ‖w - x‖ + ell ρ ‖w - conj x‖ := by
  unfold Lr Nr neumannH ell; ring

theorem norm_sub_le_norm_sub_conj {w x : ℂ} (hw : w ∈ Hbar) (hx : x ∈ Hbar) :
    ‖w - x‖ ≤ ‖w - conj x‖ := by
  have hw' : 0 ≤ w.im := hw
  have hx' : 0 ≤ x.im := hx
  have h1 : ‖w - x‖ ^ 2 ≤ ‖w - conj x‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    nlinarith
  calc ‖w - x‖ = √(‖w - x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(‖w - conj x‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = ‖w - conj x‖ := Real.sqrt_sq (norm_nonneg _)

theorem Lr_bounds {ρ : ℝ} {w x : ℂ} (hw : w ∈ Hbar) (hx : x ∈ Hbar) (hd : 0 < ‖w - x‖) :
    0 ≤ Lr ρ w x ∧ Lr ρ w x ≤ 2 * ell ρ ‖w - x‖ := by
  have h := norm_sub_le_norm_sub_conj hw hx
  rw [Lr_eq_ell]
  refine ⟨add_nonneg (ell_nonneg hd) (ell_nonneg (hd.trans_le h)), ?_⟩
  have := ell_anti (ρ := ρ) hd h
  linarith

/-- The circle average of `log⁺(ρ/|v − c|)` is at most `ρ / r`. -/
theorem integral_ell_circle_le (s c : ℂ) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    Integrable (fun v => ell ρ ‖v - c‖) (circleUnif s r) ∧
      ∫ v, ell ρ ‖v - c‖ ∂circleUnif s r ≤ ρ / r := by
  have hcont : Continuous fun v : ℂ => Real.log (max ρ ‖v - c‖) :=
    (continuous_const.max (continuous_id.sub continuous_const).norm).log
      fun v => (hρ.trans_le (le_max_left _ _)).ne'
  have i1 : Integrable (fun v : ℂ => Real.log (max ρ ‖v - c‖)) (circleUnif s r) :=
    KernelId.integrable_circleUnif_of_continuous hcont s r
  have i2 := SmoothConv.integrable_log_norm_sub_circleUnif_sc s c r
  refine ⟨i1.sub i2, ?_⟩
  unfold ell
  rw [integral_sub i1 i2, SmoothConv.integral_log_norm_sub_circleUnif_sc s c hr]
  have hJ : ∫ v, Real.log (max ρ ‖v - c‖) ∂circleUnif s r ≤ Real.log (max r (‖s - c‖ + ρ)) := by
    have e1 : ∀ v : ℂ, Real.log (max ρ ‖v - c‖) = ∫ y, Real.log ‖y - v‖ ∂circleUnif c ρ := by
      intro v; rw [SmoothConv.integral_log_norm_sub_circleUnif_sc c v hρ, norm_sub_rev]
    simp_rw [e1]
    have hint : Integrable (Function.uncurry fun (v y : ℂ) => Real.log ‖y - v‖)
        ((circleUnif s r).prod (circleUnif c ρ)) := by
      have := LQGDimension.Coupling.integrable_log_circ_prod s c r hρ
      rw [← CircleMV.circleUnif_eq_circMeas, ← CircleMV.circleUnif_eq_circMeas] at this
      refine this.congr (ae_of_all _ fun p => ?_)
      simp only [Function.uncurry]
      rw [norm_sub_rev]
    rw [integral_integral_swap hint]
    have e2 : ∀ y : ℂ, ∫ v, Real.log ‖y - v‖ ∂circleUnif s r = Real.log (max r ‖s - y‖) := by
      intro y
      rw [← SmoothConv.integral_log_norm_sub_circleUnif_sc s y hr]
      congr 1; funext v; rw [norm_sub_rev]
    simp_rw [e2]
    have hb : ∀ᵐ y ∂circleUnif c ρ,
        Real.log (max r ‖s - y‖) ≤ Real.log (max r (‖s - c‖ + ρ)) := by
      filter_upwards [SmoothConv.ae_circleUnif_sc c ρ] with y hy
      refine Real.log_le_log (hr.trans_le (le_max_left _ _)) (max_le_max le_rfl ?_)
      calc ‖s - y‖ = ‖(s - c) - (y - c)‖ := by congr 1; ring
        _ ≤ ‖s - c‖ + ‖y - c‖ := norm_sub_le _ _
        _ = ‖s - c‖ + ρ := by rw [hy, abs_of_pos hρ]
    have hi3 : Integrable (fun y => Real.log (max r ‖s - y‖)) (circleUnif c ρ) :=
      KernelId.integrable_circleUnif_of_continuous
        ((continuous_const.max (continuous_const.sub continuous_id).norm).log
          fun y => (hr.trans_le (le_max_left _ _)).ne') c ρ
    calc _ ≤ ∫ _y, Real.log (max r (‖s - c‖ + ρ)) ∂circleUnif c ρ :=
          integral_mono_ae hi3 (integrable_const _) hb
      _ = _ := by simp
  have := abs_log_max_sub_log_max_le (x := ‖s - c‖ + ρ) (y := ‖s - c‖) hr
  rw [add_sub_cancel_left, abs_of_pos hρ] at this
  linarith [le_abs_self (Real.log (max r (‖s - c‖ + ρ)) - Real.log (max r ‖s - c‖))]

/-- **Smoothing-variance bound**: `|Var[X(η * fc_ρ) − X(η)]| ≤ B` whenever the smoothing
defects `∫ Lr ρ (·) x dη` lie in `[0, B]` for `x ∈ Hbar`. -/
theorem abs_kernelCov2_bind_le {η : Measure ℂ} [IsProbabilityMeasure η] (hη : IsAdmissibleH η)
    {ρ : ℝ} (hρ : 0 < ρ) (hηρ : IsAdmissibleH (η.bind fun w => foldedCircle w ρ)) {B : ℝ}
    (hB : ∀ x ∈ Hbar, 0 ≤ ∫ w, Lr ρ w x ∂η ∧ ∫ w, Lr ρ w x ∂η ≤ B) :
    |kernelCov2 neumannH (η.bind fun w => foldedCircle w ρ, η)
        (η.bind fun w => foldedCircle w ρ, η)| ≤ B := by
  set η' := η.bind fun w => foldedCircle w ρ with hη'
  have hη'P : IsProbabilityMeasure η' := ⟨by rw [hη', bind_circle_univ]; exact measure_univ⟩
  obtain ⟨Kη, hKη, hKηH, hηK⟩ := hη.2.1
  have hNr : ∀ x : ℂ, Integrable (fun w => Nr ρ w x) η := by
    intro x
    have hc : Continuous fun w => Nr ρ w x :=
      (continuous_Nr hρ).comp (continuous_id.prodMk continuous_const)
    have hi := hc.continuousOn.integrableOn_compact (μ := η) hKη
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hηK)] at hi
  have hℓm : AEStronglyMeasurable (fun x => ∫ w, Lr ρ w x ∂η) η' := by
    have := ((measurable_Lr hρ).comp measurable_swap).stronglyMeasurable.integral_prod_right'
      (ν := η)
    exact this.aestronglyMeasurable
  have hℓm' : AEStronglyMeasurable (fun x => ∫ w, Lr ρ w x ∂η) η := by
    have := ((measurable_Lr hρ).comp measurable_swap).stronglyMeasurable.integral_prod_right'
      (ν := η)
    exact this.aestronglyMeasurable
  -- the key identity, for an admissible probability `p`
  have key : ∀ p : Measure ℂ, IsProbabilityMeasure p → IsAdmissibleH p →
      AEStronglyMeasurable (fun x => ∫ w, Lr ρ w x ∂η) p →
      ∃ Λ, 0 ≤ Λ ∧ Λ ≤ B ∧ kernelCov neumannH p η' = kernelCov neumannH p η - Λ := by
    intro p hpP hp hℓp
    obtain ⟨Kp, hKp, hKpH, hpK⟩ := hp.2.1
    have i1 := (integrable_neumannH_prod hp hηρ).prod_right_ae
    have i2 := (integrable_neumannH_prod hp hη).prod_right_ae
    have hpt : ∀ᵐ x ∂p, ∫ y, neumannH x y ∂η' = ∫ y, neumannH x y ∂η - ∫ w, Lr ρ w x ∂η ∧
        x ∈ Hbar := by
      filter_upwards [i1, i2, ae_iff.2 hpK] with x h1 h2 hx
      refine ⟨?_, hKpH hx⟩
      rw [integral_bind_neumannH hρ x h1]
      have hLr : Integrable (fun w => Lr ρ w x) η := by
        have : (fun w => Lr ρ w x) = fun w => neumannH x w - Nr ρ w x := by
          funext w; unfold Lr; rw [neumannH_symm]
        rw [this]; exact h2.sub (hNr x)
      rw [← integral_sub h2 hLr]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      simp only [Lr, neumannH_symm w x]; ring
    have hℓi : Integrable (fun x => ∫ w, Lr ρ w x ∂η) p := by
      refine Integrable.of_bound hℓp B ?_
      filter_upwards [hpt] with x hx
      obtain ⟨b0, b1⟩ := hB x hx.2
      rw [Real.norm_eq_abs, abs_of_nonneg b0]; exact b1
    have hF : Integrable (fun x => ∫ y, neumannH x y ∂η) p :=
      (integrable_neumannH_prod hp hη).integral_prod_left
    refine ⟨∫ x, ∫ w, Lr ρ w x ∂η ∂p, ?_, ?_, ?_⟩
    · exact integral_nonneg_of_ae (by filter_upwards [hpt] with x hx using (hB x hx.2).1)
    · calc _ ≤ ∫ _x, B ∂p := integral_mono_ae hℓi (integrable_const _)
            (by filter_upwards [hpt] with x hx using (hB x hx.2).2)
        _ = B := by simp
    · unfold kernelCov
      rw [← integral_sub hF hℓi]
      exact integral_congr_ae (by filter_upwards [hpt] with x hx using hx.1)
  obtain ⟨Λ1, h10, h11, h1⟩ := key η' hη'P hηρ hℓm
  obtain ⟨Λ2, h20, h21, h2⟩ := key η inferInstance hη hℓm'
  unfold kernelCov2
  simp only
  rw [h1, h2]
  have e : kernelCov neumannH η' η - Λ1 - kernelCov neumannH η' η -
      (kernelCov neumannH η η - Λ2) + kernelCov neumannH η η = Λ2 - Λ1 := by ring
  rw [e, abs_le]
  constructor <;> linarith

/-! ### The Frostman-type bound for pushed-forward semicircles -/

namespace Data

variable {ψ : ℂ → ℂ} {a b δ m C : ℝ}

set_option maxHeartbeats 800000 in
theorem integral_Lr_pc_bounds (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ r0 δ m C) {s r : ℝ} (hr : 0 < r) (hsr : |s - t| + r ≤ R) {ρ : ℝ}
    (hρ : 0 < ρ) {x : ℂ} (hx : x ∈ Hbar) :
    0 ≤ ∫ w, Lr ρ w x ∂(pc ψ s r) ∧ ∫ w, Lr ρ w x ∂(pc ψ s r) ≤ 16 * ρ / (m * r) := by
  have hRδ : R ≤ δ := hR.trans r0_le_δ
  have hm := h.mpos
  have hgm : Measurable fun w => Lr ρ w x :=
    (measurable_Lr hρ).comp (measurable_id.prodMk measurable_const)
  rw [h.integral_pc ht hRδ hr hsr hgm]
  set K' : Set ℂ := closedBall (s : ℂ) r ∩ Hbar
  have hK' : IsCompact K' := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hsK : (s : ℂ) ∈ K' := ⟨mem_closedBall_self hr.le, show (0 : ℝ) ≤ (s : ℂ).im by simp⟩
  have hK'B : K' ⊆ closedBall (t : ℂ) R := by
    intro z hz
    have hz1 : ‖z - s‖ ≤ r := by rw [← dist_eq_norm]; exact hz.1
    rw [mem_closedBall, dist_eq_norm]
    calc ‖z - t‖ = ‖(z - s) + ((s : ℂ) - t)‖ := by congr 1; ring
      _ ≤ ‖z - s‖ + ‖(s : ℂ) - t‖ := norm_add_le _ _
      _ ≤ r + |s - t| := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; linarith
      _ ≤ R := by linarith
  have hcont : ContinuousOn (fun z => ‖ψ z - x‖) K' :=
    ((h.continuousOn_closedBall ht hRδ).mono hK'B).sub continuousOn_const |>.norm
  obtain ⟨z, hzK, hzmin⟩ := hK'.exists_isMinOn ⟨_, hsK⟩ hcont
  set ρ' := ρ / (m / 4) with hρ'
  have hρ'0 : 0 < ρ' := div_pos hρ (by linarith)
  have hbd : ∀ᵐ v ∂circleUnif (s : ℂ) r, 0 ≤ Lr ρ (ψ (foldH v)) x ∧
      Lr ρ (ψ (foldH v)) x ≤ 2 * (ell ρ' ‖v - z‖ + ell ρ' ‖v - conj z‖) := by
    filter_upwards [ae_norm_circleUnif s hr, ae_ne_circleUnif (s : ℂ) hr.ne' z,
      ae_ne_circleUnif (s : ℂ) hr.ne' (conj z)] with v hv h1 h2
    have hfv : foldH v ∈ K' := by
      refine ⟨?_, SmoothConv.foldH_mem_Hbar_sc v⟩
      rw [mem_closedBall, dist_eq_norm, norm_foldH_sub_ofReal, hv]
    have hfvB := hK'B hfv
    have hwH : ψ (foldH v) ∈ Hbar := h.im_nonneg ht hR0 hR hfvB hfv.2
    have hfz : foldH v ≠ z := by
      intro e
      unfold foldH at e
      split_ifs at e
      · exact h1 e
      · exact h2 (by rw [← e, Complex.conj_conj])
    have hdz : 0 < ‖foldH v - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hfz)
    have hlip : m / 2 * ‖foldH v - z‖ ≤ ‖ψ (foldH v) - ψ z‖ := by
      rw [h.sub_eq ht (h.closedBall_sub t hRδ hfvB) (h.closedBall_sub t hRδ (hK'B hzK)),
        norm_mul]
      have := h.norm_dq_ge ht hR0 hR hfvB (hK'B hzK)
      nlinarith [norm_nonneg (foldH v - z)]
    have hmin : ‖ψ z - x‖ ≤ ‖ψ (foldH v) - x‖ := isMinOn_iff.1 hzmin _ hfv
    have htri : ‖ψ (foldH v) - ψ z‖ ≤ 2 * ‖ψ (foldH v) - x‖ := by
      calc ‖ψ (foldH v) - ψ z‖ = ‖(ψ (foldH v) - x) - (ψ z - x)‖ := by congr 1; ring
        _ ≤ ‖ψ (foldH v) - x‖ + ‖ψ z - x‖ := norm_sub_le _ _
        _ ≤ 2 * ‖ψ (foldH v) - x‖ := by linarith
    have hlow : m / 4 * ‖foldH v - z‖ ≤ ‖ψ (foldH v) - x‖ := by linarith
    have hm4 : 0 < m / 4 * ‖foldH v - z‖ := mul_pos (by linarith) hdz
    have hd : 0 < ‖ψ (foldH v) - x‖ := lt_of_lt_of_le hm4 hlow
    obtain ⟨b0, b1⟩ := Lr_bounds (ρ := ρ) hwH hx hd
    refine ⟨b0, b1.trans ?_⟩
    have e1 : ell ρ ‖ψ (foldH v) - x‖ ≤ ell ρ' ‖foldH v - z‖ := by
      rw [hρ', ← ell_mul (by linarith) hdz]
      exact ell_anti hm4 hlow
    have hv1 : 0 < ‖v - z‖ := norm_pos_iff.2 (sub_ne_zero.2 h1)
    have hv2 : 0 < ‖v - conj z‖ := norm_pos_iff.2 (sub_ne_zero.2 h2)
    have e2 : ell ρ' ‖foldH v - z‖ ≤ ell ρ' ‖v - z‖ + ell ρ' ‖v - conj z‖ := by
      unfold foldH
      split_ifs
      · linarith [ell_nonneg (ρ := ρ') hv2]
      · have : ‖conj v - z‖ = ‖v - conj z‖ := by
          rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
        rw [this]; linarith [ell_nonneg (ρ := ρ') hv1]
    linarith
  obtain ⟨i1, j1⟩ := integral_ell_circle_le (s : ℂ) z hr hρ'0
  obtain ⟨i2, j2⟩ := integral_ell_circle_le (s : ℂ) (conj z) hr hρ'0
  refine ⟨integral_nonneg_of_ae (hbd.mono fun v hv => hv.1), ?_⟩
  calc ∫ v, Lr ρ (ψ (foldH v)) x ∂circleUnif (s : ℂ) r
      ≤ ∫ v, 2 * (ell ρ' ‖v - z‖ + ell ρ' ‖v - conj z‖) ∂circleUnif (s : ℂ) r :=
        integral_mono_of_nonneg (hbd.mono fun v hv => hv.1) ((i1.add i2).const_mul 2)
          (hbd.mono fun v hv => hv.2)
    _ = 2 * (∫ v, ell ρ' ‖v - z‖ ∂circleUnif (s : ℂ) r +
          ∫ v, ell ρ' ‖v - conj z‖ ∂circleUnif (s : ℂ) r) := by
        rw [integral_const_mul, integral_add i1 i2]
    _ ≤ 2 * (ρ' / r + ρ' / r) := by linarith
    _ = 16 * ρ / (m * r) := by rw [hρ']; field_simp; ring

theorem isAdmissibleH_pc_bind (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ r0 δ m C) {s r : ℝ} (hr : 0 < r) (hsr : |s - t| + r ≤ R) {ρ : ℝ}
    (hρ : 0 < ρ) : IsAdmissibleH ((pc ψ s r).bind fun w => foldedCircle w ρ) := by
  have hadm := h.isAdmissibleH_pc ht hR0 hR hr hsr
  obtain ⟨K, hK, -, hKc⟩ := hadm.2.1
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  have := isFiniteMeasure_bind_circle (r := ρ) (pc ψ s r)
  refine admissible_of_bounds (R := R₀ + ρ) (bind_circle_support (pc ψ s r) hρ.le hKc hR₀ le_rfl)
    (C := (pc ψ s r) univ * (2 * ENNReal.ofReal (potConst ρ))) ?_
    (bind_circle_pot (pc ψ s r) (fun z y => foldedCircle_pot_le hρ z y))
  rw [measure_univ, one_mul]
  exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top

/-- **Regularization at pushed-forward semicircles** (M4-T4 step 1): almost surely the
regularized evaluation of the free field at `ψ_* fc(s, r)` is its raw coordinate. -/
theorem ae_evalReg_pc {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ r0 δ m C) {s r : ℝ} (hr : 0 < r) (hsr : |s - t| + r ≤ R) :
    ∀ᵐ ω ∂P, evalReg (X ω) (pc ψ s r) = X ω (pc ψ s r) := by
  set μ := pc ψ s r
  have hadm : IsAdmissibleH μ := h.isAdmissibleH_pc ht hR0 hR hr hsr
  obtain ⟨K, hK, hKH, hKc⟩ := hadm.2.1
  have h1 : ∀ᵐ ω ∂P, ∀ k, ∫ z, avgReg (X ω) k z ∂μ =
      X ω (μ.bind fun w => foldedCircle w (radius k)) :=
    ae_all_iff.2 fun k => Regularization.ae_integral_avgReg_eq hX k μ hK hKH hKc
  set D : ℕ → Ω → ℝ := fun k ω => X ω (μ.bind fun w => foldedCircle w (radius k)) - X ω μ
  have hadmk : ∀ k, IsAdmissibleH (μ.bind fun w => foldedCircle w (radius k)) := fun k =>
    h.isAdmissibleH_pc_bind ht hR0 hR hr hsr (radius_pos k)
  have hmass : ∀ k, (μ.bind fun w => foldedCircle w (radius k)) univ = μ univ := fun k =>
    bind_circle_univ μ
  have hmom := fun k => integral_sq_pair_eq hX (hadmk k) hadm (hmass k)
  have hvar : ∀ k, ∫ ω, D k ω ^ 2 ∂P ≤ 16 / (m * r) * (1 / 2 : ℝ) ^ k := by
    intro k
    rw [(hmom k).2]
    refine (le_abs_self _).trans ((abs_kernelCov2_bind_le hadm (radius_pos k) (hadmk k)
      (fun x hx => h.integral_Lr_pc_bounds ht hR0 hR hr hsr (radius_pos k) hx)).trans
      (le_of_eq ?_))
    unfold radius; field_simp
  have hsum : Summable fun k => ∫ ω, D k ω ^ 2 ∂P := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => sq_nonneg _) hvar ?_
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h2 := ae_tendsto_zero_of_summable_sq
    (fun k => ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable)
    (fun k => (hmom k).1) hsum
  filter_upwards [h1, h2] with ω h1 h2
  unfold evalReg
  simp only [h1]
  have h3 : Tendsto (fun k => X ω (μ.bind fun w => foldedCircle w (radius k))) atTop
      (𝓝 (X ω μ)) := by
    have := h2.add_const (X ω μ)
    rw [zero_add] at this
    refine this.congr fun k => ?_
    show D k ω + X ω μ = _
    simp only [D]; ring
  exact h3.limUnder_eq

end Data

end CoordChange
end QuantumZipper
