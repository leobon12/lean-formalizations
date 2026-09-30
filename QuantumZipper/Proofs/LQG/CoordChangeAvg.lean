import QuantumZipper.Proofs.LQG.CoordChangeSmooth
import QuantumZipper.Proofs.LQG.RegularSample

/-!
# M4-T4, step 1 (continued): the regularized averages of the transformed field

For `y = coordChange (X ω) ψ Q` and a real point `t` of the inner interval, the dyadic
regularization `avgReg y k t` is, almost surely,

  `X ω (ψ_* fc(t, 2^{-k})) + Q ∫ log |ψ'| d fc(t, 2^{-k})`

(`ae_avgReg_coordChange`). The proof combines the regularization at pushed-forward semicircles
(`ae_evalReg_pc`), the increment bound `abs_kernelCov2_pc_pc_le` with Borel–Cantelli along the
dyadic approximations of `t`, and the Lipschitz continuity of the `log |ψ'|` term.
`measurable_avgReg_coordChange` gives joint measurability in `(t, ω)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace CoordChange

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `log |ψ'|` term of `coordChange` at the semicircle `fc(s, r)`. -/
def cc (ψ : ℂ → ℂ) (s r : ℝ) : ℝ := ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle (s : ℂ) r

theorem coordChange_fc (x : FieldSample) (ψ : ℂ → ℂ) (Q s r : ℝ) :
    coordChange x ψ Q (foldedCircle (s : ℂ) r) = evalReg x (pc ψ s r) + Q * cc ψ s r := rfl

theorem dyadicRoundC_ofReal (n : ℕ) (t : ℝ) : dyadicRoundC n (t : ℂ) = (dyadicRound n t : ℂ) := by
  apply Complex.ext
  · show dyadicRound n (t : ℂ).re = ((dyadicRound n t : ℝ) : ℂ).re
    rw [Complex.ofReal_re, Complex.ofReal_re]
  · show dyadicRound n (t : ℂ).im = ((dyadicRound n t : ℝ) : ℂ).im
    rw [Complex.ofReal_im, Complex.ofReal_im]
    simp [dyadicRound]

theorem measurable_dyadicRound' (n : ℕ) : Measurable (dyadicRound n) := by
  unfold dyadicRound
  exact ((measurable_from_top : Measurable (Int.cast : ℤ → ℝ)).div_const ((2 : ℝ) ^ n)).comp
    (Measurable.floor (measurable_id.const_mul ((2 : ℝ) ^ n)))

theorem countable_range_dyadicRound (n : ℕ) : (range (dyadicRound n)).Countable := by
  have hsub : range (dyadicRound n) ⊆ range (fun m : ℤ => (m : ℝ) / (2 : ℝ) ^ n) := by
    rintro _ ⟨x, rfl⟩; exact ⟨⌊(2 : ℝ) ^ n * x⌋, rfl⟩
  exact (countable_range _).mono hsub

/-- A function of `(t, ω)` that reads `t` only through `dyadicRound n` is jointly measurable. -/
theorem measurable_comp_dyadicRound {G : ℝ → Ω → ℝ} (hG : ∀ d, Measurable (G d)) (n : ℕ) :
    Measurable (fun p : ℝ × Ω => G (dyadicRound n p.1) p.2) := by
  have : Countable (range (dyadicRound n)) := (countable_range_dyadicRound n).to_subtype
  intro T hT
  have key : (fun p : ℝ × Ω => G (dyadicRound n p.1) p.2) ⁻¹' T
      = ⋃ d : range (dyadicRound n), (dyadicRound n ⁻¹' {(d : ℝ)}) ×ˢ (G d ⁻¹' T) := by
    ext ⟨t, ω⟩
    simp only [mem_preimage, mem_iUnion, mem_prod, mem_singleton_iff]
    constructor
    · intro hmem; exact ⟨⟨dyadicRound n t, mem_range_self t⟩, rfl, hmem⟩
    · rintro ⟨d, hd, hmem⟩; rw [hd]; exact hmem
  rw [key]
  exact MeasurableSet.iUnion fun d =>
    ((measurable_dyadicRound' n) (measurableSet_singleton _)).prod (hG d hT)

theorem measurable_fieldSample {P : Measure Ω} {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    Measurable X :=
  measurable_pi_iff.2 hX.measurable_coord

/-- Joint measurability of the regularized averages of the transformed field. -/
theorem measurable_avgReg_coordChange {P : Measure Ω} {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (ψ : ℂ → ℂ) (Q : ℝ) (k : ℕ) :
    Measurable (fun p : ℝ × Ω => avgReg (coordChange (X p.2) ψ Q) k (p.1 : ℂ)) := by
  have hn : ∀ n, Measurable (fun p : ℝ × Ω =>
      coordChange (X p.2) ψ Q (foldedCircle (dyadicRoundC n (p.1 : ℂ)) (radius k))) := by
    intro n
    simp_rw [dyadicRoundC_ofReal]
    refine measurable_comp_dyadicRound (G := fun d ω =>
      coordChange (X ω) ψ Q (foldedCircle (d : ℂ) (radius k))) (fun d => ?_) n
    exact (measurable_coordChange_apply ψ Q _).comp (measurable_fieldSample hX)
  unfold avgReg
  exact (StronglyMeasurable.limUnder (fun n => (hn n).stronglyMeasurable)).measurable

namespace Data

variable {ψ : ℂ → ℂ} {a b δ m C : ℝ}

theorem norm_deriv_ge (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : R ≤ r0 δ m C) {z : ℂ} (hz : z ∈ closedBall (t : ℂ) R) : m / 2 ≤ ‖deriv ψ z‖ := by
  have := h.norm_dq_ge ht hR0 hR hz hz
  rwa [dq_self] at this

theorem abs_log_norm_deriv_sub_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ r0 δ m C) {p q : ℂ} (hp : p ∈ closedBall (t : ℂ) R)
    (hq : q ∈ closedBall (t : ℂ) R) :
    |Real.log ‖deriv ψ p‖ - Real.log ‖deriv ψ q‖| ≤ 4 * C / m * ‖p - q‖ := by
  have hm2 : 0 < m / 2 := by linarith [h.mpos]
  have hRδ := hR.trans r0_le_δ
  refine (abs_log_sub_log_le hm2 (h.norm_deriv_ge ht hR0 hR hp)
    (h.norm_deriv_ge ht hR0 hR hq)).trans ?_
  have h2 := (abs_norm_sub_norm_le (deriv ψ p) (deriv ψ q)).trans (le_of_eq_of_le
    (by rw [dq_self, dq_self]) (h.dq_lip ht (h.closedBall_sub t hRδ hp)
      (h.closedBall_sub t hRδ hp) (h.closedBall_sub t hRδ hq) (h.closedBall_sub t hRδ hq)))
  calc |‖deriv ψ p‖ - ‖deriv ψ q‖| / (m / 2) ≤ C * (‖p - q‖ + ‖p - q‖) / (m / 2) :=
        div_le_div_of_nonneg_right h2 hm2.le
    _ = 4 * C / m * ‖p - q‖ := by field_simp; ring

theorem continuousOn_log_norm_deriv (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ r0 δ m C) :
    ContinuousOn (fun z => Real.log ‖deriv ψ z‖) (closedBall (t : ℂ) R) := by
  have hRδ := hR.trans r0_le_δ
  have hc : ContinuousOn (deriv ψ) (closedBall (t : ℂ) R) :=
    ((h.diff t ht).deriv isOpen_ball).continuousOn.mono (h.closedBall_sub t hRδ)
  refine hc.norm.log fun z hz => ?_
  have := h.norm_deriv_ge ht hR0 hR hz
  have := h.mpos
  exact (show 0 < ‖deriv ψ z‖ by linarith).ne'

/-- Lipschitz continuity of the `log |ψ'|` term in the centre. -/
theorem abs_cc_sub_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ} (hr : 0 < r)
    (hr0 : 2 * r ≤ r0 δ m C) {s s' : ℝ} (hs : |s - t| ≤ r) (hs' : |s' - t| ≤ r) :
    |cc ψ s r - cc ψ s' r| ≤ 4 * C / m * |s - s'| := by
  have hR0 : (0 : ℝ) ≤ 2 * r := by positivity
  set g : ℂ → ℝ := fun z => Real.log ‖deriv ψ z‖
  have hgc := h.continuousOn_log_norm_deriv ht hR0 hr0
  set B := closedBall (t : ℂ) (2 * r)
  have hsr : |s - t| + r ≤ 2 * r := by linarith
  have hs'r : |s' - t| + r ≤ 2 * r := by linarith
  -- rewrite both as integrals over `circleUnif 0 r`
  have hrep : ∀ s'' : ℝ, |s'' - t| + r ≤ 2 * r →
      Integrable (fun u => g (foldH ((s'' : ℂ) + u))) (circleUnif 0 r) ∧
      cc ψ s'' r = ∫ u, g (foldH ((s'' : ℂ) + u)) ∂circleUnif 0 r := by
    intro s'' hs''
    have hae : ∀ᵐ u ∂circleUnif (0 : ℂ) r, foldH ((s'' : ℂ) + u) ∈ B := by
      filter_upwards [SmoothConv.ae_circleUnif_sc 0 r] with u hu
      refine foldH_mem_closedBall_real (mem_closedBall_of_circle ?_ hs'')
      rw [add_sub_cancel_left]; simpa [abs_of_pos hr] using hu
    have hcomp : ContinuousOn (fun u => g (foldH ((s'' : ℂ) + u)))
        ((fun u => foldH ((s'' : ℂ) + u)) ⁻¹' B) :=
      hgc.comp (CircleFubini.continuous_foldH'.comp (continuous_const.add continuous_id)).continuousOn
        (fun u hu => hu)
    have hmeasB : MeasurableSet ((fun u => foldH ((s'' : ℂ) + u)) ⁻¹' B) :=
      (CircleFubini.continuous_foldH'.comp (continuous_const.add continuous_id)).measurable
        measurableSet_closedBall
    have hsm : AEStronglyMeasurable (fun u => g (foldH ((s'' : ℂ) + u))) (circleUnif 0 r) := by
      have := hcomp.aestronglyMeasurable (μ := circleUnif (0 : ℂ) r) hmeasB
      have hae' : ∀ᵐ u ∂circleUnif (0 : ℂ) r, u ∈ (fun u => foldH ((s'' : ℂ) + u)) ⁻¹' B := hae
      rwa [Measure.restrict_eq_self_of_ae_mem hae'] at this
    obtain ⟨M, hM⟩ := (isCompact_closedBall (t : ℂ) (2 * r)).exists_bound_of_continuousOn hgc
    have hint : Integrable (fun u => g (foldH ((s'' : ℂ) + u))) (circleUnif 0 r) :=
      Integrable.of_bound hsm M (hae.mono fun u hu => hM _ hu)
    refine ⟨hint, ?_⟩
    unfold cc foldedCircle
    rw [circleUnif_ofReal_eq_map s'' r, Measure.map_map measurable_foldH (measurable_const_add _)]
    refine integral_map ((measurable_foldH.comp (measurable_const_add _)).aemeasurable) ?_
    rw [← Measure.map_map measurable_foldH (measurable_const_add _), ← circleUnif_ofReal_eq_map]
    have hae' : ∀ᵐ z ∂(circleUnif (s'' : ℂ) r).map foldH, z ∈ B :=
      (ae_mem_foldedCircle hr hs'').mono fun z hz => hz.1
    have := hgc.aestronglyMeasurable (μ := (circleUnif (s'' : ℂ) r).map foldH)
      measurableSet_closedBall
    rwa [Measure.restrict_eq_self_of_ae_mem hae'] at this
  obtain ⟨i1, e1⟩ := hrep s hsr
  obtain ⟨i2, e2⟩ := hrep s' hs'r
  rw [e1, e2, ← integral_sub i1 i2]
  have hb : ∀ᵐ u ∂circleUnif (0 : ℂ) r,
      ‖g (foldH ((s : ℂ) + u)) - g (foldH ((s' : ℂ) + u))‖ ≤ 4 * C / m * |s - s'| := by
    filter_upwards [SmoothConv.ae_circleUnif_sc 0 r] with u hu
    have hu' : ‖u‖ = r := by simpa [abs_of_pos hr] using hu
    have hp : foldH ((s : ℂ) + u) ∈ B :=
      foldH_mem_closedBall_real (mem_closedBall_of_circle (by rw [add_sub_cancel_left]; exact hu') hsr)
    have hq : foldH ((s' : ℂ) + u) ∈ B :=
      foldH_mem_closedBall_real (mem_closedBall_of_circle (by rw [add_sub_cancel_left]; exact hu') hs'r)
    rw [Real.norm_eq_abs]
    refine (h.abs_log_norm_deriv_sub_le ht hR0 hr0 hp hq).trans ?_
    refine mul_le_mul_of_nonneg_left ((RegSample.norm_foldH_sub_le _ _).trans (le_of_eq ?_))
      (div_nonneg (by linarith [h.C_nonneg ht]) h.mpos.le)
    rw [show (s : ℂ) + u - ((s' : ℂ) + u) = ((s - s' : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const hb
  simpa [Real.norm_eq_abs] using this

/-- **Identification of the regularized averages** of `coordChange (X ω) ψ Q` at a fixed real
point. -/
theorem ae_avgReg_coordChange {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) (Q : ℝ)
    {k : ℕ} (hk : 2 * radius k ≤ r0 δ m C) :
    ∀ᵐ ω ∂P, avgReg (coordChange (X ω) ψ Q) k (t : ℂ) =
      X ω (pc ψ t (radius k)) + Q * cc ψ t (radius k) := by
  set r := radius k with hrdef
  have hr : 0 < r := radius_pos k
  have hR0 : (0 : ℝ) ≤ 2 * r := by positivity
  have hdt : ∀ n, |dyadicRound n t - t| ≤ 1 / 2 ^ n := fun n => CircleCont.abs_dyadicRound_sub_le n t
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, (1 / 2 : ℝ) ^ n₀ < r :=
    exists_pow_lt_of_lt_one hr (by norm_num)
  have hdn : ∀ n, |dyadicRound (n + n₀) t - t| ≤ r := by
    intro n
    refine (hdt _).trans ?_
    have : (1 : ℝ) / 2 ^ (n + n₀) ≤ (1 / 2) ^ n₀ := by
      rw [← one_div_pow]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hdnR : ∀ n, |dyadicRound (n + n₀) t - t| + r ≤ 2 * r := fun n => by linarith [hdn n]
  have htr : |t - t| + r ≤ 2 * r := by simp; linarith
  -- (A1) regularization at the approximating semicircles
  have hA1 : ∀ᵐ ω ∂P, ∀ n, evalReg (X ω) (pc ψ (dyadicRound (n + n₀) t) r) = X ω (pc ψ (dyadicRound (n + n₀) t) r) :=
    ae_all_iff.2 fun n => h.ae_evalReg_pc hX ht hR0 hk hr (hdnR n)
  -- (A2) convergence of the Gaussian coordinates
  have hadm : ∀ s : ℝ, |s - t| + r ≤ 2 * r → IsAdmissibleH (pc ψ s r) := fun s hs =>
    h.isAdmissibleH_pc ht hR0 hk hr hs
  have hmass : ∀ s s' : ℝ, (pc ψ s r) univ = (pc ψ s' r) univ := fun s s' => by simp
  have hmom := fun n => integral_sq_pair_eq hX (hadm _ (hdnR n)) (hadm t htr) (hmass (dyadicRound (n + n₀) t) t)
  set K := 8 * C / m + 4 / r
  have hK : 0 ≤ K := by
    have := h.C_nonneg ht; have := h.mpos; positivity
  have hvar : ∀ n, ∫ ω, (X ω (pc ψ (dyadicRound (n + n₀) t) r) - X ω (pc ψ t r)) ^ 2 ∂P ≤
      K * (1 / 2 : ℝ) ^ (n + n₀) := by
    intro n
    rw [(hmom n).2]
    refine (le_abs_self _).trans ((h.abs_kernelCov2_pc_pc_le ht hr hk (hdn n)
      (by simp; exact hr.le)).trans ?_)
    refine mul_le_mul_of_nonneg_left ((hdt _).trans (le_of_eq ?_)) hK
    rw [one_div_pow]
  have hsum : Summable fun n => ∫ ω, (X ω (pc ψ (dyadicRound (n + n₀) t) r) - X ω (pc ψ t r)) ^ 2 ∂P := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun ω => sq_nonneg _) hvar ?_
    refine ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (K * (1 / 2 : ℝ) ^ n₀)).congr fun n => ?_
    rw [pow_add]; ring
  have hA2 := ae_tendsto_zero_of_summable_sq
    (fun n => ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable)
    (fun n => (hmom n).1) hsum
  -- the deterministic term
  have hcc : Tendsto (fun n => cc ψ (dyadicRound (n + n₀) t) r) atTop (𝓝 (cc ψ t r)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hg : Tendsto (fun n : ℕ => 4 * C / m * (1 / 2 : ℝ) ^ (n + n₀)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).comp (tendsto_add_atTop_nat n₀)).const_mul (4 * C / m)
      rw [mul_zero] at this
      exact this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hg
    rw [Real.norm_eq_abs]
    refine (h.abs_cc_sub_le ht hr hk (hdn n) (by simp; exact hr.le)).trans ?_
    refine mul_le_mul_of_nonneg_left ((hdt _).trans (le_of_eq ?_))
      (div_nonneg (by linarith [h.C_nonneg ht]) h.mpos.le)
    rw [one_div_pow]
  filter_upwards [hA1, hA2] with ω h1 h2
  unfold avgReg
  refine Tendsto.limUnder_eq ?_
  rw [← tendsto_add_atTop_iff_nat n₀]
  have hlim : Tendsto (fun n => X ω (pc ψ (dyadicRound (n + n₀) t) r) + Q * cc ψ (dyadicRound (n + n₀) t) r) atTop
      (𝓝 (X ω (pc ψ t r) + Q * cc ψ t r)) := by
    have := (h2.add_const (X ω (pc ψ t r))).add (hcc.const_mul Q)
    rw [zero_add] at this
    refine this.congr fun n => ?_
    simp only [Pi.sub_apply]; ring
  refine hlim.congr fun n => ?_
  rw [dyadicRoundC_ofReal, coordChange_fc, h1 n]

end Data

end CoordChange
end QuantumZipper
