import QuantumZipper.Proofs.Zipper.E5Model2
import QuantumZipper.Proofs.GFF.CoordRegHarm
import QuantumZipper.Proofs.GFF.K3.HarmonicPart
import QuantumZipper.Proofs.GFF.K3.HalfDiscPoisson

/-!
# E5-MODEL, part 3: harmonicity of the collision correction near `0` (E5-LOC, `Setup.harm`)

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4 E5, step (1) ("`g` harmonic near `0`");
Sheffield, arXiv:1012.4797, §5.4. The D3⁺ `Setup` needs `g ω ∘ foldH` harmonic on `ball 0 r`.
For the explicit correction `locCorr = −(√κ/2) k_{ϖ_t} + const` of `E5Model2` this holds as soon
as `ϖ_t` gives no mass to `ball 0 r` (and has bounded support) and `k_{ϖ_t}` is continuous
(e.g. `TRegE4.continuous_kPot` for a Frostman `ϖ_t`):

* `meanValueOn_kPot`: the circle mean value property of `k_ϖ` on `ball 0 r` (Fubini, then the
  mean value property of `log |· − a|` for `a ∉` the disc: Jensen's formula for zero-free
  functions, `CoordReg.integral_log_norm_circleUnif_of_analytic`);
* `harmonicOnNhd_kPot`: Weyl's lemma in mean-value form (`K3.harmonicOnNhd_of_meanValue`);
* `kPot_foldH`: `k_ϖ ∘ foldH = k_ϖ` (reflection symmetry of the Neumann kernel);
* `harmonicOnNhd_locCorr_foldH`: the `Setup.harm` field for `locCorr`.

Standard potential theory (the log potential of a measure is harmonic off its support); own
elementary Lean route through the mean value property.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal ComplexConjugate

namespace QuantumZipper
namespace E5

open E1 B2

theorem abs_log_le_of_mem_Icc {d M x : ℝ} (hd : 0 < d) (hx1 : d ≤ x) (hx2 : x ≤ M) :
    |Real.log x| ≤ |Real.log d| + |Real.log M| := by
  have h1 : Real.log d ≤ Real.log x := Real.log_le_log hd hx1
  have h2 : Real.log x ≤ Real.log M := Real.log_le_log (hd.trans_le hx1) hx2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log d), abs_nonneg (Real.log M)]
  · linarith [le_abs_self (Real.log M), abs_nonneg (Real.log d)]

theorem measurable_uncurry_neumannH : Measurable (Function.uncurry neumannH) := by
  unfold Function.uncurry neumannH
  exact (Real.measurable_log.comp (measurable_fst.sub measurable_snd).norm).neg.sub
    (Real.measurable_log.comp
      (measurable_fst.sub (Complex.continuous_conj.measurable.comp measurable_snd)).norm)

/-- **Mean value property of the Neumann potential** off the support of `ϖ`. -/
theorem meanValueOn_kPot {ϖ : Measure ℂ} [IsFiniteMeasure ϖ] {r B : ℝ}
    (hB : ∀ᵐ v ∂ϖ, ‖v‖ ≤ B) (h0 : ∀ᵐ v ∂ϖ, r ≤ ‖v‖) :
    K3.MeanValueOn (PalmNorm.kPot ϖ) (ball (0 : ℂ) r) := by
  intro z _ s hs hsub
  obtain ⟨w₀, hw₀, hmax⟩ := (isCompact_closedBall z s).exists_isMaxOn
    (nonempty_closedBall.2 hs.le) continuous_norm.continuousOn
  have hm : ‖w₀‖ < r := by simpa using hsub hw₀
  have hwm : ∀ w ∈ closedBall z s, ‖w‖ ≤ ‖w₀‖ := fun w hw => hmax hw
  set d := r - ‖w₀‖ with hd_def
  have hd : 0 < d := by linarith
  have hlow : ∀ w ∈ closedBall z s, ∀ a : ℂ, r ≤ ‖a‖ → d ≤ ‖w - a‖ := by
    intro w hw a ha
    have := norm_sub_norm_le a w
    rw [norm_sub_rev] at this
    linarith [hwm w hw]
  have hup : ∀ w ∈ closedBall z s, ∀ a : ℂ, ‖a‖ ≤ B → ‖w - a‖ ≤ r + B := by
    intro w hw a ha
    linarith [norm_sub_le w a, hwm w hw]
  set M := 2 * (|Real.log d| + |Real.log (r + B)|)
  have hbound : ∀ w ∈ closedBall z s, ∀ v : ℂ, r ≤ ‖v‖ → ‖v‖ ≤ B → |neumannH w v| ≤ M := by
    intro w hw v hv1 hv2
    have hc1 : r ≤ ‖conj v‖ := by rwa [Complex.norm_conj]
    have hc2 : ‖conj v‖ ≤ B := by rwa [Complex.norm_conj]
    have e1 := abs_log_le_of_mem_Icc hd (hlow w hw v hv1) (hup w hw v hv2)
    have e2 := abs_log_le_of_mem_Icc hd (hlow w hw _ hc1) (hup w hw _ hc2)
    unfold neumannH
    calc |-Real.log ‖w - v‖ - Real.log ‖w - conj v‖|
        ≤ |Real.log ‖w - v‖| + |Real.log ‖w - conj v‖| := by
          rw [sub_eq_add_neg, ← neg_add]; rw [abs_neg]; exact abs_add_le _ _
      _ ≤ M := by linarith
  have hsetm : MeasurableSet {p : ℂ × ℂ | p.1 ∈ closedBall z s ∧ r ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ B} :=
    (measurable_fst isClosed_closedBall.measurableSet).inter
      ((measurableSet_le measurable_const measurable_snd.norm).inter
        (measurableSet_le measurable_snd.norm measurable_const))
  have hae : ∀ᵐ p ∂(circleUnif z s).prod ϖ,
      p.1 ∈ closedBall z s ∧ r ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ B := by
    rw [Measure.ae_prod_iff_ae_ae hsetm]
    filter_upwards [CoordReg.ae_mem_closedBall_circleUnif z hs.le] with w hw
    filter_upwards [h0, hB] with v hv1 hv2
    exact ⟨hw, hv1, hv2⟩
  have hint : Integrable (Function.uncurry neumannH) ((circleUnif z s).prod ϖ) :=
    Integrable.of_bound measurable_uncurry_neumannH.aestronglyMeasurable M
      (hae.mono fun p hp => by
        rw [Real.norm_eq_abs]
        exact hbound p.1 hp.1 p.2 hp.2.1 hp.2.2)
  unfold PalmNorm.kPot
  rw [integral_integral_swap hint]
  refine integral_congr_ae ?_
  filter_upwards [h0] with v hv
  have hne : ∀ a : ℂ, r ≤ ‖a‖ → ∀ u ∈ closedBall z s, u - a ≠ 0 := fun a ha u hu h => by
    have := hlow u hu a ha
    rw [h, norm_zero] at this
    linarith
  have hvc : r ≤ ‖conj v‖ := by rwa [Complex.norm_conj]
  have hmean : ∀ a : ℂ, r ≤ ‖a‖ →
      ∫ w, Real.log ‖w - a‖ ∂circleUnif z s = Real.log ‖z - a‖ := fun a ha =>
    CoordReg.integral_log_norm_circleUnif_of_analytic (F := fun u => u - a)
      (measurable_id.sub_const a) hs.le (analyticOnNhd_id.sub analyticOnNhd_const) (hne a ha)
  have hintl : ∀ a : ℂ, r ≤ ‖a‖ → Integrable (fun w => Real.log ‖w - a‖) (circleUnif z s) :=
    fun a ha => CoordReg.integrable_circleUnif_of_continuousOn
      (Real.measurable_log.comp (measurable_id.sub_const a).norm) hs.le
      (ContinuousOn.log (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
        fun u hu => norm_ne_zero_iff.2 (hne a ha u hu))
  simp only [neumannH]
  rw [integral_sub (f := fun w => -Real.log ‖w - v‖) (hintl v hv).neg (hintl _ hvc), integral_neg, hmean v hv, hmean _ hvc]

/-- **The Neumann potential is harmonic off the support of `ϖ`.** -/
theorem harmonicOnNhd_kPot {ϖ : Measure ℂ} [IsFiniteMeasure ϖ] {r B : ℝ}
    (hB : ∀ᵐ v ∂ϖ, ‖v‖ ≤ B) (h0 : ∀ᵐ v ∂ϖ, r ≤ ‖v‖) (hc : Continuous (PalmNorm.kPot ϖ)) :
    InnerProductSpace.HarmonicOnNhd (PalmNorm.kPot ϖ) (ball (0 : ℂ) r) :=
  K3.harmonicOnNhd_of_meanValue hc isOpen_ball (meanValueOn_kPot hB h0)

theorem kPot_foldH (ϖ : Measure ℂ) (z : ℂ) : PalmNorm.kPot ϖ (foldH z) = PalmNorm.kPot ϖ z := by
  unfold foldH
  split_ifs
  · rfl
  · simp only [PalmNorm.kPot, K3.neumannH_conj_left_k3]

/-- **`Setup.harm` for the collision correction**: `locCorr ∘ foldH` is harmonic on `ball 0 r`
when `ϖ_t` (finite, bounded support) gives no mass to `ball 0 r` and `k_{ϖ_t}` is continuous. -/
theorem harmonicOnNhd_locCorr_foldH (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ ρ₀ : Measure ℂ)
    (x : FieldSample) {r B : ℝ} [IsFiniteMeasure (varpiT V t ϖ)]
    (hB : ∀ᵐ v ∂(varpiT V t ϖ), ‖v‖ ≤ B) (h0 : ∀ᵐ v ∂(varpiT V t ϖ), r ≤ ‖v‖)
    (hc : Continuous (PalmNorm.kPot (varpiT V t ϖ))) :
    InnerProductSpace.HarmonicOnNhd (fun z => locCorr κ V t ϖ ρ₀ x (foldH z))
      (ball (0 : ℂ) r) := by
  intro z hz
  have h := ((harmonicOnNhd_kPot hB h0 hc) z hz).const_smul (c := -(Real.sqrt κ / 2))
  have h' := h.add (InnerProductSpace.harmonicAt_const (x ρ₀ - (ofFun (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
    (varpiT V t ϖ) 0) + x) (varpiT V t ϖ) - qt κ V t ϖ))
  convert h' using 1
  funext w
  simp only [locCorr, kPot_foldH, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end E5
end QuantumZipper
