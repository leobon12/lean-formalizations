/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R2Gauss

/-!
# The Cameron–Martin data of the corrected fibre (piece R2e, proved)

Packet PROVE-AUX61-R2. Astra's follow-up 4 L224–L227 ("Weight the conditional field law by the single strictly
positive full Cameron–Martin density for adding `f`"), specification §3.2 (the GFF pairing with a cutoff's source).
Every `RefFibre` whose clock is positive carries canonical `TiltData`: the field is a GFF with mean `u0 + q`
(`Aux61R2Gauss`), so its pairings with the approximations of the source of `−Fq` converge almost surely
(`CMCut.ae_tendsto_pair` for the centred field, dominated convergence for the mean, which is bounded on the source's
support: `u0` is bounded and `q` is bounded there by `q_bdd`), the limit `Λ` has `E e^{−Λ} < ∞` (Fatou over the
Gaussian moment generating functions, whose means and variances are bounded by those of the source), and
`k = 1/E e^{−Λ}` makes the tilt a probability measure.

* `integrable_exp_neg_of_isZBGFFProcess`: the Fatou bound for a GFF whose mean is bounded on the source's support (the
  general-mean version of `CMCut`'s `integrable_exp_neg_of_isGFF`);
* `RefFibre.centred`, `RefFibre.Λ`, `measurable_Λ`, **`ae_tendsto_Λ`**, **`integrable_exp_neg_Λ`**;
* **`RefFibre.tiltData`** (`k = (E e^{−Λ})⁻¹`), **`RefFibre.isProbabilityMeasure_tilt`** (the `tilt_prob` field of
  `TiltData.Clock`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61R2

open QuantumZipper (H greenH)
open LQGMetric (TestOn DistOn)
open Restart.FlowStopIdentCMI (CMCut)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

/-- **The density `e^{−Λ}` is integrable** for a GFF whose mean is bounded on the support of the source (Fatou:
`E[e^{−H₀(s_n)}] = e^{−μ_n + v_n/2}` with `|μ_n| ≤ C ∫ |v|` and `v_n = G_ℍ(s_n, s_n) ≤ ∬ |v| |v| |G_ℍ|`). -/
theorem integrable_exp_neg_of_isZBGFFProcess {S : Type*} [MeasurableSpace S] {Q₀ : Measure S}
    [IsProbabilityMeasure Q₀] {H₀ : S → DistOn upperHalfPlaneOpens} (hH₀ : Measurable H₀) {u₀ : ℂ → ℝ}
    (hY : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ x => H₀ x φ - ∫ z, u₀ z * φ z) Q₀) (F : CMCut)
    {C₀ : ℝ} (hC₀ : ∀ z, F.src z ≠ 0 → |u₀ z| ≤ C₀) {s : ℕ → TestOn upperHalfPlaneOpens}
    (hsle : ∀ n z, |s n z| ≤ |F.src z|) {Λ : S → ℝ} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ x ∂Q₀, Tendsto (fun n => H₀ x (s n)) atTop (𝓝 (Λ x))) :
    Integrable (fun x => Real.exp (-Λ x)) Q₀ := by
  set A : ℝ := |C₀| * ∫ z, |F.src z| with hA
  set B : ℝ := ∫ p : ℂ × ℂ, |(|F.src p.1| * |F.src p.2| * greenH p.1 p.2)| ∂((volume : Measure ℂ).prod volume)
    with hB
  have hbound : ∀ n, ∫⁻ x, ENNReal.ofReal (Real.exp (-H₀ x (s n))) ∂Q₀ ≤ ENNReal.ofReal (Real.exp (A + B / 2)) := by
    intro n
    have hm : Measurable fun x => H₀ x (s n) := (LQGMetric.measurable_distOn_apply (s n)).comp hH₀
    have hmap := Coupling.map_eval_eq_gaussianReal_of_isZBGFFProcess hY (s n)
    set μn : ℝ := ∫ z, u₀ z * s n z with hμn
    set vn : ℝ := QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens (s n) (s n) with hvn
    have hvn0 : 0 ≤ vn := LocalSets.zeroGFFTestCov_self_nonneg upperHalfPlaneOpens.isOpen subset_rfl (s n)
    have hlaw : HasLaw (fun x => H₀ x (s n)) (gaussianReal μn vn.toNNReal) Q₀ := ⟨hm.aemeasurable, hmap⟩
    have hint : Integrable (fun x => Real.exp (-H₀ x (s n))) Q₀ := by
      have h1 := integrable_exp_mul_gaussianReal (μ := μn) (v := vn.toNNReal) (-1)
      have h2 : Integrable (fun y : ℝ => Real.exp (-1 * y)) (Q₀.map fun x => H₀ x (s n)) := by rwa [hmap]
      have h3 := h2.comp_measurable hm
      refine h3.congr (ae_of_all _ fun x => ?_)
      simp
    have hmgf := mgf_gaussianReal hlaw (-1)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (Real.exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ∫ x, Real.exp (-H₀ x (s n)) ∂Q₀ = mgf (fun x => H₀ x (s n)) Q₀ (-1) := by
      simp only [mgf]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp
    rw [e, hmgf, Real.coe_toNNReal _ hvn0]
    refine Real.exp_le_exp.2 ?_
    -- the mean
    have hμ : -μn ≤ A := by
      have h1 : |μn| ≤ ∫ z, |C₀| * |F.src z| := by
        rw [hμn]
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _)
          (F.integrable_src.abs.const_mul _) (ae_of_all _ fun z => ?_))
        show |u₀ z * s n z| ≤ |C₀| * |F.src z|
        rw [abs_mul]
        by_cases hz : F.src z = 0
        · have h0 := hsle n z
          rw [hz, abs_zero] at h0
          rw [abs_nonpos_iff.1 h0, abs_zero, mul_zero, hz, abs_zero, mul_zero]
        · exact mul_le_mul ((hC₀ z hz).trans (le_abs_self _)) (hsle n z) (abs_nonneg _) (abs_nonneg _)
      rw [integral_const_mul] at h1
      linarith [neg_le_abs μn]
    -- the variance
    have hv : vn ≤ B := by
      have hvg : vn = LocalExt.greenEnergy (s n) (s n) := by
        rw [hvn, LQGMetric.zeroGFFTestCov_eq_green (V := upperHalfPlaneOpens) subset_rfl GFF.isConformalOnto_id_H]
        rfl
      rw [hvg]
      have hI := F.integrable_abs_mul_greenH.abs
      have hdom : ∀ p : ℂ × ℂ, |s n p.1 * s n p.2 * greenH p.1 p.2| ≤
          |(|F.src p.1| * |F.src p.2| * greenH p.1 p.2)| := fun p => by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_abs, abs_abs]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (hsle n p.1) (hsle n p.2) (abs_nonneg _)
          (abs_nonneg _)) (abs_nonneg _)
      have hmeas : Measurable fun p : ℂ × ℂ => s n p.1 * s n p.2 * greenH p.1 p.2 :=
        (((s n).continuous.measurable.comp measurable_fst).mul ((s n).continuous.measurable.comp measurable_snd)).mul
          QuantumZipper.measurable_greenH
      have hI2 : Integrable (fun p : ℂ × ℂ => |s n p.1 * s n p.2 * greenH p.1 p.2|)
          ((volume : Measure ℂ).prod volume) :=
        Integrable.mono' hI hmeas.abs.aestronglyMeasurable (ae_of_all _ fun p => by
          rw [Real.norm_eq_abs, abs_abs]; exact hdom p)
      calc LocalExt.greenEnergy (s n) (s n) ≤ |LocalExt.greenEnergy (s n) (s n)| := le_abs_self _
        _ ≤ ∫ p : ℂ × ℂ, |s n p.1 * s n p.2 * greenH p.1 p.2| ∂((volume : Measure ℂ).prod volume) :=
          abs_integral_le_integral_abs
        _ ≤ B := integral_mono_of_nonneg (ae_of_all _ fun p => abs_nonneg _) hI (ae_of_all _ hdom)
    nlinarith
  -- Fatou
  have hmeas : ∀ n, Measurable fun x => ENNReal.ofReal (Real.exp (-H₀ x (s n))) := fun n =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((LQGMetric.measurable_distOn_apply (s n)).comp hH₀).neg)
  have hlim : (fun x => ENNReal.ofReal (Real.exp (-Λ x))) =ᵐ[Q₀]
      fun x => liminf (fun n => ENNReal.ofReal (Real.exp (-H₀ x (s n)))) atTop := by
    filter_upwards [hΛ] with x hx
    have h := ((ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).tendsto _).comp hx
    exact h.liminf_eq.symm
  have hfat := lintegral_liminf_le hmeas (μ := Q₀) (u := atTop)
  have hle : ∫⁻ x, ENNReal.ofReal (Real.exp (-Λ x)) ∂Q₀ ≤ ENNReal.ofReal (Real.exp (A + B / 2)) := by
    rw [lintegral_congr_ae hlim]
    exact hfat.trans (Filter.liminf_le_of_le ⟨0, Eventually.of_forall fun n => bot_le⟩
      fun c hc => (hc.exists).elim fun n hn => hn.trans (hbound n))
  have hfin : ∫⁻ x, ENNReal.ofReal (Real.exp (-Λ x)) ∂Q₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have h := integrable_toReal_of_lintegral_ne_top
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hΛm.neg)).aemeasurable hfin
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Function.comp_apply]
  exact ENNReal.toReal_ofReal (Real.exp_pos _).le

namespace RefFibre

variable {S : Type u} [mS : MeasurableSpace S] (D : RefFibre S)

/-- The fibre's field centred by its time-0 mean `u0 + q`. -/
def centred (ω : S) : DistOn upperHalfPlaneOpens := D.field ω + -smoothDist upperHalfPlaneOpens D.mean0

theorem measurable_centred : Measurable D.centred :=
  (Coupling.measurable_add_distOnConst _).comp D.measurable_field

theorem centred_apply (ω : S) (φ : TestOn upperHalfPlaneOpens) :
    D.centred ω φ = D.field ω φ - ∫ z, D.mean0 z * φ z := by
  have e : smoothDist upperHalfPlaneOpens D.mean0 φ = ∫ z, D.mean0 z * φ z := by
    rw [SupercriticalConformalCovariance.GM24.smoothDist_apply D.continuousOn_mean0]
    exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  change D.field ω φ + -smoothDist upperHalfPlaneOpens D.mean0 φ = _
  rw [e, ← sub_eq_add_neg]

/-- A bound for the time-0 mean on the support of the source of `Fq`. -/
theorem exists_abs_mean0_le : ∃ C : ℝ, ∀ z, D.Fq.src z ≠ 0 → |D.mean0 z| ≤ C := by
  obtain ⟨Cu, hCu⟩ := D.u0_ext.2.1
  refine ⟨Cu + D.Cq, fun z hz => ?_⟩
  have hzH : z ∈ H := (D.Fq.mem_of_src_ne_zero hz).1
  exact (abs_add_le _ _).trans (add_le_add (hCu z hzH) (D.q_bdd z hz))

theorem exists_abs_mean0_le_neg : ∃ C : ℝ, ∀ z, D.Fq.neg.src z ≠ 0 → |D.mean0 z| ≤ C := by
  obtain ⟨C, hC⟩ := D.exists_abs_mean0_le
  exact ⟨C, fun z hz => hC z fun h0 => hz (by rw [CMCut.src_neg, h0, neg_zero])⟩

/-- **The pairing limit** of the field with the source of `−Fq`: the Borel pairing of the centred field plus the
paired mean. -/
def Λ (ω : S) : ℝ := D.Fq.neg.pair (D.centred ω) + ∫ z, D.mean0 z * D.Fq.neg.src z

theorem measurable_Λ : Measurable D.Λ :=
  (D.Fq.neg.measurable_pair.comp D.measurable_centred).add_const _

/-- The paired means converge (dominated convergence: the mean is bounded on the source's support). -/
theorem tendsto_integral_mean0_testSeq :
    Tendsto (fun n => ∫ z, D.mean0 z * D.Fq.neg.testSeq n z) atTop (𝓝 (∫ z, D.mean0 z * D.Fq.neg.src z)) := by
  obtain ⟨C, hC⟩ := D.exists_abs_mean0_le_neg
  set F := D.Fq.neg
  refine tendsto_integral_of_dominated_convergence (fun z => C * |F.src z|)
    (fun n => (LocalExt.integrable_mul_testOn D.continuousOn_mean0 (F.testSeq n)).aestronglyMeasurable)
    (F.integrable_src.abs.const_mul C) (fun n => ae_of_all _ fun z => ?_)
    (ae_of_all _ fun z => (F.tendsto_testSeq z).const_mul _)
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hz : F.src z = 0
  · have h0 := F.abs_testSeq_le n z
    rw [hz, abs_zero] at h0
    rw [abs_nonpos_iff.1 h0, hz, abs_zero, mul_zero, mul_zero]
  · exact mul_le_mul (hC z hz) (F.abs_testSeq_le n z) (abs_nonneg _) ((abs_nonneg _).trans (hC z hz))

variable {D}

/-- **The field's pairings with the source of `−Fq` converge almost surely to `Λ`** (the clock is positive). -/
theorem ae_tendsto_Λ (he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω) :
    ∀ᵐ ω ∂D.P, Tendsto (fun n => D.field ω (D.Fq.neg.testSeq n)) atTop (𝓝 (D.Λ ω)) := by
  let _ := D.prob
  have hY := D.isZBGFFProcess he0
  have hY' : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens
      (fun φ ω => D.centred ω φ - ∫ z, (fun _ : ℂ => (0 : ℝ)) z * φ z) D.P := by
    have e : (fun φ ω => D.centred ω φ - ∫ z, (fun _ : ℂ => (0 : ℝ)) z * φ z) =
        fun φ ω => D.field ω φ - ∫ z, D.mean0 z * φ z := by
      funext φ ω
      rw [D.centred_apply]
      simp
    rw [e]; exact hY
  have hpair := D.Fq.neg.ae_tendsto_pair (h := D.centred) (u₀ := fun _ => 0) continuousOn_const
    (C := 0) (fun _ _ => by simp) hY'
  filter_upwards [hpair] with ω hω
  have e : ∀ n, D.field ω (D.Fq.neg.testSeq n) =
      D.centred ω (D.Fq.neg.testSeq n) + ∫ z, D.mean0 z * D.Fq.neg.testSeq n z := fun n => by
    rw [D.centred_apply]; ring
  simp_rw [e]
  exact hω.add D.tendsto_integral_mean0_testSeq

/-- **`e^{−Λ}` is integrable** (the clock is positive). -/
theorem integrable_exp_neg_Λ (he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω) : Integrable (fun ω => Real.exp (-D.Λ ω)) D.P := by
  let _ := D.prob
  obtain ⟨C, hC⟩ := D.exists_abs_mean0_le_neg
  exact integrable_exp_neg_of_isZBGFFProcess D.measurable_field (D.isZBGFFProcess he0) D.Fq.neg hC
    D.Fq.neg.abs_testSeq_le D.measurable_Λ (ae_tendsto_Λ he0)

/-- The expectation `E e^{−Λ}` is positive. -/
theorem integral_exp_neg_Λ_pos (he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω) : 0 < ∫ ω, Real.exp (-D.Λ ω) ∂D.P := by
  let _ := D.prob
  refine (integral_pos_iff_support_of_nonneg (fun ω => (Real.exp_pos _).le) (integrable_exp_neg_Λ he0)).2 ?_
  have hs : Function.support (fun ω => Real.exp (-D.Λ ω)) = univ :=
    eq_univ_of_forall fun ω => (Real.exp_pos _).ne'
  rw [hs, measure_univ]
  exact one_pos

/-- **The canonical Cameron–Martin data** of a fibre with positive clock: `Λ`, `k = (E e^{−Λ})⁻¹`. -/
def tiltData (he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω) : D.TiltData where
  Λ := D.Λ
  Λ_measurable := D.measurable_Λ
  pairing_limit := ae_tendsto_Λ he0
  integrable_exp := integrable_exp_neg_Λ he0
  k := (∫ ω, Real.exp (-D.Λ ω) ∂D.P)⁻¹
  k_pos := inv_pos.2 (integral_exp_neg_Λ_pos he0)

/-- **The canonical tilt is a probability measure** (the `tilt_prob` field of `TiltData.Clock`). -/
theorem isProbabilityMeasure_tilt (he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω) : IsProbabilityMeasure (tiltData he0).tilt := by
  let _ := D.prob
  constructor
  have hint := integrable_exp_neg_Λ he0
  have hpos := integral_exp_neg_Λ_pos he0
  change (D.P.withDensity fun ω => ENNReal.ofReal ((∫ ω, Real.exp (-D.Λ ω) ∂D.P)⁻¹ * Real.exp (-D.Λ ω))) univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
      (ae_of_all _ fun ω => mul_nonneg (inv_pos.2 hpos).le (Real.exp_pos _).le),
    integral_const_mul, inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]

end RefFibre

end InteractingSLE.Sec5.Aux61R2
