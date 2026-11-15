/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtKJoint

/-!
# Aux. lemma 55 with a random seed word: the Cameron–Martin density and the measure `Q`

Packet PROVE-LOCEXT-K (step 3 of `planning/handoffs/PROVE-LOCEXT-I.md`). In the random-word setting of
`LocalExtKJoint` (coupling clause for a filtration `𝓖`, a `𝓖₀`-measurable admissible word `c`, good paths of the
word `c ω`):

* `vSrcW`, `centreW`, `normW`: the source, the initial mean paired with the source and the Dirichlet energy, jointly
  measurable in the word (`srcCentre`, `srcNorm` on admissible words);
* `densW x T = exp(−((T, v_x) − (𝔥₀, v_x)) − ‖f_x‖²_∇/2)`: the density (HL3) of the word `x` as a Borel function of
  the word and the field; `Z ω = densW (c ω) (h ω)`;
* **`setLIntegral_densW`**: for a `𝓖`-stopping time `τ` before the local stop and `A ∈ 𝓖_τ`,
  `E[Z; A] = E[N_τ; A]`, `N_τ = srcMart` of the word `c ω` at `τ` (first line of (HL4) with random positions);
* `lintegral_densW`, `integrable_densW`: `E Z = 1`;
* **`wordMeasure`** `Q = Z · P`: a probability measure equivalent to `P`, `Q = N_τ · P` on `𝓖_τ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull greenH)
open LQGMetric (TestOn DistOn)

/-! ### The source data of a word -/

section WordData

variable {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ)

/-- The source of a word restricted to `ℍ` (`vSrc` for an admissible word, `0` otherwise). -/
def vSrcW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) : ℂ → ℝ := H.indicator (vDensW κ ρL ρR r x)

theorem vSrcW_of_adm {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) :
    vSrcW κ ρL ρR r x = vSrc κ x.1 x.2 ρL ρR r := by
  rw [vSrcW, vDensW_eq_of_adm κ ρL ρR r hx, vSrc]

theorem measurable_vSrcW :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => vSrcW κ ρL ρR r p.1 p.2 := by
  have hH : MeasurableSet {p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ | p.2 ∈ H} :=
    measurable_snd (measurableSet_lt measurable_const Complex.measurable_im)
  have e : (fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => vSrcW κ ρL ρR r p.1 p.2) =
      {p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ | p.2 ∈ H}.indicator
        fun p => vDensW κ ρL ρR r p.1 p.2 := by
    funext p
    by_cases hp : p.2 ∈ H
    · simp [vSrcW, hp]
    · simp [vSrcW, hp]
  rw [e]
  exact (measurable_vDensW κ ρL ρR r).indicator hH

/-- `(𝔥₀, v_x)` for a word. -/
def centreW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ := ∫ z, bheAt κ ρL ρR x.1 x.2 z * vSrcW κ ρL ρR r x z

/-- `‖f_x‖²_∇ = ∫ v_x f_x` for a word. -/
def normW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ := ∫ z, vSrcW κ ρL ρR r x z * fCut κ x.1 x.2 ρL ρR r z

theorem centreW_of_adm {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) :
    centreW κ ρL ρR r x = srcCentre κ x.1 x.2 ρL ρR r := by
  rw [centreW, srcCentre, vSrcW_of_adm κ ρL ρR r hx]

theorem normW_of_adm {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) :
    normW κ ρL ρR r x = srcNorm κ x.1 x.2 ρL ρR r := by
  rw [normW, srcNorm, vSrcW_of_adm κ ρL ρR r hx]

theorem measurable_centreW : Measurable (centreW (nL := nL) (nR := nR) κ ρL ρR r) := by
  have hj : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ =>
      bheAt κ ρL ρR p.1.1 p.1.2 p.2 * vSrcW κ ρL ρR r p.1 p.2 :=
    (measurable_bheAt_word κ ρL ρR).mul (measurable_vSrcW κ ρL ρR r)
  exact (hj.stronglyMeasurable.integral_prod_right (ν := (volume : Measure ℂ))).measurable

theorem measurable_normW : Measurable (normW (nL := nL) (nR := nR) κ ρL ρR r) := by
  have hj : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ =>
      vSrcW κ ρL ρR r p.1 p.2 * fCut κ p.1.1 p.1.2 ρL ρR r p.2 :=
    (measurable_vSrcW κ ρL ρR r).mul (measurable_fCut_word κ ρL ρR r)
  exact (hj.stronglyMeasurable.integral_prod_right (ν := (volume : Measure ℂ))).measurable

/-- **The Cameron–Martin density (HL3) of a word**, a Borel function of the word and the field:
`Z = exp(−((T, v_x) − (𝔥₀, v_x)) − ‖f_x‖²_∇/2)`. -/
def densW (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (T : DistOn upperHalfPlaneOpens) : ℝ :=
  Real.exp (-(srcPairW κ ρL ρR r x T - centreW κ ρL ρR r x) - normW κ ρL ρR r x / 2)

theorem densW_pos (x : (Fin nL → ℝ) × (Fin nR → ℝ)) (T : DistOn upperHalfPlaneOpens) :
    0 < densW κ ρL ρR r x T := Real.exp_pos _

theorem measurable_densW :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × DistOn upperHalfPlaneOpens =>
      densW κ ρL ρR r p.1 p.2 := by
  unfold densW
  exact Real.measurable_exp.comp (((measurable_srcPairW κ ρL ρR r).sub
    ((measurable_centreW κ ρL ρR r).comp measurable_fst)).neg.sub
    (((measurable_normW κ ρL ρR r).comp measurable_fst).div_const 2))

end WordData

/-! ### The density in the random-word setting -/

section Density

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)}

/-- The density martingale (HL4) of the random word at time `t`. -/
def martW (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  srcMart κ (c ω).1 (c ω).2 ρL ρR r W VL VR t ω

theorem martW_pos (t : ℝ≥0) (ω : Ω) : 0 < martW κ ρL ρR r W VL VR c t ω := Real.exp_pos _

/-- The shifted pairing `Y₂ = (h, v_c) − (𝔥₀, v_c) + ‖f_c‖²_∇/2`, with `e^{−Y₂} = Z`. -/
def shiftPairW (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ) (c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ))
    (h : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) : ℝ :=
  srcPairW κ ρL ρR r (c ω) (h ω) - centreW κ ρL ρR r (c ω) + normW κ ρL ρR r (c ω) / 2

theorem exp_neg_shiftPairW (ω : Ω) :
    Real.exp (-shiftPairW κ ρL ρR r c h ω) = densW κ ρL ρR r (c ω) (h ω) := by
  rw [shiftPairW, densW]
  congr 1
  ring

omit [IsProbabilityMeasure P] in
theorem measurable_shiftPairW (hhm : Measurable h) (hc : Measurable c) :
    Measurable (shiftPairW κ ρL ρR r c h) :=
  ((measurable_srcPairW_word hhm hc).sub ((measurable_centreW κ ρL ρR r).comp hc)).add
    (((measurable_normW κ ρL ρR r).comp hc).div_const 2)

variable (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h)
  (hhm : Measurable h) (hc : Measurable[𝓖 0] c) (hadm : ∀ ω, IsAdmWord r (c ω))
  (hgood : ∀ᵐ ω ∂P, IsWordPath κ ρL ρR W VL VR B ζ c ω)
include hcf hhm hc hadm hgood

/-- **The joint conditional law of `(h(φ), Y₂)`** (the shifted pairing). -/
theorem condExp_cexp_joint_shift {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) (φ : TestOn upperHalfPlaneOpens) (a b : ℝ) :
    ∀ᵐ ω ∂P, ω ∈ {ω | Disjoint (tsupport φ)
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))} →
      (P[fun ω' => Complex.exp (Complex.I * ((a * h ω' φ + b * shiftPairW κ ρL ρR r c h ω' : ℝ) : ℂ)) |
        hτ.measurableSpace]) ω =
        cfVal (a * (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
            (bheProc κ ρL ρR W VL VR ω ((τ ω).untopD 0)) z * φ z) +
            b * (srcMeanAt κ (c ω).1 (c ω).2 ρL ρR r W VL VR ((τ ω).untopD 0) ω - centreW κ ρL ρR r (c ω) +
              normW κ ρL ρR r (c ω) / 2))
          (a ^ 2 * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ +
            2 * a * b * greenCross (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ
              (vSrc κ (c ω).1 (c ω).2 ρL ρR r) +
            b ^ 2 * srcEnergyAt κ (c ω).1 (c ω).2 ρL ρR r W ((τ ω).untopD 0) ω) := by
  set d : Ω → ℝ := fun ω => -centreW κ ρL ρR r (c ω) + normW κ ρL ρR r (c ω) / 2 with hd
  have h0τ : 𝓖 0 ≤ hτ.measurableSpace := hτ.le_measurableSpace_of_const_le fun _ => bot_le
  have hdm : Measurable[hτ.measurableSpace] d :=
    ((((measurable_centreW κ ρL ρR r).comp hc).neg.add (((measurable_normW κ ρL ρR r).comp hc).div_const 2))).mono
      h0τ le_rfl
  have hjoint := condExp_cexp_joint_word hcf hhm hc hadm hgood hτ hτS φ a b
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  have he : StronglyMeasurable[hτ.measurableSpace] fun ω => Complex.exp (Complex.I * ((b * d ω : ℝ) : ℂ)) :=
    (@GFF.measurable_exp_I_mul Ω hτ.measurableSpace _ (hdm.const_mul b)).stronglyMeasurable
  have hYm : Measurable fun ω => a * h ω φ + b * srcPairW κ ρL ρR r (c ω) (h ω) :=
    (((LQGMetric.measurable_distOn_apply φ).comp hhm).const_mul a).add
      ((measurable_srcPairW_word hhm (hc.mono (𝓖.le 0) le_rfl)).const_mul b)
  have hEi : Integrable (fun ω => Complex.exp (Complex.I *
      ((a * h ω φ + b * srcPairW κ ρL ρR r (c ω) (h ω) : ℝ) : ℂ))) P :=
    Integrable.of_bound (GFF.measurable_exp_I_mul hYm).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (hnorm _).le)
  have hpull := condExp_bilin_of_stronglyMeasurable_left (m := hτ.measurableSpace) (μ := P)
    (ContinuousLinearMap.mul ℝ ℂ) he (by
      refine Integrable.of_bound ((he.mono hτ.measurableSpace_le).aestronglyMeasurable.mul hEi.1) 1
        (Eventually.of_forall fun ω => ?_)
      simp only [ContinuousLinearMap.mul_apply', norm_mul, hnorm, mul_one, le_refl]) hEi
  have hF : (fun ω' => Complex.exp (Complex.I * ((a * h ω' φ + b * shiftPairW κ ρL ρR r c h ω' : ℝ) : ℂ))) =
      fun ω' => Complex.exp (Complex.I * ((b * d ω' : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((a * h ω' φ + b * srcPairW κ ρL ρR r (c ω') (h ω') : ℝ) : ℂ)) := by
    funext ω'
    rw [← Complex.exp_add, shiftPairW]
    congr 1
    simp only [hd]
    push_cast
    ring
  rw [hF]
  filter_upwards [hpull, hjoint] with ω h1 h2 hD
  simp only [ContinuousLinearMap.mul_apply'] at h1
  have em : srcMeanAt κ (c ω).1 (c ω).2 ρL ρR r W VL VR ((τ ω).untopD 0) ω =
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
        (bheProc κ ρL ρR W VL VR ω ((τ ω).untopD 0)) z * vSrc κ (c ω).1 (c ω).2 ρL ρR r z := rfl
  rw [h1, h2 hD, cfVal, cfVal, ← Complex.exp_add, em]
  congr 1
  simp only [hd, srcEnergyAt]
  push_cast
  ring

/-- The conditional law of the shifted pairing `Y₂` alone (the case `a = 0`, `φ = 0`). -/
theorem condExp_cexp_shift {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) (b : ℝ) :
    P[fun ω' => Complex.exp (Complex.I * ((b * shiftPairW κ ρL ρR r c h ω' : ℝ) : ℂ)) | hτ.measurableSpace]
      =ᵐ[P] fun ω => cfVal (b * (srcMeanAt κ (c ω).1 (c ω).2 ρL ρR r W VL VR ((τ ω).untopD 0) ω -
          centreW κ ρL ρR r (c ω) + normW κ ρL ρR r (c ω) / 2))
        (b ^ 2 * srcEnergyAt κ (c ω).1 (c ω).2 ρL ρR r W ((τ ω).untopD 0) ω) := by
  have hj := condExp_cexp_joint_shift hcf hhm hc hadm hgood hτ hτS 0 0 b
  filter_upwards [hj] with ω hω
  have hd : ω ∈ {ω | Disjoint (tsupport ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ))
      (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))} := by
    show Disjoint _ _
    rw [show ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 from rfl, tsupport_zero]
    exact Set.empty_disjoint _
  have e := hω hd
  simp only [zero_mul, zero_add, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at e
  exact e

/-- **The first line of (HL4) for the random word**: for a `𝓖`-stopping time `τ` before the local stop and `A ∈ 𝓖_τ`,
`E[Z; A] = E[N_τ; A]`. -/
theorem setLIntegral_densW {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    ∫⁻ ω in A, ENNReal.ofReal (densW κ ρL ρR r (c ω) (h ω)) ∂P =
      ∫⁻ ω in A, ENNReal.ofReal (martW κ ρL ρR r W VL VR c ((τ ω).untopD 0) ω) ∂P := by
  have hcf' := condExp_cexp_shift hcf hhm hc hadm hgood hτ hτS
  have hXm : Measurable (shiftPairW κ ρL ρR r c h) := measurable_shiftPairW hhm (hc.mono (𝓖.le 0) le_rfl)
  have hW : Measurable[hτ.measurableSpace] (A.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hA
  have key := lintegral_mul_exp_of_condGauss hτ.measurableSpace_le hXm hcf' hW (-1)
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  rw [← lintegral_indicator hAm, ← lintegral_indicator hAm]
  have e1 : ∀ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω * ENNReal.ofReal (Real.exp (-1 * shiftPairW κ ρL ρR r c h ω)) =
      A.indicator (fun ω => ENNReal.ofReal (densW κ ρL ρR r (c ω) (h ω))) ω := fun ω => by
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω, one_mul, neg_one_mul, exp_neg_shiftPairW]
    · simp [Set.indicator_of_notMem hω]
  simp only [e1] at key
  rw [key]
  refine lintegral_congr_ae ?_
  filter_upwards [hgood, hτS] with ω hg hτω
  by_cases hω : ω ∈ A
  · simp only [Set.indicator_of_mem hω, one_mul]
    have hx := hadm ω
    have hE := loewnerGreenEnergy_vSrc_eq_of_isGoodPath (κ := κ) (ρL := ρL) (ρR := ρR) hg.1 hg.2.1 hx.1 hx.2
      hg.2.2 (coe_untopD_le_localStopPath hτω)
    rw [martW, srcMart, centreW_of_adm κ ρL ρR r hx, normW_of_adm κ ρL ρR r hx]
    simp only [srcEnergyAt]
    rw [show (fun s : ℝ => W s.toNNReal ω) = Ito.rpath (fun t => W t ω) from rfl, hE]
    congr 2
    ring
  · simp [Set.indicator_of_notMem hω]

/-- **`E Z = 1`** for the random word. -/
theorem lintegral_densW : ∫⁻ ω, ENNReal.ofReal (densW κ ρL ρR r (c ω) (h ω)) ∂P = 1 := by
  have hτ : IsStoppingTime 𝓖 fun _ : Ω => ((0 : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const _ _
  have hset := setLIntegral_densW hcf hhm hc hadm hgood hτ (ae_of_all _ fun ω => by simp)
    (MeasurableSet.univ (m := hτ.measurableSpace))
  simp only [Measure.restrict_univ] at hset
  rw [hset]
  calc ∫⁻ ω, ENNReal.ofReal (martW κ ρL ρR r W VL VR c (((0 : ℝ≥0) : WithTop ℝ≥0).untopD 0) ω) ∂P
      = ∫⁻ _, 1 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hgood] with ω hg
        have hg' : IsGoodPath κ (c ω).1 (c ω).2 ρL ρR W VL VR B ζ ω := ⟨hg.1, hg.2.1⟩
        rw [WithTop.untopD_coe, martW, srcMart_zero_of_isGoodPath hg' (hadm ω).1 (hadm ω).2,
          ENNReal.ofReal_one]
    _ = 1 := by rw [lintegral_const, measure_univ, one_mul]

omit hcf hhm hc hadm hgood in
theorem measurable_densW_word (hhm : Measurable h) (hc : Measurable c) :
    Measurable fun ω => densW κ ρL ρR r (c ω) (h ω) := by
  have h1 := (measurable_densW (nL := nL) (nR := nR) κ ρL ρR r).comp (hc.prodMk hhm)
  exact h1

theorem integrable_densW : Integrable (fun ω => densW κ ρL ρR r (c ω) (h ω)) P := by
  have hm := measurable_densW_word (κ := κ) (ρL := ρL) (ρR := ρR) (r := r) hhm (hc.mono (𝓖.le 0) le_rfl)
  refine (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (ae_of_all _ fun ω => (densW_pos κ ρL ρR r _ _).le)).1 ?_
  rw [lintegral_densW hcf hhm hc hadm hgood]
  exact ENNReal.one_ne_top

end Density

/-! ### The measure `Q = Z · P` -/

section Measure

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)}

variable (κ ρL ρR r) in
/-- **The Cameron–Martin measure of the random word** `Q = Z · P`, `Z = densW (c) (h)`. -/
def wordMeasure (P : Measure Ω) (c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)) (h : Ω → DistOn upperHalfPlaneOpens) :
    Measure Ω :=
  P.withDensity fun ω => ENNReal.ofReal (densW κ ρL ρR r (c ω) (h ω))

omit [IsProbabilityMeasure P] in
theorem wordMeasure_absolutelyContinuous : wordMeasure κ ρL ρR r P c h ≪ P :=
  withDensity_absolutelyContinuous _ _

omit [IsProbabilityMeasure P] in
theorem absolutelyContinuous_wordMeasure (hhm : Measurable h) (hc : Measurable c) :
    P ≪ wordMeasure κ ρL ρR r P c h :=
  withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp
    (measurable_densW_word hhm hc)).aemeasurable (ae_of_all _ fun ω => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact densW_pos κ ρL ρR r _ _)

variable (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h)
  (hhm : Measurable h) (hc : Measurable[𝓖 0] c) (hadm : ∀ ω, IsAdmWord r (c ω))
  (hgood : ∀ᵐ ω ∂P, IsWordPath κ ρL ρR W VL VR B ζ c ω)
include hcf hhm hc hadm hgood

theorem isProbabilityMeasure_wordMeasure : IsProbabilityMeasure (wordMeasure κ ρL ρR r P c h) :=
  ⟨by rw [wordMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_densW hcf hhm hc hadm hgood]⟩

/-- **`Q = N_τ · P` on `𝓖_τ`** for every `𝓖`-stopping time `τ` before the local stop. -/
theorem wordMeasure_apply_of_measurableSet {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    wordMeasure κ ρL ρR r P c h A =
      ∫⁻ ω in A, ENNReal.ofReal (martW κ ρL ρR r W VL VR c ((τ ω).untopD 0) ω) ∂P := by
  rw [wordMeasure, withDensity_apply _ (hτ.measurableSpace_le _ hA),
    setLIntegral_densW hcf hhm hc hadm hgood hτ hτS hA]

end Measure

end LocalExt

end InteractingSLE
