/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtCMean
import InteractingSLE.Spec.Sec7.LocalExtCReindex
import InteractingSLE.Spec.Coupling.ProtectedKernel
import InteractingSLE.Spec.Coupling.SafeEnergy
import SupercriticalConformalCovariance.GM24.TVReduce

/-!
# Aux. lemma 55, step 5 (kernel half): the recoded field has the two-seed kernel under `Q = Z · P`

Packet PROVE-LOCEXT-C. Specification p. 250: "Conditional Cameron–Martin shifting changes the mean to `C_{K_t} − P_t f`
and leaves this covariance unchanged. Equation (HL8) then changes its outside-hull mean to … `M⁰_t`. (HL9) … forgetting
the germ gives exactly the original two-seed Gaussian kernel outside `K_t`. This holds for every stopping time at most
`S`."

* `condExp_withDensity_ae_eq` (**Bayes' formula** for conditional expectations, generic): for `Q = Z · P` with
  `P[Z | m] = N > 0` and a bounded `X`, `Q[X | m] = N⁻¹ P[Z X | m]` `Q`-almost everywhere;
* `HasSrcJointKernel` (the input of PROVE-LOCEXT-A2, `SrcJointKernelStatement` of its in-flight `LocalExtA2Joint`, with
  the density and its conditional expectation abstracted): at a driving stop `τ ≤ S`,
  `P[Z | 𝓖_τ] = N` and `P[Z e^{i h(φ)} | 𝓖_τ] = N · exp(i ∫ (𝔥_τ − G_{ℍ∖K_τ} v) φ − ½ E_τ(φ))` on `{supp φ ∩ K_τ = ∅}`;
* `recodeShift`: the deterministic adjustment `f − q` of (HL8), `continuousOn_recodeShift`;
* **`condExp_recoded_eq_twoSeedKernel`** (step 5, kernel half): under `HasSrcJointKernel`, the recoded field
  `h₀ = h + f − q` satisfies, under `Q = Z · P` and almost surely on `{supp φ ∩ K_τ = ∅}`,
  `E_Q[e^{i h₀(φ)} | 𝓖_τ] = exp(i ∫ 𝔥⁰_τ φ − ½ E_τ(φ))`, the frozen kernel of the **two-seed word** (weights
  `(seedSumL, seedSumR)` at the merged seed positions).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

/-! ### Bayes' formula for conditional expectations -/

section Bayes

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `‖P[Z • X | m]‖ ≤ C N` almost everywhere when `‖X‖ ≤ C`, `Z ≥ 0` and `P[Z | m] = N`. -/
theorem norm_condExp_smul_le [IsFiniteMeasure P] {Z : Ω → ℝ} (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZi : Integrable Z P) {N : Ω → ℝ} (hN : P[Z | m] =ᵐ[P] N) {X : Ω → ℂ}
    (hXm : AEStronglyMeasurable X P) {C : ℝ} (hXb : ∀ ω, ‖X ω‖ ≤ C) :
    ∀ᵐ ω ∂P, ‖P[fun ω => Z ω • X ω | m] ω‖ ≤ C * N ω := by
  have hZX : Integrable (fun ω => Z ω • X ω) P := by
    refine (hZi.const_mul C).mono' (hZi.aestronglyMeasurable.smul hXm) (ae_of_all _ fun ω => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hZ0 ω), mul_comm]
    exact mul_le_mul_of_nonneg_right (hXb ω) (hZ0 ω)
  have h1 := norm_condExp_le (m := m) (μ := P) fun ω => Z ω • X ω
  have h2 : P[fun ω => ‖Z ω • X ω‖ | m] ≤ᵐ[P] P[fun ω => C * Z ω | m] := by
    refine condExp_mono hZX.norm (hZi.const_mul C) (ae_of_all _ fun ω => ?_)
    show ‖Z ω • X ω‖ ≤ C * Z ω
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hZ0 ω), mul_comm]
    exact mul_le_mul_of_nonneg_right (hXb ω) (hZ0 ω)
  have h3 : P[fun ω => C * Z ω | m] =ᵐ[P] fun ω => C * N ω := by
    have e := condExp_smul (m := m) (μ := P) C Z
    filter_upwards [e, hN] with ω he hNω
    show P[C • Z | m] ω = C * N ω
    rw [he, Pi.smul_apply, smul_eq_mul, hNω]
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  exact e1.trans (e2.trans e3.le)

/-- **Bayes' formula for conditional expectations.** For `Q = Z · P` (`Z ≥ 0` integrable), a version `N > 0` of
`P[Z | m]` that is `m`-strongly measurable, and a bounded `X`, `Q[X | m] = N⁻¹ P[Z X | m]` `Q`-almost everywhere. -/
theorem condExp_withDensity_ae_eq (hm : m ≤ mΩ) [IsFiniteMeasure P] {Z : Ω → ℝ} (hZm : Measurable Z)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZi : Integrable Z P) {N : Ω → ℝ} (hNm : StronglyMeasurable[m] N)
    (hNpos : ∀ ω, 0 < N ω) (hN : P[Z | m] =ᵐ[P] N) {X : Ω → ℂ} (hXm : AEStronglyMeasurable X P) {C : ℝ}
    (hXb : ∀ ω, ‖X ω‖ ≤ C) :
    (P.withDensity fun ω => ENNReal.ofReal (Z ω))[X | m] =ᵐ[P.withDensity fun ω => ENNReal.ofReal (Z ω)]
      fun ω => (N ω)⁻¹ • P[fun ω => Z ω • X ω | m] ω := by
  set f : Ω → ℝ≥0 := fun ω => (Z ω).toNNReal with hf
  have hfm : Measurable f := hZm.real_toNNReal
  have hQ : (P.withDensity fun ω => ENNReal.ofReal (Z ω)) = P.withDensity fun ω => (f ω : ℝ≥0∞) := rfl
  have hfZ : ∀ ω, ((f ω : ℝ≥0) : ℝ) = Z ω := fun ω => Real.coe_toNNReal _ (hZ0 ω)
  have hsmul : ∀ (v : Ω → ℂ) (ω : Ω), f ω • v ω = Z ω • v ω := fun v ω => by rw [NNReal.smul_def, hfZ]
  set Q := P.withDensity fun ω => (f ω : ℝ≥0∞) with hQdef
  have : IsFiniteMeasure Q := by
    rw [← hQ]
    exact isFiniteMeasure_withDensity_ofReal hZi.2
  have hZX : Integrable (fun ω => Z ω • X ω) P := by
    refine (hZi.const_mul C).mono' (hZi.aestronglyMeasurable.smul hXm) (ae_of_all _ fun ω => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hZ0 ω), mul_comm]
    exact mul_le_mul_of_nonneg_right (hXb ω) (hZ0 ω)
  set g : Ω → ℂ := fun ω => (N ω)⁻¹ • P[fun ω => Z ω • X ω | m] ω with hg
  have hgm : StronglyMeasurable[m] g :=
    (hNm.measurable.inv.stronglyMeasurable).smul stronglyMeasurable_condExp
  have hgb : ∀ᵐ ω ∂P, ‖g ω‖ ≤ C := by
    filter_upwards [norm_condExp_smul_le hZ0 hZi hN hXm hXb] with ω hω
    rw [hg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hNpos ω), inv_mul_le_iff₀ (hNpos ω), mul_comm]
    exact hω
  have hZg : Integrable (fun ω => Z ω • g ω) P := by
    refine (hZi.const_mul C).mono' (hZi.aestronglyMeasurable.smul (hgm.mono hm).aestronglyMeasurable) ?_
    filter_upwards [hgb] with ω hω
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hZ0 ω), mul_comm]
    exact mul_le_mul_of_nonneg_right hω (hZ0 ω)
  have hXQ : Integrable X Q := by
    rw [hQdef, integrable_withDensity_iff_integrable_smul hfm]
    exact hZX.congr (ae_of_all _ fun ω => (hsmul X ω).symm)
  have hgQ : Integrable g Q := by
    rw [hQdef, integrable_withDensity_iff_integrable_smul hfm]
    exact hZg.congr (ae_of_all _ fun ω => (hsmul g ω).symm)
  rw [hQ]
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hXQ (fun s _ _ => hgQ.integrableOn) ?_
    (hgm.aestronglyMeasurable)).symm
  intro s hs _
  have hs' : MeasurableSet s := hm s hs
  rw [setIntegral_withDensity_eq_setIntegral_smul hfm _ hs', setIntegral_withDensity_eq_setIntegral_smul hfm _ hs',
    integral_congr_ae (ae_of_all _ fun x => hsmul g x), integral_congr_ae (ae_of_all _ fun x => hsmul X x)]
  -- `∫_s Z g = ∫_s P[Z g | m] = ∫_s N g = ∫_s P[Z X | m] = ∫_s Z X`
  rw [← setIntegral_condExp hm hZg hs, ← setIntegral_condExp hm hZX hs]
  refine setIntegral_congr_ae (hm s hs) ?_
  have hpull := condExp_smul_of_aestronglyMeasurable_right (m := m) (μ := P) hZi hZg
    (hgm.aestronglyMeasurable)
  filter_upwards [hpull, hN] with ω h1 h2 _
  rw [show (fun ω => Z ω • g ω) = Z • g from rfl, h1]
  show P[Z | m] ω • g ω = _
  rw [h2, hg]
  simp only
  rw [smul_smul, mul_inv_cancel₀ (hNpos ω).ne', one_smul]

end Bayes

/-! ### The recoding (HL8) -/

section Recode

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}

variable (κ xL xR ρL ρR r) in
/-- The deterministic adjustment `f − q` of (HL8) (`h₀ = h + f − q`). -/
def recodeShift (z : ℂ) : ℝ := fCut κ xL xR ρL ρR r z - qExt κ xL xR ρL ρR z

theorem continuousOn_qExt : ContinuousOn (qExt κ xL xR ρL ρR) H := by
  have hL : ∀ x : ℝ, ContinuousOn (fun z : ℂ => Complex.arg (z - x)) H := fun x z hz => by
    have hz' : 0 < z.im := hz
    refine ((Complex.continuousAt_arg (Complex.mem_slitPlane_iff.2 (Or.inr ?_))).comp
      (continuousAt_id.sub continuousAt_const)).continuousWithinAt
    show (z - (x : ℂ)).im ≠ 0
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact hz'.ne'
  have hR : ∀ x : ℝ, ContinuousOn (fun z : ℂ => Complex.arg ((x : ℂ) - z)) H := fun x z hz => by
    have hz' : 0 < z.im := hz
    refine ((Complex.continuousAt_arg (Complex.mem_slitPlane_iff.2 (Or.inr ?_))).comp
      (continuousAt_const.sub continuousAt_id)).continuousWithinAt
    show ((x : ℂ) - z).im ≠ 0
    rw [Complex.sub_im, Complex.ofReal_im, zero_sub, ne_eq, neg_eq_zero]
    exact hz'.ne'
  unfold qExt
  exact continuousOn_const.mul ((continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hL (xL i))).add
    (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hR (xR i))))

theorem continuousOn_recodeShift (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    ContinuousOn (recodeShift κ xL xR ρL ρR r) H :=
  (contDiff_fCut (n := 0) hF hr).continuous.continuousOn.sub continuousOn_qExt

variable (κ xL xR ρL ρR r) in
/-- **The recoded field of (HL8)**: `h₀ = h + f − q` as a random distribution. -/
def recode (T : LQGMetric.DistOn upperHalfPlaneOpens) : LQGMetric.DistOn upperHalfPlaneOpens :=
  T + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (recodeShift κ xL xR ρL ρR r)

theorem measurable_recode : Measurable (recode κ xL xR ρL ρR r) :=
  Coupling.measurable_add_distOnConst _

theorem recode_apply (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (T : LQGMetric.DistOn upperHalfPlaneOpens) (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    recode κ xL xR ρL ρR r T φ = T φ + ∫ z, φ z * recodeShift κ xL xR ρL ρR r z := by
  rw [recode, show (T + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens
      (recodeShift κ xL xR ρL ρR r)) φ = T φ + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens
      (recodeShift κ xL xR ρL ρR r) φ from rfl,
    SupercriticalConformalCovariance.GM24.smoothDist_apply (continuousOn_recodeShift hF hr)]

end Recode

/-! ### Step 5, kernel half -/

section Kernel

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- The centred left positions at the stop `τ`. -/
def cposL (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : Fin nL → ℝ :=
  fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω

/-- The centred right positions at the stop `τ`. -/
def cposR (W : ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : Fin nR → ℝ :=
  fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω

/-- **The conditional Cameron–Martin shift before the local stop at one driving stop `τ`** (the input of
PROVE-LOCEXT-A2: its `SrcJointKernelStatement`, `Spec/Sec7/LocalExtA2Joint.lean`, with the density `Z = srcDensity (h)`
and its conditional expectation `N = srcMart` abstracted): `P[Z | m] = N`, and for every bounded harmonic extension `u`
of the force data at the stop and every test function `φ`, almost surely on `{supp φ ∩ K_τ = ∅}`,
`P[Z e^{i h(φ)} | m] = N · exp(i ∫ (𝔥_τ − G_{ℍ∖K_τ} v) φ − ½ E_τ(φ))`. -/
def HasSrcJointKernel (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ)
    (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (τ : Ω → WithTop ℝ≥0) (m : MeasurableSpace Ω) (Z N : Ω → ℝ) :
    Prop :=
  P[Z | m] =ᵐ[P] N ∧
    ∀ u : Ω → ℂ → ℝ, (∀ ω, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (cposL W VL τ ω) (cposR W VR τ ω))
        (forceJumpSet (cposL W VL τ ω) (cposR W VR τ ω)) (u ω)) →
      ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
        Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
          P[fun ω' => ((Z ω' : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ)) | m] ω =
            (N ω : ℂ) * Complex.exp (Complex.I * ((∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω)
                ((τ ω).untopD 0 : ℝ≥0) (u ω) z - greenPot κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω)
                  ((τ ω).untopD 0 : ℝ≥0) z) * φ z : ℝ) : ℂ) -
              (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ))

/-- The coupling mean times a test function supported off the hull is integrable. -/
theorem integrable_couplingMean_mul {w : ℝ≥0 → ℝ} {t : ℝ≥0} (hw : ContinuousOn (Ito.rpath w) (Icc 0 (t : ℝ)))
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) {φ : LQGMetric.TestOn upperHalfPlaneOpens}
    (hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w) t)) :
    Integrable fun z => couplingMean κ (Ito.rpath w) t u z * φ z := by
  have hK : IsCompact (tsupport (φ : ℂ → ℝ)) := φ.hasCompactSupport.isCompact
  have hsub : tsupport (φ : ℂ → ℝ) ⊆ (Coupling.hullDom w t : Set ℂ) := fun z hz =>
    Coupling.mem_hullDom hw (Coupling.tsupport_subset_H φ hz) fun hzK => hφ.ne_of_mem hz hzK rfl
  have hc : ContinuousOn (fun z => couplingMean κ (Ito.rpath w) t u z * φ z) (tsupport (φ : ℂ → ℝ)) :=
    ((Coupling.continuousOn_couplingMean κ hw hu).mono hsub).mul φ.continuous.continuousOn
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 (hc.integrableOn_compact hK)
  intro z hz
  refine subset_tsupport _ ?_
  intro h0
  exact hz (by simp only [h0, mul_zero])

/-- The merged left seed position at the stop (centred; `0` on a side without seed). -/
def seedPosL (xL : Fin nL → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ :=
  seedVal xL (cposL W VL τ ω) 0

/-- The merged right seed position at the stop (centred; `0` on a side without seed). -/
def seedPosR (xR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ :=
  seedVal xR (cposR W VR τ ω) 0

/-- **Aux. lemma 55, step 5 (kernel half): the recoded field has the two-seed kernel under `Q = Z · P`.** For a coupling
with an admissible seed, a seed radius `r` and a driving stop `τ ≤ S`, if the conditional Cameron–Martin shift of
(HL3)–(HL4) holds at `τ` (`HasSrcJointKernel`, PROVE-LOCEXT-A2's input), then for every test function `φ`, almost surely
on `{supp φ ∩ K_τ = ∅}`,

`E_Q[e^{i h₀(φ)} | 𝓖_τ] = exp(i ∫ 𝔥⁰_τ φ − ½ E_τ(φ))`,

where `h₀ = recode h = h + f − q` ((HL8)) and `𝔥⁰_τ` is the coupling mean of the **two-seed word** (weights
`(seedSumL, seedSumR)`) at the merged seed positions, for every bounded harmonic extension `u₂` of its data ((HL9)). -/
theorem condExp_recode_eq_twoSeedKernel (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) {Z N : Ω → ℝ} (hZm : Measurable Z)
    (hZpos : ∀ ω, 0 < Z ω) (hZi : Integrable Z P) (hNm : StronglyMeasurable[hτ.measurableSpace] N)
    (hNpos : ∀ ω, 0 < N ω) (hjoint : HasSrcJointKernel κ xL xR ρL ρR r P W VL VR h τ hτ.measurableSpace Z N)
    {u₂ : Ω → ℂ → ℝ}
    (hu₂ : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR)
        (fun _ => seedPosL xL W VL τ ω) (fun _ => seedPosR xR W VR τ ω))
      (forceJumpSet (fun _ : Fin 1 => seedPosL xL W VL τ ω) (fun _ : Fin 1 => seedPosR xR W VR τ ω)) (u₂ ω))
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      (P.withDensity fun ω => ENNReal.ofReal (Z ω))[fun ω' =>
          Complex.exp (Complex.I * (recode κ xL xR ρL ρR r (h ω') φ : ℂ)) | hτ.measurableSpace] ω =
        Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
            (u₂ ω) z * φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ)) := by
  have hE := hC.1
  have hhm := hC.2.1
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hm : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  set c : ℝ := ∫ z, φ z * recodeShift κ xL xR ρL ρR r z with hc
  set X : Ω → ℂ := fun ω' => Complex.exp (Complex.I * (recode κ xL xR ρL ρR r (h ω') φ : ℂ)) with hXdef
  have hXeq : ∀ ω', (Z ω') • X ω' =
      Complex.exp (Complex.I * c) * (((Z ω' : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ))) := by
    intro ω'
    rw [hXdef]
    simp only
    rw [recode_apply hF hr, Complex.real_smul]
    push_cast
    rw [mul_add, Complex.exp_add]
    ring
  have hXm : AEStronglyMeasurable X P := by
    have h1 : Measurable fun ω' => recode κ xL xR ρL ρR r (h ω') φ :=
      (measurable_pi_apply φ).comp ((LQGMetric.measurable_distEval _).comp (measurable_recode.comp hhm))
    exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp h1))).aestronglyMeasurable
  have hXb : ∀ ω', ‖X ω'‖ ≤ 1 := fun ω' => by
    rw [hXdef]
    exact (Complex.norm_exp_I_mul_ofReal _).le
  have hbayes := condExp_withDensity_ae_eq hm hZm (fun ω => (hZpos ω).le) hZi hNm hNpos hjoint.1 hXm hXb
  have hPQ : P ≪ P.withDensity fun ω => ENNReal.ofReal (Z ω) :=
    withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hZm).aemeasurable
      (ae_of_all _ fun ω => by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hZpos ω)
  have hbayesP := hPQ.ae_le hbayes
  have hpull : P[fun ω' => Z ω' • X ω' | hτ.measurableSpace] =ᵐ[P] fun ω =>
      Complex.exp (Complex.I * c) *
        P[fun ω' => ((Z ω' : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ)) | hτ.measurableSpace] ω := by
    have e : (fun ω' => Z ω' • X ω') = Complex.exp (Complex.I * c) •
        fun ω' => ((Z ω' : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ)) := by
      funext ω'
      rw [hXeq, Pi.smul_apply, smul_eq_mul]
    rw [e]
    filter_upwards [condExp_smul (m := hτ.measurableSpace) (μ := P) (Complex.exp (Complex.I * c))
      (fun ω' => ((Z ω' : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ)))] with ω hω
    rw [hω, Pi.smul_apply, smul_eq_mul]
  -- the n-word extension, explicitly
  set u : Ω → ℂ → ℝ := fun ω => Impl.forceExt κ (Ito.weightWord ρL ρR) (cposL W VL τ ω) (cposR W VR τ ω) with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (cposL W VL τ ω) (cposR W VR τ ω))
      (forceJumpSet (cposL W VL τ ω) (cposR W VR τ ω)) (u ω) := fun ω =>
    Impl.isBoundedHarmonicExtension_forceExt κ (Ito.weightWord ρL ρR) _ _
  have hJ := hjoint.2 u hu φ
  filter_upwards [hbayesP, hpull, hJ, ae_isGoodPath hE hκ, hτS] with ω hb hp hj hg hτω hdis
  rw [hb, hp, hj hdis]
  -- the stop is finite and before the lifetime
  have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top localStopPath_le_stopHorizon) hτω
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
  set t : ℝ≥0 := (τ ω).untopD 0 with htdef
  have hta : t = a := by rw [htdef, ← ha, WithTop.untopD_coe]
  have htS : (t : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by rw [hta, ha]; exact hτω
  have htζ : (t : ℝ≥0∞) < ζ ω := by
    have h1 := localStopPath_lt hg.1 hF hr hseed hg.2
    exact lt_of_le_of_lt (by exact_mod_cast htS) h1
  have hpu := hg.isSLEPathUpTo
  have hwc : ContinuousOn (Ito.rpath fun t => W t ω) (Icc 0 (t : ℝ)) := by
    refine hg.continuousOn_W.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    exact toNNReal_lt_of_mem_Icc htζ hs
  -- the merged seed positions
  have hcL : seedPosL xL W VL τ ω ≤ 0 := by
    unfold seedPosL seedVal
    split_ifs with hs
    · exact sub_nonpos.2 (hpu.vL_le_w htζ _)
    · exact le_rfl
  have hcR : 0 ≤ seedPosR xR W VR τ ω := by
    unfold seedPosR seedVal
    split_ifs with hs
    · exact sub_nonneg.2 (hpu.w_le_vR htζ _)
    · exact le_rfl
  have hcL' : ∀ i, xL i = 0 → VL i t ω - W t ω = seedPosL xL W VL τ ω := fun i hi =>
    (seedVal_of_eq_zero (v := cposL W VL τ ω) (w := 0) (fun a b ha hb => by
      show VL a t ω - W t ω = VL b t ω - W t ω
      rw [vL_eq_vL_of_xL_eq_zero hpu ha hb htζ]) hi).symm
  have hcR' : ∀ j, xR j = 0 → VR j t ω - W t ω = seedPosR xR W VR τ ω := fun j hj =>
    (seedVal_of_eq_zero (v := cposR W VR τ ω) (w := 0) (fun a b ha hb => by
      show VR a t ω - W t ω = VR b t ω - W t ω
      rw [vR_eq_vR_of_xR_eq_zero hpu ha hb htζ]) hj).symm
  -- (HL9) integrated against `φ`
  have hpt : ∀ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω) z -
      greenPot κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) t z) * φ z =
      couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u₂ ω) z * φ z - φ z * recodeShift κ xL xR ρL ρR r z := by
    intro z
    by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
    · have hy : z ∈ H \ fwdHull (Ito.rpath fun t => W t ω) t :=
        ⟨Coupling.tsupport_subset_H φ hz, fun hzK => hdis.ne_of_mem hz hzK rfl⟩
      have h9 : couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω) z -
          greenPot κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) t z + fCut κ xL xR ρL ρR r z -
            qExt κ xL xR ρL ρR z = couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u₂ ω) z :=
        couplingMean_sub_greenPot_add_eq (w := fun t => W t ω) (vL := fun i t => VL i t ω)
          (vR := fun i t => VR i t ω) hg.1 hg.2 hF hr hseed htS htζ hy (hu ω) hcL hcR hcL' hcR' (hu₂ ω)
      rw [recodeShift, ← h9]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hz]
      ring
  have hint1 : Integrable fun z => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u₂ ω) z * φ z :=
    integrable_couplingMean_mul (κ := κ) hwc (hu₂ ω).1 hdis
  have hint2 := SupercriticalConformalCovariance.GM24.integrable_test_mul (continuousOn_recodeShift
    (κ := κ) (ρL := ρL) (ρR := ρR) hF hr) φ
  have key : (∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω) z -
      greenPot κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) t z) * φ z) + c =
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u₂ ω) z * φ z := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_sub hint1 hint2, hc]
    ring
  rw [← key, Complex.real_smul]
  have hN0 : ((N ω : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hNpos ω).ne'
  have e : Complex.exp (Complex.I * (((∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω) z -
      greenPot κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) t z) * φ z) + c : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) t φ : ℝ) : ℂ)) =
      Complex.exp (Complex.I * c) * Complex.exp (Complex.I * ((∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) t
        (u ω) z - greenPot κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) t z) * φ z : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) t φ : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  push_cast
  field_simp

end Kernel

end LocalExt

end InteractingSLE
