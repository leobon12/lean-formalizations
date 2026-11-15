/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelField
import InteractingSLE.Spec.Sec7.PocketCouplingMean
import QuantumZipper.Proofs.Thm18.LWFarPocketFar

/-!
# Lemma 4.7's direction, item (A)(a): the strip counterflow hull's explicit mean in the chart `M_q`

Packet PROVE-CFRESTART2. Specification §4.2, proof of Lemma 4.7 (`source/spec/p097-144.md#lem-4.7-proof`, p. 118):
"the boundary data of the conditional law of `h` given `η′|_{[0,t]}`". The counterflow of
`Sec4.IsStripCounterflowDriver` is coupled, in the chart `M_q(w) = −1 − (1 + q)/w`, with its parameter field `h′`, the
`M_q`-chart transport of the strip field `h` with sign `−1`
(`IsChartTransport (stripCounterflowChart q) (−1) a k h h′`).
For an optional hull coupling `(h′, W, …)` (parameter `κ′ > 0`) and a stopping time `τ < ζ` of its frozen driving
filtration, this file identifies every local-set mean of the read-back hull `A = M_q⁻¹(K_τ)` for the centred strip
field `h − u₀` (`u₀` harmonic):

  `g(φ) = ∫ (−𝔥_τ(M_q z) + a + k · lift(z) − u₀(z)) φ(z) dz`  for `supp φ ⊆ ℍ ∖ A`,

with `𝔥_τ = couplingMean κ′ W τ u` the coupling mean (**`ae_apply_eq_of_isLocalSetMean_stripInvHull`**). This is the
counterflow single mean the Proposition 3.8 step needs (the template is the flow line's
`Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull`; the history marking is
`isHistoryAvoidanceLocal_stripInv_hull`). Ingredients:

* `tsupport_cfBackTest_subset`: `supp(cfBackTest φ) ⊆ M_q(supp φ)`;
* `disjoint_stripFwd_image_iff`: `M_q(S) ∩ K = ∅ ↔ S ∩ M_q⁻¹(K) = ∅` for `S, K ⊆ ℍ`;
* **`zeroGFFTestCov_cfBackTest`**: conformal invariance of the zero-boundary covariance under `M_q`
  (`σ²_{ℍ∖K}(cfBackTest φ) = σ²_{ℍ∖M_q⁻¹(K)}(φ)`), composed from the translation, dilation and `R` invariances;
* `harmonicOnNhd_cfMean`: the candidate mean is harmonic off `A`;
* `apply_eq_neg_cfBackTest`: `h(φ) = −h′(cfBackTest φ) + ∫ (a + k · lift) φ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Sec5.CrossRestart

open LocalSets

variable {q : ℝ}

/-! ### Supports, disjointness and the covariance under `M_q` -/

/-- **The support of `cfBackTest φ` lies in `M_q(supp φ)`.** -/
theorem tsupport_cfBackTest_subset (hq : 0 < q) (φ : TestOn upperHalfPlaneOpens) :
    tsupport (cfBackTest hq φ) ⊆ (Sec4.stripCounterflowChart q).1 '' tsupport φ := by
  have h1 := Sec7.PocketCoupling.tsupport_pushTest_subset_image (Exist.isConformal_shiftChart (-1))
    (Chart.pushTest (Chart.isConformal_dilation (cfr_pos hq))
      (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ))
  have h2 := Sec7.PocketCoupling.tsupport_pushTest_subset_image (Chart.isConformal_dilation (cfr_pos hq))
    (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ)
  have h3 := Sec7.PocketCoupling.tsupport_pushTest_subset_image
    Sec7.StripSysField.isConformal_infinityReturnChart φ
  refine h1.trans ((image_mono (h2.trans (image_mono h3))).trans ?_)
  rintro _ ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
  refine ⟨z, hz, ?_⟩
  have hq1 : (1 + (q : ℂ)) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.2 (by linarith)
  show -1 - (1 + (q : ℂ)) * z⁻¹ = (-z⁻¹ / ((1 / (1 + q) : ℝ) : ℂ)) + ((-1 : ℝ) : ℂ)
  push_cast
  field_simp
  ring

/-- `M_q` maps `ℍ` into `ℍ` and inverts `M_q⁻¹` there: `M_q(S) ∩ K = ∅ ↔ S ∩ M_q⁻¹(K) = ∅` for `S, K ⊆ ℍ`. -/
theorem disjoint_stripFwd_image_iff (hq : 0 < q) {S K : Set ℂ} (hS : S ⊆ H) (hK : K ⊆ H) :
    Disjoint ((Sec4.stripCounterflowChart q).1 '' S) K ↔
      Disjoint S ((Sec4.stripCounterflowChart q).2.1 '' K) := by
  constructor
  · intro hd
    refine Set.disjoint_left.2 fun z hzS ⟨w, hwK, hwz⟩ => Set.disjoint_left.1 hd ⟨z, hzS, rfl⟩ ?_
    have hw1 : w ≠ -1 := fun h => by
      have := congrArg Complex.im h
      simp only [neg_im, one_im, neg_zero] at this
      exact (ne_of_gt (show (0 : ℝ) < w.im from hK hwK)) this
    rw [← hwz, Sec4.stripCounterflowChart_fwd_inv hq hw1]
    exact hwK
  · intro hd
    refine Set.disjoint_left.2 fun w ⟨z, hzS, hzw⟩ hwK => Set.disjoint_left.1 hd hzS ⟨w, hwK, ?_⟩
    rw [← hzw, Sec4.stripCounterflowChart_inv_fwd hq (WangWu.ne_zero_of_mem_H (hS hzS))]

/-- `H ∖ (K + 1)` is the translate of `H ∖ K` (as a preimage). -/
theorem H_diff_image_add_one (K : Set ℂ) :
    H \ (fun z : ℂ => z + ((1 : ℝ) : ℂ)) '' K = (fun z : ℂ => z + ((-1 : ℝ) : ℂ)) ⁻¹' (H \ K) := by
  have h := WholeField.preimage_add_H_diff_image (-1) ((fun z : ℂ => z + ((1 : ℝ) : ℂ)) '' K)
  have e : (fun z : ℂ => z + ((-1 : ℝ) : ℂ)) '' ((fun z : ℂ => z + ((1 : ℝ) : ℂ)) '' K) = K := by
    rw [image_image]
    refine (image_congr fun z _ => ?_).trans (image_id K)
    show z + ((1 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) = z
    push_cast
    ring
  rw [e] at h
  exact h.symm

/-- **Conformal invariance of the zero-boundary covariance under `M_q`**:
`σ²_{ℍ∖K}(cfBackTest φ) = σ²_{ℍ∖M_q⁻¹(K)}(φ)` whenever `ℍ ∖ K` is open. -/
theorem zeroGFFTestCov_cfBackTest (hq : 0 < q) {K : Set ℂ} (hKo : IsOpen (H \ K)) (φ : TestOn upperHalfPlaneOpens) :
    QuantumZipper.zeroGFFTestCov (H \ K) (cfBackTest hq φ) (cfBackTest hq φ) =
      QuantumZipper.zeroGFFTestCov (H \ (Sec4.stripCounterflowChart q).2.1 '' K) φ φ := by
  set r : ℝ := 1 / (1 + q) with hr_def
  have hr : 0 < r := cfr_pos hq
  set χ₀ := Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ with hχ₀
  set χ₁ := Chart.pushTest (Chart.isConformal_dilation hr) χ₀ with hχ₁
  have hψ : ⇑(cfBackTest hq φ) = fun z => χ₁ (z + ((1 : ℝ) : ℂ)) := by
    funext z
    rw [cfBackTest, Exist.pushTest_shiftChart_apply]
    congr 1
    push_cast
    ring
  set K₁ := (fun z : ℂ => z + ((1 : ℝ) : ℂ)) '' K with hK₁
  have hU₁o : IsOpen (H \ K₁) := by
    rw [hK₁, H_diff_image_add_one]
    exact hKo.preimage (by fun_prop)
  -- translation
  have e1 : QuantumZipper.zeroGFFTestCov (H \ K) (cfBackTest hq φ) (cfBackTest hq φ) =
      QuantumZipper.zeroGFFTestCov (H \ K₁) χ₁ χ₁ := by
    rw [hψ, ← WholeField.preimage_add_H_diff_image 1 K]
    exact WholeField.zeroGFFTestCov_comp_add ((1 : ℝ) : ℂ) (H \ K₁) χ₁.continuous χ₁.continuous
  -- dilation
  set K₂ := Sec7.Lemma725RefFull.dil r '' K₁ with hK₂
  have e2 : QuantumZipper.zeroGFFTestCov (H \ K₁) χ₁ χ₁ = QuantumZipper.zeroGFFTestCov (H \ K₂) χ₀ χ₀ := by
    rw [Sec7.Lemma725RefFull.zeroGFFTestCov_dil hr hU₁o sdiff_subset χ₀,
      ← Sec7.Lemma725RefFull.H_diff_image_dil hr]
  have hU₂o : IsOpen (H \ K₂) := by
    rw [hK₂, Sec7.Lemma725RefFull.H_diff_image_dil hr]
    exact Sec7.Lemma725RefFull.isOpen_image_dil hr hU₁o
  -- `R`
  have e3 : QuantumZipper.zeroGFFTestCov (H \ K₂) χ₀ χ₀ =
      QuantumZipper.zeroGFFTestCov (H \ WangWu.negInv '' K₂) φ φ := by
    rw [WangWu.H_diff_image_negInv, WangWu.zeroGFFTestCov_image_negInv hU₂o sdiff_subset φ]
  have e4 : WangWu.negInv '' K₂ = (Sec4.stripCounterflowChart q).2.1 '' K := by
    rw [hK₂, hK₁, image_image, image_image]
    exact image_congr fun z _ => negInv_dil_add_one hq z
  rw [e1, e2, e3, e4]

/-! ### The candidate mean and the field identity -/

/-- `M_q` is analytic at every `z ≠ 0`. -/
theorem analyticAt_stripFwd {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ (Sec4.stripCounterflowChart q).1 z := by
  have : (Sec4.stripCounterflowChart q).1 = fun w : ℂ => -1 - (1 + (q : ℂ)) * w⁻¹ :=
    funext fun w => Sec4.stripCounterflowChart_fwd q w
  rw [this]
  exact analyticAt_const.sub (analyticAt_const.mul (analyticAt_inv hz))

/-- **The candidate mean is harmonic off `M_q⁻¹(K)`**: if `v` is harmonic on `ℍ ∖ K` (`K ⊆ ℍ`) and `u₀` on `ℍ`, then
`−v ∘ M_q + (a + k · lift) − u₀` is harmonic on `ℍ ∖ M_q⁻¹(K)`. -/
theorem harmonicOnNhd_cfMean (hq : 0 < q) {v u₀ : ℂ → ℝ} {K : Set ℂ} (a k : ℝ)
    (hv : InnerProductSpace.HarmonicOnNhd v (H \ K)) (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) :
    InnerProductSpace.HarmonicOnNhd (fun z => -v ((Sec4.stripCounterflowChart q).1 z) + cfShift q a k z - u₀ z)
      (H \ (Sec4.stripCounterflowChart q).2.1 '' K) := by
  intro z hz
  have hz0 : z ≠ 0 := WangWu.ne_zero_of_mem_H hz.1
  have hmem : (Sec4.stripCounterflowChart q).1 z ∈ H \ K := by
    refine ⟨Sec4.stripCounterflowChart_fwd_mem_H hq hz.1, fun hK => hz.2 ⟨_, hK, ?_⟩⟩
    exact Sec4.stripCounterflowChart_inv_fwd hq hz0
  have h1 : InnerProductSpace.HarmonicAt (v ∘ (Sec4.stripCounterflowChart q).1) z :=
    QuantumZipper.Thm18Asm.LWFar.pocket_harmonicAt_comp (analyticAt_stripFwd hz0) (hv _ hmem)
  exact (h1.neg.add (harmonicOnNhd_cfShift q a k z hz.1)).sub (hu₀ z hz.1)

/-- **The strip field from the parameter field, tested**: if `h′` is the `M_q`-chart transport of `h` with sign
`−1`, then `h(φ) = −h′(cfBackTest φ) + ∫ (a + k · lift) φ`. -/
theorem apply_eq_neg_cfBackTest (hq : 0 < q) {a k : ℝ} {h h' : DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport (Sec4.stripCounterflowChart q) (-1) a k h h') (φ : TestOn upperHalfPlaneOpens) :
    h φ = -h' (cfBackTest hq φ) + ∫ z, cfShift q a k z * φ z := by
  have e : h φ = _ := congrArg (fun T : DistOn upperHalfPlaneOpens => T φ) (eq_reflect_of_isChartTransport hq ht)
  rw [e, add_apply, WangWu.reflectField_apply, Sec7.Lemma725RefFull.dilField_apply, Exist.flowField_apply,
    Coupling.smoothDist_apply_eq (continuousOn_cfShift q a k), zero_mul, add_zero]
  rfl

/-! ### The explicit mean -/

/-- **The strip counterflow hull's mean, explicit** (the conditional law of `h` given `η′|_{[0,τ]}` alone, read in the
strip chart). Let `(h′, W, VL, VR, B, ζ)` be an optional hull coupling (parameter `κ′ > 0`) of the parameter field
`h′ ω`, the `M_q`-chart transport of `h ω` with sign `−1`; let `u₀` be harmonic with `h − u₀` a zero-boundary GFF.
For a stopping time `τ < ζ` of the frozen driving filtration, a hitting-measurable version `A` of `M_q⁻¹(K_τ)`, every
local-set mean `g` of `A` for `h − u₀` and bounded harmonic extensions `u ω` of the force data at `τ`: almost surely,
for every test function `φ` supported in `ℍ \ A`, `g(φ) = ∫ (−𝔥_τ(M_q z) + a + k · lift(z) − u₀(z)) φ(z) dz`. -/
theorem ae_apply_eq_of_isLocalSetMean_stripInvHull (hq : 0 < q) {κ' : ℝ} (hκ' : 0 < κ') {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h h' : Ω → DistOn upperHalfPlaneOpens} {a k : ℝ}
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕 W VL VR B ζ h')
    (htr : ∀ ω, IsChartTransport (Sec4.stripCounterflowChart q) (-1) a k (h ω) (h' ω))
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => h ω - smoothDist upperHalfPlaneOpens u₀) P)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = (Sec4.stripCounterflowChart q).2.1 ''
      fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean A (fun ω => h ω - smoothDist upperHalfPlaneOpens u₀) P g)
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ' ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω)) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
      g ω φ = ∫ z, (-couplingMean κ' (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω)
        ((Sec4.stripCounterflowChart q).1 z) + cfShift q a k z - u₀ z) * φ z := by
  classical
  set h0 : Ω → DistOn upperHalfPlaneOpens := fun ω => h ω - smoothDist upperHalfPlaneOpens u₀ with hh0_def
  have hℋ : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  have hmark := isHistoryAvoidanceLocal_stripInv_hull hq hκ' hC htr hu₀ hh0 hX hτ hτζ hA hAK
  have hE := hC.1
  obtain ⟨-, -, -, hX', hker⟩ := hC
  have hker' := hker τ hτ hτζ
  have hloc : IsLocalSet A h0 P := by
    refine Coupling.IsLocalSet.congr_set ?_ hAK
    exact WholeField.IsLocalSet.sub_dist (isLocalSet_stripInv_image hq hker'.1 htr)
      (WholeField.isHarmonicDistOn_smoothDist hu₀)
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := hloc.2.1
  have hKc := hker'.1.2.1
  have hτζ' : ∀ᵐ ω ∂P, (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hτζ.mono fun ω h => Coupling.coe_untopD_lt_zeta h
  set m : Ω → ℂ → ℝ := fun ω z => -couplingMean κ' (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω)
    ((Sec4.stripCounterflowChart q).1 z) + cfShift q a k z - u₀ z with hm_def
  have hmharm : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A ω) := by
    filter_upwards [hE.2.2.2.2, hτζ', hAK] with ω hp hlt hAω
    rw [hAω]
    exact harmonicOnNhd_cfMean hq a k
      (Sec7.SideHeight.harmonicOnNhd_couplingMean_rpath hp.2.2.2.1 hlt (hu ω).1) hu₀
  refine WangWu.ae_forall_apply_eq_of_forall_ae (m := m) hg.2.1 (hAc.mono fun ω h => h.2) hmharm fun φ => ?_
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hτζ] with ω hp hlt
      rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hlt
      exact ENNReal.not_lt_zero hlt
    filter_upwards [hF] with ω hω
    exact hω.elim
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ, hσ, -⟩ := WholeField.exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX)
    (B := B) (κ := κ') (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ') hseed
  -- the transported test function and the event `{supp φ ∩ A = ∅}` of `𝓕_τ`
  set ψ := cfBackTest hq φ with hψ_def
  have hφH : tsupport φ ⊆ H := φ.tsupport_subset
  have hCc : IsCompact ((Sec4.stripCounterflowChart q).1 '' tsupport φ) :=
    φ.hasCompactSupport.isCompact.image_of_continuousOn fun z hz =>
      (analyticAt_stripFwd (WangWu.ne_zero_of_mem_H (hφH hz))).continuousAt.continuousWithinAt
  have hCH : (Sec4.stripCounterflowChart q).1 '' tsupport φ ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact Sec4.stripCounterflowChart_fwd_mem_H hq (hφH hz)
  obtain ⟨G, hGm, hGiff⟩ := WholeField.exists_measurableSet_ae_iff_disjoint hE hX hσ hτ hτζ hCc hCH
  have hGiff' : ∀ᵐ ω ∂P, (ω ∈ G ↔ Disjoint (tsupport φ) (A ω)) := by
    filter_upwards [hGiff, hAK, hKc] with ω h1 h2 h3
    rw [h1, h2]
    exact disjoint_stripFwd_image_iff hq hφH h3.1
  -- the field identity `h⁰(φ) = −h′(ψ) + b`
  set b : ℝ := (∫ z, cfShift q a k z * φ z) - ∫ z, u₀ z * φ z with hb_def
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt
  have hfield : ∀ ω, h0 ω φ = -h' ω ψ + b := fun ω => by
    rw [hh0_def, sub_apply, apply_eq_neg_cfBackTest hq (htr ω) φ, Coupling.smoothDist_apply_eq hu₀c, hb_def]
    ring
  -- the kernel at every frequency
  have hfreq : ∀ c' : ℝ, ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => Complex.exp (Complex.I * ((c' * h0 ω' φ : ℝ) : ℂ)) | hτ.measurableSpace]) ω =
        Complex.exp (Complex.I * ((c' * ∫ z, m ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (c' ^ 2 * QuantumZipper.zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro c'
    have hk := hker'.2 u hu ((-c') • ψ)
    have hsm := condExp_smul (μ := P) (Complex.exp (Complex.I * ((c' * b : ℝ) : ℂ)))
      (fun ω' => Complex.exp (Complex.I * (h' ω' ((-c') • ψ) : ℂ))) hτ.measurableSpace
    have e1 : (fun ω' => Complex.exp (Complex.I * ((c' * h0 ω' φ : ℝ) : ℂ))) =
        Complex.exp (Complex.I * ((c' * b : ℝ) : ℂ)) •
          fun ω' => Complex.exp (Complex.I * (h' ω' ((-c') • ψ) : ℂ)) := by
      funext ω'
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, hfield, map_smul, smul_eq_mul]
      congr 1
      push_cast
      ring
    filter_upwards [hk, hsm, hAK, hE.2.2.2.2, hτζ', hmharm, hKc] with ω hkω hsmω hAω hp hsζ hmω hKω hdis
    have hdisK : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := by
      refine Disjoint.mono_left (tsupport_cfBackTest_subset hq φ) ?_
      rw [disjoint_stripFwd_image_iff hq hφH hKω.1, ← hAω]
      exact hdis
    have hdisc := hdisK.mono_left (WholeField.tsupport_smul_testOn_subset (-c') ψ)
    have hen := WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hp.2.2.2.1 hp.1 hsζ ψ hdisK
    have hcov : QuantumZipper.zeroGFFTestCov
        (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ψ ψ =
        QuantumZipper.zeroGFFTestCov (H \ A ω) φ φ := by
      rw [hAω]
      exact zeroGFFTestCov_cfBackTest hq hKω.2 φ
    -- the mean
    have hsupp : tsupport φ ⊆ H \ A ω := fun z hz => ⟨hφH hz, fun hzA => Set.disjoint_left.1 hdis hz hzA⟩
    have hmc : ContinuousOn (m ω) (H \ A ω) := fun z hz => (hmω z hz).1.continuousAt.continuousWithinAt
    set cm := couplingMean κ' (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) with hcm
    have hmean : ∫ z, m ω z * φ z = b - ∫ z, cm z * ψ z := by
      have hcmc : ContinuousOn (fun z => cm ((Sec4.stripCounterflowChart q).1 z)) (H \ A ω) := by
        have : ContinuousOn (fun z => -(m ω z - cfShift q a k z + u₀ z)) (H \ A ω) :=
          ((hmc.sub ((continuousOn_cfShift q a k).mono sdiff_subset)).add (hu₀c.mono sdiff_subset)).neg
        refine this.congr fun z _ => ?_
        simp only [hm_def, hcm]
        ring
      have hi1 : Integrable fun z => cm ((Sec4.stripCounterflowChart q).1 z) * φ z :=
        WholeField.integrable_mul_testOn hcmc φ hsupp
      have hi2 : Integrable fun z => cfShift q a k z * φ z :=
        WholeField.integrable_mul_testOn (continuousOn_cfShift q a k) φ hφH
      have hi3 : Integrable fun z => u₀ z * φ z := WholeField.integrable_mul_testOn hu₀c φ hφH
      have e2 : ∫ z, m ω z * φ z = (∫ z, cfShift q a k z * φ z) - (∫ z, u₀ z * φ z) -
          ∫ z, cm ((Sec4.stripCounterflowChart q).1 z) * φ z := by
        have hf : (fun z => m ω z * φ z) = fun z => (cfShift q a k z * φ z - u₀ z * φ z) -
            cm ((Sec4.stripCounterflowChart q).1 z) * φ z := by
          funext z
          simp only [hm_def, hcm]
          ring
        rw [hf, integral_sub (f := fun z => cfShift q a k z * φ z - u₀ z * φ z) (hi2.sub hi3) hi1,
          integral_sub hi2 hi3]
      rw [e2, hψ_def, integral_mul_cfBackTest, hb_def]
    rw [e1, hsmω, Pi.smul_apply, smul_eq_mul, hkω hdisc, WholeField.integral_mul_smul, FunLike.coe_smul,
      WholeField.loewnerGreenEnergy_smul, hen, hcov, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add,
      hmean]
    congr 1
    push_cast
    ring
  have k := Sec7.SideHeight.ae_condExp_germSigma_eq_of_freq hh0 hA hℋ hmark hAc φ hGm hGiff' hfreq
  have e := WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup hh0 hA hloc hℋ hmark hg φ
  filter_upwards [k, e] with ω hk he hsupp
  have hdis : Disjoint (tsupport φ) (A ω) := Set.disjoint_left.2 fun z hz hzA => (hsupp hz).2 hzA
  rw [he, hk hdis]

end InteractingSLE.Sec5.CrossRestart
