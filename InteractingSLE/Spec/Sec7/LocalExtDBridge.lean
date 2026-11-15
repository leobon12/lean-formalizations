/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA2Joint
import InteractingSLE.Spec.Sec7.LocalExtCKernel

/-!
# Aux. lemma 55, step 5 (kernel half) from A2's named statement; the empty seed side

Packet PROVE-LOCEXT-D, items 1 and 4. Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L196–L210, p. 250).

* **`hasSrcJointKernel_of_srcJointKernelStatement`** (item 1): PROVE-LOCEXT-A2's named statement
  `SrcJointKernelStatement κ` gives PROVE-LOCEXT-C's input `HasSrcJointKernel` at every driving stop `τ ≤ S`, with the
  density `Z = srcDensity ∘ h` and a strictly positive, `𝓖_τ`-strongly measurable version `N` of `E[Z | 𝓖_τ]` that is
  almost surely `srcMart` at `τ`. The identity `E[Z | 𝓖_τ] = N_τ` is the statement at the test function `0`; the
  statement's explicit harmonic extension `bheAt` is replaced by an arbitrary one through uniqueness
  (`Impl.eqOn_of_isBoundedHarmonicExtension`) along good paths.
* **`condExp_recode_srcMeasure_eq_twoSeedKernel`**: hence, under `Q = srcMeasure` and given only
  `SrcJointKernelStatement κ`, the recoded field `h₀ = h + f − q` has the two-seed kernel at every driving stop `τ ≤ S`
  (`Q`-almost surely on `{supp φ ∩ K_τ = ∅}`).
* **`couplingMean_eq_of_weightL_eq_zero`**, **`couplingMean_eq_of_weightR_eq_zero`** (item 4): a two-seed mean whose
  seed side has weight `0` does not depend on the position of that side's mark, so the merged-seed kernel above (an
  empty seed side placed at the driver) is the kernel of a two-seed coupling whose empty side is any mark (the flow of
  `0^∓`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open LQGMetric (TestOn DistOn)

/-! ### Item 4: a seed side of weight zero -/

section EmptySeed

/-- A two-seed mean whose left side has weight `0` does not see the left position. -/
theorem meanHarmonic_weightL_zero (κ sR cL cL' cR : ℝ) (w : ℂ) :
    Ito.meanHarmonic κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => sR) (fun _ => cL) (fun _ => cR) w =
      Ito.meanHarmonic κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => sR) (fun _ => cL') (fun _ => cR) w := by
  simp only [Ito.meanHarmonic, zero_mul, Finset.sum_const_zero]

/-- A two-seed mean whose right side has weight `0` does not see the right position (the constant `π (1 + ∑ ρR)`
and the `arg` term both carry the weight). -/
theorem meanHarmonic_weightR_zero (κ sL cL cR cR' : ℝ) (w : ℂ) :
    Ito.meanHarmonic κ (fun _ : Fin 1 => sL) (fun _ : Fin 1 => (0 : ℝ)) (fun _ => cL) (fun _ => cR) w =
      Ito.meanHarmonic κ (fun _ : Fin 1 => sL) (fun _ : Fin 1 => (0 : ℝ)) (fun _ => cL) (fun _ => cR') w := by
  simp only [Ito.meanHarmonic, zero_mul, Finset.sum_const_zero]

/-- **Item 4 (left).** For the two-seed word with left weight `0`, the coupling mean does not depend on the left
position: bounded harmonic extensions of the data at `(cL, cR)` and `(cL', cR)` (`cL, cL' ≤ 0 ≤ cR`) give the same
mean at every `z` with `f_t(z) ∈ ℍ`. -/
theorem couplingMean_eq_of_weightL_eq_zero {κ sR cL cL' cR : ℝ} (hcL : cL ≤ 0) (hcL' : cL' ≤ 0) (hcR : 0 ≤ cR)
    {u u' : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => sR)
      (fun _ => cL) (fun _ => cR)) (forceJumpSet (fun _ : Fin 1 => cL) (fun _ : Fin 1 => cR)) u)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => sR)
      (fun _ => cL') (fun _ => cR)) (forceJumpSet (fun _ : Fin 1 => cL') (fun _ : Fin 1 => cR)) u')
    {w : ℝ → ℝ} {t : ℝ} {z : ℂ} (hz : fwdMap w t z ∈ H) :
    couplingMean κ w t u z = couplingMean κ w t u' z := by
  rw [Ito.couplingMean_eq_meanHarmonic (fun _ => hcL) (fun _ => hcR) hu hz,
    Ito.couplingMean_eq_meanHarmonic (fun _ => hcL') (fun _ => hcR) hu' hz, meanHarmonic_weightL_zero κ sR cL cL' cR]

/-- **Item 4 (right).** For the two-seed word with right weight `0`, the coupling mean does not depend on the right
position. -/
theorem couplingMean_eq_of_weightR_eq_zero {κ sL cL cR cR' : ℝ} (hcL : cL ≤ 0) (hcR : 0 ≤ cR) (hcR' : 0 ≤ cR')
    {u u' : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => sL) (fun _ : Fin 1 => (0 : ℝ))
      (fun _ => cL) (fun _ => cR)) (forceJumpSet (fun _ : Fin 1 => cL) (fun _ : Fin 1 => cR)) u)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => sL) (fun _ : Fin 1 => (0 : ℝ))
      (fun _ => cL) (fun _ => cR')) (forceJumpSet (fun _ : Fin 1 => cL) (fun _ : Fin 1 => cR')) u')
    {w : ℝ → ℝ} {t : ℝ} {z : ℂ} (hz : fwdMap w t z ∈ H) :
    couplingMean κ w t u z = couplingMean κ w t u' z := by
  rw [Ito.couplingMean_eq_meanHarmonic (fun _ => hcL) (fun _ => hcR) hu hz,
    Ito.couplingMean_eq_meanHarmonic (fun _ => hcL) (fun _ => hcR') hu' hz, meanHarmonic_weightR_zero κ sL cL cR cR']

/-- A seed side without seed marks has total seed weight `0`. -/
theorem seedSumL_eq_zero_of_forall_ne {nL : ℕ} {xL ρL : Fin nL → ℝ} (h : ∀ i, xL i ≠ 0) : seedSumL xL ρL = 0 := by
  rw [seedSumL_eq]
  exact Finset.sum_eq_zero fun i hi => absurd (Finset.mem_filter.1 hi).2 (h i)

/-- A seed side without seed marks has total seed weight `0`. -/
theorem seedSumR_eq_zero_of_forall_ne {nR : ℕ} {xR ρR : Fin nR → ℝ} (h : ∀ i, xR i ≠ 0) : seedSumR xR ρR = 0 := by
  rw [seedSumR_eq]
  exact Finset.sum_eq_zero fun i hi => absurd (Finset.mem_filter.1 hi).2 (h i)

end EmptySeed
/-! ### Item 1: `HasSrcJointKernel` from `SrcJointKernelStatement` -/

section Bridge

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- The density `Z = srcDensity ∘ h` is integrable. -/
theorem integrable_srcDensity (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    Integrable (fun ω => srcDensity κ ρL ρR hF hr (h ω)) P := by
  have hm : Measurable fun ω => srcDensity κ ρL ρR hF hr (h ω) := (measurable_srcDensity hF hr).comp hC.2.1
  refine (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (ae_of_all _ fun ω => (srcDensity_pos hF hr (h ω)).le)).1 ?_
  rw [lintegral_srcDensity hκ hC hF hr hseed]
  exact ENNReal.one_ne_top

/-- The coupling mean of two bounded harmonic extensions of the same force data agree at `z ∉ K_t` along a path
continuous on `[0, t]`. -/
theorem couplingMean_eq_of_isBoundedHarmonicExtension {w : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hw : ContinuousOn w (Icc 0 t)) {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {u u' : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) u)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) u')
    {z : ℂ} (hz : z ∈ H \ fwdHull w t) : couplingMean κ w t u z = couplingMean κ w t u' z := by
  have hfH : fwdMap w t z ∈ H :=
    Ito.im_fwdMap_pos_of_continuousOn ht hw hz.1 (Ito.exists_isForwardSol_of_mem ht hz) ⟨ht, le_rfl⟩
  have huF : Impl.IsBoundedHarmonicExtension (Impl.forceBoundaryData κ (Ito.weightWord ρL ρR) vL vR)
      (Impl.forceJumpSet (Ito.weightWord ρL ρR) vL vR) u := hu
  have huF' : Impl.IsBoundedHarmonicExtension (Impl.forceBoundaryData κ (Ito.weightWord ρL ρR) vL vR)
      (Impl.forceJumpSet (Ito.weightWord ρL ρR) vL vR) u' := hu'
  have he := Impl.eqOn_of_isBoundedHarmonicExtension
    (Impl.forceJumpSet_finite (Ito.weightWord ρL ρR) vL vR) huF huF' hfH
  rw [couplingMean, couplingMean, he]

/-- **Item 1: PROVE-LOCEXT-C's input `HasSrcJointKernel` from PROVE-LOCEXT-A2's named statement.** At every driving
stop `τ ≤ S` there is a strictly positive `𝓖_τ`-strongly measurable `N`, almost surely equal to `srcMart` at `τ`, such
that `HasSrcJointKernel` holds with the density `Z = srcDensity ∘ h` and `N`. -/
theorem hasSrcJointKernel_of_srcJointKernelStatement (hjk : SrcJointKernelStatement.{u} κ) (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) :
    ∃ N : Ω → ℝ, StronglyMeasurable[hτ.measurableSpace] N ∧ (∀ ω, 0 < N ω) ∧
      N =ᵐ[P] (fun ω => srcMart κ xL xR ρL ρR r W VL VR ((τ ω).untopD 0) ω) ∧
      HasSrcJointKernel κ xL xR ρL ρR r P W VL VR h τ hτ.measurableSpace
        (fun ω => srcDensity κ ρL ρR hF hr (h ω)) N := by
  have hP : IsProbabilityMeasure P := hC.1.1.isProbabilityMeasure'
  set m := hτ.measurableSpace with hmdef
  set Z : Ω → ℝ := fun ω => srcDensity κ ρL ρR hF hr (h ω) with hZdef
  set M : Ω → ℝ := fun ω => srcMart κ xL xR ρL ρR r W VL VR ((τ ω).untopD 0) ω with hMdef
  have hZi : Integrable Z P := integrable_srcDensity hκ hC hF hr hseed
  have hJ := hjk xL xR ρL ρR r hF hr hseed P 𝓕 W VL VR B ζ h hC hX τ hτ hτS
  -- the statement at the test function `0`: `E[Z | 𝓖_τ] = N_τ`
  have h0 := hJ 0
  have hZc : P[fun ω' => ((Z ω' : ℝ) : ℂ) | m] =ᵐ[P] fun ω => ((M ω : ℝ) : ℂ) := by
    filter_upwards [h0] with ω hω
    have hd : Disjoint (tsupport ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ))
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := by
      rw [show ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 from rfl, tsupport_zero]
      exact Set.empty_disjoint _
    have e := hω hd
    have e1 : (fun ω' => ((srcDensity κ ρL ρR hF hr (h ω') : ℝ) : ℂ) *
        Complex.exp (Complex.I * (h ω' 0 : ℂ))) = fun ω' => ((Z ω' : ℝ) : ℂ) := by
      funext ω'
      rw [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    rw [e1] at e
    rw [e]
    have e2 : ∀ g : ℂ → ℝ, (∫ z, g z * ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) z) = 0 := fun g => by
      simp only [show ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 from rfl, Pi.zero_apply, mul_zero,
        integral_zero]
    have e3 : loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
        ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 := by
      simp only [loewnerGreenEnergy, show ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 from rfl, Pi.zero_apply,
        zero_mul, integral_zero]
    rw [e2, e3, cfVal]
    simp [M]
  have hcomm := Complex.ofRealCLM.comp_condExp_comm (m := m) hZi
  have hZM : P[Z | m] =ᵐ[P] M := by
    filter_upwards [hcomm, hZc] with ω h1 h2
    have h3 : ((P[Z | m] ω : ℝ) : ℂ) = ((M ω : ℝ) : ℂ) := by
      rw [← h2]
      exact h1
    exact_mod_cast h3
  -- a strictly positive version
  set N : Ω → ℝ := fun ω => if 0 < P[Z | m] ω then P[Z | m] ω else 1 with hNdef
  have hgood := ae_isGoodPath hC.1 hκ
  have hMpos : ∀ ω, 0 < M ω := fun ω => Real.exp_pos _
  have hNm : StronglyMeasurable[m] N := by
    have hs : MeasurableSet[m] {ω | 0 < P[Z | m] ω} :=
      measurableSet_lt (measurable_const) stronglyMeasurable_condExp.measurable
    exact StronglyMeasurable.ite hs stronglyMeasurable_condExp stronglyMeasurable_const
  have hNM : N =ᵐ[P] M := by
    filter_upwards [hZM] with ω hω
    simp only [hNdef, hω, hMpos ω, ↓reduceIte]
  have hZN : P[Z | m] =ᵐ[P] N := hZM.trans hNM.symm
  refine ⟨N, hNm, fun ω => ?_, hNM, hZN, ?_⟩
  · simp only [hNdef]
    split_ifs with hpos
    · exact hpos
    · exact one_pos
  -- the kernel identity for an arbitrary bounded harmonic extension
  intro u hu φ
  filter_upwards [hJ φ, hNM, hgood, hτS] with ω hω hNω hg hτω hdis
  rw [hω hdis, hNω, cfVal]
  -- replace `bheAt` by `u ω` under the integral
  have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top localStopPath_le_stopHorizon) hτω
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
  set t : ℝ≥0 := (τ ω).untopD 0 with htdef
  have hta : t = a := by rw [htdef, ← ha, WithTop.untopD_coe]
  have htS : (t : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by rw [hta, ha]; exact hτω
  have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast htS) (localStopPath_lt hg.1 hF hr hseed hg.2)
  have hwc : ContinuousOn (fun s : ℝ => W s.toNNReal ω) (Icc 0 (t : ℝ)) := by
    refine hg.continuousOn_W.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    exact toNNReal_lt_of_mem_Icc htζ hs
  have huω : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω)
      (fun i => VR i t ω - W t ω)) (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω) :=
    hu ω
  have hpt : ∀ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) t
      (bheAt κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) z -
        greenPot κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) t z) * φ z =
      (couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω) z -
        greenPot κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) t z) * φ z := by
    intro z
    by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
    · have hy : z ∈ H \ fwdHull (fun s : ℝ => W s.toNNReal ω) t :=
        ⟨Coupling.tsupport_subset_H φ hz, fun hzK => hdis.ne_of_mem hz hzK rfl⟩
      rw [couplingMean_eq_of_isBoundedHarmonicExtension t.coe_nonneg hwc
        (isBoundedHarmonicExtension_bheAt κ ρL ρR _ _) huω hy]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  rw [integral_congr_ae (ae_of_all _ hpt)]

/-- **Step 5, kernel half, from A2's named statement.** Under `Q = srcMeasure = Z · P` and given only
`SrcJointKernelStatement κ`, the recoded field `h₀ = h + f − q` of (HL8) has at every driving stop `τ ≤ S` the frozen
kernel of the two-seed word (weights `(seedSumL, seedSumR)` at the merged seed positions), `Q`-almost surely on
`{supp φ ∩ K_τ = ∅}`. -/
theorem condExp_recode_srcMeasure_eq_twoSeedKernel (hjk : SrcJointKernelStatement.{u} κ) (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω)
    {u₂ : Ω → ℂ → ℝ}
    (hu₂ : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR)
        (fun _ => seedPosL xL W VL τ ω) (fun _ => seedPosR xR W VR τ ω))
      (forceJumpSet (fun _ : Fin 1 => seedPosL xL W VL τ ω) (fun _ : Fin 1 => seedPosR xR W VR τ ω)) (u₂ ω))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂(srcMeasure κ ρL ρR P hF hr h),
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      (srcMeasure κ ρL ρR P hF hr h)[fun ω' =>
          Complex.exp (Complex.I * (recode κ xL xR ρL ρR r (h ω') φ : ℂ)) | hτ.measurableSpace] ω =
        Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
            (u₂ ω) z * φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ)) := by
  obtain ⟨N, hNm, hNpos, -, hjoint⟩ :=
    hasSrcJointKernel_of_srcJointKernelStatement hjk hκ hC hF hr hseed hX hτ hτS
  have hP := condExp_recode_eq_twoSeedKernel hκ hC hF hr hseed hX hτ hτS
    ((measurable_srcDensity hF hr).comp hC.2.1) (fun ω => srcDensity_pos hF hr (h ω))
    (integrable_srcDensity hκ hC hF hr hseed) hNm hNpos hjoint hu₂ φ
  exact srcMeasure_absolutelyContinuous hF hr hP

end Bridge

end LocalExt

end InteractingSLE
