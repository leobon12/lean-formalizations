/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtKDens
import InteractingSLE.Spec.Sec7.LocalExtGStmt
import InteractingSLE.Spec.Sec7.LocalExtDGFF

/-!
# Aux. lemma 55 with a random seed word: the two-seed kernel under `Q`

Packet PROVE-LOCEXT-K (step 5 of `planning/handoffs/PROVE-LOCEXT-I.md`, kernel half). In the random-word setting of
`LocalExtKJoint`/`LocalExtKDens`:

* **`condExp_densW_mul_cexp`** (the conditional Cameron–Martin shift (HL3)–(HL4) with random positions): at a
  `𝓖`-stopping time `τ` before the local stop, almost surely on `{supp φ ∩ K_τ = ∅}`,
  `E[Z e^{i h(φ)} | 𝓖_τ] = N_τ · exp(i ∫ (𝔥_τ − G_{ℍ∖K_τ} v_c) φ − ½ E_τ(φ))`;
* `exists_pos_version_condExp_densW`: a strictly positive `𝓖_τ`-measurable version of `E[Z | 𝓖_τ] = N_τ`;
* **`condExp_recode_wordMeasure_eq_twoSeedKernel`**: under `Q = Z · P` the recoded field `h₀ = recode_{c}(h)` of (HL8)
  has, at every such `τ`, the **two-seed kernel** (weights the seed sums of `c`, positions the merged seed positions).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull greenH)
open LQGMetric (TestOn DistOn)

section Kernel

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)}

variable (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h)
  (hhm : Measurable h) (hc : Measurable[𝓖 0] c) (hadm : ∀ ω, IsAdmWord r (c ω))
  (hgood : ∀ᵐ ω ∂P, IsWordPath κ ρL ρR W VL VR B ζ c ω)
include hcf hhm hc hadm hgood

/-- **The conditional Cameron–Martin shift for the random word** (HL3)–(HL4): almost surely on
`{supp φ ∩ K_τ = ∅}`, `E[Z e^{i h(φ)} | 𝓖_τ] = N_τ · exp(i ∫ (𝔥_τ − G_{ℍ∖K_τ} v_c) φ − ½ E_τ(φ))`. -/
theorem condExp_densW_mul_cexp {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      P[fun ω' => ((densW κ ρL ρR r (c ω') (h ω') : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ)) |
          hτ.measurableSpace] ω =
        ((martW κ ρL ρR r W VL VR c ((τ ω).untopD 0) ω : ℝ) : ℂ) *
          cfVal (∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
              (bheProc κ ρL ρR W VL VR ω ((τ ω).untopD 0)) z -
              greenPot κ (c ω).1 (c ω).2 ρL ρR r (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) z) * φ z)
            (loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ) := by
  have hY₁ : Measurable fun ω => h ω φ := (LQGMetric.measurable_distOn_apply φ).comp hhm
  have hY₂ : Measurable (shiftPairW κ ρL ρR r c h) := measurable_shiftPairW hhm (hc.mono (𝓖.le 0) le_rfl)
  have hint : Integrable (fun ω => Real.exp (-shiftPairW κ ρL ρR r c h ω)) P := by
    simp_rw [exp_neg_shiftPairW]
    exact integrable_densW hcf hhm hc hadm hgood
  have key := ae_condExp_tilt_of_joint (m := hτ.measurableSpace) hτ.measurableSpace_le hY₁ hY₂ hint
    (condExp_cexp_joint_shift hcf hhm hc hadm hgood hτ hτS φ)
  have hfun : (fun ω' => ((densW κ ρL ρR r (c ω') (h ω') : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ))) =
      fun ω' => ((Real.exp (-shiftPairW κ ρL ρR r c h ω') : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ)) := by
    funext ω'
    rw [exp_neg_shiftPairW]
  rw [hfun]
  filter_upwards [key, hgood, hτS] with ω h1 hg hτω hD
  rw [h1 hD]
  have hx := hadm ω
  have hD' : Disjoint (tsupport φ) (fwdHull (Ito.rpath fun t => W t ω) ((τ ω).untopD 0 : ℝ≥0)) := hD
  have e1 := integral_sub_greenPot_mul_eq hg.1 hg.2.1 hx.1 hx.2 hg.2.2 (coe_untopD_le_localStopPath hτω) φ hD'
    (isBoundedHarmonicExtension_bheProc κ ρL ρR (W := W) (VL := VL) (VR := VR) ω ((τ ω).untopD 0))
  have hE := loewnerGreenEnergy_vSrc_eq_of_isGoodPath (κ := κ) (ρL := ρL) (ρR := ρR) hg.1 hg.2.1 hx.1 hx.2
    hg.2.2 (coe_untopD_le_localStopPath hτω)
  have e2 : srcEnergyAt κ (c ω).1 (c ω).2 ρL ρR r W ((τ ω).untopD 0) ω = srcNorm κ (c ω).1 (c ω).2 ρL ρR r -
      ∫ u in (0 : ℝ)..((τ ω).untopD 0 : ℝ≥0), srcDrift κ (c ω).1 (c ω).2 ρL ρR r
        (fun s : ℝ => W s.toNNReal ω) u ^ 2 := hE
  have e1' : (∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
        (bheProc κ ρL ρR W VL VR ω ((τ ω).untopD 0)) z -
        greenPot κ (c ω).1 (c ω).2 ρL ρR r (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) z) * φ z) =
      (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
        (bheProc κ ρL ρR W VL VR ω ((τ ω).untopD 0)) z * φ z) -
        greenCross (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ (vSrc κ (c ω).1 (c ω).2 ρL ρR r) := e1
  rw [e1', martW, srcMart, e2, centreW_of_adm κ ρL ρR r hx, normW_of_adm κ ρL ρR r hx]
  congr 3
  ring

/-- **A strictly positive `𝓖_τ`-measurable version of `E[Z | 𝓖_τ]`**, almost surely equal to `N_τ`. -/
theorem exists_pos_version_condExp_densW {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) :
    ∃ N : Ω → ℝ, StronglyMeasurable[hτ.measurableSpace] N ∧ (∀ ω, 0 < N ω) ∧
      N =ᵐ[P] (fun ω => martW κ ρL ρR r W VL VR c ((τ ω).untopD 0) ω) ∧
      P[fun ω => densW κ ρL ρR r (c ω) (h ω) | hτ.measurableSpace] =ᵐ[P] N := by
  set m := hτ.measurableSpace with hmdef
  set Z : Ω → ℝ := fun ω => densW κ ρL ρR r (c ω) (h ω) with hZdef
  set M : Ω → ℝ := fun ω => martW κ ρL ρR r W VL VR c ((τ ω).untopD 0) ω with hMdef
  have hZi : Integrable Z P := integrable_densW hcf hhm hc hadm hgood
  have h0 := condExp_densW_mul_cexp hcf hhm hc hadm hgood hτ hτS 0
  have hZc : P[fun ω' => ((Z ω' : ℝ) : ℂ) | m] =ᵐ[P] fun ω => ((M ω : ℝ) : ℂ) := by
    filter_upwards [h0] with ω hω
    have hd : Disjoint (tsupport ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ))
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := by
      rw [show ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 from rfl, tsupport_zero]
      exact Set.empty_disjoint _
    have e := hω hd
    have e1 : (fun ω' => ((densW κ ρL ρR r (c ω') (h ω') : ℝ) : ℂ) *
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
  set N : Ω → ℝ := fun ω => if 0 < P[Z | m] ω then P[Z | m] ω else 1 with hNdef
  have hMpos : ∀ ω, 0 < M ω := fun ω => martW_pos _ ω
  have hNm : StronglyMeasurable[m] N := by
    have hs : MeasurableSet[m] {ω | 0 < P[Z | m] ω} :=
      measurableSet_lt (measurable_const) stronglyMeasurable_condExp.measurable
    exact StronglyMeasurable.ite hs stronglyMeasurable_condExp stronglyMeasurable_const
  have hNM : N =ᵐ[P] M := by
    filter_upwards [hZM] with ω hω
    simp only [hNdef, hω, hMpos ω, ↓reduceIte]
  refine ⟨N, hNm, fun ω => ?_, hNM, hZM.trans hNM.symm⟩
  simp only [hNdef]
  split_ifs with hpos
  · exact hpos
  · exact one_pos

/-- **Step 5 (kernel half) for the random word**: under `Q = Z · P` (`wordMeasure`) the recoded field
`h₀ = recode_{c}(h)` has, at every `𝓖`-stopping time `τ` before the local stop and almost surely on
`{supp φ ∩ K_τ = ∅}`, the **two-seed kernel** `E_Q[e^{i h₀(φ)} | 𝓖_τ] = exp(i ∫ 𝔥⁰_τ φ − ½ E_τ(φ))`, `𝔥⁰_τ` the
coupling mean of the two-seed word of `c` (weights the seed sums, positions the merged seed positions). -/
theorem condExp_recode_wordMeasure_eq_twoSeedKernel {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) {u₂ : Ω → ℂ → ℝ}
    (hu₂ : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun _ : Fin 1 => seedSumL (c ω).1 ρL) (fun _ : Fin 1 => seedSumR (c ω).2 ρR)
        (fun _ => seedPosL (c ω).1 W VL τ ω) (fun _ => seedPosR (c ω).2 W VR τ ω))
      (forceJumpSet (fun _ : Fin 1 => seedPosL (c ω).1 W VL τ ω) (fun _ : Fin 1 => seedPosR (c ω).2 W VR τ ω))
      (u₂ ω))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      (wordMeasure κ ρL ρR r P c h)[fun ω' =>
          Complex.exp (Complex.I * (recode κ (c ω').1 (c ω').2 ρL ρR r (h ω') φ : ℂ)) | hτ.measurableSpace] ω =
        Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
            (u₂ ω) z * φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ)) := by
  have hm : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  have h0τ : 𝓖 0 ≤ hτ.measurableSpace := hτ.le_measurableSpace_of_const_le fun _ => bot_le
  have hcm : Measurable c := hc.mono (𝓖.le 0) le_rfl
  obtain ⟨N, hNm, hNpos, hNM, hN⟩ := exists_pos_version_condExp_densW hcf hhm hc hadm hgood hτ hτS
  set Z : Ω → ℝ := fun ω => densW κ ρL ρR r (c ω) (h ω) with hZdef
  have hZm : Measurable Z := measurable_densW_word hhm hcm
  have hZi : Integrable Z P := integrable_densW hcf hhm hc hadm hgood
  -- the random shift `c' = ∫ φ (f − q)` of the recoding
  set sh : Ω → ℝ := fun ω => ∫ z, recodeShift κ (c ω).1 (c ω).2 ρL ρR r z * φ z with hshdef
  have hshm : Measurable[hτ.measurableSpace] sh := by
    have hj : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ =>
        recodeShift κ p.1.1 p.1.2 ρL ρR r p.2 * φ p.2 :=
      (measurable_recodeShift_word κ ρL ρR r).mul ((φ.continuous.measurable).comp measurable_snd)
    have hg : Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) => ∫ z, recodeShift κ x.1 x.2 ρL ρR r z * φ z :=
      (hj.stronglyMeasurable.integral_prod_right (ν := (volume : Measure ℂ))).measurable
    exact (hg.comp hc).mono h0τ le_rfl
  set X : Ω → ℂ := fun ω' => Complex.exp (Complex.I * (recode κ (c ω').1 (c ω').2 ρL ρR r (h ω') φ : ℂ)) with hXdef
  have hrec : ∀ ω', recode κ (c ω').1 (c ω').2 ρL ρR r (h ω') φ = h ω' φ + sh ω' := fun ω' => by
    rw [recode_apply']
    congr 1
    exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have hXeq : ∀ ω', (Z ω') • X ω' = Complex.exp (Complex.I * (sh ω' : ℂ)) *
      (((Z ω' : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ))) := by
    intro ω'
    rw [hXdef]
    simp only
    rw [hrec ω', Complex.real_smul]
    push_cast
    rw [mul_add, Complex.exp_add]
    ring
  have hhφ : Measurable fun ω' => h ω' φ := (LQGMetric.measurable_distOn_apply φ).comp hhm
  have hXm : AEStronglyMeasurable X P := by
    have h1 : Measurable fun ω' => recode κ (c ω').1 (c ω').2 ρL ρR r (h ω') φ := by
      simp_rw [hrec]
      exact hhφ.add (hshm.mono hm le_rfl)
    exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp h1))).aestronglyMeasurable
  have hXb : ∀ ω', ‖X ω'‖ ≤ 1 := fun ω' => by
    rw [hXdef]
    exact (Complex.norm_exp_I_mul_ofReal _).le
  have hbayes := condExp_withDensity_ae_eq hm hZm (fun ω => (densW_pos κ ρL ρR r _ _).le) hZi hNm hNpos hN hXm hXb
  have hPQ : P ≪ wordMeasure κ ρL ρR r P c h := absolutelyContinuous_wordMeasure hhm hcm
  have hbayesP := hPQ.ae_le hbayes
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  have he : StronglyMeasurable[hτ.measurableSpace] fun ω => Complex.exp (Complex.I * (sh ω : ℂ)) :=
    (@GFF.measurable_exp_I_mul Ω hτ.measurableSpace _ hshm).stronglyMeasurable
  have hgi : Integrable (fun ω' => ((Z ω' : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ))) P := by
    refine hZi.ofReal.mul_bdd ?_ (Eventually.of_forall fun ω => (hnorm _).le)
    exact (GFF.measurable_exp_I_mul hhφ).aestronglyMeasurable
  have hpull : P[fun ω' => Z ω' • X ω' | hτ.measurableSpace] =ᵐ[P] fun ω => Complex.exp (Complex.I * (sh ω : ℂ)) *
      P[fun ω' => ((Z ω' : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ)) | hτ.measurableSpace] ω := by
    have e : (fun ω' => Z ω' • X ω') = fun ω' => (ContinuousLinearMap.mul ℝ ℂ)
        (Complex.exp (Complex.I * (sh ω' : ℂ))) (((Z ω' : ℝ) : ℂ) * Complex.exp (Complex.I * (h ω' φ : ℂ))) :=
      funext fun ω' => by rw [hXeq ω']; rfl
    rw [e]
    have hp := condExp_bilin_of_stronglyMeasurable_left (m := hτ.measurableSpace) (μ := P) (ContinuousLinearMap.mul ℝ ℂ) he (by
      refine hgi.bdd_mul (he.mono hm).aestronglyMeasurable (c := 1) (Eventually.of_forall fun ω => ?_)
      exact (hnorm _).le) hgi
    filter_upwards [hp] with ω hω
    rw [hω]
    rfl
  have hJ := condExp_densW_mul_cexp hcf hhm hc hadm hgood hτ hτS φ
  filter_upwards [hbayesP, hpull, hJ, hgood, hτS, hNM] with ω hb hp hj hg hτω hNω hdis
  rw [show wordMeasure κ ρL ρR r P c h = P.withDensity fun ω => ENNReal.ofReal (Z ω) from rfl, hb, hp, hj hdis]
  have hx := hadm ω
  have hg' : IsGoodPath κ (c ω).1 (c ω).2 ρL ρR W VL VR B ζ ω := ⟨hg.1, hg.2.1⟩
  -- the stop is finite and before the lifetime
  have hne : τ ω ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top localStopPath_le_stopHorizon) hτω
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
  set t : ℝ≥0 := (τ ω).untopD 0 with htdef
  have hta : t = a := by rw [htdef, ← ha, WithTop.untopD_coe]
  have htS : (t : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by rw [hta, ha]; exact hτω
  have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast htS) (hg.localStopPath_lt hx)
  have hpu := hg'.isSLEPathUpTo
  have hwc : ContinuousOn (Ito.rpath fun t => W t ω) (Icc 0 (t : ℝ)) := by
    refine hg'.continuousOn_W.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    exact toNNReal_lt_of_mem_Icc htζ hs
  -- the merged seed positions
  have hcL : seedPosL (c ω).1 W VL τ ω ≤ 0 := by
    unfold seedPosL seedVal
    split_ifs with hs
    · exact sub_nonpos.2 (hpu.vL_le_w htζ _)
    · exact le_rfl
  have hcR : 0 ≤ seedPosR (c ω).2 W VR τ ω := by
    unfold seedPosR seedVal
    split_ifs with hs
    · exact sub_nonneg.2 (hpu.w_le_vR htζ _)
    · exact le_rfl
  have hcL' : ∀ i, (c ω).1 i = 0 → VL i t ω - W t ω = seedPosL (c ω).1 W VL τ ω := fun i hi =>
    (seedVal_of_eq_zero (v := cposL W VL τ ω) (w := 0) (fun a b ha hb => by
      show VL a t ω - W t ω = VL b t ω - W t ω
      rw [vL_eq_vL_of_xL_eq_zero hpu ha hb htζ]) hi).symm
  have hcR' : ∀ j, (c ω).2 j = 0 → VR j t ω - W t ω = seedPosR (c ω).2 W VR τ ω := fun j hj =>
    (seedVal_of_eq_zero (v := cposR W VR τ ω) (w := 0) (fun a b ha hb => by
      show VR a t ω - W t ω = VR b t ω - W t ω
      rw [vR_eq_vR_of_xR_eq_zero hpu ha hb htζ]) hj).symm
  -- (HL9) integrated against `φ`
  have hpt : ∀ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (bheProc κ ρL ρR W VL VR ω t) z -
      greenPot κ (c ω).1 (c ω).2 ρL ρR r (fun s : ℝ => W s.toNNReal ω) t z) * φ z =
      couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u₂ ω) z * φ z -
        recodeShift κ (c ω).1 (c ω).2 ρL ρR r z * φ z := by
    intro z
    by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
    · have hy : z ∈ H \ fwdHull (Ito.rpath fun t => W t ω) t :=
        ⟨Coupling.tsupport_subset_H φ hz, fun hzK => hdis.ne_of_mem hz hzK rfl⟩
      have h9 : couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (bheProc κ ρL ρR W VL VR ω t) z -
          greenPot κ (c ω).1 (c ω).2 ρL ρR r (fun s : ℝ => W s.toNNReal ω) t z +
            fCut κ (c ω).1 (c ω).2 ρL ρR r z - qExt κ (c ω).1 (c ω).2 ρL ρR z =
          couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u₂ ω) z :=
        couplingMean_sub_greenPot_add_eq (w := fun t => W t ω) (vL := fun i t => VL i t ω)
          (vR := fun i t => VR i t ω) hg.1 hg.2.1 hx.1 hx.2 hg.2.2 htS htζ hy
          (isBoundedHarmonicExtension_bheProc κ ρL ρR ω t) hcL hcR hcL' hcR' (hu₂ ω)
      rw [recodeShift, ← h9]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hz]
      ring
  have hint1 : Integrable fun z => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u₂ ω) z * φ z :=
    integrable_couplingMean_mul (κ := κ) hwc (hu₂ ω).1 hdis
  have hint2 : Integrable fun z => recodeShift κ (c ω).1 (c ω).2 ρL ρR r z * φ z := by
    have h1 := SupercriticalConformalCovariance.GM24.integrable_test_mul
      (continuousOn_recodeShift' κ ρL ρR r (c ω).1 (c ω).2) φ
    exact h1.congr (ae_of_all _ fun z => mul_comm _ _)
  have key : (∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (bheProc κ ρL ρR W VL VR ω t) z -
      greenPot κ (c ω).1 (c ω).2 ρL ρR r (fun s : ℝ => W s.toNNReal ω) t z) * φ z) + sh ω =
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u₂ ω) z * φ z := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_sub hint1 hint2, hshdef]
    ring
  rw [← key, Complex.real_smul, hNω, martW]
  have hN0 : ((srcMart κ (c ω).1 (c ω).2 ρL ρR r W VL VR t ω : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  have e : Complex.exp (Complex.I * (((∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) t
      (bheProc κ ρL ρR W VL VR ω t) z - greenPot κ (c ω).1 (c ω).2 ρL ρR r (fun s : ℝ => W s.toNNReal ω) t z) *
        φ z) + sh ω : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) t φ : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (sh ω : ℂ)) * cfVal (∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) t
        (bheProc κ ρL ρR W VL VR ω t) z - greenPot κ (c ω).1 (c ω).2 ρL ρR r (fun s : ℝ => W s.toNNReal ω) t z) *
          φ z) (loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) t φ) := by
    rw [cfVal, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  push_cast
  field_simp

/-- **The two-seed GFF law at time `0` under `Q`** ((E3) for the random word): if the seed sums of `c` are almost surely
`sL, sR`, then `h₀ − 𝔥⁰₀` is a zero-boundary GFF process under `Q = Z · P` for every bounded harmonic extension `𝔥⁰₀` of
the two-seed data at time `0`. The identification of the law uses any reference zero-boundary GFF process with the same
characteristic functional. -/
theorem isZBGFFProcess_recode_wordMeasure {sL sR : ℝ}
    (hsum : ∀ᵐ ω ∂P, seedSumL (c ω).1 ρL = sL ∧ seedSumR (c ω).2 ρR = sR) {u₂ : ℂ → ℝ}
    (hu₂ : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => sL) (fun _ : Fin 1 => sR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₂)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {X' : Ω' → DistOn upperHalfPlaneOpens}
    (m' : DistOn upperHalfPlaneOpens) (href : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => X' ω φ - m' φ) P')
    (hrefcf : ∀ φ : TestOn upperHalfPlaneOpens, ∫ ω, Complex.exp (Complex.I * ((X' ω φ - m' φ : ℝ) : ℂ)) ∂P' =
      ((Real.exp (-(1 / 2) * loewnerGreenEnergy (fun _ => 0) 0 φ) : ℝ) : ℂ)) :
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens
      (fun φ ω => recode κ (c ω).1 (c ω).2 ρL ρR r (h ω) φ - ∫ z, u₂ z * φ z) (wordMeasure κ ρL ρR r P c h) := by
  have hcm : Measurable c := hc.mono (𝓖.le 0) le_rfl
  have hQ := isProbabilityMeasure_wordMeasure hcf hhm hc hadm hgood (r := r)
  have hQP : wordMeasure κ ρL ρR r P c h ≪ P := wordMeasure_absolutelyContinuous
  have hgoodQ := hQP.ae_le hgood
  have hsumQ := hQP.ae_le hsum
  have hu₂c : ContinuousOn u₂ H := continuousOn_of_isBoundedHarmonicExtension hu₂
  have e₁ : ∀ (u : ℂ → ℝ), ContinuousOn u H → ∀ φ : TestOn upperHalfPlaneOpens,
      ∫ z, u z * φ z = SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u φ := fun u hu φ => by
    rw [SupercriticalConformalCovariance.GM24.smoothDist_apply hu]
    exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have eQ : (fun φ ω => recode κ (c ω).1 (c ω).2 ρL ρR r (h ω) φ - ∫ z, u₂ z * φ z) = fun φ ω =>
      recode κ (c ω).1 (c ω).2 ρL ρR r (h ω) φ -
        SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₂ φ := by
    funext φ ω; rw [e₁ u₂ hu₂c φ]
  have hXm : Measurable fun ω => recode κ (c ω).1 (c ω).2 ρL ρR r (h ω) := by
    have h1 := (measurable_recode_word (nL := nL) (nR := nR) κ ρL ρR r).comp (hcm.prodMk hhm)
    exact h1
  rw [eQ]
  refine isZBGFFProcess_of_integral_cexp_eq hXm _ m' href fun φ => ?_
  rw [hrefcf φ, ← e₁ u₂ hu₂c φ]
  -- the kernel at `τ = 0`
  set τ : Ω → WithTop ℝ≥0 := fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0) with hτdef
  have hτ : IsStoppingTime 𝓖 τ := isStoppingTime_const _ _
  set u₂' : Ω → ℂ → ℝ := fun ω => Impl.forceExt κ (Ito.weightWord (fun _ : Fin 1 => seedSumL (c ω).1 ρL)
    (fun _ : Fin 1 => seedSumR (c ω).2 ρR)) (fun _ => seedPosL (c ω).1 W VL τ ω)
      (fun _ => seedPosR (c ω).2 W VR τ ω) with hu₂'def
  have hu₂' : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun _ : Fin 1 => seedSumL (c ω).1 ρL) (fun _ : Fin 1 => seedSumR (c ω).2 ρR)
        (fun _ => seedPosL (c ω).1 W VL τ ω) (fun _ => seedPosR (c ω).2 W VR τ ω))
      (forceJumpSet (fun _ : Fin 1 => seedPosL (c ω).1 W VL τ ω) (fun _ : Fin 1 => seedPosR (c ω).2 W VR τ ω))
      (u₂' ω) :=
    fun ω => Impl.isBoundedHarmonicExtension_forceExt κ _ _ _
  have hk := condExp_recode_wordMeasure_eq_twoSeedKernel hcf hhm hc hadm hgood hτ
    (ae_of_all _ fun _ => zero_le) hu₂' φ
  set cst : ℂ := Complex.exp (Complex.I * ((∫ z, u₂ z * φ z : ℝ) : ℂ) -
    (((1 / 2 : ℝ) * loewnerGreenEnergy (fun _ => 0) 0 φ : ℝ) : ℂ)) with hcdef
  have hcond : (wordMeasure κ ρL ρR r P c h)[fun ω => Complex.exp (Complex.I *
      (recode κ (c ω).1 (c ω).2 ρL ρR r (h ω) φ : ℂ)) | hτ.measurableSpace] =ᵐ[wordMeasure κ ρL ρR r P c h]
        fun _ => cst := by
    filter_upwards [hQP.ae_le hk, hgoodQ, hsumQ] with ω hω hg hs
    have hg' : IsGoodPath κ (c ω).1 (c ω).2 ρL ρR W VL VR B ζ ω := ⟨hg.1, hg.2.1⟩
    have hdis : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (((τ ω).untopD 0 : ℝ≥0) : ℝ)) := by
      rw [hτdef, WithTop.untopD_coe, hg.fwdHull_zero (hadm ω)]
      exact disjoint_empty _
    rw [hω hdis, hcdef]
    have hpu := hg'.isSLEPathUpTo
    have hw0 : W 0 ω = 0 := hpu.w_zero
    have hw0' : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by simpa using hw0
    obtain ⟨hsL, hsR⟩ := seedPos_zero_of_isGoodPath (κ := κ) (ρL := ρL) (ρR := ρR) hg'
    simp only [hτdef, WithTop.untopD_coe, NNReal.coe_zero]
    rw [Coupling.MartMeans2.loewnerGreenEnergy_zero_eq hw0' φ]
    congr 4
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
    · have hzH : z ∈ H := Coupling.tsupport_subset_H φ hz
      have hz0 : z ≠ 0 := fun h0 => by
        have : (0 : ℝ) < z.im := hzH
        rw [h0, Complex.zero_im] at this; exact lt_irrefl _ this
      rw [Coupling.MartMeans2.couplingMean_zero κ (w := fun s : ℝ => W s.toNNReal ω) hw0' (u₂' ω) hz0]
      have h1 : Impl.IsBoundedHarmonicExtension (Impl.forceBoundaryData κ (Ito.weightWord
          (fun _ : Fin 1 => sL) (fun _ : Fin 1 => sR)) LP.twoSeedXL LP.twoSeedXR)
          (Impl.forceJumpSet (Ito.weightWord (fun _ : Fin 1 => sL) (fun _ : Fin 1 => sR))
            LP.twoSeedXL LP.twoSeedXR) (u₂' ω) := by
        have := hu₂' ω
        rw [hτdef] at this
        simp only [hsL, hsR, hs.1, hs.2] at this
        exact this
      have h2 : Impl.IsBoundedHarmonicExtension (Impl.forceBoundaryData κ (Ito.weightWord
          (fun _ : Fin 1 => sL) (fun _ : Fin 1 => sR)) LP.twoSeedXL LP.twoSeedXR)
          (Impl.forceJumpSet (Ito.weightWord (fun _ : Fin 1 => sL) (fun _ : Fin 1 => sR))
            LP.twoSeedXL LP.twoSeedXR) u₂ := hu₂
      rw [Impl.eqOn_of_isBoundedHarmonicExtension (Impl.forceJumpSet_finite _ _ _) h2 h1 hzH]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  have hI := integral_eq_of_condExp_ae_eq_const hτ.measurableSpace_le hcond
  have e : (fun ω => Complex.exp (Complex.I * ((recode κ (c ω).1 (c ω).2 ρL ρR r (h ω) φ -
      ∫ z, u₂ z * φ z : ℝ) : ℂ))) = fun ω => Complex.exp (-(Complex.I * ((∫ z, u₂ z * φ z : ℝ) : ℂ))) *
        Complex.exp (Complex.I * (recode κ (c ω).1 (c ω).2 ρL ρR r (h ω) φ : ℂ)) := by
    funext ω
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e, integral_const_mul, hI, hcdef, ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

end Kernel

end LocalExt

end InteractingSLE
