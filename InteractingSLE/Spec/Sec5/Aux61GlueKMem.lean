/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibKGlued
import InteractingSLE.Spec.Restart.DomainMarkovLocMain

/-!
# (F4′): the member identities of almost every fibre from projection independence on the glued space

Packet PROVE-AUX61-GLUEK (Theorem 1.2's Prop 5.1 (E1); `planning/handoffs/PROVE-AUX61-FIB2.md`, "What remains"
(F4′)). A fibre of the glued space is the regular conditional law `condDistrib Y Z μ (Z x)` of the code `Y` of the
restarted chart path and chart field given the retained history `Z`. `FibMembersRaw` asks, for every pair of rational
times `r < s` and every finite family `F` of rational closed balls in `ℍ`, that the law of the centred fibre field
over `D ∩ {s < life, ⋃F off the hull at s}` be projection-independent at `⋃F`, for **every** raw code event `D` at `r`.

* `refMean0`, `fibMean0 = refMean0 + q` (the fibre's mean at time `0`), `refExt_zero`;
* `integral_cexp_of_raw`, **`map_fibField_of_raw`**: under a law on the codes with the path facts and `FibKernelRaw`,
  the field has the law `fieldLaw0 (fibMean0 d)` (the kernel at the dyadic time `0`, where the hull is empty);
* `measurableSet_safeEv_fib`: the safe event is a raw code event;
* **`ae_fibMembersRaw_of_glued`**: if, on the glued space, the law of the chart field over every rectangle
  `{Z ∈ B'} ∩ {Y ∈ ratPi r T ∩ safeEv F s}` (`B' ⊆ B` a history event, `T` a finite family of rational generators of
  the raw code σ-algebra at `r`) is projection-independent at `⋃F`, then almost every fibre over `B` (with the path
  facts and `FibKernelRaw`) satisfies `FibMembersRaw`. Proof: countably many shift identities (rational combinations
  of the generating tests, Dirichlet approximations) pass to almost every fibre for every event of the generating
  π-system (`ae_forall_setIntegral_condDistrib_eq_zero₂`), hence for every raw code event at `r` (Dynkin); the landed
  `Restart.DomainMarkov.isProjIndepMeasure_of_shift` turns them into projection independence (the fibre law at time
  `0` is `fieldLaw0`); subtracting the harmonic mean keeps it (`IsProjIndepMeasure.map_sub`).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result; R77: no post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GlueK

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open Aux61Win (meanF IsCutoffOn)
open Aux61R2 (RefExt)
open Aux61Fib (FibCode FibData PathGood fibW fibΓ fibU fibField)
open Aux61FibK (FibKernelRaw FibMembersRaw centredFib codeFiltration ratPi)
open Sec7.PocketTraversal

universe u

/-! ### The fibre's law at time `0` -/

/-- The reference mean at time `0` of the data's word (the bounded harmonic extension of its boundary data). -/
def refMean0 (d : FibData) : ℂ → ℝ :=
  MartChar.meanExt d.κ (flowLineRhoL d.κ d.bR d.JR 0 0) (flowLineRhoR d.κ d.bR d.JR 0 0) 0
    (flowLineXL d.bR d.JR 0) (flowLineXR d.bR d.JR 0)

/-- **The fibre's mean at time `0`**: the reference mean plus the correction `q`. -/
def fibMean0 (d : FibData) (z : ℂ) : ℝ := refMean0 d z + d.q z

theorem refMean0_ext (d : FibData) : IsBoundedHarmonicExtension
    (forceBoundaryData d.κ (flowLineRhoL d.κ d.bR d.JR 0 0) (flowLineRhoR d.κ d.bR d.JR 0 0)
      (fun i => flowLineXL d.bR d.JR 0 i - 0) (fun j => flowLineXR d.bR d.JR 0 j - 0))
    (forceJumpSet (fun i => flowLineXL d.bR d.JR 0 i - 0) (fun j => flowLineXR d.bR d.JR 0 j - 0)) (refMean0 d) :=
  MartChar.isBoundedHarmonicExtension_meanExt _ _ _ 0 _ _

theorem harmonicOnNhd_fibMean0 (d : FibData) : InnerProductSpace.HarmonicOnNhd (fibMean0 d) H :=
  fun z hz => ((refMean0_ext d).1 z hz).add (d.q_harm z hz)

theorem continuousOn_fibMean0 (d : FibData) : ContinuousOn (fibMean0 d) H :=
  fun z hz => ((harmonicOnNhd_fibMean0 d z hz).1.continuousAt).continuousWithinAt

/-- The reference extension at time `0` of the decoded driver is the reference mean. -/
theorem refExt_zero (d : FibData) (ω : ULift.{u} FibCode) : RefExt d.κ d.bR d.JR fibW 0 ω (refMean0 d) := by
  have hF := Theorem15.isOrderedForceWord_flowLine d.bR d.JR 0
  have hc : ∀ ω : ULift.{u} FibCode, Continuous fun t => fibW t ω := fun ω =>
    Aux61Fib.FibCode.continuous_driver ω.down
  have hz : ∀ ω : ULift.{u} FibCode, fibW 0 ω = 0 := fun ω => Aux61Fib.FibCode.driver_zero ω.down
  have hL : (fun i => geomLW fibW (fun _ => flowLineXL d.bR d.JR 0) i 0 ω - fibW 0 ω) =
      fun i => flowLineXL d.bR d.JR 0 i - 0 := funext fun i => by
    rw [geomLW_zero hc hz (hF.2.1 i), hz ω]
  have hR : (fun j => geomRW fibW (fun _ => flowLineXR d.bR d.JR 0) j 0 ω - fibW 0 ω) =
      fun j => flowLineXR d.bR d.JR 0 j - 0 := funext fun j => by
    rw [geomRW_zero hc hz (hF.2.2.2 j), hz ω]
  unfold RefExt
  rw [hL, hR]
  exact refMean0_ext d

theorem dyT_zero : Restart.DomainMarkov.dyT 0 0 = 0 := by simp [Restart.DomainMarkov.dyT]

/-- **The integrated time-0 kernel of a code fibre**: `E[e^{i h(φ)}] = cfVal(∫ (refMean0 + q) φ, E_ℍ(φ))`
(`FibKernelRaw` at the dyadic time `0`, where `{0 < life}` is almost sure and the hull is empty). -/
theorem integral_cexp_of_raw (d : FibData) (P : Measure (ULift.{u} FibCode)) [IsProbabilityMeasure P]
    (hgood : ∀ᵐ s ∂P, PathGood d s.down) (hraw : FibKernelRaw d P) (φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (fibField ω φ : ℂ)) ∂P =
      cfVal (∫ z, fibMean0 d z * φ z) (QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens φ φ) := by
  obtain ⟨N, F, -, hbN, hF, -⟩ :=
    Aux61Cov.exists_cmCut_of_harmonic d.O₀_open d.q_harm d.q_zero d.buffer_compact d.buffer_real
  have hb : d.buffer ⊆ N := subset_closure.trans hbN
  have hu : ∀ ω, RefExt d.κ d.bR d.JR fibW (Restart.DomainMarkov.dyT 0 0) ω (refMean0 d) := fun ω => by
    rw [dyT_zero]; exact refExt_zero d ω
  have hker := hraw F N hF hb 0 0 (fun _ => refMean0 d) hu φ
  rw [dyT_zero] at hker
  have hpos : ∀ᵐ s ∂P, 0 < fibU s :=
    Aux61Fib.ae_life_pos P d.ℓ_zero (hgood.mono fun _ h => h.2.2.1)
  refine LocalExt.integral_eq_of_condExp_ae_eq_const ((Ito.nullAugmented codeFiltration.{u} P).le 0) ?_
  filter_upwards [hker, hpos] with ω hω hp
  have hw : Continuous (Ito.rpath (fibW · ω)) :=
    (Aux61Fib.FibCode.continuous_driver ω.down).comp continuous_real_toNNReal
  have hw0 : Ito.rpath (fibW · ω) 0 = 0 := by
    simp [Ito.rpath, Aux61Fib.FibCode.driver_zero ω.down]
  have hK0 : fwdHull (Ito.rpath (fibW · ω)) 0 = ∅ := QuantumZipper.RS.fwdHull_zero_eq_empty hw
  have hd : Disjoint (tsupport φ) (fwdHull (Ito.rpath (fibW · ω)) ((0 : ℝ≥0) : ℝ)) := by
    rw [NNReal.coe_zero, hK0]; exact disjoint_empty _
  rw [hω (by simpa using hp) hd]
  have hm := Aux61R2.integral_meanF_zero (κ := d.κ) (refMean0_ext d).1
    (d.q_harm.contDiffOn.continuousOn) (Fq := F) (Aux61Fib.FibCode.continuous_driver ω.down)
    (Aux61Fib.FibCode.driver_zero ω.down) φ
  rw [NNReal.coe_zero] at hm ⊢
  rw [hm, Coupling.MartMeans2.loewnerGreenEnergy_zero_eq hw0, Sec7.Lemma71J.loewnerGreenEnergy_const_zero]
  rfl

/-- **The law of the field of a code fibre** with the path facts and `FibKernelRaw` is `fieldLaw0 (fibMean0 d)`. -/
theorem map_fibField_of_raw (d : FibData) (P : Measure (ULift.{u} FibCode)) [IsProbabilityMeasure P]
    (hgood : ∀ᵐ s ∂P, PathGood d s.down) (hraw : FibKernelRaw d P) :
    P.map fibField = Coupling.fieldLaw0 (fibMean0 d) := by
  have hmc := continuousOn_fibMean0 d
  have hfm : Measurable (fibField.{u}) := Aux61Fib.FibCode.measurable_field.comp measurable_down
  refine Restart.DomainMarkov.map_eq_fieldLaw0_of_isZBGFFProcess hfm hmc ?_
  have href := Coupling.isZBGFFProcess_fieldLaw0 hmc
  have e₁ : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, fibMean0 d z * φ z =
      smoothDist upperHalfPlaneOpens (fibMean0 d) φ := fun φ => by
    rw [SupercriticalConformalCovariance.GM24.smoothDist_apply hmc]
    exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have eP : (fun φ ω => fibField ω φ - ∫ z, fibMean0 d z * φ z) = fun φ (ω : ULift.{u} FibCode) =>
      fibField ω φ - smoothDist upperHalfPlaneOpens (fibMean0 d) φ := by
    funext φ ω; rw [e₁ φ]
  have eR : (fun φ (x : DistOn upperHalfPlaneOpens) => x φ - ∫ z, fibMean0 d z * φ z) = fun φ x =>
      x φ - smoothDist upperHalfPlaneOpens (fibMean0 d) φ := by
    funext φ x; rw [e₁ φ]
  rw [eR] at href
  rw [eP]
  refine LocalExt.isZBGFFProcess_of_integral_cexp_eq (X := fibField) hfm _ (X' := fun x => x) _ href
    fun φ => ?_
  rw [← e₁ φ]
  set c : ℝ := ∫ z, fibMean0 d z * φ z
  have hsplit : ∀ y : ℝ, Complex.exp (Complex.I * ((y - c : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I * (c : ℂ))) * Complex.exp (Complex.I * (y : ℂ)) := fun y => by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp only [hsplit]
  rw [integral_const_mul, integral_const_mul, integral_cexp_of_raw d P hgood hraw φ,
    Coupling.integral_cexp_fieldLaw0 hmc φ, cfVal]
  congr 2
  push_cast
  ring

/-! ### The safe event on the codes -/

open Restart.DomainMarkov (safeEv safeU indK ballsOpen) in
/-- On the codes the safe event of `F` at `s` is the safe union of the indicator test of `⋃F`. -/
theorem safeEv_eq_safeU {F : Finset (ℚ × ℚ × ℚ)} (hFH : Coupling.ballsK F ⊆ H) (s : ℝ≥0) :
    safeEv fibW.{u} fibU F s = safeU fibW fibU univ (indK F) s := by
  ext ω
  rw [Restart.DomainMarkov.mem_safeU_indK_iff (W := fibW.{u}) (ζ := fibU) (ω := ω)
    (Aux61Fib.FibCode.continuous_driver ω.down).continuousOn (Aux61Fib.FibCode.driver_zero ω.down) hFH s]
  rfl

open Restart.DomainMarkov (safeEv) in
/-- **The safe event is a raw code event** at its time. -/
theorem measurableSet_safeEv_fib {F : Finset (ℚ × ℚ × ℚ)} (hFH : Coupling.ballsK F ⊆ H) (s : ℝ≥0) :
    MeasurableSet[codeFiltration.{u} s] (safeEv fibW.{u} fibU F s) := by
  rw [safeEv_eq_safeU hFH s]
  exact Restart.DomainMarkov.measurableSet_safeU_indK
    (Coupling.adaptedBefore_killedDriving_W Aux61Fib.isMeasurableKilledDriving_fib.{u})
    (fun ω => (Aux61Fib.FibCode.continuous_driver ω.down).continuousOn) hFH s

theorem toNNReal_nnratCast (r : ℚ≥0) : (((r : ℚ) : ℝ)).toNNReal = (r : ℝ≥0) := by
  rw [← NNReal.coe_inj, Real.coe_toNNReal _ (by positivity)]
  norm_cast

/-- The raw code σ-algebra at a rational time is generated by the rational π-system. -/
theorem codeFiltration_eq_generateFrom (r : ℚ≥0) :
    codeFiltration.{u} (r : ℝ≥0) =
      MeasurableSpace.generateFrom (range (ratPi fibW.{u} fibU (r : ℝ≥0))) :=
  (Aux61FibK.generateFrom_ratPi fibW fibU (fun s => Aux61Fib.FibCode.continuous_driver s.down)
    ⟨(r : ℚ), toNNReal_nnratCast r⟩).symm

theorem ratPi_empty (q : ℝ≥0) : ratPi fibW.{u} fibU q ∅ = univ := by
  simp [Aux61FibK.ratPi]

/-! ### The shift identities pass to almost every fibre -/

/-- The integrand of the shift identities: on the history event `B` and the code event `S`,
`e^{i h(Φ)} − c e^{i h(Ξ)}`. -/
def shiftInt {β : Type*} (B : Set β) (S : Set (ULift.{u} FibCode)) (c : ℂ) (Φ Ξ : TestOn upperHalfPlaneOpens)
    (zs : β × ULift.{u} FibCode) : ℂ :=
  B.indicator (fun _ => S.indicator (fun s => Complex.exp (Complex.I * (fibField s Φ : ℂ)) -
    c * Complex.exp (Complex.I * (fibField s Ξ : ℂ))) zs.2) zs.1

theorem measurable_cexp_fibField (Φ : TestOn upperHalfPlaneOpens) :
    Measurable fun s : ULift.{u} FibCode => Complex.exp (Complex.I * (fibField s Φ : ℂ)) :=
  Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    ((LQGMetric.measurable_distOn_apply Φ).comp (Aux61Fib.FibCode.measurable_field.comp measurable_down))))

theorem measurable_shiftInt {β : Type*} [MeasurableSpace β] {B : Set β} (hB : MeasurableSet B)
    {S : Set (ULift.{u} FibCode)} (hS : MeasurableSet S) (c : ℂ) (Φ Ξ : TestOn upperHalfPlaneOpens) :
    Measurable (shiftInt.{u} B S c Φ Ξ) := by
  have h1 : Measurable fun zs : β × ULift.{u} FibCode => S.indicator (fun s =>
      Complex.exp (Complex.I * (fibField s Φ : ℂ)) - c * Complex.exp (Complex.I * (fibField s Ξ : ℂ))) zs.2 :=
    (((measurable_cexp_fibField Φ).sub (measurable_const.mul (measurable_cexp_fibField Ξ))).indicator hS).comp
      measurable_snd
  have e : shiftInt.{u} B S c Φ Ξ = (Prod.fst ⁻¹' B).indicator fun zs => S.indicator (fun s =>
      Complex.exp (Complex.I * (fibField s Φ : ℂ)) - c * Complex.exp (Complex.I * (fibField s Ξ : ℂ))) zs.2 := by
    funext zs
    by_cases h : zs.1 ∈ B <;> simp [shiftInt, Set.indicator, h]
  rw [e]
  exact h1.indicator (measurable_fst hB)

theorem norm_shiftInt_le {β : Type*} (B : Set β) (S : Set (ULift.{u} FibCode)) (c : ℂ)
    (Φ Ξ : TestOn upperHalfPlaneOpens) (zs : β × ULift.{u} FibCode) : ‖shiftInt.{u} B S c Φ Ξ zs‖ ≤ 1 + ‖c‖ := by
  simp only [shiftInt, Set.indicator]
  split_ifs
  · refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal, mul_one]
  · simp only [norm_zero]; positivity
  · simp only [norm_zero]; positivity

/-- **The shift identities in almost every fibre**: if on the glued space
`∫_{Z ∈ B', Y ∈ ratPi r T ∩ S} e^{i h(Φ)} = c ∫_{…} e^{i h(Ξ)}` for every finite family `T` and every history event
`B' ⊆ B`, then for almost every `x` over `B` the same identity holds in the fibre for every raw code event at `r`. -/
theorem ae_shift_fibre {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {β : Type*} [MeasurableSpace β] {Z : X → β} (hZ : Measurable Z) {Y : X → FibCode} (hY : Measurable Y)
    {B : Set β} (hB : MeasurableSet B) {S : Set (ULift.{u} FibCode)} (hS : MeasurableSet S) (c : ℂ)
    (Φ Ξ : TestOn upperHalfPlaneOpens) (r : ℚ≥0)
    (hid : ∀ (T : Finset (ℚ × ℚ × ℚ)) (B' : Set β), MeasurableSet B' → B' ⊆ B →
      ∫ x in Z ⁻¹' B' ∩ (fun x => ULift.up.{u} (Y x)) ⁻¹' (ratPi fibW fibU (r : ℝ≥0) T ∩ S),
          Complex.exp (Complex.I * (fibField (ULift.up.{u} (Y x)) Φ : ℂ)) ∂μ =
        c * ∫ x in Z ⁻¹' B' ∩ (fun x => ULift.up.{u} (Y x)) ⁻¹' (ratPi fibW fibU (r : ℝ≥0) T ∩ S),
          Complex.exp (Complex.I * (fibField (ULift.up.{u} (Y x)) Ξ : ℂ)) ∂μ) :
    ∀ᵐ x ∂μ, Z x ∈ B → ∀ D : Set (ULift.{u} FibCode), MeasurableSet[codeFiltration.{u} (r : ℝ≥0)] D →
      ∫ s in D ∩ S, Complex.exp (Complex.I * (fibField s Φ : ℂ))
          ∂(condDistrib (fun x => ULift.up.{u} (Y x)) Z μ (Z x)) =
        c * ∫ s in D ∩ S, Complex.exp (Complex.I * (fibField s Ξ : ℂ))
          ∂(condDistrib (fun x => ULift.up.{u} (Y x)) Z μ (Z x)) := by
  set Y' : X → ULift.{u} FibCode := fun x => ULift.up (Y x) with hY'def
  have hY' : Measurable Y' := measurable_up.comp hY
  have hsig : codeFiltration.{u} (r : ℝ≥0) ≤ (inferInstance : MeasurableSpace (ULift.{u} FibCode)) :=
    codeFiltration.le _
  have h𝒜 : ∀ T : Finset (ℚ × ℚ × ℚ), MeasurableSet (ratPi fibW.{u} fibU (r : ℝ≥0) T) := fun T => by
    have h : MeasurableSet[MeasurableSpace.generateFrom (range (ratPi fibW.{u} fibU (r : ℝ≥0)))]
        (ratPi fibW fibU (r : ℝ≥0) T) := MeasurableSpace.measurableSet_generateFrom ⟨T, rfl⟩
    rw [← codeFiltration_eq_generateFrom] at h
    exact hsig _ h
  have hm := measurable_shiftInt.{u} (β := β) hB hS c Φ Ξ
  have hfm : ∀ Φ' : TestOn upperHalfPlaneOpens, Integrable
      (fun x => Complex.exp (Complex.I * (fibField (Y' x) Φ' : ℂ))) μ := fun Φ' =>
    Integrable.of_bound ((measurable_cexp_fibField Φ').comp hY').aestronglyMeasurable 1
      (ae_of_all _ fun x => (Complex.norm_exp_I_mul_ofReal _).le)
  -- the rectangle identities for every history event
  have H : ∀ (T : Finset (ℚ × ℚ × ℚ)) (B' : Set β), MeasurableSet B' →
      ∫ x in Z ⁻¹' B' ∩ Y' ⁻¹' ratPi fibW fibU (r : ℝ≥0) T, shiftInt.{u} B S c Φ Ξ (Z x, Y' x) ∂μ = 0 := by
    intro T B' hB'
    have e : (fun x => shiftInt.{u} B S c Φ Ξ (Z x, Y' x)) = (Z ⁻¹' B ∩ Y' ⁻¹' S).indicator fun x =>
        Complex.exp (Complex.I * (fibField (Y' x) Φ : ℂ)) - c * Complex.exp (Complex.I * (fibField (Y' x) Ξ : ℂ)) := by
      funext x
      simp only [shiftInt, Set.indicator, mem_inter_iff, mem_preimage]
      split_ifs <;> simp_all
    rw [e, setIntegral_indicator ((hZ hB).inter (hY' hS))]
    have eset : Z ⁻¹' B' ∩ Y' ⁻¹' ratPi fibW fibU (r : ℝ≥0) T ∩ (Z ⁻¹' B ∩ Y' ⁻¹' S) =
        Z ⁻¹' (B' ∩ B) ∩ Y' ⁻¹' (ratPi fibW fibU (r : ℝ≥0) T ∩ S) := by
      ext x; simp only [mem_inter_iff, mem_preimage]; tauto
    rw [eset, integral_sub (hfm Φ).integrableOn ((hfm Ξ).const_mul c).integrableOn, integral_const_mul,
      hid T (B' ∩ B) (hB'.inter hB) inter_subset_right, sub_self]
  have Huniv : ∀ B' : Set β, MeasurableSet B' → ∫ x in Z ⁻¹' B', shiftInt.{u} B S c Φ Ξ (Z x, Y' x) ∂μ = 0 := by
    intro B' hB'
    have := H ∅ B' hB'
    rwa [ratPi_empty, preimage_univ, inter_univ] at this
  have hfib := Aux61FibK.ae_forall_setIntegral_condDistrib_eq_zero₂ hZ hY' hm (norm_shiftInt_le B S c Φ Ξ) h𝒜
    (Aux61FibK.isPiSystem_ratPi _ _ _) H Huniv
  filter_upwards [hfib] with x hx hxB D hD
  rw [codeFiltration_eq_generateFrom] at hD
  have h0 := hx D hD
  have hDm : MeasurableSet D := by
    rw [← codeFiltration_eq_generateFrom] at hD
    exact hsig _ hD
  have e : (fun s => shiftInt.{u} B S c Φ Ξ (Z x, s)) = S.indicator fun s =>
      Complex.exp (Complex.I * (fibField s Φ : ℂ)) - c * Complex.exp (Complex.I * (fibField s Ξ : ℂ)) := by
    funext s
    simp only [shiftInt, Set.indicator_of_mem hxB]
  have hgm : ∀ Φ' : TestOn upperHalfPlaneOpens, Integrable
      (fun s : ULift.{u} FibCode => Complex.exp (Complex.I * (fibField s Φ' : ℂ)))
      (condDistrib Y' Z μ (Z x)) := fun Φ' =>
    Integrable.of_bound (measurable_cexp_fibField Φ').aestronglyMeasurable 1
      (ae_of_all _ fun s => (Complex.norm_exp_I_mul_ofReal _).le)
  rw [e, setIntegral_indicator hS, integral_sub (hgm Φ).integrableOn ((hgm Ξ).const_mul c).integrableOn,
    integral_const_mul, sub_eq_zero] at h0
  exact h0

/-! ### The member identities in almost every fibre -/

open Restart.DomainMarkov (safeEv ballsOpen) in
open Coupling (IsProjIndepMeasure projFactor) in
open LocalSets (lapTest) in
open Restart (RatComb ratComb) in
/-- **(F4′): `FibMembersRaw` in almost every fibre from projection independence on the glued space.** If for all
rational `r < s`, every finite family `F` of rational closed balls in `ℍ`, every finite family `T` of rational
generators and every history event `B' ⊆ B`, the law of the chart field over
`{Z ∈ B'} ∩ {Y ∈ ratPi r T ∩ safeEv F s}` is projection-independent at `⋃F` (the marked locality of the union on the
glued space at the rational fibre times), then almost every fibre over `B` that has the path facts and
`FibKernelRaw` satisfies `FibMembersRaw`. -/
theorem ae_fibMembersRaw_of_glued {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {β : Type*} [MeasurableSpace β] {Z : X → β} (hZ : Measurable Z) {Y : X → FibCode} (hY : Measurable Y)
    {B : Set β} (hB : MeasurableSet B) (d : β → FibData)
    (hgood : ∀ᵐ x ∂μ, Z x ∈ B → ∀ᵐ s ∂(condDistrib (fun x => ULift.up.{u} (Y x)) Z μ (Z x)),
      PathGood (d (Z x)) s.down)
    (hraw : ∀ᵐ x ∂μ, Z x ∈ B → FibKernelRaw (d (Z x)) (condDistrib (fun x => ULift.up.{u} (Y x)) Z μ (Z x)))
    (hloc : ∀ r s : ℚ≥0, r < s → ∀ F : Finset (ℚ × ℚ × ℚ), Coupling.ballsK F ⊆ H →
      ∀ (T : Finset (ℚ × ℚ × ℚ)) (B' : Set β), MeasurableSet B' → B' ⊆ B →
        IsProjIndepMeasure (ballsOpen F)
          ((μ.restrict (Z ⁻¹' B' ∩ (fun x => ULift.up.{u} (Y x)) ⁻¹'
            (ratPi fibW fibU (r : ℝ≥0) T ∩ safeEv fibW fibU F (s : ℝ≥0)))).map
              fun x => fibField (ULift.up.{u} (Y x)))) :
    ∀ᵐ x ∂μ, Z x ∈ B → FibMembersRaw (d (Z x)) (condDistrib (fun x => ULift.up.{u} (Y x)) Z μ (Z x)) := by
  set Y' : X → ULift.{u} FibCode := fun x => ULift.up (Y x) with hY'def
  have hY' : Measurable Y' := measurable_up.comp hY
  have hfm : Measurable (fibField.{u}) := Aux61Fib.FibCode.measurable_field.comp measurable_down
  have hVH : ∀ F : Finset (ℚ × ℚ × ℚ), Coupling.ballsK F ⊆ H → ((ballsOpen F : Opens ℂ) : Set ℂ) ⊆ H :=
    fun F hF z hz => hF (Coupling.ballsU_subset_ballsK F hz)
  -- Borel versions of the projections onto `H(⋃F)` and Dirichlet approximations, chosen once
  have hGex : ∀ F : Finset (ℚ × ℚ × ℚ), ∃ G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens,
      Coupling.ballsK F ⊆ H → Measurable G ∧
        GFF.IsMarkovDecomposition (ballsOpen F) upperHalfPlaneOpens id G (Coupling.zbLaw upperHalfPlaneOpens) := by
    intro F
    by_cases hF : Coupling.ballsK F ⊆ H
    · obtain ⟨G, hGm, hGd⟩ := Coupling.exists_markovMap_zbLaw (ballsOpen F) (hVH F hF)
      exact ⟨G, fun _ => ⟨hGm, hGd⟩⟩
    · exact ⟨id, fun h => absurd h hF⟩
  choose G hG using hGex
  have hfex : ∀ (F : Finset (ℚ × ℚ × ℚ)) (k : RatComb), ∃ f : ℕ → LQGMetric.MarkovZB.zsSub (Coupling.ballsU F),
      Coupling.ballsK F ⊆ H →
      Tendsto (fun m => QuantumZipper.K3.gradFeat (Coupling.ballsU F) (f m).1) atTop
        (𝓝 (QuantumZipper.Thm11Asm.covVec (Coupling.ballsU F) (ratComb upperHalfPlaneOpens k))) ∧
      ∀ᵐ g ∂Coupling.zbLaw upperHalfPlaneOpens,
        Tendsto (fun m => g (lapTest (ballsOpen F) (f m))) atTop (𝓝 (G F g (ratComb upperHalfPlaneOpens k))) := by
    intro F k
    by_cases hF : Coupling.ballsK F ⊆ H
    · obtain ⟨f, hf1, hf2⟩ := Coupling.exists_tendsto_ae_zbLaw (hG F hF).1 (hG F hF).2 (hVH F hF)
        (ratComb upperHalfPlaneOpens k)
      exact ⟨f, fun _ => ⟨hf1, hf2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hF⟩
  choose fam hfam using hfex
  -- the countably many shift identities in almost every fibre
  have hshift : ∀ᵐ x ∂μ, ∀ i : ℚ≥0 × ℚ≥0 × Finset (ℚ × ℚ × ℚ) × RatComb × ℕ,
      i.1 < i.2.1 → Coupling.ballsK i.2.2.1 ⊆ H → Z x ∈ B →
      ∀ D : Set (ULift.{u} FibCode), MeasurableSet[codeFiltration.{u} (i.1 : ℝ≥0)] D →
        ∫ s in D ∩ safeEv fibW fibU i.2.2.1 (i.2.1 : ℝ≥0),
            Complex.exp (Complex.I * (fibField s (ratComb upperHalfPlaneOpens i.2.2.2.1) : ℂ))
            ∂(condDistrib Y' Z μ (Z x)) =
          projFactor (ballsOpen i.2.2.1) (fam i.2.2.1 i.2.2.2.1 i.2.2.2.2)
              (ratComb upperHalfPlaneOpens i.2.2.2.1 - lapTest (ballsOpen i.2.2.1) (fam i.2.2.1 i.2.2.2.1 i.2.2.2.2)) *
            ∫ s in D ∩ safeEv fibW fibU i.2.2.1 (i.2.1 : ℝ≥0),
              Complex.exp (Complex.I * (fibField s (ratComb upperHalfPlaneOpens i.2.2.2.1 -
                lapTest (ballsOpen i.2.2.1) (fam i.2.2.1 i.2.2.2.1 i.2.2.2.2)) : ℂ))
              ∂(condDistrib Y' Z μ (Z x)) := by
    rw [ae_all_iff]
    rintro ⟨r, s, F, k, m⟩
    by_cases hrs : r < s
    swap
    · exact ae_of_all _ fun x h => absurd h hrs
    by_cases hF : Coupling.ballsK F ⊆ H
    swap
    · exact ae_of_all _ fun x _ h => absurd h hF
    set Φ := ratComb upperHalfPlaneOpens k
    set f := fam F k m
    have hS : MeasurableSet (safeEv fibW.{u} fibU F (s : ℝ≥0)) :=
      codeFiltration.le _ _ (measurableSet_safeEv_fib hF _)
    refine (ae_shift_fibre hZ hY hB hS _ Φ (Φ - lapTest (ballsOpen F) f) r ?_).mono
      fun x hx _ _ => hx
    intro T B' hB' hB'B
    have h := hloc r s hrs F hF T B' hB' hB'B f (Φ - lapTest (ballsOpen F) f)
    have hR : MeasurableSet (Z ⁻¹' B' ∩ Y' ⁻¹' (ratPi fibW fibU (r : ℝ≥0) T ∩ safeEv fibW fibU F (s : ℝ≥0))) := by
      refine (hZ hB').inter (hY' ((?_ : MeasurableSet (ratPi fibW.{u} fibU (r : ℝ≥0) T)).inter hS))
      have h' : MeasurableSet[MeasurableSpace.generateFrom (range (ratPi fibW.{u} fibU (r : ℝ≥0)))]
          (ratPi fibW fibU (r : ℝ≥0) T) := MeasurableSpace.measurableSet_generateFrom ⟨T, rfl⟩
      rw [← codeFiltration_eq_generateFrom] at h'
      exact codeFiltration.le _ _ h'
    have hcm : ∀ Φ' : TestOn upperHalfPlaneOpens, Measurable fun x : DistOn upperHalfPlaneOpens =>
        Complex.exp (Complex.I * (x Φ' : ℂ)) := fun Φ' =>
      Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        (LQGMetric.measurable_distOn_apply Φ')))
    have hfY : Measurable fun x => fibField.{u} (ULift.up.{u} (Y x)) := hfm.comp hY'
    rw [integral_map hfY.aemeasurable (hcm _).aestronglyMeasurable,
      integral_map hfY.aemeasurable (hcm _).aestronglyMeasurable,
      add_sub_cancel] at h
    exact h
  filter_upwards [hshift, hgood, hraw] with x hx hgx hrx hxB
  have hlaw := map_fibField_of_raw (d (Z x)) (condDistrib Y' Z μ (Z x)) (hgx hxB) (hrx hxB)
  intro r s hrs F hF
  refine ⟨safeEv fibW fibU F (s : ℝ≥0), codeFiltration.le _ _ (measurableSet_safeEv_fib hF _),
    Filter.EventuallyEq.rfl, fun D hD => ?_⟩
  have hpi := Restart.DomainMarkov.isProjIndepMeasure_of_shift (ν := condDistrib Y' Z μ (Z x)) hfm
    (harmonicOnNhd_fibMean0 (d (Z x))) hlaw (hVH F hF) (hG F hF).1 (hG F hF).2 (fam F)
    (fun k => (hfam F k hF).1) (fun k => (hfam F k hF).2)
    (D := D ∩ safeEv fibW fibU F (s : ℝ≥0)) fun k m => hx (r, s, F, k, m) hrs hF hxB D hD
  have hc := WholeField.isHarmonicDistOn_smoothDist (harmonicOnNhd_fibMean0 (d (Z x)))
  have e : ((condDistrib Y' Z μ (Z x)).restrict (D ∩ safeEv fibW fibU F (s : ℝ≥0))).map (centredFib (d (Z x))) =
      (((condDistrib Y' Z μ (Z x)).restrict (D ∩ safeEv fibW fibU F (s : ℝ≥0))).map fibField).map
        fun y => y - smoothDist upperHalfPlaneOpens (fibMean0 (d (Z x))) := by
    rw [Measure.map_map (Coupling.measurable_sub_distOnConst _) hfm]
    rfl
  rw [e]
  exact Restart.DomainMarkov.IsProjIndepMeasure.map_sub (hVH F hF) hpi hc

end InteractingSLE.Sec5.Aux61GlueK
