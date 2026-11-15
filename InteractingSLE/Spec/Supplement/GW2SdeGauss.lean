/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdStgEngine
import InteractingSLE.Spec.Coupling.MartMeans2Lemma71
import InteractingSLE.Spec.Sec7.Lemma71Joint
import InteractingSLE.Spec.Sec7.PocketTraversalCoords
import InteractingSLE.Spec.Restart.RetPlumbLine
import InteractingSLE.Spec.Restart.RetAux79Word
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Restart.ChartGauss

/-!
# K2's relative safe law at time `0`: the conditional Gaussian law of the stage field given its record

Packet PROVE-GW2-SDE. K2's (S) clause (`Restart.DomainMarkov.K2.HasSafeLaw`), read at relative time `0` on the
record events `{record ∈ A, 0 < stop}` (which lie in `canonFilt 0`), says that the conditional characteristic
functional of the relative field given the record is the time-`0` coupling functional of the typed flow-line word.
At time `0` the hull is empty, the coupling mean is the bounded harmonic extension of the force data of the typed word,
which is the mean of the word itself (`forceBoundaryData_zero_of_isFlowType`, `Sec4.forceBoundaryData_flowLine`), and
the Loewner–Green energy is the zero-boundary GFF covariance on `ℍ`. So K2's inputs already contain the time-`0`
conditional field law (the stage field is a GFF with the stage word's data given the stage record), and the SDE half
need not consume it separately:

* `cfAt_zero_eq_gaussCF`: the time-`0` coupling functional of the typed word is `gaussCF` of the word;
* **`ae_condExp_eq_gaussCF_of_relSafe`**: from `HasRelSafe` on every word type (and a positive stop on the record
  event), `E[exp(i Hr(φ)) | σ(rec)] = gaussCF (β rec) φ` almost surely on `{rec ∈ E}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Sde

open Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Restart.DomainMarkov Restart.DomainMarkov.K2
  Sec7.PocketTraversal

/-- **The time-`0` coupling functional of a typed word is the Gaussian functional of the word.** -/
theorem cfAt_zero_eq_gaussCF {κ : ℝ} (hκ : 0 < κ) {w : WordType} {β : RecData → BoundaryWord} (y : CanonSpace)
    (hw : wordType κ (β y.1) = w) (hs : (β y.1).IsSorted) (ψ : TestOn upperHalfPlaneOpens) :
    Coupling.cfAt κ canonDrv (bheProc κ (typedRhoL w) (typedRhoR w) canonDrv
        (geomLW canonDrv fun y => typedXL κ w (β y.1)) (geomRW canonDrv fun y => typedXR κ w (β y.1)))
        ψ 1 (fun _ => 0) y = gaussCF (β y.1) ψ := by
  have hW0 : ∀ y : CanonSpace, canonDrv 0 y = 0 := canonDrv_zero
  have hWc : ∀ y : CanonSpace, Continuous fun t => canonDrv t y := continuous_canonDrv
  have hw0 : (fun s : ℝ => canonDrv s.toNNReal y) 0 = 0 := by
    simp only [Real.toNNReal_zero, canonDrv_zero]
  have hft := isFlowType_typed (κ := κ) hw
  obtain ⟨hsL, hsR⟩ := RetAux79.isFlowType_signs hft
  have hL0 : ∀ i, geomLW canonDrv (fun y => typedXL κ w (β y.1)) i 0 y = typedXL κ w (β y.1) i := fun i =>
    geomLW_zero hWc hW0 (hsL i)
  have hR0 : ∀ j, geomRW canonDrv (fun y => typedXR κ w (β y.1)) j 0 y = typedXR κ w (β y.1) j := fun j =>
    geomRW_zero hWc hW0 (hsR j)
  -- the time-`0` mean is the word mean on `ℍ`
  have hu := isBoundedHarmonicExtension_bheProc (κ := κ) (ρL := typedRhoL w) (ρR := typedRhoR w) (W := canonDrv)
    (VL := geomLW canonDrv fun y => typedXL κ w (β y.1)) (VR := geomRW canonDrv fun y => typedXR κ w (β y.1)) y 0
  simp only [hL0, hR0, canonDrv_zero, sub_zero] at hu
  have hS : ({0} ∪ ((β y.1).jumps : Set ℝ)).Finite := (finite_singleton 0).union (β y.1).jumps.finite_toSet
  have hmean := RetAux79.eqOn_mean_add_of_forceBoundaryData hu hs 0 hS fun y' hy' => by
    have h0 : y' ≠ 0 := fun h => hy' (Or.inl h)
    have hJ : y' ∉ (β y.1).jumps := fun h => hy' (Or.inr h)
    rw [RetAux79.forceBoundaryData_zero_of_isFlowType hft,
      Sec4.forceBoundaryData_flowLine hκ (β y.1).isPiecewiseConstantBoundaryData h0 hJ, add_zero]
  have hint : (∫ z, couplingMean κ (fun s : ℝ => canonDrv s.toNNReal y) 0
      (bheProc κ (typedRhoL w) (typedRhoR w) canonDrv (geomLW canonDrv fun y => typedXL κ w (β y.1))
        (geomRW canonDrv fun y => typedXR κ w (β y.1)) y 0) z * ψ z) = ∫ z, (β y.1).mean z * ψ z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : ψ z = 0
    · simp only [hz, mul_zero]
    · have hzH : z ∈ H := ψ.tsupport_subset (subset_tsupport _ hz)
      have hz0 : z ≠ 0 := fun h => by
        rw [h] at hzH
        exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hzH)
      change couplingMean κ (fun s : ℝ => canonDrv s.toNNReal y) 0 _ z * ψ z = (β y.1).mean z * ψ z
      rw [Coupling.MartMeans2.couplingMean_zero (w := fun s : ℝ => canonDrv s.toNNReal y) κ hw0 _ hz0,
        hmean z hzH, add_zero]
  have henergy : loewnerGreenEnergy (fun s : ℝ => canonDrv s.toNNReal y) 0 ψ =
      QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens ψ ψ := by
    rw [Coupling.MartMeans2.loewnerGreenEnergy_zero_eq (w := fun s : ℝ => canonDrv s.toNNReal y) hw0,
      Sec7.Lemma71J.loewnerGreenEnergy_const_zero]
  simp only [Coupling.cfAt, gaussCF]
  congr 1
  push_cast
  ring_nf
  rw [hint, henergy]

/-- Removing the conditioning of a pushforward law on a set integral. -/
theorem setIntegral_cond_map {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] {P : Measure Ω}
    {Φ : Ω → Y} (hΦ : Measurable Φ) {T D : Set Y} (hT : MeasurableSet T) (hD : MeasurableSet D) {F : Y → ℂ}
    (hF : Measurable F) :
    ∫ y in D, F y ∂((P.map Φ)[|T]) = ((P.map Φ) T)⁻¹.toReal • ∫ ω in Φ ⁻¹' (D ∩ T), F (Φ ω) ∂P := by
  rw [ProbabilityTheory.cond, Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict hD,
    setIntegral_map (hD.inter hT) hF.aestronglyMeasurable hΦ.aemeasurable]

/-- **The time-`0` conditional field law from K2's inputs** (conditional helper: `HasRelSafe` on every word type and
a positive stop on the record event are hypotheses): almost surely on `{rec ∈ E}`,
`E[exp(i Hr(φ)) | σ(rec)] = gaussCF (β rec) φ`. -/
theorem ae_condExp_eq_gaussCF_of_relSafe {κ : ℝ} (hκ : 0 < κ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {β : RecData → BoundaryWord} (hβ : Measurable β) {E : Set RecData}
    (hE : MeasurableSet E) (hcount : (range fun r : RecData => wordType κ (β r)).Countable)
    (hsort : ∀ r ∈ E, (β r).IsSorted) {rec : Ω → RecData} (hrecm : Measurable rec)
    {Hr : Ω → DistOn upperHalfPlaneOpens} (hHr : Measurable Hr) {R : ℝ≥0 → Ω → ℝ} (hRm : ∀ t, Measurable (R t))
    {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    (hS : ∀ w : WordType, HasRelSafe κ w β E (P.map fun ω => (rec ω, relVar Hr R V ω)))
    (hV0 : ∀ᵐ ω ∂P, rec ω ∈ E → 0 < V ω) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, rec ω ∈ E →
      P[fun ω' => Complex.exp (Complex.I * (Hr ω' φ : ℂ)) | MeasurableSpace.comap rec inferInstance] ω =
        gaussCF (β (rec ω)) φ := by
  have hΦ : Measurable fun ω => (rec ω, relVar Hr R V ω) := hrecm.prodMk (measurable_relVar hHr hRm hVm)
  have h𝒢 : MeasurableSpace.comap rec inferInstance ≤ mΩ := hrecm.comap_le
  have hf_int : Integrable (fun ω => Complex.exp (Complex.I * (Hr ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hHr)
  have hgm : Measurable fun ω => gaussCF (β (rec ω)) φ := (measurable_gaussCF φ).comp (hβ.comp hrecm)
  have hg_int : Integrable (fun ω => gaussCF (β (rec ω)) φ) P :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => norm_gaussCF_le _ φ)
  have hF1 : Measurable fun y : CanonSpace => Complex.exp (Complex.I * (canonFld y φ : ℂ)) :=
    GFF.measurable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp measurable_canonFld)
  have hF2 : Measurable fun y : CanonSpace => gaussCF (β y.1) φ := (measurable_gaussCF φ).comp (hβ.comp measurable_fst)
  -- the set identity on every record event of one word type
  have hset : ∀ (w : WordType) (A : Set RecData), MeasurableSet A →
      ∫ ω in rec ⁻¹' (A ∩ (E ∩ {r | wordType κ (β r) = w})), Complex.exp (Complex.I * (Hr ω φ : ℂ)) ∂P =
        ∫ ω in rec ⁻¹' (A ∩ (E ∩ {r | wordType κ (β r) = w})), gaussCF (β (rec ω)) φ ∂P := by
    intro w A hA
    have hTm : MeasurableSet (typeEvent κ w β E) := measurableSet_typeEvent hβ hE
    have hD0 : MeasurableSet[canonFilt 0] (Prod.fst ⁻¹' A ∩ {y : CanonSpace | 0 < canonStp y}) := by
      refine (comap_fst_le_canonFilt 0 _ ⟨A, hA, rfl⟩).inter ?_
      have e : {y : CanonSpace | 0 < canonStp y} = {y | canonStp y ≤ ((0 : ℝ≥0) : ℝ≥0∞)}ᶜ := by
        ext y
        simp only [mem_ofPred_eq, mem_compl_iff, not_le, ENNReal.coe_zero]
      rw [e]
      exact (measurableSet_canonStp_le (le_refl (0 : ℝ≥0))).compl
    have hDm : MeasurableSet (Prod.fst ⁻¹' A ∩ {y : CanonSpace | 0 < canonStp y}) := canonFilt.le 0 _ hD0
    have hav : ∀ᵐ y ∂((P.map fun ω => (rec ω, relVar Hr R V ω))[|typeEvent κ w β E]),
        y ∈ Prod.fst ⁻¹' A ∩ {y : CanonSpace | 0 < canonStp y} → y ∈ univ ∧ y ∈ avoidSet canonDrv canonStp φ 0 := by
      refine Eventually.of_forall fun y hy => ⟨mem_univ _, ?_⟩
      have hc : Continuous fun s : ℝ => canonDrv s.toNNReal y :=
        (continuous_canonDrv y).comp continuous_real_toNNReal
      have h2 : 0 < canonStp y := hy.2
      refine ⟨by simpa only [ENNReal.coe_zero] using h2, ?_⟩
      rw [NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hc]
      exact disjoint_empty _
    have hlaw := (hS w).1 φ 0 _ hD0 hav
    have hlaw' : ∫ y in Prod.fst ⁻¹' A ∩ {y : CanonSpace | 0 < canonStp y},
        Complex.exp (Complex.I * (canonFld y φ : ℂ)) ∂((P.map fun ω => (rec ω, relVar Hr R V ω))[|typeEvent κ w β E]) =
        ∫ y in Prod.fst ⁻¹' A ∩ {y : CanonSpace | 0 < canonStp y}, gaussCF (β y.1) φ
          ∂((P.map fun ω => (rec ω, relVar Hr R V ω))[|typeEvent κ w β E]) := by
      rw [hlaw]
      refine setIntegral_congr_ae hDm ?_
      filter_upwards [ae_cond_mem hTm] with y hyT _
      exact cfAt_zero_eq_gaussCF hκ y hyT.2 (hsort _ hyT.1) φ
    rw [setIntegral_cond_map hΦ hTm hDm hF1, setIntegral_cond_map hΦ hTm hDm hF2] at hlaw'
    have hae : ((fun ω => (rec ω, relVar Hr R V ω)) ⁻¹'
        ((Prod.fst ⁻¹' A ∩ {y : CanonSpace | 0 < canonStp y}) ∩ typeEvent κ w β E) : Set Ω) =ᵐ[P]
        rec ⁻¹' (A ∩ (E ∩ {r | wordType κ (β r) = w})) := by
      filter_upwards [hV0] with ω hω
      apply propext
      simp only [typeEvent, mem_preimage, mem_inter_iff, mem_ofPred_eq, canonStp, relStp, relVar]
      constructor
      · rintro ⟨⟨hA', -⟩, hT⟩
        exact ⟨hA', hT⟩
      · rintro ⟨hA', hT⟩
        exact ⟨⟨hA', hω hT.1⟩, hT⟩
    rw [← setIntegral_congr_set hae, ← setIntegral_congr_set hae]
    by_cases h0 : (P.map fun ω => (rec ω, relVar Hr R V ω)) (typeEvent κ w β E) = 0
    · have hP0 : P ((fun ω => (rec ω, relVar Hr R V ω)) ⁻¹'
          ((Prod.fst ⁻¹' A ∩ {y : CanonSpace | 0 < canonStp y}) ∩ typeEvent κ w β E)) = 0 := by
        rw [← Measure.map_apply hΦ (hDm.inter hTm)]
        exact measure_mono_null inter_subset_right h0
      rw [setIntegral_measure_zero _ hP0, setIntegral_measure_zero _ hP0]
    · have hc : ((P.map fun ω => (rec ω, relVar Hr R V ω)) (typeEvent κ w β E))⁻¹.toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 (measure_ne_top _ _), ENNReal.inv_ne_top.2 h0⟩
      exact smul_right_injective ℂ hc hlaw'
  -- the conditional expectation on the record event of each word type
  have htype : ∀ w : WordType, ∀ᵐ ω ∂P, rec ω ∈ E ∩ {r | wordType κ (β r) = w} →
      P[fun ω' => Complex.exp (Complex.I * (Hr ω' φ : ℂ)) | MeasurableSpace.comap rec inferInstance] ω =
        gaussCF (β (rec ω)) φ := by
    intro w
    have hMs : MeasurableSet (E ∩ {r | wordType κ (β r) = w}) :=
      hE.inter ((measurable_wordType κ).comp hβ (measurableSet_singleton w))
    have hM : MeasurableSet[MeasurableSpace.comap rec inferInstance] (rec ⁻¹' (E ∩ {r | wordType κ (β r) = w})) :=
      ⟨_, hMs, rfl⟩
    have hgm' : Measurable[MeasurableSpace.comap rec inferInstance] fun ω => gaussCF (β (rec ω)) φ :=
      (measurable_gaussCF φ).comp (hβ.comp (comap_measurable rec))
    have h1 : (rec ⁻¹' (E ∩ {r | wordType κ (β r) = w})).indicator (fun ω => gaussCF (β (rec ω)) φ) =ᵐ[P]
        P[(rec ⁻¹' (E ∩ {r | wordType κ (β r) = w})).indicator
          (fun ω => Complex.exp (Complex.I * (Hr ω φ : ℂ))) | MeasurableSpace.comap rec inferInstance] := by
      refine ae_eq_condExp_of_forall_setIntegral_eq h𝒢 (hf_int.indicator (h𝒢 _ hM))
        (fun s _ _ => (hg_int.indicator (h𝒢 _ hM)).integrableOn) (fun s hs _ => ?_)
        ((hgm'.indicator hM).stronglyMeasurable.aestronglyMeasurable)
      obtain ⟨A, hA, rfl⟩ := hs
      rw [setIntegral_indicator (h𝒢 _ hM), setIntegral_indicator (h𝒢 _ hM), ← preimage_inter]
      exact (hset w A hA).symm
    have h2 := condExp_indicator hf_int hM
    filter_upwards [h1, h2] with ω h1 h2 hω
    have hω' : ω ∈ rec ⁻¹' (E ∩ {r | wordType κ (β r) = w}) := hω
    rw [indicator_of_mem hω', h2, indicator_of_mem hω'] at h1
    exact h1.symm
  have hall := (ae_ball_iff hcount).2 fun w _ => htype w
  filter_upwards [hall] with ω hω hωE
  exact hω _ ⟨rec ω, rfl⟩ ⟨hωE, rfl⟩

end InteractingSLE.Theorem14.GW2Sde
