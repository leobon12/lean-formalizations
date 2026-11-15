/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2StlThr
import InteractingSLE.Spec.Supplement.BW1InInt

/-!
# GW2's stage lines, part 2: the integrability clause at a stage

Packet PROVE-GW2-STAGEMEAN, stage-lines round (targets of PROVE-GW2-SDE's `GW2Sde.StageInst.LinesLocal`). The
integrability clause `LinesLocal.int` (RELDET's `hint`) asks that every pairing of the stage field be integrable under
the joint law of the record and the relative variable conditioned on the record event of a type. BW1 proved it for
its relative field (`BW1In.integrable_canonFld_bw`); the argument only uses that, conditionally on a σ-algebra for
which the record is measurable, the field is a GFF whose boundary data are bounded uniformly on the record event:

* **`integrable_canonFld_of_condGFF`**: for ANY record `rec`, word map `β`, record event `E`, field `Hr`, driver `R`
  and stop `V`: if `rec` is `𝒢`-measurable and, for almost every `ω₀` with `rec ω₀ ∈ E`, `Hr` is under
  `condExpKernel P 𝒢 ω₀` a GFF with piecewise-constant data bounded by `M`, the clause holds;
* `integrable_canonFld_of_condGFF_word`: the same with the data of the word `β(rec ω₀)` itself;
* **`StageInst.lines_int`**: `LinesLocal.int` of a stage instance from the conditional GFF law of the stage field
  given any σ-algebra for which the augmented stage record is measurable.

The disintegration is `KernelTower.lintegral_lintegral_condExpKernel`; the uniform Gaussian bound is
`BW1In.lintegral_enorm_apply_le_of_isGFF`. Conditional helper with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Stl

open Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop GW2Rd GW2Sde GW2TipSystem
  GW2TipSystem.RootC24

section Generic

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {κ : ℝ} {rec : Ω → RecData} {β : RecData → BoundaryWord} {E : Set RecData}
  {Hr : Ω → DistOn upperHalfPlaneOpens} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- **The integrability clause from a conditional GFF law with uniformly bounded data.** -/
theorem integrable_canonFld_of_condGFF (h𝒢 : 𝒢 ≤ mΩ) (hrec : Measurable[𝒢] rec) (hβ : Measurable β)
    (hE : MeasurableSet E) (hHr : Measurable Hr) (hRm : ∀ t, Measurable (R t)) (hVm : Measurable V) {M : ℝ}
    (hM0 : 0 ≤ M)
    (hgff : ∀ᵐ ω₀ ∂P, rec ω₀ ∈ E → ∃ (b : ℝ → ℝ) (J : Finset ℝ), IsPiecewiseConstantBoundaryData b J ∧
      (∀ y ∉ J, |b y| ≤ M) ∧ IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) Hr b J)
    (w : WordType) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun y => canonFld y φ) ((P.map fun ω => (rec ω, relVar Hr R V ω))[|typeEvent κ w β E]) := by
  have hrecm : Measurable rec := hrec.mono h𝒢 le_rfl
  set F : Set Ω := rec ⁻¹' E with hFdef
  have hF𝒢 : MeasurableSet[𝒢] F := hrec hE
  have hF : MeasurableSet F := h𝒢 _ hF𝒢
  have hXm : Measurable fun ω => Hr ω φ := (LQGMetric.measurable_distOn_apply φ).comp hHr
  set C : ℝ≥0∞ := ENNReal.ofReal (M * ∫ z, |φ z|) +
    ∫⁻ x, ‖x‖ₑ ∂(gaussianReal 0 (QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ).toNNReal)
    with hC
  have hCtop : C < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, BW1In.lintegral_enorm_gaussianReal_lt_top _⟩
  set f : Ω → ℝ≥0∞ := F.indicator fun ω => ‖Hr ω φ‖ₑ with hfdef
  have hfm : Measurable f := hXm.enorm.indicator hF
  have hbound : ∀ᵐ ω₀ ∂P, ∫⁻ ω, f ω ∂(condExpKernel P 𝒢 ω₀) ≤ C := by
    filter_upwards [KernelTower.ae_condExpKernel_compl_eq_zero h𝒢 hF𝒢, hgff] with ω₀ hc hg
    by_cases hω₀ : ω₀ ∈ F
    · obtain ⟨b, J, hb, hbM, hG⟩ := hg hω₀
      calc ∫⁻ ω, f ω ∂(condExpKernel P 𝒢 ω₀) ≤ ∫⁻ ω, ‖Hr ω φ‖ₑ ∂(condExpKernel P 𝒢 ω₀) :=
            lintegral_mono (indicator_le_self _ _)
        _ ≤ C := BW1In.lintegral_enorm_apply_le_of_isGFF hb hG hM0 hbM φ
    · have h0 : condExpKernel P 𝒢 ω₀ F = 0 := hc.2 hω₀
      rw [hfdef, lintegral_indicator hF, setLIntegral_measure_zero _ _ h0]
      exact zero_le
  have hon : IntegrableOn (fun ω => Hr ω φ) F P := by
    refine ⟨hXm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [← lintegral_indicator hF]
    change ∫⁻ ω, f ω ∂P < ⊤
    rw [← KernelTower.lintegral_lintegral_condExpKernel h𝒢 hfm]
    calc ∫⁻ ω₀, ∫⁻ ω, f ω ∂(condExpKernel P 𝒢 ω₀) ∂P ≤ ∫⁻ _, C ∂P := lintegral_mono_ae hbound
      _ = C := by rw [lintegral_const, measure_univ, mul_one]
      _ < ⊤ := hCtop
  have hΦ : Measurable fun ω => (rec ω, relVar Hr R V ω) := hrecm.prodMk (measurable_relVar hHr hRm hVm)
  have hSm : MeasurableSet (typeEvent κ w β E) := measurableSet_typeEvent hβ hE
  have hφm : Measurable fun y : Supp8.Q3Stop.CanonSpace => canonFld y φ :=
    (LQGMetric.measurable_distOn_apply φ).comp measurable_canonFld
  have hon' : IntegrableOn (fun ω => Hr ω φ) (rec ⁻¹' (E ∩ {y | wordType κ (β y) = w})) P :=
    hon.mono_set fun ω hω => hω.1
  have hi : IntegrableOn (fun y => canonFld y φ) (typeEvent κ w β E)
      (P.map fun ω => (rec ω, relVar Hr R V ω)) := by
    unfold IntegrableOn
    rw [Measure.restrict_map hΦ hSm]
    exact (integrable_map_measure hφm.aestronglyMeasurable hΦ.aemeasurable).2 hon'
  by_cases h0 : (P.map fun ω => (rec ω, relVar Hr R V ω)) (typeEvent κ w β E) = 0
  · rw [cond_eq_zero_of_meas_eq_zero h0]
    exact integrable_zero_measure
  · unfold ProbabilityTheory.cond
    exact hi.smul_measure (ENNReal.inv_ne_top.2 h0)

/-- **The integrability clause from the conditional GFF law of the word itself**: conditionally on `𝒢`, the field is
the GFF of the word `β(rec ω₀)`, whose data are bounded by `M` on the record event. -/
theorem integrable_canonFld_of_condGFF_word (h𝒢 : 𝒢 ≤ mΩ) (hrec : Measurable[𝒢] rec) (hβ : Measurable β)
    (hE : MeasurableSet E) (hHr : Measurable Hr) (hRm : ∀ t, Measurable (R t)) (hVm : Measurable V) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ y ∈ E, ∀ x ∉ (β y).jumps, |(β y).fn x| ≤ M)
    (hgff : ∀ᵐ ω₀ ∂P, rec ω₀ ∈ E →
      IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) Hr (β (rec ω₀)).fn (β (rec ω₀)).jumps)
    (w : WordType) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun y => canonFld y φ) ((P.map fun ω => (rec ω, relVar Hr R V ω))[|typeEvent κ w β E]) :=
  integrable_canonFld_of_condGFF h𝒢 hrec hβ hE hHr hRm hVm hM0
    (hgff.mono fun ω₀ h hm => ⟨_, _, (β (rec ω₀)).isPiecewiseConstantBoundaryData, hM _ hm, h hm⟩) w φ

end Generic

/-! ### The integrability target of a stage instance -/

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω}
  {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)}

/-- **`LinesLocal.int` of a stage instance**: if, conditionally on a σ-algebra `𝒢` for which the augmented stage
record is measurable, the stage field is (on the record event) the GFF of the stage word, and the stage words of the
record event have data bounded by `M`, every pairing of the stage field is integrable under every conditioned type
law. -/
theorem StageInst.lines_int (I : StageInst Ω) (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) (hβ : Measurable I.β)
    (hE : MeasurableSet I.E) (hHr : Measurable I.Hr) (h𝒢 : 𝒢 ≤ mΩ)
    (hrec : Measurable[𝒢] (I.srec c r l)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ I.E, ∀ x ∉ (I.β y).jumps, |(I.β y).fn x| ≤ M)
    (hgff : ∀ᵐ ω₀ ∂c.P, I.srec c r l ω₀ ∈ I.E →
      IsGFFWithBoundaryData (condExpKernel c.P 𝒢 ω₀) I.Hr (I.β (I.srec c r l ω₀)).fn
        (I.β (I.srec c r l ω₀)).jumps)
    (w : WordType) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun y => canonFld y φ)
      ((c.P.map fun ω => (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))[|typeEvent c.κ w I.β I.E]) :=
  integrable_canonFld_of_condGFF_word h𝒢 hrec hβ hE hHr (measurable_stgR hv.1 hv.2.1 hpre)
    (measurable_stgV hv.2.2.2.2.1 hpre) hM0 hM hgff w φ

end InteractingSLE.Theorem14.GW2Stl
