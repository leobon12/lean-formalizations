/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MwStep
import InteractingSLE.Spec.Supplement.SB2LcdKernel

/-!
# SB2(2)'s kernel half under the upper kernel: the code match from a law and a code given a fixed σ-algebra

Packet PROVE-SB2-LCMEAN, round 14 (item 4 of the adopted split: transfer to the upper kernel, identification with
`EL`, gluing). The `P`-level induction produces, at each stage, objects that do not depend on the upper-past sample:
a σ-algebra `𝓜` (the marks), a word `c` measurable for it, a chart field `Z` that is conditionally a GFF with the data
of `c` given `𝓜`, and the pathwise match of the stage driver with the canonical code of `(c, Z)`. This file turns
these into the code match against an arbitrary witness of the stage's conditional law:

* **`ae_codeMatch_of_lawCode`** (generic, for any measure): if the retained past of stage `k` is contained in `𝓜` up
  to null sets, then almost surely on the launch event the stage driver matches the canonical code of every witness
  `(β, Y)`. Two more inputs: `Z` is conditionally a GFF with the data of `c` given `𝓜` on an event `G`; and, at
  almost every launched conditioning sample, `Z` is kernel-almost surely the field read in that sample's run chart.
  Proof: under the kernel given `𝓜` the stage driver matches the code of `(c, Z)`, so it is the flow line of the run
  chart's field (Theorem 1.3, `Cond.isFlowLineDriver_of_driverCodeMatch_univ`). Then LCOND's nested identity
  (`Lcd.ae_codeMatch_of_condFlowLine_data`) gives the code of the witness.
* **`ae_ae_isGFF_upper`** (transfer): a conditional GFF law given `𝓜` under `P` holds, for `P`-almost every
  upper-past sample `ω₀`, under the upper kernel `condExpKernel P (comap f) ω₀` when `comap f ≤ 𝓜`
  (`Lk.ae_ae_nested_of_ae_sup`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mx

open Restart Exist Exist.Staged Exist.StagedLaw

section Core

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The code match from a law and a code given a fixed σ-algebra.** -/
theorem ae_codeMatch_of_lawCode (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (θ₀ : ℝ) {k : ℕ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}) (hpast : pastSigma κ b jumps spec E k ≤ LocalSets.aeSigma 𝓜.1 P)
    (hhm : Measurable h) {c : Ω → BoundaryWord} (hc : Measurable[𝓜.1] c) {Z : Ω → DistOn upperHalfPlaneOpens}
    {G : Set Ω}
    (hlaw : ∀ᵐ ω₁ ∂P, ω₁ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝓜.1 ω₁) Z (c ω₁).fn (c ω₁).jumps)
    (hcode : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      ω ∈ G ∧ IsDriverCodeMatch (driverCode h12p hκ θ₀ (c ω, Z ω)) (fun t => (E k ω).1 t) (E k ω).2)
    (htr : ∀ᵐ ω₁ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₁) (k + 1)).2.2.2.1 k ≠ none →
      ∀ᵐ ω ∂(condExpKernel P 𝓜.1 ω₁),
        IsChartTransport (Cond.runChart κ b jumps spec E k ω₁) 1 0 (chiC κ) (h ω) (Z ω))
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsDriverCodeMatch (driverCode h12p hκ θ₀ (β ω, Y ω)) (fun t => (E k ω).1 t) (E k ω).2 := by
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := by
    rw [pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hreg j) k le_rfl).comap_le
  have h𝒢'' : 𝓜.1 ⊔ pastSigma κ b jumps spec E k ≤ mΩ := sup_le 𝓜.2 h𝒢
  -- the kernels given `𝓜` and given `𝓜 ⊔ pastSigma k` agree almost everywhere
  have hker : ∀ᵐ ω ∂P, condExpKernel P 𝓜.1 ω = condExpKernel P (𝓜.1 ⊔ pastSigma κ b jumps spec E k) ω :=
    KernelTower.ae_condExpKernel_eq_of_le_aeSigma 𝓜.2 h𝒢''
      ((le_sup_left : 𝓜.1 ≤ 𝓜.1 ⊔ pastSigma κ b jumps spec E k).trans (LocalSets.le_aeSigma _ P))
      (sup_le (LocalSets.le_aeSigma _ P) hpast)
  have hL : MeasurableSet[pastSigma κ b jumps spec E k]
      {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
    Lv.measurableSet_launch_pastSigma hb hEm hreg k
  have hL'' : MeasurableSet[𝓜.1 ⊔ pastSigma κ b jumps spec E k]
      {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
    (le_sup_right : pastSigma κ b jumps spec E k ≤ _) _ hL
  have hWm : ∀ t, Measurable fun ω => (E k ω).1 t := fun t =>
    (measurable_pi_apply t).comp (measurable_fst.comp (hEm k))
  have hLm : Measurable fun ω => (E k ω).2 := measurable_snd.comp (hEm k)
  have hcfl : SB.IsCondFlowLineDriverOn κ θ₀ 𝓜.1 P
      {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} h
      (Cond.runChart κ b jumps spec E k) (fun ω => (c ω).fn) (fun ω => (c ω).jumps)
      (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) := by
    filter_upwards [hlaw, hcode, htr, hW.2.2.1, hker,
      Sec7.Aux122Disint.ae_condExpKernel_apply_eq_indicator (P := P) h𝒢'' hL'',
      Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) 𝓜.2 hc,
      KernelTower.ae_ae_condExpKernel_of_ae 𝓜.2 hcode] with ω₁ hlaw₁ hcode₁ htr₁ hp₁ hker₁ hind₁ hc₁ hcodeK hl₁
    have hl₁' : (ExplState.run κ b jumps spec (fun j => E j ω₁) (k + 1)).2.2.2.1 k ≠ none := hl₁
    obtain ⟨hconf, hlift, -⟩ := hp₁ hl₁'
    have hconf' : (Cond.runChart κ b jumps spec E k ω₁).IsConformal := hconf
    set h' : Ω → DistOn upperHalfPlaneOpens := fun ω =>
      Chart.chartTransport hconf' 1 0 (chiC κ) (h ω) with hh'
    have hT : ∀ ω, IsChartTransport (Cond.runChart κ b jumps spec E k ω₁) 1 0 (chiC κ) (h ω) (h' ω) :=
      fun ω => Chart.isChartTransport_chartTransport hconf' (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0
        (chiC κ) (h ω)
    -- the launch event is kernel-almost sure at a launched conditioning sample
    have hLK : ∀ᵐ ω ∂(condExpKernel P 𝓜.1 ω₁),
        (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      have h1 : condExpKernel P 𝓜.1 ω₁
          {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none}ᶜ = 0 := by
        rw [hker₁, measure_compl (h𝒢'' _ hL'') (measure_ne_top _ _), hind₁, indicator_of_mem hl₁, measure_univ]
        simp
      exact measure_eq_zero_iff_ae_notMem.1 h1 |>.mono fun ω hω => by simpa using hω
    have hZh' : Z =ᵐ[condExpKernel P 𝓜.1 ω₁] h' := by
      filter_upwards [htr₁ hl₁'] with ω hω
      exact IsChartTransport.unique hconf' hω (hT ω)
    have hG₁ : ω₁ ∈ G := (hcode₁ hl₁').1
    have hh'm : Measurable h' := (Chart.measurable_chartTransport hconf' 1 0 (chiC κ)).comp hhm
    have hgff : IsGFFWithBoundaryData (condExpKernel P 𝓜.1 ω₁) h' (c ω₁).fn (c ω₁).jumps :=
      isGFFWithBoundaryData_congr_ae (hlaw₁ hG₁) hh'm hZh'
    have hmatch : ∀ᵐ ω ∂(condExpKernel P 𝓜.1 ω₁),
        IsDriverCodeMatch (driverCode h12p hκ θ₀ (c ω₁, h' ω)) (fun t => (E k ω).1 t) (E k ω).2 := by
      filter_upwards [hcodeK, hLK, hc₁, hZh'] with ω hcω hlω hcω' hZω
      have h1 := (hcω hlω).2
      rw [hcω', hZω] at h1
      exact h1
    refine ⟨(c ω₁).isPiecewiseConstantBoundaryData, h', hT, ?_⟩
    exact Cond.isFlowLineDriver_of_driverCodeMatch_univ h12p hκ θ₀ h13 (c ω₁) hgff hWm hLm
      (fun ω => (hreg k ω).1) hmatch
  exact Lcd.ae_codeMatch_of_condFlowLine_data h12p h13 hκ θ₀ hb hEm hreg 𝓜 hpast
    (Eventually.of_forall fun _ hl => hl) hW hcfl

end Core

/-- **A conditional GFF law given a σ-algebra `𝓜` containing the upper past moves under the upper kernel**: for
`P`-almost every upper-past sample `ω₀`, almost surely under `condExpKernel P (comap f) ω₀`, the kernel given `𝓜`
of that conditional world carries the same law (`Lk.ae_ae_nested_of_ae_sup`; `comap f ⊔ 𝓜 = 𝓜`). -/
theorem ae_ae_isGFF_upper {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] {f : Ω → X}
    (hf : Measurable f) (h𝓜 : 𝓜 ≤ mΩ)
    (hf𝓜 : MeasurableSpace.comap f inferInstance ≤ 𝓜) (hcg : @MeasurableSpace.CountablyGenerated Ω 𝓜) {G : Set Ω}
    {Z : Ω → DistOn upperHalfPlaneOpens} {c : Ω → BoundaryWord}
    (hlaw : ∀ᵐ ω₁ ∂P, ω₁ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₁) Z (c ω₁).fn (c ω₁).jumps) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω₁ ∂(condExpKernel P (MeasurableSpace.comap f inferInstance) ω₀), ω₁ ∈ G →
      IsGFFWithBoundaryData (condExpKernel (condExpKernel P (MeasurableSpace.comap f inferInstance) ω₀) 𝓜 ω₁) Z
        (c ω₁).fn (c ω₁).jumps := by
  have hsup : MeasurableSpace.comap f inferInstance ⊔ 𝓜 = 𝓜 := sup_eq_right.2 hf𝓜
  have hcg' : @MeasurableSpace.CountablyGenerated Ω (MeasurableSpace.comap f inferInstance ⊔ 𝓜) := by
    rw [hsup]
    exact hcg
  refine Lk.ae_ae_nested_of_ae_sup (ℋ := 𝓜)
    (p := fun x μ => x ∈ G → IsGFFWithBoundaryData μ Z (c x).fn (c x).jumps) hf h𝓜 hcg' ?_
  rw [hsup]
  exact hlaw

end InteractingSLE.Theorem14.SB.Mx
