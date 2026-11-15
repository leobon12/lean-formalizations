/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LawsWitness
import InteractingSLE.Spec.Supplement.GW1RestartPairData
import InteractingSLE.Spec.Supplement.GW2LaterPass

/-!
# GW1's restart laws: the conditional centred counterflow at a launch, read from the field

Packet PROVE-GW1-LAWS. At a launch `k` of a staged history, let `(β, Y)` be a stage witness (the past-measurable
conditional word and the field read in the launch chart) whose word is almost surely sorted and satisfies the two
height bounds of `ae_cfDrvOf_snd_eq_top`. Then the canonical driver read at the witness,
`ω ↦ cfDrvOf h12p hκ (β ω, Y ω)`, is **measurable**, and under the regular conditional law given the retained past,
at almost every launch sample, it drives the frozen centred counterflow of **every** field `h'` that is `h` read in the
launch chart, with almost surely infinite lifetime (`ae_isCenteredCounterflowDriver_witness`). No measurable selection
and no relative-chain construction is used: the driver is a Borel function of the conditional word and the chart
field (Theorem 1.2 jointly measurable in the word, R44).

For the boundary walks this gives the **conditional clause** of GW1's two restart laws at the next launch
(`exists_next_launch_canonical`): the conditional half of `GW1RestartPair.IsForcedRetarget`, with the kernel given
the post-piece past (equal to the kernel given the next-launch past, `condExpKernel_walk_connector`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1Laws

open Exist Exist.StagedLaw Exist.Staged Restart PiecewiseConstantBoundaryData

/-- The two height bounds of `ae_cfDrvOf_snd_eq_top`, for a sorted word. -/
def IsCfGoodWord (κ : ℝ) (c : BoundaryWord) : Prop :=
  c.IsSorted ∧ (∀ y, y < 0 → y ∉ c.jumps → c.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ) ∧
    ∀ y, 0 < y → y ∉ c.jumps → -sleLambda κ < c.fn y + Real.pi / 2 * chiC κ

section Kernel

variable (h12p : Exist.Staged.Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
  {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- The canonical driver read at a stage witness is measurable at each time. -/
theorem measurable_cfDrvOf_witness {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E) {k : ℕ} {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y) :
    Measurable (fun ω => cfDrvOf h12p hκ (β ω, Y ω)) :=
  (measurable_cfDrvOf h12p hκ).comp ((hW.1.mono (hE.2.1 k) le_rfl).prodMk hW.2.1)

/-- **The conditional centred counterflow at a launch, read from the field.** -/
theorem ae_isCenteredCounterflowDriver_witness (h13 : Exist.Theorem13Statement.{u})
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens} (hW : IsStageWitness κ b jumps P h spec E k β Y)
    (hgood : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsCfGoodWord κ (β ω)) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∀ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
        IsCenteredCounterflowDriver κ (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h'
          (fun t ω => (cfDrvOf h12p hκ (β ω, Y ω)).1 t) (fun ω => (cfDrvOf h12p hκ (β ω, Y ω)).2) ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), (cfDrvOf h12p hκ (β ω, Y ω)).2 = ⊤ := by
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := hE.2.1 k
  have hD := measurable_cfDrvOf_witness h12p hκ hE hW
  filter_upwards [hgood, hW.2.2.2, ae_ae_run_eq runMeasStatement hb spec (k := k) (fun j _ => hE.1 j)
      (fun j _ => hreg j) (P := P), Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hW.2.2.1,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 hW.1] with ω₀ hg₀ hgff hrun htr hβ c θ hl h' hh'
  have hl₀ : (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none := by
    rw [hl]; exact Option.some_ne_none _
  obtain ⟨hs, hL, hR⟩ := hg₀ hl₀
  have hgffμ := hgff hl₀
  have hc : c = (ExplState.run κ b jumps spec (fun j => E j ω₀) k).2.2.2.2.1 :=
    (eq_launch_of_launches spec (fun j => E j ω₀) hl).2.2
  -- the witness field is the field read in the launch chart, under the kernel
  have hYe : Y =ᵐ[condExpKernel P (pastSigma κ b jumps spec E k) ω₀] h' := by
    filter_upwards [hrun, htr] with ω hr ht
    have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [launches_run_succ_of_run_eq spec hr]; exact hl₀
    obtain ⟨hconf, -, htrY⟩ := ht hlω
    rw [hr] at hconf htrY
    rw [← hc] at hconf htrY
    exact htrY.unique hconf (hh' ω)
  have hreg₀ : c.IsConformal ∧ ContinuousOn (fun w => c.2.2 (c.2.1 w)) QuantumZipper.H := by
    obtain ⟨ω, hω⟩ := (hrun.and htr).exists
    have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [launches_run_succ_of_run_eq spec hω.1]; exact hl₀
    obtain ⟨h1, h2, -⟩ := hω.2 hlω
    rw [hω.1, ← hc] at h1 h2
    exact ⟨h1, h2⟩
  have hh'm : Measurable h' := by
    have e : h' = fun ω => Chart.chartTransport hreg₀.1 1 0 (chiC κ) (h ω) := funext fun ω =>
      (hh' ω).eq_chartTransport hreg₀.1 (Chart.locallyIntegrableOn_of_continuousOn hreg₀.2)
    rw [e]
    exact (Chart.measurable_chartTransport _ _ _ _).comp hh.1
  have hgff' : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' (β ω₀).fn (β ω₀).jumps :=
    isGFFWithBoundaryData_congr_ae hgffμ hh'm hYe
  have hae : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), (cfDrvOf h12p hκ (β ω, Y ω)).2 = (cfDrvOf h12p hκ (β ω₀, h' ω)).2 ∧
      ∀ t, (cfDrvOf h12p hκ (β ω, Y ω)).1 t = (cfDrvOf h12p hκ (β ω₀, h' ω)).1 t := by
    filter_upwards [hβ, hYe] with ω hb' hy
    rw [hb', hy]
    exact ⟨rfl, fun _ => rfl⟩
  refine ⟨isCenteredCounterflowDriver_of_ae_cfDrvOf h12p hκ h13 hs hgff'
    (fun t => (measurable_pi_apply t).comp (measurable_fst.comp hD)) (measurable_snd.comp hD) hae, ?_⟩
  filter_upwards [hae, ae_cfDrvOf_snd_eq_top h12p hκ h13 hs hL hR hgff'] with ω h1 h2
  rw [h1.1, h2]

/-- **The canonical lifetime at a stage witness is infinite** under almost every conditional law at a launch. -/
theorem ae_cfDrvOf_witness_eq_top (h13 : Exist.Theorem13Statement.{u}) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E) {k : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens} (hW : IsStageWitness κ b jumps P h spec E k β Y)
    (hgood : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsCfGoodWord κ (β ω)) :
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), (cfDrvOf h12p hκ (β ω, Y ω)).2 = ⊤ := by
  filter_upwards [hgood, hW.2.2.2, Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) (hE.2.1 k) hW.1]
    with ω₀ hg hgff hβ hl
  obtain ⟨hs, hL, hR⟩ := hg hl
  filter_upwards [hβ, ae_cfDrvOf_snd_eq_top h12p hκ h13 hs hL hR (hgff hl)] with ω h1 h2
  rw [h1]
  exact h2

end Kernel

end InteractingSLE.Theorem14.GW1Laws
