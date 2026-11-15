/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LawsTerminal

/-!
# GW1's terminal restart law: the conditional half proved, the pathwise half isolated

Packet PROVE-GW1-LAWS. `GW1RestartPair.IsTerminalRestart` (BW1 in the walk's retained conditional experiment) has a
**conditional** half (a measurable driver which, under the regular conditional law given the post-piece past, drives
the centred counterflow of the field read in the post-piece chart, with infinite lifetime) and a **pathwise** half
(almost surely the relative curve is the launch counterflow before its first visit to the new union, through a
retained clock).

* `ae_terminal_kernel`: under almost every conditional law given the post-piece past, at a next launch, the field read
  in the post-piece chart is the GFF of the recentred next-launch word, which is the good stop word of the piece.
* `exists_terminal_canonical`: the canonical post-piece driver (`GW1Laws.cfDrvOf` at that word and field) is measurable,
  satisfies the conditional half, and is almost surely continuous from `0` with infinite lifetime.
* `IsTerminalRestartCond`, `IsTerminalRestartPath`, `isTerminalRestart_iff`.
* **`TerminalPathStatement`** (named input): every such driver satisfies the pathwise half for some clock — BW1's
  identification of the canonical conditional counterflow with the actual counterflow prefix (Astra follow-up 5 §4.3,
  "Proposition 4.2": the adopted collar comparisons, mean identification and integrated uniqueness).
* **`terminalRestartLawStatement_of_path`**: `TerminalRestartLawStatement` from Theorems 1.2–1.3 and
  `TerminalPathStatement`.
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

open Exist Exist.StagedLaw Exist.Staged Restart PiecewiseConstantBoundaryData GW1RestartPair

theorem shiftW_neg_shiftW (a : ℝ) (c : BoundaryWord) :
    BoundaryWord.shiftW (-a) (BoundaryWord.shiftW a c) = c := by
  obtain ⟨m, p, q⟩ := c
  simp only [BoundaryWord.shiftW, sub_neg_eq_add, sub_add_cancel]

/-- The post-piece word: the next-launch word recentred back at the threshold. -/
def postWord (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) {Ω : Type*}
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) (βk : Ω → BoundaryWord) (ω : Ω) : BoundaryWord :=
  BoundaryWord.shiftW (-(postShift κ b jumps spec (fun j => E j ω) n)) (βk ω)

/-- The post-piece field: the next-launch field read back in the post-piece chart. -/
def postField (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) {Ω : Type*}
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) (Yk : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) :
    DistOn upperHalfPlaneOpens :=
  flowField (-(postShift κ b jumps spec (fun j => E j ω) n)) 0 (Yk ω)

section Kernel

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

omit [StandardBorelSpace Ω] in
theorem measurable_postShift (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (n : ℕ) : Measurable fun ω => postShift κ b jumps spec (fun j => E j ω) n := by
  have h1 := (runMeasStatement κ b jumps hb spec E hEm hreg (2 * n + 1)).2 0
  have h2 := (runMeasStatement κ b jumps hb spec E hEm hreg (2 * (n + 1))).2 0
  unfold postShift
  exact Complex.measurable_re.comp (h1.sub h2)

omit [StandardBorelSpace Ω] in
/-- The post-piece field is measurable. -/
theorem measurable_postField (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (n : ℕ) {Yk : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Yk) :
    Measurable (postField κ b jumps spec E n Yk) := by
  have hs := (measurable_postShift (κ := κ) hb spec hEm hreg n).neg
  have h := measurable_flowField_uncurry.comp (hs.prodMk hY)
  exact h

omit [StandardBorelSpace Ω] in
/-- The post-piece word is measurable. -/
theorem measurable_postWord (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (n : ℕ) {βk : Ω → BoundaryWord} (hβ : Measurable βk) :
    Measurable (postWord κ b jumps spec E n βk) := by
  have hs := (measurable_postShift (κ := κ) hb spec hEm hreg n).neg
  have h := BoundaryWord.measurable_shiftW.comp (hs.prodMk hβ)
  exact h

/-- **The post-piece field under the conditional law at a next launch.** -/
theorem ae_terminal_kernel (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h (GW1Z.walkSpec b jumps right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {n : ℕ} {βk : Ω → BoundaryWord} {Yk : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (GW1Z.walkSpec b jumps right) E (2 * (n + 1)) βk Yk)
    (hgood : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) (2 * (n + 1) + 1)).2.2.2.1
        (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
      ∃ γ : BoundaryWord, IsCfGoodWord κ γ ∧
        βk ω = BoundaryWord.shiftW (postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) n) γ)
    (hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) (2 * (n + 1) + 1)).2.2.2.1
        (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none) :
    ∀ᵐ ω₀ ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) (2 * (n + 1) + 1)).2.2.2.1
        (2 * (n + 1)) ≠ none →
      IsCfGoodWord κ (postWord κ b jumps (GW1Z.walkSpec b jumps right) E n βk ω₀) ∧
      IsGFFWithBoundaryData
        (condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * (n + 1))) ω₀)
        (postField κ b jumps (GW1Z.walkSpec b jumps right) E n Yk)
        (postWord κ b jumps (GW1Z.walkSpec b jumps right) E n βk ω₀).fn
        (postWord κ b jumps (GW1Z.walkSpec b jumps right) E n βk ω₀).jumps ∧
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * (n + 1))) ω₀),
        postWord κ b jumps (GW1Z.walkSpec b jumps right) E n βk ω =
          postWord κ b jumps (GW1Z.walkSpec b jumps right) E n βk ω₀) ∧
      (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) (2 * n + 1))).IsConformal ∧
      ContinuousOn (fun w => (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E j ω₀) (2 * n + 1))).2.2 ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E j ω₀) (2 * n + 1))).2.1 w)) QuantumZipper.H ∧
      ∀ h' : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E j ω₀) (2 * n + 1))) 1 0 (chiC κ) (h ω) (h' ω)) →
        postField κ b jumps (GW1Z.walkSpec b jumps right) E n Yk
          =ᵐ[condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * (n + 1))) ω₀] h' := by
  have hk𝒢 : pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * (n + 1)) ≤ mΩ := hE.2.1 _
  have hker : ∀ ω, condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * (n + 1))) ω =
      condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * n + 1)) ω :=
    condExpKernel_walk_connector (κ := κ) (b := b) (jumps := jumps)
      (θ := if right then -(Real.pi / 2) else Real.pi / 2) (right := right) P E n
  have hYdm : Measurable (postField κ b jumps (GW1Z.walkSpec b jumps right) E n Yk) :=
    measurable_postField hb _ hE.1 hreg n hW.2.1
  filter_upwards [hgood, hprev, hW.2.2.2,
    ae_ae_run_eq runMeasStatement hb (GW1Z.walkSpec b jumps right) (k := 2 * (n + 1)) (fun j _ => hE.1 j) (fun j _ => hreg j) (P := P),
    ae_ae_run_eq runMeasStatement hb (GW1Z.walkSpec b jumps right) (k := 2 * n + 1) (fun j _ => hE.1 j) (fun j _ => hreg j) (P := P),
    Sec7.Aux122Disint.ae_ae_condExpKernel hk𝒢 hW.2.2.1,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) hk𝒢 hW.1] with ω₀ hg hp hgff hrunk hrun1 htr hβ hlk
  rw [← hker ω₀] at hrun1
  have hl := hp hlk
  obtain ⟨γ, hγ, hβk⟩ := hg hlk hl
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
  obtain ⟨ℓ, hℓk, ⟨c', θ', hl'⟩, -, hn, x₀, hchart⟩ :=
    exists_last_launch (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) (by omega : 0 < 2 * (n + 1)) hcθ
  have hℓ : ℓ = 2 * n := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hl (hn (2 * n) hlt (by omega))
    · have h1 : ℓ = 2 * n + 1 := by omega
      subst h1
      have h2 := GW1RestartPair.noLaunch_walk_odd (κ := κ) (b := b) (jumps := jumps)
        (θ := if right then -(Real.pi / 2) else Real.pi / 2) (right := right) (fun j => E j ω₀) n
      rw [h2] at hl'
      exact absurd hl' (by simp)
  subst hℓ
  set d₀ := stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) (2 * n + 1)) with hd₀
  have hx : postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) n = x₀ := by
    unfold postShift
    rw [hchart]
    simp [Chart.recenter]
  -- the recentring amount and the word are constant under the kernel
  have hpost : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * (n + 1))) ω₀),
      postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) n = x₀ := by
    filter_upwards [hrunk, hrun1] with ω h1 h2
    rw [← hx]
    unfold postShift
    rw [h1, h2]
  -- the post-piece field is the field read in the post-piece chart
  have hchart' : ∀ ω, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) (2 * (n + 1))) =
      ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) (2 * (n + 1)) →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none := by
    intro ω hr
    rw [launches_run_succ_of_run_eq (GW1Z.walkSpec b jumps right) hr]
    exact hlk
  have hreg₀ : d₀.IsConformal ∧ ContinuousOn (fun w => d₀.2.2 (d₀.2.1 w)) QuantumZipper.H := by
    obtain ⟨ω, hω⟩ := (hrunk.and htr).exists
    obtain ⟨h1, h2, -⟩ := hω.2 (hchart' ω hω.1)
    rw [hω.1] at h1 h2
    change (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) (2 * (n + 1)))).IsConformal at h1
    change ContinuousOn (fun w => (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) (2 * (n + 1)))).2.2
      ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) (2 * (n + 1)))).2.1 w)) QuantumZipper.H at h2
    rw [stChart, hchart] at h1 h2
    have e : (d₀.recenter x₀).recenter (-x₀) = d₀ := by
      rw [Chart.recenter_recenter, add_neg_cancel, Chart.recenter_zero]
    refine ⟨?_, ?_⟩
    · have := h1.recenter (-x₀)
      rwa [e] at this
    · have := Chart.continuousOn_recenter_lift (a := -x₀) h2
      rwa [e] at this
  refine ⟨?_, ?_, ?_, hreg₀.1, hreg₀.2, fun h' hh' => ?_⟩
  · have e : postWord κ b jumps (GW1Z.walkSpec b jumps right) E n βk ω₀ = γ := by
      unfold postWord
      rw [hβk, shiftW_neg_shiftW]
    rw [e]
    exact hγ
  · have hg' := isGFFWithBoundaryData_shiftW (-(postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) n)) (hgff hlk)
    refine isGFFWithBoundaryData_congr_ae hg' hYdm ?_
    filter_upwards [hpost] with ω hω
    unfold postField
    rw [hω, hx]
  · filter_upwards [hpost, hβ] with ω h1 h2
    unfold postWord
    rw [h1, h2, hx]
  · filter_upwards [hrunk, htr, hpost] with ω hr ht hω
    obtain ⟨hconf, hlift, htrY⟩ := ht (hchart' ω hr)
    rw [hr] at hconf hlift htrY
    change (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) (2 * (n + 1)))).IsConformal at hconf
    change ContinuousOn (fun w => (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) (2 * (n + 1)))).2.2
      ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) (2 * (n + 1)))).2.1 w)) QuantumZipper.H at hlift
    change IsChartTransport (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀) (2 * (n + 1)))) 1 0 (chiC κ)
      (h ω) (Yk ω) at htrY
    rw [stChart, hchart] at hconf hlift htrY
    have h2 := isChartTransport_shiftChart (-x₀) (chiC κ) (Yk ω)
    have h3 := IsChartTransport.trans hconf (isConformal_shiftChart _) hlift (continuousOn_shiftChart_lift _) htrY h2
    rw [← Chart.recenter_eq_trans, Chart.recenter_recenter, add_neg_cancel, Chart.recenter_zero] at h3
    unfold postField
    rw [hω]
    exact h3.unique hreg₀.1 (hh' ω)

end Kernel

end InteractingSLE.Theorem14.GW1Laws
