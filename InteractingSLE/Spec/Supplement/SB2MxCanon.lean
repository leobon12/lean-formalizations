/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MxHull

/-!
# The code match from the canonical hull chart of a stage

Packet PROVE-SB2-LCMEAN, round 14 (item 4). `Mx.ae_codeMatch_of_lawCode` with the canonical objects of a stage:
the chart field `Z` is the field `h` read in the hull chart of a random compact set `K` with an offset `x₀`, both
measurable for the marks `𝓜`. Its kernel-level transport input then reduces to a statement at the conditioning
sample alone: under the kernel given `𝓜` the hull chart is almost surely the one at the conditioning sample
(`Mx.ae_ae_condExpKernel_set_eq` and `Sec7.Aux122Disint.ae_ae_condExpKernel_eq`).

* `chartTransport_congr_chart`: transports by equal charts agree;
* **`isChartTransport_run_of_phys`** (deterministic): if the relative chart in physical coordinates
  `Mo.physRelChart c c₁ m` and a chart `Φ` are domain charts of the same domain agreeing on it, then reading the
  shifted upper-chart field `affField m g'` in the relative run chart `c₁` gives the field `g` read in `Φ`;
* **`ae_codeMatch_of_canon`**: the code match against every witness of the stage's conditional law from
  - the conditional GFF law of the canonical chart field given `𝓜`;
  - the pathwise code match of the stage driver with the canonical code;
  - at every launched conditioning sample, the run chart transporting `h` to the field read in that sample's canonical
    chart.

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

/-- Transports by equal charts agree. -/
theorem chartTransport_congr_chart {c c' : Chart} (h : c = c') (hc : c.IsConformal) (hc' : c'.IsConformal)
    (σ a k : ℝ) (g : DistOn upperHalfPlaneOpens) :
    Chart.chartTransport hc σ a k g = Chart.chartTransport hc' σ a k g := by
  subst h
  rfl

/-- **The relative run chart reads the shifted upper-chart field as the canonical chart reads the physical field.** -/
theorem isChartTransport_run_of_phys {c c₁ Φ : Chart} {D : Set ℂ} {m : ℝ} (hc : c.IsConformal)
    (hc₁ : c₁.IsConformal) (hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H)
    (hℓ₁ : ContinuousOn (fun w => c₁.2.2 (c₁.2.1 w)) H) (hΦ : IsDomainChart D Φ)
    (hP : IsDomainChart D (Mo.physRelChart c c₁ m)) (hfwd : EqOn Φ.1 (Mo.physRelChart c c₁ m).1 D)
    (hlift : EqOn Φ.2.2 (Mo.physRelChart c c₁ m).2.2 D) {χ : ℝ} {g g' : DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport c 1 0 χ g g') :
    IsChartTransport c₁ 1 0 χ (FlowDilate.affField m one_pos g')
      (Chart.chartTransport hΦ.isConformal 1 0 χ g) := by
  have hX := Chart.isChartTransport_chartTransport hc₁ (Chart.locallyIntegrableOn_of_continuousOn hℓ₁) 1 0 χ
    (FlowDilate.affField m one_pos g')
  have hP' := Mo.isChartTransport_physRelChart hc hc₁ hℓ hℓ₁ ht hX
  have hΦ' := isChartTransport_of_eqOn_domain hΦ hP hfwd hlift hP'
  have hΦt := Chart.isChartTransport_chartTransport hΦ.isConformal
    (Chart.locallyIntegrableOn_of_continuousOn hΦ.continuousOn_lift_inv) 1 0 χ g
  rw [← IsChartTransport.unique hΦ.isConformal hΦ' hΦt]
  exact hX

section Canon

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The code match from the canonical hull chart of a stage.** -/
theorem ae_codeMatch_of_canon (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (θ₀ : ℝ) {k : ℕ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hhm : Measurable h)
    (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}) (hpast : pastSigma κ b jumps spec E k ≤ LocalSets.aeSigma 𝓜.1 P)
    {K : Ω → Set ℂ} (hKm : @IsDyadicHitMeasurable Ω 𝓜.1 K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {x₀ : Ω → ℝ} (hx₀ : Measurable[𝓜.1] x₀)
    {hphys : Ω → DistOn upperHalfPlaneOpens} {c : Ω → BoundaryWord} (hc : Measurable[𝓜.1] c) {G : Set Ω}
    (hlaw : ∀ᵐ ω₁ ∂P, ω₁ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝓜.1 ω₁)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (hphys ω))
      (c ω₁).fn (c ω₁).jumps)
    (hcode : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      ω ∈ G ∧ IsDriverCodeMatch (driverCode h12p hκ θ₀
        (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (hphys ω)))
        (fun t => (E k ω).1 t) (E k ω).2)
    (htr : ∀ᵐ ω₁ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₁) (k + 1)).2.2.2.1 k ≠ none →
      ∀ ω, IsChartTransport (Cond.runChart κ b jumps spec E k ω₁) 1 0 (chiC κ) (h ω)
        (Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω₁) 1 0 (chiC κ) (hphys ω)))
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsDriverCodeMatch (driverCode h12p hκ θ₀ (β ω, Y ω)) (fun t => (E k ω).1 t) (E k ω).2 := by
  refine ae_codeMatch_of_lawCode h12p h13 hκ θ₀ hb hEm hreg 𝓜 hpast hhm hc hlaw hcode ?_ hW
  filter_upwards [htr, ae_ae_condExpKernel_set_eq (μ := P) 𝓜.2 hKm fun ω => (hKc ω).isClosed,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) 𝓜.2 hx₀] with ω₁ htr₁ hK₁ hx₁ hl₁
  filter_upwards [hK₁, hx₁] with ω hKω hxω
  have e : Mo.hullChart (fillH (K ω)) (x₀ ω) = Mo.hullChart (fillH (K ω₁)) (x₀ ω₁) := by rw [hKω, hxω]
  rw [chartTransport_congr_chart e (Mu.isConformal_canon x₀ hKc hKp ω) (Mu.isConformal_canon x₀ hKc hKp ω₁)]
  exact htr₁ hl₁ ω

end Canon

end InteractingSLE.Theorem14.SB.Mx
