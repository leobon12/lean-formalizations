/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StagedEntranceStrip
import InteractingSLE.Spec.Sec7.StripWallMean

/-!
# Entrance-history locality of both strip walls

Packet PROVE-STRIPSYS29. Specification §7.4, proof of Aux. lemma 130 (`source/spec/p385-432.md`, pp. 410–412): the
walls `α = η^{1,∞}_{−π/2,θ₁}` and `β^{(r)} = η^{r,∞}_{π/2,θ₂}` of (RS13.1) are "deterministic own-time angle changes,
so the already proved simplicity, locality, determination, and reverse containment apply" (p. 411); the change time
`r` is "one deterministic rational `r`" (p. 411, after (RS13.4)).

PROVE-STAGEDLOC2's `Restart.StagedEntrance.Strip.isEntranceHistoryLocal_strip` proved Lemma 6.2's locality input
for an **increasing** two-angle path (`θ₀ ≤ θ ≤ θ₀ + π`), with the continuation's field determination taken from
PROVE-STRIPSYS21. Here:

* **`isEntranceHistoryLocal_strip_of_drv`**: the same gluing argument with the continuation's determination abstracted
  — any Borel map `D r` of the field read in the record chart (one per first record `r`) that almost surely gives the
  continuation's driver, and any field-determined version of the path;
* **`isEntranceHistoryLocal_strip_refl`**: the **decreasing** change (`θ ≤ θ₀ ≤ θ + π`), with PROVE-STRIPSYS27's
  reflected determination (`StripWall.ae_drv_one_refl`, `isDetTwoPiece_of_heights_refl`);
* **`isEntranceHistoryLocal_alpha`**, **`isEntranceHistoryLocal_beta`**: every version of either strip wall (continuous,
  starting at `0`, measurable at fixed times, almost surely a generating trace of the concatenated driver) is
  entrance-history local for the centred field; the wall `β^{(q)}` for every rational change time `q > 0`. The
  continuation's chart trace and the join formula come from PROVE-STRIPSYS28's `exists_wallVersions_twoAngle`.

No Theorem 1.2/1.3 (R43, R48): the only named input is `AdmCode.Theorem12ParamCond44Statement` (from the §4.2
reference, R48-safe).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Restart

namespace StagedEntrance

namespace Strip

open Sec6 Exist.Staged Exist.StagedLaw Sec7.StripSideHeightProb Sec7.StripDet Sec7.AdmCode

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **Entrance-history locality of a two-angle path, for any field-determined continuation** (the gluing of
`isEntranceHistoryLocal_strip` with the continuation's determination abstracted). Let `E` be a two-angle staged history
(angle `θ₀` until the rational own time `q > 0`, then `θ`) of a GFF `h` with piecewise constant data `b` having the
(4.4) heights at `θ₀`. Suppose that almost surely the continuation lives forever and its driver is `D r (field₁ r h)`
for the first record `r = recOf q (E 0)` (`D r` Borel for every `r`), and that the version `αc` of the joined trace is
field determined at fixed times. With the Loewner concatenation data `β`, `hcat` (as in `isEntranceHistoryLocal_strip`),
`αc` is entrance-history local for the centred field. -/
theorem isEntranceHistoryLocal_strip_of_drv (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) {q : ℚ≥0} (hq : 0 < q)
    (hE : IsStagedHistory κ b jumps P h (Sec7.StripSys.twoAngleSpec θ₀ (q : ℝ≥0) θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : RecData → DistOn upperHalfPlaneOpens → ℝ≥0 → ℝ) (hDm : ∀ r, Measurable (D r))
    (hd1 : ∀ᵐ ω ∂P, (E 1 ω).2 = ⊤ ∧ (E 1 ω).1 = D (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω))
      (field₁ κ (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω)) (h ω)))
    {αc : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (αc ω)) (hα0 : ∀ ω, αc ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => αc ω t)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 (q : ℝ≥0) (E 1 ω).1) ⊤ (αc ω))
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => αc ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E 1 ω).1 ⊤ (β ω))
    (hcat : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → β ω s ∈ H ∧
      αc ω ((q : ℝ≥0) + s) = (recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω))).2.1 (β ω s)) :
    IsEntranceHistoryLocal αc (WholeField.centredField h u₀) P := by
  classical
  have hd0 := ae_exists_trace_first hκ hκ4 hb hh hE hL0 hR0
  have hζ : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤ := by
    filter_upwards [hd0, hd1] with ω h0 h1
    exact ⟨h0.1, h1.1⟩
  have hq' : (0 : ℝ≥0) < (q : ℝ≥0) := by exact_mod_cast hq
  have hpast : StagedEntrance.pastSigma αc (q : ℝ≥0) ≤ mΩ := pastSigma_le hαm
  have hK := ae_condExpKernel_pastSigma_eq hE hreg hq' hαm hζ htr
  -- the record chart of the first piece, replaced by the identity chart off the good event
  let G : Ω → Prop := fun ω => ∀ z ∈ H,
    z ∈ closure ((recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω))).dom : Set ℂ) →
      z ∉ (recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω))).dom → z ∈ αc ω '' Icc 0 (q : ℝ≥0)
  have hG : ∀ᵐ ω ∂P, G ω := by
    filter_upwards [hζ, htr] with ω hω hα
    exact frontier_recChart (hreg 0 ω) (hreg 1 ω) hω.1 hω.2 hα
  let c : Ω → Chart := fun ω => if G ω then recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω)) else Chart.id
  have hcG : ∀ ω, G ω → c ω = recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω)) := fun ω hω => by
    simp only [c, hω, ↓reduceIte]
  have hcN : ∀ ω, ¬ G ω → c ω = Chart.id := fun ω hω => by
    simp only [c, hω, ↓reduceIte]
  have hc : ∀ ω, (c ω).IsConformal := fun ω => by
    by_cases hω : G ω
    · rw [hcG ω hω]; exact isConformal_recChart _
    · rw [hcN ω hω]; exact Chart.isConformal_id
  have hfr : ∀ ω, ∀ z ∈ H, z ∈ closure ((c ω).dom : Set ℂ) → z ∉ (c ω).dom → z ∈ αc ω '' Icc 0 (q : ℝ≥0) := by
    intro ω z hz hcl hnd
    by_cases hω : G ω
    · rw [hcG ω hω] at hcl hnd
      exact hω z hz hcl hnd
    · rw [hcN ω hω] at hnd
      exact absurd (mem_dom_id hz) hnd
  -- the chart field and its data
  let h'' : Ω → Ω → DistOn upperHalfPlaneOpens := fun ω₀ ω => recField κ (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀)) (h ω)
  have hst : ∀ᵐ ω₀ ∂P, ∃ p : (ℝ → ℝ) × Finset ℝ, IsPiecewiseConstantBoundaryData p.1 p.2 ∧
      IsFlowLineDriver κ p.1 p.2 θ (condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀) (h'' ω₀)
        (fun t ω => (E 1 ω).1 t) (fun ω => (E 1 ω).2) := by
    filter_upwards [ae_isFlowLineDriver_second hE hreg (hζ.mono fun ω hω => hω.1), hK] with ω₀ h1 h2
    rw [h2] at h1
    exact h1
  let bJ : Ω → (ℝ → ℝ) × Finset ℝ := fun ω₀ => Classical.epsilon fun p : (ℝ → ℝ) × Finset ℝ =>
    IsPiecewiseConstantBoundaryData p.1 p.2 ∧
      IsFlowLineDriver κ p.1 p.2 θ (condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀) (h'' ω₀)
        (fun t ω => (E 1 ω).1 t) (fun ω => (E 1 ω).2)
  let u' : Ω → ℂ → ℝ := fun ω₀ => Classical.epsilon fun u : ℂ → ℝ =>
    IsBoundedHarmonicExtension (bJ ω₀).1 (bJ ω₀).2 u
  have hu' : ∀ ω₀, IsPiecewiseConstantBoundaryData (bJ ω₀).1 (bJ ω₀).2 →
      IsBoundedHarmonicExtension (bJ ω₀).1 (bJ ω₀).2 (u' ω₀) := fun ω₀ hp => by
    obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hp
    exact Classical.epsilon_spec (p := fun u : ℂ → ℝ => IsBoundedHarmonicExtension (bJ ω₀).1 (bJ ω₀).2 u) ⟨u, hu⟩
  let m : Ω → TestOn upperHalfPlaneOpens → ℝ := fun ω₀ φ =>
    SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ (Chart.pushTest (hc ω₀) φ) +
      chiC κ * Chart.liftDist (c ω₀) φ - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (u' ω₀) φ
  have hchart : ∀ᵐ ω₀ ∂P, IsPiecewiseConstantBoundaryData (bJ ω₀).1 (bJ ω₀).2 ∧
      IsBoundedHarmonicExtension (bJ ω₀).1 (bJ ω₀).2 (u' ω₀) ∧
      IsGFFWithBoundaryData (condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀) (h'' ω₀) (bJ ω₀).1
        (bJ ω₀).2 ∧
      ∀ φ, ∀ᵐ ω ∂(condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀),
        WholeField.centredField (h'' ω₀) (u' ω₀) ω φ =
          WholeField.centredField h u₀ ω (Chart.pushTest (hc ω₀) φ) + m ω₀ φ := by
    filter_upwards [hst, hG] with ω₀ hp hGω
    obtain ⟨hbp, hfl⟩ := Classical.epsilon_spec hp
    refine ⟨hbp, hu' ω₀ hbp, Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hbp hfl,
      fun φ => Eventually.of_forall fun ω => ?_⟩
    have e1 : h'' ω₀ ω φ = 1 * h ω (Chart.pushTest (isConformal_recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀))) φ) +
        0 * Chart.oneDist φ + chiC κ * Chart.liftDist (recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀))) φ :=
      Chart.chartTransport_apply' _ _ _ _ _ _
    have e2 : Chart.pushTest (hc ω₀) φ =
        Chart.pushTest (isConformal_recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀))) φ :=
      pushTest_congr _ _ (hcG ω₀ hGω) φ
    have e3 : Chart.liftDist (c ω₀) = Chart.liftDist (recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀))) := by
      rw [hcG ω₀ hGω]
    simp only [WholeField.centredField, m, sub_apply, e1, e2, e3]
    ring
  -- the a.s. facts under Lemma 6.2's conditional laws
  have hT1 := KernelTower.ae_ae_condExpKernel_of_ae hpast hd1
  have hT3 := KernelTower.ae_ae_condExpKernel_of_ae hpast hβtr
  have hT4 := KernelTower.ae_ae_condExpKernel_of_ae hpast hcat
  have hT2 : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀),
      recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω) = recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀) := by
    have hm : Measurable[_root_.InteractingSLE.pastSigma κ b jumps (Sec7.StripSys.twoAngleSpec θ₀ (q : ℝ≥0) θ) E 1]
        (pastMap κ b jumps (Sec7.StripSys.twoAngleSpec θ₀ (q : ℝ≥0) θ) E 1) := by
      rw [pastSigma_eq_comap]
      exact comap_measurable _
    filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel_eq (hE.2.1 1) hm, hK] with ω₀ h1 h2
    rw [← h2]
    filter_upwards [h1] with ω hω
    have e := pastMap_one_last (κ := κ) (b := b) (jumps := jumps) (θ₀ := θ₀) (θ := θ) (t₀ := (q : ℝ≥0)) (E := E) ω
    have e' := pastMap_one_last (κ := κ) (b := b) (jumps := jumps) (θ₀ := θ₀) (θ := θ) (t₀ := (q : ℝ≥0)) (E := E) ω₀
    rw [← e, ← e', hω]
  have hflow : ∀ᵐ ω₀ ∂P,
      IsFlowLine κ (bJ ω₀).1 (bJ ω₀).2 0 θ (condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀) (h'' ω₀) β
        (fun ω => (E 1 ω).2) ∧
      (∀ᵐ ω ∂(condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀), (E 1 ω).2 = ⊤) ∧
      (∀ ω, Continuous (β ω)) ∧ (∀ ω, β ω 0 = 0) ∧ (∀ t, Measurable fun ω => β ω t) ∧
      (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
        (fun ω => β ω t) =ᵐ[condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀]
          fun ω => f (WholeField.centredField (h'' ω₀) (u' ω₀) ω)) ∧
      ∀ᵐ ω ∂(condExpKernel P (StagedEntrance.pastSigma αc (q : ℝ≥0)) ω₀), ∀ s, 0 < s →
        β ω s ∈ H ∧ αc ω ((q : ℝ≥0) + s) = (c ω₀).2.1 (β ω s) := by
    filter_upwards [hst, hG, hT1, hT2, hT3, hT4] with ω₀ hp hGω h1 h2 h3 h4
    obtain ⟨-, hfl⟩ := Classical.epsilon_spec hp
    refine ⟨?_, h1.mono fun ω hω => hω.1, hβc, hβ0, hβm, fun t => ?_, ?_⟩
    · obtain ⟨h₃, 𝓕, VL, VR, B, ht, hC⟩ := hfl
      refine ⟨h₃, 𝓕, fun t ω => (E 1 ω).1 t, VL, VR, B, ht, hC, ?_⟩
      filter_upwards [h1, h3] with ω hω hβω
      simp only [Complex.ofReal_zero, sub_zero]
      rw [hω.1]
      exact hβω
    · refine ⟨fun X => LP.traceAt t (D (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀))
        (X + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (u' ω₀))), ?_, ?_⟩
      · exact (LP.measurable_traceAt t).comp ((hDm _).comp (Coupling.measurable_add_distOnConst _))
      · filter_upwards [h1, h2, h3] with ω hω hr hβω
        have hc1 : Continuous (E 1 ω).1 := continuous_of_regular_top (hreg 1 ω) hω.1
        have e1 : β ω t = LP.traceAt t (E 1 ω).1 :=
          (LP.traceAt_eq_of_isGeneratingTrace hβω hc1.continuousOn (hreg 1 ω).2.1 ENNReal.coe_lt_top).symm
        have e3 : WholeField.centredField (h'' ω₀) (u' ω₀) ω +
            SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (u' ω₀) =
              field₁ κ (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀)) (h ω) := by
          simp only [WholeField.centredField, sub_add_cancel, h'', field₁, Sec7.Prop74B.flowField_zero_zero]
        change β ω t = LP.traceAt t (D (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω₀))
          (WholeField.centredField (h'' ω₀) (u' ω₀) ω +
            SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (u' ω₀)))
        rw [e3, e1, hω.2, hr]
    · filter_upwards [h4, h2] with ω hω hr s hs
      rw [hcG ω₀ hGω, ← hr]
      exact hω s hs
  have h0H : (0 : ℂ) ∉ H := fun h0 => by
    have h0' : (0 : ℝ) < (0 : ℂ).im := h0
    rw [Complex.zero_im] at h0'
    exact lt_irrefl _ h0'
  exact isEntranceHistoryLocal_of_restart_isFlowLine hκ hκ4
    (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀) h0H hαc hα0 hαm (q₀ := q)
    (fun t => frozenPath_ae_eq_comp hdet _ t)
    (isEntranceHistoryLocal_frozenPath_first hκ hκ4 hb hh hE hreg hL0 hR0 hu₀ hαc hαm htr) hc hfr
    (b := fun ω₀ => (bJ ω₀).1) (jumps := fun ω₀ => (bJ ω₀).2) (θ := fun _ => θ) (u₀ := u') (h'' := h'')
    (m := m) (β := fun _ => β) (ζ := fun _ ω => (E 1 ω).2) hchart hflow

/-- **Entrance-history locality of a decreasing two-angle path** (the reflected condition; spec p. 410). As
`isEntranceHistoryLocal_strip`, for `θ ≤ θ₀ ≤ θ + π` and the heights `b + θχ ≤ −λ` left, `b + θχ ≥ λ − πχ` right of `0`
(the wall `β^{(r)}`: `θ₀ = π/2`, `θ = θ₂ ∈ [−π/2, π/2]`): the continuation is the negated, mirrored field-determined
flow line (`StripWall.ae_drv_one_refl`), and the path is field determined (`isDetTwoPiece_of_heights_refl`). -/
theorem isEntranceHistoryLocal_strip_refl (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) {q : ℚ≥0} (hq : 0 < q)
    (hE : IsStagedHistory κ b jumps P h (Sec7.StripSys.twoAngleSpec θ₀ (q : ℝ≥0) θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ) (hθ : θ ≤ θ₀)
    (hθπ : θ₀ ≤ θ + Real.pi) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {αc : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (αc ω)) (hα0 : ∀ ω, αc ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => αc ω t)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 (q : ℝ≥0) (E 1 ω).1) ⊤ (αc ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E 1 ω).1 ⊤ (β ω))
    (hcat : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → β ω s ∈ H ∧
      αc ω ((q : ℝ≥0) + s) = (recChart (recOf ((q : ℝ≥0) : ℝ≥0∞) (E 0 ω))).2.1 (β ω s)) :
    IsEntranceHistoryLocal αc (WholeField.centredField h u₀) P := by
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  refine isEntranceHistoryLocal_strip_of_drv hκ hκ4 hb hh hq hE hreg hL0 hR0 hu₀
    (fun r X => (Sec7.StripWall.negDrv (admDrv h44 hκ hκ4 (-θ)
      (Sec7.StripWall.reflWord (word₁ κ θ₀ c₀ r), Sec7.FlowReflect.reflField X))).1)
    (fun r => measurable_fst.comp (Sec7.StripWall.measurable_negDrv.comp ((measurable_admDrv h44 hκ hκ4 (-θ)).comp
      (measurable_const.prodMk Sec7.FlowReflect.measurable_reflField)))) ?_ hαc hα0 hαm htr
    ((Sec7.StripWall.isDetTwoPiece_of_heights_refl h44 hκ hκ4 hb hh hE hreg hL0 hR0 hL hR hθ hθπ).hdet hreg u₀ htr)
    hβc hβ0 hβm hβtr hcat
  filter_upwards [Sec7.StripWall.ae_drv_one_refl h44 hκ hκ4 hb hh hE hreg hc₀J hc₀ hL0 hR0 hL hR hθ hθπ] with ω hω
  refine ⟨hω.1, funext fun t => ?_⟩
  show (E 1 ω).1 t = -(admDrv h44 hκ hκ4 (-θ) _).1 t
  rw [hω.2.2 t (by rw [hω.1]; exact ENNReal.coe_lt_top), neg_neg]

end Strip

end StagedEntrance

end Restart

end InteractingSLE

namespace InteractingSLE

namespace Sec7

namespace StripWall

open StripSideHeightProb
open Exist.Staged (IsRegularDriver)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- Two paths that almost surely generate the chain of the same concatenated driver of regular drivers with infinite
lifetimes agree almost surely. -/
theorem ae_eq_of_isGeneratingTrace_catPath {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {t₀ : ℝ≥0} (hζ : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤) {γ γ' : Ω → ℝ≥0 → ℂ}
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω))
    (hγ' : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ' ω)) :
    ∀ᵐ ω ∂P, γ ω = γ' ω := by
  filter_upwards [hζ, hγ, hγ'] with ω hω h1 h2
  obtain ⟨hcc, hcc0⟩ := continuous_catPath_of_isRegularDriver (hreg 0 ω) (hreg 1 ω) hω.1 hω.2 t₀
  funext t
  rw [← LP.traceAt_eq_of_isGeneratingTrace h1 hcc.continuousOn hcc0 ENNReal.coe_lt_top,
    LP.traceAt_eq_of_isGeneratingTrace h2 hcc.continuousOn hcc0 ENNReal.coe_lt_top]

/-- **Every version of the wall `β^{(q)}` is entrance-history local** (Lemma 6.2's `hloc`; spec pp. 410–411), for every
rational change time `q > 0` (the source's "one deterministic rational `r`", p. 411): a family `β`, continuous at every
sample, starting at `0`, measurable at fixed times and almost surely a generating trace of the concatenated driver of
the strip system's staged history `η^{q,∞}_{π/2,θ₂}`, is entrance-history local for the centred field `h − u₀`. -/
theorem isEntranceHistoryLocal_beta (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ≥0} (hq : 0 < q)
    (hregβ : ∀ j ω, IsRegularDriver (Es (StripSys.betaSpec (q : ℝ≥0) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec (q : ℝ≥0) θ₂) 0 ω).1 (q : ℝ≥0)
      (Es (StripSys.betaSpec (q : ℝ≥0) θ₂) 1 ω).1) ⊤ (β ω)) :
    Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hp := StripSys.pi_div_two_mem_Icc
  have hE := hS.isStagedHistory_beta hθ₂ (q : ℝ≥0)
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ; linarith
  have hRθ : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ - π * chiC κ ≤ b y + θ₂ * chiC κ := fun y hy hyJ => by
    have := hcumR _ hθ₂ y hy hyJ; linarith
  obtain ⟨γ, η₁, hγ, hη₁c, hη₁0, hη₁m, hη₁⟩ := exists_wallVersions_twoAngle (θ₀ := π / 2) (θ := θ₂) hκ hκ4
    hS.boundaryData hS.gff hE hregβ (hL44 _ hp) (hcumR _ hp) (hL44 _ hθ₂) hRθ (by linarith [hθ₂.2, Real.pi_pos])
    (by linarith [hθ₂.1, Real.pi_pos])
  have hs := ae_simple_trace_beta hS hcumL hcumR hθ₂ (q : ℝ≥0) hregβ
  have heq := ae_eq_of_isGeneratingTrace_catPath hregβ (hs.mono fun ω hω => hω.1) hβtr
    (hγ.ae_trace.mono fun ω hω => hω.1)
  refine Restart.StagedEntrance.Strip.isEntranceHistoryLocal_strip_refl (θ₀ := π / 2) (θ := θ₂) h44 hκ hκ4
    hS.boundaryData hS.gff hq hE hregβ (hL44 _ hp) (hcumR _ hp) (hcumL _ hθ₂) hRθ hθ₂.2
    (by linarith [hθ₂.1, Real.pi_pos]) hu₀ hβc hβ0 hβm hβtr hη₁c hη₁0 hη₁m (hη₁.mono fun ω hω => hω.1) ?_
  filter_upwards [hη₁, heq] with ω hω he s hs
  rw [he]
  exact ⟨hω.2.2.1 s hs, (hω.2.2.2.2 s hs).2⟩

/-- **Every version of the wall `α = η^{1,∞}_{−π/2,θ₁}` is entrance-history local** (Lemma 6.2's `hloc`;
PROVE-STAGEDLOC2's increasing case `isEntranceHistoryLocal_strip_one`, with the continuation's chart trace and the
join formula from `exists_wallVersions_twoAngle`). -/
theorem isEntranceHistoryLocal_alpha (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω)) :
    Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hE := hS.isStagedHistory_alpha hθ₁
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ; linarith
  have hRθ : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ - π * chiC κ ≤ b y + θ₁ * chiC κ := fun y hy hyJ => by
    have := hcumR _ hθ₁ y hy hyJ; linarith
  obtain ⟨γ, η₁, hγ, hη₁c, hη₁0, hη₁m, hη₁⟩ := exists_wallVersions_twoAngle (θ₀ := -(π / 2)) (θ := θ₁) (t₀ := 1) hκ
    hκ4 hS.boundaryData hS.gff hE hregα (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁) hRθ
    (by linarith [hθ₁.2, Real.pi_pos]) (by linarith [hθ₁.1, Real.pi_pos])
  have hs := ae_simple_trace_alpha hS hcumL hcumR hθ₁ hregα
  have heq := ae_eq_of_isGeneratingTrace_catPath hregα (hs.mono fun ω hω => hω.1) hαtr
    (hγ.ae_trace.mono fun ω hω => hω.1)
  refine Restart.StagedEntrance.Strip.isEntranceHistoryLocal_strip_one (θ₀ := -(π / 2)) (θ := θ₁) h44 hκ hκ4
    hS.boundaryData hS.gff hE hregα (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁) (hcumR _ hθ₁) hθ₁.1
    (by linarith [hθ₁.2, Real.pi_pos]) hu₀ hαc hα0 hαm hαtr hη₁c hη₁0 hη₁m (hη₁.mono fun ω hω => hω.1) ?_
  filter_upwards [hη₁, heq] with ω hω he s hs
  rw [he]
  exact ⟨hω.2.2.1 s hs, (hω.2.2.2.2 s hs).2⟩

end StripWall

end Sec7

end InteractingSLE
