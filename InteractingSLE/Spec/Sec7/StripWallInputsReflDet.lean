/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripWallInputsRefl
import InteractingSLE.Spec.Sec7.StripWallHeights

/-!
# A decreasing angle change is field determined (the reflected condition)

Packet PROVE-STRIPSYS27 (the walls' Lemma 6.2 inputs, for `β^{(r)} = η^{r,∞}_{π/2,θ₂}`). Specification §7.4, proof
of Aux. lemma 130 (`source/spec/p385-432.md` L442–L448, p. 410): "For the decreasing change of `β^{(r)}`, put
`δ′ = π/2 − θ₂ ∈ (0, π)`. Its seed totals are `δ′χ/λ` on the left and `−δ′χ/λ` on the right, so the reflected
condition applies. […] Conditional field determination makes the continuation measurable from the first prefix and the
original field; the first prefix is itself field determined."

PROVE-STRIPSYS21 proved the increasing case (`StripDet.exists_borel_drivers`, `θ₀ ≤ θ ≤ θ₀ + π`). For the decreasing
case `θ ≤ θ₀ ≤ θ + π` the continuation's word fails (4.4) but its mirror image under `R(z) = −z̄` satisfies it
(`cond44_reflWord_stopWord`). Under the regular conditional law given the first record, the mirrored continuation `−W`
is the angle-`(−θ)` flow-line driver of the mirrored chart field (`isFlowLineDriver_reflect`), so PROVE-STRIPSYS21's
R48-safe determination `AdmCode.admDrv` applies to it:

* **`ae_stageDrv_eq_refl`**: the mirror of `StripDet.ae_stageDrv_eq` — if a.s. at a launch the mirrored stage word
  satisfies (4.4) at `−θ_k`, then a.s. at a launch the piece has infinite lifetime and `−(E k)` is
  `admDrv (−θ_k) (reflWord β, reflField Y)` before the lifetime;
* **`ae_drv_one_refl`**: the continuation of a decreasing two-angle path is a.s. that mirrored determination;
* **`isDetTwoPiece_of_heights_refl`**: both pieces are Borel functions of the field with infinite lifetimes
  (`IsDetTwoPiece`), for heights `b + θ₀χ` with (4.4) and `b + θχ ≤ −λ` left, `≥ λ − πχ` right (all implied by Aux.
  lemma 130's choice).

Inputs: `AdmCode.Theorem12ParamCond44Statement` (from the §4.2 reference). No Theorem 1.2/1.3 (R43, R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace StripWall

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw Exist.StagedLaw.BoundaryWord AdmCode Sec4 QuantumZipper
open StripDet
open FlowReflect (reflData reflJumps reflField)

/-! ### Negated drivers -/

/-- The negated driver `(−e.1, e.2)`. -/
def negDrv (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : (ℝ≥0 → ℝ) × ℝ≥0∞ := (fun t => -e.1 t, e.2)

theorem measurable_negDrv : Measurable negDrv :=
  (measurable_pi_iff.2 fun t => ((measurable_pi_apply t).comp measurable_fst).neg).prodMk measurable_snd

theorem isRegularDriver_negDrv {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) : IsRegularDriver (negDrv e) := by
  obtain ⟨h1, h2, h3, h4⟩ := he
  refine ⟨h1.neg, ?_, fun t ht => ?_, fun hne hpos c hc => ?_⟩
  · show -e.1 0 = 0
    rw [h2, neg_zero]
  · show -e.1 t = -e.1 e.2.toNNReal
    rw [h3 t ht]
  · show -e.1 e.2.toNNReal = c
    have hc' : Tendsto e.1 (𝓝[<] e.2.toNNReal) (𝓝 (-c)) := by
      have := hc.neg
      refine this.congr fun t => ?_
      show -(-e.1 t) = e.1 t
      rw [neg_neg]
    rw [h4 hne hpos (-c) hc', neg_neg]

/-! ### The mirrored stage determination -/

section Stage

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A launched piece is field-determined when its mirrored stage word satisfies (4.4)** (R48-safe; the mirror of
`StripDet.ae_stageDrv_eq`). -/
theorem ae_stageDrv_eq_refl (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hβ : Measurable[pastSigma κ b jumps spec E k] β) (hY : Measurable Y)
    (hpath : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.1 w)) QuantumZipper.H ∧
      IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 1 0 (QuantumZipper.chiC κ)
        (h ω) (Y ω))
    (hker : ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) Y (β ω₀).fn (β ω₀).jumps)
    (h44w : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      Sec4.Cond44 κ (flowLineRhoL κ (reflWord (β ω)).fn (reflWord (β ω)).jumps 0 (-instrAngle spec k))
        (flowLineRhoR κ (reflWord (β ω)).fn (reflWord (β ω)).jumps 0 (-instrAngle spec k))) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → (E k ω).2 = ⊤ ∧
      (admDrv h44 hκ hκ4 (-instrAngle spec k) (reflWord (β ω), reflField (Y ω))).2 = (E k ω).2 ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < (E k ω).2 →
          (admDrv h44 hκ hκ4 (-instrAngle spec k) (reflWord (β ω), reflField (Y ω))).1 t = -(E k ω).1 t := by
  have hB := runMeasStatement.{u}
  have hEm : ∀ j < k, Measurable (E j) := fun j _ => hE.1 j
  have hreg' : ∀ j < k, ∀ ω, IsRegularDriver (E j ω) := fun j _ => hreg j
  have hpm : Measurable (pastMap κ b jumps spec E k) := measurable_pastMap hB hb spec hEm hreg' k le_rfl
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := by rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hLm : MeasurableSet {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
    measurableSet_launch_self hB hb hEm hreg'
  have hL𝒢 : MeasurableSet[pastSigma κ b jumps spec E k]
      {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
    measurableSet_pastSigma_of_run hB hb spec hEm hreg' hLm fun ω ω' he hω => by
      change (ExplState.run κ b jumps spec (fun j => E j ω') (k + 1)).2.2.2.1 k ≠ none
      rw [← launches_run_succ_of_run_eq spec he]
      exact hω
  have hW : ∀ t, Measurable fun ω => -(E k ω).1 t := fun t =>
    ((measurable_pi_apply t).comp (measurable_fst.comp (hE.1 k))).neg
  have hL : Measurable fun ω => (E k ω).2 := measurable_snd.comp (hE.1 k)
  have hWc : ∀ ω, ContinuousOn (fun t => -(E k ω).1 t) {t | (t : ℝ≥0∞) < (E k ω).2} := fun ω =>
    (hreg k ω).1.neg
  have hβ' : Measurable[pastSigma κ b jumps spec E k] fun ω => reflWord (β ω) := measurable_reflWord.comp hβ
  have hY' : Measurable fun ω => reflField (Y ω) := FlowReflect.measurable_reflField.comp hY
  refine ae_admDrv_eq_of_ae_condExpKernel h44 hκ hκ4 (-instrAngle spec k) h𝒢 hL𝒢 hβ' hY' hW hL hWc ?_
  filter_upwards [hE.2.2.2 k, hker, h44w, hpath, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hpath,
    ae_ae_run_eq hB hb spec hEm hreg' (P := P)] with ω₀ hstg hk₀ h44₀ hp₀ hpK hrunK hl
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨hspec, -, hc⟩ := eq_launch_of_launches spec _ hcθ
  have hθ : instrAngle spec k = θ := by unfold instrAngle; rw [hspec]
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hstg c θ hcθ
  obtain ⟨hconf, hlift, -⟩ := hp₀ hl
  rw [← hc] at hconf hlift
  have hh'e : h' = fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => (hT' ω).eq_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift)
  have hh'm : Measurable h' := by
    rw [hh'e]; exact (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
  have hYh' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), h' ω = Y ω := by
    filter_upwards [hpK, hrunK] with ω hpω hrω
    have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [launches_run_succ_of_run_eq spec hrω]; exact hl
    obtain ⟨-, -, hT⟩ := hpω hlω
    rw [hrω, ← hc] at hT
    exact IsChartTransport.unique hconf (hT' ω) hT
  have hG : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' (β ω₀).fn
      (β ω₀).jumps := isGFFWithBoundaryData_congr_ae (hk₀ hl) hh'm (hYh'.mono fun ω hω => hω.symm)
  refine ⟨h44₀ hl, fun ω => reflField (h' ω), hYh'.mono fun ω hω => by simp only [hω], ?_⟩
  rw [hθ]
  exact isFlowLineDriver_reflWord (isFlowLineDriver_reflect (β ω₀).isPiecewiseConstantBoundaryData
    (isFlowLineDriver_word hκ hG hb' hfl))

end Stage

/-! ### The decreasing two-angle path -/

section Strip

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {t₀ : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The continuation of a decreasing change is the mirrored field-determined flow line** (R48-safe; spec p. 410).
If `b` has the (4.4) heights at `θ₀`, the heights `b + θχ ≤ −λ` left of `0` and `b + θχ ≥ λ − πχ` right of `0`, and
`θ ≤ θ₀ ≤ θ + π`, then almost surely the continuation has infinite lifetime and its negation is
`admDrv (−θ) (reflWord (stopWord κ (c₀, θ₀, rec₀)), reflField (recField κ rec₀ h))`, `rec₀ = recOf t₀ (E 0)`. -/
theorem ae_drv_one_refl (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ) (hθ : θ ≤ θ₀)
    (hθπ : θ₀ ≤ θ + Real.pi) :
    ∀ᵐ ω ∂P, (E 1 ω).2 = ⊤ ∧
      (admDrv h44 hκ hκ4 (-θ) (reflWord (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (E 0 ω))),
        reflField (field₁ κ (recOf (t₀ : ℝ≥0∞) (E 0 ω)) (h ω)))).2 = (E 1 ω).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < (E 1 ω).2 →
        (admDrv h44 hκ hκ4 (-θ) (reflWord (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (E 0 ω))),
          reflField (field₁ κ (recOf (t₀ : ℝ≥0∞) (E 0 ω)) (h ω)))).1 t = -(E 1 ω).1 t := by
  have hB := runMeasStatement.{u}
  have hζ₀ := ae_drv_zero h44 hκ hκ4 hb hh hE hreg hc₀J hc₀ hL0 hR0
  obtain ⟨hβ₀, hY₀, hpath₀, hker₀⟩ := stageWitness_zero (E := E) (θ := θ) (t₀ := t₀) (θ₀ := θ₀) hh hc₀J hc₀
  have hpost := post_stage (spec := StripSys.twoAngleSpec θ₀ t₀ θ) (E := E) (ℓ := 0)
    (StripSideHeightProb.isStopLaw_stopWord hκ) hB hκ hb hh (fun j _ => hE.1 j) (fun j _ => hreg j) (hE.2.2.2 0)
    hβ₀ hY₀ hpath₀ hker₀
  have hpm : Measurable (pastMap κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1) :=
    measurable_pastMap hB hb _ (fun j _ => hE.1 j) (fun j _ => hreg j) 1 le_rfl
  have h𝒢 : pastSigma κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1 ≤ mΩ := by
    rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hr : Measurable (rec₀ κ b jumps θ₀ θ t₀ E) := measurable_pi_iff.1 hpm (Fin.last 0)
  have hβ₁ : Measurable[pastSigma κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1]
      (fun ω => word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)) :=
    Measurable.comp (g := word₁ κ θ₀ c₀) (f := rec₀ κ b jumps θ₀ θ t₀ E) (measurable_word₁ κ θ₀ c₀)
      measurable_rec₀_past
  have hY₁ : Measurable (fun ω => field₁ κ (rec₀ κ b jumps θ₀ θ t₀ E ω) (h ω)) :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => field₁ κ p.1 p.2)
      (f := fun ω => (rec₀ κ b jumps θ₀ θ t₀ E ω, h ω)) (measurable_field₁ κ) (hr.prodMk hh.1)
  have hpath₁ : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) (1 + 1)).2.2.2.1 1
      ≠ none →
      (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1.2.1 w)) H ∧
      IsChartTransport (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1 1 0
        (chiC κ) (h ω) (field₁ κ (rec₀ κ b jumps θ₀ θ t₀ E ω) (h ω)) := by
    filter_upwards [hζ₀] with ω hω _
    have h0 : (t₀ : ℝ≥0∞) < (E 0 ω).2 := by rw [hω.1]; exact ENNReal.coe_lt_top
    have hrec : rec₀ κ b jumps θ₀ θ t₀ E ω = recOf (t₀ : ℝ≥0∞) (E 0 ω) := pastMap_one_last ω
    rw [chart_one_eq (hreg 0 ω) h0, hrec]
    refine ⟨isConformal_recChart _, continuousOn_recChart_lift _, ?_⟩
    rw [field₁, Prop74B.flowField_zero_zero]
    exact isChartTransport_recField κ _ _
  have hker₁ : ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω₀) (1 + 1)).2.2.2.1 1
      ≠ none → IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1) ω₀)
        (fun ω => field₁ κ (rec₀ κ b jumps θ₀ θ t₀ E ω) (h ω)) (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω₀)).fn
        (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω₀)).jumps := by
    have hG := ae_isGFFWithBoundaryData_condExpKernel h𝒢 (M := univ)
      (β := fun ω => word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω))
      (Eventually.of_forall fun ω _ => isSorted_stopWord κ _) hY₁ (fun φ => by
        filter_upwards [hpost.2 φ] with ω hω _
        exact hω (launch_zero _) (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)))
    filter_upwards [hG] with ω₀ hω₀ _
    exact hω₀ (mem_univ _)
  have hL' : ∀ y : ℝ, y < 0 → y ∉ (shiftW 0 c₀).jumps → (shiftW 0 c₀).fn y + θ * chiC κ ≤ -sleLambda κ := by
    intro y hy hyJ
    obtain ⟨hyj, he⟩ := shiftW_zero_fn_of_notMem hc₀J hc₀ hyJ
    rw [he]; exact hL y hy hyj
  have hR' : ∀ y : ℝ, 0 < y → y ∉ (shiftW 0 c₀).jumps →
      sleLambda κ - Real.pi * chiC κ ≤ (shiftW 0 c₀).fn y + θ * chiC κ := by
    intro y hy hyJ
    obtain ⟨hyj, he⟩ := shiftW_zero_fn_of_notMem hc₀J hc₀ hyJ
    rw [he]; exact hR y hy hyj
  have h44w : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) (1 + 1)).2.2.2.1 1
      ≠ none → Cond44 κ (flowLineRhoL κ (reflWord (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω))).fn
        (reflWord (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω))).jumps 0
          (-instrAngle (StripSys.twoAngleSpec θ₀ t₀ θ) 1))
        (flowLineRhoR κ (reflWord (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω))).fn
          (reflWord (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω))).jumps 0
            (-instrAngle (StripSys.twoAngleSpec θ₀ t₀ θ) 1)) :=
    Eventually.of_forall fun _ _ => cond44_reflWord_stopWord hκ hκ4 (shiftW 0 c₀) θ₀ θ _ hθ hθπ hL' hR'
  filter_upwards [ae_stageDrv_eq_refl h44 hκ hκ4 hb hh hE hreg 1 hβ₁ hY₁ hpath₁ hker₁ h44w, hζ₀] with ω hω hω₀
  have h0 : (t₀ : ℝ≥0∞) < (E 0 ω).2 := by rw [hω₀.1]; exact ENNReal.coe_lt_top
  have hrec : rec₀ κ b jumps θ₀ θ t₀ E ω = recOf (t₀ : ℝ≥0∞) (E 0 ω) := pastMap_one_last ω
  obtain ⟨h1, h2, h3⟩ := hω (launch_one_of_lt h0)
  rw [hrec] at h2 h3
  exact ⟨h1, h2, h3⟩

/-- **A decreasing angle change is field determined** (R48-safe; spec p. 410, "the reflected condition applies"): for
the (4.4) heights of `b` at `θ₀`, the heights `b + θχ ≤ −λ` left and `b + θχ ≥ λ − πχ` right, and `θ ≤ θ₀ ≤ θ + π`
(the wall `β^{(r)}`: `θ₀ = π/2`, `θ = θ₂ ∈ [−π/2, π/2]`), both pieces are Borel functions of the field with infinite
lifetimes. -/
theorem isDetTwoPiece_of_heights_refl (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ) (hθ : θ ≤ θ₀)
    (hθπ : θ₀ ≤ θ + Real.pi) : IsDetTwoPiece P h E := by
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  set D₀ : DistOn upperHalfPlaneOpens → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun f =>
    admDrv h44 hκ hκ4 θ₀ (shiftW 0 c₀, flowField 0 0 f) with hD₀def
  have hD₀ : Measurable D₀ :=
    (measurable_admDrv h44 hκ hκ4 θ₀).comp (measurable_const.prodMk (measurable_flowField 0 0))
  have hD₀r : ∀ f, IsRegularDriver (D₀ f) := fun f => admDrv_regular h44 hκ hκ4 θ₀ _
  have hR₀ : Measurable fun f => recOf (t₀ : ℝ≥0∞) (D₀ f) := measurable_recOf hD₀ hD₀r _
  set D₁ : DistOn upperHalfPlaneOpens → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun f =>
    negDrv (admDrv h44 hκ hκ4 (-θ) (reflWord (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (D₀ f))),
      reflField (field₁ κ (recOf (t₀ : ℝ≥0∞) (D₀ f)) f))) with hD₁def
  have hD₁ : Measurable D₁ := by
    refine measurable_negDrv.comp ((measurable_admDrv h44 hκ hκ4 (-θ)).comp
      ((measurable_reflWord.comp ((measurable_word₁ κ θ₀ c₀).comp hR₀)).prodMk ?_))
    exact FlowReflect.measurable_reflField.comp
      (Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => field₁ κ p.1 p.2)
        (f := fun f => (recOf (t₀ : ℝ≥0∞) (D₀ f), f)) (measurable_field₁ κ) (hR₀.prodMk measurable_id))
  refine ⟨D₀, D₁, hD₀, hD₁, hD₀r, fun f => isRegularDriver_negDrv (admDrv_regular h44 hκ hκ4 (-θ) _), ?_⟩
  filter_upwards [ae_drv_zero h44 hκ hκ4 hb hh hE hreg hc₀J hc₀ hL0 hR0,
    ae_drv_one_refl h44 hκ hκ4 hb hh hE hreg hc₀J hc₀ hL0 hR0 hL hR hθ hθπ] with ω h0 h1
  have e0 : E 0 ω = D₀ (h ω) := by
    refine Prod.ext (funext fun t => ?_) h0.2.1.symm
    refine (h0.2.2 t ?_).symm
    rw [h0.1]; exact ENNReal.coe_lt_top
  refine ⟨h0.1, h1.1, e0, ?_⟩
  rw [e0] at h1
  refine Prod.ext (funext fun t => ?_) h1.2.1.symm
  show (E 1 ω).1 t = -(admDrv h44 hκ hκ4 (-θ) _).1 t
  rw [h1.2.2 t (by rw [h1.1]; exact ENNReal.coe_lt_top), neg_neg]

end Strip

end StripWall

end Sec7

end InteractingSLE
