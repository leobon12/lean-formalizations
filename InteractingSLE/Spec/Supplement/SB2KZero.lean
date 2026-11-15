/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JZero
import InteractingSLE.Spec.Supplement.BR4aPathField

/-!
# SB2(1) at the first launch: clauses (1)–(3), and the reduction of the named input to later launches

Packet PROVE-T14-SB2FIN5. At the first instruction (`k = 0`) of the lower walk the conditional law given the retained
past is `P`, the launch chart is the root chart and the entry point is the upper seed `u` (`SB2JZero`). There the
remaining input of SB2(1), `SB2RelCoreCfStatement` (ruling R96), holds outright for every family:

* clause (1): the upper flow `η` from `u`, translated by `−u` (`IsFlowLine.affine` with `a = 1`), is a flow line from
  `0` of `recField u h = h(· + u)`, the field read in `Chart.id.recenter u` (`BR4aPath.isChartTransport_recField`); at
  `x = 0` the frozen `IsFlowLine` unpacks to `IsFlowLineDriver` (`exists_driver_of_isFlowLine`);
* clause (2): `activeWord_zero` (PROVE-T14-SB2FIN4);
* clause (3): the first visit of `η` to `L = u` is time `0`, the clock is the identity, the lifetime is `ζ`, and the
  chosen trace plus `u` is `η` before `ζ` (uniqueness of the generating trace, `IsGeneratingTrace.eq_of_le`;
  Theorem 1.3 for the chosen trace) — `isRemainderLink_self`;
* **`relCoreCf_zero`**, and the reduction **`sb2RelCoreCfStatement_of_succ`**: SB2(1)'s remaining input follows from
  its form for families regular at every sample at the launches `k + 1` only (`SB2RelCoreCfRegSuccStatement`).

R48: Theorem 1.3 is a hypothesis; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open FlowDilate
open Sec4 Exist.Staged

/-- The field read in the chart recentred at `x` is the affine image `affField (−x)` with `a = 1`. -/
theorem flowField_eq_affField (x : ℝ) (f : DistOn upperHalfPlaneOpens) :
    Exist.flowField x 0 f = affField (-x) one_pos f := by
  ext φ
  rw [affField_apply, Exist.flowField_apply, zero_mul, add_zero]
  congr 1
  ext z
  rw [Exist.pushTest_shiftChart_apply, affTest_apply]
  simp [aff, sub_eq_add_neg]

/-- **The driver of a flow line from `x`**: translated by `−x`, an angle-`ψ` flow line from `x` of `h` is a flow line
from `0` of `h(· + x)` (data `b(· + x)` in the form `affData 1 (−x) b`), i.e. a flow-line driver with the same lifetime
whose generating trace is `η − x`. -/
theorem exists_driver_of_isFlowLine {κ ψ x : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hb : IsPiecewiseConstantBoundaryData b J) (hfl : IsFlowLine κ b J x ψ P h η ζ) :
    ∃ W : ℝ≥0 → Ω → ℝ, IsFlowLineDriver κ (affData 1 (-x) b) (affJumps 1 (-x) J) ψ P
      (fun ω => BR4aPath.recField x (h ω)) W ζ ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x) := by
  have h1 := hfl.affine (a := 1) (m := -x) one_pos hb
  have e0 : raff 1 (-x) x = 0 := by simp [raff]
  rw [e0] at h1
  have ef : (fun ω => affField (-x) one_pos (h ω)) = fun ω => BR4aPath.recField x (h ω) :=
    funext fun ω => (flowField_eq_affField x (h ω)).symm
  rw [ef] at h1
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hc, hgen⟩ := h1
  have ec : cDil 1 = 1 := by simp [cDil]
  refine ⟨W, ⟨h', 𝓕, VL, VR, B, htr, ?_⟩, ?_⟩
  · simpa [ec] using hc
  · filter_upwards [hgen] with ω hω
    convert hω using 2
    · simp [ec]
    · simp [ec, aff, sub_eq_add_neg]


/-- A flow-line driver is almost surely continuous before its lifetime and starts at `0`. -/
theorem ae_continuousOn_of_isFlowLineDriver {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b J θ P h W ζ) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
  obtain ⟨_, _, _, _, _, _, hC⟩ := hfl
  filter_upwards [hC.1.2.2.2.2] with ω hω
  exact ⟨hω.2.2.2.1, hω.1⟩

/-- **The remainder link of a curve with itself**: if `η - x` and `γ` are generating traces of one driver, continuous
before the lifetime and starting at `0`, then `γ + x` is the remainder of `η` after its first visit to `x` (time `0`),
read in the identity chart, with the same lifetime and the identity clock. -/
theorem isRemainderLink_self {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η γ : ℝ≥0 → ℂ} {x : ℝ}
    (hη : IsGeneratingTrace w ζ (fun t => η t - x)) (hγ : IsGeneratingTrace w ζ γ)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) :
    IsRemainderLink (Chart.id.recenter 0) η ζ x (fun t => γ t + x) ζ := by
  have h0 : η 0 = x := sub_eq_zero.1 hη.1
  have hv : firstVisit η ζ x = 0 := le_antisymm (iInf₂_le 0 ⟨zero_le, h0⟩) bot_le
  intro _
  refine ⟨id, rfl, strictMono_id, continuous_id, fun s => ⟨?_, fun hs _ => ?_⟩⟩
  · simp [hv]
  · have e := IsGeneratingTrace.eq_of_le hγ hη hw hw0 hs.le
    rw [Exist.StagedLaw.Chart.recenter_zero, hv]
    simp only [id, ENNReal.toNNReal_zero, zero_add]
    change γ s + x = η s
    rw [e]
    ring

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **SB2(1)'s clauses (1)–(3) at the first launch** (`k = 0`, for every family `E`; Theorem 1.3 for the chosen
trace): the driver of the upper flow `η` read from its seed `u` is the conditional flow-line driver in the root chart
recentred at the entry `u` (the conditional law given the trivial past is `P`); the active word is
`activeWord_zero`; the remainder after the first visit to `L = u` (time `0`) is the whole curve. -/
theorem relCoreCf_zero (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {u ψ : ℝ} (hu : u ≤ 0) {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps u ψ P h η ζ) :
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      IsCondFlowLineDriverOn κ ψ (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) 0) P (launchSet κ b jumps E 0) h
        (fun ω => (launchChart κ b jumps E 0 ω).recenter (launchEntry κ b jumps E 0 u ω)) bc jc W ζr ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E 0 →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport (launchChart κ b jumps E 0 ω₀) 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) 0) ω₀) h' b' jumps' →
          IsActiveLowWord κ b jumps u b' jumps' (launchEntry κ b jumps E 0 u ω₀)) ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E 0 →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) 0) ω₀),
          IsRemainderLink (launchChart κ b jumps E 0 ω₀) (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E 0 u ω))
            (fun t => GW2aSingle.chosenTrace W ζr ω t + launchEntry κ b jumps E 0 u ω₀) (ζr ω)) := by
  obtain ⟨W, hW, hgen⟩ := exists_driver_of_isFlowLine hb hη
  refine ⟨fun _ => affData 1 (-u) b, fun _ => affJumps 1 (-u) jumps, W, ζ, ?_, activeWord_zero hb hh hu, ?_⟩
  · refine Eventually.of_forall fun ω₀ _ => ⟨isPiecewiseConstantBoundaryData_affData one_pos hb,
      fun ω => BR4aPath.recField u (h ω), fun ω => ?_, ?_⟩
    · show IsChartTransport ((launchChart κ b jumps E 0 ω₀).recenter (launchEntry κ b jumps E 0 u ω₀)) 1 0 (chiC κ)
        (h ω) (BR4aPath.recField u (h ω))
      rw [launchChart_zero, launchEntry_zero hu, Exist.StagedLaw.Chart.recenter_zero]
      exact BR4aPath.isChartTransport_recField _ u (h ω)
    · rw [condExpKernel_pastSigma_zero]
      exact hW
  · refine Eventually.of_forall fun ω₀ _ => ?_
    rw [condExpKernel_pastSigma_zero, launchChart_zero, launchEntry_zero hu]
    filter_upwards [GW2aSingle.ae_chosenTrace h13 hκ hW, hgen, ae_continuousOn_of_isFlowLineDriver hW]
      with ω hc hg hw
    rw [realMin_lowerPrefix_zero hu]
    exact isRemainderLink_self hg hc.1 hw.1 hw.2

/-- **`SB2RelCoreCfRegStatement` at the launches after the first** (`k + 1` in place of `k`; the first launch is
`relCoreCf_zero`). -/
def SB2RelCoreCfRegSuccStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (j : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec j ω)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E (k + 1) u ω) (η ω) a) →
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      IsCondFlowLineDriverOn κ ψ (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) P (launchSet κ b jumps E (k + 1)) h
        (fun ω => (launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω))
        bc jc W ζr ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport (launchChart κ b jumps E (k + 1) ω₀) 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) ω₀) h' b' jumps' →
          IsActiveLowWord κ b jumps u b' jumps' (launchEntry κ b jumps E (k + 1) u ω₀)) ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) ω₀),
          IsRemainderLink (launchChart κ b jumps E (k + 1) ω₀) (η ω) (ζ ω)
            (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
            (fun t => GW2aSingle.chosenTrace W ζr ω t + launchEntry κ b jumps E (k + 1) u ω₀) (ζr ω))

/-- **SB2(1)'s remaining input for regular families from the launches after the first** (`k = 0` is
`relCoreCf_zero`). -/
theorem sb2RelCoreCfRegStatement_of_succ (h13 : Exist.Theorem13Statement.{u})
    (hs : SB2RelCoreCfRegSuccStatement.{u}) : SB2RelCoreCfRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER hreg k u ψ hu hψ hL hH η ζ hη hS1
  cases k with
  | zero => exact relCoreCf_zero h13 hκ hb hh E hu hη
  | succ k => exact hs κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER hreg k u ψ hu hψ hL hH η ζ hη hS1

/-- **SB2(1)'s remaining input (R96) from its form for regular families at the launches after the first**
(`sb2RelCoreCfStatement_of_reg` after `sb2RelCoreCfRegStatement_of_succ`). -/
theorem sb2RelCoreCfStatement_of_succ (h13 : Exist.Theorem13Statement.{u})
    (hs : SB2RelCoreCfRegSuccStatement.{u}) : SB2RelCoreCfStatement.{u} :=
  sb2RelCoreCfStatement_of_reg h13 (sb2RelCoreCfRegStatement_of_succ h13 hs)

end InteractingSLE.Theorem14.SB.Lv
