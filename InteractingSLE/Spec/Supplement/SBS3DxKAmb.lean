/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KAmb
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen

/-!
# Successor of `SB2KAmb` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SB2KAmb` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `SB2RelCoreAmbLeStatement`;
* `SB2RelCoreAmbRegLeStatement`;
* `SB2RelCoreAmbRegSuccLeStatement`;
* `sb2UpperLaunchEntryLAmbStatement_of_coreLe`;
* `sb2RelCoreAmbStatement_of_regLe`;
* `sb2RelCoreAmbRegStatement_of_succLe`;
* `sb2UpperLaunchEntryLAmbStatement_of_succLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Sec4 Exist.Staged

/-- **Named input: SB2(1)'s clauses (1)–(3) in K2's output form, in GW1's ambient setting** (`SB2RelDriverLStatement`
with R95's premise `Ly.LowerLeftAdmissible` and without the clause `m ≤ 0`, which GW1-EXTREC proves there). -/
def SB2RelCoreAmbLeStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    Ly.LowerLeftAdmissible κ b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ → ∀ [Fact (ψ ≤ Real.pi / 2)],
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      (∀ᵐ ω ∂P, Lx.LowerLaunch κ b jumps E k ω → ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
        IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) →
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      IsCondFlowLineDriverOn κ ψ (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) P (launchSet κ b jumps E k) h
        (fun ω => (launchChart κ b jumps E k ω).recenter (launchEntry κ b jumps E k u ω)) bc jc W ζr ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport (launchChart κ b jumps E k ω₀) 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h' b' jumps' →
          IsActiveLowWord κ b jumps u b' jumps' (launchEntry κ b jumps E k u ω₀)) ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀),
          IsRemainderLink (launchChart κ b jumps E k ω₀) (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω))
            (fun t => GW2aSingle.chosenTrace W ζr ω t + launchEntry κ b jumps E k u ω₀) (ζr ω))

/-- **`SB2RelCoreAmbLeStatement` for families regular at every sample.** -/
def SB2RelCoreAmbRegLeStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    Ly.LowerLeftAdmissible κ b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (j : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec j ω)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ → ∀ [Fact (ψ ≤ Real.pi / 2)],
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      (∀ᵐ ω ∂P, Lx.LowerLaunch κ b jumps E k ω → ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
        IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) →
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      IsCondFlowLineDriverOn κ ψ (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) P (launchSet κ b jumps E k) h
        (fun ω => (launchChart κ b jumps E k ω).recenter (launchEntry κ b jumps E k u ω)) bc jc W ζr ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport (launchChart κ b jumps E k ω₀) 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h' b' jumps' →
          IsActiveLowWord κ b jumps u b' jumps' (launchEntry κ b jumps E k u ω₀)) ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀),
          IsRemainderLink (launchChart κ b jumps E k ω₀) (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω))
            (fun t => GW2aSingle.chosenTrace W ζr ω t + launchEntry κ b jumps E k u ω₀) (ζr ω))

/-- **`SB2RelCoreAmbRegLeStatement` at the launches after the first** (`k + 1` in place of `k`). -/
def SB2RelCoreAmbRegSuccLeStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    Ly.LowerLeftAdmissible κ b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (j : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec j ω)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ → ∀ [Fact (ψ ≤ Real.pi / 2)],
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      (∀ᵐ ω ∂P, Lx.LowerLaunch κ b jumps E (k + 1) ω → ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
        IsOneSided (lowerPrefix κ b jumps E (k + 1) u ω) (η ω) a) →
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      IsCondFlowLineDriverOn κ ψ (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) P (launchSet κ b jumps E (k + 1)) h
        (fun ω => (launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω)) bc jc W ζr ∧
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

/-- **SB2(1) in GW1's ambient setting (the form SB3 consumes) from its clauses (1)–(3)**. -/
theorem sb2UpperLaunchEntryLAmbStatement_of_coreLe (h13 : Exist.Theorem13Statement.{u})
    (hrel : SB2RelCoreAmbLeStatement.{u}) : Ly.SB2UpperLaunchEntryLAmbLeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hER k u ψ hu hψ _ hL hH η ζ hη hone
  obtain ⟨bc, jc, W, ζr, hK, hword, hlink⟩ :=
    hrel κ hκ hκ4 b jumps hb P h hh hadm E hE hER k u ψ hu hψ hL hH η ζ hη hone
  have hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ := fun t ht htJ =>
    Ly.height_lt_of_cumWeightLeft hκ (hadm t ht htJ)
  have hcc := GW1Ext.ae_launchEntry_nonpos_of_ambient hκ hb hh hE hER hamb k hu
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  unfold Ly.SB2UpperConclAt
  filter_upwards [hcc, hK, hword, hlink, hER _ hprog, ae_isLeftEntryValue_launchEntry (hER _ hprog) k u]
    with ω₀ hcc₀ hK₀ hword₀ hlink₀ hR₀ hent₀
  intro c₀ θ hlaunch b' J' h' hb' hT' hG'
  have hF := mem_launchSet hlaunch
  have hc0 := launchChart_eq hlaunch
  have hm := hcc₀ hF
  have hent := hent₀ hF
  obtain ⟨hbc, h'', hT'', hdrv⟩ := hK₀ hF
  rw [hc0] at hent hT'' hword₀ hlink₀
  obtain ⟨-, -, hcr⟩ := Exist.StagedLaw.eq_launch_of_launches _ _ hlaunch
  obtain ⟨hcf, hℓ⟩ := GW2aCont.isConformal_runChart _ _ k fun j _ c' θ' hl' =>
    hR₀ j θ' _ c' (Exist.StagedLaw.eq_launch_of_launches _ _ hl').1 hl'
  rw [← hcr] at hcf hℓ
  have hG'' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hbc hdrv
  have htr := GW2aSingle.ae_chosenTrace h13 hκ hdrv
  refine ⟨launchEntry κ b jumps E k u ω₀,
    fun ω t => GW2aSingle.chosenTrace W ζr ω t + launchEntry κ b jumps E k u ω₀, ζr, hm, hent,
    hword₀ hF b' J' h' hb' hT' hG', ?_, hlink₀ hF⟩
  exact isFlowLine_of_recenter_driver hcf hℓ hb' hbc hT' hT'' hG' hG'' hdrv
    (htr.mono fun ω hω => hω.1)

/-- **The ambient input for general families from the form for families regular at every sample** (the
regularized family `StagedReg.regFam E`; the proof of FIN4's `sb2RelCoreCfStatement_of_reg`, with S1 at launch
samples). -/
theorem sb2RelCoreAmbStatement_of_regLe (h13 : Exist.Theorem13Statement.{u})
    (hrel : SB2RelCoreAmbRegLeStatement.{u}) : SB2RelCoreAmbLeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hER k u ψ hu hψ _ hL hH η ζ hη hS1
  set w : ExplSpec := (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) with hwdef
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hR' : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (StagedReg.regFam E spec) := fun spec hs =>
    Exist.StagedLaw.stagedPiecesRegular_of_regular h13 hκ hb (hE' spec hs) (hreg' spec)
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hrw := hrun _ hw
  have hpm' : Measurable (pastMap κ b jumps w (StagedReg.regFam E w) k) :=
    Measurable.of_comap_le ((hE' _ hw).2.1 k)
  have hpm : Measurable (pastMap κ b jumps w (E w) k) := Measurable.of_comap_le ((hE _ hw).2.1 k)
  have hK : ∀ᵐ ω₀ ∂P, condExpKernel P (pastSigma κ b jumps w (StagedReg.regFam E w) k) ω₀ =
      condExpKernel P (pastSigma κ b jumps w (E w) k) ω₀ :=
    StagedReg.ae_condExpKernel_eq_of_ae_eq hpm' hpm (StagedReg.ae_pastMap_regHist (hER _ hw) k)
  have hS1' : ∀ᵐ ω ∂P, Lx.LowerLaunch κ b jumps (StagedReg.regFam E) k ω → ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
      IsOneSided (lowerPrefix κ b jumps (StagedReg.regFam E) k u ω) (η ω) a := by
    filter_upwards [hS1, hrw] with ω hω hr hl a ha
    have e := launch_objects_eq_of_run_eq hr k u
    rw [e.2.2.1]
    exact hω (e.2.2.2.2.1 hl) a ha
  obtain ⟨bc, jc, W, ζr, h1, h2, h3⟩ :=
    hrel κ hκ hκ4 b jumps hb P h hh hadm (StagedReg.regFam E) hE' hR' hreg' k u ψ hu hψ hL hH η ζ hη hS1'
  refine ⟨bc, jc, W, ζr, ?_, ?_, ?_⟩
  · filter_upwards [h1, hrw, hK] with ω₀ hω₀ hr hk hF
    have e := launch_objects_eq_of_run_eq hr k u
    rw [← e.2.1, ← e.2.2.2.1, ← hk]
    exact hω₀ (e.1.2 hF)
  · filter_upwards [h2, hrw, hK] with ω₀ hω₀ hr hk hF b' J' h' hb' hT' hG'
    have e := launch_objects_eq_of_run_eq hr k u
    rw [← e.2.1] at hT'
    rw [← hk] at hG'
    rw [← e.2.2.2.1]
    exact hω₀ (e.1.2 hF) b' J' h' hb' hT' hG'
  · filter_upwards [h3, hrw, hK, Sec7.Aux122Disint.ae_ae_condExpKernel ((hE _ hw).2.1 k) hrw]
      with ω₀ hω₀ hr hk hrr hF
    have e := launch_objects_eq_of_run_eq hr k u
    rw [← hk]
    filter_upwards [hω₀ (e.1.2 hF), (show ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w
        (StagedReg.regFam E w) k) ω₀), _ from hk ▸ hrr)]
      with ω hω hrω
    have e' := launch_objects_eq_of_run_eq hrω k u
    rw [← e.2.1, ← e.2.2.2.1, ← e'.2.2.1]
    exact hω

/-- **The regular ambient input from the launches after the first** (`k = 0` is `relCoreCf_zero`). -/
theorem sb2RelCoreAmbRegStatement_of_succLe (h13 : Exist.Theorem13Statement.{u})
    (hs : SB2RelCoreAmbRegSuccLeStatement.{u}) : SB2RelCoreAmbRegLeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hER hreg k u ψ hu hψ _ hL hH η ζ hη hS1
  cases k with
  | zero => exact relCoreCf_zero h13 hκ hb hh E hu hη
  | succ k => exact hs κ hκ hκ4 b jumps hb P h hh hadm E hE hER hreg k u ψ hu hψ hL hH η ζ hη hS1

/-- **SB2(1) in the ambient form SB3 consumes, from the launches after the first** (Theorem 1.3 and
`SB2RelCoreAmbRegSuccLeStatement`). -/
theorem sb2UpperLaunchEntryLAmbStatement_of_succLe (h13 : Exist.Theorem13Statement.{u})
    (hs : SB2RelCoreAmbRegSuccLeStatement.{u}) : Ly.SB2UpperLaunchEntryLAmbLeStatement.{u} :=
  sb2UpperLaunchEntryLAmbStatement_of_coreLe h13
    (sb2RelCoreAmbStatement_of_regLe h13 (sb2RelCoreAmbRegStatement_of_succLe h13 hs))

end InteractingSLE.Theorem14.SB.Lv
