/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2HFlow
import InteractingSLE.Spec.Supplement.SBLvStage
import InteractingSLE.Spec.Supplement.SB2HEntry
import InteractingSLE.Spec.Supplement.SB2Remainder

/-!
# SB2(1) in entry form from K2's conclusion in the recentred launch chart

Packet PROVE-T14-SB2FIN3. SB2(1)'s target is the entry form `Lx.SB2UpperLaunchEntryStatement` (ruling R91; it implies
the R87 launch form `Lv.SB2UpperLaunchStatement`): for every witness `(b', jumps', h')` of the lower walk's launch
clause, a flow line of `h'` from the entry `m = e_L ≤ 0` of the launch chart. K2
(`SB.Cond.isCondFlowLineDriverOn_of_markedKernel`) concludes `SB.IsCondFlowLineDriverOn` — a flow-line driver from `0`
of the field read in a random chart, conditionally on `𝒢 = pastSigma … k`, on a live event. This file states SB2(1)
in exactly the form K2 produces, in the launch chart `c = launchChart …` recentred at its entry point
`m = launchEntry …` (`Lx.leftEntry c (realMin (lowerPrefix …))`, the only possible `m`), with the two clauses K2 does
not touch (SB2(1)'s active word and its pathwise link), and proves the target from it:

* **`SB2RelDriverStatement`** (named input, Lemma SB2(1) in K2's output form): almost surely on the launch event
  `m ≤ 0`; conditional data `(bc, jc)` and a relative driver
  `W` with lifetime `ζr` such that K2's conclusion holds in `c.recenter m` (K2's input `hG`, the GFF law of that chart
  field, follows from it: `GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver`); every witness read in `c` carries
  SB2(1)'s active word on `(m, 0)`; and the relative curve (Theorem 1.3's chosen trace of `W`, moved to `m`) is linked
  pathwise to the actual upper flow;
* **`sb2UpperLaunchEntryStatement_of_relDriver`**: Theorem 1.3 and `SB2RelDriverStatement` give the entry form
  (through `isFlowLine_of_recenter_driver` and `GW2aSingle.ae_chosenTrace`; the launch chart is conformal with a
  continuous lift by `StagedPiecesRegular` and `GW2aCont.isConformal_runChart`); `sb2UpperLaunchStatement_of_relDriver`:
  the R87 launch form;
* **`ae_isLeftEntryValue_launchEntry`**: almost surely at a launch `m` IS the entry value of `c`
  (`Lx.isLeftEntryValue_launchChart`, `SB2HEntry`), so the entry clause of the target needs only `m ≤ 0`.

R48: Theorem 1.3 is a hypothesis; this serves Theorem 1.4 only.
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

open Sec4

/-- **Named input: Lemma SB2(1) in K2's output form** (supplement pp. 630–633, `source/spec/p625-671.md` L113–L133,
the entry L117 and L161; the setting and hypotheses of `SB2UpperLaunchStatement`). Write `c = launchChart … k` for the
lower walk's launch chart and `m = launchEntry … k u` for its entry point `e_L = g_A(L⁻)` at `L = min(A ∩ ℝ)` (that
it is the entry value, `Lx.IsLeftEntryValue`, ruling R91, is proved: `ae_isLeftEntryValue_launchEntry`). Almost
surely on the launch event `m ≤ 0`; and there are
conditional data `(bc, jc)` and a relative driver `W` with lifetime `ζr` such that, conditionally on the lower walk's
past `pastSigma … k`, on the launch event:

1. (K2's conclusion) `W` is the angle-`ψ` flow-line driver of the field read in `c` recentred at `m`, with data `bc`;
2. (SB2(1)'s active word) every witness `(b', jumps', h')` read in `c` has SB2(1)'s active word on `(m, 0)`;
3. (SB2(1)'s link) almost surely the relative curve — Theorem 1.3's chosen trace of `W`, moved to `m` — is linked to the
   actual upper flow by `IsRemainderLink`. -/
def SB2RelDriverStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) →
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k → launchEntry κ b jumps E k u ω₀ ≤ 0) ∧
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

/-- **The entry-value half of SB2(1)'s entry clause is automatic** (ruling R91): almost surely, at a launch of the
lower walk, the launch chart has the entry value `launchEntry` at `L = realMin (lowerPrefix …)`
(`Lx.isLeftEntryValue_launchChart`: the retained prefix is compact before the walk is finished, the pieces being
regular by `StagedPiecesRegular`). -/
theorem ae_isLeftEntryValue_launchEntry {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hER : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))) (k : ℕ) (u : ℝ) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
      Lx.IsLeftEntryValue (launchChart κ b jumps E k ω₀) (realMin (lowerPrefix κ b jumps E k u ω₀))
        (launchEntry κ b jumps E k u ω₀) := by
  filter_upwards [hER] with ω₀ hR₀ hF
  exact Lx.isLeftEntryValue_launchChart (fun j c' θ' hl' =>
    hR₀ j θ' _ c' (Exist.StagedLaw.eq_launch_of_launches _ _ hl').1 hl') hF

/-- **Lemma SB2(1) in entry form from K2's output form** (with Theorem 1.3 for the relative curve; ruling R91): the
launch chart of the named input is the launch chart of the target, the flow-line driver in the recentred chart
becomes, for every witness of the launch clause, the flow line from `m` (`isFlowLine_of_recenter_driver`), and the
entry, the active word and the link are the input's. -/
theorem sb2UpperLaunchEntryStatement_of_relDriver (h13 : Exist.Theorem13Statement.{u})
    (hrel : SB2RelDriverStatement.{u}) : Lx.SB2UpperLaunchEntryStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hER k u ψ hu hψ hL hH η ζ hη hone
  obtain ⟨bc, jc, W, ζr, hcc, hK, hword, hlink⟩ :=
    hrel κ hκ hκ4 b jumps hb P h hh E hE hER k u ψ hu hψ hL hH η ζ hη hone
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  filter_upwards [hcc, hK, hword, hlink, hER _ hprog, ae_isLeftEntryValue_launchEntry (hER _ hprog) k u]
    with ω₀ hcc₀ hK₀ hword₀ hlink₀ hR₀ hent₀
  intro c₀ θ hlaunch b' J' h' hb' hT' hG'
  have hF := mem_launchSet hlaunch
  have hc0 := launchChart_eq hlaunch
  have hm := hcc₀ hF
  have hent := hent₀ hF
  obtain ⟨hbc, h'', hT'', hdrv⟩ := hK₀ hF
  rw [hc0] at hent hT'' hword₀ hlink₀
  -- the launch chart is the run's chart before the launch: conformal, continuous lift (`StagedPiecesRegular`)
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

/-- The R87 launch form, through the entry form (`Lx.sb2UpperLaunchStatement_of_entry`). -/
theorem sb2UpperLaunchStatement_of_relDriver (h13 : Exist.Theorem13Statement.{u})
    (hrel : SB2RelDriverStatement.{u}) : SB2UpperLaunchStatement.{u} :=
  Lx.sb2UpperLaunchStatement_of_entry (sb2UpperLaunchEntryStatement_of_relDriver h13 hrel)

end InteractingSLE.Theorem14.SB.Lv
