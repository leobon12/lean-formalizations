/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2HWire
import InteractingSLE.Spec.Supplement.SBLxInduct

/-!
# SB2(1)'s named input with S1 only at launch samples (ruling R94)

Packet PROVE-T14-SB2FIN4. Ruling R94 makes SB2(1)'s target `Lx.SB2UpperLaunchEntryLStatement` (S1 assumed only where
instruction `k` launches: after an infinite earlier piece the prefix is the whole unbounded walk, where S1 is not
available). PROVE-T14-SB2FIN3's named input `SB2RelDriverStatement` assumes S1 at every sample; this file restates it
with the weaker premise and re-proves the wiring:

* **`SB2RelDriverLStatement`**: `SB2RelDriverStatement` with the S1 premise only on `Lx.LowerLaunch`;
* **`sb2UpperLaunchEntryLStatement_of_relDriverL`**: Theorem 1.3 and `SB2RelDriverLStatement` give R94's target (the
  proof of `sb2UpperLaunchEntryStatement_of_relDriver`, which never uses S1 itself);
* `sb2RelDriverStatement_of_L`: the L-form implies FIN3's form (its premise is weaker).

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

/-- **Named input: Lemma SB2(1) in K2's output form, S1 at launch samples** (ruling R94; otherwise exactly
`SB2RelDriverStatement`, PROVE-T14-SB2FIN3): the conclusion — `m ≤ 0` on the launch event, K2's conditional
flow-line driver in the launch chart recentred at its entry `m = launchEntry …`, SB2(1)'s active word for every
witness, and the pathwise link — under S1 assumed only where instruction `k` of the lower walk launches. -/
def SB2RelDriverLStatement : Prop :=
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
      (∀ᵐ ω ∂P, Lx.LowerLaunch κ b jumps E k ω → ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
        IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) →
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

/-- **Lemma SB2(1) in R94's entry form from K2's output form** (the proof of
`sb2UpperLaunchEntryStatement_of_relDriver`, verbatim: S1 is only passed on to the named input). -/
theorem sb2UpperLaunchEntryLStatement_of_relDriverL (h13 : Exist.Theorem13Statement.{u})
    (hrel : SB2RelDriverLStatement.{u}) : Lx.SB2UpperLaunchEntryLStatement.{u} := by
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


/-- The launch-sample form of the named input implies PROVE-T14-SB2FIN3's form (its S1 premise is weaker). -/
theorem sb2RelDriverStatement_of_L (h : SB2RelDriverLStatement.{u}) : SB2RelDriverStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ hh' hh E hE hER k u ψ hu hψ hL hH η ζ hη hS1
  exact h κ hκ hκ4 b jumps hb P hh' hh E hE hER k u ψ hu hψ hL hH η ζ hη (hS1.mono fun _ hω _ => hω)

end InteractingSLE.Theorem14.SB.Lv
