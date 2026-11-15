/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TjLoc
import InteractingSLE.Spec.Supplement.SB2VrBad
import InteractingSLE.Spec.Supplement.SB2VrRad
import InteractingSLE.Spec.Sec7.StripSysPath

/-!
# Review item N4, item 3: the candidate's death is its first entrance into the bad set (launch coordinates)

Packet PROVE-GW2-RELDET (DECISIONS-FABLE-2 §D10's argument, for GW2's candidate piece). Under the conditional law
`ν = condExpKernel P pastG ω₀` of the earlier pieces, the candidate is a flow line of the launch field, whose boundary
data is the launch word `b'` (`IsStagedHistory`). D10's two steps hold for every flow line of a GFF with boundary data
(PROVE-AUX61-NOJUMP, `SB2VrBad`, `SB2VrRad`):
* before its lifetime the flow line never meets the closure of its word's bad set (bad points force a threshold;
  the other limit points are marks of outward weight `> −2 > κ/2 − 4`, never visited by Lemma G12,
  `g12FlowStatement`);
* at a finite positive lifetime the tip is a bad point.

* `isFlowLine_of_isFlowLineDriver`: a flow-line driver with almost sure traces is a flow line of the chosen traces;
* **`ae_candidate_life_badEntrance`**: for `P`-almost every `ω₀`, at a launch of the candidate, under `ν` the
  candidate's launch trace stays off the closed bad set of the launch word before its lifetime and, at a finite
  positive lifetime, is at a bad point. So its lifetime is its first entrance into that closed set.

The statement is in the launch chart. Reading it with D10's set of the ORIGINAL data and GB6's physical trace (the
life gauge of PROVE-GW2-SDE's `GW2SdzLife`) needs the boundary correspondence of the launch chart (see the handoff).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  Sec7.StripSysPath

open scoped Classical in
/-- **A flow-line driver with almost sure traces is a flow line** of the chosen traces (from `0`). -/
theorem isFlowLine_of_isFlowLineDriver {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hW : IsFlowLineDriver κ b jumps θ P h W ζ) (htr : ∀ᵐ ω ∂P, HasTrace (fun t => W t ω) (ζ ω)) :
    IsFlowLine κ b jumps 0 θ P h
      (fun ω => if hT : HasTrace (fun t => W t ω) (ζ ω) then hT.choose else fun _ => 0) ζ := by
  obtain ⟨h', 𝓕, VL, VR, B, htr', hC⟩ := hW
  refine ⟨h', 𝓕, W, VL, VR, B, htr', hC, ?_⟩
  filter_upwards [htr] with ω hω
  simp only [hω, ↓reduceDIte]
  simp only [Complex.ofReal_zero, sub_zero]
  exact hω.choose_spec.1

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The candidate's death is its first entrance into the closed bad set of its launch word** (D10's argument under
the conditional law of the earlier pieces, Theorem 1.3). -/
theorem ae_candidate_life_badEntrance (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω₀ ∂c.P, ∀ (cL : Chart) (θ : ℝ), GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) →
      ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ),
        IsPiecewiseConstantBoundaryData b' jumps' ∧ (∀ ω, IsChartTransport cL 1 0 (chiC c.κ) (c.h ω) (h' ω)) ∧
        IsFlowLine c.κ b' jumps' 0 θ (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) h' η
          (fun ω => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2) ∧
        ∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀),
          0 < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 →
          (∀ t : ℝ≥0, (t : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 →
            η ω t ∉ closure (SB.Vr.badSet (flowLineXL b' jumps' 0) (flowLineXR b' jumps' 0)
              (flowLineRhoL c.κ b' jumps' 0 θ) (flowLineRhoR c.κ b' jumps' 0 θ))) ∧
          ((GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 ≠ ⊤ →
            SB.Vq.IsBadPoint (flowLineXL b' jumps' 0) (flowLineXR b' jumps' 0) (flowLineRhoL c.κ b' jumps' 0 θ)
              (flowLineRhoR c.κ b' jumps' 0 θ)
              (η ω (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2.toNNReal)) := by
  set x := rootPt r.1 with hx
  set L := futureProgram c r l a with hL
  set spec := GW2Olm.futSpec c r l a with hspec
  set E := GW2Olm.futFam c r l a with hEdef
  set k := GW2Olm.curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  filter_upwards [hS.2.2.2 k, IsStagedHistory.ae_ae_hasTrace (theorem13LowStatement_of_theorem13 h13) c.hκ c.hκ4
    hS k] with ω₀ hst htr cL θ hl
  obtain ⟨b', j', h', hb', htr', hW⟩ := hst cL θ hl
  have hfl := isFlowLine_of_isFlowLineDriver hW (htr cL θ hl)
  have hgff := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb' hW
  refine ⟨b', j', h', _, hb', htr', hfl, ?_⟩
  filter_upwards [SB.Vr.ae_notMem_closure_badSet c.hκ c.hκ4 hb' hgff hfl, SB.Vr.ae_tip_bad_of_isFlowLine hfl]
    with ω h1 h2 hζ0
  refine ⟨fun t ht => ?_, fun hζt => ?_⟩
  · have := h1 hζ0 t ht
    simpa only [Complex.ofReal_zero, sub_zero] using this
  · have := h2 hζ0 hζt
    simpa only [Complex.ofReal_zero, sub_zero] using this

end InteractingSLE.Theorem14.GW2Rd
