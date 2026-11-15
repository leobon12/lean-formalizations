/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmMeanI

/-!
# GW2's open lines: the far-right height of GEOM2's word map at ROOTX's corrected instance

Packet PROVE-GW2-STAGEMEAN, R121 round. Discharges `hfar` of `pair_inst` / `meanX_inst` for GEOM2's stage word map
`GW2Wm.schedWordMapX … θa` at the history program:

* `decHist_srecX`: the root record decoded from the instance's stage record is the counterflow record;
* **`ae_farR_srecX`**: on the live event the word map at the stage record has the far-right height
  `λ'(16/κ) − πχ + θa χ` (`farR_schedWordMapX`, the counterflow's left mark is negative on the good records).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open Restart Exist Exist.Staged Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rd
  GW2Rz GW2Sde Supp8 Supp8.GB6 Supp8.Q3Stop

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The root record decoded from the instance's stage record is the counterflow record.** -/
theorem decHist_srecX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (x₀ : ℝ)
    (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (T : ℝ≥0) (ω : Ω) :
    (GW2Wm.decHist ((entryList l).length + 1)
      (stgRecX x₀ c.s c.W c.ζ W GT R V T (stageEncRec c r l) ω)).1 = gb6Rec c.s c.W c.ζ ω := by
  unfold GW2Wm.decHist stgRecX augRec
  rw [MeasurableEquiv.symm_apply_apply]
  exact GW2Rd.stgRecDec_stageEncRec c r l ω

/-- **The far-right height of GEOM2's word map at the instance's stage record**, on the live event. -/
theorem ae_farR_srecX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) (c' : BoundaryWord)
    (hN : (historyProgram c r l).length = (entryList l).length + 1) (θa : ℝ)
    (hβ : ch.β = GW2Wm.schedWordMapX c.κ c' (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
      hN θa) (w : WordType) :
    ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      GW2Wm.FarR (ch.β ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω))
        (sleLambda (16 / c.κ) - Real.pi * chiC c.κ + θa * chiC c.κ) := by
  set I := GW2Rv.schedInstSX c r l a GT hA ch with hIdef
  have hv := hA.1.1
  have hρ := hA.1.2.choose_spec
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r l (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  filter_upwards [hEgood, hGT.2.2] with ω hEω hGTω hlive
  have hωGT : ω ∈ GT := hGTω.2 (hEω hlive.1).1
  rw [hβ]
  refine farR_schedWordMapX c.hκ c' (rootPt r.1) c.s (historyProgram c r l) _ hN θa _ ?_
  have hd : (GW2Wm.decHist ((entryList l).length + 1) (I.srecX c r l (rootPt r.1) ω)).1 =
      gb6Rec c.s c.W c.ζ ω := decHist_srecX c r l (rootPt r.1) (schedW c r l a) GT R V (historyTime c r l) ω
  rw [hd]
  exact (physGoodX_tip_marks (hGT.1 ω hωGT)).2.2

end InteractingSLE.Theorem14.GW2Psm
