/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PuDthF
import InteractingSLE.Spec.Supplement.GW2NgJunc
import InteractingSLE.Spec.Supplement.GW2RjBd

/-!
# The decoded root record is the counterflow record, in `gb6TS` (D81, the tip exclusion's stage-word side)

Packet PROVE-GW2-STAGEMEAN, R127 round (D81: "STAGEMEAN proves that the decoded root record is the counterflow record
in `gb6TS`"; the part of `goodX` NEARIMG2's `GW2Ni.flowSwallow_premises_schedWordMapX_of_mem` consumes). The stage word
`schedWordMapX` reads the root record `(decHist N y).1` of the augmented stage record `y`:

* `decHist_fst_eq_augσ`: that is the instance's counterflow decoder `augσ N y` (definitional);
* **`decHist_fst_srecX`**: on every sample, the decoded root record of an instance's stage record is the counterflow
  record `cfRec c.s c.W c.ζ ω` (`pairEnc.symm_apply_apply`, `stgRecDec_stageEncRec`);
* **`decHist_fst_mem_goodX_schedInstSX`**, `…_gb6TS_…`: on the record event of the corrected root-`x` instance it is
  in `goodX ⊆ gb6TS` (the record event lies in `aliveRecX`);
* `ae_decHist_fst_mem_goodX_of_mem_GT`, `…_gb6TS_…`: almost surely on ROOTX's good set `schedGTX` (`schedGTX_spec`);
* RELDET's (W) (its handoff, round 38, "What remains"), at the top's word map `baseWm cw`:
  * `β_schedInstSX_baseWm`: the instance's word is `schedWordMapX` at the candidate's angle;
  * `candAngle_mem_Ioo`: the candidate's angle is in `(−π/2, π/2)` (`c.hΘ`);
  * **`flowSwallow_premises_schedInstSX`**: on the record event, `0 < farJunctionX`, the total right weight is
    `< κ/2 − 2` and the word has the far height beyond `farJunctionX`;
  * **`exists_farJunction_schedInstSX`**: RELDET's form `∃ J θa, 0 < J ∧ θa ∈ Ioo (−π/2) (π/2) ∧ FarRAt …`.

Deterministic on the record event (no measure).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Pq

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  GW2Rz GW2Wm GW2Rd GW2Rv GW2Sde Supp8.GB6

/-- The decoded root record is the augmented record's counterflow decoder. -/
theorem decHist_fst_eq_augσ (N : ℕ) (z : RecData) : (GW2Wm.decHist N z).1 = augσ N z := rfl

/-- On the live records the decoded root record is good at the root. -/
theorem decHist_fst_mem_goodX_of_mem_aliveRecX {N : ℕ} {x₀ : ℝ} {s : ℝ≥0} {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    {z : RecData} (hz : z ∈ aliveRecX N x₀ s ρ) : (GW2Wm.decHist N z).1 ∈ goodX x₀ s :=
  hz.1

/-- On the live records the decoded root record is in `gb6TS`. -/
theorem decHist_fst_mem_gb6TS_of_mem_aliveRecX {N : ℕ} {x₀ : ℝ} {s : ℝ≥0} {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    {z : RecData} (hz : z ∈ aliveRecX N x₀ s ρ) : (GW2Wm.decHist N z).1 ∈ gb6TS s :=
  hz.1.1

section Inst

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The decoded root record of an instance's stage record is the counterflow record**, at every sample. -/
theorem decHist_fst_srecX (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (x₀ : ℝ) (ω : Ω) :
    (GW2Wm.decHist ((entryList l).length + 1) (I.srecX c r l x₀ ω)).1 = cfRec c.s c.W c.ζ ω := by
  show stgRecDec _ (pairEnc.symm (pairEnc (stageEncRec c r l ω, _))).1 = _
  rw [MeasurableEquiv.symm_apply_apply, stgRecDec_stageEncRec]
  rfl

/-- **On the record event of the corrected root-`x` instance the decoded root record is good** (`goodX`). -/
theorem decHist_fst_mem_goodX_schedInstSX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (GT : Set Ω) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (ch : GW2Sdh.SchedChoice Ω) {y : RecData} (hy : y ∈ (schedInstSX c r l a GT hA ch).E) :
    (GW2Wm.decHist ((entryList l).length + 1) y).1 ∈ goodX (rootPt r.1) c.s :=
  hy.2.1

/-- **On the record event of the corrected root-`x` instance the decoded root record is in `gb6TS`.** -/
theorem decHist_fst_mem_gb6TS_schedInstSX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (GT : Set Ω) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (ch : GW2Sdh.SchedChoice Ω) {y : RecData} (hy : y ∈ (schedInstSX c r l a GT hA ch).E) :
    (GW2Wm.decHist ((entryList l).length + 1) y).1 ∈ gb6TS c.s :=
  (decHist_fst_mem_goodX_schedInstSX c r l a GT hA ch hy).1

/-- **Almost surely on ROOTX's good set the decoded root record of any instance's stage record is good.** -/
theorem ae_decHist_fst_mem_goodX_of_mem_GT [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (I : StageInst Ω) :
    ∀ᵐ ξ ∂c.P, ξ ∈ schedGTX h13 c r l a →
      (GW2Wm.decHist ((entryList l).length + 1) (I.srecX c r l (rootPt r.1) ξ)).1 ∈ goodX (rootPt r.1) c.s := by
  filter_upwards [(schedGTX_spec h13 c r l a).2.2] with ξ hξ hG
  rw [decHist_fst_srecX]
  exact hξ.1 hG

/-- Almost surely on ROOTX's good set the decoded root record of any instance's stage record is in `gb6TS`. -/
theorem ae_decHist_fst_mem_gb6TS_of_mem_GT [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (I : StageInst Ω) :
    ∀ᵐ ξ ∂c.P, ξ ∈ schedGTX h13 c r l a →
      (GW2Wm.decHist ((entryList l).length + 1) (I.srecX c r l (rootPt r.1) ξ)).1 ∈ gb6TS c.s :=
  (ae_decHist_fst_mem_goodX_of_mem_GT h13 c r l a I).mono fun _ h hG => (h hG).1

/-- The candidate's angle is in the source's open range. -/
theorem candAngle_mem_Ioo (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    candAngle c r l a ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  rw [GW2Rj.candAngle_eq]
  exact c.hΘ (RootJ31.candidateAngle c r a).2

end Inst

/-! ### RELDET's (W) at the top's word map -/

section Top

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The word of the corrected root-`x` instance at the top's word map** is `schedWordMapX` at the candidate's
angle. -/
theorem β_schedInstSX_baseWm (cw : Wire.T14Cur.CfWord.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (GT : Set Ω) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V) :
    (schedInstSX c r l a GT hA (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a)).β =
      GW2Wm.schedWordMapX c.κ (cw Ω c r) (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
        (length_historyProgram c r l) (candAngle c r l a) := by
  show (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a).β = _
  rw [GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 (Wire.T14Cur.baseWm cw) c r l a]
  rfl

/-- **The premises of `FlowSwallowStatement` on the record event of the top's instance** (D81): the point
`farJunctionX` of the record is positive, the total right weight of the word is `< κ/2 − 2`, and the word has the
raised far height beyond `farJunctionX` (NEARIMG2's `flowSwallow_premises_schedWordMapX_of_mem` with the decoded root
record in `gb6TS` and the candidate's angle in `(−π/2, π/2)`). -/
theorem flowSwallow_premises_schedInstSX (cw : Wire.T14Cur.CfWord.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (GT : Set Ω) {R : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V) {y : RecData}
    (hy : y ∈ (schedInstSX c r l a GT hA (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a)).E) :
    0 < GW2Ni.farJunctionX (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
        (length_historyProgram c r l) y ∧
      ∑ j, flowLineRhoR c.κ
          ((schedInstSX c r l a GT hA (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a)).β y).fn
          ((schedInstSX c r l a GT hA (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a)).β y).jumps 0 0 j <
        c.κ / 2 - 2 ∧
      GW2Ni.FarRAt ((schedInstSX c r l a GT hA (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a)).β y)
        (sleLambda (16 / c.κ) - Real.pi * chiC c.κ + candAngle c r l a * chiC c.κ)
        (GW2Ni.farJunctionX (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
          (length_historyProgram c r l) y) := by
  rw [β_schedInstSX_baseWm cw c r l a GT hA]
  exact GW2Ni.flowSwallow_premises_schedWordMapX_of_mem c.hκ c.hκ4 (cw Ω c r) (rootPt r.1) c.s
    (historyProgram c r l) ((entryList l).length + 1) (length_historyProgram c r l) (candAngle_mem_Ioo c r l a) y
    (decHist_fst_mem_gb6TS_schedInstSX c r l a GT hA _ hy)

/-- **RELDET's (W) on the record event of the top's instance**, in its form: a positive point `J` and an angle
`θa ∈ (−π/2, π/2)` with the raised far height `λ′ − πχ + θa χ` beyond `J` (`J = farJunctionX`, `θa` the candidate's
angle). -/
theorem exists_farJunction_schedInstSX (cw : Wire.T14Cur.CfWord.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (GT : Set Ω) {R : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V) {y : RecData}
    (hy : y ∈ (schedInstSX c r l a GT hA (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a)).E) :
    ∃ J θa : ℝ, 0 < J ∧ θa ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
      GW2Ni.FarRAt ((schedInstSX c r l a GT hA (Wire.T14Cur.chL (Wire.T14Cur.baseWm cw) Ω c r l a)).β y)
        (sleLambda (16 / c.κ) - Real.pi * chiC c.κ + θa * chiC c.κ) J := by
  obtain ⟨hJ, -, hfar⟩ := flowSwallow_premises_schedInstSX cw c r l a GT hA hy
  exact ⟨_, _, hJ, candAngle_mem_Ioo c r l a, hfar⟩

/-- **RELDET's (W) at the top's instances** (`Wire.T14Cur.instC ver (baseWm cw)`, version `n`), on the stage record
of every sample on the record event. -/
theorem exists_farJunction_instC (ver : SchedVerXFamily.{u}) (cw : Wire.T14Cur.CfWord.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ) (h : GoodRoot c r) (ω : Ω)
    (hω : (Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).srecX c r l (rootPt r.1) ω ∈
      (Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).E) :
    ∃ J θa : ℝ, 0 < J ∧ θa ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
      GW2Ni.FarRAt ((Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).β
          ((Wire.T14Cur.instC ver (Wire.T14Cur.baseWm cw) Ω c r l a n h).srecX c r l (rootPt r.1) ω))
        (sleLambda (16 / c.κ) - Real.pi * chiC c.κ + θa * chiC c.κ) J :=
  exists_farJunction_schedInstSX cw c r l a _ _ hω

end Top

end InteractingSLE.Theorem14.GW2Pq
