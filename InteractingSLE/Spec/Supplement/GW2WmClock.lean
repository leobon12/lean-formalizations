/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WmDec
import InteractingSLE.Spec.Supplement.GW2StmPairEq
import InteractingSLE.Spec.Supplement.GW2GmBack

/-!
# GW2's stage word map, part 5: the decoder's boundaries are GB6's relative clock (root `0`)

Packet PROVE-GW2-GEOM2 (round 7). The decoder `GW2Wm.stageDec` reads the intermediate relative stage boundaries by
ROOT2's capacity reader at the physical stage times `T_j = schedTime 0 L j` of the program, applied to the decoded
counterflow record and the joined physical record. At root `0` this reading IS GB6's relative clock at `T_j`, before
the first contact, as soon as the joined physical driver agrees with the explored driver up to `T_j`:

* **`stageRead_zero_eq_relClock`** (one sample; the hypotheses are those of STAGEMEAN's
  `GW2Stm.forwardCapacity_agree`, with the explored driver complete);
* **`stageDec_augRec_of_clock`**: hence the decoder returns the records of the instance's relative driver between
  the boundaries `min (ofReal (relClock … T_j)) (stgStart T)` — the relative clock of the earlier physical stage
  ends, clipped at the instance's stage start.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Wm

open Restart Exist.Staged Exist.StagedLaw Supp8.GB6 GW2TipSystem

section Clock

variable {Ω : Type*} {Wα W : ℝ≥0 → Ω → ℝ} {ζα ζ : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ} {s : ℝ≥0} {ω : Ω}

/-- **At root `0` the decoder's boundary reading is GB6's relative clock** at the physical stage time `T_j`, before
the first contact, when the joined physical driver of the decoded pieces agrees with the explored driver up to `T_j`. -/
theorem stageRead_zero_eq_relClock (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (z : RecData)
    (P : Fin N → RecData) (hz : decHist N z = (cfRec s Wα ζα ω, P)) (j : ℕ)
    (hjT : GW2Schedule.schedTime 0 L j ≤ Sec5.Prop513Schedule.lastTime 0 L)
    (hagree : ∀ u ≤ GW2Schedule.schedTime 0 L j,
      RootJ31.joinedRead L (fun i => P (Fin.cast hN i)) u = W u ω)
    (hW0α : Wα 0 ω = 0) (hWcα : ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω})
    (hα : IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (hs : (s : ℝ≥0∞) < ζα ω) (hsH : α ω s ∈ H)
    (hζ : ζ ω = ⊤) (hW0 : W 0 ω = 0) (hWc : Continuous fun t => W t ω)
    (hγ : IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (hq : (GW2Schedule.schedTime 0 L j : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
      ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s)) :
    stageRead 0 s L N hN z j =
      relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) (GW2Schedule.schedTime 0 L j) := by
  set q := GW2Schedule.schedTime 0 L j with hqdef
  have key := GW2Stm.forwardCapacity_agree (g := fun _ => cfRec s Wα ζα ω) (W := W) (ζ := ζ) hW0α hWcα hα hs hsH
    hζ hW0 hWc hγ rfl q hq
  rw [← key]
  unfold stageRead
  rw [hz]
  have hJ := RootJ31.continuous_joinedRead L (fun i => P (Fin.cast hN i))
  have hcf : cfRec q W ζ ω = recOf (q : ℝ≥0∞) ((fun t => W t ω), ⊤) := by
    unfold cfRec
    rw [GW2JointKernel.cfE_eq q hζ hW0 hWc]
  have hEq : EqOn (rdrv (RootJ31.joinedRecord L fun i => P (Fin.cast hN i))) (rdrv (cfRec q W ζ ω))
      (Icc 0 (q : ℝ)) := by
    intro u hu
    have hu0 : (u.toNNReal : ℝ) = u := Real.coe_toNNReal _ hu.1
    have huq : u.toNNReal ≤ q := Real.toNNReal_le_iff_le_coe.2 hu.2
    rw [← hu0]
    unfold RootJ31.joinedRecord
    rw [Gm.rdrv_recOfDriver hJ.1 hJ.2, min_eq_left (huq.trans hjT), hagree _ huq, hcf,
      Gm.rdrv_recOf_eq (Gm.isRegularDriver_top hWc hW0) (by simp) (by simpa using hWc.continuousOn)]
    congr 1
    rw [show min (q : ℝ≥0∞) ((fun t => W t ω), (⊤ : ℝ≥0∞)).2 = q from min_eq_left le_top, ENNReal.toNNReal_coe,
      min_eq_left huq]
  have hH : QuantumZipper.fwdHull (rdrv (RootJ31.joinedRecord L fun i => P (Fin.cast hN i))) q =
      QuantumZipper.fwdHull (rdrv (cfRec q W ζ ω)) q :=
    LocalExt.fwdHull_congr_of_continuousOn (t' := (q : ℝ) + 1) (continuous_rdrv _).continuousOn
      (continuous_rdrv _).continuousOn q.coe_nonneg (by linarith) hEq
  unfold RootH29.forwardCapacity RootZ21.forwardCapacity RootH29.forwardHull RootZ21.forwardHull
    RootH29.translatedHull
  simp only [Complex.ofReal_zero, zero_add, Set.image_id']
  rw [hH]

end Clock

end InteractingSLE.Theorem14.GW2Wm
