/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3KernelWord
import InteractingSLE.Spec.Supplement.GB6RestartProofWord

/-!
# GB6's actual words: the coupling marks are the flowed marks

Packet PROVE-Q3-REL3, item (A) of `planning/handoffs/PROVE-Q3-REL2.md` §4.1 (the GB6-specific words of
`Q3Rel.IsRelConfigOff`). Supplement p. 519 ("Thus the conditional Poisson mean is exactly the evolving finite word") and
Astra's follow-up 3, Q3 §3.3.

* `gapR_eq_markPos`, `gapL_eq_markPosL` (deterministic): along an integrated `SLE(ρ)` path, before the lifetime the
  centred mark positions `V^{j,R}_T − W_T`, `V^{i,L}_T − W_T` are the positions read from the driver at time `T`
  (`Exist.StagedLaw.markPos`, `markPosL`: the infimum of the real Loewner flow over the alive rational points beyond
  the initial position) — the integrated mark equation makes the centred mark a solution of the real Loewner equation
  (`Exist.StagedLaw.IsMark`);
* **`ae_gap_eq_markPos`**: the same almost surely for every optional hull coupling;
* `flowedData`, `initJumps`, `flowedJumps`: the force data of a force word read at its flowed marks, and the jump sets
  (as finite sets, `coe_initJumps`: the frozen `forceJumpSet`);
* **`isSideWord_flowedData`**, **`isFlowedWord_flowedData`**: the two word clauses of `IsRelConfigOff` for flowed
  marks (PROVE-Q3-REL2's `isSideWord_forceBoundaryData_markPos`, `isFlowedWord_forceBoundaryData_markPos` with the
  jump sets fixed);
* `cfData`, `cfJumps`, `cfFlowedData`, `cfFlowedJumps`: the same for the counterflow word (angle `0`, from `0`) of a
  boundary word (`flowLineXL/XR`, `flowLineRhoL/RhoR`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE.Supp8.Q3Chain

open Exist.StagedLaw (markPos markPosL)

/-! ### The coupling marks are the flowed marks -/

section Marks

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **A right mark of an integrated path is the flowed mark** (before the lifetime): for a continuous driver `D` from
`0` agreeing with the path's driver on `[0, T]`, `V^{j,R}_T − W_T = markPos D T (x^{j,R})`. -/
theorem gapR_eq_markPos (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {D : ℝ → ℝ} (hD : Continuous D)
    (hD0 : D 0 = 0) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (hDw : ∀ s : ℝ≥0, s ≤ T → D s = w s) (j : Fin nR) :
    vR j T - w T = markPos D T (xR j) := by
  obtain ⟨-, -, -, h4, -, h6, -, -, h9, -, -, h12, -, -, h15, -, h17, -⟩ := hp
  have h := Exist.StagedLaw.tendsto_gap_markPos (s := fun _ => T) hD hD0 hT.le (fun s hs _ => hDw s hs) h4 (h6 j)
    (fun t ht => h9 t ht j) (fun t ht => h15 t ht j) (fun t ht => h12 t ht j) (h17 j)
    (fun hTe => absurd hTe hT.ne) (fun _ => hT) tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds h

/-- **A left mark of an integrated path is the flowed mark** (by reflection):
`V^{i,L}_T − W_T = markPosL D T (x^{i,L})`. -/
theorem gapL_eq_markPosL (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {D : ℝ → ℝ} (hD : Continuous D)
    (hD0 : D 0 = 0) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (hDw : ∀ s : ℝ≥0, s ≤ T → D s = w s) (i : Fin nL) :
    vL i T - w T = markPosL D T (xL i) := by
  obtain ⟨-, -, -, h4, h5, -, -, h8, -, -, h11, -, -, h14, -, h16, -, -⟩ := hp
  have heq : ∀ t' : ℝ≥0, (t' : ℝ≥0∞) < ζ → -vL i t' = -xL i +
      ∫ s in (0 : ℝ)..t', 2 / (-vL i s.toNNReal - -w s.toNNReal) := by
    intro t' ht'
    rw [h14 t' ht' i]
    have : (∫ s in (0 : ℝ)..t', 2 / (-vL i s.toNNReal - -w s.toNNReal)) =
        -∫ s in (0 : ℝ)..t', 2 / (vL i s.toNNReal - w s.toNNReal) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun s _ => ?_
      show 2 / (-vL i s.toNNReal - -w s.toNNReal) = -(2 / (vL i s.toNNReal - w s.toNNReal))
      rw [show -vL i s.toNNReal - -w s.toNNReal = -(vL i s.toNNReal - w s.toNNReal) by ring, div_neg]
    rw [this]
    ring
  have hint : ∀ t' : ℝ≥0, (t' : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun s : ℝ => (-w s.toNNReal - -vL i s.toNNReal)⁻¹) volume 0 t' := by
    intro t' ht'
    refine (h11 t' ht' i).neg.congr fun s _ => ?_
    change -(w s.toNNReal - vL i s.toNNReal)⁻¹ = (-w s.toNNReal - -vL i s.toNNReal)⁻¹
    rw [show -w s.toNNReal - -vL i s.toNNReal = -(w s.toNNReal - vL i s.toNNReal) by ring, inv_neg]
  have hnull : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ -w s.toNNReal = -vL i s.toNNReal} = 0 := by
    refine measure_mono_null (fun s hs => ?_) (h16 i)
    exact ⟨hs.1, hs.2.1, neg_inj.1 hs.2.2⟩
  have hmain := Exist.StagedLaw.tendsto_gap_markPos (s := fun _ => T) (w := fun s => -w s) (v := fun s => -vL i s)
    (x := -xL i) (D := fun r => -D r) hD.neg (by simp [hD0]) hT.le
    (fun s hs _ => by show -D s = -w s; rw [hDw s hs]) h4.neg (h5 i).neg
    (fun t' ht' => neg_le_neg (h8 t' ht' i)) heq hint hnull (fun hTe => absurd hTe hT.ne) (fun _ => hT)
    tendsto_const_nhds
  have h := tendsto_nhds_unique tendsto_const_nhds hmain
  unfold markPosL
  linarith

end Marks

/-- **The coupling marks are the flowed marks, almost surely.** For an optional hull coupling with driver `W` and
marks `VL`, `VR`, almost surely: for every continuous `D` from `0` and every `T` before the lifetime with `D = W` on
`[0, T]`, the centred marks at `T` are the flowed marks `markPosL D T (x^{i,L})`, `markPos D T (x^{j,R})`. -/
theorem ae_gap_eq_markPos {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∀ᵐ ω ∂P, ∀ D : ℝ → ℝ, Continuous D → D 0 = 0 → ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
      (∀ s : ℝ≥0, s ≤ T → D s = W s ω) →
        (∀ i, VL i T ω - W T ω = markPosL D T (xL i)) ∧ ∀ j, VR j T ω - W T ω = markPos D T (xR j) := by
  filter_upwards [hC.1.2.2.2.2] with ω hp D hD hD0 T hT hDw
  exact ⟨fun i => gapL_eq_markPosL hp hD hD0 hT hDw i, fun j => gapR_eq_markPos hp hD hD0 hT hDw j⟩

/-! ### The words of flowed marks -/

section Words

variable {nL nR : ℕ}

/-- **The force data of a force word read at its flowed marks** (time `u`, driver `D`). -/
def flowedData (k : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (D : ℝ → ℝ)
    (u : ℝ) : ℝ → ℝ :=
  forceBoundaryData k ρL ρR (fun i => markPosL D u (xL i)) (fun j => markPos D u (xR j))

/-- The jump set of a force word as a finite set: `0` and the marks. -/
def initJumps (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : Finset ℝ :=
  insert 0 (Finset.univ.image xL ∪ Finset.univ.image xR)

/-- The jump set of the flowed marks. -/
def flowedJumps (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (D : ℝ → ℝ) (u : ℝ) : Finset ℝ :=
  initJumps (fun i => markPosL D u (xL i)) (fun j => markPos D u (xR j))

theorem coe_initJumps (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : (initJumps xL xR : Set ℝ) = forceJumpSet xL xR := by
  ext x
  simp [initJumps, forceJumpSet]

theorem zero_mem_initJumps (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : (0 : ℝ) ∈ initJumps xL xR :=
  Finset.mem_insert_self _ _

theorem left_mem_initJumps (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (i : Fin nL) : xL i ∈ initJumps xL xR :=
  Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))

theorem right_mem_initJumps (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (j : Fin nR) : xR j ∈ initJumps xL xR :=
  Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))

variable {D : ℝ → ℝ} {η : ℝ → ℂ} {u : ℝ}

/-- **The side word of flowed marks** (`IsRelConfigOff`'s clauses `sideE`, `sideu`). -/
theorem isSideWord_flowedData (hη : IsLoewnerTrace D η) (hD : Continuous D) (hD0 : D 0 = 0) (hu : 0 ≤ u) (k : ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0)
    (hxR : ∀ j, 0 ≤ xR j) :
    BHMean.IsSideWord (flowedData k ρL ρR xL xR D u) (flowedJumps xL xR D u) (fwdMapInv D u) (fwdHull D u)
      (Real.pi / Real.sqrt k) :=
  Q3Kernel.isSideWord_forceBoundaryData_markPos hη hD hD0 hu k ρL ρR hxL hxR
    (fun i => left_mem_initJumps _ _ i) (fun j => right_mem_initJumps _ _ j)

/-- **The flowed word of flowed marks** (`IsRelConfigOff`'s clause `flow`), from the initial force data. -/
theorem isFlowedWord_flowedData (hη : IsLoewnerTrace D η) (hD : Continuous D) (hD0 : D 0 = 0) (hu : 0 < u) (k : ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0)
    (hxR : ∀ j, 0 ≤ xR j) :
    BHMean.IsFlowedWord (flowedData k ρL ρR xL xR D u) (forceBoundaryData k ρL ρR xL xR) (flowedJumps xL xR D u)
      (initJumps xL xR) (fwdMapInv D u) (fwdHull D u) :=
  Q3Kernel.isFlowedWord_forceBoundaryData_markPos hη hD hD0 hu k ρL ρR hxL hxR (zero_mem_initJumps _ _)
    (fun i => left_mem_initJumps _ _ i) (fun j => right_mem_initJumps _ _ j) (fun i => left_mem_initJumps _ _ i)

end Words

/-! ### The counterflow word of a boundary word (angle `0`, from `0`) -/

section CfWord

/-- The counterflow force data of boundary data `(b, J)` at parameter `k` (angle `0`, seed `0`). -/
def cfData (k : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) : ℝ → ℝ :=
  forceBoundaryData k (flowLineRhoL k b J 0 0) (flowLineRhoR k b J 0 0) (flowLineXL b J 0) (flowLineXR b J 0)

/-- Its jump set. -/
def cfJumps (b : ℝ → ℝ) (J : Finset ℝ) : Finset ℝ := initJumps (flowLineXL b J 0) (flowLineXR b J 0)

/-- The counterflow force data at the marks flowed by `D` to time `u`. -/
def cfFlowedData (k : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (D : ℝ → ℝ) (u : ℝ) : ℝ → ℝ :=
  flowedData k (flowLineRhoL k b J 0 0) (flowLineRhoR k b J 0 0) (flowLineXL b J 0) (flowLineXR b J 0) D u

/-- Its jump set. -/
def cfFlowedJumps (b : ℝ → ℝ) (J : Finset ℝ) (D : ℝ → ℝ) (u : ℝ) : Finset ℝ :=
  flowedJumps (flowLineXL b J 0) (flowLineXR b J 0) D u

variable {b : ℝ → ℝ} {J : Finset ℝ} {D : ℝ → ℝ} {η : ℝ → ℂ} {u : ℝ}

theorem coe_cfJumps : (cfJumps b J : Set ℝ) = forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0) :=
  coe_initJumps _ _

theorem isSideWord_cfFlowedData (hη : IsLoewnerTrace D η) (hD : Continuous D) (hD0 : D 0 = 0) (hu : 0 ≤ u)
    (k : ℝ) :
    BHMean.IsSideWord (cfFlowedData k b J D u) (cfFlowedJumps b J D u) (fwdMapInv D u) (fwdHull D u)
      (Real.pi / Real.sqrt k) :=
  isSideWord_flowedData hη hD hD0 hu k _ _ (Theorem14.GW3Word.flowLineXL_nonpos b J)
    (Theorem14.GW3Word.flowLineXR_nonneg b J)

theorem isFlowedWord_cfFlowedData (hη : IsLoewnerTrace D η) (hD : Continuous D) (hD0 : D 0 = 0) (hu : 0 < u)
    (k : ℝ) :
    BHMean.IsFlowedWord (cfFlowedData k b J D u) (cfData k b J) (cfFlowedJumps b J D u) (cfJumps b J)
      (fwdMapInv D u) (fwdHull D u) :=
  isFlowedWord_flowedData hη hD hD0 hu k _ _ (Theorem14.GW3Word.flowLineXL_nonpos b J)
    (Theorem14.GW3Word.flowLineXR_nonneg b J)

/-- **The coupling's force data at time `T` is the flowed counterflow data** (on the almost sure event of
`ae_gap_eq_markPos`). -/
theorem forceBoundaryData_gap_eq_cfFlowedData {k : ℝ} {VL : Fin (flowLineNL b J 0) → ℝ}
    {VR : Fin (flowLineNR b J 0) → ℝ}
    {w : ℝ} (hL : ∀ i, VL i - w = markPosL D u (flowLineXL b J 0 i))
    (hR : ∀ j, VR j - w = markPos D u (flowLineXR b J 0 j)) :
    forceBoundaryData k (flowLineRhoL k b J 0 0) (flowLineRhoR k b J 0 0) (fun i => VL i - w) (fun j => VR j - w) =
      cfFlowedData k b J D u := by
  simp only [cfFlowedData, flowedData, hL, hR]

/-- The coupling's jump set at time `T` is the flowed one. -/
theorem forceJumpSet_gap_eq_cfFlowedJumps {VL : Fin (flowLineNL b J 0) → ℝ} {VR : Fin (flowLineNR b J 0) → ℝ}
    {w : ℝ} (hL : ∀ i, VL i - w = markPosL D u (flowLineXL b J 0 i))
    (hR : ∀ j, VR j - w = markPos D u (flowLineXR b J 0 j)) :
    forceJumpSet (fun i => VL i - w) (fun j => VR j - w) = (cfFlowedJumps b J D u : Set ℝ) := by
  simp only [cfFlowedJumps, flowedJumps, coe_initJumps, hL, hR]

end CfWord

end InteractingSLE.Supp8.Q3Chain
