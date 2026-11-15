/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BfSlow
import InteractingSLE.Spec.Supplement.GW2RootD25Passage

/-!
# GW2's near buffer fact: from a force-coordinate crossing to the actual reach event

Packet PROVE-GW2-BUF. JOINTDET's `NearBufferFact` asks that a visit of the comparison state to the near target
(`{p | 2 + 1/8 < p.1}` for a rightward family) before the comparison stop put the actual sample in J31's (and
J32's) reach set `RootD25.reachSet` ("some live rational read is above `2`"). The reads of these samples are
ABSOLUTE (centred at the root's initial capacity), so with the affine read `read = S + W` of
`GW2BfSlow.ae_slowRead_rootFrame` the comparison driver `W` (which starts at `0`) and the read differ by the stage
start `S`.

* **`mem_reachSet_of_cross`**: a record reading `S + W` on its lifetime (`W` continuous) is in the reach set as soon
  as `2 < S + W t` at some real `t` below the lifetime;
* **`exists_read_of_mem_reachSet`**, **`exists_cross_of_mem_reachSet`**: conversely a record of the reach set has
  a live rational read above `2`, so with `read = S + W` the comparison driver exceeds `2 − S` before the lifetime;
* **`mem_reachSet_of_target`**: the target clause in the form JOINTDET needs, valid when `−1/8 ≤ S`;
* **`mem_reachSet_of_scaled_target`**: the same for a comparison dilated by `λ` with `λ (2 + 1/8 − S) ≤ 2 + 1/8`,
  valid for EVERY start `S < 2 + 1/8` (the repair for the stage starts `S ∈ (−9/4, −7/4)`; see the handoff);
* **`nearTarget_rootFrame`**, **`measurableSet_reach_rootFrame`**: the near target and the reach set in ROOT2's
  frame.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bf

open GW2JDetR11 GW2Sde GW2Sdf GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootD25 GW2TipSystem.RootV7

/-! ### Reach from a crossing -/

/-- A real time below a lifetime has a rational time above it, below the lifetime and within `ε`. -/
theorem exists_nnrat_near {t : ℝ≥0} {L : ℝ≥0∞} (ht : (t : ℝ≥0∞) < L) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ≥0, t < (q : ℝ≥0) ∧ ((q : ℝ≥0) : ℝ≥0∞) < L ∧ dist ((q : ℝ≥0) : ℝ) (t : ℝ) < ε := by
  obtain ⟨b, htb, hbL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  let e : ℝ≥0 := ⟨ε / 2, by positivity⟩
  have he : 0 < e := by
    change (0 : ℝ) < ε / 2
    positivity
  have htm : t < min b (t + e) := lt_min (ENNReal.coe_lt_coe.1 htb) (lt_add_of_pos_right t he)
  obtain ⟨q, h1, h2⟩ := Sec5.Prop59Stage.exists_nnrat_btwn₀ htm
  refine ⟨q, h1, lt_of_le_of_lt (ENNReal.coe_le_coe.2 (h2.le.trans (min_le_left _ _))) hbL, ?_⟩
  have hlt : (q : ℝ≥0) < t + e := h2.trans_le (min_le_right _ _)
  rw [Real.dist_eq, abs_of_pos (sub_pos.2 (NNReal.coe_lt_coe.2 h1))]
  have : (((q : ℝ≥0) : ℝ≥0) : ℝ) < (t : ℝ) + ε / 2 := by
    exact_mod_cast hlt
  linarith

/-- **Reach from a crossing**: a record reading `S + W` at every live rational time (`W` continuous) is in the reach
set as soon as `2 < S + W t` at a real time `t` below its lifetime. -/
theorem mem_reachSet_of_cross {z : DriverRecord} {S : ℝ} {W : ℝ≥0 → ℝ} (hW : Continuous W)
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q = S + W q)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < z.1) (hcross : 2 < S + W t) : z ∈ reachSet := by
  have hU : IsOpen {s : ℝ≥0 | 2 < S + W s} := isOpen_lt continuous_const (continuous_const.add hW)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU t hcross
  obtain ⟨q, -, hqL, hqd⟩ := exists_nnrat_near ht hε
  have hq2 : 2 < z.2 q := by
    rw [hread q hqL]
    exact hball (by rw [Metric.mem_ball, NNReal.dist_eq]; exact hqd)
  change entryCapacity z < z.1
  refine lt_of_le_of_lt (iInf_le _ q) ?_
  rw [ite_eq_left (show ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q from ⟨hqL, hq2⟩)]
  exact hqL

/-- **A record of the reach set has a live rational read above `2`.** -/
theorem exists_read_of_mem_reachSet {z : DriverRecord} (hz : z ∈ reachSet) :
    ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q := by
  by_contra h
  push Not at h
  have htop : entryCapacity z = ⊤ := by
    refine iInf_eq_top.2 fun q => ?_
    refine ite_eq_right ?_
    rintro ⟨h1, h2⟩
    exact (h q h1).not_gt h2
  have hz' : entryCapacity z < z.1 := hz
  rw [htop] at hz'
  exact not_top_lt hz'

/-- **The comparison driver must exceed `2 − S`**: for a record reading `S + W`, membership in the reach set forces
`2 − S < W q` at a live rational time `q`. -/
theorem exists_cross_of_mem_reachSet {z : DriverRecord} {S : ℝ} {W : ℝ≥0 → ℝ}
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q = S + W q) (hz : z ∈ reachSet) :
    ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 - S < W q := by
  obtain ⟨q, hq, h2⟩ := exists_read_of_mem_reachSet hz
  refine ⟨q, hq, ?_⟩
  rw [hread q hq] at h2
  linarith

/-- **The target clause** of `NearBufferFact` for a rightward comparison whose driver `W` is the read minus a start
`S ≥ −1/8`: a target visit (`2 + 1/8 < W t`) before a stop at most the lifetime gives the reach event. -/
theorem mem_reachSet_of_target {z : DriverRecord} {S : ℝ} {W : ℝ≥0 → ℝ} (hW : Continuous W)
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q = S + W q) (hS : -(1 / 8) ≤ S)
    {τ : ℝ≥0∞} (hτ : τ ≤ z.1) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) (htarget : 2 + 1 / 8 < W t) :
    z ∈ reachSet :=
  mem_reachSet_of_cross hW hread (ht.trans_le hτ) (by linarith)

/-- **The target clause for a dilated comparison**: if the comparison driver is `λ W(· / λ²)` with
`λ (2 + 1/8 − S) ≤ 2 + 1/8`, a target visit of the comparison before its stop (`λ²` times a stop at most the
lifetime) gives the reach event, for every start `S < 2 + 1/8`. -/
theorem mem_reachSet_of_scaled_target {z : DriverRecord} {S lam : ℝ} {W : ℝ≥0 → ℝ} (hW : Continuous W)
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q = S + W q) (hlam : 0 < lam)
    (hS : S < 2 + 1 / 8) (hscale : lam * (2 + 1 / 8 - S) ≤ 2 + 1 / 8)
    {τ : ℝ≥0∞} (hτ : τ ≤ z.1) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) (htarget : 2 + 1 / 8 < lam * W t) :
    z ∈ reachSet := by
  refine mem_reachSet_of_cross hW hread (ht.trans_le hτ) ?_
  have hpos : 0 < 2 + 1 / 8 - S := by linarith
  have h1 : lam * (2 + 1 / 8 - S) < lam * W t := lt_of_le_of_lt hscale htarget
  have h2 : 2 + 1 / 8 - S < W t := lt_of_mul_lt_mul_left h1 hlam.le
  linarith

/-! ### ROOT2's frame -/

/-- The first state coordinate of ROOT2's near comparison is its prescribed driver. -/
theorem nearState_fst_rootFrame (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (n m : ℕ) (t : ℝ≥0)
    (ξ : Ω) :
    (Coupling.stateAt (((comparisonFamilyO K.rootFrame.frame Ω c r).near l ω).dynamics n m).W
        (((comparisonFamilyO K.rootFrame.frame Ω c r).near l ω).dynamics n m).VL
        (((comparisonFamilyO K.rootFrame.frame Ω c r).near l ω).dynamics n m).VR t ξ).1 =
      (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 *
        ((K Ω c r).inst l ((K Ω c r).nearCandidate l ω n m)).drv c (t / (4 : ℝ≥0) ^ r.2) ξ) :=
  rootFrame_near_W K Ω c r l ω n m t ξ

/-- A rightward near family's target is the driver coordinate above `2 + 1/8`. -/
theorem mem_nearTarget_iff {κ : ℝ} (f : RootN4.NearCrossingFamily.{u} κ) (hf : f.goLeft = false)
    (p : ℝ × (Fin f.nL → ℝ) × (Fin f.nR → ℝ)) : p ∈ nearTarget f ↔ 2 + 1 / 8 < p.1 := by
  simp only [nearTarget, hf, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The reach set of J31/J32 is measurable (the first clause of `NearBufferFact`). -/
theorem measurableSet_reach_rootFrame : MeasurableSet reachSet := measurableSet_reachSet

end InteractingSLE.Theorem14.GW2Bf
