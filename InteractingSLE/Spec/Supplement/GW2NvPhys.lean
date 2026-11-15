/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NvExp

/-!
# The death clock on the good set (one sample)

Packet PROVE-GW2-NOTHR (round 4, D46). Physical facts about RELDET's root-`x` death clock `deathClockX` at a sample
of ROOTX's good set, used on both sides of the kernel-to-`P` step:

* **`deathClockX_lt_top_iff`**, **`mem_deathFin_iff`**: the death clock is finite iff the death is before the cap
  and before the contact, iff the sample is in the measurable event `deathFin`;
* **`stage_start_death`**: with the stage start below the cap and a finite death clock, the stage start is the
  clock at the history's end `T`. The death clock is the clock at `T + candLife`, and the start is at most the death
  (strictly before it for a positive lifetime, equal to it for a zero lifetime);
* **`exists_cap_gt`**: D27's exhaustion below the death (in RELDET's clock form) puts every value below the death
  clock below some cap (intermediate values of the clock).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Nv

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Rv
  GW2Sde GW2Sdh Supp8

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

open Classical in
/-- **The death clock is finite iff the death is before the cap and before the contact.** -/
theorem deathClockX_lt_top_iff (ω : Ω) :
    deathClockX c r l a ω < ⊤ ↔ candLife c r l a ω ≤ candidateCap c r a ∧
      ((historyTime c r l + (candLife c r l a ω).toNNReal : ℝ≥0) : ℝ≥0∞) <
        contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω := by
  unfold deathClockX
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => ENNReal.ofReal_lt_top⟩
  · exact ⟨fun h' => absurd h' (lt_irrefl _), fun h' => absurd h' h⟩

open Classical in
/-- The value of a finite death clock. -/
theorem deathClockX_eq_of_lt_top {ω : Ω} (hd : deathClockX c r l a ω < ⊤) :
    deathClockX c r l a ω = ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
      (historyTime c r l + (candLife c r l a ω).toNNReal) ω) := by
  have h := (deathClockX_lt_top_iff c r l a ω).1 hd
  unfold deathClockX
  simp only [h, and_self, ite_true]

variable {GT : Set Ω}
  (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
  (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1)

include hGT in
/-- **On the good set, the measurable event `deathFin` is the finite death clock.** -/
theorem mem_deathFin_iff (I : StageInst Ω) (hIW : I.W = schedW c r l a) (hIT : I.T = historyTime c r l)
    (hIGT : I.GT = GT) {ω : Ω} (hω : ω ∈ GT) :
    ω ∈ deathFin c r l a I (rootPt r.1) ↔ deathClockX c r l a ω < ⊤ := by
  rw [deathClockX_lt_top_iff]
  unfold deathFin
  rw [hIW, hIT, hIGT]
  simp only [mem_inter_iff, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨hcap, q, hlt, hloc⟩
    obtain ⟨-, hqc⟩ := (mem_locEvX_iff hGT hω).1 hloc
    exact ⟨hcap, hlt.trans hqc⟩
  · rintro ⟨hcap, hc⟩
    obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hc
    refine ⟨hcap, q, hq1, (mem_locEvX_iff hGT hω).2 ⟨?_, hq2⟩⟩
    exact ENNReal.coe_lt_coe.1 (bot_le.trans_lt hq1)

include hGT hs hx in
/-- The clock facts at a good sample: `0` at `0`, strictly increasing and continuous before the contact. -/
theorem clockX_props_at {ω : Ω} (hω : ω ∈ GT) :
    clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) 0 ω = 0 ∧
      StrictMonoOn (fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω)
        {t | (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω} ∧
      ContinuousOn (fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω)
        {t | (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω} := by
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ω hω
  exact clock_props c.W c.ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ

include hGT hs hx in
/-- **The stage start and the death on the clock.** With the stage start below the cap and a finite death clock:
the start is the clock at `T`, the death clock is the clock at `T + candLife`, and the start is at most the death
clock (strictly below it for a positive lifetime, equal to it for a zero lifetime). -/
theorem stage_start_death {V : Ω → ℝ≥0∞} {ω : Ω} (hω : ω ∈ GT) (hVfin : V ω ≠ ⊤)
    (hSV : ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω : ℝ≥0) : ℝ≥0∞) < V ω)
    (hd : deathClockX c r l a ω < ⊤) :
    ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω : ℝ≥0) : ℝ) =
        clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω ∧
      0 ≤ clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω ∧
      clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω ≤
        clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l + (candLife c r l a ω).toNNReal) ω ∧
      (0 < candLife c r l a ω → clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω <
        clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l + (candLife c r l a ω).toNNReal) ω) ∧
      (candLife c r l a ω = 0 → clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω =
        clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l + (candLife c r l a ω).toNNReal) ω) := by
  set T := historyTime c r l with hTdef
  set cl := (candLife c r l a ω).toNNReal with hcldef
  obtain ⟨hcap, hc⟩ := (deathClockX_lt_top_iff c r l a ω).1 hd
  obtain ⟨h0, hmono, -⟩ := clockX_props_at c r l a hGT hs hx hω
  have hTc : (T : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω :=
    (ENNReal.coe_le_coe.2 (le_self_add : T ≤ T + cl)).trans_lt hc
  have hTV : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ω) < V ω := by
    have h1 : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V T ω < V ω := by
      have hne : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V T ω ≠ ⊤ :=
        ne_top_of_le_ne_top hVfin (by unfold stgStartMX; exact min_le_right _ _)
      have := hSV
      unfold stgStartX at this
      rwa [ENNReal.coe_toNNReal hne] at this
    unfold stgStartMX at h1
    rw [physClockX_eq_clockX hGT hs hx hω hTc] at h1
    exact (min_lt_iff.1 h1).resolve_right (lt_irrefl _)
  have hS := GW2Sdo.stgStartX_eq_clockX hGT hs hx hω hTc hTV
  have h0le : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      0 ≤ clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω := fun t ht => by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h]; exact h0.ge
    · have := hmono (show ((0 : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω from
        (ENNReal.coe_le_coe.2 zero_le).trans_lt ht) ht h
      change clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) 0 ω < _ at this
      linarith
  have hT0 := h0le T hTc
  refine ⟨by rw [hS, Real.coe_toNNReal _ hT0], hT0, ?_, fun hpos => ?_, fun hz => ?_⟩
  · rcases eq_or_lt_of_le (le_self_add : T ≤ T + cl) with h | h
    · rw [← h]
    · exact (hmono hTc hc h).le
  · have hcl : 0 < cl := by
      rw [hcldef]
      exact ENNReal.toNNReal_pos hpos.ne' (ne_top_of_le_ne_top ENNReal.coe_ne_top hcap)
    exact hmono hTc hc (lt_add_of_pos_right T hcl)
  · rw [hcldef, hz, ENNReal.toNNReal_zero, add_zero]

include hGT hs hx in
/-- **D27's exhaustion puts every value below a finite death clock below some cap.** -/
theorem exists_cap_gt {Vf : ℕ → Ω → ℝ≥0∞} {ω : Ω} (hω : ω ∈ GT) (hd : deathClockX c r l a ω < ⊤)
    (hD27 : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < Vf n ω)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < deathClockX c r l a ω) : ∃ n, (q : ℝ≥0∞) < Vf n ω := by
  set T := historyTime c r l with hTdef
  set cl := (candLife c r l a ω).toNNReal with hcldef
  obtain ⟨-, hc⟩ := (deathClockX_lt_top_iff c r l a ω).1 hd
  obtain ⟨h0, -, hcont⟩ := clockX_props_at c r l a hGT hs hx hω
  have hdeq := deathClockX_eq_of_lt_top c r l a hd
  have hqlt : (q : ℝ) < clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (T + cl) ω := by
    rw [hdeq, ← ENNReal.ofReal_coe_nnreal] at hq
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg q.coe_nonneg).1 hq
  have hsub : Icc (0 : ℝ≥0) (T + cl) ⊆
      {t | (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω} := fun t ht =>
    (ENNReal.coe_le_coe.2 ht.2).trans_lt hc
  obtain ⟨t, ht, htq⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ T + cl) (hcont.mono hsub)
    ⟨by rw [h0]; exact q.coe_nonneg, hqlt.le⟩
  have htc := hsub ht
  have htq' : clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω = q := htq
  have hqd : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω := by
    rw [htq', ENNReal.ofReal_coe_nnreal]; exact hq
  obtain ⟨n, hn⟩ := (hD27 t htc hqd).exists
  refine ⟨n, ?_⟩
  rwa [htq', ENNReal.ofReal_coe_nnreal] at hn

end InteractingSLE.Theorem14.GW2Nv
