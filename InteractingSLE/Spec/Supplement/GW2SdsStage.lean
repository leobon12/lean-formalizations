/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdsFirst
import InteractingSLE.Spec.Supplement.GW1ActiveWord

/-!
# The near structure (N3), step G: junctions strictly off the tip at every alive stage start

Packet PROVE-GW2-SDE (round 18). The `hjL`, `hjR` clauses of `GW2Sdp.nearStruct_stageWord'` on the instance's past
`pastOf cf R (trueBdX …) N`: the junctions carried through the stage pieces are strictly off the tip. Only the last
piece matters (`junctionL N ≤ markPosL_{piece N} 0`, `markPos_{piece N} 0 ≤ junctionR N`, monotonicity of the
marks), and the last piece's tip is interior: its physical tip at the history time is an interior point of `ℍ` minus
the hull at the previous switch (`ae_tip_mem_diff_hist`), so in the root-`x` chart (`junctions_strict_stgRec_versionX`).

* **`junctions_succ_strict`** (deterministic); `schedTime_lt_succ`; **`ae_stageJunctions`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sds

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Wm
  GW2Schedule

/-- **The last piece decides the strictness of the stage junctions.** -/
theorem junctions_succ_strict {S : Type*} {n : ℕ} (x : GW2JDetR5.Past S (n + 1))
    (hL : markPosL (rdrv x.2) (rtime x.2) 0 < 0) (hR : 0 < markPos (rdrv x.2) (rtime x.2) 0) :
    GW2Sdp.junctionL (n + 1) x < 0 ∧ 0 < GW2Sdp.junctionR (n + 1) x := by
  have hw := continuous_rdrv x.2
  have hw0 := rdrv_zero x.2
  have hT : 0 ≤ rtime x.2 := NNReal.coe_nonneg _
  constructor
  · show markPosL (rdrv x.2) (rtime x.2) (GW2Sdp.junctionL n x.1) < 0
    exact (GW1W.markPosL_mono hw hw0 hT le_rfl (GW2Sdp.junctionL_nonpos n x.1)).trans_lt hL
  · show 0 < markPos (rdrv x.2) (rtime x.2) (GW2Sdp.junctionR n x.1)
    exact hR.trans_le (GW1W.markPos_mono hw hw0 hT le_rfl (GW2Sdp.junctionR_nonneg n x.1))

/-- Strictly time-ordered schedules with a positive first time have strictly increasing switching times. -/
theorem schedTime_lt_succ {L : List (ℝ × ℝ≥0)} (hpw : L.Pairwise (fun p q => p.2 < q.2)) {k : ℕ}
    (hk : k < L.length) (h0 : ∀ h : 0 < L.length, (0 : ℝ≥0) < (L[0]'h).2) :
    schedTime 0 L k < schedTime 0 L (k + 1) := by
  rw [Gm.schedTime_succ_eq_getElem hk]
  rcases k with _ | j
  · show (0 : ℝ≥0) < _
    exact h0 hk
  · rw [Gm.schedTime_succ_eq_getElem (by omega : j < L.length)]
    exact List.pairwise_iff_getElem.1 hpw j (j + 1) (by omega) hk (by omega)

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The stage junctions are strictly off the tip at every alive history**, almost surely, on the past of any
root-`x` version of a candidate whose stop passes the history's clock. -/
theorem ae_stageJunctions (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {R : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) < V ω →
      GW2Sdp.junctionL ((entryList l).length + 1) (pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω)
          (trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V (historyProgram c r l)
            ((entryList l).length + 1) (historyTime c r l) ω) ((entryList l).length + 1)) < 0 ∧
        0 < GW2Sdp.junctionR ((entryList l).length + 1) (pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω)
          (trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V (historyProgram c r l)
            ((entryList l).length + 1) (historyTime c r l) ω) ((entryList l).length + 1)) := by
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  filter_upwards [GW2Ru.ae_alive_goodEvent h13 c r, hGTae, GW2Ru.versionAtX_of_isRelVersionX hA,
    ae_tip_mem_diff_hist h13 c r l a] with ω hgood hGTω hVA htip halive hV
  obtain ⟨hcf, hcon⟩ := hgood l halive
  have hω := hGTω.2 hcf
  have hR := hVA hcf
  have hγ := (hGT ω hω).1.2.2
  have hmem := htip halive hγ
  set n := (entryList l).length with hn
  set Lh := historyProgram c r l with hLh
  have hLn : Lh.length = n + 1 := GW2Ru.length_historyProgram c r l
  have hpw := RootJ32.pairwise_lt_historyProgram_of_alive c r l ω halive
  have h0 : ∀ h : 0 < Lh.length, (0 : ℝ≥0) < (Lh[0]'h).2 := fun _ => by
    show (0 : ℝ≥0) < (rootEntry r.1).2
    exact c.hQpos _ r.1.2.2.2
  have hTl : historyTime c r l = schedTime 0 Lh (n + 1) := by rw [← hLn]; rfl
  have hlt : schedTime 0 Lh n < historyTime c r l :=
    hTl ▸ schedTime_lt_succ hpw (show n < Lh.length by rw [hLn]; exact Nat.lt_succ_self n) h0
  have hTc := hcon a
  have hnc : ((schedTime 0 Lh n : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω :=
    (ENNReal.coe_lt_coe.2 hlt).trans hTc
  obtain ⟨-, hmono, hclk0⟩ := clockX_props hGT hs hx hω
  -- the boundaries of the last piece are the clocks at the two switches
  set b := trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V Lh (n + 1)
    (historyTime c r l) ω with hb
  have hbN : b (n + 1) = (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω).toNNReal := by
    rw [hb]
    unfold trueBdX
    rw [ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (lt_irrefl _)]
    exact GW2Sdo.stgStartX_eq_clockX hGT hs hx hω hTc hV
  have hbn : b n = (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTime 0 Lh n) ω).toNNReal := by
    rw [hb]
    unfold trueBdX
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [ite_eq_left hn0]
      have e : schedTime 0 Lh n = 0 := by rw [hn0]; rfl
      rw [e, Real.toNNReal_of_nonpos (ENNReal.ofReal_eq_zero.1 hclk0)]
    · rw [ite_eq_right hnpos.ne', ite_eq_left (Nat.lt_succ_self n)]
      exact GW2Sdo.stgStartX_eq_clockX hGT hs hx hω hnc ((hmono hnc hTc hlt.le).trans_lt hV)
  have hT' : (schedTime 0 Lh (Lh.length - 1) : ℝ) = schedTime 0 Lh n := by
    rw [hLn, Nat.add_sub_cancel]
  rw [hT'] at hmem
  have hpiece := junctions_strict_stgRec_versionX hGT hs hx hω hR hlt hTc hV.le hmem
  have key : (pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b (n + 1)).2 =
      recOf (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω).toNNReal -
        (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTime 0 Lh n) ω).toNNReal : ℝ≥0) : ℝ≥0∞)
        (fun u => GW2Rd.stgDrv (fun t => R t ω)
          (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTime 0 Lh n) ω).toNNReal u, ⊤) := by
    change recOf ((b (n + 1) - b n : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv (fun t => R t ω) (b n) u, ⊤) = _
    rw [hbN, hbn]
  have hL : markPosL (rdrv (pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b (n + 1)).2)
      (rtime (pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b (n + 1)).2) 0 < 0 := by
    rw [key]; exact hpiece.1
  have hR' : 0 < markPos (rdrv (pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b (n + 1)).2)
      (rtime (pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b (n + 1)).2) 0 := by
    rw [key]; exact hpiece.2
  exact junctions_succ_strict _ hL hR'

end InteractingSLE.Theorem14.GW2Sds
