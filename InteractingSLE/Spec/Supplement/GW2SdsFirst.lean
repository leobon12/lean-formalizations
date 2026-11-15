/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdsGap
import InteractingSLE.Spec.Supplement.GW2SdrSpan

/-!
# The near structure (N3), step G: both first-piece junctions beyond `3√s` on the junction-gap cover

Packet PROVE-GW2-SDE (round 18). On J32's alive event over the scaled cover with round 16's junction gap
`GW2Sdq.gapFam` (`17/35 · min (−jL, jR, 1)` of the root prefix), `3 < 2ᵏ · gap` puts both junctions of the root
prefix at least `3√s` from the tip, `s = nearRootScale r.2 (nearLam l)` (both near dilations `1`, `17/35`). This is
the `hfirst` clause of `GW2Sdp.nearStruct_stageWord'` (both orientations).

* `junction_ge_of_junctionFun`; **`ae_firstJunctions`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sds

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd

/-- Both junctions are at least `35/17` times the junction functional. -/
theorem junction_ge_of_junctionFun (p : RecData) :
    35 / 17 * GW2Sdq.junctionFun p ≤ -markPosL (rdrv p) (rtime p) 0 ∧
      35 / 17 * GW2Sdq.junctionFun p ≤ markPos (rdrv p) (rtime p) 0 := by
  unfold GW2Sdq.junctionFun
  have h1 := min_le_left (min (-markPosL (rdrv p) (rtime p) 0) (markPos (rdrv p) (rtime p) 0)) 1
  have h2 := min_le_left (-markPosL (rdrv p) (rtime p) 0) (markPos (rdrv p) (rtime p) 0)
  have h3 := min_le_right (-markPosL (rdrv p) (rtime p) 0) (markPos (rdrv p) (rtime p) 0)
  constructor <;> nlinarith

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Both root-prefix junctions beyond `3√s` on the junction-gap cover**: almost surely on J32S's alive event (gap
`GW2Sdq.gapFam`), for every root-`x` version of a candidate whose cap passes the history's clock, the record of its
driver up to the root prefix's clock has `3√s ≤ −jL` and `3√s ≤ jR`, `s = nearRootScale r.2 (nearLam l)`. -/
theorem ae_firstJunctions (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {R' : ℝ≥0 → Ω → ℝ} {V' : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R' V') :
    ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
        ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) < V' ω →
      3 * Real.sqrt (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) ≤
          -markPosL (rdrv (recOf (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) [])
            ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R' u ω, ⊤)))
            (rtime (recOf (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) [])
            ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R' u ω, ⊤))) 0 ∧
        3 * Real.sqrt (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) ≤
          markPos (rdrv (recOf (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) [])
            ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R' u ω, ⊤)))
            (rtime (recOf (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) [])
            ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R' u ω, ⊤))) 0 := by
  have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
  set x := r.1 with hxdef
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  obtain ⟨hGT0, -, hGTae0⟩ := schedGTX_spec h13 c (x, 0) [] 0
  filter_upwards [GW2Ru.ae_alive_goodEvent_scaled h13 GW2Sdq.gapFam c r, GW2Ru.ae_nil_lt_contactX h13 c (x, 0),
    GW2Sdq.ae_gapFam_eq c x ⟨hx, hs⟩, GW2Sdq.ae_refFun_eq h13 c x hx hs,
    ae_all_iff.2 fun n => GW2Sdq.ae_root_versions_agree h13 c r l a hs hx hA n, hGTae, hGTae0]
    with ω hgoodEv hnil hgap href hagree hGTω hGTω0 halive hV'
  have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
  obtain ⟨hcover, hsucc, hord⟩ := RootJ32.alive_spec c r l ω halive32
  have halive0 : ω ∈ (RootJ32.experiment c (x, 0)).data.alive ((RootJ32.construction c).G (x, 0)) [] := hcover
  have hsucc0 : oldSuccess c (x, 0) [] ω := (RootJ32.alive_spec c (x, 0) [] ω halive0).2.1
  obtain ⟨hcf, hcon⟩ := hgoodEv l halive
  have hTc0 := hnil 0 halive0
  have hTle := GW2Sdr.historyTime_root_le c r l hord
  have hTc : ((historyTime c (x, 0) [] : ℝ≥0) : ℝ≥0∞) < contactX (rootPt x) c.s (schedTr c r l a) c.α ω :=
    (ENNReal.coe_le_coe.2 hTle).trans_lt (hcon a)
  have hω := hGTω.2 hcf
  have hω0 := hGTω0.2 hcf
  have hmono := (clockX_props hGT hs hx hω).2.1
  have hV'0 : ENNReal.ofReal (clockX (rootPt x) c.s c.W c.ζ (schedW c r l a) (historyTime c (x, 0) []) ω) <
      V' ω := (hmono hTc (hcon a) hTle).trans_lt hV'
  obtain ⟨n, hn1, hn2⟩ := (href hcf hTc0).exists
  have hWW : ∀ t ≤ historyTime c (x, 0) [], schedW c r l a t ω = schedW c (x, 0) [] 0 t ω := fun t ht =>
    GW2Sdq.schedW_eq_root c r l a hsucc hsucc0 (ht.trans (GW2Sdq.historyTime_root c r).le)
  have hclk : clockX (rootPt x) c.s c.W c.ζ (schedW c r l a) (historyTime c (x, 0) []) ω =
      clockX (rootPt x) c.s c.W c.ζ (schedW c (x, 0) [] 0) (historyTime c (x, 0) []) ω :=
    GW2Sdo.clockX_congr hWW
  have hag := hagree n hcf hsucc hsucc0 hTc hTc0 hV'0 hn2
  have hS := GW2Sdo.stgStartX_eq_clockX hGT0 hs hx hω0 hTc0 hn2
  have hq : recOf (((clockX (rootPt x) c.s c.W c.ζ (schedW c r l a) (historyTime c (x, 0) []) ω).toNNReal :
      ℝ≥0) : ℝ≥0∞) (fun u => R' u ω, ⊤) = GW2Sdq.refPre h13 c x hx n ω := by
    change _ = recOf ((stgStartX (rootPt x) c.s c.W c.ζ (schedW c (x, 0) [] 0) (schedGTX h13 c (x, 0) [] 0)
      ((GW2Sdq.refVer h13 c x hx).2 n) (historyTime c (x, 0) []) ω : ℝ≥0) : ℝ≥0∞)
      (fun u => (GW2Sdq.refVer h13 c x hx).1 n u ω, ⊤)
    rw [hS, ← hclk]
    exact GW2Wm.recOf_congr_top hag
  rw [hq]
  have hsc : RootCv.scaledCoverEvent c (GW2Sdq.gapFam Ω c) r ω :=
    GW2Sdr.alive_subset_scaledCover GW2Sdq.gapFam c r l halive
  have hg3 : 3 < 2 ^ r.2 * GW2Sdq.gapFam Ω c x ω := hsc.2
  have hval : GW2Sdq.gapFam Ω c x ω = GW2Sdq.junctionFun (GW2Sdq.refPre h13 c x hx n ω) := hgap.symm.trans hn1
  have hlam : (17 / 35 : ℝ≥0) ≤ GW2Sdh.nearLam Ω c r l ω := by
    unfold GW2Sdh.nearLam
    split_ifs
    · rw [div_le_one (by norm_num)]; norm_num
    · exact le_rfl
  have h6 := GW2Sdr.six_sqrt_le hlam hg3
  rw [hval] at h6
  obtain ⟨hjL, hjR⟩ := junction_ge_of_junctionFun (GW2Sdq.refPre h13 c x hx n ω)
  constructor <;> linarith

end InteractingSLE.Theorem14.GW2Sds
