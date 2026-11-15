/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdrGap
import InteractingSLE.Spec.Supplement.GW2SdrStruct
import InteractingSLE.Spec.Supplement.GW2RuShell

/-!
# The near structure (N3): the root prefix's junction span on the scaled cover

Packet PROVE-GW2-SDE (round 17). On the scaled cover with the span gap (`GW2Sdr.gapFam2`), every alive history's
instance reads a root-prefix record whose junction span is at least `6√s` at the near scale
`s = nearRootScale r.2 (nearLam l)`:

* `alive_subset_scaledCover`, `historyTime_root_le`;
* **`ae_firstSpan`**: almost surely on J32S's alive event, for any root-`x` version of any candidate whose cap passes
  the history's clock, the record of its driver up to the root prefix's clock has junction span `≥ 6√s`. The record
  is the reference prefix record (`GW2Sdq.ae_root_versions_agree`), whose span is at least `70/17` times the gap
  (`GW2Sdr.span_ge_of_spanFun`), and the scaled cover gives `3 < 2ᵏ · gap`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdr

open Restart Exist.StagedLaw GW2Rz GW2Rd GW2Sde GW2Sdq GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  Sec7.StripSideHeightProb Sec5.Prop513Schedule

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Scaled-alive histories lie in the scaled cover event.** -/
theorem alive_subset_scaledCover (gap : RootCv.GapFamily.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ l : List (EntryIdx c.Θ c.Q),
      ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l ⊆
        RootCv.scaledCoverEvent c (gap Ω c) r
  | [] => fun _ h => h
  | _ :: l => fun _ h => alive_subset_scaledCover gap c r l h.1

omit [StandardBorelSpace Ω] in
/-- The root time is before the history time of a time-ordered history. -/
theorem historyTime_root_le (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (hord : TimeOrdered 0 (historyProgram c r l)) : historyTime c (r.1, 0) [] ≤ historyTime c r l := by
  have h1 := GW2Ru.schedTime_le_historyTime c r l hord (j := 1)
    (by rw [GW2Ru.length_historyProgram]; omega)
  rw [Gm.schedTime_succ_eq_getElem (by rw [GW2Ru.length_historyProgram]; omega)] at h1
  rw [GW2Ru.historyTime_nil]
  simpa [historyProgram, schedOf] using h1

/-- The near-scale arithmetic: `6√s ≤ (70/17) g` from `3 < 2ᵏ g`, at both near dilations. -/
theorem six_sqrt_le {k : ℕ} {lam : ℝ≥0} (hlam : (17 / 35 : ℝ≥0) ≤ lam) {g : ℝ} (hg : 3 < 2 ^ k * g) :
    6 * Real.sqrt (GW2Sdh.nearRootScale k lam) ≤ 70 / 17 * g := by
  have hinv := GW2Sdh.sqrt_nearRootScale_inv k lam
  have hl : (17 / 35 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hlam
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hpos : 0 < (2 : ℝ) ^ k * lam := mul_pos h2k (by linarith)
  have hsq : Real.sqrt (GW2Sdh.nearRootScale k lam) = ((2 : ℝ) ^ k * lam)⁻¹ := by
    rw [← hinv, inv_inv]
  rw [hsq]
  have hmul : (2 : ℝ) ^ k * (17 / 35) ≤ (2 : ℝ) ^ k * lam := mul_le_mul_of_nonneg_left hl h2k.le
  rw [mul_inv_le_iff₀ hpos]
  nlinarith

/-- **The root prefix's junction span on the scaled cover** (Theorem 1.3, R48): almost surely on J32S's alive
event, for every root-`x` version of a candidate whose cap passes the history's clock, the record of its driver up to
the root prefix's clock has junction span at least `6√s`, `s = nearRootScale r.2 (nearLam l)`. -/
theorem ae_firstSpan (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {R' : ℝ≥0 → Ω → ℝ} {V' : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R' V') :
    ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S gapFam2 Ω c).experiment r).data.alive ((GW2Sdz.J32S gapFam2 Ω c).G r) l →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) < V' ω →
      6 * Real.sqrt (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) ≤
        markPos (rdrv (recOf (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) [])
          ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R' u ω, ⊤)))
          (rtime (recOf (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) [])
          ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R' u ω, ⊤))) 0 -
        markPosL (rdrv (recOf (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) [])
          ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R' u ω, ⊤)))
          (rtime (recOf (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) [])
          ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R' u ω, ⊤))) 0 := by
  have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
  set x := r.1 with hxdef
  have hspec := refVer_spec h13 c x hx
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  obtain ⟨hGT0, -, hGTae0⟩ := schedGTX_spec h13 c (x, 0) [] 0
  filter_upwards [GW2Ru.ae_alive_goodEvent_scaled h13 gapFam2 c r, GW2Ru.ae_nil_lt_contactX h13 c (x, 0),
    ae_gapFam2_eq c x ⟨hx, hs⟩, ae_refFun2_eq h13 c x hx hs,
    ae_all_iff.2 fun n => GW2Sdq.ae_root_versions_agree h13 c r l a hs hx hA n, hGTae, hGTae0]
    with ω hgoodEv hnil hgap href hagree hGTω hGTω0 halive hV'
  have halive32 := GW2Sdz.alive_scaled_subset gapFam2 Ω c r l halive
  obtain ⟨hcover, hsucc, hord⟩ := RootJ32.alive_spec c r l ω halive32
  have halive0 : ω ∈ (RootJ32.experiment c (x, 0)).data.alive ((RootJ32.construction c).G (x, 0)) [] := hcover
  have hsucc0 : oldSuccess c (x, 0) [] ω := (RootJ32.alive_spec c (x, 0) [] ω halive0).2.1
  obtain ⟨hcf, hcon⟩ := hgoodEv l halive
  have hTc0 := hnil 0 halive0
  have hTle := historyTime_root_le c r l hord
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
  -- the slot's record is the reference prefix record
  have hS := GW2Sdo.stgStartX_eq_clockX hGT0 hs hx hω0 hTc0 hn2
  have hq : recOf (((clockX (rootPt x) c.s c.W c.ζ (schedW c r l a) (historyTime c (x, 0) []) ω).toNNReal :
      ℝ≥0) : ℝ≥0∞) (fun u => R' u ω, ⊤) = refPre h13 c x hx n ω := by
    change _ = recOf ((stgStartX (rootPt x) c.s c.W c.ζ (schedW c (x, 0) [] 0) (schedGTX h13 c (x, 0) [] 0)
      ((refVer h13 c x hx).2 n) (historyTime c (x, 0) []) ω : ℝ≥0) : ℝ≥0∞) (fun u => (refVer h13 c x hx).1 n u ω, ⊤)
    rw [hS, ← hclk]
    exact GW2Wm.recOf_congr_top hag
  rw [hq]
  have hsc : RootCv.scaledCoverEvent c (gapFam2 Ω c) r ω := alive_subset_scaledCover gapFam2 c r l halive
  have hg3 : 3 < 2 ^ r.2 * gapFam2 Ω c x ω := hsc.2
  have hval : gapFam2 Ω c x ω = spanFun (refPre h13 c x hx n ω) := hgap.symm.trans hn1
  have hlam : (17 / 35 : ℝ≥0) ≤ GW2Sdh.nearLam Ω c r l ω := by
    unfold GW2Sdh.nearLam
    split_ifs
    · rw [div_le_one (by norm_num)]; norm_num
    · exact le_rfl
  have h6 := six_sqrt_le hlam hg3
  rw [hval] at h6
  exact h6.trans (span_ge_of_spanFun _)

end InteractingSLE.Theorem14.GW2Sdr
