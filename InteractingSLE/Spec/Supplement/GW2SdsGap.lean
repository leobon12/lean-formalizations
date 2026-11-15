/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdsPhys
import InteractingSLE.Spec.Supplement.GW2SdqGap
import InteractingSLE.Spec.Supplement.GW2RuLive

/-!
# The near structure (N3), step G: the junction gap `GW2Sdq.gapFam` is positive on the cover event

Packet PROVE-GW2-SDE (round 18). The top's `hpos` for round 16's gap family (`17/35 · min (−jL, jR, 1)` of the root
stage's prefix record): on the cover event of a root `(x, 0)`, almost surely, the gap is positive. The root piece's
tip at the root time is in `ℍ` (`ae_tip_mem_diff_hist` at the empty history), so the prefix record of every version
has both junctions strictly off the tip (`junctions_strict_versionX`).

* `junctionFun_pos`; **`ae_gapFam_pos`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sds

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd

/-- The junction functional is positive at strict junctions. -/
theorem junctionFun_pos {p : RecData} (hL : markPosL (rdrv p) (rtime p) 0 < 0)
    (hR : 0 < markPos (rdrv p) (rtime p) 0) : 0 < GW2Sdq.junctionFun p := by
  unfold GW2Sdq.junctionFun
  have h : 0 < min (min (-markPosL (rdrv p) (rtime p) 0) (markPos (rdrv p) (rtime p) 0)) 1 :=
    lt_min (lt_min (by linarith) hR) one_pos
  positivity

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The gap's positivity (`hpos`) for `GW2Sdq.gapFam`.** -/
theorem ae_gapFam_pos (c : SourceData Ω) (x : RootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < GW2Sdq.gapFam Ω c x ω := by
  classical
  by_cases h : 0 ≤ rootPt x ∧ 0 < c.s
  · have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
    obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c (x, 0) [] 0
    have hspec := GW2Sdq.refVer_spec h13 c x h.1
    have hVA : ∀ᵐ ω ∂c.P, ∀ n : ℕ, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt x) c.s →
        VersionAtX (rootPt x) c.s c.W c.ζ (schedW c (x, 0) [] 0) (schedTr c (x, 0) [] 0) c.α
          ((GW2Sdq.refVer h13 c x h.1).1 n) ((GW2Sdq.refVer h13 c x h.1).2 n) ω :=
      ae_all_iff.2 fun n => GW2Ru.versionAtX_of_isRelVersionX (hspec.1 n).1.1
    filter_upwards [GW2Sdq.ae_gapFam_eq c x h, GW2Sdq.ae_refFun_eq h13 c x h.1 h.2, GW2Ru.ae_alive_goodX h13 c (x, 0),
      GW2Ru.ae_nil_lt_contactX h13 c (x, 0), hGTae, hVA, ae_tip_mem_diff_hist h13 c (x, 0) [] 0]
      with ω hgap href hgood hnil hGTω hVAω htip hcov
    have halive : ω ∈ (RootJ32.experiment c (x, 0)).data.alive ((RootJ32.construction c).G (x, 0)) [] := hcov
    have hcf := hgood [] halive
    have hTc := hnil 0 halive
    obtain ⟨n, hn1, hn2⟩ := (href hcf hTc).exists
    have hω := hGTω.2 hcf
    have hval : GW2Sdq.gapFam Ω c x ω = GW2Sdq.junctionFun (GW2Sdq.refPre h13 c x h.1 n ω) := hgap.symm.trans hn1
    rw [hval]
    have hS := GW2Sdo.stgStartX_eq_clockX hGT h.2 h.1 hω hTc hn2
    have hγ := (hGT ω hω).1.2.2
    have hH := (htip halive hγ).1
    have hj := junctions_strict_versionX hGT h.2 h.1 hω (hVAω n hcf) hTc hn2.le hH
    unfold GW2Sdq.refPre stgPreRecX
    rw [hS]
    exact junctionFun_pos hj.1 hj.2
  · refine Eventually.of_forall fun ω _ => ?_
    change 0 < GW2Sdq.gapAt c x ω
    unfold GW2Sdq.gapAt
    simp only [h, ↓reduceDIte]
    exact one_pos

end InteractingSLE.Theorem14.GW2Sds
