/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NqNoTip
import InteractingSLE.Spec.Supplement.GW2NqCont
import InteractingSLE.Spec.Supplement.GW2UcLaw

/-!
# The guarded stopped stage law before the contact, on the stop family, with no inputs (D84/D87)

Packet PROVE-GW2-NEARIMG2, decisions D84 item (1) and D87. RELDET proved `GW2Rd.StageLawXSGTStatement` on NOTHR's stop
family from `TipUnbStatement` alone (`GW2Rd.stageLawXSGTStatement_stop`, `GW2UcLaw`). `TipUnbStatement` is false
(`GW2NqTip`). This file proves the same law **with no inputs**, by RELDET's argument with the case split corrected:

* stop before the contact: RELDET's `isCanonXS_of_stop_first`, unchanged;
* a first contact at or before the stop: the relative trace has a finite limit there almost surely
  (`ae_tendsto_stage`), so the canonical driver of `canonContactLimStatement` gives the law (`isCanonXS_of_tendsto`).
  This covers RELDET's two contact cases (away from the tip; at the tip, excluded) together.

* **`stageLawXSGTStatement_closed`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist Staged StagedLaw Restart Supp8.GB6 GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rv
  GW2Sde GW2Sdh GW2Rd

/-- **The guarded stopped stage law before the contact, on the stop family**, with no inputs (RELDET's
`stageLawXSGTStatement_stop` without `TipUnbStatement`, D84/D87). -/
theorem stageLawXSGTStatement_closed :
    GW2Rd.StageLawXSGTStatement.{u} Wire.T14Asm7.h13 (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) := by
  intro Ω _ _ c r l a hg hord hgd
  obtain ⟨hx, hs⟩ := hg
  have hcode : ∀ κ : ℝ, 0 < κ → ∃ F : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens →
      Sec2.Assembly.PCode × ℝ≥0∞, IsCanonicalDriverCode κ 0 F := fun κ hκ =>
    Restart.canonicalDriverCodeStatement_of_param
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀) Wire.T14Asm7.h13₀
      κ 0 hκ
  have hnoTip := ae_tendsto_stage Wire.T14Asm7.h13₀ (GW2Pr.flowSwallowStatement_of_thm13 Wire.T14Asm7.h13₀)
    GW2Pt.stageFieldLawXStatement hcode (fun _ _ _ _ _ _ _ _ => 0) c r l a ⟨hx, hs⟩ hgd
  have hGTs := schedGTX_spec Wire.T14Asm7.h13 c r l a
  have A3 := ae_all_iff.2 fun n =>
    ((GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).isA hx n).1.1.2.2.2.2.2.2
  have AV := ae_all_iff.2 fun n => GW2Nx.ae_schedVerXStop_le_physClockX Wire.T14Asm7.h13 c r l a hx hs hord hGTs.1 n
  have A7 := GW2Nz.ae_candLife_pos_succ Wire.T14Asm7.h13 c r l a hgd.1
  filter_upwards [hnoTip, A3, AV, A7, hGTs.2.2] with ξ hnt h3 hV h7 h8 hξ hold hTc
  have hgx := h8.1 hξ
  have hR : ∀ n, VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α
      ((GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).R n)
      ((GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).V n) ξ := fun n =>
    ⟨((GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).isA hx n).1.1.2.1 ξ,
      ((GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).isA hx n).1.1.2.2.1 ξ, (h3 n hgx).2.2⟩
  have hlife := h7 hold
  by_cases hstop : ((historyTime c r l + GW2Psm.candStop c r l a ξ : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ
  · -- the stop comes first
    have hcs : 0 < GW2Psm.candStop c r l a ξ := by
      unfold GW2Psm.candStop
      have hmin : 0 < min (candidateCap c r a : ℝ≥0∞) (candLife c r l a ξ) :=
        lt_min (ENNReal.coe_pos.2 (candidateCap_pos c r a)) hlife
      exact ENNReal.toNNReal_pos hmin.ne' (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
    exact isCanonXS_of_stop_first c r l a hGTs.1 hs hx hξ hR (fun n => hV n hξ hgx hold hlife)
      (add_pos_of_nonneg_of_pos zero_le hcs) hstop
  · -- the contact comes first
    rw [not_lt] at hstop
    have hfin : contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top hstop
    have hτ : contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ =
        ((contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ).toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
    have hTτ : historyTime c r l < (contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ).toNNReal := by
      rw [hτ] at hTc
      exact_mod_cast hTc
    exact isCanonXS_of_tendsto canonContactLimStatement c r l a hGTs.1 hs hx hξ hR
      (fun n u hu => (h3 n hgx).2.1 u hu) hτ (hnt hgx hold _ hτ hTτ (hτ ▸ hstop))

end InteractingSLE.Theorem14.GW2Ni
