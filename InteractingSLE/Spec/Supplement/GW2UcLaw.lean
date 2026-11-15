/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UcTip
import InteractingSLE.Spec.Supplement.GW2UcCont
import InteractingSLE.Spec.Supplement.GW2UaStop
import InteractingSLE.Spec.Supplement.GW2PrSw
import InteractingSLE.Spec.Supplement.GW2PtLaw
import InteractingSLE.Spec.Supplement.GW2NcEnd

/-!
# The stopped stage law on guarded histories before the contact, proved on the stop family

Packet PROVE-GW2-RELDET (round 39, decision D84 with the refinement (A′) of RELDET's handoff). The guarded stopped
stage law reads the stage law of the current stage only; a first contact during the history (in particular during the
root piece, which no stage instance covers) is not reachable by it. On alive histories the history time is before
every candidate's contact (ROOTX's `GW2Ru.ae_nil_lt_contactX` / `ae_cons_lt_contactX`; BUF's `GW2Bx.ae_bundleS`
outputs it), so the consumers lose nothing by the premise:

* **`StageLawXSGTStatement h13 ver`**: `StageLawXSGStatement h13 ver` with the almost-sure premise
  `historyTime c r l < contactX …` on the sample;
* **`stageLawXSGTStatement_stop`**: it holds on NOTHR's stop family, from NEARIMG2's `TipUnbStatement` (D84) alone:
  * stop before the contact: `isCanonXS_of_stop_first` (the versions are at most the clock of the stop,
    `GW2Nx.ae_schedVerXStop_le_physClockX`; positive life, `GW2Nz.ae_candLife_pos_succ`);
  * a first contact at or before the stop, away from the tip: `isCanonXS_of_contact` (NEARIMG2's
    `canonContactStatement`);
  * a first contact at the tip: excluded almost surely (`ae_noTip_stage`; Theorem 1.3 in `Type`,
    STAGEMEAN's `flowSwallowStatement_of_thm13` and `stageFieldLawXStatement`, the canonical driver codes).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart Supp8.GB6 GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rv
  GW2Sde GW2Sdh

/-- **The guarded stopped stage law before the contact** (D84 with the premise `T < contact`, RELDET's (A′)). -/
def StageLawXSGTStatement (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l → Wire.T14Gd.Guard c r l →
    ∀ᵐ ξ ∂c.P, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
      ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ∃ Wc : ℝ≥0 → ℝ, IsCanonXS c r l a (ver Ω c r l a).R (ver Ω c r l a).V ξ Wc

/-- The guarded law gives the guarded law before the contact. -/
theorem StageLawXSGStatement.beforeContact {h13 : Exist.Theorem13Statement.{u}} {ver : SchedVerXFamily.{u}}
    (h : StageLawXSGStatement h13 ver) : StageLawXSGTStatement h13 ver :=
  fun Ω _ _ c r l a hg hord hgd => (h Ω c r l a hg hord hgd).mono fun _ h' hGT hold _ => h' hGT hold

/-- **The guarded stopped stage law before the contact, on the stop family**, from `TipUnbStatement` (NEARIMG2, D84). -/
theorem stageLawXSGTStatement_stop (htu : TipUnbStatement.{u}) :
    StageLawXSGTStatement.{u} Wire.T14Asm7.h13 (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) := by
  intro Ω _ _ c r l a hg hord hgd
  obtain ⟨hx, hs⟩ := hg
  have hcode : ∀ κ : ℝ, 0 < κ → ∃ F : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens →
      Sec2.Assembly.PCode × ℝ≥0∞, IsCanonicalDriverCode κ 0 F := fun κ hκ =>
    Restart.canonicalDriverCodeStatement_of_param
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 Wire.T14Asm7.h12₀ Wire.T14Asm7.h13₀) Wire.T14Asm7.h13₀
      κ 0 hκ
  have hnoTip := ae_noTip_stage Wire.T14Asm7.h13₀ (GW2Pr.flowSwallowStatement_of_thm13 Wire.T14Asm7.h13₀)
    GW2Pt.stageFieldLawXStatement htu hcode (fun _ _ _ _ _ _ _ _ => 0) c r l a ⟨hx, hs⟩ hgd
  have hGTs := schedGTX_spec Wire.T14Asm7.h13 c r l a
  have A3 := ae_all_iff.2 fun n =>
    ((GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13 Ω c r l a).isA hx n).1.1.2.2.2.2.2.2
  have AV := ae_all_iff.2 fun n => GW2Nx.ae_schedVerXStop_le_physClockX Wire.T14Asm7.h13 c r l a hx hs hord hGTs.1 n
  have A7 := GW2Nz.ae_candLife_pos_succ Wire.T14Asm7.h13 c r l a hgd.1
  filter_upwards [hnoTip, A3, AV, A7, hGTs.2.2] with ξ hnt h3 hV h7 h8 hξ hold hTc
  have hgx := h8.1 hξ
  obtain ⟨-, -, -, hrect, -⟩ := hGTs.1 ξ hξ
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
    have hαs : c.α ξ c.s ≠ 0 := fun h0 => by
      have hH : c.α ξ c.s ∈ H := by
        rw [← hrect c.s le_rfl]
        exact hgx.1.2.1
      rw [h0] at hH
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH)
    by_cases htip : sphereInv (((rootPt r.1 : ℂ) + schedTr c r l a ξ
        (contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ).toNNReal : ℂ) : OnePoint ℂ) =
        ((c.α ξ c.s : ℂ) : OnePoint ℂ)
    · exact absurd htip (hnt hgx hold _ hτ hTτ (hτ ▸ hstop))
    · exact isCanonXS_of_contact GW2Ni.canonContactStatement c r l a hGTs.1 hs hx hξ hR
        (fun n u hu => (h3 n hgx).2.1 u hu) hτ htip hαs

end InteractingSLE.Theorem14.GW2Rd
