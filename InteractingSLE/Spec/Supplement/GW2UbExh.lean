/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UbAsm
import InteractingSLE.Spec.Supplement.GW2NxFam

/-!
# At a contact before the candidate's stop, the stop family exhausts the relative clock

Packet PROVE-GW2-RELDET (round 38, decisions D73 route (ii) and D81). The tip exclusion reads the stage code through
all versions of the stop family; at a first contact at or before the candidate's stop `T + candStop` the versions'
caps must exhaust every clock value before the contact. The stop family's caps are strictly below the stop gauge's life
`GW2Nx.schedStopLifeX` and exhaust the clock below it (`GW2Nx.schedVerXStop_exhausts_stop`); here that life is `⊤`:

* the cap part `capLife` is `⊤`, since `T + cap ≥ T + candStop ≥` the contact;
* the launch part is `⊤` at a zero lifetime (`GW2Rd.ae_schedLaunchLifeX_eq_top_of_zero`) and the death clock
  otherwise (`GW2Rd.ae_schedLaunchLifeX_eq`), which is `⊤` since the candidate does not die before the contact.

* **`ae_schedStopLifeX_eq_top`**, **`ae_exhausts_of_contact`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz
  Sec5.Prop513Schedule

section Sched

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- **At a contact at or before the candidate's stop, the stop gauge's life is `⊤`** (history's success). -/
theorem ae_schedStopLifeX_eq_top (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω →
      contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω ≤
        ((historyTime c r l + GW2Psm.candStop c r l a ω : ℝ≥0) : ℝ≥0∞) →
      GW2Nx.schedStopLifeX c r l a ω = ⊤ := by
  filter_upwards [ae_schedLaunchLifeX_eq h13 c r l a hord, ae_schedLaunchLifeX_eq_top_of_zero h13 c r l a hord]
    with ω hlaunch hzero hold hcon
  have hstop_le_cap : GW2Psm.candStop c r l a ω ≤ candidateCap c r a := by
    unfold GW2Psm.candStop
    exact (ENNReal.toNNReal_mono ENNReal.coe_ne_top (min_le_left _ _)).trans_eq (ENNReal.toNNReal_coe _)
  rw [GW2Nx.schedStopLifeX_eq]
  refine min_eq_top.2 ⟨?_, ?_⟩
  · rcases eq_zero_or_pos (candLife c r l a ω) with h0 | h0
    · exact hzero hold h0
    · rw [hlaunch hold h0, deathClockX]
      refine ite_eq_right_of_eq_false _ _ (eq_false fun hd => ?_)
      have hne : candLife c r l a ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hd.1
      have hcs : GW2Psm.candStop c r l a ω = (candLife c r l a ω).toNNReal := by
        unfold GW2Psm.candStop
        rw [min_eq_right hd.1]
      rw [hcs] at hcon
      exact absurd (hcon.trans_lt hd.2) (lt_irrefl _)
  · unfold GW2Nx.capLife
    refine ite_eq_right_of_eq_false _ _ (eq_false fun hlt => ?_)
    have : ((historyTime c r l + GW2Psm.candStop c r l a ω : ℝ≥0) : ℝ≥0∞) ≤
        ((historyTime c r l + candidateCap c r a : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.coe_le_coe.2 (add_le_add_right hstop_le_cap _)
    exact absurd (hcon.trans this) (not_le.2 hlt)

include h13 in
/-- **At a contact at or before the candidate's stop, the stop family exhausts every clock value before the contact**
(good record, history's success). -/
theorem ae_exhausts_of_contact (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
      contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω ≤
        ((historyTime c r l + GW2Psm.candStop c r l a ω : ℝ≥0) : ℝ≥0∞) →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
          (GW2Nx.schedVerXStop h13 c r l a).V n ω := by
  filter_upwards [GW2Nx.schedVerXStop_exhausts_stop h13 c r l a hx hs hord, ae_schedStopLifeX_eq_top h13 c r l a hord]
    with ω hexh htop hgood hold hcon t ht
  exact hexh hgood t ht (by rw [htop hold hcon]; exact ENNReal.ofReal_lt_top)

end Sched

end InteractingSLE.Theorem14.GW2Rd
