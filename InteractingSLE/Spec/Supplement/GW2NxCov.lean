/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NxFam
import InteractingSLE.Spec.Supplement.GW2NiUncLaw
import InteractingSLE.Spec.Supplement.GW2SdtCov

/-!
# The stop-capped family's exhaustion statements

Packet PROVE-GW2-NOTHR (round 6, decision D54). For the re-wiring of the top to the stop-capped family
`GW2Nx.schedVerXStopFamily` (D49 (A)): the two exhaustion statements proved for RELDET's death family that hold
verbatim for the stop family.

* **`exhStopStatement_stop`**: NEARIMG2's `GW2Ni.ExhStopStatement` (exhaustion below the death, before the cap);
* **`hcov_stop`**: the analogue of `GW2Sdt.hcov_death` (the family covers the history's clock on J32's alive event).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Nx

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd
  Sec5.Prop513Schedule

/-- **The stop family exhausts below the death before the cap** (NEARIMG2's `ExhStopStatement`). -/
theorem exhStopStatement_stop (h13 : Exist.Theorem13Statement.{u}) :
    GW2Ni.ExhStopStatement (schedVerXStopFamily h13) := by
  intro Ω _ _ c r l a hg hord
  filter_upwards [schedVerXStop_exhausts_stop h13 c r l a hg.1 hg.2 hord, ae_schedLaunchLifeX_eq h13 c r l a hord,
    ae_schedLaunchLifeX_eq_top_of_zero h13 c r l a hord, ae_schedClockX_props h13 c r l a hg.1 hg.2]
    with ω hex hlaunch hz hclk hgx hold t ht htcap hd
  refine hex hgx t ht ?_
  obtain ⟨-, hmono, -⟩ := hclk hgx
  rw [schedStopLifeX_eq]
  refine lt_min ?_ ?_
  · rcases eq_zero_or_pos (candLife c r l a ω) with h0 | h0
    · rw [hz hold h0]
      exact ENNReal.ofReal_lt_top
    · rw [hlaunch hold h0]
      exact hd
  · unfold capLife
    split_ifs with hc
    · have h0 : 0 ≤ clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω := RootH29.forwardCapacity_nonneg _ _ _ _
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).2 (hmono ht hc htcap)
    · exact ENNReal.ofReal_lt_top

/-- **The stop family covers the history's clock** on J32's alive event (`GW2Sdt.hcov_death` for the stop family). -/
theorem hcov_stop (h13 : Exist.Theorem13Statement.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GW2Rv.GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
        cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
        (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) <
          (schedVerXStopFamily h13 Ω c r l a).V n ω := by
  intro Ω _ _ c r l a hg
  by_cases hord : TimeOrdered 0 (historyProgram c r l)
  swap
  · exact Eventually.of_forall fun ω halive =>
      absurd (RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive) hord
  filter_upwards [schedVerXStop_exhausts_stop h13 c r l a hg.1 hg.2 hord,
    GW2Sdt.ae_clock_lt_deathClockX h13 c r l a hg, ae_schedLaunchLifeX_eq h13 c r l a hord,
    ae_schedLaunchLifeX_eq_top_of_zero h13 c r l a hord, ae_schedClockX_props h13 c r l a hg.1 hg.2]
    with ω hex hdeath hlaunch hz hclk halive hcf hTc
  have hold : oldSuccess c r l ω := (RootJ32.alive_spec c r l ω halive).2.1
  refine hex hcf (historyTime c r l) hTc ?_
  obtain ⟨-, hmono, -⟩ := hclk hcf
  rw [schedStopLifeX_eq]
  refine lt_min ?_ ?_
  · rcases eq_zero_or_pos (candLife c r l a ω) with h0 | h0
    · rw [hz hold h0]
      exact ENNReal.ofReal_lt_top
    · rw [hlaunch hold h0]
      exact hdeath halive hcf hTc
  · unfold capLife
    split_ifs with hc
    · have h0 : 0 ≤ clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω :=
        RootH29.forwardCapacity_nonneg _ _ _ _
      have hlt : historyTime c r l < historyTime c r l + candidateCap c r a :=
        lt_add_of_pos_right _ (candidateCap_pos c r a)
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).2 (hmono hTc hc hlt)
    · exact ENNReal.ofReal_lt_top

end InteractingSLE.Theorem14.GW2Nx
