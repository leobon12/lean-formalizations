/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmFarX

/-!
# GW2's open lines: below a version stopped at the candidate's stop, the stage time is before the stop

Packet PROVE-GW2-STAGEMEAN, R121 round. Discharges `hcapb` and `hlife` of `meanX_inst` from the version's stop
property `hVd`: the version cap is at most the root-`x` physical clock at the candidate's stop `T + d`,
`d = min (cap, life)` (after the stop the explored driver is constant and its Loewner hull grows a vertical slit, which
is not a flow line; the stage mean cannot hold there).

* `lt_stop_of_clockX` (one sample): `clockX t < capX` and `V ≤ physClock (T + d)` give `t < d`;
* **`ae_capb_of_stop`**, **`ae_life_of_stop`**: `hcapb` and `hlife` on the live event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open Restart Exist Exist.Staged Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rd
  GW2Rz GW2Sde Supp8 Supp8.GB6 Supp8.Q3Stop

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The candidate's stop** in own time: the smaller of its cap and its life. -/
def candStop (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) : ℝ≥0 :=
  (min (candidateCap c r a : ℝ≥0∞) (candLife c r l a ω)).toNNReal

/-- **One sample: below a version stopped at the candidate's stop, the stage time is before the stop.** -/
theorem lt_stop_of_clockX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hs0 : 0 < c.s) (hx : (0 : ℝ) ≤ rootPt r.1) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) {ω : Ω} {t : ℝ≥0}
    (hVd : V ω ≤ physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT
      (historyTime c r l + candStop c r l a ω) ω)
    (hlt : (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
      (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω) :
    t < candStop c r l a ω := by
  have hstartne : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω ≠ ⊤ :=
    ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hltV : min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) <
      V ω := by
    by_contra hcon
    push Not at hcon
    have h1 : V ω - stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω ≤
        min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) -
          stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω :=
      tsub_le_tsub_right hcon _
    have h2 : (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω =
        V ω - stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω := by
      show V ω - ((stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω).toNNReal :
        ℝ≥0∞) = _
      rw [ENNReal.coe_toNNReal hstartne]
    have h3 : (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω =
        min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) -
          stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω := rfl
    have hlt' := hlt
    rw [h2, h3] at hlt'
    exact absurd (lt_of_lt_of_le hlt' h1) (lt_irrefl _)
  have hpc : physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω < V ω := by
    by_contra hcon
    push Not at hcon
    rw [min_eq_right hcon] at hltV
    exact lt_irrefl _ hltV
  by_contra hge
  push Not at hge
  have hmono := monotone_physClockX hGT hs0 hx (W' := c.W) (ζ' := c.ζ) (w := schedW c r l a) (GT := GT) ω
    (add_le_add le_rfl hge : historyTime c r l + candStop c r l a ω ≤ historyTime c r l + t)
  exact absurd (lt_of_lt_of_le hpc (hVd.trans hmono)) (lt_irrefl _)

/-- **`hcapb` of `meanX_inst` from the version's stop.** -/
theorem capb_of_stop {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} {a : ℕ}
    {ω : Ω} {t : ℝ≥0} (h : t < candStop c r l a ω) : t < candidateCap c r a := by
  have hne : min (candidateCap c r a : ℝ≥0∞) (candLife c r l a ω) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have h1 : (t : ℝ≥0∞) < min (candidateCap c r a : ℝ≥0∞) (candLife c r l a ω) := by
    rw [← ENNReal.coe_toNNReal hne]
    exact_mod_cast h
  exact_mod_cast lt_of_lt_of_le h1 (min_le_left _ _)

/-- **`hlife` of `meanX_inst` from the version's stop.** -/
theorem life_of_stop {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} {a : ℕ}
    {ω : Ω} {t : ℝ≥0} (h : t < candStop c r l a ω) : (t : ℝ≥0∞) < candLife c r l a ω := by
  have hne : min (candidateCap c r a : ℝ≥0∞) (candLife c r l a ω) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have h1 : (t : ℝ≥0∞) < min (candidateCap c r a : ℝ≥0∞) (candLife c r l a ω) := by
    rw [← ENNReal.coe_toNNReal hne]
    exact_mod_cast h
  exact lt_of_lt_of_le h1 (min_le_right _ _)

end InteractingSLE.Theorem14.GW2Psm
