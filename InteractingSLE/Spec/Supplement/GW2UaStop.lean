/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UaStmt

/-!
# The stopped stage law where the candidate stops before the contact (pathwise)

Packet PROVE-GW2-RELDET (round 37, decision D71 (A)). At one sample of ROOTX's good set, if the candidate's stop
`v = T + candStop` comes before the root-`x` contact, the canonical stopped driver is the re-centred relative chain at
the horizon `v` (ROOTX's `GW2Rz.exists_recentred_chain`):

* its generating trace is the capacity tip up to the clock at `v` (`GW2Bf.isGeneratingTrace_capacityTip_of_hull`);
* the stopped relative life is the clock at `v` (the clock is monotone before the contact);
* the clock is bounded by its value at `v` before the stop;
* every version capped at most the physical clock of `v` (the stop family, D68) is the horizon-`v` reader below its
  cap (`GW2Rz.version_eq_reader`), which is the chain's driver (`GW2Bf.capacityDriverRead_eq_of_hull`).

* **`isCanonXS_of_stop_first`** (one sample, no probability).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rv GW2Sde GW2Sdh

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The stopped stage law where the candidate stops before the contact** (one sample): the re-centred relative
chain at the stop horizon is a canonical stopped driver for every version family capped at most the physical clock
of the stop. -/
theorem isCanonXS_of_stop_first (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞} {ξ : Ω} (hξ : ξ ∈ GT)
    (hR : ∀ n, VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n) ξ)
    (hVst : ∀ n, V n ξ ≤ physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT
      (RootJ31.historyTime c r l + GW2Psm.candStop c r l a ξ) ξ)
    (hv0 : 0 < RootJ31.historyTime c r l + GW2Psm.candStop c r l a ξ)
    (hstop : ((RootJ31.historyTime c r l + GW2Psm.candStop c r l a ξ : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ) :
    ∃ Wc : ℝ≥0 → ℝ, IsCanonXS c r l a R V ξ Wc := by
  set v : ℝ≥0 := RootJ31.historyTime c r l + GW2Psm.candStop c r l a ξ with hvdef
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ξ hξ
  have he := Gm.isRegularDriver_top hwc hw0
  have hv : (v : ℝ≥0∞) < min (contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
      ((fun t => schedW c r l a t ξ), (⊤ : ℝ≥0∞)).2 := by
    rw [min_top_right]
    exact hstop
  obtain ⟨Rc, hRc, hRc0, hhull⟩ := exists_recentred_chain c.W c.ζ ξ hα hW hW0 hζ hs hx harc he hγ hv hv0
  have hgen := GW2Bf.isGeneratingTrace_capacityTip_of_hull c.W c.ζ ξ hα hW hW0 hζ hs hx harc he hγ hv hhull
  -- the clock before the contact
  obtain ⟨-, hmono, -⟩ := clockX_props hGT hs hx hξ
  have hcl0 : ∀ t, 0 ≤ clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ := fun t =>
    RootJ32.forwardCapacity_nonneg _ _ _ _
  have hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ → t ≤ v →
      clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ ≤
        clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ := fun t ht htv =>
    (ENNReal.ofReal_le_ofReal_iff (hcl0 v)).1 (hmono ht hstop htv)
  -- the stopped life is the clock at the stop
  have hlife : stopLifeX c r l a ξ = clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ := by
    refine IsGreatest.csSup_eq ⟨⟨v, ⟨hstop, le_rfl⟩, rfl⟩, ?_⟩
    rintro _ ⟨t, ⟨ht, htv⟩, rfl⟩
    exact hle t ht htv
  refine ⟨Rc, hRc, hRc0, fun n q hq => ?_, ⟨_, _, hgen, ?_⟩,
    clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ, fun t ht htv => hle t ht htv⟩
  · -- every version is the horizon reader, which is the chain's driver
    have hphys := physClockX_eq_clockX hGT hs hx hξ hstop
    have hqV : (q : ℝ≥0∞) < ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ) := by
      rw [← hphys]
      exact hq.trans_le (hVst n)
    have hqc : (q : ℝ) < clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ := by
      rw [← ENNReal.ofReal_coe_nnreal] at hqV
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg q.coe_nonneg).1 hqV
    rw [version_eq_reader hGT hs hx hξ (hR n) hv0 hstop hqc hq.le]
    exact GW2Bf.capacityDriverRead_eq_of_hull c.W c.ζ ξ hα hW hW0 hζ hs hx harc he hγ hv hRc hRc0 hhull hqc
  · rw [hlife]
    exact le_rfl

end InteractingSLE.Theorem14.GW2Rd
