/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1SafeRead
import InteractingSLE.Spec.Supplement.RelSafeS7

/-!
# The shape of BW1's physical union ((L2) for BW1)

Packet PROVE-BW1-SAFELAW. GB6's `RelSafeS.ae_compl_union_eq_relChart` with the retained time read from the record:
almost surely on the good event and before the stop, `ℍ ∖ (−1/K_ζ ∪ K'_t)` is the inverse relative chart image of
`ℍ ∖ K̃_{a(t)}` (`a = min(bClock, V)`, `K_ζ` the hull of the record driver at its own time `recS`, `K'_t` the physical
counterflow hull, `K̃` the relative hull of the version): `t` precedes the first contact (otherwise the clock has
reached `V`), `a(t)` is the relative clock at `t`, the version maps `K'_t` onto `K̃_{a(t)}`, and `K'_t` misses the
retained set before the first contact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)

namespace InteractingSLE.Theorem14.BW1Safe

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.RelSafe Supp8.RelSafeS Theorem14.GW2JointKernel BW1Ver

section Shape

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {rec : Ω → RecData} {W : ℝ≥0 → Ω → ℝ}
  {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

omit mΩ in
/-- On the good event, before the stop, the physical time precedes the first contact and the line clock is the
relative clock. -/
theorem lt_bTc_of_lt_stop (hGT : ∀ ω ∈ GT, BGood rec W ω) {ω : Ω} (hωG : ω ∈ GT)
    (hreachV : ∀ u : ℝ≥0, (u : ℝ≥0∞) < V ω →
      ∃ t : ℝ≥0, (t : ℝ≥0∞) < bTc rec W ω ∧ (u : ℝ) < rclk (rec ω) (W · ω) t)
    {t : ℝ≥0} (hlt : min (bClock rec W GT t ω) (V ω) < V ω) : (t : ℝ≥0∞) < bTc rec W ω := by
  by_contra hcon
  have hle : bTc rec W ω ≤ t := le_of_not_gt hcon
  have hV : V ω ≤ bClock rec W GT t ω := by
    rw [bClock_eq_iSup hGT hωG]
    refine ENNReal.le_of_forall_nnreal_lt fun u hu => ?_
    obtain ⟨t', ht', hut'⟩ := hreachV u hu
    have ht't : t' < t := by
      have := lt_of_lt_of_le ht' hle
      exact_mod_cast this
    refine le_trans ?_ (le_iSup₂ (f := fun (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) < bTc rec W ω) =>
      ENNReal.ofReal (rclk (rec ω) (W · ω) t')) t' ⟨ht't, ht'⟩)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hut'.le
  rw [min_eq_right hV] at hlt
  exact lt_irrefl _ hlt

/-- **The complement of BW1's physical union is the inverse relative chart image of the complement of the relative
hull**, almost surely on the good event before the stop. -/
theorem ae_compl_union_eq_relChart_bw (hGT : ∀ ω ∈ GT, BGood rec W ω) (hv : IsBVer P rec W GT R V) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ GT → min (bClock rec W GT t ω) (V ω) < V ω →
      H \ (Supp8.Q3Rel.invHull (rdrv (rec ω)) (recS (rec ω)) ∪ fwdHull (fun r : ℝ => W r.toNNReal ω) t) =
        (relChart (rec ω)).2.1 ''
          (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal) := by
  filter_upwards [hv.ae] with ω hω hωG hlt
  have hg := hGT ω hωG
  obtain ⟨-, hreachV, hhull⟩ := hω hωG
  have htc := lt_bTc_of_lt_stop hGT hωG hreachV hlt
  -- the clock at `t`
  have hphys := bClock_eq_rclk hGT hωG htc
  obtain ⟨ha0, hsm, -⟩ := hg.clock_regular
  have hnn : 0 ≤ rclk (rec ω) (W · ω) t := by
    have h0T : ((0 : ℝ≥0) : ℝ≥0∞) < bTc rec W ω := lt_of_le_of_lt bot_le htc
    have := hsm.monotoneOn h0T htc (bot_le : (0 : ℝ≥0) ≤ t)
    rw [ha0] at this
    exact this
  have hlt' : ENNReal.ofReal (rclk (rec ω) (W · ω) t) < V ω := by
    rw [hphys] at hlt
    exact lt_of_not_ge fun h => lt_irrefl _ (by rwa [min_eq_right h] at hlt)
  have hmin : min (bClock rec W GT t ω) (V ω) = ENNReal.ofReal (rclk (rec ω) (W · ω) t) := by
    rw [hphys]
    exact min_eq_left hlt'.le
  have hreal : (((ENNReal.ofReal (rclk (rec ω) (W · ω) t)).toNNReal : ℝ≥0) : ℝ) = rclk (rec ω) (W · ω) t := by
    rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hnn]
  have hH := hhull t htc hlt'.le
  rw [hmin, hreal]
  change H \ (Supp8.Q3Rel.invHull (rdrv (rec ω)) (recS (rec ω)) ∪ fwdHull (Ito.rpath (W · ω)) t) =
    (relChart (rec ω)).2.1 '' (H \ fwdHull (Ito.rpath (R · ω)) (rclk (rec ω) (W · ω) t))
  rw [hH]
  -- the relative chart of the record
  have hw := continuous_rdrv (rec ω)
  have hw0 := rdrv_zero (rec ω)
  rw [relChart_eq_jointChart (s := recS (rec ω)) rfl,
    show relMap (rdrv (rec ω)) (recS (rec ω)) = (jointChart (rdrv (rec ω)) (recS (rec ω))).1 from rfl]
  have hdc := Supp8.Q3Rel.isDomainChart_rel hw hw0 (recS (rec ω)).coe_nonneg
  -- the counterflow hull misses the retained set
  have hdis' := Supp8.Q3Rel.disjoint_closure_invHull hw (recS (rec ω)).coe_nonneg (hg.disjoint htc)
  have hK : fwdHull (Ito.rpath (W · ω)) t ⊆ H \ Supp8.Q3Rel.invHull (rdrv (rec ω)) (recS (rec ω)) := by
    intro z hz
    refine ⟨(isHPHull_fwdHull (hg.cont.comp continuous_real_toNNReal) t.coe_nonneg).1 hz, fun hzA => ?_⟩
    exact Set.disjoint_left.1 hdis' (subset_closure hz) (subset_closure hzA)
  rw [image_inv_compl_image_fwd hdc.1 hdc.2.1 hK, Set.sdiff_sdiff]

end Shape

end InteractingSLE.Theorem14.BW1Safe
