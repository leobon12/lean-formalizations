import InteractingSLE.Spec.Sec5.Aux61RestartInst

/-!
# Keeping the original right strip end as target

Packet PROVE-AUX61-R1. The strip chart Q sends the right strip end to `1`;
its counterflow starting point is infinity. Thus the old `junR` access must
not be substituted for this target. The map `z / (1-z)` sends `1` to infinity.
A domain with a free half-disc at `1` becomes the complement of a bounded
half-plane hull. This makes the existing hydrodynamic boundary APIs available.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61Restart

/-- Retarget Q at the original right strip end `1`, keeping the seed `0`. -/
def stripRightRetarget : ℂ → ℂ := QuantumZipper.CA.realMobius 1 0 (-1) 1

/-- The inverse of the right-strip-end retargeting map. -/
def stripRightUntarget : ℂ → ℂ := QuantumZipper.CA.realMobius 1 0 1 1

/-- The existing real Möbius bijection and its elementary derivative as a bundle. -/
theorem isConformalBijection_realMobius_of_pos_det {a b c d : ℝ}
    (hd : 0 < a * d - b * c) :
    IsConformalBijection (QuantumZipper.CA.realMobius a b c d) H H := by
  refine ⟨?_, QuantumZipper.CA.bijOn_realMobius_H hd⟩
  exact (((differentiable_id.const_mul (a : ℂ)).add_const (b : ℂ)).differentiableOn.div
    ((differentiable_id.const_mul (c : ℂ)).add_const (d : ℂ)).differentiableOn
    fun z hz => QuantumZipper.CA.realMobius_denom_ne_zero hd hz)

theorem isConformalBijection_stripRightRetarget :
    IsConformalBijection stripRightRetarget H H :=
  isConformalBijection_realMobius_of_pos_det (by norm_num)

theorem isConformalBijection_stripRightUntarget :
    IsConformalBijection stripRightUntarget H H :=
  isConformalBijection_realMobius_of_pos_det (by norm_num)

theorem stripRightUntarget_retarget {z : ℂ} (hz : z ∈ H) :
    stripRightUntarget (stripRightRetarget z) = z := by
  have h := QuantumZipper.CA.realMobius_inv_apply
    (a := 1) (b := 0) (c := -1) (d := 1) (by norm_num) hz
  simpa only [stripRightUntarget, stripRightRetarget, neg_zero, neg_neg] using h

theorem stripRightRetarget_untarget {z : ℂ} (hz : z ∈ H) :
    stripRightRetarget (stripRightUntarget z) = z := by
  have h := QuantumZipper.CA.realMobius_inv_apply
    (a := 1) (b := 0) (c := 1) (d := 1) (by norm_num) hz
  simpa only [stripRightUntarget, stripRightRetarget, neg_zero] using h

theorem tendsto_stripRightRetarget_target :
    Tendsto stripRightRetarget (𝓝[H] 1) (Bornology.cobounded ℂ ⊓ 𝓟 H) := by
  have h := PrimeEnd.tendsto_realMobius_approachH
    (a := 1) (b := 0) (c := -1) (d := 1) (by norm_num) (1 : ℝ)
  simpa only [stripRightRetarget, mobiusBdry_coe, neg_one_mul, neg_add_cancel, ite_true,
    PrimeEnd.approachH_infty, PrimeEnd.approachH_coe, ofReal_one] using h

theorem tendsto_stripRightUntarget_infty :
    Tendsto stripRightUntarget (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝[H] 1) := by
  have h := PrimeEnd.tendsto_realMobius_approachH
    (a := 1) (b := 0) (c := 1) (d := 1) (by norm_num) OnePoint.infty
  simpa only [stripRightUntarget, mobiusBdry_infty, one_ne_zero, ite_false, div_one,
    PrimeEnd.approachH_infty, PrimeEnd.approachH_coe, ofReal_one] using h

/-- The hull obtained by retaining the selected domain and changing its target. -/
def stripTargetHull (D : Set ℂ) : Set ℂ := H \ stripRightRetarget '' D

theorem H_diff_stripTargetHull {D : Set ℂ} (hDH : D ⊆ H) :
    H \ stripTargetHull D = stripRightRetarget '' D := by
  have hsub : stripRightRetarget '' D ⊆ H :=
    (isConformalBijection_stripRightRetarget.2.mapsTo.mono_left hDH).image_subset
  simp only [stripTargetHull, sdiff_sdiff_right_self, inter_eq_right.mpr hsub]

/-- A free collar at the original right end turns a simply connected retained
domain into a bounded hydrodynamic hull complement. -/
theorem isHPHull_stripTargetHull {D : Set ℂ} (hDo : IsOpen D)
    (hDs : IsSimplyConnected D) (hDH : D ⊆ H)
    (htarget : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ D) :
    IsHPHull (stripTargetHull D) := by
  obtain ⟨δ, hδ, hfree⟩ := htarget
  have hev : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 H, stripRightUntarget z ∈ D := by
    filter_upwards [tendsto_stripRightUntarget_infty.eventually
      (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (1 : ℂ) hδ)),
      mem_inf_of_right (mem_principal_self H)] with z hz hzH
    exact hfree ⟨hz, isConformalBijection_stripRightUntarget.2.mapsTo hzH⟩
  obtain ⟨R, hR⟩ := eventually_cobounded_inf_principal_iff.1 hev
  have hb : Bornology.IsBounded (stripTargetHull D) := by
    apply isBounded_iff_forall_norm_le.2
    refine ⟨R, fun z hz => le_of_not_ge fun hnorm => ?_⟩
    exact hz.2 ⟨stripRightUntarget z, hR z hz.1 hnorm, stripRightRetarget_untarget hz.1⟩
  have hf : IsConformalBijection stripRightRetarget D (stripRightRetarget '' D) :=
    ⟨isConformalBijection_stripRightRetarget.1.mono hDH,
      (isConformalBijection_stripRightRetarget.2.injOn.mono hDH).bijOn_image⟩
  refine ⟨sdiff_subset, hb, ?_, ?_⟩
  · rw [H_diff_stripTargetHull hDH]
    exact QuantumZipper.CA.isOpen_image_of_injOn hDo hf.1 hf.2.injOn hDo Subset.rfl
  · rw [H_diff_stripTargetHull hDH]
    exact isSimplyConnected_of_isConformalBijection hDo hf hDs

end InteractingSLE.Sec5.Aux61Restart
