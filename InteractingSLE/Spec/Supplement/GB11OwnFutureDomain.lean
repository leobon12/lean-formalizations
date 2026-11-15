/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11OwnFuturePoint

/-!
# GB11: the ambient own future and the current domain

The current domain is the image of the active part of the reversed pocket under the
ambient mapping-out function. We compactify it by `mu`, which is regular on the closed
half-plane, so the bounded and unbounded pockets use the same boundary-extension API.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-- The current domain in the centered ambient chart at time `t`. -/
def ownDomain (W : ℝ → ℝ) (C : Set ℂ) (t : ℝ) : Set ℂ :=
  {w ∈ H | trMap W 0 t w ∈ relDom C}

/-- The finite compactification of the current domain is bounded. -/
theorem isBounded_mu_ownDomain (W : ℝ → ℝ) (C : Set ℂ) (t : ℝ) :
    IsBounded (mu '' ownDomain W C t) :=
  (isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset (by
    rintro _ ⟨w, hw, rfl⟩
    exact mem_closedBall_zero_iff.2 (norm_mu_le_one (H_subset_Hbar hw.1)))

/-- Inverting the compactification is a conformal bijection on the current domain. -/
theorem isConformalBijection_muInv_ownDomain (W : ℝ → ℝ) (C : Set ℂ) (t : ℝ) :
    IsConformalBijection muInv (mu '' ownDomain W C t) (ownDomain W C t) := by
  refine ⟨fun w hw => ?_, ?_, ?_, ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hw
    have h0 : mu z ≠ 0 := mu_ne_zero_of_mem_Hbar (H_subset_Hbar hz.1)
    have hdid : DifferentiableAt ℂ (fun w : ℂ => w) (mu z) := differentiableAt_id
    have hd : DifferentiableAt ℂ (fun w : ℂ => -w⁻¹ - Complex.I) (mu z) :=
      (hdid.inv h0).neg.sub (differentiableAt_const _)
    exact hd.differentiableWithinAt
  · rintro _ ⟨w, hw, rfl⟩
    rwa [muInv_mu]
  · intro w _ w' _ he
    have := congrArg mu he
    simpa only [mu_muInv] using this
  · intro w hw
    exact ⟨mu w, ⟨w, hw, rfl⟩, muInv_mu w⟩

/-- The ambient inverse maps the current domain conformally onto the active pocket. -/
theorem isConformalBijection_trMap_ownDomain {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) (hCH : C ⊆ H) :
    IsConformalBijection (trMap W 0 t) (ownDomain W C t) (relDom C \ fwdHull W t) := by
  have heq : ∀ w ∈ H, trMap W 0 t w = fwdMapInv W t w := fun w hw => by
    rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW ht hw,
      YuanSimpleApprox.shiftDrive_zero_eq hW0, sub_zero]
  refine ⟨((QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 ht).mono fun w hw => hw.1).congr
    (fun w hw => heq w hw.1), ?_, ?_, ?_⟩
  · intro w hw
    refine ⟨hw.2, ?_⟩
    rw [heq w hw.1]
    exact (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hw.1).2
  · intro w hw w' hw' he
    rw [heq w hw.1, heq w' hw'.1] at he
    exact QuantumZipper.RS.injOn_fwdMapInv_H hW hW0 ht hw.1 hw'.1 he
  · intro z hz
    have hzD : z ∈ H \ fwdHull W t := ⟨relDom_subset_H hCH hz.1, hz.2⟩
    rw [← QuantumZipper.RS.image_fwdMapInv_H hW hW0 ht] at hzD
    obtain ⟨w, hw, rfl⟩ := hzD
    refine ⟨w, ⟨hw, ?_⟩, heq w hw⟩
    rw [heq w hw]
    exact hz.1

/-- The open-pocket visits approach every nonterminal traversal time from the right. -/
theorem mem_closure_later_visits {γ : ℝ≥0 → ℂ} {C : Set ℂ} {τ : ℝ≥0} {σ : ℝ≥0∞}
    (hD : ∀ a b : ℝ≥0, τ ≤ a → a < b → (b : ℝ≥0∞) < σ →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C)
    {s : ℝ} {a : ℝ≥0} (hsa : s ≤ (a : ℝ)) (hτa : τ ≤ a) (haσ : (a : ℝ≥0∞) < σ) :
    (a : ℝ) ∈ closure {r : ℝ | s < r ∧ γ r.toNNReal ∈ relDom C} := by
  apply Metric.mem_closure_iff.2
  intro ε hε
  have hlt : (a : ℝ≥0∞) < min σ ((a + (ε / 2).toNNReal : ℝ≥0) : ℝ≥0∞) :=
    lt_min haσ (ENNReal.coe_lt_coe.2 (lt_add_of_pos_right _
      (Real.toNNReal_pos.2 (half_pos hε))))
  obtain ⟨b, hab, hb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  obtain ⟨r, hr, -, hrC⟩ := hD a b hτa (ENNReal.coe_lt_coe.1 hab)
    (lt_of_lt_of_le hb (min_le_left _ _))
  have hba : (b : ℝ) ≤ (a : ℝ) + ε / 2 := by
    have h := NNReal.coe_le_coe.2 (ENNReal.coe_le_coe.1 (hb.le.trans (min_le_right _ _)))
    rwa [NNReal.coe_add, Real.coe_toNNReal _ (half_pos hε).le] at h
  have har : (a : ℝ) < (r : ℝ) := NNReal.coe_lt_coe.2 hr.1
  have hrb : (r : ℝ) < (b : ℝ) := NNReal.coe_lt_coe.2 hr.2
  refine ⟨(r : ℝ), ⟨hsa.trans_lt har, ?_⟩, ?_⟩
  · simpa only [Real.toNNReal_coe] using (show γ r ∈ relDom C from hrC)
  · rw [Real.dist_eq, abs_of_neg (sub_neg.2 har)]
    linarith

end InteractingSLE.Theorem14.GB11Chart
