/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRThetaLog
import InteractingSLE.Spec.Supplement.GW4SafeRBoundaryAccess

/-! # GW4: finite physical boundary extensions of the component charts -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GB11Chart

/-- A nonzero boundary coordinate of the pocket inverse cannot be the
physical point zero: on the real boundary this follows from the simple
walls and their prescribed orientation. -/
theorem pocket_G_ne_zero {αR αL : ℝ≥0 → ℂ} (hR : GB11.IsCompleteSimpleFlow αR)
    (hL : GB11.IsCompleteSimpleFlow αL) {C : Set ℂ} {c : Chart}
    (hc : IsComponentChart (range αR) (range αL) C c) (hCH : C ⊆ H)
    {s₁ t₁ : ℝ≥0} {E : Set ℂ} {ψ G : ℂ → ℂ} {k : ℝ}
    (hpc : IsPocketCoord αR αL C c s₁ t₁ E ψ G k) {z : ℂ}
    (hz : z ∈ Hbar) (hz0 : z ≠ 0) : G z ≠ 0 := by
  by_cases hzH : z ∈ H
  · have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hpc.pos.ne'
    have hdiv : z / (k : ℂ) ∈ H := by
      show 0 < (z / (k : ℂ)).im
      rw [div_ofReal_im]
      exact div_pos hzH hpc.pos
    have he := hpc.inv_eq (z / (k : ℂ)) hdiv
    rw [mul_div_cancel₀ _ hk0] at he
    exact ne_zero_of_mem_H' (he ▸ hCH (hc.2.2.1 hdiv))
  have hzi : z.im = 0 := le_antisymm (not_lt.1 hzH) hz
  have hzr : z = (z.re : ℂ) := Complex.ext (by simp only [ofReal_re]) (by simp only [ofReal_im, hzi])
  have hzr0 : z.re ≠ 0 := fun h => hz0 (by rw [hzr, h, ofReal_zero])
  rw [hzr]
  rcases lt_or_gt_of_ne hzr0 with hneg | hpos
  · obtain ⟨t, ht, he⟩ := hpc.neg_arc _ hneg
    intro h0
    have ht0 : t = 0 := hL.2.1 ((he.trans h0).trans hL.2.2.1.symm)
    exact (not_lt_of_ge (show 0 ≤ t₁ from zero_le)) (show t₁ < 0 from ht0 ▸ ht)
  · obtain ⟨s, hs, he⟩ := hpc.pos_arc _ hpos
    intro h0
    have hs0 : s = 0 := hR.2.1 ((he.trans h0).trans hR.2.2.1.symm)
    exact (not_lt_of_ge (show 0 ≤ s₁ from zero_le)) (show s₁ < 0 from hs0 ▸ hs)

/-- The conjugated component inverse has finite limits at every finite
coordinate. The entry uses the bounded/unbounded pocket alternatives;
every other coordinate uses the actual continuous wall parametrization. -/
theorem Frame.exists_physical_inverse_extension {F : Frame} (hF : F.IsOk)
    {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) :
    ∃ E : ℂ → ℂ, EqOn E (relInvC F.c) H ∧ ContinuousOn E Hbar ∧ MapsTo E Hbar Hbar := by
  have hCo := Frame.isOpen_C hF hw
  have hCH := GW4Traverse.subset_H_of_mem_betweenComponents hF.2.1
  have hpc := hF.2.2.2.2.2.1
  have hpd := hF.2.2.2.2.2
  have hB := hw.2.2.2.2
  have hlim : ∀ v ∈ Hbar, ∃ p : ℂ, Tendsto (relInvC F.c) (𝓝[H] v) (𝓝 p) := by
    intro v hv
    by_cases hv0 : v = 0
    · subst v
      rcases hpd.2.2.2.2.2.2.2 with ⟨hE, -⟩ | ⟨hE, -⟩
      · refine ⟨0, ?_⟩
        have hdom : (0 : ℂ) ∈ relDomBar F.C F.E (F.αR F.s₁) := Or.inl ⟨rfl, hE⟩
        simpa only [relPt, eq_self, true_or, ite_true] using
          tendsto_relInvC_relPt hpc hpd.2.2.1 hpd.2.2.2.2.1 hpd.2.2.2.2.2.2.1 hdom
      · have hQ0 : F.αR F.s₂.toNNReal ≠ 0 := by
          intro h0
          exact hpd.2.2.1 (by rw [hE, h0]; exact mem_singleton 0)
        refine ⟨-(F.αR F.s₂.toNNReal)⁻¹, ?_⟩
        have h1 := ((hpd.2.2.2.2.1 _ (by rw [hE]; exact mem_singleton _)).comp
          (tendsto_mul_negInv_zero hpc.pos)).inv₀ hQ0
        have h2 := h1.neg
        exact h2.congr' (eventually_nhdsWithin_of_forall fun y hy => (relInvC_eq hpc hy).symm)
    · have harg : (F.k : ℂ) * -v⁻¹ ∈ Hbar := by
        simpa only [neg_mul, mul_neg] using negInv_inv_mem_Hbar hpc.pos hv
      have harg0 : (F.k : ℂ) * -v⁻¹ ≠ 0 :=
        mul_ne_zero (ofReal_ne_zero.2 hpc.pos.ne') (neg_ne_zero.2 (inv_ne_zero hv0))
      have hG0 := pocket_G_ne_zero hB.1 hB.2.1 hF.2.2.2.1 hCH hpc harg harg0
      have ha : Tendsto (fun y : ℂ => (F.k : ℂ) * -y⁻¹) (𝓝[H] v)
          (𝓝[Hbar] ((F.k : ℂ) * -v⁻¹)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => ?_⟩
        · exact (continuousAt_const.mul (continuousAt_inv₀ hv0).neg).tendsto.mono_left nhdsWithin_le_nhds
        · simpa only [neg_mul, mul_neg] using
            negInv_inv_mem_Hbar hpc.pos (QuantumZipper.H_subset_Hbar hy)
      refine ⟨-(F.G ((F.k : ℂ) * -v⁻¹))⁻¹, ?_⟩
      have he := ((hpc.continuousOn_G _ harg).tendsto.comp ha).inv₀ hG0
      exact he.neg.congr' (eventually_nhdsWithin_of_forall fun y hy => (relInvC_eq hpc hy).symm)
  let E := extendFrom H (relInvC F.c)
  have hEq : EqOn E (relInvC F.c) H := fun z hz =>
    extendFrom_eq (subset_closure hz) (((continuousOn_relInvC hF.2.2.2.1 hCo hCH).continuousAt
      (QuantumZipper.isOpen_H.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds)
  have hEc : ContinuousOn E Hbar := continuousOn_extendFrom
    (by rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]) hlim
  refine ⟨E, hEq, hEc, fun z hz => ?_⟩
  have hzcl : z ∈ closure H := by
    rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]; exact hz
  have : (𝓝[H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hzcl
  obtain ⟨p, hp⟩ := hlim z hz
  have hEp : E z = p := extendFrom_eq (by
    rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]; exact hz) hp
  rw [hEp, ← show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]
  exact mem_closure_of_tendsto hp (eventually_nhdsWithin_of_forall fun y hy =>
    relDom_subset_H hCH (relInvC_mem hF.2.2.2.1 hy))

/-- The actual relative hull version also gives the finite physical
inverse extension after each live stage, including wall accesses. -/
theorem Frame.exists_physical_stage_inverse_extension {F : Frame} (hF : F.IsOk)
    {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) {R : ℝ → ℝ}
    (hR : Continuous R) (hR0 : R 0 = 0) {q t : ℝ≥0}
    (he : QuantumZipper.fwdHull R q = F.hullAt w t) :
    ∃ E : ℂ → ℂ, EqOn E (componentAmbientChart F.c R q).2.1 H ∧
      ContinuousOn E Hbar ∧ MapsTo E Hbar Hbar := by
  obtain ⟨E, hE, hEc, hEH⟩ := Frame.exists_physical_inverse_extension hF hw
  obtain ⟨Fb, hFb, hFbc⟩ := Frame.exists_inverse_extension_of_hullAt hF hw hR hR0 he
  have hFbH0 : MapsTo Fb H H := fun y hy =>
    hFb hy ▸ QuantumZipper.RS.fwdMapInv_mem_H hR hR0 q.coe_nonneg hy
  have hFbH : MapsTo Fb Hbar Hbar := by
    have hcl : closure H = Hbar := Complex.closure_setOfPred_lt_im 0
    rw [← hcl] at hFbc ⊢
    exact hFbH0.closure_of_continuousOn hFbc
  refine ⟨E ∘ Fb, ?_, hEc.comp hFbc hFbH, hEH.comp hFbH⟩
  intro z hz
  change E (Fb z) = relInvC F.c (QuantumZipper.fwdMapInv R q z)
  rw [hFb hz, hE (QuantumZipper.RS.fwdMapInv_mem_H hR hR0 q.coe_nonneg hz)]

end InteractingSLE.Theorem14.GW4Fix
