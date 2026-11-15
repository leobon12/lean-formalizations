/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRIotaAccess

/-! # GW4: finite physical exceptions have finite initial-coordinate fibers -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GB11Chart

/-- The finite inverse extension agrees away from zero with the explicit
pocket coordinate formula, including on the original real boundary. -/
theorem Frame.physical_inverse_extension_eq {F : Frame} (hF : F.IsOk)
    {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) {E : ℂ → ℂ}
    (hE : EqOn E (relInvC F.c) H) (hEc : ContinuousOn E Hbar)
    {z : ℂ} (hz : z ∈ Hbar) (hz0 : z ≠ 0) :
    E z = -(F.G ((F.k : ℂ) * -z⁻¹))⁻¹ := by
  have hpc := hF.2.2.2.2.2.1
  have hCH := subset_H_of_mem_betweenComponents hF.2.1
  have hB := hw.2.2.2.2
  have harg : (F.k : ℂ) * -z⁻¹ ∈ Hbar := by
    simpa only [neg_mul, mul_neg] using negInv_inv_mem_Hbar hpc.pos hz
  have harg0 : (F.k : ℂ) * -z⁻¹ ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.2 hpc.pos.ne') (neg_ne_zero.2 (inv_ne_zero hz0))
  have hG0 := pocket_G_ne_zero hB.1 hB.2.1 hF.2.2.2.1 hCH hpc harg harg0
  have ha : Tendsto (fun y : ℂ => (F.k : ℂ) * -y⁻¹) (𝓝[H] z)
      (𝓝[Hbar] ((F.k : ℂ) * -z⁻¹)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => ?_⟩
    · exact (continuousAt_const.mul (continuousAt_inv₀ hz0).neg).tendsto.mono_left nhdsWithin_le_nhds
    · simpa only [neg_mul, mul_neg] using negInv_inv_mem_Hbar hpc.pos (QuantumZipper.H_subset_Hbar hy)
  have hlim : Tendsto (relInvC F.c) (𝓝[H] z)
      (𝓝 (-(F.G ((F.k : ℂ) * -z⁻¹))⁻¹)) :=
    (((hpc.continuousOn_G _ harg).tendsto.comp ha).inv₀ hG0).neg.congr'
      (eventually_nhdsWithin_of_forall fun y hy => (relInvC_eq hpc hy).symm)
  have hzcl : z ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact hz
  have : (𝓝[H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hzcl
  exact tendsto_nhds_unique
    (((hEc z hz).tendsto.mono_left (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)).congr'
      (eventually_nhdsWithin_of_forall fun y hy => hE hy)) hlim

/-- The initial physical inverse is injective on the closed half-plane
away from the entry coordinate. This is the existing pocket homeomorphism,
conjugated by inversion and its positive normalization. -/
theorem Frame.injOn_physical_inverse_extension {F : Frame} (hF : F.IsOk)
    {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) {E : ℂ → ℂ}
    (hE : EqOn E (relInvC F.c) H) (hEc : ContinuousOn E Hbar) :
    InjOn E (Hbar \ {0}) := by
  intro z hz v hv he
  rw [Frame.physical_inverse_extension_eq hF hw hE hEc hz.1 hz.2,
    Frame.physical_inverse_extension_eq hF hw hE hEc hv.1 hv.2] at he
  have hpc := hF.2.2.2.2.2.1
  have hz' : (F.k : ℂ) * -z⁻¹ ∈ Hbar := by
    simpa only [neg_mul, mul_neg] using negInv_inv_mem_Hbar hpc.pos hz.1
  have hv' : (F.k : ℂ) * -v⁻¹ ∈ Hbar := by
    simpa only [neg_mul, mul_neg] using negInv_inv_mem_Hbar hpc.pos hv.1
  have hG := inv_injective (neg_injective he)
  have harg := hpc.injOn_G hz' hv' hG
  have hneg := mul_left_cancel₀ (ofReal_ne_zero.2 hpc.pos.ne') harg
  exact inv_injective (neg_injective hneg)

/-- Every finite set of physical exceptions retains only finitely many
initial-coordinate fibers. The entry fiber is explicitly retained. -/
theorem Frame.finite_physical_inverse_preimage {F : Frame} (hF : F.IsOk)
    {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) {E : ℂ → ℂ}
    (hE : EqOn E (relInvC F.c) H) (hEc : ContinuousOn E Hbar)
    {S : Set ℂ} (hS : S.Finite) : (Hbar ∩ E ⁻¹' S).Finite := by
  have hi := Frame.injOn_physical_inverse_extension hF hw hE hEc
  have hfin : ((Hbar \ {0}) ∩ E ⁻¹' S).Finite :=
    (hS.subset (image_subset_iff.2 fun _ hz => hz.2)).of_finite_image
      (hi.mono inter_subset_left)
  apply ((finite_singleton (0 : ℂ)).union hfin).subset
  intro z hz
  by_cases hz0 : z = 0
  · exact Or.inl hz0
  · exact Or.inr ⟨⟨hz.1, hz0⟩, hz.2⟩

end InteractingSLE.Theorem14.GW4Fix
