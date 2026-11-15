/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedInstAccess
import InteractingSLE.Spec.ZhanGT4.DualTwoDirEncl

/-!
# The actual chosen two-view rectangle from protected enclosures

Packet PROVE-ZHAN-GT4-A22. Both image chains use the landed `imgChain`
choice. Their existence and mutual-tip aliveness are proved here from the
hull inclusions, including the two zero-height sides.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (H IsForwardSol fwdMap fwdHull)

/-- The actual opposite chosen clock, with its growing source at zero. -/
def seedTSrcClock (W₁ W₂ : ℝ → ℝ) (T s : ℝ) : ℝ → ℝ :=
  seedSrcClock (fun u => W₂ u - W₂ 0) T (fun u => W₁ u - W₂ 0) s

/-- The actual opposite chosen image driver. -/
def seedTSrcDriver (W₁ W₂ : ℝ → ℝ) (T s : ℝ) : ℝ → ℝ :=
  seedSrcDriver (fun u => W₂ u - W₂ 0) T (fun u => W₁ u - W₂ 0) s

/-- The opposite chosen chain exists on the entire second horizon for
any frozen first height in the rectangle. -/
theorem seedTSrcOwn_of_enclosures {W₁ W₂ : ℝ → ℝ} {S T s δ : ℝ} {H₁ H₂ : Set ℂ}
    (hW₁ : Continuous W₁) (hW₂ : Continuous W₂) (hT : 0 < T) (hs : s ∈ Icc (0 : ℝ) S)
    (hδ : 0 < δ) (hsep : ∀ z ∈ H₂, ∀ w ∈ H₁, 2 * δ ≤ ‖z - w‖)
    (hK₁ : fwdHull W₁ S ⊆ H₁) (hK₂ : fwdHull W₂ T ⊆ H₂) :
    OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) s)
      (frzChart (fun u => W₁ u - W₂ 0) s) T (seedTSrcClock W₁ W₂ T s) (seedTSrcDriver W₁ W₂ T s) := by
  have hsep' : ∀ z ∈ H₁, ∀ w ∈ H₂, 2 * δ ≤ ‖z - w‖ := by
    intro z hz w hw
    rw [norm_sub_rev]
    exact hsep w hw z hz
  exact seedSrcOwn_of_enclosures (hW₂.sub continuous_const) (sub_self _) hT
    (hW₁.sub continuous_const) hs.1 hδ (sep_transl hsep' (-W₂ 0))
    (fwdHull_sub_const_subset hK₂)
    (fwdHull_sub_const_subset (((QuantumZipper.fwdHull_mono).1 hs.2).trans hK₁))

/-- The actual source selections satisfy the whole two-view rectangle
from the protected enclosures; no image-chain or access-flow premise remains. -/
theorem twoViewRect_seedSrc_of_enclosures {W₁ W₂ : ℝ → ℝ} {S T δ p q d : ℝ} {H₁ H₂ : Set ℂ}
    (hp : A1SeedField.IsProtectedPair H₁ H₂ δ p q d)
    (hW₁ : Continuous W₁) (hW₂ : Continuous W₂) (h0₁ : W₁ 0 = 0) (h0₂ : W₂ 0 = p)
    (hS : 0 < S) (hT : 0 < T) (hK₁ : fwdHull W₁ S ⊆ H₁) (hK₂ : fwdHull W₂ T ⊆ H₂) :
    TwoViewRect W₁ W₂ S T (seedSrcClock W₁ S W₂) (seedSrcDriver W₁ S W₂)
      (seedTSrcClock W₁ W₂ T) (seedTSrcDriver W₁ W₂ T) where
  nonneg_X := hS.le
  nonneg_Y := hT.le
  sOwn t ht := by
    have hKt := ((QuantumZipper.fwdHull_mono).1 ht.2).trans hK₂
    have ho := seedSrcOwn_of_enclosures hW₁ h0₁ hS hW₂ ht.1 hp.sep_pos hp.sep hK₁ hKt
    have hne : W₁ 0 ≠ W₂ 0 := by rw [h0₁, h0₂]; exact (hp.prot_pos.trans hp.prot_lt).ne
    exact ⟨S, le_rfl, ho, ho.tip_alive_of_enclosures hp.hull₁ hp.hull₂ hp.sep_pos hp.sep
      hW₂ ht.1 hne (by simpa only [h0₂] using hp.src) hK₁ hKt⟩
  tOwn s hs := by
    have ho := seedTSrcOwn_of_enclosures hW₁ hW₂ hT hs hp.sep_pos hp.sep hK₁ hK₂
    have hsep' : ∀ z ∈ H₁, ∀ w ∈ H₂, 2 * δ ≤ ‖z - w‖ := by
      intro z hz w hw
      rw [norm_sub_rev]
      exact hp.sep w hw z hz
    have hsrc : (((fun u => W₁ u - W₂ 0) 0 : ℝ) : ℂ) ∈ closure (transl (-W₂ 0) H₁) := by
      have hm := mem_closure_transl (closure_mono hK₁ (start_mem_closure_fwdHull hW₁ hS)) (-W₂ 0)
      simpa only [ofReal_sub, ofReal_neg, sub_eq_add_neg, ofReal_add] using hm
    have hne : (fun u => W₂ u - W₂ 0) 0 ≠ (fun u => W₁ u - W₂ 0) 0 := by
      simp only [h0₁, h0₂, sub_self, zero_sub]
      exact (neg_neg_of_pos (hp.prot_pos.trans hp.prot_lt)).ne'
    exact ⟨T, le_rfl, ho, ho.tip_alive_of_enclosures
      (isHPHull_transl hp.hull₂ (-W₂ 0)) (isHPHull_transl hp.hull₁ (-W₂ 0))
      hp.sep_pos (sep_transl hsep' (-W₂ 0)) (hW₁.sub continuous_const) hs.1 hne hsrc
      (fwdHull_sub_const_subset hK₂)
      (fwdHull_sub_const_subset (((QuantumZipper.fwdHull_mono).1 hs.2).trans hK₁))⟩

end InteractingSLE.ZhanGT4
