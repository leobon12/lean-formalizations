/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBCurve
import InteractingSLE.Spec.Supplement.GW1ActiveWord
import InteractingSLE.Spec.Supplement.GW2FbDual
import InteractingSLE.Spec.Sec7.Aux37SideReflect

/-!
# The untouched real boundary of GW2's retained chart

Packet PROVE-GW2-SAFE. Away from the closed retained hull, the extended
relative map is real-boundary-conformal. Its real boundary values are the
two inversions of the ordinary real Loewner flow. These facts allow the
closed bad-boundary set to be compared in physical and relative coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdMap)

namespace InteractingSLE.Theorem14.GW2Sf

open Restart Exist.StagedLaw FCDet Sec7.StripSysField Supp8 Supp8.GB6 Supp8.GB6.CoordB Q3Rel

/-- The relative boundary map has the existing Schwarz-reflection interface
on every disc missing the closed retained hull. -/
theorem isRealBoundaryConformal_relBdry {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s x r : ℝ} (hs : 0 ≤ s) (hball : ball (x : ℂ) r ⊆ (closure (invHull U s))ᶜ) :
    R16.IsRealBoundaryConformal (relBdry U s) x r := by
  have hc := isDomainChart_rel hU hU0 hs
  have hsub : H ∩ ball (x : ℂ) r ⊆ relDomain U s :=
    fun z hz => ⟨hz.1, fun h => hball hz.2 (subset_closure h)⟩
  have heq : EqOn (relBdry U s) (relMap U s) (H ∩ ball (x : ℂ) r) :=
    fun z hz => relBdry_eq hU hs hz.1 (hball hz.2)
  refine ⟨(hc.differentiableOn_fwd.mono hsub).congr heq, ?_, ?_, ?_, ?_⟩
  · exact (continuousOn_relBdry hU hU0 hs).mono fun z hz => ⟨hz.1, hball hz.2⟩
  · intro z hz hz0
    have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa only [ofReal_im] using hz0)
    exact he ▸ im_relBdry_of_real hU hU0 hs (he ▸ hball hz)
  · intro z hz
    rw [heq hz]
    exact hc.fwd_mem (hsub hz)
  · intro z hz w hw he
    rw [heq hz, heq hw] at he
    exact hc.isConformalBijection.2.2.1 (hsub hz) (hsub hw) he

/-- Explicit real boundary values at a nonzero untouched point. -/
theorem relBdry_of_real {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s x : ℝ} (hs : 0 ≤ s) (hx0 : x ≠ 0) (hxA : (x : ℂ) ∉ closure (invHull U s)) :
    relBdry U s x = ((-(fwdMap U s ((-x⁻¹ : ℝ) : ℂ)).re⁻¹ : ℝ) : ℂ) := by
  have hy0 : -x⁻¹ ≠ 0 := by simp [hx0]
  have hyK := negInv_notMem_closure hx0 hxA
  have : NeBot (𝓝[H] (((-x⁻¹ : ℝ)) : ℂ)) := by
    apply mem_closure_iff_nhdsWithin_neBot.1
    rw [closure_H]
    simp [QuantumZipper.Hbar]
  have hF := tendsto_fwdMap_re hU hU0 hs hy0 hyK
  obtain ⟨v, hvp, hvn, hv⟩ := exists_tendsto_fwdMap_real hU hU0 hs hy0 hyK
  have he : (v : ℂ) = ((fwdMap U s ((-x⁻¹ : ℝ) : ℂ)).re : ℂ) := tendsto_nhds_unique hv hF
  have hne : ((fwdMap U s ((-x⁻¹ : ℝ) : ℂ)).re : ℂ) ≠ 0 := by
    rw [← he, ofReal_ne_zero]
    rcases lt_or_gt_of_ne hy0 with hn | hp
    · exact (hvn hn).ne
    · exact (hvp hp).ne'
  have ht := ((continuousAt_inv₀ hne).neg.tendsto).comp
    (hF.comp (tendsto_negInv_real hx0 (sdiff_subset : relDomain U s ⊆ H)))
  have ht' : Tendsto (relMap U s) (𝓝[relDomain U s] (x : ℂ))
      (𝓝 (((-(fwdMap U s ((-x⁻¹ : ℝ) : ℂ)).re⁻¹ : ℝ)) : ℂ)) := by
    convert ht using 1 <;> try rfl
    simp only [Pi.neg_apply, ofReal_neg, ofReal_inv]
  exact extendFrom_eq (relSafe_subset_closure_relDomain U s ⟨by simp [QuantumZipper.Hbar], hxA⟩) ht'

/-- The untouched real chart preserves the side of the seed. -/
theorem relBdry_real_sign {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s x : ℝ} (hs : 0 ≤ s) (hx0 : x ≠ 0) (hxA : (x : ℂ) ∉ closure (invHull U s)) :
    (0 < x ↔ 0 < (relBdry U s x).re) ∧ (x < 0 ↔ (relBdry U s x).re < 0) := by
  have hy0 : -x⁻¹ ≠ 0 := by simp [hx0]
  have hyK := negInv_notMem_closure hx0 hxA
  obtain ⟨v, hvp, hvn, hv⟩ := exists_tendsto_fwdMap_real hU hU0 hs hy0 hyK
  have : NeBot (𝓝[H] (((-x⁻¹ : ℝ)) : ℂ)) :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; simp [QuantumZipper.Hbar])
  have he := tendsto_nhds_unique hv (tendsto_fwdMap_re hU hU0 hs hy0 hyK)
  have her : v = (fwdMap U s ((-x⁻¹ : ℝ) : ℂ)).re := by exact_mod_cast he
  rw [relBdry_of_real hU hU0 hs hx0 hxA, ofReal_re, ← her]
  rcases lt_or_gt_of_ne hx0 with hn | hp
  · have hvpos := hvp (neg_pos.2 (inv_lt_zero.2 hn))
    constructor
    · exact iff_of_false (not_lt.2 hn.le) (not_lt.2 (neg_nonpos.2 (inv_nonneg.2 hvpos.le)))
    · exact iff_of_true hn (neg_lt_zero.2 (inv_pos.2 hvpos))
  · have hvneg := hvn (neg_lt_zero.2 (inv_pos.2 hp))
    constructor
    · exact iff_of_true hp (neg_pos.2 (inv_lt_zero.2 hvneg))
    · exact iff_of_false (not_lt.2 hp.le) (not_lt.2 (neg_nonneg.2 (inv_nonpos.2 hvneg.le)))

/-- On the untouched real line, the returned stop word has exactly the
initial returned height, away from the finitely many word junctions. -/
theorem gb6WordOfRec_fn_relBdry {k : ℝ} (hk : 0 < k) (c : BoundaryWord) (r : RecData)
    {x : ℝ} (hx0 : x ≠ 0) (hxA : (x : ℂ) ∉ closure (invHull (rdrv r) (rtime r)))
    (hxJ : -x⁻¹ ∉ c.jumps)
    (hyJ : (relBdry (rdrv r) (rtime r) x).re ∉ (gb6WordOfRec k 0 c r).jumps) :
    (gb6WordOfRec k 0 c r).fn (relBdry (rdrv r) (rtime r) x).re =
      returnData (Real.pi * QuantumZipper.chiC k) (QuantumZipper.chiC k) c.fn x := by
  have hc := continuous_rdrv r
  have hc0 := rdrv_zero r
  have hs := rtime_nonneg r
  have hsign := relBdry_real_sign hc hc0 hs hx0 hxA
  have halive := BHMean.exists_isForwardSol_of_notMem_closure hc hc0 hs
    (negInv_notMem_closure hx0 hxA) (by simp [hx0] : -x⁻¹ ≠ 0)
  have he : -(relBdry (rdrv r) (rtime r) x).re⁻¹ =
      (fwdMap (rdrv r) (rtime r) ((-x⁻¹ : ℝ) : ℂ)).re := by
    rw [relBdry_of_real hc hc0 hs hx0 hxA, ofReal_re, neg_inv_neg_inv_real]
  have hzJ := negInv_notMem_stopWord_jumps (κ := k) 0 c r hyJ
  rw [he] at hzJ
  rcases lt_or_gt_of_ne hx0 with hn | hp
  · rw [gb6WordOfRec_fn_of_neg 0 c r (hsign.2.1 hn) hyJ, he,
      GW1W.stopWord_fn_fwdMap hk c 0 r (neg_pos.2 (inv_lt_zero.2 hn)) halive hxJ hzJ,
      returnData, liftBoundary_of_neg hn]
    ring
  · rw [gb6WordOfRec_fn_of_pos 0 c r (hsign.1.1 hp) hyJ, he,
      GW1W.stopWord_fn_fwdMap_neg hk c 0 r (neg_lt_zero.2 (inv_pos.2 hp)) halive hxJ hzJ,
      returnData, liftBoundary_of_pos hp]
    ring

end InteractingSLE.Theorem14.GW2Sf
