import QuantumZipper.Proofs.Section5.Prop16LitDilEvent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the dilation event, deterministic consequences (D98)

* `dil_of_dilGood`: the event forces the canonical local limit `(· / s)_* μ`;
* `dilGood_of_localAreaRegular`: local regularity (a.s. at fixed points) implies the event at
  every scale `s > 0`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open ExA GoodSample

theorem preimage_mul_ball_inter_H {r s : ℝ} (hs : 0 < s) :
    (fun z : ℂ => (s : ℂ) * z) ⁻¹' (ball 0 r ∩ H) = ball 0 (r / s) ∩ H := by
  ext z
  simp only [mem_preimage, mem_inter_iff, mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hs.le]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [lt_div_iff₀ hs]; linarith, ?_⟩
    have h2' : 0 < ((s : ℂ) * z).im := h2
    rw [Complex.im_ofReal_mul] at h2'
    exact pos_of_mul_pos_right h2' hs.le
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [lt_div_iff₀ hs] at h1; linarith, ?_⟩
    show 0 < ((s : ℂ) * z).im
    rw [Complex.im_ofReal_mul]; exact mul_pos hs h2

theorem map_div_facts {r s : ℝ} (hs : 0 < s) {μ : Measure ℂ} (h0 : μ (ball 0 r ∩ H)ᶜ = 0)
    (hK : ∀ K, IsCompact K → K ⊆ ball 0 r ∩ H → μ K < ∞) :
    (μ.map fun z => z / (s : ℂ)) (ball 0 (r / s) ∩ H)ᶜ = 0 ∧
      ∀ K, IsCompact K → K ⊆ ball 0 (r / s) ∩ H → (μ.map fun z => z / (s : ℂ)) K < ∞ := by
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hm : Measurable fun z : ℂ => z / (s : ℂ) := measurable_id.div_const _
  have hpre : ∀ T : Set ℂ, (fun z : ℂ => z / (s : ℂ)) ⁻¹' ((fun z => (s : ℂ) * z) ⁻¹' T) = T :=
    fun T => by ext z; simp only [mem_preimage, mul_div_cancel₀ _ hsc]
  rw [← preimage_mul_ball_inter_H hs]
  refine ⟨?_, fun K hKc hKU => ?_⟩
  · rw [Measure.map_apply hm ((measurableSet_ball.inter isOpen_H.measurableSet).preimage
      (measurable_const_mul _)).compl, preimage_compl, hpre]
    exact h0
  · rw [Measure.map_apply hm hKc.measurableSet]
    have he : (fun z : ℂ => z / (s : ℂ)) ⁻¹' K = (fun z => (s : ℂ) * z) '' K := by
      ext z; constructor
      · intro hz; exact ⟨z / s, hz, mul_div_cancel₀ _ hsc⟩
      · rintro ⟨w, hw, rfl⟩; show (s : ℂ) * w / s ∈ K; rwa [mul_div_cancel_left₀ _ hsc]
    rw [he]
    refine hK _ (hKc.image (continuous_const.mul continuous_id)) ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hKU hw

/-- **The dilation event forces the canonical local limit.** -/
theorem dil_of_dilGood {γ : ℝ} {Z : FieldSample} {r s : ℝ} (hs : 0 < s) {μ : Measure ℂ}
    (hμ : IsVagueLimitOn (ball 0 r ∩ H) (areaApprox γ Z) μ) (h : DilGood γ Z r s) :
    IsVagueLimitOn (ball 0 (r / s) ∩ H) (areaApprox γ (rescale Z (Qc γ) s))
      (μ.map fun z => z / (s : ℂ)) := by
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  obtain ⟨hA, hC⟩ := h
  obtain ⟨μc, hμc⟩ := exists_vague_of_goodA hA
  obtain ⟨h0, hK⟩ := map_div_facts hs hμ.1 hμ.2.1
  have hmeq : μc = μ.map fun z => z / (s : ℂ) := by
    refine VagueOpen.eq_of_integral_cutoff_eq (isOpen_ball.inter isOpen_H) inter_subset_right
      (continuous_hbCut _) (hbCut_nonneg _) (hbCut_le_one _) (tsupport_hbCut _)
      (fun K hK hKU => hbCut_eventually_one hK hKU) famF_dense hμc.1 h0 hμc.2.1 hK
      fun n g hg => ?_
    obtain ⟨l, h1, h2⟩ := hC n g hg
    obtain ⟨hgc, hgs, -⟩ := famF_dense.1 g hg
    have hFc : Continuous fun z => hbCut (r / s) n z * g z := (continuous_hbCut _ n).mul hgc
    have hFs : HasCompactSupport fun z => hbCut (r / s) n z * g z := hgs.mul_left
    have hFU : tsupport (fun z => hbCut (r / s) n z * g z) ⊆ ball 0 (r / s) ∩ H :=
      (tsupport_mul_subset_left).trans (tsupport_hbCut _ n)
    have hmd : Measurable fun z : ℂ => z / (s : ℂ) := measurable_id.div_const _
    rw [integral_map hmd.aemeasurable hFc.aestronglyMeasurable,
      tendsto_nhds_unique (hμc.2.2 _ hFc hFs hFU) h1]
    -- the pulled-back test function
    set h' : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (s : ℂ) hsc
    have hsymm : ∀ z, h'.symm z = z / s := fun z => by simp [h', div_eq_inv_mul]
    have hGc : Continuous fun z => hbCut (r / s) n (z / s) * g (z / s) :=
      hFc.comp (continuous_id.div_const _)
    have hGe : (fun z => hbCut (r / s) n (z / s) * g (z / s)) =
        (fun z => hbCut (r / s) n z * g z) ∘ h'.symm := funext fun z => by simp [hsymm]
    have hGs : HasCompactSupport fun z => hbCut (r / s) n (z / s) * g (z / s) :=
      hGe ▸ hFs.comp_homeomorph h'.symm
    have hGU : tsupport (fun z => hbCut (r / s) n (z / s) * g (z / s)) ⊆ ball 0 r ∩ H := by
      intro w hw
      rw [hGe, tsupport_comp_eq_preimage] at hw
      have hw' := hFU hw
      rw [hsymm, ← preimage_mul_ball_inter_H hs] at hw'
      simpa [mul_div_cancel₀ _ hsc] using hw'
    exact tendsto_nhds_unique h2 (hμ.2.2 _ hGc hGs hGU)
  rw [← hmeq]
  exact hμc

end Prop16Lit
end QuantumZipper
