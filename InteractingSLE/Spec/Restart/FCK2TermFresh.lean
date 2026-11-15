/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2TermZero

/-! # A fresh real endpoint is a new extreme and is accessed from its side -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Restart.FCPlumb
open MartChar.RealFlow FlowStopIdentLL

/-- The closed terminal tip belongs to the closure of every earlier active
Loewner domain. This follows directly from the terminal inverse-map limit. -/
theorem terminal_mem_closure_earlier_active {W : ℝ≥0 → ℝ} {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hg : IsGeneratingTrace W U γ) (hc : Continuous W) (h0 : W 0 = 0)
    {T : ℝ≥0} (hT : 0 < T) (hTU : (T : ℝ≥0∞) ≤ U) {q : ℝ≥0} (hq : q ≤ T) :
    γ T ∈ closure (H \ fwdHull (fun s : ℝ => W s.toNNReal) q) := by
  let D : ℝ → ℝ := fun s => W s.toNNReal
  have hD : Continuous D := hc.comp continuous_real_toNNReal
  have hD0 : D 0 = 0 := by simpa only [D, Real.toNNReal_zero] using h0
  obtain ⟨hB, htip⟩ := terminal_boundary_data hg hT hTU hD hD0
    (fun s _ => by simp only [D, Real.toNNReal_coe])
  have hNe : (𝓝[H] (0 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    exact show (0 : ℝ) ≤ (0 : ℂ).im by simp
  have hlim := hB.tendsto (show (0 : ℂ) ∈ Hbar by simp [Hbar])
  rw [htip] at hlim
  apply mem_closure_of_tendsto hlim
  apply eventually_nhdsWithin_of_forall
  intro z hz
  have hmem := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hD hD0 T.coe_nonneg hz
  exact ⟨hmem.1, fun hn => hmem.2 (QuantumZipper.fwdHull_mono.1 (by exact_mod_cast hq) hn)⟩

/-- A positive real endpoint of a simple generating trace is at least every
earlier real contact. The filled upper collar excludes a middle new contact. -/
theorem real_contacts_le_positive_endpoint {W : ℝ≥0 → ℝ} {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hg : IsGeneratingTrace W U γ) (hc : Continuous W) (h0 : W 0 = 0)
    (hi : InjOn γ {s | (s : ℝ≥0∞) ≤ U})
    {T : ℝ≥0} (hT : 0 < T) (hTU : (T : ℝ≥0∞) ≤ U) {X : ℝ}
    (hX : 0 < X) (hvis : γ T = X) :
    ∀ s ≤ T, (γ s).im = 0 → (γ s).re ≤ X := by
  intro s hs him
  rcases hs.lt_or_eq with hs | rfl
  · have hsU : (s : ℝ≥0∞) < U := (ENNReal.coe_lt_coe.2 hs).trans_le hTU
    let g : ℝ → ℂ := fun r => γ r.toNNReal
    have hgc : ContinuousOn g (Icc 0 (s : ℝ)) :=
      hg.2.1.comp continuous_real_toNNReal.continuousOn
        (fun r hr => (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans hsU.le)
    have hgH : MapsTo g (Icc 0 (s : ℝ)) Hbar := fun r hr =>
      Sec7.IsGeneratingTrace.mem_Hbar hg hc.continuousOn h0
        ((ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans hsU.le)
    have hnot : (X : ℂ) ∉ g '' Icc 0 (s : ℝ) := by
      rintro ⟨r, hr, he⟩
      have hru : (r.toNNReal : ℝ≥0∞) ≤ U :=
        (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans hsU.le
      have heq := hi hru hTU (he.trans hvis.symm)
      have hrs : r.toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.2 hr.2
      exact not_le_of_gt hs (heq ▸ hrs)
    have hHull : fwdHull (fun r : ℝ => W r.toNNReal) s = fillH (g '' Icc 0 (s : ℝ)) := by
      have h := hg.2.2 s hsU
      have hAc : IsCompact (γ '' Icc 0 s) :=
        isCompact_Icc.image_of_continuousOn (hg.2.1.mono
          (fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hsU.le))
      rw [isFilling_iff_inter_H_eq_fillH hAc.isBounded hAc.isClosed,
        inter_eq_left.2 ((QuantumZipper.fwdHull_mono (W := fun r : ℝ => W r.toNNReal)).2 _)] at h
      rw [h]
      congr 1
      ext z
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨r, ⟨by exact_mod_cast hr.1, by exact_mod_cast hr.2⟩,
          by simp only [g, Real.toNNReal_coe]⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨r.toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hr.2⟩, rfl⟩
    have hactive := terminal_mem_closure_earlier_active hg hc h0 hT hTU hs.le
    rw [hvis, hHull] at hactive
    have hex := Theorem14.GW1WalkExit.new_real_contact_is_extreme hgc hgH
      (u := 0) (v := s) (L := 0) (R := (γ s).re) ⟨le_rfl, s.coe_nonneg⟩
      ⟨s.coe_nonneg, le_rfl⟩ (by simp only [g, Real.toNNReal_zero, hg.1, ofReal_zero])
      (by simp only [g, Real.toNNReal_coe]; exact (Sec7.SideHeightBox.ofReal_re_of_im him).symm)
      hnot hactive
    exact le_of_lt (hex.resolve_left (not_lt_of_ge hX.le))
  · simpa only [hvis, Complex.ofReal_re] using (le_rfl : X ≤ X)

/-- The zero right image collides at a positive real endpoint of a simple
generating trace, even when the endpoint is the finite lifetime. -/
theorem zero_right_collision_of_simple_real_endpoint {W : ℝ≥0 → ℝ}
    {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ} (hg : IsGeneratingTrace W U γ)
    (hc : Continuous W) (h0 : W 0 = 0) (hi : InjOn γ {s | (s : ℝ≥0∞) ≤ U})
    {T : ℝ≥0} (hT : 0 < T) (hTU : (T : ℝ≥0∞) ≤ U) {X : ℝ}
    (hX : 0 < X) (hvis : γ T = X) :
    rightImg (fun s : ℝ => W s.toNNReal) 0 T = W T := by
  have hmax := real_contacts_le_positive_endpoint hg hc h0 hi hT hTU hX hvis
  have hal : ∀ t : ℝ≥0, t < T → Alive (fun r : ℝ => W r.toNNReal) X t := by
    intro t ht
    apply alive_of_trace_off_global hg hc h0 ((ENNReal.coe_lt_coe.2 ht).trans_le hTU) hX
    intro s hs y hy he
    have hsr := hmax s (hs.trans ht.le) (by rw [he]; simp)
    have hyX : y = X := le_antisymm (by simpa only [he, Complex.ofReal_re] using hsr) hy
    have hsU : (s : ℝ≥0∞) ≤ U := (ENNReal.coe_le_coe.2 (hs.trans ht.le)).trans hTU
    have heq := hi hsU hTU (by rw [he, hyX, hvis])
    exact not_le_of_gt ht (heq ▸ hs)
  have hz := zero_right_collision_of_first_swallow (D := fun r : ℝ => W r.toNNReal)
    (hc.comp continuous_real_toNNReal)
    hX.le (NNReal.coe_pos.2 hT)
    (fun t ht0 htT => by
      have ht' : t.toNNReal < T := (Real.toNNReal_lt_iff_lt_coe ht0).2 htT
      simpa only [Real.coe_toNNReal t ht0] using hal t.toNNReal ht')
    (not_alive_of_closed_real_visit hg hc h0 hT hTU hvis)
  simpa only [Real.toNNReal_coe] using hz

end InteractingSLE.Restart.FCPlumb
