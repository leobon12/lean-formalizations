/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9BW4
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Spec.Theorem15Inputs
import QuantumZipper.Proofs.RS.KoebeLoewnerTime
import QuantumZipper.Proofs.Thm18.R18RTMaskNeg

/-!
# Supplement §9, Lemma W4: Loewner slits of flow-line prefixes, and W4 on the frozen carriers

Packet PROVE-SUPP9-C.

* `exists_isSlitCompletion_of_isGeneratingTrace`: a prefix `η([0, b])`, `b < T`, of an injective continuous generating
  trace of a continuous driver has a slit completion: follow `η` to `b`, then the image `F_b(i s)` of the vertical ray
  under the inverse mapping-out function at time `b` (the "inverse image of a vertical ray in the one-path half-plane
  chart", supplement p. 506). It is continuous at `b` because `F_b(w) → η(b)` as `w → 0` (O3, TraceBridge), injective
  because `F_b` is, proper because `F_b(w) − w` is bounded, and its new points lie in `ℍ \ K_b`, off `η([0, b])`.
* `ae_forall_exists_isSlitCompletion_of_isFlowLine`: almost surely every available prefix of a flow line has a slit
  completion (injectivity from Aux. lemma 25).
* `w4Statement_of_inputs`: **Lemma W4 on the frozen carriers** (`Supp9.W4Statement`) from Aux. lemma 25 and the
  deterministic tip-access input `W4TipAccessStatement`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMapInv)

universe u

namespace InteractingSLE

namespace Supp9B

/-! ### The Loewner slit of a generating trace -/

section Slit

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The Loewner slit.** -/
theorem exists_isSlitCompletion_of_isGeneratingTrace (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ T})
    {b : ℝ≥0} (hb : (b : ℝ≥0∞) < T) : ∃ S, IsSlitCompletion η b S := by
  obtain ⟨t₂, hbt₂, ht₂T⟩ := exists_real_btwn_of_lt hb
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg b).trans hbt₂.le
  set W₂ := frozenDrive w t₂ with hW₂
  have hW₂c : Continuous W₂ := continuous_frozenDrive_of_lt hw ht₂T
  have hW₂0 : W₂ 0 = 0 := by rw [hW₂, frozenDrive_zero ht₂, hw0]
  have hb0 : (0 : ℝ) ≤ b := NNReal.coe_nonneg b
  have heq : ∀ r ∈ Icc (0 : ℝ) t₂, (fun s : ℝ => w s.toNNReal) r = W₂ r := fun r hr =>
    (frozenDrive_eq hr).symm
  set F := fwdMapInv (fun s : ℝ => w s.toNNReal) b with hF
  have hFeq : F = fwdMapInv W₂ b := fwdMapInv_eq_of_eqOn hb0 hbt₂ heq
  have hKeq : fwdHull (fun s : ℝ => w s.toNNReal) b = fwdHull W₂ b := fwdHull_eq_of_eqOn hb0 hbt₂ heq
  have hFH : ∀ z ∈ H, F z ∈ H \ fwdHull W₂ b := fun z hz => by
    rw [hFeq]; exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW₂c hW₂0 hb0 hz
  have hFi : InjOn F H := by rw [hFeq]; exact QuantumZipper.RS.injOn_fwdMapInv_H hW₂c hW₂0 hb0
  have hFc : ContinuousOn F H := by
    rw [hFeq]; exact (QuantumZipper.RS.differentiableOn_fwdMapInv hW₂c hW₂0 hb0).continuousOn
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ H, ‖F z - z‖ ≤ C := by
    rw [hFeq]; exact QuantumZipper.R18.exists_norm_fwdMapInv_sub_le hW₂c hW₂0 hb0
  have htip : Tendsto F (𝓝[H] 0) (𝓝 (η b)) := hη.tendsto_fwdMapInv_tip hw hw0 hb
  -- the filling of the prefix avoids `ℍ \ K_b`
  have hfill := hη.2.2 b hb
  have hoff : ∀ z ∈ H \ fwdHull W₂ b, z ∉ η '' Icc 0 b := by
    intro z hz hzA
    obtain ⟨z₀, -, hz₀⟩ := hfill.1
    have hz' : z ∈ H \ fwdHull (fun s : ℝ => w s.toNNReal) b := by rw [hKeq]; exact hz
    rw [← hz₀] at hz'
    exact (connectedComponentIn_subset _ _ hz').2 hzA
  -- the prefix lies in the closed upper half-plane
  have hHbar : ∀ t ≤ b, η t ∈ Hbar := by
    intro t ht
    have htT : (t : ℝ≥0∞) < T := lt_of_le_of_lt (by exact_mod_cast ht) hb
    have hlim := hη.tendsto_fwdMapInv_tip hw hw0 htT
    obtain ⟨t₃, htt₃, ht₃T⟩ := exists_real_btwn_of_lt htT
    have ht0 : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
    have heq₃ : ∀ r ∈ Icc (0 : ℝ) t₃, (fun s : ℝ => w s.toNNReal) r = frozenDrive w t₃ r := fun r hr =>
      (frozenDrive_eq hr).symm
    have hW₃c : Continuous (frozenDrive w t₃) := continuous_frozenDrive_of_lt hw ht₃T
    have hW₃0 : frozenDrive w t₃ 0 = 0 := by
      rw [frozenDrive_zero (ht0.trans htt₃.le), hw0]
    have hev : ∀ᶠ z in 𝓝[H] (0 : ℂ), fwdMapInv (fun s : ℝ => w s.toNNReal) t z ∈ Hbar := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [fwdMapInv_eq_of_eqOn ht0 htt₃ heq₃]
      exact QuantumZipper.H_subset_Hbar (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW₃c hW₃0 ht0 hz).1
    have hne : (𝓝[H] (0 : ℂ)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]
      show (0 : ℝ) ≤ (0 : ℂ).im; simp
    exact QuantumZipper.isClosed_Hbar.mem_of_tendsto hlim hev
  -- the vertical ray
  set ray : ℝ≥0 → ℂ := fun s => ((s : ℝ) : ℂ) * I with hray
  have hrayH : ∀ s, 0 < s → ray s ∈ H := fun s hs => by
    show 0 < (((s : ℝ) : ℂ) * I).im; simpa using hs
  set S : ℝ≥0 → ℂ := fun t => if t ≤ b then η t else F (ray (t - b)) with hS
  have hSle : ∀ t ≤ b, S t = η t := fun t ht => by simp only [hS, ht, ↓reduceIte]
  have hSgt : ∀ t, b < t → S t = F (ray (t - b)) := fun t ht => by
    simp only [hS, not_le.2 ht, ↓reduceIte]
  have hSH : ∀ t, b < t → S t ∈ H \ fwdHull W₂ b := fun t ht => by
    rw [hSgt t ht]; exact hFH _ (hrayH _ (tsub_pos_of_lt ht))
  -- continuity
  have hηc : ContinuousOn η {t | (t : ℝ≥0∞) ≤ T} := hη.2.1
  have hrayc : Continuous ray := by rw [hray]; fun_prop
  have hSc : Continuous S := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    rcases lt_trichotomy t b with htb | rfl | htb
    · have hn : Iio b ∈ 𝓝 t := isOpen_Iio.mem_nhds htb
      have hTn : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T} ∈ 𝓝 t := by
        refine mem_of_superset ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds
          (show (t : ℝ≥0∞) < T from lt_trans (by exact_mod_cast htb) hb)) fun s (hs : (s : ℝ≥0∞) < T) =>
          show (s : ℝ≥0∞) ≤ T from le_of_lt hs
      exact ((hηc.continuousAt hTn).congr (mem_of_superset hn fun s hs => (hSle s (le_of_lt hs)).symm))
    · -- at the junction
      have hTn : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T} ∈ 𝓝 t := by
        refine mem_of_superset ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hb)
          fun s (hs : (s : ℝ≥0∞) < T) => show (s : ℝ≥0∞) ≤ T from le_of_lt hs
      have hl : ContinuousWithinAt S (Iic t) t :=
        ((hηc.continuousAt hTn).continuousWithinAt).congr (fun s hs => hSle s hs) (hSle t le_rfl)
      have hr : ContinuousWithinAt S (Ioi t) t := by
        rw [ContinuousWithinAt, hSle t le_rfl]
        have h1 : Tendsto (fun s : ℝ≥0 => ray (s - t)) (𝓝[>] t) (𝓝[H] 0) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
          · have : Tendsto (fun s : ℝ≥0 => ray (s - t)) (𝓝 t) (𝓝 (ray (t - t))) :=
              (hrayc.comp (continuous_id.sub continuous_const)).tendsto t
            simpa [hray] using this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with s hs using hrayH _ (tsub_pos_of_lt hs)
        refine (htip.comp h1).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs using (hSgt s hs).symm
      exact continuousAt_iff_continuous_left_right.2 ⟨hl, continuousWithinAt_Ioi_iff_Ici.1 hr⟩
    · have hn : Ioi b ∈ 𝓝 t := isOpen_Ioi.mem_nhds htb
      have hcF : ContinuousAt (fun s => F (ray (s - b))) t := by
        have h1 : ContinuousAt (fun s : ℝ≥0 => ray (s - b)) t :=
          (hrayc.comp (continuous_id.sub continuous_const)).continuousAt
        exact ContinuousAt.comp (g := F)
          (hFc.continuousAt (QuantumZipper.isOpen_H.mem_nhds (hrayH _ (tsub_pos_of_lt htb)))) h1
      exact hcF.congr (mem_of_superset hn fun s hs => (hSgt s hs).symm)
  -- injectivity
  have hSi : Function.Injective S := by
    intro t t' htt'
    have hbT : ∀ s ≤ b, s ∈ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T} := fun s hs =>
      show (s : ℝ≥0∞) ≤ T from (lt_of_le_of_lt (by exact_mod_cast hs) hb).le
    by_cases ht : t ≤ b <;> by_cases ht' : t' ≤ b
    · rw [hSle t ht, hSle t' ht'] at htt'; exact hinj (hbT t ht) (hbT t' ht') htt'
    · exfalso
      have h1 := hSH t' (not_le.1 ht')
      rw [← htt', hSle t ht] at h1
      exact hoff _ h1 ⟨t, ⟨zero_le, ht⟩, rfl⟩
    · exfalso
      have h1 := hSH t (not_le.1 ht)
      rw [htt', hSle t' ht'] at h1
      exact hoff _ h1 ⟨t', ⟨zero_le, ht'⟩, rfl⟩
    · rw [hSgt t (not_le.1 ht), hSgt t' (not_le.1 ht')] at htt'
      have h1 := hFi (hrayH _ (tsub_pos_of_lt (not_le.1 ht))) (hrayH _ (tsub_pos_of_lt (not_le.1 ht'))) htt'
      have h2 : t - b = t' - b := by
        have := congrArg Complex.im h1
        simp only [hray, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero, add_zero] at this
        exact NNReal.coe_injective (by simpa using this)
      exact (tsub_left_inj (not_le.1 ht).le (not_le.1 ht').le).1 h2
  -- properness
  have hSn : Tendsto (fun t => ‖S t‖) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun r => ⟨b + (r + C).toNNReal + 1, fun t ht => ?_⟩
    have hbt : b < t := lt_of_lt_of_le (lt_of_le_of_lt le_self_add (lt_add_one (b + (r + C).toNNReal))) ht
    rw [hSgt t hbt]
    have hz := hrayH _ (tsub_pos_of_lt hbt)
    have h1 := hC _ hz
    have h2 : ‖ray (t - b)‖ = ((t - b : ℝ≥0) : ℝ) := by simp [hray]
    have h3 : r + C ≤ ((t - b : ℝ≥0) : ℝ) := by
      have : b + (r + C).toNNReal ≤ t := le_trans le_self_add ht
      have h4 : (r + C).toNNReal ≤ t - b := le_tsub_of_add_le_left this
      exact (Real.le_coe_toNNReal _).trans (by exact_mod_cast h4)
    have h5 : ‖ray (t - b)‖ ≤ ‖F (ray (t - b))‖ + ‖F (ray (t - b)) - ray (t - b)‖ := by
      calc ‖ray (t - b)‖ = ‖F (ray (t - b)) - (F (ray (t - b)) - ray (t - b))‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  refine ⟨S, ⟨hSc, hSi, fun t => ?_, hSn, hSle⟩, fun t ht => ⟨(hSH t ht).1, hoff _ (hSH t ht)⟩⟩
  by_cases ht : t ≤ b
  · rw [hSle t ht]; exact hHbar t ht
  · exact (hSH t (not_le.1 ht)).1.le

end Slit

/-! ### Slits of flow lines; Lemma W4 on the frozen carriers -/

section FlowLine

/-- Translating a curve by a real number preserves slit completions. -/
theorem isSlitCompletion_add_real {γ S : ℝ≥0 → ℂ} {b : ℝ≥0} (h : IsSlitCompletion γ b S) (x : ℝ) :
    IsSlitCompletion (fun t => (x : ℂ) + γ t) b (fun t => (x : ℂ) + S t) := by
  obtain ⟨⟨hc, hi, him, hn, he⟩, hs⟩ := h
  refine ⟨⟨continuous_const.add hc, fun t t' h' => hi (add_left_cancel h'), fun t => by simpa using him t,
    ?_, fun t ht => by simp only [he t ht]⟩, fun t ht => ⟨by simpa using (hs t ht).1, ?_⟩⟩
  · refine tendsto_atTop_mono' atTop (Eventually.of_forall fun t => ?_)
      (tendsto_atTop_add_const_right atTop (-|x|) hn)
    have h1 : ‖S t‖ ≤ ‖(x : ℂ) + S t‖ + ‖(x : ℂ)‖ := by
      calc ‖S t‖ = ‖((x : ℂ) + S t) - (x : ℂ)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    show ‖S t‖ + -|x| ≤ ‖(x : ℂ) + S t‖
    linarith
  · rintro ⟨y, hy, hyt⟩
    exact (hs t ht).2 ⟨y, hy, add_left_cancel hyt⟩

/-- **Loewner slits of flow lines.** Almost surely every available prefix `η([0, c])`, `c < ζ`, of a flow line has
a slit completion (injectivity from Aux. lemma 25). -/
theorem ae_forall_exists_isSlitCompletion_of_isFlowLine (hA : Theorem15.Aux25Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ c : ℝ≥0, (c : ℝ≥0∞) < ζ ω → ∃ S, IsSlitCompletion (η ω) c S := by
  have hinj := Theorem15.ae_injOn_of_isFlowLine hA hκ hκ4 hη
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hcoup, htr⟩ := hη
  filter_upwards [hinj, htr, hcoup.1.2.2.2.2] with ω hωi hωt hωp
  intro c hc
  have hw : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := hωp.2.2.2.1
  have hw0 : W 0 ω = 0 := hωp.1
  have hinj' : InjOn (fun t => η ω t - x) {t | (t : ℝ≥0∞) ≤ ζ ω} := fun s hs t ht hst =>
    hωi hs ht (sub_left_inj.1 hst)
  obtain ⟨S, hS⟩ := exists_isSlitCompletion_of_isGeneratingTrace hωt hw hw0 hinj' hc
  have h1 := isSlitCompletion_add_real hS x
  have h2 : (fun t => (x : ℂ) + (η ω t - x)) = η ω := funext fun t => by ring
  rw [h2] at h1
  exact ⟨_, h1⟩

/-- **Lemma W4 on the frozen carriers** (`Supp9.W4Statement`, supplement p. 532), from Aux. lemma 25 and the
deterministic tip-access input `W4TipAccessStatement`. -/
theorem w4Statement_of_inputs (hA : Theorem15.Aux25Statement.{u}) (hND : W4TipAccessStatement) :
    Supp9.W4Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  filter_upwards [ae_forall_exists_isSlitCompletion_of_isFlowLine hA hκ hκ4 hη₁,
    ae_forall_exists_isSlitCompletion_of_isFlowLine hA hκ hκ4 hη₂, Supp9.ae_apply_zero_of_isFlowLine hη₁,
    Supp9.ae_apply_zero_of_isFlowLine hη₂] with ω h1 h2 h10 h20
  exact extendsWithoutNewContact_of_slits hND (by rw [h10]; simp) (by rw [h20]; simp)
    (by rw [h10, h20]; simpa using hx) h1 h2

end FlowLine

end Supp9B

end InteractingSLE
