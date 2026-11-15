/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLwShift
import InteractingSLE.Spec.Supplement.RLCHG2aWire
import InteractingSLE.Foundations.Loewner.YuanTrace

/-!
# The relative upper curve's pathwise regularity

Packet PROVE-T14-SBLEAVES2. `Lw.erasureStep_of_link_shift` needs, of SB2(1)'s relative upper curve `ηr` (a flow line of
the conditional field, `Lv.HasRelStageOrdering`), five pathwise facts: continuity on its range, its start, values in
`ℍ̄`, dense interior times and transience at infinite lifetime. `ae_flowLine_regular` gives all five almost surely for
every flow line, from its generating trace (`IsFlowLine`'s last clause) and Theorem 1.3's transience (transferred by
uniqueness of the generating trace, `IsGeneratingTrace.eq_of_le`, as in `RLC.ae_tendsto_norm_of_thm13`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Lw

/-- **Pathwise regularity of a flow line**, almost surely: continuous on its available range, started at its seed,
in `ℍ̄`, with dense interior times, and transient at infinite lifetime (Theorem 1.3). -/
theorem ae_flowLine_regular (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} {x θ : ℝ} {S : Type u} [MeasurableSpace S] {Q : Measure S}
    [IsProbabilityMeasure Q] {h : S → LQGMetric.DistOn upperHalfPlaneOpens} {α : S → ℝ≥0 → ℂ}
    {ζ : S → ℝ≥0∞} (hfl : IsFlowLine κ b J x θ Q h α ζ) :
    ∀ᵐ ω ∂Q, ContinuousOn (α ω) {t | (t : ℝ≥0∞) ≤ ζ ω} ∧ α ω 0 = x ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ ω → 0 ≤ (α ω s).im) ∧
      (∀ a c : ℝ≥0, a < c → (c : ℝ≥0∞) ≤ ζ ω → ∃ s ∈ Ioo a c, α ω s ∈ H) ∧
      (ζ ω = ⊤ → Tendsto (fun t => ‖α ω t‖) atTop atTop) := by
  rcases hfl with ⟨h', 𝓕, W, VL, VR, B, _htranslate, hopt, hgen⟩
  have hevol := hopt.1
  have h13ae := h13 hκ (Theorem15.isOrderedForceWord_flowLine b J x) hevol
  filter_upwards [h13ae, hgen, hevol.2.2.2.2] with ω h13ω hgenω hpath
  have hw := hpath.2.2.2.1
  have hw0 := hpath.1
  have hcont : ContinuousOn (α ω) {t | (t : ℝ≥0∞) ≤ ζ ω} := by
    refine (hgenω.2.1.add (continuousOn_const (c := (x : ℂ)))).congr fun t _ => ?_
    simp only [Pi.add_apply, sub_add_cancel]
  have h0 : α ω 0 = x := by
    have := hgenω.1
    exact sub_eq_zero.1 this
  have hdense : ∀ a c : ℝ≥0, a < c → (c : ℝ≥0∞) ≤ ζ ω → ∃ s ∈ Ioo a c, α ω s ∈ H := fun a c hac hc =>
    Restart.IsGeneratingTrace.exists_mem_H_add hgenω hw hw0 hac hc
  have hlt : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω → 0 ≤ (α ω s).im := by
    intro s hs
    have h1 := Restart.IsGeneratingTrace.mem_closure_self hgenω hw hw0 hs
    have h2 : α ω s - x ∈ Hbar := by
      rw [← closure_H]; exact closure_mono sdiff_subset h1
    have h3 : 0 ≤ (α ω s - x).im := h2
    simpa using h3
  refine ⟨hcont, h0, fun s hs => ?_, hdense, fun hζ => ?_⟩
  · rcases hs.lt_or_eq with hs' | hs'
    · exact hlt s hs'
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs0 | hs0
    · rw [← hs0, h0]; simp
    have : NeBot (𝓝[<] s) := nhdsLT_neBot_of_exists_lt ⟨0, hs0⟩
    have hsub : Iio s ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ ω} := fun t ht =>
      (ENNReal.coe_le_coe.2 (le_of_lt ht)).trans hs
    have hlim : Tendsto (fun t => (α ω t).im) (𝓝[<] s) (𝓝 (α ω s).im) :=
      (Complex.continuous_im.tendsto _).comp ((hcont s hs).tendsto.mono_left (nhdsWithin_mono _ hsub))
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hlt t (hs' ▸ ENNReal.coe_lt_coe.2 ht)
  · rcases h13ω.2 with ⟨γ, hγ, hγtrans⟩
    have hγeq : ∀ t : ℝ≥0, γ t = α ω t - (x : ℂ) := fun t =>
      IsGeneratingTrace.eq_of_le hγ hgenω hw hw0 (by rw [hζ]; exact le_top)
    have hshift : Tendsto (fun t : ℝ≥0 => ‖α ω t - (x : ℂ)‖) atTop atTop := by
      simpa only [← hγeq] using hγtrans hζ
    refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-‖(x : ℂ)‖) hshift)
    have := norm_sub_le (α ω t) (x : ℂ)
    show ‖α ω t - x‖ + -‖(x : ℂ)‖ ≤ ‖α ω t‖
    linarith

end InteractingSLE.Theorem14.SB.Lw
