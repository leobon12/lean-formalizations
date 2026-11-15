/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6SourceCPrefixes

/-!
# Measurable GB6 relative coordinates from the original trace hypotheses

The original source traces need not be measurable, and the flow driver need
only be continuous before its lifetime. Measurable versions, contact events
and rational physical prefixes instantiate the proved relative-driver atlas.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.SourceC

open RelDrv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The relative-driver part of the source version construction, with a
positive measurable life and all-sample local path regularity. -/
structure RelativeDriverCoordinates (s : ℝ≥0) (P : Measure Ω)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞) : Prop where
  measurable : ∀ t, Measurable (D t)
  life_measurable : Measurable L
  life_pos : ∀ ω, 0 < L ω
  continuous : ∀ ω, ContinuousOn (D · ω) {u | (u : ℝ≥0∞) < L ω}
  zero : ∀ ω, D 0 ω = 0
  adapted : AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) L D
  relative : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
    (∀ u : ℝ≥0, (u : ℝ≥0∞) < L ω → ∃ t : ℝ≥0,
      (t : ℝ≥0∞) < gb6Tc s γ α ω ∧ (u : ℝ) < gb6Clock s W Wα ω t) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
      0 ≤ gb6Clock s W Wα ω t ∧ ENNReal.ofReal (gb6Clock s W Wα ω t) < L ω ∧
      QuantumZipper.fwdHull (fun r : ℝ => D r.toNNReal ω) (gb6Clock s W Wα ω t) =
        relMap (fun r : ℝ => Wα r.toNNReal ω) s ''
          QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t

/-- Source adaptation and a.e. generating traces supply the full measurable
relative driver. There is no gauge or stopping-rule hypothesis. -/
theorem exists_relative_driver {𝓕 𝓕α : Filtration ℝ≥0 mΩ}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hWa : AdaptedBefore 𝓕 ζ W) (hWαa : AdaptedBefore 𝓕α ζα Wα)
    (hcf : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ W 0 ω = 0 ∧ Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (hfl : ∀ᵐ ω ∂P, Wα 0 ω = 0 ∧ ContinuousOn (Wα · ω) {t | (t : ℝ≥0∞) < ζα ω} ∧
      IsGeneratingTrace (Wα · ω) (ζα ω) (α ω)) (s : ℝ≥0) (hs : 0 < s) :
    ∃ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞), RelativeDriverCoordinates s P W Wα ζα γ α D L := by
  classical
  obtain ⟨V, hVm, hVc, hV0, hVW⟩ := exists_top_driver_version hWa
    (hcf.mono fun ω hω => ⟨hω.1, hω.2.1, hω.2.2.1⟩)
  have hγV : ∀ᵐ ω ∂P, IsGeneratingTrace (V · ω) ⊤ (γ ω) := by
    filter_upwards [hcf, hVW] with ω hω he
    have he' : (V · ω) = (W · ω) := funext he
    rw [he']; exact hω.2.2.2
  obtain ⟨Γ, hΓc, hΓ0, hΓm, hΓγ⟩ := exists_top_trace_version hVm hVc hV0 hγV
  obtain ⟨U, A, hUm, hUc, hU0, hAc, hAm, -, hUA⟩ := exists_prefix_versions hWαa hfl s
  have hall : ∀ᵐ ω ∂P,
      (W 0 ω = 0 ∧ Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω)) ∧
      (Wα 0 ω = 0 ∧ ContinuousOn (Wα · ω) {t | (t : ℝ≥0∞) < ζα ω} ∧ IsGeneratingTrace (Wα · ω) (ζα ω) (α ω)) ∧
      (∀ t, V t ω = W t ω) ∧ Γ ω = γ ω ∧
      ((s : ℝ≥0∞) < ζα ω → (∀ t ≤ s, U t ω = Wα t ω) ∧ ∀ t, A ω t = α ω (min t s)) := by
    filter_upwards [hcf, hfl, hVW, hΓγ, hUA] with ω hc hf he hg hu
    exact ⟨hc.2, hf, he, hg, hu⟩
  obtain ⟨G, hGm, hGae, hG⟩ := exists_measurable_good hall
  have hsm : MeasurableSet {ω | (s : ℝ≥0∞) < ζα ω} := by
    have h := hWαa s univ MeasurableSet.univ
    simp only [mem_univ, and_true] at h
    exact 𝓕α.le s _ h
  let M : Set Ω := G ∩ {ω | (s : ℝ≥0∞) < ζα ω}
  have hMm : MeasurableSet M := hGm.inter hsm
  let Tc : Ω → ℝ≥0∞ := gb6Tc s Γ A
  obtain ⟨T, hT, hcover⟩ := exists_prefix_times
  let E : ℕ → Set Ω := fun n => M ∩ {ω | (T n : ℝ≥0∞) < Tc ω}
  have hEm : ∀ n, MeasurableSet (E n) := fun n => hMm.inter
    (measurableSet_lt_firstContactTime hΓc hAc hΓm hAm (T n) s)
  have hpre : ∀ ω ∈ M, (∀ t ≤ s, U t ω = Wα t ω) ∧ (∀ t ≤ s, A ω t = α ω t) := by
    intro ω hω
    obtain ⟨hu, ha⟩ := (hG ω hω.1).2.2.2.2 hω.2
    exact ⟨hu, fun t ht => by rw [ha t, min_eq_left ht]⟩
  have hTc : ∀ ω ∈ M, Tc ω = gb6Tc s γ α ω := by
    intro ω hω
    dsimp only [Tc, gb6Tc]
    rw [(hG ω hω.1).2.2.2.1]
    exact firstContactTime_eq_of_prefix_eq (hpre ω hω).2
  have hgeom : ∀ n ω, ω ∈ E n → Continuous (V · ω) ∧ V 0 ω = 0 ∧
      IsGeneratingTrace (V · ω) ⊤ (Γ ω) ∧ ∃ p : ℂ,
      Tendsto (QuantumZipper.fwdMapInv (Ito.rpath (U · ω)) s) (𝓝[H] 0) (𝓝 p) ∧
      Disjoint (closure (QuantumZipper.fwdHull (Ito.rpath (U · ω)) s))
        (closure ((fun z : ℂ => -z⁻¹) '' QuantumZipper.fwdHull (Ito.rpath (V · ω)) (T n))) := by
    intro n ω hω
    obtain ⟨hc, hf, hv, hg, -⟩ := hG ω hω.1.1
    have hp := hpre ω hω.1
    have hce : (V · ω) = (W · ω) := funext hv
    have hchart := chart_prefix_eq hf.2.1 hf.1 (hUc ω) (hU0 ω) hω.1.2 hp.1
    refine ⟨hVc ω, hV0 ω, ?_, α ω s, ?_, ?_⟩
    · rw [hg, hce]; exact hc.2.2
    · have htip := IsGeneratingTrace.tendsto_fwdMapInv_tip hf.2.2 hf.2.1 hf.1 hω.1.2
      have hH : ∀ᶠ z : ℂ in 𝓝[H] 0, z ∈ H := self_mem_nhdsWithin
      exact htip.congr' (hH.mono fun z hz => (hchart.2 z hz).symm)
    · have ht : (T n : ℝ≥0∞) < gb6Tc s γ α ω := (hTc ω hω.1) ▸ hω.2
      have hd := disjoint_closure_fwdHull_of_lt_firstContactTime hf.2.2 hf.2.1 hf.1
        hc.2.2 hc.2.1.continuousOn hc.1 hω.1.2 ENNReal.coe_lt_top ht
      rw [hchart.1, hce]
      exact hd
  obtain ⟨D, L, hDm, hLm, hDc, hD0, -, hcov, hK⟩ :=
    CoordB.exists_measurable_driver_of_separated_prefixes hUm hUc hU0 hΓm hs hEm hT hgeom
  let D' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ M then D t ω else 0
  let L' : Ω → ℝ≥0∞ := fun ω => if ω ∈ M then L ω else ⊤
  have hD'm : ∀ t, Measurable (D' t) := fun t => Measurable.ite hMm (hDm t) measurable_const
  have hL'm : Measurable L' := Measurable.ite hMm hLm measurable_const
  refine ⟨D', L', ⟨hD'm, hL'm, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro ω
    by_cases hω : ω ∈ M
    · have hpos : 0 < Tc ω := by
        have h := firstContactTime_pos (hΓc ω).continuousAt (hΓ0 ω)
          ((isCompact_Icc (a := (0 : ℝ≥0)) (b := s)).image (hAc ω)).isBounded
        simpa only [Tc, gb6Tc, image_image, Function.comp_def] using h
      obtain ⟨n, -, hn⟩ := hcover (Tc ω) 0 (by simpa only [ENNReal.coe_zero] using hpos)
      have hKn := (hK n ω ⟨hω, hn⟩ 0 (hT n)).2.1
      exact (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal _ from zero_le).trans_lt
        (by simpa only [L', hω, ↓reduceIte] using hKn)
    · simp only [L', hω, ↓reduceIte]; exact ENNReal.zero_lt_top
  · intro ω
    by_cases hω : ω ∈ M
    · simpa only [D', L', hω, ↓reduceIte] using hDc ω
    · simp only [D', L', hω, ↓reduceIte]
      exact continuous_const.continuousOn
  · intro ω
    by_cases hω : ω ∈ M
    · simpa only [D', hω, ↓reduceIte] using hD0 ω
    · simp only [D', hω, ↓reduceIte]
  · intro t B hB
    exact (measurableSet_lt measurable_const hL'm).inter (hD'm t hB)
  · filter_upwards [hGae] with ω hω hsω _
    have hM : ω ∈ M := ⟨hω, hsω⟩
    have hUeq : ∀ r ∈ Icc (0 : ℝ) s, Ito.rpath (U · ω) r = Wα r.toNNReal ω :=
      fun r hr => (hpre ω hM).1 _ (Real.toNNReal_le_iff_le_coe.2 hr.2)
    have hveq : (V · ω) = (W · ω) := funext (hG ω hω).2.2.1
    have hclock : relClock (Ito.rpath (U · ω)) s (Ito.rpath (V · ω)) =
        relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) := by
      rw [hveq]
      exact relClock_eq_of_eqOn s.coe_nonneg hUeq _
    have hmap := relMap_eq_of_eqOn s.coe_nonneg hUeq
    refine ⟨?_, fun t ht => ?_⟩
    · intro u hu
      have huL : (u : ℝ≥0∞) < L ω := by simpa only [L', hM, ↓reduceIte] using hu
      obtain ⟨n, hn, t, ht, hut⟩ := hcov ω u huL
      refine ⟨t, ?_, ?_⟩
      · exact (ENNReal.coe_lt_coe.2 ht).trans ((hTc ω hM) ▸ hn.2)
      · simpa only [gb6Clock, ← hclock] using hut
    · have htTc : (t : ℝ≥0∞) < Tc ω := (hTc ω hM).symm ▸ ht
      obtain ⟨n, htn, hn⟩ := hcover (Tc ω) t htTc
      have hkt := hK n ω ⟨hM, hn⟩ t htn
      rw [hclock, hmap] at hkt
      rw [hveq] at hkt
      simp only [L', D', hM, ↓reduceIte, gb6Clock]
      exact hkt

end InteractingSLE.Supp8.GB6.SourceC
