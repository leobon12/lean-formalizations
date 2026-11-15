/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop420ThreeEntr
import InteractingSLE.WangWu.Prop421Seed
import InteractingSLE.WangWu.ImgChartConstMarks
import InteractingSLE.Spec.Sec7.Lemma71GFlow

/-!
# Wang–Wu at `κ = 4`: every nonnegative seed line has Lemma 6.2's hypotheses

Packet PROVE-WW-B22. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Proposition 4.20
(text dump L1701–1745): "The single-line determinism proved in Proposition 4.18 and Lemma 4.5 give locality. […] If
either line is stopped in the filtration enlarged by the other line, the same rule holds on all exposed sides. The
statement also holds for three ordered seed lines, one of which may be stopped in the filtration enlarged by the other
two."

Exposing complete seed lines and a stopped one (Lemma 4.5 = the specification's Lemma 6.2, landed as
`Sec6.Three.ae_condExp_exp_eq_three_of_tendsto` and `Sec7.Lemma71L.ae_condExp_exp_eq_three_of_le_aeSigma`) needs, for
each
curve, Lemma 6.2's hypotheses `Sec7.Lemma71G.IsLemma62Curve`: a version continuous for every `ω`, started at `0`, in
`ℍ̄`, measurable at each time, determined by the field, history-sensitively local at first entrance times, transient.

**`SeedField.exists_lemma62Version_seed`** proves them for the seed line of every optional hull coupling of a
nonnegative two-seed word `(ρL − c/λ; ρR + c/λ)` with the field `h + c` (`Exist.flowField 0 c h`), for the common
centred field `h − u₀`:
* field determination: the contact step of Proposition 4.18 (`reverseTipContactStatement`, B19) gives a
  field-determined history for every such coupling (`twoSeed_of_nonneg_of_contact`), hence a Borel function of `h + c`
  for the trace (`LP.exists_measurable_lifetime_trace_eq_comp_field_of_isFieldDeterminedHistory`), and `h + c` is a
  Borel function of `h − u₀`;
* locality: `WholeField.isEntranceKilledHistoryLocal_of_translate` (Aux. lemma 56 at first entrance times for a line of
  `h(· + 0) + c`, `κ ≤ 4`) for each capped path, then `Sec7.Lemma71G.isEntranceHistoryLocal_of_capAt`;
* the trace, its infinite lifetime and transience: `IsMarkedChain.ae_seedLine` (nonnegative cumulative weights).

This is the `κ = 4` counterpart of `Sec7.Lemma71G.exists_lemma62Version` (flow lines, `κ < 4`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.SeedField

open Sec7.Lemma71G (IsLemma62Curve)

/-- **The seed line of a nonnegative `κ = 4` two-seed coupling of `h + c` has Lemma 6.2's hypotheses for `h − u₀`.**
There is a path `η` which is continuous for every `ω`, starts at `0`, takes values in `ℍ̄`, is measurable at each time
and determined by the centred field `h − u₀`, has the history-sensitive locality at first entrance times for `h − u₀`,
and is transient; almost surely the lifetime is infinite, `η` is the seed line on `[0, ∞)`, and the seed line is a
simple proper arc. -/
theorem exists_lemma62Version_seed {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {rL rR c : ℝ} (hL : 0 ≤ rL - c / wwLambda)
    (hR : 0 ≤ rR + c / wwLambda) {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - c / wwLambda)
      (fun _ => rR + c / wwLambda) P 𝓕 W VL VR B ζ (fun ω => Exist.flowField 0 c (h ω)))
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) :
    ∃ η : Ω → ℝ≥0 → ℂ, IsLemma62Curve η (WholeField.centredField h u₀) P ∧
      ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, η ω t = seedLine ζ W ω t) ∧ IsProperArc (seedLine ζ W ω) := by
  classical
  have hseed := IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1
  -- field determination of the history (contact step), and a Borel trace map
  have hdet := (twoSeed_of_nonneg_of_contact.{u, 0} reverseTipContactStatement.{0} hL hR).1 P 𝓕 W VL VR B ζ
    (fun ω => Exist.flowField 0 c (h ω)) hC
  obtain ⟨Φ, hΦm, hΦ⟩ := LP.exists_measurable_lifetime_trace_eq_comp_field_of_isFieldDeterminedHistory hC hdet
  -- the good event
  set good : Ω → Prop := fun ω => ζ ω = ⊤ ∧ IsProperArc (seedLine ζ W ω) ∧
    IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t : ℝ≥0 => seedLine ζ W ω t) ∧
    ∀ t : ℝ≥0, (Φ (Exist.flowField 0 c (h ω))).2 t = seedLine ζ W ω t with hgooddef
  have hgood : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hseed, hΦ] with ω hs hΦω
    obtain ⟨hζ, ⟨η, hη, heq⟩, -, harc, -⟩ := hs
    have hfun : (fun t : ℝ≥0 => seedLine ζ W ω t) = η := by
      funext t
      rw [heq]
      exact congrArg η (Real.toNNReal_coe (r := t))
    have hη' : IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t : ℝ≥0 => seedLine ζ W ω t) := by
      rw [hfun, hζ]
      exact hη
    refine ⟨hζ, harc, hη', fun t => ?_⟩
    rw [hΦω.2 _ hη' t, hζ, min_eq_left le_top, ENNReal.toNNReal_coe]
  set G : Set Ω := (toMeasurable P {ω | ¬ good ω})ᶜ with hGdef
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGg : ∀ ω ∈ G, good ω := fun ω hω => by
    by_contra hng
    exact hω (subset_toMeasurable _ _ hng)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    have e : {ω | ¬ ω ∈ G} = toMeasurable P {ω | ¬ good ω} := by ext ω; simp [hGdef]
    rw [e, measure_toMeasurable]
    exact ae_iff.1 hgood
  set η' : Ω → ℝ≥0 → ℂ := fun ω t => if ω ∈ G then seedLine ζ W ω t else 0 with hη'def
  have hη'G : ∀ ω ∈ G, η' ω = fun t : ℝ≥0 => seedLine ζ W ω t := fun ω hω => funext fun t => by
    simp only [hη'def, hω, ↓reduceIte]
  have hη'nG : ∀ ω ∉ G, η' ω = fun _ => 0 := fun ω hω => funext fun t => by
    simp only [hη'def, hω, ↓reduceIte]
  have hc : ∀ ω, Continuous (η' ω) := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hη'G ω hω]
      exact (hGg ω hω).2.1.cont.comp_continuous NNReal.continuous_coe fun t => t.2
    · rw [hη'nG ω hω]; exact continuous_const
  have h0 : ∀ ω, η' ω 0 = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hη'G ω hω]
      simp only [NNReal.coe_zero]
      exact (hGg ω hω).2.1.zero
    · rw [hη'nG ω hω]
  have hm : ∀ t, Measurable fun ω => η' ω t := fun t =>
    Measurable.ite hGm (measurable_seedLine hC.1.2.1 t) measurable_const
  have hhm0 : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField hhm u₀
  have h0H : (0 : ℂ) ∉ H := fun h0' => by
    have h' : (0 : ℝ) < (0 : ℂ).im := h0'
    simp at h'
  refine ⟨η', ⟨hc, h0, fun ω t => ?_, hm, fun t => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hω : ω ∈ G
    · rw [hη'G ω hω]
      rcases (t.2 : (0 : ℝ) ≤ t).eq_or_lt with ht | ht
      · have ht0 : t = 0 := NNReal.coe_eq_zero.1 ht.symm
        show 0 ≤ (seedLine ζ W ω ((t : ℝ≥0) : ℝ)).im
        rw [ht0, NNReal.coe_zero, (hGg ω hω).2.1.zero, Complex.zero_im]
      · exact ((hGg ω hω).2.1.mem_H _ ht).le
    · rw [hη'nG ω hω]; simp
  · -- determination by the centred field
    refine ⟨fun g => (Φ (Exist.flowField 0 c (g + SupercriticalConformalCovariance.GM24.smoothDist
      upperHalfPlaneOpens u₀))).2 t, (measurable_pi_apply t).comp (measurable_snd.comp (hΦm.comp
        ((Exist.measurable_flowField 0 c).comp (WholeField.measurable_add_dist _)))), ?_⟩
    filter_upwards [hGae] with ω hω
    simp only [WholeField.centredField, sub_add_cancel]
    rw [hη'G ω hω, (hGg ω hω).2.2.2 t]
  · -- history locality of the complete path from that of its capped paths (Aux. lemma 56)
    refine Sec7.Lemma71G.isEntranceHistoryLocal_of_capAt hhm0 hc hm (fun ω => by rw [h0 ω]; exact h0H) fun n => ?_
    refine Restart.IsEntranceKilledHistoryLocal.isEntranceHistoryLocal
      (ζ := fun ω => Restart.cutLife (ζ ω) n) ?_
    refine WholeField.isEntranceKilledHistoryLocal_of_translate (κ := 4) (by norm_num) le_rfl (x := 0) (c := c)
      (fun ω => Exist.isTranslateAddConst_flowField 0 c (h ω)) hC (η := η') ?_ hhm hu₀ n
      (fun ω => Sec7.Lemma71G.continuous_capAt (hc ω) n) (fun t => hm _) ?_
    · filter_upwards [hGae] with ω hω
      have hg := (hGg ω hω).2.2.1
      rw [hη'G ω hω]
      simpa only [Complex.ofReal_zero, sub_zero] using hg
    · filter_upwards [hGae] with ω hω t
      rw [(hGg ω hω).1, Sec7.Lemma71G.capTime_top]
      rfl
  · filter_upwards [hGae] with ω hω
    rw [hη'G ω hω, ← tendsto_norm_atTop_iff_cobounded]
    exact (hGg ω hω).2.1.tendsto.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
  · filter_upwards [hGae] with ω hω
    have hg := hGg ω hω
    exact ⟨hg.1, fun t => by rw [hη'G ω hω], hg.2.1⟩

end InteractingSLE.WangWu.SeedField
