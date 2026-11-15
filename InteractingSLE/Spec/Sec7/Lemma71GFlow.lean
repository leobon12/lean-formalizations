/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71GLoc
import InteractingSLE.Spec.Restart.R1Flow
import InteractingSLE.Spec.Sec4.Prob41Lemmas
import InteractingSLE.Spec.Zhan.WordsEscape
import InteractingSLE.Spec.Sec7.ContinuityProb2Join
import InteractingSLE.Spec.Exist.FlowField

/-!
# Lemma 7.1: one flow line of the three-curve configuration with all of Lemma 6.2's hypotheses

Packet PROVE-LEMMA71G, part (A) (specification §7.1, setup p. 221 and proof of Lemma 7.1, pp. 223–225,
`source/spec/p193-240.md` L543, L596–L601). The three curves of §7.1 are flow lines `η_θ` (angles `θ₂ > 0 > θ₁` and
`0`) from `0` of one GFF `h` whose boundary data are large enough that "Proposition 5.5 applies" (Remark 4.1's regime:
no boundary contacts, infinite lifetime, transience). Lemma 6.2 (`Sec6.ae_condExp_exp_eq_explored_of_tendsto`, its
three-curve form `Sec6.Three.ae_condExp_exp_eq_three_of_tendsto`) asks of each curve: continuity and a real seed for
every `ω`, values in `ℍ̄`, measurability at each time, determination by the field, the history-sensitive locality at
first entrance times, and transience. This file supplies one version of an angle-`θ` flow line with all of them.

* `hasAdmissiblePartialSums_flowLine_angle`: Remark 4.1 for the angle-`θ` flow line (the data of `h + θχ`);
* `IsFlowLine.ae_tendsto_angle`: in that regime the flow line almost surely has infinite lifetime, never touches
  `ℝ ∖ {0}` and tends to `∞` (Aux. lemma 7, `Zhan.aux7Statement`, proved for `κ ≤ 4`);
* **`exists_lemma62Version`**: from Lemma 7.5 (`Theorem15.Lemma75Statement`, field determination) and Aux. lemma 56 at
  first entrance times (`Restart.RetainedRangeEntranceStatement`, history locality of every finite prefix), the
  version, for the centred field `h − 𝔥₀` (a zero-boundary GFF). The passage from finite prefixes to the complete curve
  is `isEntranceHistoryLocal_of_capAt` ("the extension to complete outer curves is obtained by increasing finite
  prefixes", p. 225).

The two named inputs are those of the landed first-contact locality (`Restart.exists_fcUnion_marked_of_isFlowLine`);
in the present regime (Remark 4.1) both are the §4.2 forms of their statements.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71G

open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open Sec6

/-! ### Remark 4.1 and transience for an angle-`θ` flow line -/

section Angle

variable {k : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}

/-- **Remark 4.1 for the angle-`θ` flow line from `0`.** If `b + θχ` is at most `−λ + πχ` left of `0` and at least
`λ − πχ` right of `0` (off the jump candidates), the flow-line word has every side partial sum at least `k/2 − 2`. -/
theorem hasAdmissiblePartialSums_flowLine_angle (hk : 0 < k) (hb : IsPiecewiseConstantBoundaryData b J) (θ : ℝ)
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → b x + θ * chiC k ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → sleLambda k - π * chiC k ≤ b x + θ * chiC k) :
    Sec4.HasAdmissiblePartialSums k (flowLineRhoL k b J 0 θ) (flowLineRhoR k b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0) := by
  refine Sec4.hasAdmissiblePartialSums_of_forall_not_mem hk (insert 0 J) (fun x hx hxE _ => ?_)
    (fun x hx hxE _ => ?_)
  · have hxJ : x ∉ J := fun h => hxE (Finset.mem_insert_of_mem h)
    rw [Exist.forceBoundaryData_flowLine_seed hk hb 0 θ hx.ne (by rwa [add_zero]), add_zero]
    exact hL x hx hxJ
  · have hx0 : x ≠ 0 := fun h => hxE (h ▸ Finset.mem_insert_self 0 J)
    have hxJ : x ∉ J := fun h => hxE (Finset.mem_insert_of_mem h)
    rw [Exist.forceBoundaryData_flowLine_seed hk hb 0 θ hx0 (by rwa [add_zero]), add_zero]
    exact hR x (lt_of_le_of_ne hx (Ne.symm hx0)) hxJ

/-- The generating trace of a flow line from `0`. -/
theorem IsFlowLine.exists_evolution_angle {θ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine k b J 0 θ P h η ζ) :
    ∃ (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsIntegratedSLEEvolution k (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL k b J 0 θ)
        (flowLineRhoR k b J 0 θ) P 𝓕 W VL VR B ζ ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω) := by
  obtain ⟨_, 𝓕, W, VL, VR, B, -, hcpl, htr⟩ := hfl
  refine ⟨𝓕, W, VL, VR, B, hcpl.1, ?_⟩
  filter_upwards [htr] with ω hω
  have he : (fun t => η ω t - ((0 : ℝ) : ℂ)) = η ω := by
    funext t
    simp
  rwa [he] at hω

/-- **Boundary avoidance and transience of an angle-`θ` flow line** in Remark 4.1's regime (`0 < k ≤ 4`): almost
surely the lifetime is infinite, the trace never touches `ℝ ∖ {0}`, and it tends to `∞`. -/
theorem IsFlowLine.ae_tendsto_angle (hk : 0 < k) (hk4 : k ≤ 4) (hb : IsPiecewiseConstantBoundaryData b J) {θ : ℝ}
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → b x + θ * chiC k ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → sleLambda k - π * chiC k ≤ b x + θ * chiC k)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine k b J 0 θ P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, ∀ x : ℝ, x ≠ 0 → η ω t ≠ x) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop := by
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := IsFlowLine.exists_evolution_angle hfl
  have hword := Theorem15.isOrderedForceWord_flowLine b J 0
  have hadm := hasAdmissiblePartialSums_flowLine_angle hk hb θ hL hR
  filter_upwards [Sec4.IsIntegratedSLEEvolution.ae_trace_ne_of_hasAdmissiblePartialSums hk hword hadm hev htr,
    Zhan.aux7Statement hk hk4 _ _ _ _ P 𝓕 W VL VR B ζ hword hadm hev, htr] with ω h1 h2 h3
  obtain ⟨hζ, hne⟩ := h1
  refine ⟨hζ, fun t x hx => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hx with hx | hx
    · exact (hne t).1 _ x hx (by rw [Sec4.flowLineXL_zero]; exact hx.le)
    · exact (hne t).2 _ x hx (by rw [Sec4.flowLineXR_zero]; exact hx.le)
  · rw [hζ] at h3
    exact h2.2.2 _ h3

end Angle

/-! ### Lemma 6.2's hypotheses on one curve -/

/-- **Lemma 6.2's hypotheses on one curve** (those of `Sec6.Three.ae_condExp_exp_eq_three_of_tendsto` for each of the
three curves): continuous for every `ω`, started at `0`, values in `ℍ̄`, measurable at each time, determined by the
field `h`, the history-sensitive locality at first entrance times, and transience. -/
def IsLemma62Curve {Ω : Type*} [MeasurableSpace Ω] (η : Ω → ℝ≥0 → ℂ) (h : Ω → DistOn upperHalfPlaneOpens)
    (P : Measure Ω) : Prop :=
  (∀ ω, Continuous (η ω)) ∧ (∀ ω, η ω 0 = 0) ∧ (∀ ω t, 0 ≤ (η ω t).im) ∧ (∀ t, Measurable fun ω => η ω t) ∧
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧ (fun ω => η ω t) =ᵐ[P] fun ω => f (h ω)) ∧
    IsEntranceHistoryLocal η h P ∧ ∀ᵐ ω ∂P, Tendsto (η ω) atTop (Bornology.cobounded ℂ)

/-! ### The version with Lemma 6.2's hypotheses -/

theorem capTime_top (m : ℝ≥0) (t : ℝ≥0) : Restart.capTime m ⊤ t = min t m := by
  unfold Restart.capTime
  rw [min_eq_right le_top, ENNReal.toNNReal_coe]


section Version

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **One flow line of the three-curve configuration with all of Lemma 6.2's hypotheses.** Let `0 < κ < 4`, let `h`
be a GFF with finite piecewise-constant data `b` (bounded harmonic extension `u₀`), and let `η` be an angle-`θ` flow
line of `h` from `0` in Remark 4.1's regime. From Lemma 7.5 and Aux. lemma 56 at first entrance times there is a path
`η'` which is continuous for every `ω`, starts at `0`, takes values in `ℍ̄`, is measurable at each time and
determined by the centred field `h − 𝔥₀`, has Lemma 6.2's history-sensitive locality for `h − 𝔥₀`, and almost surely
equals the flow line on `[0, ∞)` (the lifetime is infinite), avoids `ℝ ∖ {0}` and tends to `∞`. -/
theorem exists_lemma62Version (hL75 : Theorem15.Lemma75Statement.{u})
    (hA56 : Restart.RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → b x + θ * chiC κ ≤ -sleLambda κ + π * chiC κ)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → sleLambda κ - π * chiC κ ≤ b x + θ * chiC κ)
    (hη : IsFlowLine κ b J 0 θ P h η ζ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀) :
    ∃ η' : Ω → ℝ≥0 → ℂ, IsLemma62Curve η' (WholeField.centredField h u₀) P ∧
      ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t, η' ω t = η ω t) ∧ ∀ t : ℝ≥0, ∀ x : ℝ, x ≠ 0 → η' ω t ≠ x := by
  classical
  obtain ⟨Φ, hΦm, hΦ⟩ := hL75 κ hκ hκ4 b J hb 0 θ
  have hΦh := hΦ P h hh η ζ hη
  obtain ⟨η'', hη''m, hη''⟩ := Restart.exists_measurable_version_of_isFlowLine hη
  have hT := IsFlowLine.ae_tendsto_angle hκ hκ4.le hb hL hR hη
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := IsFlowLine.exists_evolution_angle hη
  -- the good event
  set good : Ω → Prop := fun ω => ζ ω = ⊤ ∧ (∀ t, η'' ω t = η ω t) ∧ Continuous (η ω) ∧ η ω 0 = 0 ∧
    (∀ t, η ω t ∈ Hbar) ∧ (∀ t : ℝ≥0, ∀ x : ℝ, x ≠ 0 → η ω t ≠ x) ∧ Tendsto (fun t => ‖η ω t‖) atTop atTop ∧
    ∀ t, (Φ (h ω)).2 t = η ω t with hgooddef
  have hgood : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hT, hη'', htr, hev.2.2.2.2, hΦh] with ω hT hη'' htr hpath hΦω
    obtain ⟨hζ, hne, hlim⟩ := hT
    obtain ⟨hw0, -, -, hcw, -⟩ := hpath
    rw [hζ] at htr hη'' hΦω hcw
    refine ⟨hζ, fun t => hη'' t le_top, ?_, htr.1, fun t => ?_, hne, hlim, fun t => hΦω.2 t le_top⟩
    · rw [← continuousOn_univ]
      exact htr.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top
    · exact Sec7.IsGeneratingTrace.mem_Hbar htr hcw hw0 le_top
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
  set η' : Ω → ℝ≥0 → ℂ := fun ω t => if ω ∈ G then η'' ω t else 0 with hη'def
  have hη'G : ∀ ω ∈ G, η' ω = η ω := fun ω hω => funext fun t => by
    simp only [hη'def, hω, ↓reduceIte]
    exact (hGg ω hω).2.1 t
  have hη'nG : ∀ ω ∉ G, η' ω = fun _ => 0 := fun ω hω => funext fun t => by
    simp only [hη'def, hω, ↓reduceIte]
  have hc : ∀ ω, Continuous (η' ω) := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hη'G ω hω]; exact (hGg ω hω).2.2.1
    · rw [hη'nG ω hω]; exact continuous_const
  have h0 : ∀ ω, η' ω 0 = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hη'G ω hω]; exact (hGg ω hω).2.2.2.1
    · rw [hη'nG ω hω]
  have hm : ∀ t, Measurable fun ω => η' ω t := fun t =>
    Measurable.ite hGm (hη''m t) measurable_const
  have hhm0 : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField hh.1 u₀
  refine ⟨η', ⟨hc, h0, fun ω t => ?_, hm, fun t => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hω : ω ∈ G
    · rw [hη'G ω hω]; exact (hGg ω hω).2.2.2.2.1 t
    · rw [hη'nG ω hω]; simp
  · refine ⟨fun g => (Φ (g + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)).2 t,
      (measurable_pi_apply t).comp (measurable_snd.comp (hΦm.comp (WholeField.measurable_add_dist _))), ?_⟩
    filter_upwards [hGae] with ω hω
    simp only [WholeField.centredField, sub_add_cancel]
    rw [hη'G ω hω, (hGg ω hω).2.2.2.2.2.2.2 t]
  · -- history locality of the complete path from that of its finite prefixes (Aux. lemma 56)
    have h0H : (0 : ℂ) ∉ H := fun h0' => by
      have h' : (0 : ℝ) < (0 : ℂ).im := h0'
      simp at h'
    refine isEntranceHistoryLocal_of_capAt hhm0 hc hm (fun ω => by rw [h0 ω]; exact h0H) ?_
    intro n
    refine Restart.IsEntranceKilledHistoryLocal.isEntranceHistoryLocal
      (ζ := fun ω => Restart.cutLife (ζ ω) n) ?_
    refine hA56 κ hκ hκ4 b J hb 0 θ P h hh η ζ hη u₀ hu₀ n (fun ω => capAt (η' ω) n)
      (fun ω => continuous_capAt (hc ω) n) (fun t => hm _) ?_
    filter_upwards [hGae] with ω hω t
    rw [(hGg ω hω).1, capTime_top]
    show η' ω (min t n) = η ω (min t n)
    rw [hη'G ω hω]
  · filter_upwards [hGae] with ω hω
    rw [hη'G ω hω, ← tendsto_norm_atTop_iff_cobounded]
    exact (hGg ω hω).2.2.2.2.2.2.1
  · filter_upwards [hGae] with ω hω
    have hg := hGg ω hω
    exact ⟨hg.1, fun t => by rw [hη'G ω hω], fun t x hx => by rw [hη'G ω hω]; exact hg.2.2.2.2.2.1 t x hx⟩

end Version

end InteractingSLE.Sec7.Lemma71G
