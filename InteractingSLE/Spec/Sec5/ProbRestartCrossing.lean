/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.ProbCrossing
import InteractingSLE.Spec.Sec2.RestartEvolution

/-!
# Lemma 5.10 for an evolution from a random initial state

Packet PROVE-RESTART. The crossing estimate `Sec5.crossing_lower_bound` (packet PROVE-SEC5-B) is stated for
an evolution with a deterministic force word. An evolution restarted at a stopping time
(`Sec2.Restart.exists_restart`) starts from the random state `V_T − W_T`, so the conditional form of
Lemma 5.10 needs the estimate for a random start (`IsIntegratedSLEEvolutionFrom`).

`crossing_lower_bound_from` is that estimate, with the same constant `p₀ = p₀(κ, C, J)`. Its proof is the
proof of `crossing_lower_bound`, unchanged except that the force positions are read at `ω`: the change of
measure (`girsanov_cutDriftT`), the reference events and the pathwise argument `crossing_path` use the
initial positions only through `0 ≤ x_{1,R}`, which holds for every start (`w_le_vR` at time `0`).
(The landed `crossing_lower_bound` is the special case of a constant start,
`isIntegratedSLEEvolutionFrom_const_iff`.)
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper.RS
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Sec5

open Girsanov

/-- **Lemma 5.10 for a random initial state.** Fix `κ > 0`, `C`, and a compact `J ⊂ (−2, ∞)`. There is
`p₀ > 0` such that for every integrated `SLE_κ(ρ_L; ρ_R)` evolution from a random, `𝓕_0`-measurable initial
state (`IsIntegratedSLEEvolutionFrom`, at least one right force point) on any probability space, whose first
right weight lies in `J`, which is defined through `τ ∧ 1` (`τ = inf {t : |W_t| ≥ 1}`), and whose remaining
drift `U = otherDrift` satisfies `|U_t| ≤ C` for almost every `t ≤ τ ∧ 1`, almost surely: `ℙ[τ ≥ 1] ≥ p₀`. -/
theorem crossing_lower_bound_from {κ C : ℝ} (hκ : 0 < κ) {J : Set ℝ} (hJ : IsCompact J)
    (hJ2 : J ⊆ Set.Ioi (-2)) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) {nL nR : ℕ} (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
      (ρL : Fin nL → ℝ) (ρR : Fin (nR + 1) → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolutionFrom κ ρL ρR P 𝓕 xL xR W VL VR B ζ → ρR 0 ∈ J →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ 1 → (∀ u < t, |W u ω| < 1) → (t : ℝ≥0∞) < ζ ω) →
      (∀ᵐ ω ∂P, ∀ᵐ r ∂(volume : Measure ℝ), 0 ≤ r → r.toNNReal ≤ 1 →
        (∀ u < r.toNNReal, |W u ω| < 1) →
        |otherDrift ρL ρR (W r.toNNReal ω) (fun i => VL i r.toNNReal ω)
          (fun i => VR i r.toNNReal ω)| ≤ C) →
      p₀ ≤ P.real {ω | ∀ t : ℝ≥0, t < 1 → |W t ω| < 1} := by
  obtain ⟨ρlo, ρmax, hρlo, hρmax0, hJb⟩ := exists_crossing_params hJ hJ2
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set sk : ℝ := Real.sqrt κ with hskdef
  have hsk : 0 < sk := Real.sqrt_pos.2 hκ
  set cl : ℝ := (2 + ρlo) / κ with hcldef
  have hcl : 0 < cl := div_pos (by linarith) hκ
  set a₁ : ℝ := 1 / (8 * sk) with ha₁def
  have ha₁ : 0 < a₁ := by positivity
  set b₁ : ℝ := cl * sk / (8 * (ρmax + 1)) with hb₁def
  have hb₁ : 0 < b₁ := by positivity
  -- the reference Wiener measure
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, B₀, hB₀, hB₀c, -⟩ := OneForce.exists_filteredBrownian
  have hB₀m : ∀ t, Measurable (B₀ t) := fun t => (hB₀.2.1 t).mono (𝓕₀.le t) le_rfl
  set μ₀ : Measure CPath := P₀.map (toCPath B₀ hB₀c) with hμ₀def
  have : IsProbabilityMeasure μ₀ := by rw [hμ₀def]; infer_instance
  have hμ₀ : IsPreBrownianReal canonBM μ₀ :=
    (isBrownianReal_canonBM hB₀.1.toIsPreBrownianReal hB₀m hB₀c).toIsPreBrownianReal
  obtain ⟨s, hs0, hs1, gY, hgY, hq₁⟩ :=
    exists_pos_measureReal_pastEvent hμ₀ hcl ha₁ hb₁ (s₁ := 1) one_pos
  set a₂ : ℝ := min (1 / 8) (sk * gY / 4) / sk with ha₂def
  have ha₂ : 0 < a₂ := div_pos (lt_min (by norm_num) (by positivity)) hsk
  set q₂ : ℝ := Real.exp (-(Real.pi ^ 2 * ((1 - s : ℝ≥0) : ℝ) / (8 * a₂ ^ 2))) with hq₂def
  set q : ℝ := μ₀.real (pastEvent cl a₁ b₁ gY s) * q₂ with hqdef
  have hq : 0 < q := mul_pos hq₁ (Real.exp_pos _)
  set g : ℝ := sk * gY with hgdef
  have hg : 0 < g := mul_pos hsk hgY
  set M : ℝ := C' / sk + ρmax / sk * (g / 2)⁻¹ with hMdef
  refine ⟨Real.exp (-(M ^ 2 * 2)) * q ^ 2, by positivity, ?_⟩
  intro Ω mΩ P hP 𝓕 nL nR xL xR ρL ρR W VL VR B ζ hE hρJ hlife hU
  obtain ⟨hBF, -, -, hWad, hVLad, hVRad, hpath⟩ := hE
  obtain ⟨hρlo', hρmax'⟩ := hJb _ hρJ
  have hmad : ∀ j, AdaptedBefore 𝓕 ζ (allMarks VL VR j) := Sec2.allMarks_adaptedBefore hVLad hVRad
  have hFm : Measurable (uncurry3 (crossF κ C' ρL ρR g s)) := measurable_crossF κ C' ρL ρR hg s
  have hFb : ∀ t w u, |crossF κ C' ρL ρR g s t w u| ≤ M := fun t w u =>
    abs_crossF_le hC'0 hρmax' hg s t w u
  -- the cut time `1 ∧ (lifetime)`
  have hτ : ∀ u : ℝ≥0, MeasurableSet[𝓕 u] {ω | min (1 : ℝ≥0∞) (ζ ω) ≤ u} := by
    intro u
    have h1 : MeasurableSet[𝓕 u] {ω | (u : ℝ≥0∞) < ζ ω} := by
      simpa using hWad u Set.univ MeasurableSet.univ
    have : {ω | min (1 : ℝ≥0∞) (ζ ω) ≤ u} = {_ω | (1 : ℝ≥0∞) ≤ u} ∪ {ω | (u : ℝ≥0∞) < ζ ω}ᶜ := by
      ext ω
      simp [min_le_iff, not_lt]
    rw [this]
    exact (MeasurableSet.const _).union h1.compl
  have hτζ : ∀ ω, min (1 : ℝ≥0∞) (ζ ω) ≤ ζ ω := fun ω => min_le_right _ _
  have hτT : ∀ ω, min (1 : ℝ≥0∞) (ζ ω) ≤ ((1 : ℝ≥0) : ℝ≥0∞) := fun ω => by
    simp
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => allMarks VL VR j s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hpath] with ω hp
    refine ⟨hp.2.2.2.1, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hp.2.2.2.2.1 i
    | right i => simpa [allMarks] using hp.2.2.2.2.2.1 i
  have hFc : ∀ᵐ ω ∂P, ∀ᵐ r ∂(volume : Measure ℝ), 0 < r →
      (r.toNNReal : ℝ≥0∞) < min (1 : ℝ≥0∞) (ζ ω) →
      ContinuousAt (uncurry3 (crossF κ C' ρL ρR g s))
        (r.toNNReal, W r.toNNReal ω, fun j => allMarks VL VR j r.toNNReal ω) := by
    filter_upwards [hpath] with ω hp
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcL, hcR, -⟩ := hp
    have hL : ∀ᵐ r ∂(volume : Measure ℝ), ∀ i, r ∉ {r : ℝ | 0 ≤ r ∧
        (r.toNNReal : ℝ≥0∞) < ζ ω ∧ W r.toNNReal ω = VL i r.toNNReal ω} :=
      ae_all_iff.2 fun i => measure_eq_zero_iff_ae_notMem.1 (hcL i)
    have hR : ∀ᵐ r ∂(volume : Measure ℝ), ∀ i, r ∉ {r : ℝ | 0 ≤ r ∧
        (r.toNNReal : ℝ≥0∞) < ζ ω ∧ W r.toNNReal ω = VR i r.toNNReal ω} :=
      ae_all_iff.2 fun i => measure_eq_zero_iff_ae_notMem.1 (hcR i)
    filter_upwards [hL, hR, ae_ne_real (s : ℝ)] with r hrL hrR hrs hr0 hrτ
    have hrζ : (r.toNNReal : ℝ≥0∞) < ζ ω := hrτ.trans_le (hτζ ω)
    refine continuousAt_crossF κ C' ρL ρR hg s ?_ (fun i => ?_) (fun i => ?_)
    · intro h
      apply hrs
      rw [← h, Real.coe_toNNReal _ hr0.le]
    · rw [markL_allMarks]
      exact fun h => hrL i ⟨hr0.le, hrζ, h⟩
    · rw [markR_allMarks]
      exact fun h => hrR i ⟨hr0.le, hrζ, h⟩
  -- Girsanov
  obtain ⟨hequiv, hBQ, hid⟩ := girsanov_cutDriftT hBF hFm hFb hWad hmad hτ hτζ hτT hcont hFc
  have hQprob := hequiv.isProb
  have hQP := hequiv.ac
  have := isFilteredPreBrownian_of_isFilteredBrownianReal hBF
  have hθp := isStronglyProgressive_cutDriftT hFm hWad hmad hτ
  have hθb := abs_cutDriftT_le (τ := fun ω => min (1 : ℝ≥0∞) (ζ ω)) (ζ := ζ) (W := W)
    (U := allMarks VL VR) hFb
  have hθreg := isRiemannRegular_cutDriftT (P := P) hFb hτζ hcont hFc
  have hA'm := measurableSet_goodEvent hWad
  have htr := le_measureReal_of_girsanov (B := B) hθp.stronglyAdapted hθb hθreg (1 + 1) hA'm
  set θ := cutDriftT (fun ω => min (1 : ℝ≥0∞) (ζ ω)) ζ (crossF κ C' ρL ρR g s) W (allMarks VL VR)
    with hθdef
  set Q := girsanovMeasure P 𝓕 B θ (1 + 1) with hQdef
  -- `goodEvent ⊆ {τ ≥ 1}`
  have hAA : P.real (goodEvent W ζ) ≤ P.real {ω | ∀ t : ℝ≥0, t < 1 → |W t ω| < 1} := by
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [hcont] with ω hω hωA
    exact forall_abs_lt_of_mem_goodEvent hω.1 hωA
  -- the changed Brownian motion has the reference law
  obtain ⟨Bt, hBtm, hBtc, -, hBt, hBteq⟩ := exists_good_version0 hBQ.1
  have hmap : Q.map (toCPath Bt hBtc) = μ₀ :=
    map_toCPath_eq hBt.toIsPreBrownianReal hB₀.1.toIsPreBrownianReal hBtm hB₀m hBtc hB₀c
  set E : Set CPath := pastEvent cl a₁ b₁ gY s ∩ incrEvent s (1 - s) a₂ with hEdef
  have hshift : Measurable fun f : CPath => shiftPath s f :=
    measurable_pi_iff.2 fun u => (measurable_canonBM _).sub (measurable_canonBM s)
  have hEm : MeasurableSet E :=
    (canonFilt.le s _ (measurableSet_pastEvent hcl a₁ b₁ gY s)).inter
      (hshift.comap_le _ (measurableSet_incrEvent s (1 - s) a₂))
  have hQE : Q.real (toCPath Bt hBtc ⁻¹' E) = μ₀.real E := by
    rw [← hmap, measureReal_def, measureReal_def,
      Measure.map_apply (measurable_toCPath hBtm hBtc) hEm]
  have hμE : q ≤ μ₀.real E := by
    rw [hEdef, measureReal_pastEvent_inter_incrEvent hμ₀ hcl]
    exact mul_le_mul_of_nonneg_left (exp_le_measureReal_incrEvent hμ₀ s (1 - s) ha₂)
      measureReal_nonneg
  have hBes : ∀ᵐ ω ∂Q, Bessel.IsBesselPath cl 0 (fun t => -(toCPath Bt hBtc ω).1 t)
      (fun t => besY cl (toCPath Bt hBtc ω) t) := by
    have h := ae_isBesselPath_besY hμ₀ hcl
    rw [← hmap] at h
    exact ae_of_ae_map (measurable_toCPath hBtm hBtc).aemeasurable h
  -- the pathwise argument on `E`
  have hincl : toCPath Bt hBtc ⁻¹' E ≤ᵐ[Q] goodEvent W ζ := by
    filter_upwards [hQP.ae_le hpath, hQP.ae_le hlife, hQP.ae_le hU, hQP.ae_le hid, hBteq, hBes]
      with ω hp hl hu hgi hBe hYb hωE
    obtain ⟨⟨hE1, hE2, hE3⟩, hF⟩ := hωE
    have hsplit := fun (t : ℝ≥0) (ht : (t : ℝ≥0∞) < ζ ω) => w_eq_split hp ht
    obtain ⟨hw0, -, hvR0, hwc, -, hvRc, -, -, hwvR, -, -, hgR, -, -, hvReq, -, hcR, -⟩ := hp
    have hlife' : ∀ t, InDom (fun t => W t ω) t → (t : ℝ≥0∞) < ζ ω := fun t ht => hl t ht.1 ht.2
    have hx : 0 ≤ xR ω 0 := by
      have h0 := hwvR 0 (hlife' 0 ⟨zero_le_one, fun u hu => absurd hu (not_lt_zero)⟩) 0
      rw [hw0, hvR0 0] at h0
      exact h0
    have ho : ∀ᵐ r ∂(volume : Measure ℝ), 0 ≤ r → InDom (fun t => W t ω) r.toNNReal →
        |otherDrift ρL ρR (W r.toNNReal ω) (fun i => VL i r.toNNReal ω)
          (fun i => VR i r.toNNReal ω)| ≤ C' := by
      filter_upwards [hu] with r hr hr0 hd
      exact (hr hr0 hd.1 hd.2).trans (le_max_left _ _)
    have hgir : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min 1 (ζ ω) → Bt t ω = B t ω + ∫ r in (0 : ℝ)..t,
        crossIntegrand κ C' (ρR 0) g s r.toNNReal (W r.toNNReal ω)
          (VR 0 r.toNNReal ω) (otherDrift ρL ρR (W r.toNNReal ω) (fun i => VL i r.toNNReal ω)
            (fun i => VR i r.toNNReal ω)) := by
      intro t ht
      rw [hBe t, hgi t ht]
      simp only [crossF_allMarks]
    have hsk0 := hsk.ne'
    have hcl0 := hcl.ne'
    have ha₁' : sk * a₁ + ρmax * b₁ / (cl * sk) ≤ 1 / 4 := by
      have e1 : sk * a₁ = 1 / 8 := by
        rw [ha₁def]; field_simp
      have e2 : ρmax * b₁ / (cl * sk) = ρmax / (8 * (ρmax + 1)) := by
        rw [hb₁def]; field_simp
      have e3 : ρmax / (8 * (ρmax + 1)) ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have ha₂' : sk * a₂ ≤ min (1 / 8) (sk * gY / 4) := by
      rw [ha₂def, mul_div_cancel₀ _ hsk.ne']
    have hclc : cl ≤ (2 + ρR 0) / κ := div_le_div_of_nonneg_right (by linarith) hκ.le
    have hpath' := crossing_path (w := fun t => W t ω) (v := fun t => VR 0 t ω)
      (o := fun t => otherDrift ρL ρR (W t ω) (fun i => VL i t ω) (fun i => VR i t ω))
      (b := fun t => B t ω) (bq := fun t => Bt t ω) (y := fun t => besY cl (toCPath Bt hBtc ω) t)
      (ζ := ζ ω) (C := C') hκ hgY hρmax' hcl hclc hx hw0 hlife' hwc (hvRc 0)
      (fun t ht => hwvR t ht 0) (fun t ht => hgR t ht 0) (fun t ht => (hsplit t ht).1)
      (fun t ht => (hsplit t ht).2) (fun t ht => hvReq t ht 0) (hcR 0) ho hgir hYb hE1 hE2 hE3 hF
      ha₁' ha₂'
    simp only [goodEvent, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_Icc]
    intro q hq
    obtain ⟨h1, h2⟩ := hpath' q (le_of_mem_ratTimesLE hq)
    exact ⟨h1, (abs_le.1 h2).1, (abs_le.1 h2).2⟩
  have hQA : q ≤ Q.real (goodEvent W ζ) :=
    hμE.trans (hQE ▸ ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hincl))
  have h2 : ((1 + 1 : ℝ≥0) : ℝ) = 2 := by norm_num
  rw [h2] at htr
  calc Real.exp (-(M ^ 2 * 2)) * q ^ 2
      ≤ Real.exp (-(M ^ 2 * 2)) * (Q.real (goodEvent W ζ)) ^ 2 := by
        gcongr
    _ ≤ P.real (goodEvent W ζ) := htr
    _ ≤ _ := hAA

end Sec5

end InteractingSLE
