/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP4SwallowEvent
import InteractingSLE.Spec.Sec7.TrialsHiCompare

/-!
# LP4's right swallowing: deleting the separated left drift

Packet PROVE-LP18. Specification p. 482: "Thus, for sufficiently small deterministic `ε`, it is swallowed before the
buffered stop `1/64 ∧ inf{|W| ≥ 1/4}` with positive probability. The separated left drift can be deleted through this
stop by the bounded-energy change in LP1. Equivalence transfers that positive probability to the actual two-seed future."

For a word with one left mark at `x_L < 0` and one right mark at `x_R > x_L`, two left weights `ρ_L` (the law that is
run) and `ρ_L'` (the target law) and a right weight `ρ_R > −2`: if under the run law, with positive probability, a
point beyond the right mark is swallowed by a time `t < N` before which the driver stays above `−M`, where
`x_L + M + 2δ ≤ 0` (so the left gap stays at least `2δ`), then the canonical probability that the target law swallows
a point beyond its right mark is positive (`codeLaw_allSet_ne_zero_of_compare`).

The proof is PROVE-TRIALS-HI's `Sec7.TrialsHi.measure_horizonEvent_le` (Girsanov's theorem with a bounded energy,
`Sec2.IsSLEEvolutionUpTo.girsanov_changeWeights`, and pathwise uniqueness of the target law driven by the Girsanov
Brownian motion, `Sec2.UpTo.agree_of_lt_min`), with only the **left** gap stopped (the right mark may meet the driver,
which is how points beyond it are swallowed): the stop is the first time the left gap falls below `δ` (the smallest gap
of the state with a dummy right mark at distance `1`), capped at the horizon. The target law reaches no continuation
threshold before that stop, because its left mark is away from the driver and its right weight is `> −2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.LP.LP4S

open QuantumZipper Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart Girsanov Coupling

/-- The energy of a drift bounded by `C` on `[0, T]` is at most `C² T`. -/
theorem quadInt_le_of_bound {Ω : Type*} {θ : ℝ≥0 → Ω → ℝ} {C : ℝ} (hθ : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0)
    (ω : Ω) : quadInt θ T ω ≤ C ^ 2 * T := by
  unfold quadInt
  by_cases hint : IntervalIntegrable (fun u : ℝ => θ u.toNNReal ω ^ 2) volume 0 T
  · calc (∫ u in (0 : ℝ)..T, θ u.toNNReal ω ^ 2) ≤ ∫ _ in (0 : ℝ)..T, C ^ 2 :=
          intervalIntegral.integral_mono_on T.coe_nonneg hint intervalIntegrable_const fun u _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hθ _ _) 2
      _ = C ^ 2 * T := by rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring
  · rw [intervalIntegral.integral_undef hint]; positivity

/-- A state whose left mark is away from the driver, with a right weight `> −2`, is not a continuation threshold. -/
theorem not_thresholdCondition_of_left {ρL ρR : Fin 1 → ℝ} (hρR : -2 < ρR 0) {w₀ : ℝ} {vL₀ vR₀ : Fin 1 → ℝ}
    (h : vL₀ 0 ≠ w₀) : ¬ ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := by
  rintro (h1 | h1)
  · have hfe : (Finset.univ.filter fun i : Fin 1 => vL₀ i = w₀) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun i _ he => h (by rwa [Fin.fin_one_eq_zero i] at he)
    rw [hfe, Finset.sum_empty] at h1; linarith
  · by_cases hR : vR₀ 0 = w₀
    · have hfe : (Finset.univ.filter fun i : Fin 1 => vR₀ i = w₀) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => by rwa [Fin.fin_one_eq_zero i]
      rw [hfe, Fin.sum_univ_one] at h1; linarith
    · have hfe : (Finset.univ.filter fun i : Fin 1 => vR₀ i = w₀) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun i _ he => hR (by rwa [Fin.fin_one_eq_zero i] at he)
      rw [hfe, Finset.sum_empty] at h1; linarith

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL xR ρL ρL' ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Deleting the separated left drift transfers positivity** (LP4, p. 482; LP1's bounded-energy change). If the
run law `(ρ_L; ρ_R)` from `(x_L, x_R)` swallows, with positive probability, a point beyond its right mark by a time
`t < N` before which the driver stays above `−M`, with `x_L + M + 2δ ≤ 0`, `0 < δ < 1`, then the target law
`(ρ_L'; ρ_R)` swallows a point beyond its right mark with positive canonical probability. -/
theorem codeLaw_allSet_ne_zero_of_compare [IsProbabilityMeasure P] (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hsep : xL 0 < xR 0) (hρR : -2 < ρR 0) {M N δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hMδ : xL 0 + M + 2 * δ ≤ 0) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hpos : P {ω | SwalWin M N (xL, xR) (fun t => W t ω) (ζ ω)} ≠ 0) :
    codeLaw κ ρL' ρR allSet (xL, xR) ≠ 0 := by
  have hsep' : ∀ i j, xL i < xR j := fun i j => by
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; exact hsep
  set T₀ : ℝ≥0 := N.toNNReal with hT₀
  have hNT : N ≤ (T₀ : ℝ) := Real.le_coe_toNNReal N
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  -- the good paths
  set Good : Ω → Prop := fun ω => ζ ω = ⊤ ∧ Continuous (fun s => W s ω) ∧ Continuous (fun s => VL 0 s ω) ∧
    Continuous (fun s => VR 0 s ω) ∧ IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) ⊤ with hGood
  have hgood : ∀ᵐ ω ∂P, Good ω := by
    filter_upwards [hζ, hE.2.2.2.2] with ω hζω hp
    rw [hζω] at hp
    have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ⊤} → Continuous f := fun hf =>
      continuousOn_univ.1 (hf.mono fun t _ => ENNReal.coe_lt_top)
    exact ⟨hζω, hcont hp.2.2.2.1, hcont (hp.2.2.2.2.1 0), hcont (hp.2.2.2.2.2.1 0), hp⟩
  set Nn := {ω | ¬ Good ω} with hNndef
  have hN : P Nn = 0 := ae_iff.1 hgood
  set G := (toMeasurable P Nn)ᶜ with hGdef
  have hGm : MeasurableSet[𝓖 0] G :=
    (Ito.measurableSet_usualAugmentation_of_null (measurableSet_toMeasurable P Nn)
      (by rw [measure_toMeasurable]; exact hN) 0).compl
  have hGgood : ∀ ω ∈ G, Good ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P Nn h)
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact hN
  -- the left-gap stop: the smallest gap of the state with a dummy right mark at distance `1`
  set VR' : Fin 1 → ℝ≥0 → Ω → ℝ := fun _ t ω => W t ω + 1 with hVR'
  have hstc : ∀ ω ∈ G, Continuous (fun s => stateAt W VL VR' s ω) := fun ω hω => by
    obtain ⟨-, hw, hl, -, -⟩ := hGgood ω hω
    refine hw.prodMk ((continuous_pi fun i => ?_).prodMk (continuous_pi fun _ => hw.add continuous_const))
    rw [Fin.fin_one_eq_zero i]; exact hl
  have hVR'a : AdaptedBefore 𝓖 ζ (VR' 0) :=
    ZhanGT4.adaptedBefore_of_eq (fun _ p => p.1 + 1) (fun _ => by fun_prop) hE𝓖.2.1 (hE𝓖.2.2.1 0) (hE𝓖.2.2.2.1 0)
      fun _ _ => rfl
  set τ := minGapStop G δ T₀ ζ W VL VR' with hτdef
  have hτm : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | τ ω ≤ s} :=
    measurableSet_minGapStop_le hE𝓖.2.1 hE𝓖.2.2.1 (fun _ => hVR'a) hGm fun ω hω => (hstc ω hω).continuousOn
  have hτζ : ∀ ω, τ ω ≤ ζ ω := minGapStop_le_zeta fun ω hω => (hGgood ω hω).1
  have hτT : ∀ ω, τ ω ≤ T₀ := minGapStop_le
  have hgapG : ∀ ω ∈ G, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → δ ≤ |W t ω - VL 0 t ω| := fun ω hω t ht =>
    (le_minGap_iff.1 (le_minGap_of_lt_minGapStop hω ht (ht.trans_le (hτζ ω)))).2.1 0
  have hτG : ∀ ω, ω ∉ G → τ ω = 0 := fun ω hω => by simp [hτdef, minGapStop, hω]
  have hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i, ρL' i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧ ∀ i, ρR i ≠ ρR i → δ ≤ |W t ω - VR i t ω| :=
    Eventually.of_forall fun ω t ht => by
      by_cases hω : ω ∈ G
      · exact ⟨fun i _ => by rw [Fin.fin_one_eq_zero i]; exact hgapG ω hω t ht, fun i h => absurd rfl h⟩
      · rw [hτG ω hω] at ht
        exact absurd ht (not_lt.2 zero_le)
  -- Girsanov
  have hEU := hE𝓖.isSLEEvolutionUpTo
  obtain ⟨hQeq, hEQ⟩ := hEU.girsanov_changeWeights hκ ρL' ρR hτm hτζ hτT hδ hgap
  obtain ⟨hθp, hθb, hθreg⟩ := hEU.weightDrift_props ρL' ρR hτm hτζ hδ
  set θ := weightDrift κ δ ρL ρL' ρR ρR τ ζ W VL VR with hθdef
  set Q := girsanovMeasure P 𝓖 B θ (T₀ + 1) with hQdef
  have hQp : IsProbabilityMeasure Q := hQeq.isProb
  have href : codeLaw κ ρL' ρR (univ : Set (XCode 1 1)) (xL, xR) = 1 := by
    obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
      exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := ρL') (ρR := ρR)
    rw [← measure_eventOf_eq_codeLaw hκ hsep' hE' (Φ := fun _ _ => True) MeasurableSet.univ
      (fun _ _ _ => iff_of_true (mem_univ _) trivial) (fun _ _ _ _ h => h)]
    simp
  have hpath : Measurable fun ω (s : ℝ≥0) => girsanovProcess B θ s ω :=
    measurable_pi_iff.2 fun s => (hEQ.brownian.2.1 s).mono (𝓖.le s) le_rfl
  have hmap : Q.map (fun ω (s : ℝ≥0) => girsanovProcess B θ s ω) = wienerPath :=
    map_path_eq_wienerPath hEQ.brownian.1.toIsPreBrownianReal hpath
  have hstart : Measurable fun ω => (((xL, xR) : (Fin 1 → ℝ) × (Fin 1 → ℝ)),
      fun s : ℝ≥0 => girsanovProcess B θ s ω) := measurable_const.prodMk hpath
  set F := (fun ω => (((xL, xR) : (Fin 1 → ℝ) × (Fin 1 → ℝ)), fun s : ℝ≥0 => girsanovProcess B θ s ω)) ⁻¹'
    restartSetS κ ρL' ρR allSet with hFdef
  have hFm : MeasurableSet F := hstart (measurableSet_restartSetS measurableSet_allSet)
  set C : ℝ := |1 / Real.sqrt κ| * ((∑ j, |weightDiff ρL ρL' ρR ρR j|) * δ⁻¹) with hC
  have hdens := measure_inter_le_girsanov (isFilteredPreBrownian_of_isFilteredBrownianReal hE𝓖.1)
    hθp.stronglyAdapted hθb hθreg (T₀ + 1) hFm MeasurableSet.univ (A := univ) (m := C ^ 2 * (T₀ + 1 : ℝ≥0))
    fun ω _ => quadInt_le_of_bound hθb _ ω
  have hQF : Q F = codeLaw κ ρL' ρR allSet (xL, xR) := by
    rw [hFdef, show (fun ω => (((xL, xR) : (Fin 1 → ℝ) × (Fin 1 → ℝ)),
        fun s : ℝ≥0 => girsanovProcess B θ s ω)) =
        Prod.mk ((xL, xR) : (Fin 1 → ℝ) × (Fin 1 → ℝ)) ∘ fun ω (s : ℝ≥0) => girsanovProcess B θ s ω from rfl,
      Set.preimage_comp, ← Measure.map_apply hpath
        ((measurableSet_restartSetS measurableSet_allSet).preimage measurable_prodMk_left), hmap]
    rfl
  have hcan : ∀ᵐ ω ∂Q, (((xL, xR) : (Fin 1 → ℝ) × (Fin 1 → ℝ)), fun s : ℝ≥0 => girsanovProcess B θ s ω) ∈
      restartSetS κ ρL' ρR (univ : Set (XCode 1 1)) := by
    have hS : MeasurableSet (Prod.mk ((xL, xR) : (Fin 1 → ℝ) × (Fin 1 → ℝ)) ⁻¹'
        restartSetS κ ρL' ρR (univ : Set (XCode 1 1))) :=
      (measurableSet_restartSetS MeasurableSet.univ).preimage measurable_prodMk_left
    have hW1 : ∀ᵐ f ∂wienerPath, f ∈ Prod.mk ((xL, xR) : (Fin 1 → ℝ) × (Fin 1 → ℝ)) ⁻¹'
        restartSetS κ ρL' ρR (univ : Set (XCode 1 1)) := by
      have h1 : wienerPath (Prod.mk ((xL, xR) : (Fin 1 → ℝ) × (Fin 1 → ℝ)) ⁻¹'
          restartSetS κ ρL' ρR (univ : Set (XCode 1 1))) = 1 := href
      exact (ae_mem_iff_measure_eq hS.nullMeasurableSet).2 (by rw [h1, measure_univ])
    rw [← hmap] at hW1
    exact ae_of_ae_map hpath.aemeasurable hW1
  -- the windowed event of the run law lies in `F`
  have hsub : {ω | SwalWin M N (xL, xR) (fun t => W t ω) (ζ ω)} ≤ᵐ[P] (F ∩ univ : Set Ω) := by
    filter_upwards [hQeq.ac'.ae_le hEQ.ae_path, hQeq.ac'.ae_le hEQ.brownian.1.cont,
      hQeq.ac'.ae_le hcan, measure_eq_zero_iff_ae_notMem.1 hGc] with ω hpω hcω hxω hωG' hω
    have hωG : ω ∈ G := by simpa using hωG'
    obtain ⟨hζω, hwc, hlc, hrc, hp⟩ := hGgood ω hωG
    obtain ⟨q, t, k, hq, -, htN, hal, hlow⟩ := hω
    have hlowR := forall_le_of_forall_rat hwc hlow
    obtain ⟨-, hvL0, -, -, -, -, -, hvLw, -, -, hgL, -, -, hvLeq, -, -, -, -, -, -⟩ := hp
    have hvL : ∀ u : ℝ≥0, VL 0 u ω ≤ xL 0 := fun u => by
      have h := LP4HB.le_of_forceL (w := fun t => W t ω) (v := fun t => VL 0 t ω) (x := xL 0)
        (fun s => hvLw s ENNReal.coe_lt_top 0) (fun s => hgL s ENNReal.coe_lt_top 0)
        (fun s => hvLeq s ENNReal.coe_lt_top 0) (zero_le (a := u))
      rwa [show VL 0 0 ω = xL 0 from hvL0 0] at h
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hgap2 : ∀ u : ℝ≥0, u ≤ (t : ℝ≥0) → 2 * δ < W u ω - VL 0 u ω := fun u hu => by
      have h1 := hlowR u hu; have h2 := hvL u; linarith
    -- the stop comes after `t`
    have htτ : ((t : ℝ≥0) : ℝ≥0∞) < τ ω := by
      set f : ℝ≥0 → ℝ := fun s => minGap (stateAt W VL VR' s ω) with hf
      have hfc : Continuous f := continuous_minGap.comp (hstc ω hωG)
      have hfK : ∀ u ∈ Icc (0 : ℝ≥0) (t : ℝ≥0), δ < f u := fun u hu => by
        simp only [hf, minGap]
        rw [Finset.lt_inf'_iff]
        rintro (_ | i | j) -
        · exact hδ1
        · show δ < |W u ω - VL i u ω|
          rw [Fin.fin_one_eq_zero i, abs_of_pos (by linarith [hgap2 u hu.2])]
          linarith [hgap2 u hu.2]
        · show δ < |W u ω - (W u ω + 1)|
          rw [show W u ω - (W u ω + 1) = -1 by ring, abs_neg, abs_one]; exact hδ1
      obtain ⟨ε, hε, hsubK⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (t : ℝ≥0))).exists_cthickening_subset_open
        (isOpen_lt continuous_const hfc) hfK
      have hhit : (((t : ℝ≥0) + ε.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ minGapHit G δ ζ W VL VR' ω := by
        simp only [minGapHit, hωG, ↓reduceIte]
        refine le_hitBelow fun s _ hs => ?_
        by_contra hlt
        push Not at hlt
        refine absurd (hsubK ?_) (not_lt.2 hs.le)
        by_cases hst : s ≤ (t : ℝ≥0)
        · exact Metric.self_subset_cthickening _ ⟨zero_le, hst⟩
        · push Not at hst
          refine Metric.mem_cthickening_of_dist_le s (t : ℝ≥0) ε _ ⟨zero_le, le_rfl⟩ ?_
          rw [NNReal.dist_eq, abs_of_pos (sub_pos.2 (show ((t : ℝ≥0) : ℝ) < s from hst))]
          have : (s : ℝ) < (t : ℝ≥0) + ε := by
            have h := (NNReal.coe_lt_coe.2 hlt)
            rwa [NNReal.coe_add, Real.coe_toNNReal _ hε.le] at h
          linarith
      have htT : ((t : ℝ≥0) : ℝ) < T₀ := htN.trans_le hNT
      have hlt : ((t : ℝ≥0) : WithTop ℝ≥0) < min (minGapHit G δ ζ W VL VR' ω) (T₀ : WithTop ℝ≥0) := by
        refine lt_min (lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_) hhit) (WithTop.coe_lt_coe.2 ?_)
        · exact lt_add_of_pos_right _ (Real.toNNReal_pos.2 hε)
        · exact_mod_cast htT
      rw [← coe_capTime] at hlt
      simp only [hτdef, minGapStop, hωG, ↓reduceIte]
      exact ENNReal.coe_lt_coe.2 (WithTop.coe_lt_coe.1 hlt)
    refine ⟨?_, mem_univ _⟩
    obtain ⟨x, ⟨⟨hxF, hxSep⟩, -⟩, hxeq⟩ := hxω
    have hxs : startOf x = (xL, xR) := (Prod.ext_iff.1 hxeq).1
    have hx1 : x.1 = enc (fun s => girsanovProcess B θ s ω) := (Prod.ext_iff.1 hxeq).2
    have hxC : x ∈ CRel κ xL xR ρL' ρR := mem_cRelF_iff.1 ⟨hxF, hxs⟩
    have hpx : IsIntegratedSLEPath κ xL xR ρL' ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
    have hcb : cb x = fun s => girsanovProcess B θ s ω := by
      show dec x.1 = _
      rw [hx1]
      exact Sec2.Assembly2.dec_enc_of_continuous hcω
    rw [hcb] at hpx
    have hup := hpx.isSLEPathUpTo (le_refl (cζ x))
    -- the canonical solution of the target law lives beyond `t`
    have htζ : ((t : ℝ≥0) : ℝ≥0∞) < cζ x := by
      by_contra hle
      push Not at hle
      have hxfin : cζ x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
      set t₀ : ℝ≥0 := (cζ x).toNNReal with ht₀
      have ht₀e : (t₀ : ℝ≥0∞) = cζ x := ENNReal.coe_toNNReal hxfin
      have ht₀t : t₀ ≤ (t : ℝ≥0) := by
        have : (t₀ : ℝ≥0∞) ≤ ((t : ℝ≥0) : ℝ≥0∞) := by rw [ht₀e]; exact hle
        exact_mod_cast this
      have hvLt₀ : VL 0 t₀ ω ≠ W t₀ ω := fun he => by
        have := hgap2 t₀ ht₀t; rw [he, sub_self] at this; linarith
      rcases eq_or_ne t₀ 0 with h0 | h0
      · have hz : cζ x = 0 := by rw [← ht₀e, h0]; rfl
        have h := hpx.isForcePath.threshold_of_eq_zero hz
        have hw0 : W t₀ ω = 0 := by rw [h0]; exact hpω.1
        have hl0 : VL 0 t₀ ω = xL 0 := by rw [h0]; exact hpω.vL_zero 0
        refine not_thresholdCondition_of_left hρR (ρL := ρL') ?_ h
        rw [← hw0, ← hl0]; exact hvLt₀
      · have hagree : ∀ r : ℝ≥0, r < t₀ → Agree (fun s => W s ω) (fun i s => VL i s ω)
            (fun j s => VR j s ω) (cw x) (cvL x) (cvR x) r := fun r hr =>
          UpTo.agree_of_lt_min hsep' hpω hpω.driverEq hup hup.driverEq (t := r)
            (lt_min (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (lt_of_lt_of_le hr ht₀t)) htτ.le)
              (by rw [← ht₀e]; exact ENNReal.coe_lt_coe.2 hr))
        have hst : Continuous fun s => (W s ω, fun i => VL i s ω, fun j => VR j s ω) := by
          refine hwc.prodMk ((continuous_pi fun i => ?_).prodMk (continuous_pi fun j => ?_))
          · rw [Fin.fin_one_eq_zero i]; exact hlc
          · rw [Fin.fin_one_eq_zero j]; exact hrc
        have hlim : Tendsto (fun s => (cw x s, fun i => cvL x i s, fun j => cvR x j s)) (𝓝[<] t₀)
            (𝓝 (W t₀ ω, fun i => VL i t₀ ω, fun j => VR j t₀ ω)) := by
          refine (hst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with r hr
          obtain ⟨h1, h2, h3⟩ := hagree r hr
          simp only [h1, h2, h3]
        exact not_thresholdCondition_of_left hρR hvLt₀
          (hpx.isForcePath.threshold_of_tendsto (pos_iff_ne_zero.2 h0) ht₀e hlim)
    have hagree : ∀ r : ℝ≥0, r ≤ (t : ℝ≥0) → W r ω = cw x r := fun r hr =>
      (UpTo.agree_of_lt_min hsep' hpω hpω.driverEq hup hup.driverEq (t := r)
        (lt_min (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) htτ)
          (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) htζ))).1
    -- the canonical code has the swallowing event
    obtain ⟨n, hn⟩ := exists_nat_ge (max M N)
    have hxS : x ∈ (allSet : Set (XCode 1 1)) := by
      show SwalAll (startOf x) (cw x) (cζ x)
      refine ⟨n, q, t, k, by rw [hxs]; exact hq, htζ, htN.trans_le ((le_max_right _ _).trans hn), ?_, ?_⟩
      · have hstp : LP3.stopPath (t : ℝ≥0) (cw x) = LP3.stopPath (t : ℝ≥0) (fun s => W s ω) := by
          funext r
          simp only [LP3.stopPath]
          exact (hagree _ (min_le_right _ _)).symm
        rw [hstp]; exact hal
      · intro u hu
        rw [← hagree u (by exact_mod_cast hu)]
        have := hlow u hu
        have hMn : M ≤ n := (le_max_left _ _).trans hn
        linarith
    exact ⟨x, ⟨⟨hxF, hxSep⟩, hxS⟩, hxeq⟩
  intro h0
  have h1 : P {ω | SwalWin M N (xL, xR) (fun t => W t ω) (ζ ω)} ≤ 0 := by
    calc P {ω | SwalWin M N (xL, xR) (fun t => W t ω) (ζ ω)} ≤ P (F ∩ univ) := measure_mono_ae hsub
      _ ≤ _ := hdens
      _ = 0 := by
          rw [hQF, h0, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero]
  exact hpos (le_antisymm h1 zero_le)

end InteractingSLE.LP.LP4S
