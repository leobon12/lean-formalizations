/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb6Ratio
import InteractingSLE.Spec.Sec7.ContinuityProb5Aux106
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# §7.3: Aux. lemma 106 when both weights exceed `−2` (`Aux106PositiveStatement`)

Packet PROVE-SEC7-C6. Specification pp. 354–355, Aux. lemma 106, "Suppose now that `a, b > 0`", by the route of
Astra's follow-up note §B.3 (ruling R38) with [Yua22] Corollary 1.3 for the restarted traces (the specification's own
final paragraph: "A continuous Loewner trace remains a continuous trace under its own mapping-out operation by
Corollary 1.3 of [Yua22] … Pull this trace back through the inverse hydrodynamic map of the actual finite prefix").

* `codeLaw_nt_eq_zero_of_twoSeed`: under the two-seed premise for the weights, the canonical probability of a
  non-transient trace vanishes at every strictly separated pair `(−L, R)` (the ratio restart of
  `ContinuityProb6Ratio.lean` on the canonical two-seed evolution, lifted to the universe of the premise; the ray
  constant by dilation of an evolution from `(−1, R/L)`).
* `ae_forall_rat_not_nonTransient`: for every evolution of a one-mark-per-side word (any start), almost surely at
  every positive rational time at which the driver is strictly between the marks, the restarted driver has no
  non-transient trace (the strong Markov restart at a constant time).
* **`aux106PositiveStatement`**: `Sec7.Aux106PositiveStatement` holds. Almost surely, on infinite lifetime, choose a
  positive rational time with the driver strictly between the marks (the collision sets are null); the restarted
  driver has a trace (Yuan), which is therefore transient, and transience passes back through the join.

The proof uses neither `κ < 4` nor the position of the marks: it holds for every word with one mark on each side and
weights `> −2`, given the two-seed premise for those weights.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace Positive

open ZhanGT4 Sec7.RandRestart

/-! ### The canonical non-transience probability vanishes off the seed -/

section Ray

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ}

/-- **The ray argument on a two-seed evolution in the universe of the premise**: if the canonical probability of a
non-transient trace is a constant `K` along the ray `(−L, r L)`, `L > 0`, then `K = 0`. -/
theorem eq_zero_of_twoSeed_evolution (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
    (h2 : LP.IsCompleteForceWord.{u} κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) ρL ρR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ) {r : ℝ} (hr : 0 < r)
    {K : ℝ≥0∞} (hdil : ∀ L : ℝ, 0 < L → codeLaw κ ρL ρR ntCodeSet ((fun _ => -L), fun _ => r * L) = K) :
    K = 0 := by
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := Sec2.Assembly2.ae_lifetime_eq_top_twoSeed hκ hE hρL hρR
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hgood : ∀ᵐ ω ∂P, GoodRatioSep r W VL VR ζ ω := by
    filter_upwards [hζ, ae_exists_ratioGap_eq_zero hκ hρL hρR hE hζ hr, h2 P 𝓕 W VL VR B ζ hE, hE.2.2.2.2]
      with ω hζω ⟨t₀, ht₀, hz⟩ ⟨η, hη, htr⟩ hp
    have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ζ ω} → Continuous f := fun hf =>
      continuousOn_univ.1 (hf.mono fun t _ => by
        show (t : ℝ≥0∞) < ζ ω
        rw [hζω]; exact ENNReal.coe_lt_top)
    have hwc := hcont hp.2.2.2.1
    have htr' := htr hζω
    rw [hζω] at hη
    refine ⟨hζω, hwc, hp.1, hcont (hp.2.2.2.2.1 0), hcont (hp.2.2.2.2.2.1 0), fun t ht => ?_, ⟨t₀, ht₀, hz⟩,
      ⟨η, hη⟩, fun η' hη' => ?_⟩
    · exact hp.vL_lt_vR_of_pos Zhan.isOrderedForceWord_zero ht (by rw [hζω]; exact ENNReal.coe_lt_top) 0 0
    · refine htr'.congr fun t => ?_
      rw [hη.eq_of_le hη' hwc.continuousOn hp.1 le_top]
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  exact eq_zero_of_restart_ratio_sep hκ hEa hr (N := N)
    (fun t => Ito.measurableSet_usualAugmentation_of_null hNm hN0 t) hN0
    (fun ω hω => by
      by_contra h
      exact hω (hNsub h)) hdil

/-- **The canonical probability of a non-transient trace is `0` at every strictly separated pair** `(−L, R)`,
`L, R > 0`, for weights `> −2`, given the two-seed premise for these weights (in any universe `u`). -/
theorem codeLaw_nt_eq_zero_of_twoSeed (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
    (h2 : LP.IsCompleteForceWord.{u} κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) ρL ρR)
    {L R : ℝ} (hL : 0 < L) (hR : 0 < R) :
    codeLaw κ ρL ρR ntCodeSet ((fun _ : Fin 1 => -L), fun _ : Fin 1 => R) = 0 := by
  set r : ℝ := R / L with hrdef
  have hr : 0 < r := div_pos hR hL
  -- the ray constant, by dilation of an evolution from `(−1, r)`
  have hF1 : IsOrderedForceWord (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => r) :=
    ⟨fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j], fun _ => by norm_num,
      fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j], fun _ => hr.le⟩
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hE₁⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hF1 (ρL := ρL) (ρR := ρR)
  have hζ₁ : ∀ᵐ ω ∂P₁, ζ₁ ω = ⊤ := Sec2.Assembly2.ae_lifetime_eq_top_twoSeed hκ hE₁ hρL hρR
  have hsep₁ : ∀ i j, (fun _ : Fin 1 => (-1 : ℝ)) i < (fun _ : Fin 1 => r) j := fun _ _ => by
    show (-1 : ℝ) < r
    linarith
  have hdil : ∀ L' : ℝ, 0 < L' → codeLaw κ ρL ρR ntCodeSet ((fun _ => -L'), fun _ => r * L') =
      codeLaw κ ρL ρR ntCodeSet ((fun _ => (-1 : ℝ)), fun _ => r) := by
    intro L' hL'
    set c : ℝ≥0 := ⟨(1 / L') ^ 2, by positivity⟩ with hcdef
    have hc : c ≠ 0 := by
      intro h
      have : (1 / L') ^ 2 = 0 := congrArg NNReal.toReal h
      exact (pow_pos (div_pos one_pos hL') 2).ne' this
    have hsc : (√(c : ℝ))⁻¹ = L' := by
      rw [show (c : ℝ) = (1 / L') ^ 2 from rfl, Real.sqrt_sq (div_pos one_pos hL').le, one_div, inv_inv]
    rw [← codeLaw_nt_dilate hκ hsep₁ hE₁ hζ₁ hc]
    congr 1
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · show -L' = (√(c : ℝ))⁻¹ * -1
      rw [hsc]; ring
    · show r * L' = (√(c : ℝ))⁻¹ * r
      rw [hsc]; ring
  -- the canonical two-seed evolution, lifted to the universe `u`
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ := Sec2.exists_isIntegratedSLEEvolution_twoSeed hκ
    (xL := fun _ => (0 : ℝ)) (xR := fun _ => (0 : ℝ)) (fun _ => rfl) (fun _ => rfl) ρL ρR
  have hdown : Measurable (ULift.down : ULift.{u} Ω₀ → Ω₀) := measurable_down
  have hup : Measurable (ULift.up : Ω₀ → ULift.{u} Ω₀) := measurable_up
  have hmap : (P₀.map ULift.up).map ULift.down = P₀ := by
    rw [Measure.map_map hdown hup]
    exact Measure.map_id
  have hE := isIntegratedSLEEvolution_comap hE₀ hdown hmap
  have : IsProbabilityMeasure (P₀.map (ULift.up : Ω₀ → ULift.{u} Ω₀)) :=
    ⟨by rw [Measure.map_apply hup MeasurableSet.univ, preimage_univ, measure_univ]⟩
  have hK := eq_zero_of_twoSeed_evolution hκ hρL hρR h2 hE hr hdil
  have hword : ((fun _ : Fin 1 => -L), fun _ : Fin 1 => R) = ((fun _ : Fin 1 => -L), fun _ : Fin 1 => r * L) := by
    refine Prod.ext rfl (funext fun _ => ?_)
    show R = R / L * L
    field_simp
  rw [hword, hdil L hL, hK]

end Ray

/-! ### The restart at positive rational times -/

section Rational

variable {κ : ℝ} {xL xR ρL ρR : Fin 1 → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **No non-transient restarted trace at positive rational times with the driver strictly between the marks**:
the strong Markov restart at the constant time `q`, where the restarted word is a strictly separated pair. -/
theorem ae_forall_rat_not_nonTransient [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hK : ∀ L R : ℝ, 0 < L → 0 < R →
      codeLaw κ ρL ρR ntCodeSet ((fun _ : Fin 1 => -L), fun _ : Fin 1 => R) = 0) :
    ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < q → (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω →
      VL 0 (q : ℝ).toNNReal ω < W (q : ℝ).toNNReal ω → W (q : ℝ).toNNReal ω < VR 0 (q : ℝ).toNNReal ω →
      ¬ NonTransientEvent (Sec7.shiftNN (fun t => W t ω) (q : ℝ).toNNReal) (ζ ω - (q : ℝ).toNNReal) := by
  rw [ae_all_iff]
  intro q
  by_cases hq : 0 < q
  swap
  · exact ae_of_all _ fun ω h => absurd h hq
  set t : ℝ≥0 := (q : ℝ).toNNReal with ht
  have ht0 : 0 < t := Real.toNNReal_pos.2 (by exact_mod_cast hq)
  set A : Set Ω := {ω | (t : ℝ≥0∞) < ζ ω ∧ VL 0 t ω < W t ω ∧ W t ω < VR 0 t ω} with hA
  have hS0 : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    have h := hE.2.1 t univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using h
  have hS1 := Band.measurableSet_lt_and_le_of_adaptedBefore hE.2.1 (hE.2.2.1 0) t 0
  have hS2 := Band.measurableSet_lt_and_le_of_adaptedBefore (hE.2.2.2.1 0) hE.2.1 t 0
  have hAeq : A = {ω | (t : ℝ≥0∞) < ζ ω} ∩ {ω | (t : ℝ≥0∞) < ζ ω ∧ W t ω - VL 0 t ω ≤ 0}ᶜ ∩
      {ω | (t : ℝ≥0∞) < ζ ω ∧ VR 0 t ω - W t ω ≤ 0}ᶜ := by
    ext ω
    simp only [hA, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_and, not_le, sub_pos]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, fun _ => h2⟩, fun _ => h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2 h1, h3 h1⟩
  have hAm : MeasurableSet[𝓕 t] A := by
    rw [hAeq]
    exact (hS0.inter hS1.compl).inter hS2.compl
  have hTs := isStoppingTime_const 𝓕 t
  have hA' : MeasurableSet[hTs.measurableSpace] A := by
    rw [IsStoppingTime.measurableSpace_const]
    exact hAm
  have hAT : ∀ ω ∈ A, (((fun _ : Ω => t) ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      (0 < (fun _ : Ω => t) ω ∨ ∀ i j, xL i < xR j) := fun ω hω => ⟨hω.1, Or.inl ht0⟩
  have hlaw := measure_restart_codeEvent hκ hE (T := fun _ => t) hTs hA' hAT
    (Φ := NonTransientEvent) measurableSet_ntCodeSet (fun _ _ _ => Iff.rfl) nonTransientEvent_congr
  have hAmeas : MeasurableSet A := 𝓕.le t _ hAm
  have hzero : ∫⁻ ω in A, codeLaw κ ρL ρR ntCodeSet (wordAt W VL VR (fun _ => t) ω) ∂P = 0 := by
    refine (setLIntegral_congr_fun hAmeas (fun ω hω => ?_)).trans lintegral_zero
    have hword : wordAt W VL VR (fun _ => t) ω =
        ((fun _ => -(W t ω - VL 0 t ω)), fun _ => VR 0 t ω - W t ω) := by
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · rw [Fin.fin_one_eq_zero i]
        simp only [wordAt]
        ring
      · rw [Fin.fin_one_eq_zero j]
        rfl
    rw [hword]
    exact hK _ _ (sub_pos.2 hω.2.1) (sub_pos.2 hω.2.2)
  rw [hzero] at hlaw
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hlaw] with ω hω _ h1 h2 h3 hnt
  exact hω ⟨⟨h1, h2, h3⟩, hnt⟩

end Rational

/-! ### Aux. lemma 106 when both weights exceed `−2` -/

/-- **Transience for one mark on each side with weights `> −2`, from the two-seed premise for these weights** (any
start, any `κ > 0`): almost surely, on infinite lifetime, every continuous generating trace on `[0, ∞)` tends to
infinity. -/
theorem ae_tendsto_of_twoSeed {κ : ℝ} (hκ : 0 < κ) {xL xR ρL ρR : Fin 1 → ℝ} (hρL : -2 < ρL 0)
    (hρR : -2 < ρR 0)
    (h2 : LP.IsCompleteForceWord.{u} κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) ρL ρR)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have hK : ∀ L R : ℝ, 0 < L → 0 < R →
      codeLaw κ ρL ρR ntCodeSet ((fun _ : Fin 1 => -L), fun _ : Fin 1 => R) = 0 :=
    fun _ _ hL hR => codeLaw_nt_eq_zero_of_twoSeed hκ hρL hρR h2 hL hR
  filter_upwards [ae_forall_rat_not_nonTransient hκ hE hK, hE.2.2.2.2] with ω hrat hp hζω η hη
  have hlt : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω := fun s => by rw [hζω]; exact ENNReal.coe_lt_top
  have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ζ ω} → Continuous f := fun hf =>
    continuousOn_univ.1 (hf.mono fun t _ => hlt t)
  obtain ⟨hw0, -, -, hcw, hcl, hcr, -, hlw, hwr, -, -, -, -, -, -, hcL, hcR, -⟩ := hp
  have hwc := hcont hcw
  -- a positive rational time with the driver strictly between the marks
  have hcL' : volume {s : ℝ | 0 ≤ s ∧ W s.toNNReal ω = VL 0 s.toNNReal ω} = 0 := by
    refine measure_mono_null ?_ (hcL 0)
    intro s hs
    exact ⟨hs.1, hlt _, hs.2⟩
  have hcR' : volume {s : ℝ | 0 ≤ s ∧ W s.toNNReal ω = VR 0 s.toNNReal ω} = 0 := by
    refine measure_mono_null ?_ (hcR 0)
    intro s hs
    exact ⟨hs.1, hlt _, hs.2⟩
  obtain ⟨q, hq, h1, h2⟩ := exists_rat_lt_sep hwc (hcont (hcl 0)) (hcont (hcr 0))
    (fun s => hlw s (hlt s) 0) (fun s => hwr s (hlt s) 0) hcL' hcR'
  -- the restarted driver has a trace, which is transient; transience passes back
  have hnt := hrat q hq (hlt _) h1 h2
  rw [hζω, ENNReal.top_sub_coe] at hnt
  have hwc₂ : Continuous (Sec7.shiftNN (fun t => W t ω) (q : ℝ).toNNReal) :=
    (hwc.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [nonTransientEvent_iff hwc₂ (Sec7.shiftNN_zero _ _)] at hnt
  have hhas := exists_isGeneratingTrace_shiftNN_of_isGeneratingTrace hwc hw0 hη (q : ℝ).toNNReal
  have htt : HasTransTrace (Sec7.shiftNN (fun t => W t ω) (q : ℝ).toNNReal) := by
    by_contra h
    exact hnt ⟨hhas, h⟩
  exact tendsto_norm_of_hasTransTrace_shiftNN hwc hw0 htt hη

/-- **`Sec7.Aux106PositiveStatement`** (Specification pp. 354–355, Aux. lemma 106 when `a, b > 0`). -/
theorem aux106PositiveStatement : Aux106PositiveStatement.{u} := by
  intro κ hκ _ h2 xL xR ρL ρR _ _ hρL hρR Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have h2' : LP.IsCompleteForceWord.{u} κ (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) ρL ρR :=
    h2 _ _ ρL ρR (fun _ => rfl) (fun _ => rfl) (fun i => by rw [Fin.fin_one_eq_zero i]; exact hρL)
      (fun i => by rw [Fin.fin_one_eq_zero i]; exact hρR)
  exact ae_tendsto_of_twoSeed hκ hρL hρR h2' hE

end Positive

end Sec7

end InteractingSLE
