/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb6Positive
import InteractingSLE.Spec.Sec7.ContinuityProb2Aux99

/-!
# Wang–Wu Lemma 5.1: one force point away from the start, from the adjacent seed

Packet PROVE-WW-C2. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §5.1, Lemma 5.1
(text dump L1945–L1985):

> **Lemma 5.1** (One force point away from the start). Assume the continuous, simple, transient adjacent-force seed
> `SLE₄(0; ρ)` is available for every `ρ > −2`, together with its force-point strong Markov property. Then the
> corresponding one-force-point process with force point at any `x > 0` is simple, continuous, and transient for
> `ρ > −2`, and almost surely does not visit its marked force point. For `ρ ≤ −2` it is continuous up to its
> threshold, with endpoint `x`.
>
> *Proof.* For `ρ > −2`, take the adjacent-force seed and stop at deterministic time 1. Its right gap
> `A = V^R_1 − W_1` is positive almost surely. […] Conditional on the prefix, the future, mapped by `(g_1 − W_1)/A`, has
> the one-force-point law with force point `1` by the strong Markov property and scaling. The transformed future is
> continuous. […] At infinity the hydrodynamic normalization gives `g_1(z) − W_1 = z + O(1)`, so transience is
> preserved. […] Scaling replaces `1` by any `x > 0`.

This file proves the continuity and transience assertion of the case `ρ > −2`, for every `κ > 0` (the source's
argument uses `κ = 4` nowhere), in the form used by the finite-force inductions: the word with one right mark at
`x > 0` is complete (`LP.IsCompleteForceWord`) as soon as the seed word with the same weight is. The steps are the
source's, with two substitutions:

* "the future is continuous" (the source: the simple future is disjoint from the compact past, and the conformal map is
  continuous along it) is [Yua22] Corollary 1.3 (`Sec7.Positive.exists_isGeneratingTrace_shiftNN_of_isGeneratingTrace`:
  a continuous Loewner trace stays a continuous trace under its own mapping-out), and its transience is the
  hydrodynamic normalization (`ZhanGT4.tendsto_norm_of_shift`);
* the restart is at a positive rational time `q` with `W_q < V_q` (instead of the time `1`, at which the gap is
  positive almost surely), on the event `A_q = {W_q < V_q}`; the canonical law of the restarted word is
  `Sec7.RandRestart.measure_restart_codeEvent`, and "scaling replaces `1` by any `x > 0`" is the dilation invariance
  of the canonical law of the no-trace event (`codeLaw_noTrace_dilate`, the dilation of an evolution
  `IsIntegratedSLEEvolution.dilate`). Some `A_q` has positive probability because the collision set is Lebesgue-null.

The simplicity and the avoidance of the marked point are not needed downstream and are not proved. The case
`ρ ≤ −2` (retargeting at `x` by Lemma 2.2) needs the integrated target-change identity; it is the named statement
`OneRightNonAdmissibleStatement`, which Aux. lemma 99 implies (`oneRightNonAdmissibleStatement_of_stopped`).

## Main results

* `traceEvent_top_iff`, `codeLaw_noTrace_dilate`: dilation invariance of the canonical no-trace probability.
* **`isCompleteForceWord_oneRight_of_seed`** (Lemma 5.1, `ρ > −2`, every `κ > 0`).
* `isCompleteForceWord_seedRight_of_twoSeed`: the seed one-force word from the two-seed premise (`LP.TwoSeedComplete`),
  every `κ > 0` (the left seed of weight `0` is forgotten; Theorem 2.2's one-force uniqueness transfers the trace).
* `OneRightNonAdmissibleStatement` (Lemma 5.1, `ρ ≤ −2`, as a named statement) and
  `oneRightNonAdmissibleStatement_of_stopped`.
* **`oneForceStatement_of_seed`**: LP10's one-force base `LP.OneForceStatement κ` from the seed theorem and the
  case `ρ ≤ −2` alone; **`oneForceStatement_of_twoSeed`**: the same from the two-seed premise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.Lemma51

open Sec7 Sec7.RandRestart ZhanGT4 Sec7.Dilation

/-! ### Dilation invariance of the canonical no-trace probability -/

/-- On an infinite horizon the trace event is the existence of a transient generating trace. -/
theorem traceEvent_top_iff {w : ℝ≥0 → ℝ} : TraceEvent w ⊤ ↔ HasTransTrace w := by
  constructor
  · rintro ⟨η, hη, htr⟩
    exact ⟨η, hη, htr rfl⟩
  · rintro ⟨η, hη, htr⟩
    exact ⟨η, hη, fun _ => htr⟩

/-- **Dilation invariance of the canonical no-trace probability** ("scaling replaces `1` by any `x > 0`"): if the
separated word `(xL, xR)` has an evolution with infinite lifetime, the canonical probability that the driver has no
transient continuous generating trace is the same at `λ (xL, xR)` for every `λ > 0` (here `λ = (√c)⁻¹`). -/
theorem codeLaw_noTrace_dilate {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hκ : 0 < κ) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {c : ℝ≥0}
    (hc : c ≠ 0) :
    codeLaw κ ρL ρR (traceCodeSet (nL := nL) (nR := nR))ᶜ
        ((fun i => (√(c : ℝ))⁻¹ * xL i), fun j => (√(c : ℝ))⁻¹ * xR j) =
      codeLaw κ ρL ρR (traceCodeSet (nL := nL) (nR := nR))ᶜ (xL, xR) := by
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hs : 0 < (√(c : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hc')
  have hsep' : ∀ i j, (√(c : ℝ))⁻¹ * xL i < (√(c : ℝ))⁻¹ * xR j := fun i j =>
    mul_lt_mul_of_pos_left (hsep i j) hs
  rw [← measure_eventOf_eq_codeLaw hκ hsep' (hE.dilate hc) measurableSet_traceCodeSet.compl
      compl_traceCodeSet_iff not_traceEvent_congr,
    ← measure_eventOf_eq_codeLaw hκ hsep hE measurableSet_traceCodeSet.compl compl_traceCodeSet_iff
      not_traceEvent_congr]
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [hζ] with ω hζω
  show ¬ TraceEvent (dilPath c fun t => W t ω) (ζ ω / c) ↔ ¬ TraceEvent (fun t => W t ω) (ζ ω)
  rw [hζω, ENNReal.top_div_of_ne_top ENNReal.coe_ne_top, traceEvent_top_iff, traceEvent_top_iff,
    hasTransTrace_dilPath_iff hc]

/-! ### Lemma 5.1 for `ρ > −2` -/

/-- The ordered one-mark words `(∅; x)`, `x ≥ 0`. -/
theorem isOrderedForceWord_oneRight {xL : Fin 0 → ℝ} {xR : Fin 1 → ℝ} (hx : 0 ≤ xR 0) :
    IsOrderedForceWord xL xR :=
  ⟨fun i _ _ => i.elim0, fun i => i.elim0,
    fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j], fun j => by
      rw [Fin.fin_one_eq_zero j]; exact hx⟩

/-- **The ray** ("scaling replaces `1` by any `x > 0`"): for `ρ > −2` the canonical probability of no transient trace
is the same at every one-mark word `(∅; y)`, `y > 0`. -/
theorem codeLaw_noTrace_ray {κ : ℝ} (hκ : 0 < κ) {xL ρL : Fin 0 → ℝ} {xR ρR : Fin 1 → ℝ} (hx : 0 < xR 0)
    (hρ : -2 < ρR 0) (yL : Fin 0 → ℝ) (yR : Fin 1 → ℝ) (hy : 0 < yR 0) :
    codeLaw κ ρL ρR (traceCodeSet (nL := 0) (nR := 1))ᶜ (yL, yR) =
      codeLaw κ ρL ρR (traceCodeSet (nL := 0) (nR := 1))ᶜ (xL, xR) := by
  obtain ⟨Ω₁, m₁, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hE₁⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ (isOrderedForceWord_oneRight (xL := xL) hx.le)
      (ρL := ρL) (ρR := ρR)
  have hζ₁ : ∀ᵐ ω ∂P₁, ζ₁ ω = ⊤ := Sec7.ae_lifetime_eq_top_oneForceRight hκ hx.le hρ hE₁
  have hq : 0 < xR 0 / yR 0 := div_pos hx hy
  set c : ℝ≥0 := ⟨(xR 0 / yR 0) ^ 2, by positivity⟩ with hcdef
  have hc : c ≠ 0 := by
    intro h
    have : (xR 0 / yR 0) ^ 2 = 0 := congrArg NNReal.toReal h
    exact (pow_pos hq 2).ne' this
  have hsc : (√(c : ℝ))⁻¹ * xR 0 = yR 0 := by
    rw [show (c : ℝ) = (xR 0 / yR 0) ^ 2 from rfl, Real.sqrt_sq hq.le, inv_div,
      div_mul_cancel₀ _ hx.ne']
  rw [← codeLaw_noTrace_dilate hκ (fun i => i.elim0) hE₁ hζ₁ hc]
  congr 1
  refine Prod.ext (funext fun i => i.elim0) (funext fun j => ?_)
  rw [Fin.fin_one_eq_zero j]
  exact hsc.symm

/-- **The restart at a positive rational time** (the core of the proof of Lemma 5.1, `ρ > −2`). On a seed evolution
whose driver has a transient trace, if the canonical probability of no transient trace is a constant `K` along the
one-mark words `(∅; y)`, `y > 0`, then `K = 0`. At a positive rational time `q` restart on `A_q = {W_q < V_q}`: by
[Yua22] Corollary 1.3 the restarted driver has a continuous trace, transient by the hydrodynamic normalization, so
`K · P(A_q) = P(A_q ∩ {no trace after q}) = 0`; some `A_q` has positive probability since the collision set is
Lebesgue-null. -/
theorem eq_zero_of_seed_evolution {κ : ℝ} (hκ : 0 < κ) {xL ρL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ} (hρ : -2 < ρR 0)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, TraceEvent (fun t => W t ω) (ζ ω)) {K : ℝ≥0∞}
    (hK : ∀ (yL : Fin 0 → ℝ) (yR : Fin 1 → ℝ), 0 < yR 0 →
      codeLaw κ ρL ρR (traceCodeSet (nL := 0) (nR := 1))ᶜ (yL, yR) = K) : K = 0 := by
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := Sec7.ae_lifetime_eq_top_oneForceRight hκ le_rfl hρ hE
  -- the good paths
  have hgood : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ TraceEvent (fun t => W t ω) (ζ ω) ∧
      IsIntegratedSLEPath κ xL (fun _ => 0) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun j t => VR j t ω) (fun t => B t ω) (ζ ω) := by
    filter_upwards [hζ, htr, hE.2.2.2.2] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- the restart at each positive rational time
  have hA : ∀ q : ℚ, 0 < q → K * P {ω | (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      W (q : ℝ).toNNReal ω < VR 0 (q : ℝ).toNNReal ω} = 0 := by
    intro q hq
    set t : ℝ≥0 := (q : ℝ).toNNReal with ht
    have ht0 : 0 < t := Real.toNNReal_pos.2 (by exact_mod_cast hq)
    set A : Set Ω := {ω | (t : ℝ≥0∞) < ζ ω ∧ W t ω < VR 0 t ω} with hAdef
    have hS0 : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
      have h := hE.2.1 t univ MeasurableSet.univ
      simpa only [mem_univ, and_true] using h
    have hS2 := Band.measurableSet_lt_and_le_of_adaptedBefore (hE.2.2.2.1 0) hE.2.1 t 0
    have hAeq : A = {ω | (t : ℝ≥0∞) < ζ ω} ∩ {ω | (t : ℝ≥0∞) < ζ ω ∧ VR 0 t ω - W t ω ≤ 0}ᶜ := by
      ext ω
      simp only [hAdef, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_and, not_le, sub_pos]
      exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
    have hAm : MeasurableSet[𝓕 t] A := by
      rw [hAeq]
      exact hS0.inter hS2.compl
    have hTs := isStoppingTime_const 𝓕 t
    have hA' : MeasurableSet[hTs.measurableSpace] A := by
      rw [IsStoppingTime.measurableSpace_const]
      exact hAm
    have hAT : ∀ ω ∈ A, (((fun _ : Ω => t) ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        (0 < (fun _ : Ω => t) ω ∨ ∀ i j, xL i < (fun _ : Fin 1 => (0 : ℝ)) j) := fun ω hω =>
      ⟨hω.1, Or.inl ht0⟩
    have hlaw := measure_restart_codeEvent hκ hE (T := fun _ => t) hTs hA' hAT
      (Φ := fun w τ => ¬ TraceEvent w τ) measurableSet_traceCodeSet.compl compl_traceCodeSet_iff
      not_traceEvent_congr
    have hAmeas : MeasurableSet A := 𝓕.le t _ hAm
    -- the realized word lies on the ray
    have hR : ∫⁻ ω in A, codeLaw κ ρL ρR (traceCodeSet (nL := 0) (nR := 1))ᶜ
        (wordAt W VL VR (fun _ => t) ω) ∂P = K * P A := by
      rw [← setLIntegral_const]
      refine setLIntegral_congr_fun hAmeas fun ω hω => ?_
      exact hK _ _ (sub_pos.2 hω.2)
    -- the restarted driver has the trace event
    have hL : P (A ∩ {ω | ¬ TraceEvent (fun s => W (t + s) ω - W t ω) (ζ ω - t)}) = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hgood)
      obtain ⟨-, hnt⟩ := hω
      intro hg
      obtain ⟨hζω, hη0, hp⟩ := hg
      apply hnt
      have hwc : Continuous fun s => W s ω := by
        have h := hp.2.2.2.1
        rw [hζω] at h
        exact continuousOn_univ.1 (h.mono fun s _ => ENNReal.coe_lt_top)
      rw [hζω] at hη0
      obtain ⟨η, hη, hηt⟩ := hη0
      obtain ⟨η₂, hη₂⟩ := Positive.exists_isGeneratingTrace_shiftNN_of_isGeneratingTrace hwc hp.1 hη t
      rw [hζω, ENNReal.top_sub_coe]
      exact ⟨η₂, hη₂, fun _ => tendsto_norm_of_shift hwc hp.1 hη (hηt rfl) hη₂⟩
    rw [← hR, ← hlaw, hL]
  -- some restart event has positive probability
  have hcover : ∀ᵐ ω ∂P, ∃ q : ℚ, 0 < q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      W (q : ℝ).toNNReal ω < VR 0 (q : ℝ).toNNReal ω := by
    filter_upwards [hgood] with ω ⟨hζω, _, hp⟩
    have hlt : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω := fun s => by rw [hζω]; exact ENNReal.coe_lt_top
    have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ζ ω} → Continuous f := fun hf =>
      continuousOn_univ.1 (hf.mono fun t _ => hlt t)
    obtain ⟨hw0, -, -, hcw, -, hcr, -, -, hwr, -, -, -, -, -, -, -, hcR, -⟩ := hp
    have hwc := hcont hcw
    have hcR' : volume {s : ℝ | 0 ≤ s ∧ W s.toNNReal ω = VR 0 s.toNNReal ω} = 0 := by
      refine measure_mono_null ?_ (hcR 0)
      intro s hs
      exact ⟨hs.1, hlt _, hs.2⟩
    have hcL' : volume {s : ℝ | 0 ≤ s ∧ W s.toNNReal ω = W s.toNNReal ω - 1} = 0 := by
      refine measure_mono_null (fun s hs => ?_) measure_empty
      have := hs.2
      linarith
    obtain ⟨q, hq, -, h2⟩ := Positive.exists_rat_lt_sep (vL := fun s => W s ω - 1) hwc
      (hwc.sub continuous_const) (hcont (hcr 0)) (fun s => sub_le_self _ zero_le_one)
      (fun s => hwr s (hlt s) 0) hcL' hcR'
    exact ⟨q, hq, hlt _, h2⟩
  by_contra hK0
  have hA0 : ∀ q : ℚ, 0 < q → P {ω | (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      W (q : ℝ).toNNReal ω < VR 0 (q : ℝ).toNNReal ω} = 0 := fun q hq =>
    (mul_eq_zero.1 (hA q hq)).resolve_left hK0
  have hnull : P {ω | ∃ q : ℚ, 0 < q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      W (q : ℝ).toNNReal ω < VR 0 (q : ℝ).toNNReal ω} = 0 := by
    have hsub : {ω | ∃ q : ℚ, 0 < q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        W (q : ℝ).toNNReal ω < VR 0 (q : ℝ).toNNReal ω} ⊆ ⋃ q : {q : ℚ // 0 < q},
        {ω | ((((q : ℚ) : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
          W ((q : ℚ) : ℝ).toNNReal ω < VR 0 ((q : ℚ) : ℝ).toNNReal ω} := by
      rintro ω ⟨q, hq, h⟩
      exact mem_iUnion.2 ⟨⟨q, hq⟩, h⟩
    exact measure_mono_null hsub (measure_iUnion_null fun q => hA0 q q.2)
  have h1 : P {ω | ∃ q : ℚ, 0 < q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      W (q : ℝ).toNNReal ω < VR 0 (q : ℝ).toNNReal ω}ᶜ = 0 := ae_iff.1 hcover
  have := measure_union_le (μ := P) {ω | ∃ q : ℚ, 0 < q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      W (q : ℝ).toNNReal ω < VR 0 (q : ℝ).toNNReal ω}
    {ω | ∃ q : ℚ, 0 < q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      W (q : ℝ).toNNReal ω < VR 0 (q : ℝ).toNNReal ω}ᶜ
  rw [union_compl_self, measure_univ, hnull, h1, add_zero] at this
  exact absurd this (by norm_num)

/-- **Wang–Wu, Lemma 5.1, the case `ρ > −2`** (continuity and transience; every `κ > 0`). If the seed word with one
right mark at `0⁺` of weight `ρ > −2` is complete, so is the word with one right mark at any `x > 0` of the same
weight: every integrated evolution almost surely has a continuous generating trace up to its lifetime, transient on
infinite lifetime. -/
theorem isCompleteForceWord_oneRight_of_seed {κ : ℝ} (hκ : 0 < κ) {xL ρL : Fin 0 → ℝ} {xR ρR : Fin 1 → ℝ}
    (hx : 0 < xR 0) (hρ : -2 < ρR 0) (hseed : LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR) :
    LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  -- the seed evolution, lifted to the universe `u`
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ
      (isOrderedForceWord_oneRight (xL := xL) (xR := fun _ => 0) le_rfl) (ρL := ρL) (ρR := ρR)
  have hdown : Measurable (ULift.down : ULift.{u} Ω₀ → Ω₀) := measurable_down
  have hup : Measurable (ULift.up : Ω₀ → ULift.{u} Ω₀) := measurable_up
  have hmap : (P₀.map ULift.up).map ULift.down = P₀ := by
    rw [Measure.map_map hdown hup]
    exact Measure.map_id
  have hE₁ := isIntegratedSLEEvolution_comap hE₀ hdown hmap
  have : IsProbabilityMeasure (P₀.map (ULift.up : Ω₀ → ULift.{u} Ω₀)) :=
    ⟨by rw [Measure.map_apply hup MeasurableSet.univ, preimage_univ, measure_univ]⟩
  have htr₁ : ∀ᵐ ω ∂(P₀.map (ULift.up : Ω₀ → ULift.{u} Ω₀)),
      TraceEvent (fun t => W₀ t ω.down) (ζ₀ ω.down) := hseed _ _ _ _ _ _ _ hE₁
  -- the canonical probability of no transient trace vanishes on the ray, in particular at `x`
  have hK0 := eq_zero_of_seed_evolution hκ hρ hE₁ htr₁ (codeLaw_noTrace_ray (xL := xL) hκ hx hρ)
  -- every evolution from `x`
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have e := measure_eventOf_eq_codeLaw hκ (fun i => i.elim0) hE (Φ := fun w τ => ¬ TraceEvent w τ)
    measurableSet_traceCodeSet.compl compl_traceCodeSet_iff not_traceEvent_congr
  rw [hK0] at e
  exact ae_iff.2 e

/-- **The seed one-force word from the two-seed premise** (every `κ > 0`; WW: "Insert zero-weight points at `0−` and
`0+` when a later argument requires them. They change neither the drift nor the boundary function"). A two-seed
evolution with weights `(0; ρ)` (Theorem 2.2), lifted to the universe `u`, has a transient trace (the premise) and
infinite lifetime; forgetting its zero-weight left mark gives a one-mark evolution, and Theorem 2.2's one-force
uniqueness in law transfers the coded trace event (`Sec7.ae_transfer_of_killedState`). -/
theorem isCompleteForceWord_seedRight_of_twoSeed {κ : ℝ} (hκ : 0 < κ) (h2 : LP.TwoSeedComplete.{u} κ)
    (xL ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ) (hρ : -2 < ρR 0) :
    LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR := by
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ := Sec2.exists_isIntegratedSLEEvolution_twoSeed hκ
    (xL := fun _ => (0 : ℝ)) (xR := fun _ => (0 : ℝ)) (fun _ => rfl) (fun _ => rfl) (fun _ => (0 : ℝ))
    (fun _ => ρR 0)
  have hdown : Measurable (ULift.down : ULift.{u} Ω₀ → Ω₀) := measurable_down
  have hup : Measurable (ULift.up : Ω₀ → ULift.{u} Ω₀) := measurable_up
  have hmap : (P₀.map ULift.up).map ULift.down = P₀ := by
    rw [Measure.map_map hdown hup]
    exact Measure.map_id
  have hE₁ := isIntegratedSLEEvolution_comap hE₀ hdown hmap
  have : IsProbabilityMeasure (P₀.map (ULift.up : Ω₀ → ULift.{u} Ω₀)) :=
    ⟨by rw [Measure.map_apply hup MeasurableSet.univ, preimage_univ, measure_univ]⟩
  have htr₁ := h2 0 (ρR 0) (by norm_num) hρ _ _ _ _ _ _ _ hE₁
  have hζ₁ := Sec2.Assembly2.ae_lifetime_eq_top_twoSeed hκ hE₁ (by norm_num) hρ
  have hE₂ := IsIntegratedSLEEvolution.forgetLeft_of_top (fun _ => rfl) hE₁ hζ₁ xL ρL (fun i => i.elim0)
  -- an arbitrary evolution of the seed word
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := Sec7.ae_lifetime_eq_top_oneForceRight hκ le_rfl hρ hE
  have hρeq : ρR = fun _ => ρR 0 := funext fun i => by rw [Fin.fin_one_eq_zero i]
  rw [hρeq] at hE
  have hF : IsOrderedForceWord xL (fun _ : Fin 1 => (0 : ℝ)) := isOrderedForceWord_oneRight le_rfl
  obtain ⟨G, hG, hGp⟩ := transientTraceCodingStatement
  rw [hasTransientGeneratingTrace_iff_of_top hζ]
  exact ae_transfer_of_killedState (p := IsTransientDriver) hG hGp hE₂ hζ₁
    ((hasTransientGeneratingTrace_iff_of_top hζ₁).1 htr₁) hE hζ
    (fun n ts A hA => OneForce.measure_killedState_eq_right hκ hF hE₂ hE n ts A hA)

/-! ### The one-force base of the finite-force inductions -/

/-- **Named statement: Wang–Wu, Lemma 5.1, the case `ρ ≤ −2`** ("For `ρ ≤ −2` it is continuous up to its
threshold, with endpoint `x`"; the source's proof retargets at `x` by Lemma 2.2, so that the old target becomes a left
mark of weight `−2 − ρ ≥ 0` at `−x`; the non-boundary-intersecting seed gives a continuous transient transformed trace,
whose inverse image lands at `x` with finite capacity). One right mark at `x > 0` with weight `ρ ≤ −2` gives a
complete word. The stopped Aux. lemma 99 implies it (`oneRightNonAdmissibleStatement_of_stopped`). -/
def OneRightNonAdmissibleStatement (κ : ℝ) : Prop :=
  ∀ (xL ρL : Fin 0 → ℝ) (xR ρR : Fin 1 → ℝ), 0 < xR 0 → ρR 0 ≤ -2 → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- The stopped Aux. lemma 99 gives the case `ρ ≤ −2` of Lemma 5.1 (no continuation after the first swallow is
needed: the swallow is the continuation threshold). -/
theorem oneRightNonAdmissibleStatement_of_stopped {κ : ℝ} (h99 : Sec7.Aux99StoppedStatement.{u} κ) :
    OneRightNonAdmissibleStatement.{u} κ := fun _ _ _ _ hx hρ =>
  Sec7.isCompleteForceWord_oneRight_of_stopped h99 hx fun h => absurd h (not_lt.2 hρ)

/-- **The one-force base `LP.OneForceStatement κ` of LP10's induction from the seed theorem and the case `ρ ≤ −2`**
(every `κ > 0`): one right mark at `x ≥ 0`, any weight. At the seed: the seed theorem, or lifetime `0`; away from the
seed: Lemma 5.1 (`isCompleteForceWord_oneRight_of_seed` for `ρ > −2`, the named case for `ρ ≤ −2`). -/
theorem oneForceStatement_of_seed {κ : ℝ} (hκ : 0 < κ)
    (hseed : ∀ (xL ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ), -2 < ρR 0 →
      LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR)
    (hna : OneRightNonAdmissibleStatement.{u} κ) : LP.OneForceStatement.{u} κ := by
  intro xL ρL xR ρR hx
  rcases hx.lt_or_eq with hpos | hzero
  · rcases lt_or_ge (-2) (ρR 0) with h | h
    · exact isCompleteForceWord_oneRight_of_seed hκ hpos h (hseed xL ρL ρR h)
    · exact hna xL ρL xR ρR hpos h
  · have hxR : xR = fun _ => 0 := funext fun i => by
      rw [Fin.fin_one_eq_zero i]
      exact hzero.symm
    subst hxR
    intro Ω mΩ
    rcases lt_or_ge (-2) (ρR 0) with h | h
    · exact hseed xL ρL ρR h
    · exact Sec7.isCompleteForceWord_seed_of_le h

/-- **The one-force base from the two-seed premise and the case `ρ ≤ −2`** (every `κ > 0`). -/
theorem oneForceStatement_of_twoSeed {κ : ℝ} (hκ : 0 < κ) (h2 : LP.TwoSeedComplete.{u} κ)
    (hna : OneRightNonAdmissibleStatement.{u} κ) : LP.OneForceStatement.{u} κ :=
  oneForceStatement_of_seed hκ (fun xL ρL ρR h => isCompleteForceWord_seedRight_of_twoSeed hκ h2 xL ρL ρR h) hna

end InteractingSLE.WangWu.Lemma51
