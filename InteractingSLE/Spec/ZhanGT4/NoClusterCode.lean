/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.NoClusterGirsanov

/-!
# Lemma 3.4: code events that read the start, and the band event

Packet PROVE-ZHAN-GT4-B2. The restart kernel of §7.3 (`Sec7.RandRestart.measure_restart_codeEvent`,
`measure_eventOf_eq_codeLaw`) transfers events of the restarted *driver*. The band event of Lemma 3.4 ("the future has a
real terminal cluster point within the fraction `θ` of the gap next to one of its marks") also reads the restarted
*start* (the word `V_T − W_T`), which a canonical solution code records (`Sec2.Assembly.startOf`). This file proves the
two transfer identities for events `Φ s w τ` of (start, driver, lifetime), and sets up the band event: its Borel coding
through rational trace values, its real-time form for continuous traces, its dilation invariance, and the continuity of
its canonical probability as the fraction `θ` decreases.

## Main results

* `measure_eventOf_eq_codeLawS`, `measure_restart_codeEventS`: the canonical and conditional laws of start-dependent
  code events.
* `dIcc`: the distance from `z` to a real interval; `bandDist θ s z`; `BandEvent θ s w τ`; `bandCodeSet θ` (Borel).
* `bandEvent_iff`: for a continuous driver with a generating trace `η` on `[0, ∞)`, the band event says
  `∀ ε > 0, ∀ N, ∃ t ≥ N, bandDist θ s (η t) < ε`.
* `codeLaw_band_dilate`: dilation invariance.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart QuantumZipper.StrongMarkov

/-! ### Start-dependent code events -/

section StartCode

variable {nL nR : ℕ} {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The canonical law of a start-dependent coded event** (`measure_eventOf_eq_codeLaw` with `Φ` reading the start). -/
theorem measure_eventOf_eq_codeLawS [IsProbabilityMeasure P] (ha : 0 < a) (hsep : ∀ i j, xL i < xR j)
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {S : Set (XCode nL nR)}
    {Φ : (Fin nL → ℝ) × (Fin nR → ℝ) → (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} (hS : MeasurableSet S)
    (hSΦ : ∀ x ∈ CRelF a ρL ρR, HasLimW x → (x ∈ S ↔ Φ (startOf x) (cw x) (cζ x)))
    (hΦ : ∀ (s : (Fin nL → ℝ) × (Fin nR → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞),
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) → Φ s w τ → Φ s w' τ) :
    P {ω | Φ (xL, xR) (fun t => W t ω) (ζ ω)} = codeLaw a ρL ρR S (xL, xR) := by
  obtain ⟨B', hm, hc, -, hbm, hae⟩ := QuantumZipper.RS.exists_good_version0 h.1.1
  have hpm : Measurable fun ω (s : ℝ≥0) => B' s ω := measurable_pi_iff.2 hm
  rw [codeLaw, ← map_path_eq_wienerPath hbm.toIsPreBrownianReal hpm,
    Measure.map_apply hpm ((measurableSet_restartSetS hS).preimage measurable_prodMk_left)]
  refine measure_congr ?_
  filter_upwards [ae_codeOf_mem ha h hc hae, h.ae_tendsto_threshold ha] with ω ⟨hmem, hdec⟩ hl
  set x := codeOf xL xR B' W VL VR ζ ω with hx
  have hx1 : x.1 = enc (B' · ω) := rfl
  have hxζ : cζ x = ζ ω := rfl
  have hxF : x ∈ CRelF a ρL ρR := (mem_cRelF_iff.2 hmem).1
  have hxs : startOf x = (xL, xR) := (mem_cRelF_iff.2 hmem).2
  have hxl : HasLimW x := hasLimW_of_tendsto (fun t ht => (hdec t ht).1) hl
  refine propext ?_
  show Φ (xL, xR) (fun t => W t ω) (ζ ω) ↔ ((xL, xR), enc (B' · ω)) ∈ lawSetS a ρL ρR S
  rw [← hx1, mem_lawSetS_iff hsep hmem, hSΦ x hxF hxl, hxζ, hxs]
  exact ⟨hΦ _ _ _ _ fun t ht => ((hdec t ht).1).symm, hΦ _ _ _ _ fun t ht => (hdec t ht).1⟩

/-- **The conditional law of a start-dependent coded event of the restarted evolution**
(`measure_restart_codeEvent` with `Φ` reading the restarted start `V_T − W_T`). -/
theorem measure_restart_codeEventS (ha : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j))
    {S : Set (XCode nL nR)} {Φ : (Fin nL → ℝ) × (Fin nR → ℝ) → (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop}
    (hS : MeasurableSet S)
    (hSΦ : ∀ x ∈ CRelF a ρL ρR, HasLimW x → (x ∈ S ↔ Φ (startOf x) (cw x) (cζ x)))
    (hΦ : ∀ (s : (Fin nL → ℝ) × (Fin nR → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞),
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) → Φ s w τ → Φ s w' τ) :
    P (A ∩ {ω | Φ (wordAt W VL VR T ω) (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)}) =
      ∫⁻ ω in A, codeLaw a ρL ρR S (wordAt W VL VR T ω) ∂P := by
  obtain ⟨st, g, c, -, -, hlaw, hid⟩ := restart_core ha hE hT hA hAT
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  have hset : (A ∩ {ω | Φ (wordAt W VL VR T ω) (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)} :
      Set Ω) =ᵐ[P] A ∩ (fun ω => (st ω, g ω)) ⁻¹' restartSetS a ρL ρR S := by
    filter_upwards [hid] with ω h
    have key : ∀ hωA : ω ∈ A, (Φ (wordAt W VL VR T ω) (fun t => W (T ω + t) ω - W (T ω) ω)
        (ζ ω - T ω) ↔ (st ω, g ω) ∈ restartSetS a ρL ρR S) := fun hωA => by
      obtain ⟨hst, hsep, hc, hc1, hcζ, hcw, hcl⟩ := h hωA
      have hcs : startOf (c ω) = st ω := (mem_cRelF_iff.2 hc).2
      have e1 : (st ω, g ω) ∈ restartSetS a ρL ρR S ↔
          (((st ω).1, (st ω).2), (c ω).1) ∈ lawSetS a ρL ρR S := by
        rw [hc1]; exact Iff.rfl
      rw [e1, mem_lawSetS_iff hsep hc, hSΦ _ (mem_cRelF_iff.2 hc).1 hcl, hcζ, hcs, hst]
      exact ⟨hΦ _ _ _ _ fun t ht => (hcw t ht).symm, hΦ _ _ _ _ fun t ht => hcw t ht⟩
    exact propext ⟨fun ⟨h1, h2⟩ => ⟨h1, (key h1).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (key h1).2 h2⟩⟩
  rw [measure_congr hset, hlaw _ (measurableSet_restartSetS hS)]
  refine setLIntegral_congr_fun_ae hAm ?_
  filter_upwards [hid] with ω h hωA
  rw [(h hωA).1]
  rfl

/-- **Decreasing code events.** If `S n` decreases, the canonical laws decrease to the canonical law of the intersection
(`lawSetS` is the injective image of the canonical separated codes). -/
theorem tendsto_codeLaw_iInter {S : ℕ → Set (XCode nL nR)} (hS : ∀ n, MeasurableSet (S n))
    (hanti : Antitone S) (s : (Fin nL → ℝ) × (Fin nR → ℝ)) :
    Tendsto (fun n => codeLaw a ρL ρR (S n) s) atTop (𝓝 (codeLaw a ρL ρR (⋂ n, S n) s)) := by
  have hD : ∀ n, MeasurableSet (Prod.mk s ⁻¹' restartSetS a ρL ρR (S n)) := fun n =>
    (measurableSet_restartSetS (hS n)).preimage measurable_prodMk_left
  have hDanti : Antitone fun n => Prod.mk s ⁻¹' restartSetS a ρL ρR (S n) := by
    intro m n hmn f hf
    obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := hf
    exact ⟨x, ⟨hx1, hanti hmn hx2⟩, hx3⟩
  have hinter : (⋂ n, Prod.mk s ⁻¹' restartSetS a ρL ρR (S n)) =
      Prod.mk s ⁻¹' restartSetS a ρL ρR (⋂ n, S n) := by
    ext f
    simp only [mem_iInter, mem_preimage]
    constructor
    · intro h
      obtain ⟨x₀, ⟨hx₀1, hx₀2⟩, hx₀3⟩ := h 0
      refine ⟨x₀, ⟨hx₀1, mem_iInter.2 fun n => ?_⟩, hx₀3⟩
      obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := h n
      have : x = x₀ := (injOn_startOf_fst a ρL ρR) hx1 hx₀1 (hx3.trans hx₀3.symm)
      rw [← this]; exact hx2
    · rintro ⟨x, ⟨hx1, hx2⟩, hx3⟩ n
      exact ⟨x, ⟨hx1, mem_iInter.1 hx2 n⟩, hx3⟩
  have h := tendsto_measure_iInter_atTop (μ := wienerPath) (fun n => (hD n).nullMeasurableSet)
    hDanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at h
  exact h

end StartCode

/-! ### The distance to a real interval -/

/-- The distance from `z` to the real interval `[a, b]` (for `a ≤ b`), through the nearest point
`max a (min (re z) b)`. -/
def dIcc (a b : ℝ) (z : ℂ) : ℝ := ‖z - ((max a (min z.re b) : ℝ) : ℂ)‖

theorem continuous_dIcc : Continuous fun p : ℝ × ℝ × ℂ => dIcc p.1 p.2.1 p.2.2 := by
  unfold dIcc
  refine (continuous_snd.comp continuous_snd).sub (Complex.continuous_ofReal.comp ?_) |>.norm
  exact continuous_fst.max ((Complex.continuous_re.comp (continuous_snd.comp continuous_snd)).min
    (continuous_fst.comp continuous_snd))

theorem norm_sub_ofReal_le_of_abs_le {z : ℂ} {r₁ r₂ : ℝ} (h : |z.re - r₁| ≤ |z.re - r₂|) :
    ‖z - r₁‖ ≤ ‖z - r₂‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  have := sq_le_sq.2 h
  nlinarith

/-- `dIcc` is at most the distance to any point of the interval. -/
theorem dIcc_le {a b : ℝ} (z : ℂ) {c : ℝ} (hc : c ∈ Icc a b) : dIcc a b z ≤ ‖z - c‖ := by
  refine norm_sub_ofReal_le_of_abs_le ?_
  rcases le_or_gt z.re a with h1 | h1
  · rw [min_eq_left (h1.trans (hc.1.trans hc.2)), max_eq_left h1, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith [hc.1])]
    linarith [hc.1]
  · rcases le_or_gt z.re b with h2 | h2
    · rw [min_eq_left h2, max_eq_right h1.le, sub_self, abs_zero]; exact abs_nonneg _
    · rw [min_eq_right h2.le, max_eq_right (hc.1.trans hc.2), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith [hc.2])]
      linarith [hc.2]

theorem clamp_mem_Icc {a b : ℝ} (hab : a ≤ b) (x : ℝ) : max a (min x b) ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem norm_sub_left_le_dIcc {a b : ℝ} (hab : a ≤ b) (z : ℂ) : ‖z - a‖ ≤ dIcc a b z + (b - a) := by
  have hm := clamp_mem_Icc hab z.re
  calc ‖z - a‖ = ‖(z - ((max a (min z.re b) : ℝ) : ℂ)) + (((max a (min z.re b) : ℝ) : ℂ) - a)‖ := by
        ring_nf
    _ ≤ dIcc a b z + ‖(((max a (min z.re b) : ℝ) : ℂ) - a)‖ := norm_add_le _ _
    _ ≤ dIcc a b z + (b - a) := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hm.1])]
        linarith [hm.2]

theorem norm_sub_right_le_dIcc {a b : ℝ} (hab : a ≤ b) (z : ℂ) : ‖z - b‖ ≤ dIcc a b z + (b - a) := by
  have hm := clamp_mem_Icc hab z.re
  calc ‖z - b‖ = ‖(z - ((max a (min z.re b) : ℝ) : ℂ)) + (((max a (min z.re b) : ℝ) : ℂ) - b)‖ := by
        ring_nf
    _ ≤ dIcc a b z + ‖(((max a (min z.re b) : ℝ) : ℂ) - b)‖ := norm_add_le _ _
    _ ≤ dIcc a b z + (b - a) := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hm.2])]
        linarith [hm.1]

theorem dIcc_smul {a b c : ℝ} (hc : 0 < c) (z : ℂ) :
    dIcc (c * a) (c * b) ((c : ℂ) * z) = c * dIcc a b z := by
  unfold dIcc
  have hre : ((c : ℂ) * z).re = c * z.re := by simp
  rw [hre, ← mul_min_of_nonneg _ _ hc.le, ← mul_max_of_nonneg _ _ hc.le, Complex.ofReal_mul, ← mul_sub,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]

/-! ### The band event -/

/-- The trace values at rational times, read from the rational driver values (`LP.traceAt`). -/
def ratTrace (w : ℝ≥0 → ℝ) (q : ℚ≥0) : ℂ := LP.traceAt q (Sec7.extendRat fun q : ℚ≥0 => w q)

/-- The distance from `z` to the two bands of the word `s` (one mark per side, `s.1 0 < 0 < s.2 0`): the fraction `θ`
of the gap next to each mark, `[s_L, (1 − θ) s_L] ∪ [(1 − θ) s_R, s_R]`. -/
def bandDist (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (z : ℂ) : ℝ :=
  min (dIcc (s.1 0) ((1 - θ) * s.1 0) z) (dIcc ((1 - θ) * s.2 0) (s.2 0) z)

theorem continuous_bandDist (θ : ℝ) :
    Continuous fun p : ℝ × ℝ × ℂ => bandDist θ ((fun _ => p.1), fun _ => p.2.1) p.2.2 := by
  unfold bandDist
  refine Continuous.min ?_ ?_
  · exact continuous_dIcc.comp (continuous_fst.prodMk ((continuous_const.mul continuous_fst).prodMk
      (continuous_snd.comp continuous_snd)))
  · exact continuous_dIcc.comp (((continuous_const.mul (continuous_fst.comp continuous_snd))).prodMk
      ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))

theorem bandDist_eq (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (z : ℂ) :
    bandDist θ s z = bandDist θ ((fun _ => s.1 0), fun _ => s.2 0) z := rfl

/-- **The band event** of (start, driver, horizon): infinite horizon, a continuous generating trace on `[0, ∞)`, and
trace values at arbitrarily late rational times arbitrarily close to the bands of the start. -/
def BandEvent (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (w : ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  τ = ⊤ ∧ (fun q : ℚ≥0 => w q) ∈ topSet ∧
    ∀ k N : ℕ, ∃ q : ℚ≥0, (N : ℝ≥0) ≤ q ∧ bandDist θ s (ratTrace w q) < 1 / ((k : ℝ) + 1)

/-- The Borel set of solution codes with the band event of their own start. -/
def bandCodeSet (θ : ℝ) : Set (XCode 1 1) := {x | BandEvent θ (startOf x) (cw x) (cζ x)}

theorem measurableSet_bandCodeSet (θ : ℝ) : MeasurableSet (bandCodeSet θ) := by
  have hR : Measurable fun x : XCode 1 1 => fun q : ℚ≥0 => cw x q :=
    measurable_pi_iff.2 fun q => (measurable_pi_apply (q : ℝ≥0)).comp measurable_cw_cζ.fst
  have h1 : MeasurableSet {x : XCode 1 1 | cζ x = ⊤} := measurable_cζ (measurableSet_singleton ⊤)
  have h2 : MeasurableSet {x : XCode 1 1 | (fun q : ℚ≥0 => cw x q) ∈ topSet} := hR measurableSet_topSet
  have h3 : ∀ (k N : ℕ) (q : ℚ≥0), MeasurableSet {x : XCode 1 1 | (N : ℝ≥0) ≤ q ∧
      bandDist θ (startOf x) (ratTrace (cw x) q) < 1 / ((k : ℝ) + 1)} := by
    intro k N q
    rw [ofPred_and]
    refine (MeasurableSet.const _).inter (measurableSet_lt ?_ measurable_const)
    have hz : Measurable fun x : XCode 1 1 => ratTrace (cw x) q :=
      (LP.measurable_traceAt (q : ℝ≥0)).comp (Sec7.measurable_extendRat.comp hR)
    exact (continuous_bandDist θ).measurable.comp
      ((measurable_startOf_fst 0).prodMk ((measurable_startOf_snd 0).prodMk hz))
  have e : bandCodeSet θ = {x : XCode 1 1 | cζ x = ⊤} ∩ ({x | (fun q : ℚ≥0 => cw x q) ∈ topSet} ∩
      ⋂ k : ℕ, ⋂ N : ℕ, ⋃ q : ℚ≥0, {x : XCode 1 1 | (N : ℝ≥0) ≤ q ∧
        bandDist θ (startOf x) (ratTrace (cw x) q) < 1 / ((k : ℝ) + 1)}) := by
    ext x
    simp only [bandCodeSet, BandEvent, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
  rw [e]
  exact h1.inter (h2.inter (MeasurableSet.iInter fun k => MeasurableSet.iInter fun N =>
    MeasurableSet.iUnion fun q => h3 k N q))

theorem bandEvent_congr (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) (hb : BandEvent θ s w τ) : BandEvent θ s w' τ := by
  obtain ⟨hτ, h2⟩ := hb
  subst hτ
  have : w = w' := funext fun t => h t ENNReal.coe_lt_top
  subst this
  exact ⟨rfl, h2⟩

/-- The band event in real time, for a continuous generating trace. -/
def RealBand (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (η : ℝ≥0 → ℂ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ N : ℝ≥0, ∃ t : ℝ≥0, N ≤ t ∧ bandDist θ s (η t) < ε

theorem ratTrace_eq {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (q : ℚ≥0) : ratTrace w q = η q := by
  unfold ratTrace
  rw [Sec7.extendRat_eq hw]
  exact LP.traceAt_eq_of_isGeneratingTrace hη hw.continuousOn hw0 ENNReal.coe_lt_top

/-- **The band event of a continuous driver with a generating trace on `[0, ∞)`** is the real-time band condition. -/
theorem bandEvent_top_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 1 → ℝ)) :
    BandEvent θ s w ⊤ ↔ RealBand θ s η := by
  have hηc : Continuous η :=
    continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  constructor
  · rintro ⟨-, -, h⟩ ε hε N
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨M, hM⟩ := exists_nat_ge (N : ℝ)
    obtain ⟨q, hq, hd⟩ := h k M
    refine ⟨q, ?_, ?_⟩
    · rw [← NNReal.coe_le_coe]; exact hM.trans (by exact_mod_cast hq)
    · rw [ratTrace_eq hw hw0 hη] at hd; linarith
  · intro h
    refine ⟨rfl, (ratVals_mem_topSet_iff hw hw0).2 ⟨η, hη⟩, fun k N => ?_⟩
    obtain ⟨t, ht, hd⟩ := h (1 / ((k : ℝ) + 1)) (by positivity) N
    have hcd : Continuous fun z => bandDist θ s z := by
      rw [show (fun z => bandDist θ s z) = fun z => bandDist θ ((fun _ => s.1 0), fun _ => s.2 0) z from rfl]
      exact (continuous_bandDist θ).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hlim : Tendsto (fun m => bandDist θ s (η (Sec7.ratAbove t m))) atTop (𝓝 (bandDist θ s (η t))) :=
      ((hcd.comp hηc).tendsto t).comp (Sec7.tendsto_ratAbove t)
    obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds hd)).exists
    refine ⟨Sec7.ratAbove t m, ht.trans (Sec7.le_ratAbove t m), ?_⟩
    rw [ratTrace_eq hw hw0 hη]; exact hm

/-! ### Dilation invariance -/

theorem bandDist_smul {c : ℝ} (hc : 0 < c) (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (z : ℂ) :
    bandDist θ ((fun i => c * s.1 i), fun j => c * s.2 j) ((c : ℂ) * z) = c * bandDist θ s z := by
  unfold bandDist
  rw [show (1 - θ) * (c * s.1 0) = c * ((1 - θ) * s.1 0) by ring,
    show (1 - θ) * (c * s.2 0) = c * ((1 - θ) * s.2 0) by ring, dIcc_smul hc, dIcc_smul hc,
    mul_min_of_nonneg _ _ hc.le]

/-- The real-time band condition is invariant under Brownian scaling of the trace and the start. -/
theorem realBand_dilate {c : ℝ≥0} (hc : c ≠ 0) (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    {η : ℝ≥0 → ℂ} :
    RealBand θ ((fun i => (√(c : ℝ))⁻¹ * s.1 i), fun j => (√(c : ℝ))⁻¹ * s.2 j)
        (fun t => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * η (c * t)) ↔ RealBand θ s η := by
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hcc : (0 : ℝ≥0) < c := pos_iff_ne_zero.2 hc
  set l : ℝ := (√(c : ℝ))⁻¹ with hl
  have hl0 : 0 < l := inv_pos.2 (Real.sqrt_pos.2 hc')
  simp only [RealBand, bandDist_smul hl0]
  constructor
  · intro h ε hε N
    obtain ⟨t, ht, hd⟩ := h (l * ε) (mul_pos hl0 hε) (N / c)
    refine ⟨c * t, ?_, (mul_lt_mul_iff_of_pos_left hl0).1 hd⟩
    rwa [div_le_iff₀ hcc, mul_comm] at ht
  · intro h ε hε N
    obtain ⟨t, ht, hd⟩ := h (ε / l) (div_pos hε hl0) (c * N)
    refine ⟨t / c, ?_, ?_⟩
    · rw [le_div_iff₀ hcc, mul_comm]; exact ht
    · rw [mul_div_cancel₀ t hc]
      rwa [lt_div_iff₀ hl0, mul_comm] at hd

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL xR ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The canonical probability of the band event is the probability for any evolution of a separated word. -/
theorem measure_band_eq_codeLaw [IsProbabilityMeasure P] (hκ : 0 < κ) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (θ : ℝ) :
    P {ω | BandEvent θ (xL, xR) (fun t => W t ω) (ζ ω)} = codeLaw κ ρL ρR (bandCodeSet θ) (xL, xR) :=
  measure_eventOf_eq_codeLawS hκ hsep hE (measurableSet_bandCodeSet θ) (fun _ _ _ => Iff.rfl)
    (bandEvent_congr θ)

/-- **Dilation invariance of the band probability** (the positive affine normalization): if the separated word
`(xL, xR)` has an evolution with infinite lifetime and a generating trace, the canonical probability of the band
event is the same at `λ (xL, xR)` for every `λ > 0` (here `λ = (√c)⁻¹`). -/
theorem codeLaw_band_dilate [IsProbabilityMeasure P] (hκ : 0 < κ) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) {c : ℝ≥0}
    (hc : c ≠ 0) (θ : ℝ) :
    codeLaw κ ρL ρR (bandCodeSet θ) ((fun i => (√(c : ℝ))⁻¹ * xL i), fun j => (√(c : ℝ))⁻¹ * xR j) =
      codeLaw κ ρL ρR (bandCodeSet θ) (xL, xR) := by
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hs : 0 < (√(c : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hc')
  have hsep' : ∀ i j, (√(c : ℝ))⁻¹ * xL i < (√(c : ℝ))⁻¹ * xR j := fun i j =>
    mul_lt_mul_of_pos_left (hsep i j) hs
  rw [← measure_band_eq_codeLaw hκ hsep' (hE.dilate hc), ← measure_band_eq_codeLaw hκ hsep hE]
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [htr, hE.2.2.2.2] with ω ⟨hζω, η, hη⟩ hp
  have hwc : Continuous fun t => W t ω := by
    have h := hp.2.2.2.1
    rw [hζω] at h
    exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
  have hdc : Continuous (Sec7.Dilation.dilPath c fun t => W t ω) :=
    continuous_const.mul (hwc.comp (continuous_const.mul continuous_id))
  have hd0 : Sec7.Dilation.dilPath c (fun t => W t ω) 0 = 0 := by simp [Sec7.Dilation.dilPath, hp.1]
  have hη' := hη.dilate hc
  rw [ENNReal.top_div_of_ne_top ENNReal.coe_ne_top] at hη'
  show BandEvent θ _ (Sec7.Dilation.dilPath c fun t => W t ω) (ζ ω / c) ↔ BandEvent θ (xL, xR) (fun t => W t ω) (ζ ω)
  rw [hζω, ENNReal.top_div_of_ne_top ENNReal.coe_ne_top, bandEvent_top_iff hdc hd0 hη',
    bandEvent_top_iff hwc hp.1 hη]
  exact realBand_dilate hc θ (xL, xR)

/-! ### Shrinking bands: a terminal cluster point at a mark -/

/-- If the band condition holds for every fraction `1/(m+1)`, one of the two marks is a terminal cluster point. -/
theorem isTermCluster_of_forall_realBand {s : (Fin 1 → ℝ) × (Fin 1 → ℝ)} (hs1 : s.1 0 < 0)
    (hs2 : 0 < s.2 0) {η : ℝ≥0 → ℂ} (h : ∀ m : ℕ, RealBand (1 / ((m : ℝ) + 1)) s η) :
    IsTermCluster η (s.1 0) ∨ IsTermCluster η (s.2 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [isTermCluster_iff_not, not_not] at h1 h2
  obtain ⟨d₁, hd₁, hev₁⟩ := h1
  obtain ⟨d₂, hd₂, hev₂⟩ := h2
  set d := min d₁ d₂ with hd
  have hd0 : 0 < d := lt_min hd₁ hd₂
  set M := -s.1 0 + s.2 0 with hM
  have hM0 : 0 < M := by linarith
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < d / 2 / M by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev₁.and hev₂)
  obtain ⟨t, ht, hdist⟩ := h m (d / 2) (by positivity) N
  set θ : ℝ := 1 / ((m : ℝ) + 1) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθM : θ * M < d / 2 := by rwa [lt_div_iff₀ hM0] at hm
  obtain ⟨hn1, hn2⟩ := hN t ht
  unfold bandDist at hdist
  rcases min_lt_iff.1 hdist with hl | hr
  · have hab : s.1 0 ≤ (1 - θ) * s.1 0 := by nlinarith
    have := norm_sub_left_le_dIcc hab (η t)
    have : θ * (-s.1 0) ≤ θ * M := mul_le_mul_of_nonneg_left (by linarith) hθ0
    have := min_le_left d₁ d₂
    nlinarith
  · have hab : (1 - θ) * s.2 0 ≤ s.2 0 := by nlinarith
    have := norm_sub_right_le_dIcc hab (η t)
    have : θ * s.2 0 ≤ θ * M := mul_le_mul_of_nonneg_left (by linarith) hθ0
    have := min_le_right d₁ d₂
    nlinarith

end InteractingSLE.ZhanGT4
