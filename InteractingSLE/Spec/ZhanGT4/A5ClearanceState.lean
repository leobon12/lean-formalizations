/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A5ClearanceMart
import InteractingSLE.Spec.Zhan.AvoidClock
import InteractingSLE.Spec.ZhanGT4.NoClusterHit
import InteractingSLE.Spec.Sec2.GirsanovDensity

/-!
# Protected-ray clearance, IV: the state process of the separated two-force law

Packet PROVE-ZHAN-CLEAR. For an integrated `SLE_κ(ρ_L; ρ_R)` evolution with one mark per side, `x_L < 0 < x_R`,
weights `≥ κ/2 − 2`, the state `Λ_t = (V^R_t, V^L_t, W_t − √κ B_t, s_t)`, `s_t = ∫₀ᵗ (V^R − W)⁻²` (`clrState`), on a
full-measure event of good paths (`IsGoodClr`: the frozen path conditions, infinite lifetime, noncollision at all
times, a continuous Brownian path from `0`; `exists_good_clr`, from Aux. lemma 6), with the initial state off it,
satisfies every hypothesis of `measure_hit_after_le` for the Lyapunov observable of `A5ClearanceGen` in the
null-augmented filtration:

* `clrState_of_good`, `clrState_zero`, `continuous_clrState`, `measurable_clrState`;
* `clrState_eq_integral`: `Λ_t = Λ_0 + ∫₀ᵗ clrField(Λ_s, B_s) ds` on good paths;
* `clrState_mem_region`: the path stays in `{Z > 0, Y > 0}`; `zC_clrState`, `yC_clrState`, `sC_clrState`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A5Clear

open QuantumZipper Zhan

section State

open scoped Classical

variable {κ : ℝ} {xL xR ρL ρR : Fin 1 → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The good paths: the integrated path conditions, infinite lifetime, the marks separated from the driver at
every time, and a continuous Brownian path started at `0`. -/
def IsGoodClr (κ : ℝ) (xL xR ρL ρR : Fin 1 → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) (ζ ω) ∧
    ζ ω = ⊤ ∧ (∀ t, VL 0 t ω < W t ω ∧ W t ω < VR 0 t ω) ∧ Continuous (B · ω) ∧ B 0 ω = 0

/-- The one-mark-per-side word with marks `x_L < 0 < x_R` is ordered. -/
theorem isOrderedForceWord_one (hxL : xL 0 < 0) (hxR : 0 < xR 0) : IsOrderedForceWord xL xR :=
  ⟨fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j], fun i => by
    rw [Fin.fin_one_eq_zero i]; exact hxL.le, fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j],
    fun j => by rw [Fin.fin_one_eq_zero j]; exact hxR.le⟩

theorem exists_good_clr [IsProbabilityMeasure P] (hκ : 0 < κ) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hwL : κ / 2 - 2 ≤ ρL 0) (hwR : κ / 2 - 2 ≤ ρR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω := by
  have hF := isOrderedForceWord_one hxL hxR
  have hadm := hasAdmissiblePartialSums_one (xL := xL) (xR := xR) hwL hwR
  have hae : ∀ᵐ ω ∂P, IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω := by
    filter_upwards [hE.2.2.2.2, Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE, hE.1.1.cont,
      hE.1.1.eval_zero_ae_eq_zero] with ω hp h6 hBc hB0
    refine ⟨hp, h6.1, fun t => ?_, hBc, hB0⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
    · subst ht
      have h0 : W 0 ω = 0 := hp.1
      have hv1 : VL 0 0 ω = xL 0 := hp.2.1 0
      have hv2 : VR 0 0 ω = xR 0 := hp.2.2.1 0
      rw [h0, hv1, hv2]; exact ⟨hxL, hxR⟩
    · exact ⟨(h6.2 t ht).1 0, (h6.2 t ht).2 0⟩
  refine ⟨(toMeasurable P {ω | ¬ IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
  · by_contra h; exact hω (subset_toMeasurable _ _ h)

/-- The gap `Z = V^R − W` on `G` (killed form; the initial gap off `G`). -/
def clrGap (G : Set Ω) (xR : Fin 1 → ℝ) (W : ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then Girsanov.killed ζ (VR 0) t ω - Girsanov.killed ζ W t ω else xR 0

/-- The state `(V^R, V^L, W − √κ B, s)` on `G` (the initial state off `G`). -/
def clrState (κ : ℝ) (G : Set Ω) (xL xR : Fin 1 → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : CE :=
  if ω ∈ G then
    (Girsanov.killed ζ (VR 0) t ω, Girsanov.killed ζ (VL 0) t ω,
      Girsanov.killed ζ W t ω - Real.sqrt κ * B t ω,
      ∫ u in (0 : ℝ)..t, ((clrGap G xR W VR ζ u.toNNReal ω) ^ 2)⁻¹)
  else (xR 0, xL 0, 0, 0)

/-- The initial state. -/
def clrInit (xL xR : Fin 1 → ℝ) : CE := (xR 0, xL 0, 0, 0)

/-- The clock of a good path. -/
def clrClock (W : ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..t, ((VR 0 u.toNNReal ω - W u.toNNReal ω) ^ 2)⁻¹

variable {G : Set Ω}

theorem IsGoodClr.continuous_w {ω : Ω} (h : IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) : Continuous (W · ω) := by
  rw [← continuousOn_univ]
  refine h.1.2.2.2.1.mono fun t _ => ?_
  show (t : ℝ≥0∞) < ζ ω
  rw [h.2.1]; exact ENNReal.coe_lt_top

theorem IsGoodClr.continuous_vL {ω : Ω} (h : IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) :
    Continuous (VL 0 · ω) := by
  rw [← continuousOn_univ]
  refine (h.1.2.2.2.2.1 0).mono fun t _ => ?_
  show (t : ℝ≥0∞) < ζ ω
  rw [h.2.1]; exact ENNReal.coe_lt_top

theorem IsGoodClr.continuous_vR {ω : Ω} (h : IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) :
    Continuous (VR 0 · ω) := by
  rw [← continuousOn_univ]
  refine (h.1.2.2.2.2.2.1 0).mono fun t _ => ?_
  show (t : ℝ≥0∞) < ζ ω
  rw [h.2.1]; exact ENNReal.coe_lt_top

theorem IsGoodClr.lt_top {ω : Ω} (h : IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (t : ℝ≥0) :
    (t : ℝ≥0∞) < ζ ω := by rw [h.2.1]; exact ENNReal.coe_lt_top

theorem clrGap_of_good {ω : Ω} (hω : ω ∈ G) (h : IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (t : ℝ≥0) :
    clrGap G xR W VR ζ t ω = VR 0 t ω - W t ω := by
  simp only [clrGap, hω, ↓reduceIte, Girsanov.killed_of_lt (h.lt_top t)]

/-- On a good path the state is the explicit one. -/
theorem clrState_of_good {ω : Ω} (hω : ω ∈ G) (h : IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (t : ℝ≥0) :
    clrState κ G xL xR W VL VR B ζ t ω =
      (VR 0 t ω, VL 0 t ω, W t ω - Real.sqrt κ * B t ω, clrClock W VR t ω) := by
  simp only [clrState, hω, ↓reduceIte, Girsanov.killed_of_lt (h.lt_top t), clrClock]
  congr 3
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [clrGap_of_good hω h]

theorem continuous_clrGap (hgood : ∀ ω ∈ G, IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (ω : Ω) :
    Continuous (clrGap G xR W VR ζ · ω) := by
  by_cases hω : ω ∈ G
  · have h := hgood ω hω
    simp only [clrGap_of_good hω h]
    exact h.continuous_vR.sub h.continuous_w
  · simp only [clrGap, hω, ↓reduceIte]; exact continuous_const

theorem clrGap_pos (hgood : ∀ ω ∈ G, IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (hxR : 0 < xR 0) (t : ℝ≥0)
    (ω : Ω) : 0 < clrGap G xR W VR ζ t ω := by
  by_cases hω : ω ∈ G
  · have h := hgood ω hω
    rw [clrGap_of_good hω h]; linarith [(h.2.2.1 t).2]
  · simp only [clrGap, hω, ↓reduceIte]; exact hxR

theorem continuous_clrClock_integral (hgood : ∀ ω ∈ G, IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω)
    (hxR : 0 < xR 0) (ω : Ω) :
    Continuous fun t : ℝ≥0 => ∫ u in (0 : ℝ)..t, ((clrGap G xR W VR ζ u.toNNReal ω) ^ 2)⁻¹ := by
  have hc : Continuous fun u : ℝ => ((clrGap G xR W VR ζ u.toNNReal ω) ^ 2)⁻¹ :=
    (((continuous_clrGap hgood ω).comp continuous_real_toNNReal).pow 2).inv₀ fun u =>
      pow_ne_zero 2 (clrGap_pos hgood hxR _ ω).ne'
  exact (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).comp
    NNReal.continuous_coe

theorem clrState_zero (hgood : ∀ ω ∈ G, IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (ω : Ω) :
    clrState κ G xL xR W VL VR B ζ 0 ω = clrInit xL xR := by
  by_cases hω : ω ∈ G
  · have h := hgood ω hω
    rw [clrState_of_good hω h]
    have hw0 : W 0 ω = 0 := h.1.1
    have hv1 : VL 0 0 ω = xL 0 := h.1.2.1 0
    have hv2 : VR 0 0 ω = xR 0 := h.1.2.2.1 0
    simp [clrInit, clrClock, hw0, hv1, hv2, h.2.2.2.2]
  · simp [clrState, clrInit, hω]

theorem continuous_clrState (hgood : ∀ ω ∈ G, IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (hxR : 0 < xR 0)
    (ω : Ω) : Continuous fun t => clrState κ G xL xR W VL VR B ζ t ω := by
  by_cases hω : ω ∈ G
  · have h := hgood ω hω
    have e : (fun t => clrState κ G xL xR W VL VR B ζ t ω) = fun t =>
        (Girsanov.killed ζ (VR 0) t ω, Girsanov.killed ζ (VL 0) t ω,
          Girsanov.killed ζ W t ω - Real.sqrt κ * B t ω,
          ∫ u in (0 : ℝ)..t, ((clrGap G xR W VR ζ u.toNNReal ω) ^ 2)⁻¹) := by
      funext t; simp only [clrState, hω, ↓reduceIte]
    rw [e]
    simp only [Girsanov.killed_of_lt (h.lt_top _)]
    exact h.continuous_vR.prodMk (h.continuous_vL.prodMk ((h.continuous_w.sub
      (continuous_const.mul h.2.2.2.1)).prodMk (continuous_clrClock_integral hgood hxR ω)))
  · simp only [clrState, hω, ↓reduceIte]; exact continuous_const

theorem measurable_clrState [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hgood : ∀ ω ∈ G, IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
    (t : ℝ≥0) : Measurable[Ito.nullAugmented 𝓕 P t] (clrState κ G xL xR W VL VR B ζ t) := by
  obtain ⟨hB, hWa, hVLa, hVRa, -⟩ := hE
  have hGt : ∀ t, MeasurableSet[Ito.nullAugmented 𝓕 P t] G := fun t => by
    have := (Ito.measurableSet_nullAugmented_of_null (𝓕 := 𝓕) hGm.compl hGc t).compl
    rwa [compl_compl] at this
  have hle := fun t => Ito.le_nullAugmented 𝓕 P t
  have hgapm : ∀ t, Measurable[Ito.nullAugmented 𝓕 P t] (clrGap G xR W VR ζ t) := fun t =>
    Measurable.ite (hGt t) (((Girsanov.measurable_killed (hVRa 0) t).sub
      (Girsanov.measurable_killed hWa t)).mono (hle t) le_rfl) measurable_const
  have hprog : IsStronglyProgressive (Ito.nullAugmented 𝓕 P) (clrGap G xR W VR ζ) :=
    StronglyAdapted.isStronglyProgressive_of_continuous (fun r => (hgapm r).stronglyMeasurable)
      (continuous_clrGap hgood)
  have hint := (Girsanov.stronglyMeasurable_integral_comp hprog (g := fun x : ℝ => (x ^ 2)⁻¹)
    (by fun_prop) t).measurable
  refine Measurable.ite (hGt t) ?_ measurable_const
  exact ((Girsanov.measurable_killed (hVRa 0) t).mono (hle t) le_rfl).prodMk
    (((Girsanov.measurable_killed (hVLa 0) t).mono (hle t) le_rfl).prodMk
      ((((Girsanov.measurable_killed hWa t).sub ((hB.2.1 t).const_mul _)).mono (hle t) le_rfl).prodMk hint))

theorem intervalIntegral_pair {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : ℝ → E} {g : ℝ → F} {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    ∫ s in a..b, (f s, g s) = (∫ s in a..b, f s, ∫ s in a..b, g s) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  exact integral_pair hf.1 hg.1

/-- The path `(Λ, B)` of the state. -/
theorem pathX_clrState_of_good {ω : Ω} (hω : ω ∈ G) (h : IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (t : ℝ≥0) :
    pathX (clrState κ G xL xR W VL VR B ζ) (Zhan.clockBrown G B) t ω =
      ((VR 0 t ω, VL 0 t ω, W t ω - Real.sqrt κ * B t ω, clrClock W VR t ω), B t ω) := by
  simp only [pathX, clrState_of_good hω h, Zhan.clockBrown, hω, ↓reduceIte]

theorem zC_clrState {ω : Ω} (hω : ω ∈ G) (h : IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (t : ℝ≥0) :
    zC κ (pathX (clrState κ G xL xR W VL VR B ζ) (Zhan.clockBrown G B) t ω) = VR 0 t ω - W t ω := by
  rw [pathX_clrState_of_good hω h]; simp only [zC]; ring

theorem yC_clrState {ω : Ω} (hω : ω ∈ G) (h : IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (t : ℝ≥0) :
    yC κ (pathX (clrState κ G xL xR W VL VR B ζ) (Zhan.clockBrown G B) t ω) = W t ω - VL 0 t ω := by
  rw [pathX_clrState_of_good hω h]; simp only [yC]; ring

theorem sC_clrState {ω : Ω} (hω : ω ∈ G) (h : IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (t : ℝ≥0) :
    sC (pathX (clrState κ G xL xR W VL VR B ζ) (Zhan.clockBrown G B) t ω) = clrClock W VR t ω := by
  rw [pathX_clrState_of_good hω h]; rfl

/-- **The path stays in the region `{Z > 0, Y > 0}`.** -/
theorem clrState_mem_region (hgood : ∀ ω ∈ G, IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) (hxL : xL 0 < 0)
    (hxR : 0 < xR 0) (ω : Ω) (t : ℝ≥0) :
    pathX (clrState κ G xL xR W VL VR B ζ) (Zhan.clockBrown G B) t ω ∈ clrRegion κ := by
  by_cases hω : ω ∈ G
  · have h := hgood ω hω
    refine ⟨?_, ?_⟩
    · rw [zC_clrState hω h]; linarith [(h.2.2.1 t).2]
    · rw [yC_clrState hω h]; linarith [(h.2.2.1 t).1]
  · simp only [clrRegion, mem_ofPred_eq, zC, yC, pathX, clrState, Zhan.clockBrown, hω, ↓reduceIte]
    constructor <;> simp <;> linarith

/-- **The state solves `Λ' = clrField(Λ, B)`** on a good path. -/
theorem clrState_eq_integral (hgood : ∀ ω ∈ G, IsGoodClr κ xL xR ρL ρR W VL VR B ζ ω) {ω : Ω} (hω : ω ∈ G)
    (t : ℝ≥0) :
    clrState κ G xL xR W VL VR B ζ t ω = clrInit xL xR +
      ∫ s in (0 : ℝ)..t, clrField κ (ρL 0) (ρR 0)
        (pathX (clrState κ G xL xR W VL VR B ζ) (Zhan.clockBrown G B) s.toNNReal ω) := by
  have h := hgood ω hω
  have hw := h.continuous_w.comp continuous_real_toNNReal
  have hvl := h.continuous_vL.comp continuous_real_toNNReal
  have hvr := h.continuous_vR.comp continuous_real_toNNReal
  have hR0 : ∀ s : ℝ, VR 0 s.toNNReal ω - W s.toNNReal ω ≠ 0 := fun s => by
    linarith [(h.2.2.1 s.toNNReal).2]
  have hL0 : ∀ s : ℝ, W s.toNNReal ω - VL 0 s.toNNReal ω ≠ 0 := fun s => by
    linarith [(h.2.2.1 s.toNNReal).1]
  have hL0' : ∀ s : ℝ, VL 0 s.toNNReal ω - W s.toNNReal ω ≠ 0 := fun s => by
    linarith [(h.2.2.1 s.toNNReal).1]
  have hR0' : ∀ s : ℝ, W s.toNNReal ω - VR 0 s.toNNReal ω ≠ 0 := fun s => by
    linarith [(h.2.2.1 s.toNNReal).2]
  have hc1 : Continuous fun s : ℝ => 2 / (VR 0 s.toNNReal ω - W s.toNNReal ω) :=
    continuous_const.div (hvr.sub hw) hR0
  have hc2 : Continuous fun s : ℝ => 2 / (VL 0 s.toNNReal ω - W s.toNNReal ω) :=
    continuous_const.div (hvl.sub hw) hL0'
  have hc3a : Continuous fun s : ℝ => ρL 0 / (W s.toNNReal ω - VL 0 s.toNNReal ω) :=
    continuous_const.div (hw.sub hvl) hL0
  have hc3b : Continuous fun s : ℝ => ρR 0 / (W s.toNNReal ω - VR 0 s.toNNReal ω) :=
    continuous_const.div (hw.sub hvr) hR0'
  have hc4 : Continuous fun s : ℝ => ((VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2)⁻¹ :=
    ((hvr.sub hw).pow 2).inv₀ fun s => pow_ne_zero 2 (hR0 s)
  have hfield : ∀ s : ℝ, clrField κ (ρL 0) (ρR 0)
      (pathX (clrState κ G xL xR W VL VR B ζ) (Zhan.clockBrown G B) s.toNNReal ω) =
      (2 / (VR 0 s.toNNReal ω - W s.toNNReal ω), 2 / (VL 0 s.toNNReal ω - W s.toNNReal ω),
        ρL 0 / (W s.toNNReal ω - VL 0 s.toNNReal ω) + ρR 0 / (W s.toNNReal ω - VR 0 s.toNNReal ω),
        ((VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2)⁻¹) := fun s => by
    simp only [clrField, zC_clrState hω h, yC_clrState hω h]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · rfl
    · show -2 / (W s.toNNReal ω - VL 0 s.toNNReal ω) = 2 / (VL 0 s.toNNReal ω - W s.toNNReal ω)
      rw [neg_div, ← div_neg, neg_sub]
    · show ρL 0 / (W s.toNNReal ω - VL 0 s.toNNReal ω) - ρR 0 / (VR 0 s.toNNReal ω - W s.toNNReal ω) =
        ρL 0 / (W s.toNNReal ω - VL 0 s.toNNReal ω) + ρR 0 / (W s.toNNReal ω - VR 0 s.toNNReal ω)
      rw [sub_eq_add_neg, ← div_neg, neg_sub]
    · show 1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 = ((VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2)⁻¹
      rw [one_div]
  rw [intervalIntegral.integral_congr fun s _ => hfield s]
  set F : ℝ → CE := fun s =>
    (2 / (VR 0 s.toNNReal ω - W s.toNNReal ω), 2 / (VL 0 s.toNNReal ω - W s.toNNReal ω),
      ρL 0 / (W s.toNNReal ω - VL 0 s.toNNReal ω) + ρR 0 / (W s.toNNReal ω - VR 0 s.toNNReal ω),
      ((VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2)⁻¹) with hFdef
  have hFi : IntervalIntegrable F volume 0 t :=
    (hc1.prodMk (hc2.prodMk ((hc3a.add hc3b).prodMk hc4))).intervalIntegrable _ _
  have e1 : (∫ s in (0 : ℝ)..t, F s).1 = ∫ s in (0 : ℝ)..t, (F s).1 :=
    Zhan.clm_intervalIntegral (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ)) hFi
  have e2 : (∫ s in (0 : ℝ)..t, F s).2.1 = ∫ s in (0 : ℝ)..t, (F s).2.1 :=
    Zhan.clm_intervalIntegral ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))) hFi
  have e3 : (∫ s in (0 : ℝ)..t, F s).2.2.1 = ∫ s in (0 : ℝ)..t, (F s).2.2.1 :=
    Zhan.clm_intervalIntegral ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))) hFi
  have e4 : (∫ s in (0 : ℝ)..t, F s).2.2.2 = ∫ s in (0 : ℝ)..t, (F s).2.2.2 :=
    Zhan.clm_intervalIntegral ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))) hFi
  have hlt := h.lt_top t
  have hp := h.1
  have hweq := hp.2.2.2.2.2.2.2.2.2.2.2.2.1 t hlt
  have hvLeq := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t hlt 0
  have hvReq := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t hlt 0
  simp only [Fin.sum_univ_one] at hweq
  rw [clrState_of_good hω h]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [Prod.fst_add, clrInit]; rw [e1]; exact hvReq
  · simp only [Prod.snd_add, Prod.fst_add, clrInit]; rw [e2]; exact hvLeq
  · simp only [Prod.snd_add, Prod.fst_add, clrInit]
    rw [e3]
    simp only [hFdef]
    rw [intervalIntegral.integral_add (hc3a.intervalIntegrable _ _) (hc3b.intervalIntegrable _ _)]
    linarith
  · simp only [Prod.snd_add, clrInit, clrClock]; rw [e4, zero_add]

end State

end InteractingSLE.ZhanGT4.A5Clear
