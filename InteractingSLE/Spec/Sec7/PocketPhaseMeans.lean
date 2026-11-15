/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketMartLifeAe
import InteractingSLE.Spec.Sec7.Lemma71CMart
import InteractingSLE.Spec.Sec7.PhaseSelAdaptCont
import InteractingSLE.Spec.Sec7.PocketWordLife

/-!
# Aux. lemma 122's hypotheses before the lifetime from the coupling clause of the pocket word

Packet PROVE-STRIPSYS18 (specification §7.4, Aux. lemma 122, pp. 389–390: "Retain a stopped Gaussian field kernel whose
harmonic mean `M_t(z)` is a continuous local martingale until `z` is swallowed. Assume the following exact boundary
description […] These data have their bounded Poisson extension, and there is no additional singular harmonic term";
Aux. lemma 125, p. 397: "Stop before a fixed coordinate bound or at `ζ`, whichever occurs first […] These are genuine
stopping times in the relative history and supply pre-lifetime localizations for the martingale and SDE arguments").

PROVE-STRIPSYS14's `PocketWordLife.pocketWordEvolution_of_hasPhaseMeans` turns Aux. lemma 122's hypotheses before the
terminal capacity time (`PocketMartLife.HasPhaseMeansBefore`: every choice of the bounded harmonic extensions of the
phase-shifted word data gives coupling means that are local martingales before `min (swallowTime z) T` and continuous
on compact windows before swallowing) into hPW. Here these hypotheses are derived, with the **canonical phase
`d = 0`**, from the field-level statement in the form the coupling arguments deliver it: the **conditional-law clause
of the optional hull specification with lifetime `T`** (`MartMeans.IsCouplingCharFun`) for the pocket word, with the
geometric force coordinates `geomLW W xL`, `geomRW W xR` of random time-zero marks. This is the generalization of
PROVE-LEMMA71C's `Lemma71C.hasMartingaleMeansBefore_of_charFun` (two-seed word, deterministic marks) to random words.

## Main results

* `adaptedBefore_geomLW`, `adaptedBefore_geomRW`: the geometric coordinates of `𝓖₀`-measurable marks along a killed
  driver are adapted before its lifetime;
* `isLocalMartingaleBefore_of_eq_before`: a local martingale before `ζ ≤ T`, right-continuous before `ζ`, stays one
  after changing it at times `≥ T` and on a null event of `𝓖₀` (localize at the minimum with an announcing sequence of
  `T`);
* `continuousOn_couplingMean_of_ext`: continuity in time of the coupling mean of any extension of the word data along
  continuous coordinates (the explicit harmonic mean);
* **`hasPhaseMeansBefore_zero_of_charFun`**: `HasPhaseMeansBefore κ ρL ρR P 𝓖 W xL xR 0 T` from
  `IsCouplingCharFun κ ρL ρR P 𝓖 W (geomLW W xL) (geomRW W xR) T h`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketPhaseMeans

open MartChar Coupling PocketTraversal PocketMartLife PhaseSel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The geometric coordinates of random marks along a killed driver -/

section Geom

variable {nL nR : ℕ} {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω})
include hc

theorem geomLW_eq_frz (xL : Ω → Fin nL → ℝ) (i : Fin nL) {t s : ℝ≥0} {ω : Ω} (ht : (t : ℝ≥0∞) < T ω)
    (hs : s ≤ t) : geomLW W xL i s ω = geomLW (Lemma71C.frz W T t) xL i s ω :=
  geomLW_congr (Lemma71C.continuous_frz hc t ω) (fun _ hr => (Lemma71C.frz_eq ht (hr.trans hs)).symm) xL i

theorem geomRW_eq_frz (xR : Ω → Fin nR → ℝ) (j : Fin nR) {t s : ℝ≥0} {ω : Ω} (ht : (t : ℝ≥0∞) < T ω)
    (hs : s ≤ t) : geomRW W xR j s ω = geomRW (Lemma71C.frz W T t) xR j s ω :=
  geomRW_congr (Lemma71C.continuous_frz hc t ω) (fun _ hr => (Lemma71C.frz_eq ht (hr.trans hs)).symm) xR j

/-- **The left geometric coordinates of `𝓖₀`-measurable marks along a killed driver are adapted before `T`.** -/
theorem adaptedBefore_geomLW {𝓖 : Filtration ℝ≥0 mΩ} (hWa : AdaptedBefore 𝓖 T W) {xL : Ω → Fin nL → ℝ}
    (hx : Measurable[𝓖 0] xL) (i : Fin nL) : AdaptedBefore 𝓖 T (geomLW W xL i) := by
  intro t A hA
  have h1 : MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < T ω} := by
    have := hWa t univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have hx' : Measurable[(Filtration.const ℝ≥0 (𝓖 t) (𝓖.le t)) 0] xL := hx.mono (𝓖.mono (zero_le : (0 : ℝ≥0) ≤ t)) le_rfl
  have h2 : MeasurableSet[𝓖 t] ((fun ω => geomLW (Lemma71C.frz W T t) xL i t ω) ⁻¹' A) :=
    ((stronglyAdapted_geomLW (Lemma71C.stronglyAdapted_frz hWa t) (Lemma71C.continuous_frz hc t) hx' i
      t).measurable) hA
  have heq : {ω | (t : ℝ≥0∞) < T ω ∧ geomLW W xL i t ω ∈ A} =
      {ω | (t : ℝ≥0∞) < T ω} ∩ (fun ω => geomLW (Lemma71C.frz W T t) xL i t ω) ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨ht, hA⟩
      exact ⟨ht, by rwa [← geomLW_eq_frz hc xL i ht le_rfl]⟩
    · rintro ⟨ht, hA⟩
      exact ⟨ht, by rwa [geomLW_eq_frz hc xL i ht le_rfl]⟩
  rw [heq]
  exact h1.inter h2

/-- **The right geometric coordinates of `𝓖₀`-measurable marks along a killed driver are adapted before `T`.** -/
theorem adaptedBefore_geomRW {𝓖 : Filtration ℝ≥0 mΩ} (hWa : AdaptedBefore 𝓖 T W) {xR : Ω → Fin nR → ℝ}
    (hx : Measurable[𝓖 0] xR) (j : Fin nR) : AdaptedBefore 𝓖 T (geomRW W xR j) := by
  intro t A hA
  have h1 : MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < T ω} := by
    have := hWa t univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have hx' : Measurable[(Filtration.const ℝ≥0 (𝓖 t) (𝓖.le t)) 0] xR := hx.mono (𝓖.mono (zero_le : (0 : ℝ≥0) ≤ t)) le_rfl
  have h2 : MeasurableSet[𝓖 t] ((fun ω => geomRW (Lemma71C.frz W T t) xR j t ω) ⁻¹' A) :=
    ((stronglyAdapted_geomRW (Lemma71C.stronglyAdapted_frz hWa t) (Lemma71C.continuous_frz hc t) hx' j
      t).measurable) hA
  have heq : {ω | (t : ℝ≥0∞) < T ω ∧ geomRW W xR j t ω ∈ A} =
      {ω | (t : ℝ≥0∞) < T ω} ∩ (fun ω => geomRW (Lemma71C.frz W T t) xR j t ω) ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨ht, hA⟩
      exact ⟨ht, by rwa [← geomRW_eq_frz hc xR j ht le_rfl]⟩
    · rintro ⟨ht, hA⟩
      exact ⟨ht, by rwa [geomRW_eq_frz hc xR j ht le_rfl]⟩
  rw [heq]
  exact h1.inter h2

end Geom

/-! ### Changing a local martingale after the lifetime and on a null event -/

section Transfer

variable {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}

/-- A function supported on a `P`-null set of `𝓖₀` is a martingale when `𝓖₀` contains the measurable null sets. -/
theorem martingale_indicator_null (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) {G : Set Ω}
    (hG : MeasurableSet[𝓖 0] G) (hGc : P Gᶜ = 0) {f : Ω → ℝ} (hf : Measurable f) :
    Martingale (fun _ => Gᶜ.indicator f) 𝓖 P := by
  have hm : Measurable[𝓖 0] (Gᶜ.indicator f) := by
    intro B hB
    have e : Gᶜ.indicator f ⁻¹' B = (Gᶜ ∩ f ⁻¹' B) ∪ (G ∩ {_ω | (0 : ℝ) ∈ B}) := by
      ext ω
      by_cases hω : ω ∈ G
      · simp [hω]
      · simp [hω]
    rw [e]
    have hGm : MeasurableSet G := 𝓖.le 0 _ hG
    refine (hnull _ (hGm.compl.inter (hf hB)) (measure_mono_null inter_subset_left hGc)).union
      (hG.inter (MeasurableSet.const _))
  have hae : Gᶜ.indicator f =ᵐ[P] 0 := by
    have hGae : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGc
    filter_upwards [hGae] with ω hω
    simp [hω]
  exact martingale_const_fun 𝓖 P hm.stronglyMeasurable
    ((integrable_zero Ω ℝ P).congr hae.symm)

/-- **A local martingale before `ζ ≤ T` survives a change at times `≥ T` and on a null event of `𝓖₀`.** Let `X` be a
local martingale before `ζ`, right-continuous before `ζ`, let `G ∈ 𝓖₀` have full measure, let `A` be a nondecreasing
sequence of stopping times strictly below `T` on `G` and exhausting `[0, T)` there, and let `Y` agree with `X` on `G`
before `T`, with a measurable time-zero value. Then `Y` is a local martingale before `ζ` (localize at
`min (σₙ, Aₙ)` on `G` and at `0` off `G`; the stopped `Y` is the stopped `X` plus a martingale supported on `Gᶜ`). -/
theorem isLocalMartingaleBefore_of_eq_before (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
    {G : Set Ω} (hG : MeasurableSet[𝓖 0] G) (hGae : ∀ᵐ ω ∂P, ω ∈ G) {ζ T : Ω → WithTop ℝ≥0}
    (hζT : ∀ ω, ζ ω ≤ T ω) {A : ℕ → Ω → ℝ≥0} (hA : ∀ n, IsStoppingTime 𝓖 fun ω => (A n ω : WithTop ℝ≥0))
    (hAm : ∀ ω, Monotone fun n => A n ω) (hAT : ∀ n, ∀ ω ∈ G, (A n ω : WithTop ℝ≥0) < T ω)
    (hAex : ∀ ω ∈ G, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < T ω → ∃ n, t ≤ A n ω)
    {X Y : ℝ≥0 → Ω → ℝ} (hX : IsLocalMartingaleBefore 𝓖 P ζ X)
    (hXrc : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) < ζ ω → ContinuousWithinAt (X · ω) (Ici s) s)
    (hXY : ∀ ω ∈ G, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < T ω → X t ω = Y t ω) (hY0 : Measurable (Y 0)) :
    IsLocalMartingaleBefore 𝓖 P ζ Y := by
  classical
  obtain ⟨σ, hσ, hσζ, hσlim, hσmart⟩ := hX
  have hGt : ∀ t, MeasurableSet[𝓖 t] G := fun t => 𝓖.mono zero_le _ hG
  have hGc : P Gᶜ = 0 := ae_iff.1 hGae
  set σ' : ℕ → Ω → WithTop ℝ≥0 := fun n ω => if ω ∈ G then min (σ n ω) (A n ω) else 0 with hσ'
  have hσ'G : ∀ n, ∀ ω ∈ G, σ' n ω = min (σ n ω) (A n ω) := fun n ω hω => by simp [hσ', hω]
  have hσ'nG : ∀ n, ∀ ω, ω ∉ G → σ' n ω = 0 := fun n ω hω => by simp [hσ', hω]
  have hσ'σ : ∀ n ω, σ' n ω ≤ σ n ω := fun n ω => by
    by_cases hω : ω ∈ G
    · rw [hσ'G n ω hω]; exact min_le_left _ _
    · rw [hσ'nG n ω hω, ← WithTop.coe_zero]; exact WithTop.coe_le_iff.2 fun _ _ => zero_le
  have hσ'stop : ∀ n, IsStoppingTime 𝓖 (σ' n) := fun n => by
    intro t
    have hmin : IsStoppingTime 𝓖 fun ω => min (σ n ω) (A n ω) := (hσ n).min (hA n)
    have heq : {ω | σ' n ω ≤ (t : WithTop ℝ≥0)} = (G ∩ {ω | min (σ n ω) (A n ω) ≤ t}) ∪ Gᶜ := by
      ext ω
      by_cases hω : ω ∈ G
      · simp [hσ'G n ω hω, hω]
      · simp only [hσ'nG n ω hω, mem_ofPred_eq, mem_union, mem_inter_iff, hω, false_and, mem_compl_iff,
          not_false_eq_true, or_true, iff_true]
        exact WithTop.coe_le_coe.2 (zero_le : (0 : ℝ≥0) ≤ t)
    rw [heq]
    exact ((hGt t).inter (hmin t)).union (hGt t).compl
  -- the stopped `X` at `σ'` is a martingale
  have hXmart : ∀ n, Martingale (stoppedProcess X (σ' n)) 𝓖 P := fun n => by
    have hrc : ∀ ω t, ContinuousWithinAt (stoppedProcess X (σ n) · ω) (Ici t) t :=
      fun ω t => continuousWithinAt_stoppedProcess (hσζ n) hXrc ω t
    have h := InteractingSLE.Martingale.stoppedProcess_of_rightContinuous (hσmart n) hrc (hσ'stop n)
    rwa [stoppedProcess_stoppedProcess_of_le_right (fun ω => hσ'σ n ω)] at h
  -- `X 0` is measurable
  have hX0 : Measurable (X 0) := by
    have h := ((hσmart 0).1 0).measurable.mono (𝓖.le 0) le_rfl
    have e : stoppedProcess X (σ 0) 0 = X 0 := by
      funext ω
      simp only [stoppedProcess]
      congr 1
      exact MathFin.untopA_min_zero _
    rwa [e] at h
  refine ⟨σ', hσ'stop, fun n ω => (hσ'σ n ω).trans (hσζ n ω), ?_, fun n => ?_⟩
  · -- exhausting
    filter_upwards [hσlim, hGae] with ω hω hωG r hr
    obtain ⟨a, hra, haζ⟩ := WithTop.lt_iff_exists_coe_btwn.1 hr
    obtain ⟨n₀, hn₀⟩ := hAex ω hωG a (haζ.trans_le (hζT ω))
    filter_upwards [hω r hr, eventually_ge_atTop n₀] with n h1 h2
    rw [hσ'G n ω hωG]
    refine lt_min h1 (hra.trans_le ?_)
    exact WithTop.coe_le_coe.2 (hn₀.trans (hAm ω h2))
  · -- the stopped `Y` is the stopped `X` plus a null-supported time-zero martingale
    have heq : stoppedProcess Y (σ' n) = stoppedProcess X (σ' n) + fun _ => Gᶜ.indicator (Y 0 - X 0) := by
      funext t ω
      by_cases hω : ω ∈ G
      · simp only [Pi.add_apply, indicator_of_notMem (show ω ∉ Gᶜ from fun h => h hω), add_zero, stoppedProcess]
        have hlt : (min (t : WithTop ℝ≥0) (σ' n ω)) < T ω := by
          rw [hσ'G n ω hω]
          exact (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (hAT n ω hω))
        have hfin : min (t : WithTop ℝ≥0) (σ' n ω) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
        refine (hXY ω hω _ ?_).symm
        rwa [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
      · simp only [Pi.add_apply, indicator_of_mem (show ω ∈ Gᶜ from hω), stoppedProcess, hσ'nG n ω hω,
          Pi.sub_apply]
        have e : (min (t : WithTop ℝ≥0) 0).untopA = 0 := by
          rw [min_comm]
          exact MathFin.untopA_min_zero _
        rw [e]
        ring
    rw [heq]
    exact (hXmart n).add (martingale_indicator_null hnull hG hGc (hY0.sub hX0))

end Transfer

/-! ### The coupling mean of any extension of the word data along continuous coordinates -/

section Mean

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **Continuity in time of the coupling mean of any extension of the word data** along continuous ordered
coordinates, at a point not swallowed by `T'`: it is the explicit harmonic mean `meanHarmonic` of the centred
coordinates at `f_t(z)`, minus `χ arg f_t'(z)` (`Ito.couplingMean_eq_meanHarmonic`), continuous in `t`. -/
theorem continuousOn_couplingMean_of_ext {w : ℝ → ℝ} {vL : Fin nL → ℝ → ℝ} {vR : Fin nR → ℝ → ℝ} {T' : ℝ}
    (hT' : 0 ≤ T') (hw : ContinuousOn w (Icc 0 T')) (hvL : ∀ i, ContinuousOn (vL i) (Icc 0 T'))
    (hvR : ∀ j, ContinuousOn (vR j) (Icc 0 T'))
    (hord : ∀ t ∈ Icc 0 T', (∀ i, vL i t ≤ w t) ∧ ∀ j, w t ≤ vR j t) {u : ℝ → ℂ → ℝ}
    (hu : ∀ t ∈ Icc 0 T', IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => vL i t - w t) (fun j => vR j t - w t))
      (forceJumpSet (fun i => vL i t - w t) (fun j => vR j t - w t)) (u t))
    {z : ℂ} (hz : z ∈ H \ QuantumZipper.fwdHull w T') :
    ContinuousOn (fun t => couplingMean κ w t (u t) z) (Icc 0 T') := by
  have hsol := Ito.exists_isForwardSol_of_mem hT' hz
  have hpos : ∀ t ∈ Icc 0 T', 0 < (QuantumZipper.fwdMap w t z).im := fun t ht =>
    Ito.im_fwdMap_pos_of_continuousOn hT' hw hz.1 hsol ht
  have hf := Ito.continuousOn_fwdMap_of_continuousOn hT' hw hz.1 hsol
  have hL := Ito.continuousOn_logDerivFwd_of_continuousOn hT' hw hz.1 hsol
  have hvL' : ContinuousOn (fun t => fun i => vL i t - w t) (Icc 0 T') :=
    continuousOn_pi.2 fun i => (hvL i).sub hw
  have hvR' : ContinuousOn (fun t => fun j => vR j t - w t) (Icc 0 T') :=
    continuousOn_pi.2 fun j => (hvR j).sub hw
  have hmh := (continuousOn_meanHarmonic_prod κ ρL ρR).comp (hvL'.prodMk (hvR'.prodMk hf)) fun t ht => hpos t ht
  have hL' : ContinuousOn (fun t => QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd w t z).im) (Icc 0 T') :=
    continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hL)
  refine (hmh.sub hL').congr fun t ht => ?_
  exact Ito.couplingMean_eq_meanHarmonic (fun i => sub_nonpos.2 ((hord t ht).1 i))
    (fun j => sub_nonneg.2 ((hord t ht).2 j)) (hu t ht) (hpos t ht)

/-- `meanHarmonic` is measurable in the coordinates at a fixed point. -/
theorem measurable_meanHarmonic {α : Type*} [MeasurableSpace α] {vL : α → Fin nL → ℝ} {vR : α → Fin nR → ℝ}
    (hvL : Measurable vL) (hvR : Measurable vR) (ξ : ℂ) :
    Measurable fun a => Ito.meanHarmonic κ ρL ρR (vL a) (vR a) ξ := by
  unfold Ito.meanHarmonic
  have hL : ∀ i, Measurable fun a => Complex.arg (ξ - (vL a i : ℂ)) := fun i =>
    Complex.measurable_arg.comp (measurable_const.sub
      (Complex.measurable_ofReal.comp ((measurable_pi_apply i).comp hvL)))
  have hR : ∀ j, Measurable fun a => Complex.arg (ξ - (vR a j : ℂ)) := fun j =>
    Complex.measurable_arg.comp (measurable_const.sub
      (Complex.measurable_ofReal.comp ((measurable_pi_apply j).comp hvR)))
  refine measurable_const.mul ((measurable_const.sub (Finset.measurable_sum _ fun i _ =>
    measurable_const.mul (hL i))).sub (Finset.measurable_sum _ fun j _ => measurable_const.mul (hR j)))

end Mean

/-! ### Aux. lemma 122's hypotheses with the canonical phase -/

section Main

variable {nL nR : ℕ}

/-- A property holding almost surely holds on a full event of `𝓖₀` when `𝓖₀` contains the measurable null sets. -/
theorem exists_mem_zero_of_ae {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∃ G : Set Ω, MeasurableSet[𝓖 0] G ∧ (∀ᵐ ω ∂P, ω ∈ G) ∧ ∀ ω ∈ G, p ω := by
  have h0 : P (toMeasurable P {ω | ¬ p ω}) = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 h
  refine ⟨(toMeasurable P {ω | ¬ p ω})ᶜ, (hnull _ (measurableSet_toMeasurable _ _) h0).compl, ae_iff.2 ?_,
    fun ω hω => ?_⟩
  · simp only [mem_compl_iff, not_not, ofPred_mem_eq]
    exact h0
  · by_contra hcon
    exact hω (subset_toMeasurable _ _ hcon)

/-- The phase-`0` word data are the force-word data. -/
theorem phaseData_zero (k : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (vL : Fin (nL + 1) → ℝ)
    (vR : Fin (nR + 1) → ℝ) : phaseData k ρL ρR vL vR 0 = forceBoundaryData k ρL ρR vL vR := by
  funext x
  simp [phaseData]

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {κ : ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}

/-- **Aux. lemma 122's hypotheses before the lifetime, with the canonical phase `d = 0`, from the coupling clause of
the pocket word** (specification pp. 389–390 and p. 397). Let `𝓖` be a right-continuous filtration whose time-zero
σ-algebra contains the measurable null sets, `W` a driver started at `0`, continuous and adapted on `[0, T)` with
`T > 0`, almost surely unbounded near a finite `T`, and `xL`, `xR` `𝓖₀`-measurable marks. If a random distribution
`h` with integrable pairings satisfies the conditional-law clause of the optional hull specification with lifetime `T`
for the word `(ρL; ρR)` at the geometric force coordinates of the marks (`MartMeans.IsCouplingCharFun`), then
`HasPhaseMeansBefore κ ρL ρR P 𝓖 W xL xR 0 T`: for every choice of the extensions before `T`, the coupling means are
local martingales before `min (swallowTime z) T` and continuous on compact windows before swallowing. -/
theorem hasPhaseMeansBefore_zero_of_charFun {h : Ω → DistOn upperHalfPlaneOpens}
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) (hW0 : ∀ ω, W 0 ω = 0)
    (hT0 : ∀ ω, 0 < T ω) (hc : ∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω})
    (hWa : AdaptedBefore 𝓖 T W)
    (hunb : ∀ᵐ ω ∂P, T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)
    (hxLm : Measurable[𝓖 0] xL) (hxRm : Measurable[𝓖 0] xR)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W (geomLW W xL) (geomRW W xR) T h) :
    HasPhaseMeansBefore κ ρL ρR P 𝓖 W xL xR (fun _ _ => 0) T := by
  classical
  have hcW : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω} := hc
  have hord : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < T ω →
      (∀ i, geomLW W xL i t ω ≤ W t ω) ∧ ∀ j, W t ω ≤ geomRW W xR j t ω :=
    fun ω t ht => ⟨fun i => geomLW_le_of_lt (hcW ω) ht xL i, fun j => le_geomRW_of_lt (hcW ω) ht xR j⟩
  intro U hU
  simp only [phaseData_zero] at hU
  -- the extensions completed after `T` by the explicit one
  set U' : Ω → ℝ≥0 → ℂ → ℝ := fun ω t => if (t : ℝ≥0∞) < T ω then U ω t else
    MartChar.meanExt κ ρL ρR (W t ω) (fun i => geomLW W xL i t ω) (fun j => geomRW W xR j t ω) with hU'def
  have hU' : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω))
      (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω)) (U' ω t) := by
    intro ω t
    by_cases ht : (t : ℝ≥0∞) < T ω
    · simp only [hU'def, ht, ↓reduceIte]
      exact hU ω t ht
    · simp only [hU'def, ht, ↓reduceIte]
      exact MartChar.isBoundedHarmonicExtension_meanExt κ ρL ρR _ _ _
  -- the continuity clause for any extension before `T`
  have hcont : ∀ V : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < T ω → IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω))
      (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω)) (V ω t)) →
      ∀ ω (z : ℂ) (T' : ℝ), 0 ≤ T' → ((T'.toNNReal : ℝ≥0) : ℝ≥0∞) < T ω →
        z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' →
        ContinuousOn (fun t : ℝ => couplingMean κ (wpath W ω) t (V ω t.toNNReal) z) (Icc 0 T') := by
    intro V hV ω z T' hT' hT'T hz
    have hlt : ∀ t ∈ Icc (0 : ℝ) T', ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < T ω := fun t ht =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal ht.2)) hT'T
    have hmaps : MapsTo Real.toNNReal (Icc (0 : ℝ) T') {s : ℝ≥0 | (s : ℝ≥0∞) < T ω} := fun t ht => hlt t ht
    refine continuousOn_couplingMean_of_ext (vL := fun i t => geomLW W xL i t.toNNReal ω)
      (vR := fun j t => geomRW W xR j t.toNNReal ω) (u := fun t => V ω t.toNNReal) hT'
      ((hc ω).comp continuous_real_toNNReal.continuousOn hmaps)
      (fun i => (continuousOn_geomLW_of_lt hcW xL i ω).comp continuous_real_toNNReal.continuousOn hmaps)
      (fun j => (continuousOn_geomRW_of_lt hcW xR j ω).comp continuous_real_toNNReal.continuousOn hmaps)
      (fun t ht => hord ω _ (hlt t ht)) (fun t ht => hV ω _ (hlt t ht)) hz
  refine ⟨fun z hz => ?_, hcont U hU⟩
  -- the martingale clause
  have hz0 : z ≠ 0 := fun h0 => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h0 ▸ hz)
  obtain ⟨G₁, hG₁0, hG₁ae, hG₁⟩ := exists_mem_zero_of_ae hnull hunb
  have hann := Lemma71C.isAnnouncingSeq_annSeq (P := P) hWa hG₁0 hc hG₁ae hG₁
  obtain ⟨G, hG0, hGae, hloc⟩ := MartMeans2.exists_isLocalMartingaleBefore_meanProcOn hnull hWa
    (fun i => adaptedBefore_geomLW hc hWa hxLm i) (fun j => adaptedBefore_geomRW hc hWa hxRm j)
    (Eventually.of_forall fun ω => ⟨hW0 ω, hc ω,
      ⟨fun i => continuousOn_geomLW_of_lt hcW xL i ω, fun j => continuousOn_geomRW_of_lt hcW xR j ω⟩,
      fun t ht => hord ω t ht⟩)
    hann hint hcf U' hU' hz
  obtain ⟨G₂, hG₂0, hG₂ae, hG₂⟩ := exists_mem_zero_of_ae hnull (ae_all_iff.2 hann.2.2.1)
  obtain ⟨G₃, hG₃0, hG₃ae, hG₃⟩ := exists_mem_zero_of_ae hnull hann.2.2.2
  have hGG : ∀ᵐ ω ∂P, ω ∈ G ∩ G₂ ∩ G₃ := by
    filter_upwards [hGae, hG₂ae, hG₃ae] with ω h1 h2 h3 using ⟨⟨h1, h2⟩, h3⟩
  refine isLocalMartingaleBefore_of_eq_before (T := T) (X := MartMeans2.meanProcOn κ W U' z G) hnull
    ((hG0.inter hG₂0).inter hG₃0) hGG (fun ω => min_le_right _ _) hann.1 hann.2.1
    (fun n ω hω => hG₂ ω hω.1.2 n) (fun ω hω t ht => hG₃ ω hω.2 t ht) ?_ ?_ ?_ ?_
  · -- the local martingale, with the lifetime written in the other order
    convert hloc using 2 with ω
    exact min_comm _ _
  · -- right-continuity before the lifetime
    intro ω s hs
    by_cases hω : ω ∈ G
    · have hU'T : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < T ω → IsBoundedHarmonicExtension
          (forceBoundaryData κ ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω))
          (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω)) (U' ω t) :=
        fun ω t _ => hU' ω t
      have h := PhaseSelAdapt.continuousWithinAt_of_continuousOn_Icc hz
        (fun T' hT' hT'T hzK => hcont U' hU'T ω z T' hT' hT'T hzK) hs
      refine h.congr (fun t _ => ?_) ?_
      · simp only [MartMeans2.meanProcOn, hω, ↓reduceIte, MartMeans.meanProc, Real.toNNReal_coe]
        rfl
      · simp only [MartMeans2.meanProcOn, hω, ↓reduceIte, MartMeans.meanProc, Real.toNNReal_coe]
        rfl
    · have e : (fun t => MartMeans2.meanProcOn κ W U' z G t ω) = fun _ => 0 := by
        funext t
        simp only [MartMeans2.meanProcOn, hω, ↓reduceIte]
      rw [e]
      exact continuousWithinAt_const
  · -- agreement before `T` on the good event
    intro ω hω t ht
    have htT : (t : ℝ≥0∞) < T ω := ht
    simp only [MartMeans2.meanProcOn, hω.1.1, ↓reduceIte, MartMeans.meanProc, hU'def, htT]
    rfl
  · -- the time-zero mean is measurable
    have hm : ∀ ω, couplingMean κ (wpath W ω) 0 (U ω 0) z = Ito.meanHarmonic κ ρL ρR
        (fun i => geomLW W xL i 0 ω - W 0 ω) (fun j => geomRW W xR j 0 ω - W 0 ω) z := by
      intro ω
      have hw0 : wpath W ω 0 = 0 := by simp [wpath, hW0 ω]
      have hf0 : QuantumZipper.fwdMap (wpath W ω) 0 z = z := by
        rw [QuantumZipper.B5.fwdMap_zero_time _ (by rw [hw0]; exact hz0), hw0, Complex.ofReal_zero, sub_zero]
      have h0 := hord ω 0 (hT0 ω)
      rw [Ito.couplingMean_eq_meanHarmonic (fun i => sub_nonpos.2 (h0.1 i)) (fun j => sub_nonneg.2 (h0.2 j))
        (hU ω 0 (hT0 ω)) (by rw [hf0]; exact hz), hf0, MartMeans2.logDerivFwd_zero, Complex.zero_im, mul_zero,
        sub_zero]
    have hgL : ∀ i, Measurable fun ω => geomLW W xL i 0 ω := fun i => by
      intro A hA
      have h := adaptedBefore_geomLW hc hWa hxLm i 0 A hA
      have e : {ω | ((0 : ℝ≥0) : ℝ≥0∞) < T ω ∧ geomLW W xL i 0 ω ∈ A} = (fun ω => geomLW W xL i 0 ω) ⁻¹' A := by
        ext ω
        simp only [mem_ofPred_eq, mem_preimage, ENNReal.coe_zero, hT0 ω, true_and]
      rw [e] at h
      exact 𝓖.le 0 _ h
    have hgR : ∀ j, Measurable fun ω => geomRW W xR j 0 ω := fun j => by
      intro A hA
      have h := adaptedBefore_geomRW hc hWa hxRm j 0 A hA
      have e : {ω | ((0 : ℝ≥0) : ℝ≥0∞) < T ω ∧ geomRW W xR j 0 ω ∈ A} = (fun ω => geomRW W xR j 0 ω) ⁻¹' A := by
        ext ω
        simp only [mem_ofPred_eq, mem_preimage, ENNReal.coe_zero, hT0 ω, true_and]
      rw [e] at h
      exact 𝓖.le 0 _ h
    have e : (fun ω => couplingMean κ (wpath W ω) ((0 : ℝ≥0) : ℝ) (U ω 0) z) = fun ω => Ito.meanHarmonic κ ρL ρR
        (fun i => geomLW W xL i 0 ω - W 0 ω) (fun j => geomRW W xR j 0 ω - W 0 ω) z := by
      funext ω
      rw [NNReal.coe_zero]
      exact hm ω
    show Measurable fun ω => couplingMean κ (wpath W ω) ((0 : ℝ≥0) : ℝ) (U ω 0) z
    rw [e]
    have hW0m : Measurable fun ω => W 0 ω := by
      simp only [hW0]
      exact measurable_const
    exact measurable_meanHarmonic (measurable_pi_iff.2 fun i => (hgL i).sub hW0m)
      (measurable_pi_iff.2 fun j => (hgR j).sub hW0m) z

end Main

/-! ### hPW from the coupling clause of the pocket word -/

section Word

universe v

/-- A driven curve has a positive terminal capacity time. -/
theorem capLife_pos {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) : 0 < Lemma71C.capLife γ := by
  have h1 : 0 < Lemma71C.capClock γ 1 := by
    have := hγ.strictMonoOn_capClock (mem_Ici.2 le_rfl) (mem_Ici.2 zero_le_one) zero_lt_one
    rwa [hγ.capClock_zero] at this
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (Lemma71C.capClock γ (1 : ℕ)) := by
        rw [Nat.cast_one]
        exact ENNReal.ofReal_pos.2 h1
    _ ≤ Lemma71C.capLife γ := le_iSup (fun n : ℕ => ENNReal.ofReal (Lemma71C.capClock γ n)) 1

/-- **Lemma 7.25's pocket-word evolution (hPW) from the coupling clause of the pocket word** (specification
pp. 389–397 and p. 414): `PocketWordLife.pocketWordEvolution_of_hasPhaseMeans` with the canonical phase `d = 0`, its
`HasPhaseMeansBefore` supplied by `hasPhaseMeansBefore_zero_of_charFun` along the canonical driver of the relative
curve. On a standard Borel probability space with a right-continuous filtration whose time-zero σ-algebra contains the
null sets: a random driven curve `γ` with points of `ℍ` of arbitrarily large modulus and adapted filled prefixes; random
`𝓕₀`-measurable marks (seeds at `0`, the other left marks negative and the other right marks positive, ordered); weights
with seed weights `r_L, r_R < κ/2 − 4` and all side partial sums `> −2`; and a random distribution `h` with integrable
pairings satisfying the conditional-law clause of the optional hull specification for the word `(ρL; ρR)` at the
geometric force coordinates of the marks along the canonical driver, with lifetime `capLife γ` (the field-level input:
R.5 with Aux. lemmas 27–29 and 119–121, in the pocket chart). -/
theorem pocketWordEvolution_of_charFun {κ rL rR : ℝ} (hκ : 4 < κ) (hLd : rL < κ / 2 - 4) (hRd : rR < κ / 2 - 4)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL) (hρR : ρR 0 = rR)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    {Ω : Type v} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hpre : Lemma71C.IsPrefixAdapted 𝓕 γ) {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω)) {h : Ω → DistOn upperHalfPlaneOpens}
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P 𝓕 (fun t ω => Lemma71C.segDriver (γ ω) t)
      (geomLW (fun t ω => Lemma71C.segDriver (γ ω) t) xL) (geomRW (fun t ω => Lemma71C.segDriver (γ ω) t) xR)
      (fun ω => Lemma71C.capLife (γ ω)) h) :
    Sec7.Lemma725Ref.PocketWordEvolution.{v} κ rL rR := by
  have hM := hasPhaseMeansBefore_zero_of_charFun hnull (fun ω => (hγ ω).segDriver_spec.1)
    (fun ω => capLife_pos (hγ ω)) (fun ω => (hγ ω).segDriver_spec.2.1)
    (adaptedBefore_segDriver_of_isDrivenCurve hγ hpre)
    (Eventually.of_forall fun ω hfin C => PocketLife.exists_lt_abs_segDriver (hγ ω) (hunb ω) hfin C)
    hxLm hxRm hint hcf
  exact PocketWordLife.pocketWordEvolution_of_hasPhaseMeans hκ hLd hRd hρL hρR hsL hsR hγ hunb hpre hxLm hxRm
    hseedL hseedR hxLd hxRd hxLi hxRi (d := fun _ _ => 0) (fun _ _ _ _ => ⟨0, by simp⟩) hM

end Word

end InteractingSLE.Sec7.PocketPhaseMeans
