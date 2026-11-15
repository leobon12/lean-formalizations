/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS3ReachProofHit
import InteractingSLE.Spec.Supplement.DS2ReachRandInitKer

/-!
# Lemma DS3 in reach form, III: the restart at `τ_r` and the reduction to the entrance law

Packet PROVE-T14-DS3. The proof of Lemma DS3 (spec p. 554, `source/spec/p529-576.md` L601–L611) in reach form,
reduced to the convergence of the entrance laws (Aux. 4, spec pp. 28–30) at the restart time. The steps of the source
and where they are proved:

* "Choose a small deterministic positive time `t₀` … At `t₀` one may take the deterministic cross-gap bound
  `a = 4√t₀`": here the restart is at the hitting time `τ_r` of the cross-gap level `r` (`DS3Reach.tauR`), which is at
  most `r²/16`, with cross gap `r` there; before it the whole state is within `r` of the initial state, so for small `r`
  the reach event is unaffected by the initial interval (`reachEvent_of_restart`, `exists_restart_of_reachEvent`);
* "use the integrated Markov transition law": `RandInit.measure_restart_reach` (the conditional law of the reach event
  given `𝓕_{τ_r}` is the kernel `RandInit.reachKer` at the restart state);
* "repeat DS2's joint tightness and limit-identification argument with … random initial states": the Fatou lemma
  `DSReach.lintegral_le_liminf_of_tendsto` with the lower semicontinuity of the kernel
  (`RandInit.reachKer_le_liminf`, i.e. DS2);
* "Aux. 4 gives weak continuity of this two-seed entrance with bounded separated drifts … Entrance continuity makes this
  choice valid uniformly for the nearby parameter laws": the named statement **`EntranceStatement`** — for every
  tolerance `e` and every small `r`, the laws of the restart state on `{τ_r < ζ}` are within `e` (uniformly over test
  functions with values in `[0, 1]`) of laws `ν_m → ν₀` carried by the restart carrier.

Main result: **`ds3ReachStatement_of_entrance`**: `EntranceStatement → DS3ReachStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp12

namespace DS3Reach

open Sec2 Sec2.Assembly2 Sec2.Assembly3 DS2 DSReach RandInit

variable {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR)

/-- The carrier of the restart laws: ordered relative words with cross gap `≥ r` whose far labels are at distance
`≥ η/2` from the driver. -/
def RestartCarrier (mL mR : ℕ) (η r : ℝ) : Set (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ))) :=
  {x | IsOrderedForceWord x.2.1 x.2.2 ∧ r ≤ x.2.2 ⟨0, hnR⟩ - x.2.1 ⟨0, hnL⟩ ∧
    (∀ i : Fin nL, mL ≤ (i : ℕ) → x.2.1 i ≤ -(η / 2)) ∧ ∀ j : Fin nR, mR ≤ (j : ℕ) → η / 2 ≤ x.2.2 j}

/-- The restart state `(W_{T_r}, V_{T_r} − W_{T_r})`: the absolute driver and the word seen from it. -/
def restartState {Ω : Type*} (r : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) :=
  (W (TR hnL hnR r ζ VL VR ω) ω, (fun i => VL i (TR hnL hnR r ζ VL VR ω) ω - W (TR hnL hnR r ζ VL VR ω) ω),
    fun j => VR j (TR hnL hnR r ζ VL VR ω) ω - W (TR hnL hnR r ζ VL VR ω) ω)

/-- A **good evolution** (the output of `exists_good_modification_eq`): every path is continuous before a positive
lifetime, the initial values hold for every `ω`, the filtration is right-continuous and contains every null set,
off which every path is an integrated path. -/
def IsGoodEvolution (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (N : Set Ω) : Prop :=
  IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ ∧ 𝓖.IsRightContinuous ∧
    (∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
    (∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
    (∀ j ω, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧ (∀ ω, Continuous (B · ω)) ∧
    (∀ ω, W 0 ω = 0) ∧ (∀ i ω, VL i 0 ω = xL i) ∧ (∀ j ω, VR j 0 ω = xR j) ∧ (∀ ω, 0 < ζ ω) ∧
    MeasurableSet N ∧ P N = 0 ∧ (∀ N' : Set Ω, MeasurableSet N' → P N' = 0 → ∀ t, MeasurableSet[𝓖 t] N') ∧
    ∀ ω, ω ∉ N → IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (B · ω) (ζ ω)

/-- The entrance bound at level `r` with tolerance `e` for the law `ν` and the weights `(ρL, ρR)`: for every good
evolution and every measurable test function with values in `[0, 1]`, the law of the restart state on `{τ_r < ζ}`
(off the null set) integrates it to within `e` of `ν`. -/
def EntranceBound (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (r e : ℝ) (ν : ProbabilityMeasure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))) : Prop :=
  ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (N : Set Ω),
    IsGoodEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ N →
    ∀ g : ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) → ℝ≥0∞, Measurable g → (∀ x, g x ≤ 1) →
      (∫⁻ ω in {ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ, g (restartState hnL hnR r ζ W VL VR ω) ∂P ≤
          ∫⁻ x, g x ∂(ν : Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))) + ENNReal.ofReal e) ∧
        ∫⁻ x, g x ∂(ν : Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))) ≤
          ∫⁻ ω in {ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ, g (restartState hnL hnR r ζ W VL VR ω) ∂P +
            ENNReal.ofReal e

/-- **Named statement: the entrance law at the restart (Aux. 4, spec pp. 28–30, in the form used by DS3).** For the
data of `DS3ReachStatement` (both nearest labels at the driver, the other labels `η`-separated, the far labels not at
the driver, (DS1.1) uniform, converging weights) and every tolerance `e > 0`, for all small `r` there are laws
`ν_m → ν₀` carried by the restart carrier with the entrance bounds at level `r` and tolerance `e`. -/
def EntranceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR) (mL mR : ℕ) (Rw ε η : ℝ),
    0 < ε → 0 < η →
    ∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : ℕ → Fin nL → ℝ) (ρR : ℕ → Fin nR → ℝ) (ρL₀ : Fin nL → ℝ)
      (ρR₀ : Fin nR → ℝ),
      xL ⟨0, hnL⟩ = 0 → xR ⟨0, hnR⟩ = 0 → (∀ i, xL i ≠ 0 → xL i ≤ -η) → (∀ j, xR j ≠ 0 → η ≤ xR j) →
      (∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≠ 0) → (∀ j : Fin nR, mR ≤ (j : ℕ) → xR j ≠ 0) →
      (∀ m, IsDS1Word mL mR Rw ε xL xR (ρL m) (ρR m)) → IsDS1Word mL mR Rw ε xL xR ρL₀ ρR₀ →
      Tendsto ρL atTop (𝓝 ρL₀) → Tendsto ρR atTop (𝓝 ρR₀) →
      ∀ e : ℝ, 0 < e → ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r : ℝ, 0 < r → r ≤ r₁ →
        ∃ (ν : ℕ → ProbabilityMeasure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ))))
          (ν₀ : ProbabilityMeasure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))),
          Tendsto ν atTop (𝓝 ν₀) ∧
          (∀ m, (ν m : Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))) (RestartCarrier hnL hnR mL mR η r)ᶜ = 0) ∧
          (ν₀ : Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))) (RestartCarrier hnL hnR mL mR η r)ᶜ = 0 ∧
          (∀ m, EntranceBound.{u} hnL hnR κ xL xR (ρL m) (ρR m) r e (ν m)) ∧
          EntranceBound.{u} hnL hnR κ xL xR ρL₀ ρR₀ r e ν₀

/-! ### Pathwise steps -/

section Path

variable {Ω : Type*} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
  {r : ℝ}

theorem coe_TR_eq (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))
    (hr0 : 0 ≤ r) (hr4 : r ≤ 4) : (TR hnL hnR r ζ VL VR ω : ℝ≥0∞) = tauR hnL hnR r ζ VL VR ω := by
  rw [coe_TR, min_eq_left]
  refine (tauR_le hnL hnR hp hr0).trans ?_
  rw [← ENNReal.coe_one, ENNReal.coe_le_coe, Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
  nlinarith

theorem TR_le_sq (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))
    (hr0 : 0 ≤ r) (hr4 : r ≤ 4) : (TR hnL hnR r ζ VL VR ω : ℝ) ≤ r ^ 2 / 16 := by
  have h := tauR_le hnL hnR hp hr0
  rw [← coe_TR_eq hnL hnR hp hr0 hr4, ENNReal.coe_le_coe] at h
  have h2 := NNReal.coe_le_coe.2 h
  rwa [Real.coe_toNNReal _ (by positivity)] at h2

/-- **The restarted reach event is inside the reach event** (for small `r`): the initial interval up to `τ_r` stays in
the ball of radius `r` around the initial state. -/
theorem reachEvent_of_restart (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))
    (hL0 : xL ⟨0, hnL⟩ = 0) (hR0 : xR ⟨0, hnR⟩ = 0) (hr0 : 0 ≤ r) (hr4 : r ≤ 4) {T : ℝ≥0} (hrT : r ^ 2 ≤ T)
    {O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))}
    (hball : Metric.closedBall ((0 : ℝ), xL, xR) r ⊆ Bf)
    (hτ : tauR hnL hnR r ζ VL VR ω < ζ ω)
    (h : ω ∈ restartReach (TR hnL hnR r ζ VL VR) (T - (r ^ 2).toNNReal) O Bf W VL VR ζ) :
    ω ∈ reachEvent T O Bf W VL VR ζ := by
  obtain ⟨s, hsT, hsζ, hsO, hsB⟩ := h
  set τ := TR hnL hnR r ζ VL VR ω with hτdef
  have hτe : (τ : ℝ≥0∞) = tauR hnL hnR r ζ VL VR ω := coe_TR_eq hnL hnR hp hr0 hr4
  have hτr : (τ : ℝ) ≤ r ^ 2 := (TR_le_sq hnL hnR hp hr0 hr4).trans (by nlinarith [sq_nonneg r])
  refine ⟨τ + s, ?_, ?_, hsO, fun u hu => ?_⟩
  · have h1 : (s : ℝ) < T - r ^ 2 := by
      have := NNReal.coe_lt_coe.2 hsT
      rwa [NNReal.coe_sub (Real.toNNReal_le_iff_le_coe.2 hrT), Real.coe_toNNReal _ (sq_nonneg r)] at this
    rw [← NNReal.coe_lt_coe, NNReal.coe_add]
    linarith
  · rw [ENNReal.coe_add]
    exact lt_tsub_iff_left.1 hsζ
  · by_cases huτ : u ≤ τ
    · have huζ : (u : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by rw [hτe.symm]; exact_mod_cast huτ) hτ
      have hD := crossGap_le_of_le_tauR hnL hnR hp hL0 hR0 hr0 (by rw [← hτe]; exact_mod_cast huτ) huζ
      exact hball (Metric.mem_closedBall.2 ((dist_state_le_crossGap hnL hnR hp hL0 hR0 huζ).trans hD))
    · push Not at huτ
      have e : u = τ + (u - τ) := (add_tsub_cancel_of_le huτ.le).symm
      rw [e]
      exact hsB _ (tsub_le_iff_left.2 hu)

/-- A reach witness can be taken at a positive time. -/
theorem exists_pos_witness (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))
    {T : ℝ≥0} {O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hO : IsOpen O) (hBo : IsOpen Bf)
    (h : ω ∈ reachEvent T O Bf W VL VR ζ) :
    ∃ t : ℝ≥0, 0 < t ∧ t < T ∧ (t : ℝ≥0∞) < ζ ω ∧ Coupling.stateAt W VL VR t ω ∈ O ∧
      ∀ u ≤ t, Coupling.stateAt W VL VR u ω ∈ Bf := by
  obtain ⟨t, htT, htζ, htO, htB⟩ := h
  rcases eq_or_ne t 0 with ht0 | ht0
  · subst ht0
    have hc : ContinuousWithinAt (fun u => Coupling.stateAt W VL VR u ω) {u | (u : ℝ≥0∞) < ζ ω} 0 :=
      (hp.continuousOn_w.prodMk ((continuousOn_pi.2 fun i => hp.continuousOn_vL i).prodMk
        (continuousOn_pi.2 fun j => hp.continuousOn_vR j))) 0 htζ
    have hU : {u : ℝ≥0 | (u : ℝ≥0∞) < ζ ω} ∈ 𝓝 (0 : ℝ≥0) :=
      (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds htζ
    have hev : ∀ᶠ u in 𝓝 (0 : ℝ≥0), Coupling.stateAt W VL VR u ω ∈ O ∩ Bf ∧ (u : ℝ≥0∞) < ζ ω ∧ u < T :=
      ((((hc.continuousAt hU).tendsto.eventually ((hO.inter hBo).mem_nhds ⟨htO, htB 0 le_rfl⟩)).and
        hU).and (gt_mem_nhds htT)).mono fun u h => ⟨h.1.1, h.1.2, h.2⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set t' : ℝ≥0 := ⟨δ / 2, by positivity⟩
    have hdist : ∀ u ≤ t', dist u 0 < δ := fun u hu => by
      rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg u)]
      have : (u : ℝ) ≤ δ / 2 := hu
      linarith
    obtain ⟨⟨hO', -⟩, hζ', hT'⟩ := hball (hdist t' le_rfl)
    have ht'0 : 0 < t' := by
      rw [← NNReal.coe_pos]
      show (0 : ℝ) < δ / 2
      positivity
    exact ⟨t', ht'0, hT', hζ', hO', fun u hu => (hball (hdist u hu)).1.2⟩
  · exact ⟨t, pos_iff_ne_zero.2 ht0, htT, htζ, htO, htB⟩

/-- **A reach path is, for all small `r`, in the restarted reach event at `τ_r`.** -/
theorem eventually_restart_of_reachEvent
    (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))
    {T : ℝ≥0} {O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hO : IsOpen O) (hBo : IsOpen Bf)
    (h : ω ∈ reachEvent T O Bf W VL VR ζ) {rs : ℕ → ℝ} (hrs0 : ∀ j, 0 ≤ rs j) (hrs : Tendsto rs atTop (𝓝 0)) :
    ∀ᶠ j in atTop, tauR hnL hnR (rs j) ζ VL VR ω < ζ ω ∧
      ω ∈ restartReach (TR hnL hnR (rs j) ζ VL VR) (T - (rs j ^ 2).toNNReal) O Bf W VL VR ζ := by
  obtain ⟨t, ht0, htT, htζ, htO, htB⟩ := exists_pos_witness hp hO hBo h
  have hD := DS3.four_mul_sqrt_le_crossGap hnL hnR hp htζ
  simp only [DS3.crossGap] at hD
  have hsqrt : 0 < 4 * Real.sqrt t := by positivity
  have hTt : 0 < (T : ℝ) - t := sub_pos.2 (by exact_mod_cast htT)
  have hev : ∀ᶠ j in atTop, rs j < 4 * Real.sqrt t ∧ rs j ^ 2 < (T : ℝ) - t ∧ rs j ≤ 4 := by
    have h2 : Tendsto (fun j => rs j ^ 2) atTop (𝓝 0) := by simpa using hrs.pow 2
    exact (((hrs.eventually (gt_mem_nhds hsqrt)).and (h2.eventually (gt_mem_nhds hTt))).and
      (hrs.eventually (ge_mem_nhds (show (0 : ℝ) < 4 by norm_num)))).mono fun j h => ⟨h.1.1, h.1.2, h.2⟩
  filter_upwards [hev] with j ⟨h1, h2, h4⟩
  have hr0 := hrs0 j
  -- `τ_r ≤ t`
  have hτt : tauR hnL hnR (rs j) ζ VL VR ω ≤ t := by
    refine hitTime_le_of_mem ?_
    simp only [killedFam, Girsanov.killed_of_lt htζ, gapR]
    linarith
  have hτ := coe_TR_eq hnL hnR hp hr0 h4
  set τ := TR hnL hnR (rs j) ζ VL VR ω with hτdef
  have hτt' : τ ≤ t := by rw [← ENNReal.coe_le_coe, hτ]; exact hτt
  refine ⟨lt_of_le_of_lt hτt htζ, t - τ, ?_, ?_, ?_, fun u hu => ?_⟩
  · have hrT : rs j ^ 2 ≤ T := by linarith [NNReal.coe_nonneg t]
    rw [← NNReal.coe_lt_coe, NNReal.coe_sub (Real.toNNReal_le_iff_le_coe.2 hrT),
      Real.coe_toNNReal _ (sq_nonneg _)]
    have : ((t - τ : ℝ≥0) : ℝ) ≤ t := by rw [NNReal.coe_sub hτt']; linarith [NNReal.coe_nonneg τ]
    linarith
  · rw [lt_tsub_iff_left, ← ENNReal.coe_add, add_tsub_cancel_of_le hτt']
    exact htζ
  · rw [add_tsub_cancel_of_le hτt']; exact htO
  · exact htB _ ((add_le_add (le_refl τ) hu).trans (by rw [add_tsub_cancel_of_le hτt']))

/-- **The restart state lies in the carrier.** -/
theorem restartState_mem_carrier
    (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))
    (hL0 : xL ⟨0, hnL⟩ = 0) (hR0 : xR ⟨0, hnR⟩ = 0) {mL mR : ℕ} {η : ℝ}
    (hfarL : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -η) (hfarR : ∀ j : Fin nR, mR ≤ (j : ℕ) → η ≤ xR j)
    (hr0 : 0 ≤ r) (hrη : r ≤ η / 4) (hr4 : r ≤ 4) (hτ : tauR hnL hnR r ζ VL VR ω < ζ ω) :
    restartState hnL hnR r ζ W VL VR ω ∈ RestartCarrier hnL hnR mL mR η r := by
  have hτe := coe_TR_eq hnL hnR hp hr0 hr4
  set τ := TR hnL hnR r ζ VL VR ω with hτdef
  have hτζ : (τ : ℝ≥0∞) < ζ ω := by rw [hτe]; exact hτ
  have hτ' : (tauR hnL hnR r ζ VL VR ω).toNNReal = τ := by
    rw [← hτe, ENNReal.toNNReal_coe]
  have hDge := le_crossGap_tauR hnL hnR hp hτ
  rw [hτ'] at hDge
  have hDle := crossGap_le_of_le_tauR hnL hnR hp hL0 hR0 hr0 (le_of_eq hτe) hτζ
  have hdist := dist_state_le_crossGap hnL hnR hp hL0 hR0 hτζ
  have hW : |W τ ω| ≤ r := by
    rw [Prod.dist_eq] at hdist
    have h1 : dist (W τ ω) 0 ≤ r := (le_max_left _ _).trans (hdist.trans hDle)
    rwa [Real.dist_eq, sub_zero] at h1
  refine ⟨⟨fun i i' hii' => ?_, fun i => ?_, fun j j' hjj' => ?_, fun j => ?_⟩, ?_, fun i hi => ?_,
    fun j hj => ?_⟩
  · simp only [restartState]; linarith [hp.antitone_vL hτζ hii']
  · simp only [restartState]; linarith [hp.vL_le_w hτζ i]
  · simp only [restartState]; linarith [hp.monotone_vR hτζ hjj']
  · simp only [restartState]; linarith [hp.w_le_vR hτζ j]
  · simp only [restartState, cg] at hDge ⊢; linarith
  · have h1 := hp.vL_le_of_le (zero_le (a := τ)) hτζ i
    simp only [hp.vL_zero] at h1
    have h2 := hfarL i hi
    simp only [restartState]
    rw [abs_le] at hW
    linarith [hW.1]
  · have h1 := hp.le_vR_of_le (zero_le (a := τ)) hτζ j
    simp only [hp.vR_zero] at h1
    have h2 := hfarR j hj
    simp only [restartState]
    rw [abs_le] at hW
    linarith [hW.2]

end Path

/-- Carrier points are DS1 words for every DS1 weights and are not threshold states. -/
theorem ds1_of_mem_carrier {mL mR : ℕ} {Rw ε η r : ℝ} (hε : 0 < ε) (hη : 0 < η) {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hw : IsDS1Word mL mR Rw ε xL xR ρL ρR)
    {x : ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ))} (hx : x ∈ RestartCarrier hnL hnR mL mR η r) :
    IsDS1Word mL mR Rw ε x.2.1 x.2.2 ρL ρR ∧ ¬ ForceWord.ThresholdCondition ρL ρR 0 x.2.1 x.2.2 := by
  have hw' : IsDS1Word mL mR Rw ε x.2.1 x.2.2 ρL ρR := ⟨hx.1, hw.2⟩
  refine ⟨hw', ?_⟩
  have hord : IsOrderedState (((0 : ℝ), x.2.1, x.2.2) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
    ⟨hx.1.1, hx.1.2.1, hx.1.2.2.2, hx.1.2.2.1⟩
  have hbuf : InCBuffer mL mR ‖x.2‖ (η / 2) (((0 : ℝ), x.2.1, x.2.2) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) := by
    refine ⟨⟨by simp, fun i => ?_, fun j => ?_⟩, fun j hj => ?_, fun i hi => ?_⟩
    · rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x.2.1 i).trans (norm_fst_le x.2)
    · rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x.2.2 j).trans (norm_snd_le x.2)
    · simp only [sub_zero]; exact hx.2.2.2 j hj
    · simp only [zero_sub]; linarith [hx.2.2.1 i hi]
  exact not_threshold_of_inCBuffer hε (by positivity) hw' hord hbuf

/-! ### The reduction -/

/-- **Lemma DS3 in reach form from the entrance law.** -/
theorem ds3ReachStatement_of_entrance (hent : EntranceStatement.{u}) : DS3ReachStatement.{u} := by
  intro κ hκ nL nR hnL hnR mL mR Rw ε g η hε hg hη xL xR ρL ρR ρL₀ ρR₀ hL0 hR0 hLη hRη hw hw₀ hρL hρR
    Ω mΩ P 𝓕 W VL VR B ζ hE Ω₀ mΩ₀ P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ hE₀ T R O Bf hO hBo hBR
  classical
  have hP : ∀ m, IsProbabilityMeasure (P m) := fun m => (hE m).1.isProbabilityMeasure'
  have hP₀ : IsProbabilityMeasure P₀ := hE₀.1.isProbabilityMeasure'
  set s₀ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) := ((0 : ℝ), xL, xR) with hs₀def
  -- if the initial state is not in the buffer, the reach event is null
  by_cases hs₀ : s₀ ∈ Bf
  swap
  · have hnull : P₀ (reachEvent T O Bf W₀ VL₀ VR₀ ζ₀) = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hE₀.2.2.2.2)
      rintro ω ⟨t, -, -, -, hB⟩ hpath
      apply hs₀
      have h0 := hB 0 zero_le
      have hfp := hpath.isForcePath
      have e : Coupling.stateAt W₀ VL₀ VR₀ 0 ω = s₀ := by
        simp only [Coupling.stateAt, hs₀def, hfp.w_zero]
        exact Prod.ext rfl (Prod.ext (funext hfp.vL_zero) (funext hfp.vR_zero))
      rwa [e] at h0
    rw [hnull]
    exact zero_le
  have hbuf₀ := hBR s₀ hs₀
  -- far labels are not at the driver
  have hfarL' : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≠ 0 := fun i hi h0 => by
    have := hbuf₀.2.2 i hi
    simp only [hs₀def, h0, sub_zero] at this
    linarith
  have hfarR' : ∀ j : Fin nR, mR ≤ (j : ℕ) → xR j ≠ 0 := fun j hj h0 => by
    have := hbuf₀.2.1 j hj
    simp only [hs₀def, h0, sub_zero] at this
    linarith
  have hfarL : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -η := fun i hi => hLη i (hfarL' i hi)
  have hfarR : ∀ j : Fin nR, mR ≤ (j : ℕ) → η ≤ xR j := fun j hj => hRη j (hfarR' j hj)
  -- the seed is not a threshold state
  have hord₀ : IsOrderedState s₀ := ⟨(hw₀.1).1, fun i => (hw₀.1).2.1 i, fun j => (hw₀.1).2.2.2 j, (hw₀.1).2.2.1⟩
  have hthr : ∀ m, ¬ ForceWord.ThresholdCondition (ρL m) (ρR m) 0 xL xR := fun m =>
    not_threshold_of_inCBuffer hε hg (hw m) hord₀ hbuf₀.inCBuffer
  have hthr₀ : ¬ ForceWord.ThresholdCondition ρL₀ ρR₀ 0 xL xR :=
    not_threshold_of_inCBuffer hε hg hw₀ hord₀ hbuf₀.inCBuffer
  -- good modifications
  choose 𝓖 h𝓖 W' VL' VR' B' ζ' hE' hW'c hVL'c hVR'c hB'c hW'0 hVL'0 hVR'0 hζ'0 hnull N hNm hN0 hNeq using
    fun m => exists_good_modification_eq (hthr m) (hE m)
  obtain ⟨𝓖₀, h𝓖₀, W₀', VL₀', VR₀', B₀', ζ₀', hE₀', hW₀'c, hVL₀'c, hVR₀'c, hB₀'c, hW₀'0, hVL₀'0, hVR₀'0,
    hζ₀'0, hnull₀, N₀, hN₀m, hN₀0, hN₀eq⟩ := exists_good_modification_eq hthr₀ hE₀
  have hgood : ∀ m, IsGoodEvolution κ xL xR (ρL m) (ρR m) (P m) (𝓖 m) (W' m) (VL' m) (VR' m) (B' m) (ζ' m)
      (N m) := fun m => ⟨hE' m, h𝓖 m, hW'c m, hVL'c m, hVR'c m, hB'c m, hW'0 m, hVL'0 m, hVR'0 m, hζ'0 m,
        hNm m, hN0 m, hnull m, fun ω hω => (hNeq m ω hω).2.2.2.2⟩
  have hgood₀ : IsGoodEvolution κ xL xR ρL₀ ρR₀ P₀ 𝓖₀ W₀' VL₀' VR₀' B₀' ζ₀' N₀ :=
    ⟨hE₀', h𝓖₀, hW₀'c, hVL₀'c, hVR₀'c, hB₀'c, hW₀'0, hVL₀'0, hVR₀'0, hζ₀'0, hN₀m, hN₀0,
      hnull₀, fun ω hω => (hN₀eq ω hω).2.2.2.2⟩
  -- the reach events agree off the null sets
  have hreach_eq : ∀ {Ω' : Type u} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} {N' : Set Ω'}
      {W₁ W₂ : ℝ≥0 → Ω' → ℝ} {VL₁ VL₂ : Fin nL → ℝ≥0 → Ω' → ℝ} {VR₁ VR₂ : Fin nR → ℝ≥0 → Ω' → ℝ}
      {ζ₁ ζ₂ : Ω' → ℝ≥0∞}, P' N' = 0 → (∀ ω, ω ∉ N' → ζ₂ ω = ζ₁ ω ∧ (∀ t, W₂ t ω = W₁ t ω) ∧
        (∀ i t, VL₂ i t ω = VL₁ i t ω) ∧ (∀ j t, VR₂ j t ω = VR₁ j t ω)) →
      P' (reachEvent T O Bf W₁ VL₁ VR₁ ζ₁) = P' (reachEvent T O Bf W₂ VL₂ VR₂ ζ₂) := by
    intro Ω' mΩ' P' N' W₁ W₂ VL₁ VL₂ VR₁ VR₂ ζ₁ ζ₂ hN' heq
    refine measure_congr ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN'] with ω hω
    obtain ⟨h1, h2, h3, h4⟩ := heq ω hω
    have hs : ∀ t, Coupling.stateAt W₂ VL₂ VR₂ t ω = Coupling.stateAt W₁ VL₁ VR₁ t ω := fun t => by
      simp only [Coupling.stateAt, h2, h3, h4]
    simp only [reachEvent, mem_ofPred_eq, hs, h1]
  rw [hreach_eq hN₀0 (fun ω hω => let h := hN₀eq ω hω; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)]
  simp_rw [hreach_eq (hN0 _) (fun ω hω => let h := hNeq _ ω hω; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)]
  -- the margin of the initial state in the buffer
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.1 hBo s₀ hs₀
  have hball : ∀ r : ℝ, r < r₂ → Metric.closedBall s₀ r ⊆ Bf := fun r hr =>
    (Metric.closedBall_subset_ball hr).trans hball₂
  -- a zero horizon gives an empty reach event
  rcases eq_or_ne T 0 with hT0 | hT0
  · have : reachEvent T O Bf W₀' VL₀' VR₀' ζ₀' = ∅ := by
      ext ω; simp only [reachEvent, hT0, not_lt_zero, false_and, exists_false, mem_ofPred_eq, mem_empty_iff_false]
    rw [this, measure_empty]; exact zero_le
  have hTpos : (0 : ℝ) < T := by exact_mod_cast pos_iff_ne_zero.2 hT0
  have hBfc := compl_nonempty_of_inBuffer hBR
  refine ENNReal.le_of_forall_pos_le_add fun e he _ => ?_
  have he4 : (0 : ℝ) < (e : ℝ) / 4 := by positivity
  obtain ⟨r₁, hr₁, hent'⟩ := hent κ hκ hnL hnR mL mR Rw ε η hε hη xL xR ρL ρR ρL₀ ρR₀ hL0 hR0 hLη hRη
    hfarL' hfarR' hw hw₀ hρL hρR ((e : ℝ) / 4) he4
  -- the levels `r_j`
  set r₀ : ℝ := min (min r₁ (η / 4)) (min (r₂ / 2) (min 4 (Real.sqrt T / 2))) with hr₀def
  have hr₀ : 0 < r₀ := by
    have : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
    positivity
  set rs : ℕ → ℝ := fun j => r₀ / ((j : ℝ) + 1) with hrsdef
  have hrs0 : ∀ j, 0 < rs j := fun j => by positivity
  have hrs_le : ∀ j, rs j ≤ r₀ := fun j => div_le_self hr₀.le (by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith)
  have hrs : Tendsto rs atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul r₀
    rw [mul_zero] at this
    refine this.congr fun x => ?_
    simp only [hrsdef, div_eq_mul_inv, one_mul]
  -- the restarted events at level `r`
  set E : (r : ℝ) → Set Ω₀ := fun r => ({ω | tauR hnL hnR r ζ₀' VL₀' VR₀' ω < ζ₀' ω} ∩ N₀ᶜ) ∩
    restartReach (TR hnL hnR r ζ₀' VL₀' VR₀') (T - (r ^ 2).toNNReal) O Bf W₀' VL₀' VR₀' ζ₀' with hEdef
  -- step 1: a level with `P₀(reach) ≤ P₀(E_r) + e/4`
  have hcover : reachEvent T O Bf W₀' VL₀' VR₀' ζ₀' ∩ N₀ᶜ ⊆ ⋃ J, ⋂ j ∈ Ici J, E (rs j) := by
    rintro ω ⟨hω, hωN⟩
    have hp := ((hN₀eq ω hωN).2.2.2.2).isForcePath
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (eventually_restart_of_reachEvent hnL hnR hp hO hBo hω
      (fun j => (hrs0 j).le) hrs)
    exact mem_iUnion.2 ⟨J, mem_iInter₂.2 fun j hj => ⟨⟨(hJ j hj).1, hωN⟩, (hJ j hj).2⟩⟩
  have hmono : Monotone fun J => ⋂ j ∈ Ici J, E (rs j) := fun J J' hJJ' =>
    biInter_subset_biInter_left fun j hj => le_trans hJJ' hj
  have hstep1 : ∃ j, P₀ (reachEvent T O Bf W₀' VL₀' VR₀' ζ₀') ≤ P₀ (E (rs j)) + ENNReal.ofReal ((e : ℝ) / 4) := by
    have h1 : P₀ (reachEvent T O Bf W₀' VL₀' VR₀' ζ₀') ≤ ⨆ J, P₀ (⋂ j ∈ Ici J, E (rs j)) := by
      rw [← hmono.measure_iUnion]
      calc P₀ (reachEvent T O Bf W₀' VL₀' VR₀' ζ₀') = P₀ (reachEvent T O Bf W₀' VL₀' VR₀' ζ₀' ∩ N₀ᶜ) := by
            refine (measure_congr ?_).symm
            filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN₀0] with ω hω
            simp only [mem_inter_iff, mem_compl_iff, hω, not_false_eq_true, and_true]
        _ ≤ _ := measure_mono hcover
    have hpos : ENNReal.ofReal ((e : ℝ) / 4) ≠ 0 := by simpa using he4
    have hsup_ne : (⨆ J, P₀ (⋂ j ∈ Ici J, E (rs j))) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun J => prob_le_one)
    have h2 : P₀ (reachEvent T O Bf W₀' VL₀' VR₀' ζ₀') <
        ⨆ J, (P₀ (⋂ j ∈ Ici J, E (rs j)) + ENNReal.ofReal ((e : ℝ) / 4)) := by
      rw [← ENNReal.iSup_add]; exact h1.trans_lt (ENNReal.lt_add_right hsup_ne hpos)
    obtain ⟨J, hJ⟩ := lt_iSup_iff.1 h2
    exact ⟨J, hJ.le.trans (add_le_add (measure_mono (biInter_subset_of_mem (mem_Ici.2 le_rfl))) le_rfl)⟩
  obtain ⟨j, hj⟩ := hstep1
  set r := rs j with hrdef
  have hr0 : 0 < r := hrs0 j
  have hr₀le : r ≤ r₀ := hrs_le j
  have hr1 : r ≤ r₁ := hr₀le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrη : r ≤ η / 4 := hr₀le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr2 : r < r₂ := lt_of_le_of_lt (hr₀le.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (by linarith)
  have hr4 : r ≤ 4 := hr₀le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrT : r ^ 2 ≤ T := by
    have h1 : r ≤ Real.sqrt T / 2 :=
      hr₀le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have h2 : r ^ 2 ≤ (Real.sqrt T / 2) ^ 2 := pow_le_pow_left₀ hr0.le h1 2
    have h3 : (Real.sqrt T / 2) ^ 2 = T / 4 := by
      rw [div_pow, Real.sq_sqrt (NNReal.coe_nonneg T)]; norm_num
    linarith
  -- the restart identity for good evolutions
  set T' : ℝ≥0 := T - (r ^ 2).toNNReal with hT'def
  have hrestart : ∀ {Ω' : Type u} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} {𝓖' : Filtration ℝ≥0 mΩ'}
      {W₁ : ℝ≥0 → Ω' → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω' → ℝ} {VR₁ : Fin nR → ℝ≥0 → Ω' → ℝ} {B₁ : ℝ≥0 → Ω' → ℝ}
      {ζ₁ : Ω' → ℝ≥0∞} {N' : Set Ω'} {ρL' : Fin nL → ℝ} {ρR' : Fin nR → ℝ},
      IsGoodEvolution κ xL xR ρL' ρR' P' 𝓖' W₁ VL₁ VR₁ B₁ ζ₁ N' →
      P' (({ω | tauR hnL hnR r ζ₁ VL₁ VR₁ ω < ζ₁ ω} ∩ N'ᶜ) ∩
          restartReach (TR hnL hnR r ζ₁ VL₁ VR₁) T' O Bf W₁ VL₁ VR₁ ζ₁) =
        ∫⁻ ω in {ω | tauR hnL hnR r ζ₁ VL₁ VR₁ ω < ζ₁ ω} ∩ N'ᶜ,
          reachKer κ ρL' ρR' T' O Bf (restartState hnL hnR r ζ₁ W₁ VL₁ VR₁ ω).1
            (restartState hnL hnR r ζ₁ W₁ VL₁ VR₁ ω).2 ∂P' := by
    intro Ω' mΩ' P' 𝓖' W₁ VL₁ VR₁ B₁ ζ₁ N' ρL' ρR' hG
    obtain ⟨hE₁, -, -, hVLc, hVRc, -, -, hVL0, hVR0, hζ0, hNm₁, hN0₁, hNt₁, hNp⟩ := hG
    have hNt := hNt₁ N' hNm₁ hN0₁
    have hT := isStoppingTime_TR hnL hnR (r := r) hE₁.2.2.1 hE₁.2.2.2.1 hVLc hVRc
    refine measure_restart_reach hκ hE₁ hT
      (measurableSet_tauR_lt hnL hnR hE₁.2.2.1 hE₁.2.2.2.1 hVLc hVRc hNt
        (fun ω hω => (hNp ω hω).isForcePath) hr0.le hr4) (fun ω hω => ?_) T' hO hBo hBfc
    have hp := (hNp ω hω.2).isForcePath
    have hτe := coe_TR_eq hnL hnR hp hr0.le hr4
    refine ⟨by rw [hτe]; exact hω.1, Or.inl ?_⟩
    have hpos : 0 < tauR hnL hnR r ζ₁ VL₁ VR₁ ω := by
      refine hitTime_killedFam_pos le_rfl (continuousOn_gapR hnL hnR hp) (hζ0 ω) fun k => ?_
      simp only [gapR, hVL0, hVR0, hL0, hR0, sub_zero]; exact hr0
    rw [← hτe] at hpos
    exact_mod_cast hpos
  -- the kernels
  set K : ℕ → ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) → ℝ≥0∞ := fun m x => reachKer κ (ρL m) (ρR m) T' O Bf x.1 x.2
    with hKdef
  set K₀ : ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) → ℝ≥0∞ := fun x => reachKer κ ρL₀ ρR₀ T' O Bf x.1 x.2 with hK₀def
  have hKm : ∀ m, Measurable (K m) := fun m => measurable_reachKer T' hO
  have hK₀m : Measurable K₀ := measurable_reachKer T' hO
  have hK1 : ∀ m x, K m x ≤ 1 := fun m x => prob_le_one
  have hK₀1 : ∀ x, K₀ x ≤ 1 := fun x => prob_le_one
  -- the entrance laws at level `r`
  obtain ⟨ν, ν₀, hν, hνF, hν₀F, hEB, hEB₀⟩ := hent' r hr0 hr1
  -- the Fatou step
  have hfatou : ∫⁻ x, K₀ x ∂(ν₀ : Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))) ≤
      liminf (fun m => ∫⁻ x, K m x ∂(ν m : Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ))))) atTop := by
    have h := lintegral_le_liminf_of_tendsto hν hνF hν₀F (K := fun m x => (K m x).toReal)
      (K₀ := fun x => (K₀ x).toReal) (fun m => (hKm m).ennreal_toReal) (fun m x => ENNReal.toReal_nonneg)
      hK₀m.ennreal_toReal (fun x => ENNReal.toReal_nonneg) ?_
    · simp only [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hK₀1 _)),
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hK1 _ _))] at h
      exact h
    · intro x hx mk y hmk hyF hy
      simp only [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hK₀1 _)),
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hK1 _ _))]
      obtain ⟨hxw, hxthr⟩ := ds1_of_mem_carrier hnL hnR hε hη hw₀ hx
      exact reachKer_le_liminf hκ hnL hnR hε hr0 hg hO hBo hBR hρL hρR hxw hx.2.1 hxthr hmk
        ((continuous_fst.tendsto _).comp hy) ((continuous_snd.tendsto _).comp hy)
        (fun k => (ds1_of_mem_carrier hnL hnR hε hη (hw (mk k)) (hyF k)).1) (fun k => (hyF k).2.1)
  -- the restarted events are inside the reach events
  have hsub : ∀ m, ({ω | tauR hnL hnR r (ζ' m) (VL' m) (VR' m) ω < ζ' m ω} ∩ (N m)ᶜ) ∩
      restartReach (TR hnL hnR r (ζ' m) (VL' m) (VR' m)) T' O Bf (W' m) (VL' m) (VR' m) (ζ' m) ⊆
        reachEvent T O Bf (W' m) (VL' m) (VR' m) (ζ' m) := fun m ω hω =>
    reachEvent_of_restart hnL hnR ((hNeq m ω hω.1.2).2.2.2.2).isForcePath hL0 hR0 hr0.le hr4 hrT
      (hball r hr2) hω.1.1 hω.2
  -- the chain
  have hEm : ∀ m, ∫⁻ x, K m x ∂(ν m : Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))) ≤
      P m (reachEvent T O Bf (W' m) (VL' m) (VR' m) (ζ' m)) + ENNReal.ofReal ((e : ℝ) / 4) := fun m => by
    refine ((hEB m _ _ _ _ _ _ _ _ _ (hgood m) (K m) (hKm m) (hK1 m)).2).trans (add_le_add ?_ le_rfl)
    rw [← hrestart (hgood m)]
    exact measure_mono (hsub m)
  have hE₀ : P₀ (E r) ≤ ∫⁻ x, K₀ x ∂(ν₀ : Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))) +
      ENNReal.ofReal ((e : ℝ) / 4) := by
    rw [hEdef]
    simp only
    rw [hrestart hgood₀]
    exact (hEB₀ _ _ _ _ _ _ _ _ _ hgood₀ K₀ hK₀m hK₀1).1
  have hlim : liminf (fun m => ∫⁻ x, K m x ∂(ν m : Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ))))) atTop ≤
      liminf (fun m => P m (reachEvent T O Bf (W' m) (VL' m) (VR' m) (ζ' m))) atTop +
        ENNReal.ofReal ((e : ℝ) / 4) := by
    rw [← liminf_add_const atTop _ _ (by isBoundedDefault) (by isBoundedDefault)]
    exact liminf_le_liminf (Eventually.of_forall hEm)
  calc P₀ (reachEvent T O Bf W₀' VL₀' VR₀' ζ₀')
      ≤ P₀ (E r) + ENNReal.ofReal ((e : ℝ) / 4) := hj
    _ ≤ (liminf (fun m => P m (reachEvent T O Bf (W' m) (VL' m) (VR' m) (ζ' m))) atTop +
          ENNReal.ofReal ((e : ℝ) / 4) + ENNReal.ofReal ((e : ℝ) / 4)) + ENNReal.ofReal ((e : ℝ) / 4) :=
        add_le_add (hE₀.trans (add_le_add (hfatou.trans hlim) le_rfl)) le_rfl
    _ ≤ _ := by
        have h3 : ENNReal.ofReal ((e : ℝ) / 4) + (ENNReal.ofReal ((e : ℝ) / 4) + ENNReal.ofReal ((e : ℝ) / 4))
            ≤ (e : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_add he4.le he4.le, ← ENNReal.ofReal_add he4.le (by positivity),
            ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
          linarith
        rw [add_assoc, add_assoc]
        exact add_le_add le_rfl h3

end DS3Reach

end Supp12

end InteractingSLE
