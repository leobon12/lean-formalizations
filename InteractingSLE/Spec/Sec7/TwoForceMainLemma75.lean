/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TwoForceRestart
import InteractingSLE.Spec.Sec2.CriticalLifetime

/-!
# Lemma 7.5: field determination of the finite-force driving evolution from local restarts

Packet PROVE-SEC7-A2 (specification §7.1, Lemma 7.5 and its proof, p. 252).

"Apply Aux. lemma 52 to the integrated driving state, first stopped at `T_* ∧ N`. Its continuous finite
endpoint exists by Aux. lemma 3. The stopped history at `T_* ∧ N` is consequently a function of `h`.
Letting `N → ∞` determines every finite part of the driving evolution."

This file carries out that application for the frozen evolution `IsIntegratedSLEEvolution`.

* `drivingState`, `completedState`: the state `X_t = (W_t, V^L_t, V^R_t)`, completed at a finite lifetime
  `ζ` by its left limit (the frozen evolution leaves the paths at and after `ζ` unconstrained).
* `ae_continuousOn_completedState`: by Aux. lemma 3 (`IsIntegratedSLEEvolution.ae_tendsto_threshold`), the
  completed state is almost surely continuous on `[0, ζ]`, including the finite endpoint.
* `ae_completedState_zero_eq`: its initial value is almost surely a deterministic constant (the initial
  force word, or a fixed value when the seed itself is at the continuation threshold, `ζ = 0`).
* `lem75_stoppedHistory_of_restart`: **Lemma 7.5's conclusion for every capacity horizon `N`**, from the
  local restart property (LG1) of the completed state, which is the content of Aux. lemmas 55 and 53
  ("At every own-filtration stopping time strictly before the continuation threshold, that lemma
  constructs a positive additional stopped driving history determined by the previous history and the
  active field"). That property is the one input taken as a hypothesis (named `hloc`); it is exactly
  the hypothesis (LG1) of Aux. lemma 52 for this process.
* `lem75_lifetime_of_restart`, `lem75_killedState_of_restart`: "letting `N → ∞`": the lifetime `ζ` and the
  whole killed driving state `t ↦ X_t 1_{t < ζ}` are almost surely Borel functions of the field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

section State

variable {Ω : Type*} {nL nR : ℕ}

/-- The integrated driving state `X_t = (W_t, V^L_t, V^R_t)`. -/
def drivingState (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (W t ω, fun i => VL i t ω, fun i => VR i t ω)

/-- The driving state completed at the lifetime: `X_t` before `ζ`, and the left limit at `t` from
`ζ` on (only the value at a finite `ζ` itself matters for the stopped histories through `ζ`). -/
def completedState (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  if (t : ℝ≥0∞) < ζ ω then drivingState W VL VR t ω
  else limUnder (𝓝[<] t) fun s => drivingState W VL VR s ω

/-- Pathwise continuity of the completed state on `[0, ζ]`, from continuity before `ζ` and the existence
of the left limit at a finite positive `ζ`. -/
theorem continuousOn_completedState {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hx : ContinuousOn (fun t => drivingState W VL VR t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω → ∃ L,
      Tendsto (fun t => drivingState W VL VR t ω) (𝓝[<] T) (𝓝 L)) :
    ContinuousOn (fun t => completedState W VL VR ζ t ω)
      {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ (ζ ω : WithTop ℝ≥0)} := by
  intro t ht
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hagree : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω →
      completedState W VL VR ζ s ω = drivingState W VL VR s ω := fun s hs => ite_eq_left hs
  rcases (show (t : ℝ≥0∞) ≤ ζ ω from ht).lt_or_eq with hlt | heq
  · have hev : (fun s => drivingState W VL VR s ω) =ᶠ[𝓝 t] fun s => completedState W VL VR ζ s ω :=
      Filter.mem_of_superset (hopen.mem_nhds hlt) fun s hs => (hagree s hs).symm
    exact ((hx.continuousAt (hopen.mem_nhds hlt)).congr hev).continuousWithinAt
  · -- the endpoint `t = ζ`
    have hset : {s : ℝ≥0 | (s : WithTop ℝ≥0) ≤ (ζ ω : WithTop ℝ≥0)} = insert t (Iio t) := by
      rw [Iio_insert]
      ext s
      simp only [mem_ofPred_eq, mem_Iic]
      change (s : ℝ≥0∞) ≤ ζ ω ↔ s ≤ t
      rw [← heq, ENNReal.coe_le_coe]
    rw [hset]
    refine ContinuousWithinAt.insert ?_
    have hev : (fun s => drivingState W VL VR s ω) =ᶠ[𝓝[<] t]
        fun s => completedState W VL VR ζ s ω := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hagree s (heq ▸ ENNReal.coe_lt_coe.2 hs)).symm
    rcases eq_zero_or_pos t with h0 | hpos
    · subst h0
      have : (𝓝[<] (0 : ℝ≥0)) = ⊥ := by
        rw [show Iio (0 : ℝ≥0) = ∅ by ext s; simp, nhdsWithin_empty]
      simp only [ContinuousWithinAt, this, tendsto_bot]
    · obtain ⟨L, hL⟩ := hlim t hpos heq
      have : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
      have hval : completedState W VL VR ζ t ω = L := by
        rw [completedState, ite_eq_right (by rw [heq]; exact lt_irrefl _)]
        exact hL.limUnder_eq
      rw [ContinuousWithinAt, hval]
      exact hL.congr' hev

end State

section Evolution

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The completed state is continuous on `[0, ζ]`** (Aux. lemma 3 supplies the continuous finite
endpoint). -/
theorem ae_continuousOn_completedState (hκ : 0 < κ)
    (hev : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t => completedState W VL VR ζ t ω)
      {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ (ζ ω : WithTop ℝ≥0)} := by
  filter_upwards [hev.2.2.2.2, hev.ae_tendsto_threshold hκ] with ω hp hT
  refine continuousOn_completedState ?_ fun T hT0 hTζ => ?_
  · exact hp.2.2.2.1.prodMk ((continuousOn_pi.2 hp.2.2.2.2.1).prodMk (continuousOn_pi.2 hp.2.2.2.2.2.1))
  · obtain ⟨w₀, vL₀, vR₀, hL, -⟩ := hT T hT0 hTζ
    exact ⟨_, hL⟩

omit [IsProbabilityMeasure P] in
open Classical in
/-- **The initial completed state is almost surely deterministic**: the initial force word when the
seed is admissible, and a fixed value when the seed is at the continuation threshold (then `ζ = 0`). -/
theorem ae_completedState_zero_eq (hev : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, completedState W VL VR ζ 0 ω =
      if ForceWord.ThresholdCondition ρL ρR 0 xL xR then
        limUnder (𝓝[<] (0 : ℝ≥0)) fun _ : ℝ≥0 => ((0 : ℝ), xL, xR)
      else ((0 : ℝ), xL, xR) := by
  filter_upwards [hev.2.2.2.2] with ω hp
  have h0 : drivingState W VL VR 0 ω = ((0 : ℝ), xL, xR) := by
    simp only [drivingState, hp.1, Prod.mk.injEq, true_and]
    exact ⟨funext hp.2.1, funext hp.2.2.1⟩
  have hbot : (𝓝[<] (0 : ℝ≥0)) = ⊥ := by
    rw [show Iio (0 : ℝ≥0) = ∅ by ext s; simp, nhdsWithin_empty]
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · rw [ite_eq_left hthr]
    have hζ : ¬ ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      intro hlt
      have hnt := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 0 hlt
      have hvL : (fun i => VL i 0 ω) = xL := funext hp.2.1
      have hvR : (fun i => VR i 0 ω) = xR := funext hp.2.2.1
      rw [hp.1, hvL, hvR] at hnt
      exact hnt hthr
    rw [completedState, ite_eq_right hζ, hbot]
    simp only [limUnder, Filter.map_bot]
  · rw [ite_eq_right hthr]
    have hζ : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      rw [ENNReal.coe_zero, pos_iff_ne_zero]
      intro hz
      exact hthr (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hz)
    rw [completedState, ite_eq_left hζ, h0]

/-- The restart property (LG1) of Aux. lemma 52 for the completed driving state and a recorded random
element `H` (the field): every `𝓖`-stopping time `τ ≤ ζ ∧ N` with determined stopped history can be
strictly extended (on `{τ < ζ ∧ N}`) to a stopping time `σ ≤ ζ ∧ N` with determined stopped history. In
§7.1 this is supplied by Aux. lemma 55 applied conditionally after `τ` (Aux. lemma 53). -/
theorem lem75_stoppedHistory_of_restart (hκ : 0 < κ)
    (hev : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {γ : Type*} [MeasurableSpace γ] {H : Ω → γ} (hH : Measurable H) {𝓖 : Filtration ℝ≥0 mΩ}
    (hloc : ∀ (τ : Ω → WithTop ℝ≥0) (N : ℝ≥0), IsStoppingTime 𝓖 τ →
      (∀ ω, τ ω ≤ min (ζ ω : WithTop ℝ≥0) N) →
      IsAEDeterminedBy P H (stoppedHistory (completedState W VL VR ζ) τ) →
      ∃ σ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 σ ∧ (∀ ω, σ ω ≤ min (ζ ω : WithTop ℝ≥0) N) ∧
        (∀ᵐ ω ∂P, τ ω ≤ σ ω ∧ (τ ω < min (ζ ω : WithTop ℝ≥0) N → τ ω < σ ω)) ∧
        IsAEDeterminedBy P H (stoppedHistory (completedState W VL VR ζ) σ))
    (N : ℝ≥0) :
    IsAEDeterminedBy P H
      (stoppedHistory (completedState W VL VR ζ) fun ω => min (ζ ω : WithTop ℝ≥0) N) := by
  classical
  have hX0 : IsAEDeterminedBy P H (completedState W VL VR ζ 0) :=
    (isAEDeterminedBy_const _).congr_ae
      (show completedState W VL VR ζ 0 =ᵐ[P] fun _ => _ from ae_completedState_zero_eq hev).symm
  exact isAEDeterminedBy_stoppedHistory_of_localRestart (T := fun ω => (ζ ω : WithTop ℝ≥0)) hH
    (ae_continuousOn_completedState hκ hev) hX0 hloc N

/-- **Lemma 7.5, the lifetime** ("Letting `N → ∞`"): under the restart property, the lifetime `ζ` is
almost surely a Borel function of the field. -/
theorem lem75_lifetime_of_restart (hκ : 0 < κ)
    (hev : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {γ : Type*} [MeasurableSpace γ] {H : Ω → γ} (hH : Measurable H) {𝓖 : Filtration ℝ≥0 mΩ}
    (hloc : ∀ (τ : Ω → WithTop ℝ≥0) (N : ℝ≥0), IsStoppingTime 𝓖 τ →
      (∀ ω, τ ω ≤ min (ζ ω : WithTop ℝ≥0) N) →
      IsAEDeterminedBy P H (stoppedHistory (completedState W VL VR ζ) τ) →
      ∃ σ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 σ ∧ (∀ ω, σ ω ≤ min (ζ ω : WithTop ℝ≥0) N) ∧
        (∀ᵐ ω ∂P, τ ω ≤ σ ω ∧ (τ ω < min (ζ ω : WithTop ℝ≥0) N → τ ω < σ ω)) ∧
        IsAEDeterminedBy P H (stoppedHistory (completedState W VL VR ζ) σ)) :
    IsAEDeterminedBy P H ζ := by
  have hN : ∀ n : ℕ, IsAEDeterminedBy P H fun ω => min (ζ ω) ((n : ℝ≥0) : ℝ≥0∞) := fun n =>
    (lem75_stoppedHistory_of_restart hκ hev hH hloc (n : ℝ≥0)).comp measurable_fst
  refine IsAEDeterminedBy.of_tendsto hH hN (Eventually.of_forall fun ω => ?_)
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 ⊤) := by
    simp only [ENNReal.coe_natCast]
    exact ENNReal.tendsto_nat_nhds_top
  have h2 := ((continuous_const (y := ζ ω)).min continuous_id).tendsto ⊤ |>.comp h1
  simpa only [Function.comp_def, id, min_top_right] using h2

/-- `stopAt τ q ω = q` when `q ≤ τ ω`. -/
theorem stopAt_eq_of_le {τ : Ω → WithTop ℝ≥0} {q : ℝ≥0} {ω : Ω} (h : (q : WithTop ℝ≥0) ≤ τ ω) :
    stopAt τ q ω = q := by
  unfold stopAt
  cases hτ : τ ω with
  | top => simp
  | coe s =>
    rw [hτ] at h
    simp only [WithTop.untopD_coe]
    exact min_eq_left (WithTop.coe_le_coe.1 h)

/-- **Lemma 7.5, the driving evolution** ("Letting `N → ∞` determines every finite part of the driving
evolution"): under the restart property, the killed driving state path `t ↦ X_t` on `{t < ζ}` (and a
fixed value `c` from `ζ` on) is almost surely a Borel function of the field, as an element of
`ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)` with the product `σ`-algebra. -/
theorem lem75_killedState_of_restart (hκ : 0 < κ)
    (hev : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {γ : Type*} [MeasurableSpace γ] {H : Ω → γ} (hH : Measurable H) {𝓖 : Filtration ℝ≥0 mΩ}
    (hloc : ∀ (τ : Ω → WithTop ℝ≥0) (N : ℝ≥0), IsStoppingTime 𝓖 τ →
      (∀ ω, τ ω ≤ min (ζ ω : WithTop ℝ≥0) N) →
      IsAEDeterminedBy P H (stoppedHistory (completedState W VL VR ζ) τ) →
      ∃ σ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 σ ∧ (∀ ω, σ ω ≤ min (ζ ω : WithTop ℝ≥0) N) ∧
        (∀ᵐ ω ∂P, τ ω ≤ σ ω ∧ (τ ω < min (ζ ω : WithTop ℝ≥0) N → τ ω < σ ω)) ∧
        IsAEDeterminedBy P H (stoppedHistory (completedState W VL VR ζ) σ))
    (c : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :
    IsAEDeterminedBy P H fun ω (t : ℝ≥0) =>
      if (t : ℝ≥0∞) < ζ ω then drivingState W VL VR t ω else c := by
  classical
  have hX0 : IsAEDeterminedBy P H (completedState W VL VR ζ 0) :=
    (isAEDeterminedBy_const _).congr_ae
      (show completedState W VL VR ζ 0 =ᵐ[P] fun _ => _ from ae_completedState_zero_eq hev).symm
  set b : ℕ → Ω → WithTop ℝ≥0 := fun n ω => min (ζ ω : WithTop ℝ≥0) ((n : ℝ≥0) : WithTop ℝ≥0)
  have hpaths : IsAEDeterminedBy P H fun ω (n : ℕ) (t : ℝ≥0) =>
      completedState W VL VR ζ (stopAt (b n) t ω) ω :=
    isAEDeterminedBy_pi fun n =>
      isAEDeterminedBy_stoppedPath_of_localRestart (T := fun ω => (ζ ω : WithTop ℝ≥0)) hH
        (ae_continuousOn_completedState hκ hev) hX0 hloc (n : ℝ≥0)
  have hjoint := (lem75_lifetime_of_restart hκ hev hH hloc).prodMk hpaths
  set G : ℝ≥0∞ × (ℕ → ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) →
      ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
    fun p t => if (t : ℝ≥0∞) < p.1 then p.2 (⌈t⌉₊ + 1) t else c
  have hG : Measurable G := by
    refine measurable_pi_iff.2 fun t => Measurable.ite (measurableSet_lt measurable_const
      measurable_fst) ((measurable_pi_apply t).comp ((measurable_pi_apply (⌈t⌉₊ + 1)).comp
        measurable_snd)) measurable_const
  refine (hjoint.comp hG).congr_ae (Eventually.of_forall fun ω => ?_)
  funext t
  simp only [G]
  split_ifs with ht
  · have hlt : (t : WithTop ℝ≥0) ≤ b (⌈t⌉₊ + 1) ω := by
      refine le_min ht.le ?_
      have : t ≤ ((⌈t⌉₊ + 1 : ℕ) : ℝ≥0) := by
        push_cast
        exact (Nat.le_ceil t).trans (le_add_of_nonneg_right zero_le_one)
      exact WithTop.coe_le_coe.2 this
    rw [stopAt_eq_of_le hlt, completedState, ite_eq_left ht]
  · rfl

end Evolution

end Sec7

end InteractingSLE
