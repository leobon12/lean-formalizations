/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketMartLifeAe

/-!
# Aux. lemma 125 before the lifetime when the phase is already zero: no upper seed-weight bound

Packet PROVE-R7POCKET. Supplement §5.6–5.7, Lemma R.6 and Theorem R.7 (`source/spec/p433-480.md` L1024–L1068,
pp. 475–478), with Aux. lemmas 122 and 125 (`source/spec/p385-432.md` L104–L131, L197–L250, pp. 389–398).

PROVE-STRIPSYS14's chain (`PocketMartLife.martingale_martProc_stop`, `ae_isWordEntrance_stop`,
`ae_capLife_eq_top_of_hasPhaseMeans`) takes Aux. lemma 122's hypotheses with an arbitrary lattice phase `d_t ∈ 2πχℤ`
and first selects `d = 0` (`PhaseSelAdapt.aux122_adapt`); only that selection uses the upper seed-weight bounds
`r_L, r_R < 2A − 2 = k − 6` (proof of Aux. lemma 122, (PS9.3)). When the exposed-side heights are already the canonical
ones (`d = 0`: the zero phase is part of the boundary description, as Lemma R.6 provides it for Theorem R.7's pockets:
"Lemma R.6 selects the zero phase for arbitrarily large weights", p. 477), the selection is void and the rest of the
chain — Theorem 2.4's converse before the lifetime and Aux. lemma 125's infinite lifetime — holds for all seed weights
`> −2`. This file proves the zero-phase versions:

* `exists_aux122_stop_zeroPhase`: the time-zero event of `exists_aux122_stop` is `univ`, with no seed-weight bound;
* **`martingale_martProc_stop_zeroPhase`**, **`ae_isWordEntrance_stop_zeroPhase`**;
* **`ae_isWordEntrance_of_hasPhaseMeans_zeroPhase`**, **`ae_isForcePathPre_of_hasPhaseMeans_zeroPhase`**,
  **`ae_capLife_eq_top_of_hasPhaseMeans_zeroPhase`**.

The proofs after the selection are PROVE-STRIPSYS14's, unchanged.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketMartLife

open MartChar PocketTraversal PhaseSel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}

section Hyps

variable {k : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}
  {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {σ : Ω → ℝ≥0}

/-- **Aux. lemma 122 for the coordinates restarted at `σ < T`, the phase already zero** (`exists_aux122_stop` with
`d = 0`): the time-zero event is `univ`, and the canonical coupling means of the restarted coordinates are local
martingales before `min (swallowTime z) σ`. No seed-weight bound is needed: with `d = 0` the canonical extension is an
extension of the given boundary data. -/
theorem exists_aux122_stop_zeroPhase [IsProbabilityMeasure P] (hk : 0 < k)
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 W xL xR (fun _ _ => 0) T)
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) :
    ∃ A : Set Ω, MeasurableSet[𝓕 0] A ∧ (∀ᵐ ω ∂P, 0 < σ ω → ω ∈ A) ∧
      (P A ≠ 0 → ∀ z ∈ H, IsLocalMartingaleBefore (subFilt 𝓕 A) (condSub P A)
        (fun ω : A => min (QuantumZipper.swallowTime (wpath (fun t (ω : A) => stopW W σ t ω) ω) z :
          WithTop ℝ≥0) (σ ω))
        (coupProc k ρL ρR (fun t (ω : A) => stopW W σ t ω) (fun i t (ω : A) => geomLW (stopW W σ) xL i t ω)
          (fun j t (ω : A) => geomRW (stopW W σ) xR j t ω) z)) := by
  have hWc' : ∀ ω, Continuous (stopW W σ · ω) := continuous_stopW hWc hσT
  refine ⟨univ, @MeasurableSet.univ _ (𝓕 0), Eventually.of_forall fun _ _ => mem_univ _, fun h0 z hz => ?_⟩
  set U : Ω → ℝ≥0 → ℂ → ℝ := fun ω t => meanExt k ρL ρR (stopW W σ t ω) (fun i => geomLW (stopW W σ) xL i t ω)
    (fun j => geomRW (stopW W σ) xR j t ω) with hUdef
  have hU : ∀ ω t, IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => geomLW (stopW W σ) xL i t ω - stopW W σ t ω)
        (fun j => geomRW (stopW W σ) xR j t ω - stopW W σ t ω) (stopD (fun _ _ => 0) σ t ω))
      (forceJumpSet (fun i => geomLW (stopW W σ) xL i t ω - stopW W σ t ω)
        (fun j => geomRW (stopW W σ) xR j t ω - stopW W σ t ω)) (U ω t) := by
    intro ω t
    have h := isBoundedHarmonicExtension_unshift (c := 0) hk (sub_nonpos.2 (geomLW_le hWc' xL ω t 0))
      (sub_nonneg.2 (le_geomRW hWc' xR ω t 0)) (isBoundedHarmonicExtension_meanExt k (shiftL k ρL 0)
        (shiftR k ρR 0) (stopW W σ t ω) (fun i => geomLW (stopW W σ) xL i t ω)
        (fun j => geomRW (stopW W σ) xR j t ω))
    simp only [shiftL_zero_eq, shiftR_zero_eq, add_zero] at h
    have e : stopD (fun _ _ => (0 : ℝ)) σ t ω = 0 := by
      simp only [stopD]
      split_ifs <;> rfl
    rw [e]
    exact h
  exact isLocalMartingaleBefore_sub (@MeasurableSet.univ _ (𝓕 0)) h0
    ((hasPhaseMeans_stop hk hWc hM hσ hσT U hU).1 z hz)

end Hyps

section Mart

open PhaseSelFull

variable {k : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}
  {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {σ : Ω → ℝ≥0}

/-- **The driver's martingale part stopped at `σ < T`, and its square compensated by `k t`, are martingales, the phase
already zero**
(Theorem 2.4's converse before the lifetime, specification p. 397: "Stop before a fixed coordinate bound or at `ζ`,
whichever occurs first"), when the coordinates are bounded by `N` up to `σ ≤ N`. -/
theorem martingale_martProc_stop_zeroPhase [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    {Wk : ℝ≥0 → Ω → ℝ} (hWka : StronglyAdapted 𝓕 Wk) (hWk : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → Wk t ω = W t ω)
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 W xL xR (fun _ _ => 0) T)
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω)
    {N : ℕ} (hσN : ∀ ω, σ ω ≤ N)
    (hbd : ∀ ω, 0 < σ ω → ∀ t ≤ σ ω, absSum W (jointV (geomLW W xL) (geomRW W xR)) t ω ≤ N) :
    Martingale (fun t ω => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) (min t (σ ω)) ω) 𝓕 P ∧
      Martingale (fun t ω => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) (min t (σ ω)) ω ^ 2
        - k * ((min t (σ ω) : ℝ≥0) : ℝ)) 𝓕 P := by
  have hk0 : 0 < k := by linarith
  obtain ⟨A, hA0, hAae, hloc⟩ := exists_aux122_stop_zeroPhase (P := P) hk0 hWc hM hσ hσT
  have hA : MeasurableSet A := 𝓕.le 0 _ hA0
  set W' := stopW W σ with hW'def
  set VL' := geomLW W' xL with hVL'def
  set VR' := geomRW W' xR with hVR'def
  set ρ := jointρ ρL ρR with hρ
  set V' := jointV VL' VR' with hV'def
  have hWc' : ∀ ω, Continuous (W' · ω) := continuous_stopW hWc hσT
  have hW0' : ∀ ω, W' 0 ω = 0 := fun ω => (stopW_of_le zero_le).trans (hW0 ω)
  have hWa' : StronglyAdapted 𝓕 W' := stronglyAdapted_stopW hWka hWk hWc hσ hσT
  have hVLa' : ∀ i, StronglyAdapted 𝓕 (VL' i) := stronglyAdapted_geomLW hWa' hWc' hxLm
  have hVRa' : ∀ j, StronglyAdapted 𝓕 (VR' j) := stronglyAdapted_geomRW hWa' hWc' hxRm
  have hVc' : ∀ j ω, Continuous fun t => V' j t ω := fun j ω => by
    cases j with
    | inl i => exact (isForcePath_geomLW hWc' xL ω i).1
    | inr j => exact (isForcePath_geomRW hWc' xR ω j).1
  have hVa' : ∀ j, StronglyAdapted 𝓕 (V' j) := fun j => by
    cases j with
    | inl i => exact hVLa' i
    | inr j => exact hVRa' j
  -- the bound of the restarted coordinates up to `σ`
  have hbd' : ∀ ω, 0 < σ ω → ∀ t ≤ σ ω, absSum W' V' t ω ≤ N := fun ω h0 t ht => by
    have e : absSum W' V' t ω = absSum W (jointV (geomLW W xL) (geomRW W xR)) t ω := by
      simp only [absSum, hW'def, stopW_of_le ht]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      cases j with
      | inl i =>
        show |geomLW (stopW W σ) xL i t ω| = |geomLW W xL i t ω|
        rw [geomLW_stopW hWc hσT ht i]
      | inr j =>
        show |geomRW (stopW W σ) xR j t ω| = |geomRW W xR j t ω|
        rw [geomRW_stopW hWc hσT ht j]
    rw [e]; exact hbd ω h0 t ht
  have hll : ∀ ω, lifeLocN W' V' (fun ω => (σ ω : WithTop ℝ≥0)) (N + 1) ω = σ ω := fun ω => by
    have h := lifeLoc_eq_of_le hWc' hVc' hσN hbd' ω
    rw [← coe_lifeLocN] at h
    exact WithTop.coe_le_coe.1 h.le |>.antisymm (WithTop.coe_le_coe.1 h.ge)
  -- the two processes, in the restarted coordinates
  set Y : ℝ≥0 → Ω → ℝ := fun t ω => martProc ρ W' V' (min t (σ ω)) ω with hYdef
  set Y2 : ℝ≥0 → Ω → ℝ := fun t ω => Y t ω ^ 2 - k * ((min t (σ ω) : ℝ≥0) : ℝ) with hY2def
  have e1 : (fun t ω => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) (min t (σ ω)) ω) = Y :=
    funext fun t => funext fun ω => martProc_stopW hWc hσT (min_le_right _ _)
  have e2 : (fun t ω => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) (min t (σ ω)) ω ^ 2
      - k * ((min t (σ ω) : ℝ≥0) : ℝ)) = Y2 := by
    funext t ω
    exact congrArg (fun x => x ^ 2 - k * ((min t (σ ω) : ℝ≥0) : ℝ)) (martProc_stopW hWc hσT (min_le_right t (σ ω)))
  rw [e1, e2]
  have hMa : StronglyAdapted 𝓕 (martProc ρ W' V') := stronglyAdapted_martProc hWa' hVa'
  have hMc : ∀ ω, Continuous fun t => martProc ρ W' V' t ω := continuous_martProc hWc' hVc'
  have hYa : StronglyAdapted 𝓕 Y := fun t =>
    (PhaseSelAdapt.measurable_stopped_value hσ hMa (fun ω => (hMc ω).continuousOn) t).stronglyMeasurable
  have hmin := PhaseSelAdapt.measurable_min_coe hσ
  have hY2a : StronglyAdapted 𝓕 Y2 := fun t =>
    (((hYa t).measurable.pow_const 2).sub (measurable_const.mul (hmin t))).stronglyMeasurable
  have hYb : ∀ t ω, |Y t ω| ≤ 2 * (N + 1 : ℕ) + (∑ j, |ρ j|) * (N + 1 : ℕ) := fun t ω => by
    have h := abs_martProc_lifeLocN_le (ρ := ρ) (T := fun ω => (σ ω : WithTop ℝ≥0)) hWc' hVc' (N + 1) t ω
    rwa [hll ω] at h
  have hYi : ∀ t, Integrable (Y t) P := fun t =>
    Integrable.of_bound ((hYa t).mono (𝓕.le t)).aestronglyMeasurable _ (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hYb t ω)
  have hσb : ∀ t ω, |((min t (σ ω) : ℝ≥0) : ℝ)| ≤ N := fun t ω => by
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast (min_le_right _ _).trans (hσN ω)
  have hY2i : ∀ t, Integrable (Y2 t) P := fun t => by
    refine Integrable.of_bound ((hY2a t).mono (𝓕.le t)).aestronglyMeasurable
      ((2 * (N + 1 : ℕ) + (∑ j, |ρ j|) * (N + 1 : ℕ)) ^ 2 + |k| * N) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hYb t ω) 2
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hσb t ω) (abs_nonneg _)
  -- off `A`, almost surely `σ = 0`
  have hY0 : ∀ ω, σ ω = 0 → ∀ t, Y t ω = 0 := fun ω h0 t => by
    simp only [hYdef, h0, min_eq_right (zero_le : (0 : ℝ≥0) ≤ t), martProc, martValue, sub_self, mul_zero,
      Finset.sum_const_zero, add_zero]
  have hY20 : ∀ ω, σ ω = 0 → ∀ t, Y2 t ω = 0 := fun ω h0 t => by
    simp only [hY2def, hY0 ω h0 t, h0, min_eq_right (zero_le : (0 : ℝ≥0) ≤ t), NNReal.coe_zero, mul_zero,
      sub_zero]; norm_num
  have hoff : ∀ᵐ ω ∂P, ω ∉ A → σ ω = 0 := by
    filter_upwards [hAae] with ω hω hωA
    by_contra h
    exact hωA (hω (pos_iff_ne_zero.2 h))
  by_cases h0 : P A = 0
  · have hnA : ∀ᵐ ω ∂P, ω ∉ A := measure_eq_zero_iff_ae_notMem.1 h0
    have hz : ∀ᵐ ω ∂P, σ ω = 0 := by filter_upwards [hnA, hoff] with ω h1 h2 using h2 h1
    have hz1 : ∀ t, Y t =ᵐ[P] (0 : ℝ≥0 → Ω → ℝ) t := fun t => by
      filter_upwards [hz] with ω hω using hY0 ω hω t
    have hz2 : ∀ t, Y2 t =ᵐ[P] (0 : ℝ≥0 → Ω → ℝ) t := fun t => by
      filter_upwards [hz] with ω hω using hY20 ω hω t
    have h00 : Martingale (0 : ℝ≥0 → Ω → ℝ) 𝓕 P := martingale_zero _ _ _
    exact ⟨⟨hYa, fun i j hij => (condExp_congr_ae (hz1 j)).trans ((h00.2 i j hij).trans (hz1 i).symm)⟩,
      ⟨hY2a, fun i j hij => (condExp_congr_ae (hz2 j)).trans ((h00.2 i j hij).trans (hz2 i).symm)⟩⟩
  have hQ : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hA h0
  have hMM := martingale_martProc_lifeLoc (P := condSub P A) (𝓕 := subFilt 𝓕 A) (ρL := ρL) (ρR := ρR)
    (W := fun t (ω : A) => W' t ω) (VL := fun i t (ω : A) => VL' i t ω) (VR := fun j t (ω : A) => VR' j t ω)
    hk0 (fun ω => hW0' ω) (fun ω => hWc' ω) (stronglyAdapted_sub hWa') (fun i => stronglyAdapted_sub (hVLa' i))
    (fun j => stronglyAdapted_sub (hVRa' j)) (fun ω t i => geomLW_le hWc' xL ω t i)
    (fun ω t j => le_geomRW hWc' xR ω t j) (fun ω i => isForcePath_geomLW hWc' xL ω i)
    (fun ω j => isForcePath_geomRW hWc' xR ω j) (isStoppingTime_sub hσ) (hloc h0) (N + 1)
  have hjV : (jointV (fun i t (ω : A) => VL' i t ω) (fun j t (ω : A) => VR' j t ω)) =
      fun j t (ω : A) => V' j t ω := funext fun j => by cases j <;> rfl
  rw [hjV] at hMM
  have hllA : ∀ ω : A, lifeLocN (fun t (ω : A) => W' t ω) (fun j t (ω : A) => V' j t ω)
      (fun ω : A => (σ ω : WithTop ℝ≥0)) (N + 1) ω = σ ω := fun ω => by
    have h := lifeLoc_eq_of_le (W := fun t (ω : A) => W' t ω) (V := fun j t (ω : A) => V' j t ω)
      (σ := fun ω : A => σ ω) (fun ω => hWc' ω) (fun j ω => hVc' j ω) (fun ω => hσN ω)
      (fun ω h0 t ht => hbd' ω h0 t ht) ω
    rw [← coe_lifeLocN] at h
    exact WithTop.coe_le_coe.1 h.le |>.antisymm (WithTop.coe_le_coe.1 h.ge)
  have hs1 : stoppedProcess (martProc ρ (fun t (ω : A) => W' t ω) fun j t (ω : A) => V' j t ω)
      (lifeLoc (fun t (ω : A) => W' t ω) (fun j t (ω : A) => V' j t ω) (fun ω : A => (σ ω : WithTop ℝ≥0)) (N + 1)) =
      fun t (ω : A) => Y t ω := by
    funext t ω
    rw [stoppedProcess_lifeLoc, hllA ω]
    rfl
  have hs2 : stoppedProcess (fun t (ω : A) => martProc ρ (fun t (ω : A) => W' t ω)
      (fun j t (ω : A) => V' j t ω) t ω ^ 2 - k * t)
      (lifeLoc (fun t (ω : A) => W' t ω) (fun j t (ω : A) => V' j t ω) (fun ω : A => (σ ω : WithTop ℝ≥0)) (N + 1)) =
      fun t (ω : A) => Y2 t ω := by
    funext t ω
    rw [stoppedProcess_lifeLoc, hllA ω]
    rfl
  rw [hs1, hs2] at hMM
  refine ⟨martingale_of_martingale_sub hA0 h0 hYa hYi ?_ hMM.1, martingale_of_martingale_sub hA0 h0 hY2a hY2i ?_
    hMM.2⟩
  · filter_upwards [hoff] with ω hω hωA t
    rw [hY0 ω (hω hωA) t, hY0 ω (hω hωA) 0]
  · filter_upwards [hoff] with ω hω hωA t
    rw [hY20 ω (hω hωA) t, hY20 ω (hω hωA) 0]

/-- **Definition 2.1's equations hold before `σ < T`, almost surely, with the noise `M/√k`** (Aux. lemma 122's
conclusion before the lifetime: "the coordinates satisfy this SDE"; specification p. 397: "All side partial sums are
greater than `−2`, so the integrated driving construction has no continuation threshold"): Aux. lemma 117 before the
stopping lifetime `σ` (`PhaseSelFull.exists_isWordEntrance_before`) for the restarted coordinates, under the
conditional law given the time-zero event of `exists_aux122_stop_zeroPhase` (no seed-weight bound). -/
theorem ae_isWordEntrance_stop_zeroPhase [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    {Wk : ℝ≥0 → Ω → ℝ} (hWka : StronglyAdapted 𝓕 Wk) (hWk : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → Wk t ω = W t ω)
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 W xL xR (fun _ _ => 0) T)
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) :
    ∀ᵐ ω ∂P, Aux117.IsWordEntrance k (xL ω) (xR ω) ρL ρR (W · ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω)
      (fun t => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) t ω / Real.sqrt k) (σ ω) := by
  have hk0 : 0 < k := by linarith
  obtain ⟨A, hA0, hAae, hloc⟩ := exists_aux122_stop_zeroPhase (P := P) hk0 hWc hM hσ hσT
  have hA : MeasurableSet A := 𝓕.le 0 _ hA0
  set W' := stopW W σ with hW'def
  have hWc' : ∀ ω, Continuous (W' · ω) := continuous_stopW hWc hσT
  have hW0' : ∀ ω, W' 0 ω = 0 := fun ω => (stopW_of_le zero_le).trans (hW0 ω)
  have hWa' : StronglyAdapted 𝓕 W' := stronglyAdapted_stopW hWka hWk hWc hσ hσT
  have hxL0 : ∀ ω i, xL ω i ≤ 0 := fun ω i => (hxLi ω (Fin.zero_le i)).trans_eq (hseedL ω)
  have hxR0 : ∀ ω j, 0 ≤ xR ω j := fun ω j => (hseedR ω).symm.trans_le (hxRi ω (Fin.zero_le j))
  have hlt : ∀ ω (t : ℝ≥0), t ≤ σ ω → (t : WithTop ℝ≥0) < T ω := fun ω t ht =>
    lt_of_le_of_lt (WithTop.coe_le_coe.2 ht) (hσT ω)
  -- the initial values of the original coordinates
  have hL0 : ∀ ω i, geomLW W xL i 0 ω = xL ω i := fun ω i => by
    rw [← geomLW_stopW hWc hσT zero_le i, geomLW_zero hWc' hW0' (hxL0 ω i)]
  have hR0 : ∀ ω j, geomRW W xR j 0 ω = xR ω j := fun ω j => by
    rw [← geomRW_stopW hWc hσT zero_le j, geomRW_zero hWc' hW0' (hxR0 ω j)]
  -- the conclusion at `σ = 0`
  have hzero : ∀ ω, σ ω = 0 → Aux117.IsWordEntrance k (xL ω) (xR ω) ρL ρR (W · ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω)
      (fun t => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) t ω / Real.sqrt k) (σ ω) :=
    fun ω h0 => by
      rw [h0, ENNReal.coe_zero]
      exact isWordEntrance_zero (hW0 ω) (hL0 ω) (hR0 ω)
  -- the conclusion from that of the restarted coordinates
  have hconv : ∀ ω, Aux117.IsWordEntrance k (fun i => geomLW W' xL i 0 ω) (fun j => geomRW W' xR j 0 ω) ρL ρR
      (W' · ω) (fun i t => geomLW W' xL i t ω) (fun j t => geomRW W' xR j t ω)
      (fun t => martProc (jointρ ρL ρR) W' (jointV (geomLW W' xL) (geomRW W' xR)) t ω / Real.sqrt k) (σ ω) →
      Aux117.IsWordEntrance k (xL ω) (xR ω) ρL ρR (W · ω) (fun i t => geomLW W xL i t ω)
        (fun j t => geomRW W xR j t ω)
        (fun t => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) t ω / Real.sqrt k) (σ ω) := by
    intro ω h
    have e1 : (fun i => geomLW W' xL i 0 ω) = xL ω := funext fun i => by
      rw [geomLW_stopW hWc hσT zero_le i, hL0 ω i]
    have e2 : (fun j => geomRW W' xR j 0 ω) = xR ω := funext fun j => by
      rw [geomRW_stopW hWc hσT zero_le j, hR0 ω j]
    rw [e1, e2] at h
    refine isWordEntrance_congr_le h (fun t ht => (stopW_of_le (ENNReal.coe_le_coe.1 ht)).symm)
      (fun t ht i => (geomLW_stopW hWc hσT (ENNReal.coe_le_coe.1 ht) i).symm)
      (fun t ht j => (geomRW_stopW hWc hσT (ENNReal.coe_le_coe.1 ht) j).symm) (fun t ht => ?_)
    rw [martProc_stopW hWc hσT (ENNReal.coe_le_coe.1 ht.le)]
  have hoff : ∀ᵐ ω ∂P, ω ∉ A → σ ω = 0 := by
    filter_upwards [hAae] with ω hω hωA
    by_contra h
    exact hωA (hω (pos_iff_ne_zero.2 h))
  by_cases h0 : P A = 0
  · have hnA : ∀ᵐ ω ∂P, ω ∉ A := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [hnA, hoff] with ω h1 h2 using hzero ω (h2 h1)
  have hQ : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hA h0
  have hVLa' := stronglyAdapted_geomLW hWa' hWc' hxLm
  have hVRa' := stronglyAdapted_geomRW hWa' hWc' hxRm
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, B, -, -, hBeq, hae⟩ := PhaseSelFull.exists_isWordEntrance_before
    (P := condSub P A) (𝓕 := subFilt 𝓕 A) (ρL := ρL) (ρR := ρR)
    (W := fun t (ω : A) => W' t ω) (VL := fun i t (ω : A) => geomLW W' xL i t ω)
    (VR := fun j t (ω : A) => geomRW W' xR j t ω) hk0 (fun ω => hW0' ω) (fun ω => hWc' ω)
    (stronglyAdapted_sub hWa') (fun i => stronglyAdapted_sub (hVLa' i)) (fun j => stronglyAdapted_sub (hVRa' j))
    (fun ω t i => geomLW_le hWc' xL ω t i) (fun ω t j => le_geomRW hWc' xR ω t j)
    (fun ω i => isForcePath_geomLW hWc' xL ω i) (fun ω j => isForcePath_geomRW hWc' xR ω j)
    (fun ω i => antitone_geomLW hWc' xL ω i) (fun ω j => monotone_geomRW hWc' xR ω j)
    (fun ω t => antitone_index_geomLW hWc' (hxLi ω) t) (fun ω t => monotone_index_geomRW hWc' (hxRi ω) t)
    (fun ω i j s t hst => geomLW_merge hWc' xL ω i j s t hst) (fun ω i j s t hst => geomRW_merge hWc' xR ω i j s t hst)
    (fun ω t ht i j => geom_sep hWc' xL xR ω t ht i j) (isStoppingTime_sub hσ) (hloc h0)
  have hjV : (jointV (fun i t (ω : A) => geomLW W' xL i t ω) (fun j t (ω : A) => geomRW W' xR j t ω)) =
      fun j t (ω : A) => jointV (geomLW W' xL) (geomRW W' xR) j t ω := funext fun j => by cases j <;> rfl
  set R : Ω → Prop := fun ω => Aux117.IsWordEntrance k (fun i => geomLW W' xL i 0 ω)
      (fun j => geomRW W' xR j 0 ω) ρL ρR (W' · ω) (fun i t => geomLW W' xL i t ω)
      (fun j t => geomRW W' xR j t ω)
      (fun t => martProc (jointρ ρL ρR) W' (jointV (geomLW W' xL) (geomRW W' xR)) t ω / Real.sqrt k)
      (σ ω) with hRdef
  have h1 : ∀ᵐ p ∂((condSub P A).prod P₀), R (p.1 : Ω) := by
    filter_upwards [hae] with p hp
    have hcol : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < (σ (p.1 : Ω) : ℝ≥0∞) →
        Aux117.ColliderNe ρL (fun t => W' t (p.1 : Ω)) (fun i t => geomLW W' xL i t (p.1 : Ω)) u ∧
          Aux117.ColliderNe ρR (fun t => W' t (p.1 : Ω)) (fun j t => geomRW W' xR j t (p.1 : Ω)) u :=
      fun u _ _ => Aux117.colliderNe_of_not_thresholdCondition (not_thresholdCondition_of_partialSums
        (antitone_index_geomLW hWc' (hxLi _) u) (fun i => geomLW_le hWc' xL _ u i)
        (monotone_index_geomRW hWc' (hxRi _) u) (fun j => le_geomRW hWc' xR _ u j) hsL hsR)
    have hE := hp (σ (p.1 : Ω) : ℝ≥0∞) le_rfl hcol
    refine PhaseSelFull.IsWordEntrance.congr_b hE fun t ht => ?_
    rw [hBeq p t (WithTop.coe_le_coe.2 (ENNReal.coe_le_coe.1 ht.le)), hjV]
    rfl
  have h2 := ae_of_ae_condSub (p := R) hA (ae_of_ae_prod_fst (p := fun ω : A => R ω) h1)
  filter_upwards [h2, hoff] with ω h3 h4
  by_cases hωA : ω ∈ A
  · exact hconv ω (h3 hωA)
  · exact hzero ω (h4 hωA)


end Mart
section Main

open Lemma71C

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {k : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {γ : Ω → ℝ → ℂ}
  {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {d : ℝ≥0 → Ω → ℝ}

/-- **Aux. lemma 122's conclusion before the lifetime: Definition 2.1's equations hold before `capLife`, almost
surely**, with the noise `M/√k` (specification pp. 389–391 and p. 397). Hypotheses: a random driven curve with points
of `ℍ` of arbitrarily large modulus and filled prefixes adapted to a right-continuous filtration; random
`𝓕₀`-measurable marks (seeds `0`, the other left marks negative, the other right marks positive, ordered in the
index); side partial sums of the weights `> −2` and no bound on the seed weights; the phase `0`
and Aux. lemma 122's hypotheses before the lifetime (`HasPhaseMeansBefore`). -/
theorem ae_isWordEntrance_of_hasPhaseMeans_zeroPhase [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hpre : IsPrefixAdapted 𝓕 γ) (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 (fun t ω => segDriver (γ ω) t) xL xR (fun _ _ => 0)
      (fun ω => capLife (γ ω))) :
    ∀ᵐ ω ∂P, Aux117.IsWordEntrance k (xL ω) (xR ω) ρL ρR (segDriver (γ ω))
      (fun i t => geomLW (fun t ω => segDriver (γ ω) t) xL i t ω)
      (fun j t => geomRW (fun t ω => segDriver (γ ω) t) xR j t ω)
      (fun t => martProc (jointρ ρL ρR) (fun t ω => segDriver (γ ω) t)
        (jointV (geomLW (fun t ω => segDriver (γ ω) t) xL) (geomRW (fun t ω => segDriver (γ ω) t) xR)) t ω /
          Real.sqrt k) (capLife (γ ω)) := by
  have hWc : ∀ ω, ContinuousOn ((fun t ω => segDriver (γ ω) t) · ω)
      {t | (t : WithTop ℝ≥0) < capLife (γ ω)} := fun ω => (hγ ω).segDriver_spec.2.1
  have hW0 : ∀ ω, segDriver (γ ω) 0 = 0 := fun ω => (hγ ω).segDriver_spec.1
  obtain ⟨τ, hτ, hτT, -, hτex, -, -⟩ := exists_announcing_coords hγ hunb hpre hxLm hxRm
  have h := fun m => ae_isWordEntrance_stop_zeroPhase (P := P) (σ := τ m) hk hsL hsR hW0 hWc
    (stronglyAdapted_killAt_segDriver hγ hpre) (fun ω t ht => killAt_segDriver_of_lt ht) hxLm hxRm hseedL hseedR
    hxLi hxRi hM (hτ m) (hτT m)
  filter_upwards [ae_all_iff.2 h] with ω hω
  refine isWordEntrance_of_forall (Tm := fun m => (τ m ω : ℝ≥0∞)) hω fun t ht => ?_
  obtain ⟨t', htt', ht'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  obtain ⟨m, hm⟩ := hτex ω t' ht'T
  exact ⟨m, htt'.trans_le (ENNReal.coe_le_coe.2 hm)⟩

/-- **The path conditions of Definition 2.1 before the lifetime hold almost surely** (`Aux125.IsForcePathPre`; the
threshold condition fails because all side partial sums exceed `−2`, specification p. 397). -/
theorem ae_isForcePathPre_of_hasPhaseMeans_zeroPhase [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hpre : IsPrefixAdapted 𝓕 γ) (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 (fun t ω => segDriver (γ ω) t) xL xR (fun _ _ => 0)
      (fun ω => capLife (γ ω))) :
    ∀ᵐ ω ∂P, Aux125.IsForcePathPre (xL ω) (xR ω) ρL ρR (segDriver (γ ω))
      (fun i t => geomLW (fun t ω => segDriver (γ ω) t) xL i t ω)
      (fun j t => geomRW (fun t ω => segDriver (γ ω) t) xR j t ω) (capLife (γ ω)) := by
  filter_upwards [ae_isWordEntrance_of_hasPhaseMeans_zeroPhase hk hsL hsR hγ hunb hpre hxLm hxRm hseedL hseedR
    hxLi hxRi hM] with ω hE
  exact isForcePathPre_of_isWordEntrance hE fun t ht => not_thresholdCondition_of_partialSums
    (hE.antitone_vL t ht) (hE.vL_le_w t ht) (hE.monotone_vR t ht) (hE.w_le_vR t ht) hsL hsR

/-- **Aux. lemma 125: the relative lifetime is infinite almost surely** (specification p. 397, "Thus `ζ = ∞`"), from
Aux. lemma 122's hypotheses before the lifetime alone: the martingale part of the driver stopped at the announcing
times `τₘ` of the coordinates is a bounded martingale with compensated square a martingale
(`martingale_martProc_stop_zeroPhase`), and the path conditions hold almost surely
(`ae_isForcePathPre_of_hasPhaseMeans_zeroPhase`). -/
theorem ae_capLife_eq_top_of_hasPhaseMeans_zeroPhase [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hpre : IsPrefixAdapted 𝓕 γ) (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 (fun t ω => segDriver (γ ω) t) xL xR (fun _ _ => 0)
      (fun ω => capLife (γ ω))) :
    ∀ᵐ ω ∂P, capLife (γ ω) = ⊤ := by
  have hk0 : 0 < k := by linarith
  set W : ℝ≥0 → Ω → ℝ := fun t ω => segDriver (γ ω) t with hWdef
  have hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < capLife (γ ω)} := fun ω =>
    (hγ ω).segDriver_spec.2.1
  have hW0 : ∀ ω, W 0 ω = 0 := fun ω => (hγ ω).segDriver_spec.1
  obtain ⟨τ, hτ, hτT, hτm, hτex, hτN, hτb⟩ := exists_announcing_coords hγ hunb hpre hxLm hxRm
  set ρ := jointρ ρL ρR with hρdef
  set V := jointV (geomLW W xL) (geomRW W xR) with hVdef
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hmart := fun m => martingale_martProc_stop_zeroPhase (P := P) (σ := τ m) (N := m) hk hW0 hWc
    (stronglyAdapted_killAt_segDriver hγ hpre) (fun ω t ht => killAt_segDriver_of_lt ht) hxLm hxRm hM (hτ m)
    (hτT m) (hτN m) (hτb m)
  refine ae_capLife_eq_top_of_martProc_ae (a := k) (VL := geomLW W xL) (VR := geomRW W xR) hγ hunb hk0
    (ae_isForcePathPre_of_hasPhaseMeans_zeroPhase hk hsL hsR hγ hunb hpre hxLm hxRm hseedL hseedR hxLi
      hxRi hM) (sum_ne_neg_two_of_partialSums hsL) (sum_ne_neg_two_of_partialSums hsR) (σ := τ) hτ
    (fun m ω => hτT m ω) hτm (fun ω t ht => hτex ω t ht)
    (fun ω => (continuousOn_martProc_of_lt hWc ρ xL xR ω).div_const _) (fun m => ?_) (fun m => ?_) (fun m => ?_)
  · refine ⟨(2 * m + (∑ j, |ρ j|) * m) / Real.sqrt k, fun ω t ht => ?_⟩
    have hC : 0 ≤ 2 * (m : ℝ) + (∑ j, |ρ j|) * m := by positivity
    rw [abs_div, abs_of_pos hsk]
    refine div_le_div_of_nonneg_right ?_ hsk.le
    rcases (zero_le : (0 : ℝ≥0) ≤ τ m ω).eq_or_lt with h0 | h0
    · have ht0 : t = 0 := le_antisymm (ht.trans h0.ge) zero_le
      subst ht0
      simp only [martProc, martValue, sub_self, mul_zero, Finset.sum_const_zero, add_zero, abs_zero]
      exact hC
    · exact abs_martProc_le (hτb m ω h0 t ht) (hτb m ω h0 0 zero_le)
  · have e : (fun t ω => martProc ρ W V (min t (τ m ω)) ω / Real.sqrt k) =
        (Real.sqrt k)⁻¹ • fun t ω => martProc ρ W V (min t (τ m ω)) ω := by
      funext t ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact (hmart m).1.smul _
  · have e : (fun t ω => (martProc ρ W V (min t (τ m ω)) ω / Real.sqrt k) ^ 2 - ((min t (τ m ω) : ℝ≥0) : ℝ)) =
        k⁻¹ • fun t ω => martProc ρ W V (min t (τ m ω)) ω ^ 2 - k * ((min t (τ m ω) : ℝ≥0) : ℝ) := by
      funext t ω
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_pow, Real.sq_sqrt hk0.le]
      field_simp
    rw [e]
    exact (hmart m).2.smul _


end Main

end InteractingSLE.Sec7.PocketMartLife
