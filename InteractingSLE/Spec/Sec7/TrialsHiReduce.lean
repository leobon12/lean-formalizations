/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHiCode
import InteractingSLE.Spec.Sec7.ContinuityProb5Trial
import InteractingSLE.Spec.Sec7.ContinuityProbGaps
import InteractingSLE.Spec.Sec7.ContinuityProb3Cont

/-!
# Aux. lemma 113, `τ = ∞`: the trials (every `κ > 0`)

Packet PROVE-TRIALS-HI. Specification §7.3, Aux. lemma 113's proof, "Two positive endpoint parameters" and the final
martingale argument (`source/spec/p337-384.md` L716–L737, pp. 370–372), with Astra's terminal trial principle (D.3.4,
`Sec7.Trial.measure_compl_eq_zero_of_trials`, ruling R38).

For an evolution of a separated ordered word with at least one mark on each side, write `L = W − V^{L,0}`,
`R = V^{R,0} − W`, `D = L + R` (the nearest cross-gap, nondecreasing) and `U = L/D`. This file proves, for every
`κ > 0`:

> if the canonical probability of the non-transience event is at most `1 − p(M)` from every ordered word whose
> nearest marks are at `∓1` and whose marks lie in `[−M, M]` (`UniformTrialBound`, the conclusion of Aux. lemmas
> 109/111 in the form the trials use), and if the evolution is transient on every eventual band (`U < 3/4`
> eventually, or `U > 1/4` eventually: the one-sided phases, Aux. lemma 101), then almost surely the evolution is not
> non-transient (`ae_not_nonTransientEvent_of_trials`).

The trials are at the stopping times `ξ_n = max(n, first t ≥ n with L = R)` (`trialTime`, the moving-midpoint
trials): at a trial the realized word divided by `D/2` has its nearest marks at `∓1` and its marks in `[−M, M]`,
`M = 1 + 2 (spreads)/D₀` (same-side spreads decrease, `D` increases; `mem_family_of_band`). By the strong Markov
restart at `ξ_n` (`measure_restart_codeEvent`), dilation invariance (`codeLaw_nt_dilate'`) and pullback at infinity
(`nonTransientEvent_shiftNN`), `P(not non-transient | 𝓕_{ξ_n}) ≥ p` on `{ξ_n < ζ}`. Off an eventual band the driver
returns to the midpoint after every time (intermediate values of `L − R`), so on the non-transience event every trial
is finite, and the terminal trial principle concludes. The trial times are at least the deterministic times `n`, so
no accumulation of trials has to be excluded.

## Main results

* `UniformTrialBound`, `famBound`, `mem_family_of_band`;
* `ae_le_condExp_indicator_of_forall` (a conditional lower bound from set-measure lower bounds);
* `bandTest`, `trialTime`, `isStoppingTime_trialTime`;
* `EventualBandPath`, `exists_band_of_not_eventualBandPath`, `codeLaw_wordAt_le_of_band`;
* **`ae_not_nonTransientEvent_of_trials`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi

open ZhanGT4 Zhan Sec7.Dilation Sec7.RandRestart Sec2 Sec2.Assembly Sec2.Restart

/-! ### The uniform trial bound -/

/-- **The uniform trial bound** for the weights `ρL, ρR` (the conclusion of Aux. lemmas 109 and 111 in the form used
by the moving-midpoint trials of Aux. lemma 113, Specification pp. 364–371: "At every subsequent midpoint time `ξ`,
center at the driver and scale by `D_ξ/2`. Both groups then lie in the same compact intervals `[−M, −1]` and
`[1, M]`"): for every `M`, a `p > 0` such that from every ordered word whose nearest marks are at `−1` and `1` and
whose marks lie in `[−M, M]`, the canonical probability of the non-transience event (infinite lifetime and a
non-transient trace) is at most `1 − p`. -/
def UniformTrialBound (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) : Prop :=
  ∀ M : ℝ, ∃ p : ℝ, 0 < p ∧ ∀ (yL : Fin (nL + 1) → ℝ) (yR : Fin (nR + 1) → ℝ), IsOrderedForceWord yL yR →
    yL 0 = -1 → yR 0 = 1 → (∀ i, -M ≤ yL i) → (∀ j, yR j ≤ M) →
    codeLaw κ ρL ρR ntCodeSet (yL, yR) ≤ ENNReal.ofReal (1 - p)

/-! ### The normalized word at a trial -/

section Family

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The bound `M = 1 + 2 (spreads)/D₀` of the normalized words at the trials. -/
def famBound (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) : ℝ :=
  1 + 2 * ((∑ i, (xL 0 - xL i)) + ∑ j, (xR j - xR 0)) / (xR 0 - xL 0)

/-- **The normalized word at a trial.** If at a time `t < ζ` the driver is at the midpoint of the nearest marks
(`L = R`), then `D > 0` and the realized word divided by `D/2` has its nearest marks at `−1`, `1` and all its marks in
`[−M, M]`, `M = famBound xL xR` (same-side spreads decrease, `D` increases). -/
theorem mem_family_of_band (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hF : IsOrderedForceWord xL xR)
    (hsep : xL 0 < xR 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hband : w t - vL 0 t = vR 0 t - w t) :
    0 < vR 0 t - vL 0 t ∧ (vL 0 t - w t) / ((vR 0 t - vL 0 t) / 2) = -1 ∧
      (vR 0 t - w t) / ((vR 0 t - vL 0 t) / 2) = 1 ∧
      (∀ i, -famBound xL xR ≤ (vL i t - w t) / ((vR 0 t - vL 0 t) / 2)) ∧
      ∀ j, (vR j t - w t) / ((vR 0 t - vL 0 t) / 2) ≤ famBound xL xR := by
  have hf := hp.isForcePath
  set D := vR 0 t - vL 0 t with hD
  set D₀ := xR 0 - xL 0 with hD₀
  have hD₀pos : 0 < D₀ := sub_pos.2 hsep
  have hDD₀ : D₀ ≤ D := by
    have := hf.crossGap_le 0 0 (zero_le : (0 : ℝ≥0) ≤ t) ht
    rwa [hf.vL_zero, hf.vR_zero] at this
  have hDpos : 0 < D := lt_of_lt_of_le hD₀pos hDD₀
  have hD2 : 0 < D / 2 := by positivity
  have hsL : ∀ i, 0 ≤ xL 0 - xL i := fun i => sub_nonneg.2 (hF.1 (Fin.zero_le i))
  have hsR : ∀ j, 0 ≤ xR j - xR 0 := fun j => sub_nonneg.2 (hF.2.2.1 (Fin.zero_le j))
  set S := (∑ i, (xL 0 - xL i)) + ∑ j, (xR j - xR 0) with hS
  have hS0 : 0 ≤ S := add_nonneg (Finset.sum_nonneg fun i _ => hsL i) (Finset.sum_nonneg fun j _ => hsR j)
  have hSL : ∀ i, xL 0 - xL i ≤ S := fun i =>
    le_add_of_le_of_nonneg (Finset.single_le_sum (fun i _ => hsL i) (Finset.mem_univ i))
      (Finset.sum_nonneg fun j _ => hsR j)
  have hSR : ∀ j, xR j - xR 0 ≤ S := fun j =>
    le_add_of_nonneg_of_le (Finset.sum_nonneg fun i _ => hsL i)
      (Finset.single_le_sum (fun j _ => hsR j) (Finset.mem_univ j))
  have hM : famBound xL xR = 1 + 2 * S / D₀ := rfl
  have hSD : 2 * S ≤ 2 * S / D₀ * D := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hD₀pos]
    exact mul_le_mul_of_nonneg_left hDD₀ (by positivity)
  refine ⟨hDpos, ?_, ?_, fun i => ?_, fun j => ?_⟩
  · rw [div_eq_iff hD2.ne']; linarith
  · rw [div_eq_iff hD2.ne']; linarith
  · have hi2 : vL 0 t - vL i t ≤ xL 0 - xL i := hf.vL_sub_vL_le ht (Fin.zero_le i)
    rw [hM, le_div_iff₀ hD2]
    nlinarith [hSL i]
  · have hj2 : vR j t - vR 0 t ≤ xR j - xR 0 := hf.vR_sub_vR_le ht (Fin.zero_le j)
    rw [hM, div_le_iff₀ hD2]
    nlinarith [hSR j]

end Family

/-! ### A conditional lower bound from set-measure lower bounds -/

section Cond

variable {Ω : Type*}

/-- **Conditional lower bound.** If `E ∈ m` and every `A ∈ m` inside `E` has `p · P(A) ≤ P(A ∩ G)`, then
`P(G ∣ m) ≥ p` almost surely on `E`. -/
theorem ae_le_condExp_indicator_of_forall {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) {P : Measure Ω}
    [IsFiniteMeasure P] {G E : Set Ω} (hG : MeasurableSet G) (hE : MeasurableSet[m] E) {p : ℝ}
    (hp : 0 ≤ p) (h : ∀ A, MeasurableSet[m] A → A ⊆ E → ENNReal.ofReal p * P A ≤ P (A ∩ G)) :
    ∀ᵐ ω ∂P, ω ∈ E → p ≤ (P[G.indicator (fun _ => (1 : ℝ)) | m]) ω := by
  set g : Ω → ℝ := G.indicator fun _ => (1 : ℝ) with hg
  have hgi : Integrable g P := (integrable_const (1 : ℝ)).indicator hG
  set f₁ : Ω → ℝ := E.indicator fun _ => p with hf₁
  set f₂ : Ω → ℝ := E.indicator (P[g | m]) with hf₂
  have hf₁m : StronglyMeasurable[m] f₁ := stronglyMeasurable_const.indicator hE
  have hf₂m : StronglyMeasurable[m] f₂ := stronglyMeasurable_condExp.indicator hE
  have hf₁i : Integrable f₁ P := (integrable_const p).indicator (hm _ hE)
  have hf₂i : Integrable f₂ P := integrable_condExp.indicator (hm _ hE)
  have hle : f₁ ≤ᵐ[P] f₂ := by
    refine ae_le_of_ae_le_trim (hm := hm) ?_
    refine ae_le_of_forall_setIntegral_le (hf₁i.trim hm hf₁m) (hf₂i.trim hm hf₂m) fun s hs _ => ?_
    rw [← setIntegral_trim hm hf₁m hs, ← setIntegral_trim hm hf₂m hs]
    have hsE : MeasurableSet[m] (s ∩ E) := hs.inter hE
    rw [hf₁, hf₂, setIntegral_indicator (hm _ hE), setIntegral_indicator (hm _ hE),
      setIntegral_condExp hm hgi hsE, hg, setIntegral_indicator hG, setIntegral_const, setIntegral_const,
      smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
    have hA := h (s ∩ E) hsE inter_subset_right
    have hfin : P (s ∩ E ∩ G) ≠ ⊤ := measure_ne_top P _
    have key : (ENNReal.ofReal p * P (s ∩ E)).toReal ≤ (P (s ∩ E ∩ G)).toReal :=
      ENNReal.toReal_mono hfin hA
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp] at key
    exact key
  filter_upwards [hle] with ω hω hωE
  simpa [hf₁, hf₂, hωE] using hω

end Cond

/-! ### Monotonicity of first meetings -/

section Meet

variable {Ω : Type*}

/-- A larger second process meets later. -/
theorem firstMeet_mono {W V V' : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (h : ∀ t, V t ω ≤ V' t ω) :
    firstMeet W V ζ ω ≤ firstMeet W V' ζ ω := by
  unfold firstMeet
  refine inf_le_inf_left _ (le_iInf₂ fun t ht => ?_)
  exact iInf₂_le t ⟨ht.1, (h t).trans ht.2⟩

end Meet


/-! ### The trial times -/

section Trials

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The midpoint test of the `n`-th trial**: `max(|L − R|, n − t)`, nonpositive exactly when `t ≥ n` and the driver
is at the midpoint of the nearest marks. -/
def bandTest (n : ℕ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ :=
  fun t ω => max |(W t ω - VL 0 t ω) - (VR 0 t ω - W t ω)| ((n : ℝ) - t)

/-- **The `n`-th trial time**: the first time `≥ n` before the lifetime at which the driver is in the middle band
(the lifetime if there is none), and at least `n`; on the null set `N` it is `n`. -/
def trialTime (N : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  max (zeroOn N (firstMeet zeroProc (bandTest n W VL VR) ζ) ω) ((n : ℝ≥0) : ℝ≥0∞)

variable {N : Set Ω} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}

theorem continuousOn_bandTest {ω : Ω} (hW : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hL : ContinuousOn (fun t => VL 0 t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hR : ContinuousOn (fun t => VR 0 t ω) {t | (t : ℝ≥0∞) < ζ ω}) (n : ℕ) :
    ContinuousOn (fun t => bandTest n W VL VR t ω - zeroProc t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
  simp only [bandTest, zeroProc, sub_zero]
  exact continuous_max.comp_continuousOn
    ((((hW.sub hL).sub (hR.sub hW)).abs).prodMk
      (continuousOn_const.sub NNReal.continuous_coe.continuousOn))

/-- **The trial times are stopping times** (in a filtration where the null set `N` is measurable at every time). -/
theorem isStoppingTime_trialTime {𝓖 : Filtration ℝ≥0 mΩ} (hW : AdaptedBefore 𝓖 ζ W)
    (hL : AdaptedBefore 𝓖 ζ (VL 0)) (hR : AdaptedBefore 𝓖 ζ (VR 0)) (hN : ∀ t, MeasurableSet[𝓖 t] N)
    (hc : ∀ ω ∉ N, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ContinuousOn (fun t => VL 0 t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ContinuousOn (fun t => VR 0 t ω) {t | (t : ℝ≥0∞) < ζ ω}) (n : ℕ) :
    IsStoppingTime 𝓖 fun ω => (trialTime N ζ W VL VR n ω : WithTop ℝ≥0) := by
  have hYa : AdaptedBefore 𝓖 ζ (bandTest n W VL VR) :=
    adaptedBefore_of_eq (fun t p => max |(p.1 - p.2.1) - (p.2.2 - p.1)| ((n : ℝ) - t))
      (fun t => by fun_prop) hW hL hR fun t ω => rfl
  have hZa : AdaptedBefore 𝓖 ζ (zeroProc (Ω := Ω)) :=
    adaptedBefore_of_eq (fun _ _ => 0) (fun _ => measurable_const) hW hL hR fun _ _ => rfl
  have h := isStoppingTime_firstMeet_off hZa hYa hN fun ω hω =>
    continuousOn_bandTest (hc ω hω).1 (hc ω hω).2.1 (hc ω hω).2.2 n
  exact h.max_const (n : ℝ≥0)

theorem le_trialTime (n : ℕ) (ω : Ω) : ((n : ℝ≥0) : ℝ≥0∞) ≤ trialTime N ζ W VL VR n ω := le_max_right _ _

theorem monotone_trialTime (ω : Ω) : Monotone fun n => trialTime N ζ W VL VR n ω := by
  intro n n' hn
  refine max_le_max ?_ (by exact_mod_cast hn)
  by_cases hω : ω ∈ N
  · simp only [zeroOn_of_mem hω, le_refl]
  · rw [zeroOn_of_notMem hω, zeroOn_of_notMem hω]
    refine firstMeet_mono fun t => max_le_max le_rfl ?_
    have : (n : ℝ) ≤ n' := by exact_mod_cast hn
    linarith

/-- At a trial before the lifetime (off `N`) the driver is at the midpoint and the trial time is the first
meeting. -/
theorem exists_trialTime_eq {n : ℕ} {ω : Ω} (hω : ω ∉ N)
    (hc : ContinuousOn (fun t => bandTest n W VL VR t ω - zeroProc t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hlt : trialTime N ζ W VL VR n ω < ζ ω) :
    ∃ m : ℝ≥0, trialTime N ζ W VL VR n ω = m ∧ (m : ℝ≥0∞) < ζ ω ∧
      W m ω - VL 0 m ω = VR 0 m ω - W m ω := by
  have hfm : firstMeet zeroProc (bandTest n W VL VR) ζ ω < ζ ω := by
    refine lt_of_le_of_lt ?_ hlt
    rw [trialTime, zeroOn_of_notMem hω]
    exact le_max_left _ _
  obtain ⟨m, hm, hmζ, hmV⟩ := exists_eq_firstMeet hc hfm
  simp only [bandTest, zeroProc, max_le_iff] at hmV
  have hnm : ((n : ℝ≥0) : ℝ≥0∞) ≤ m := by
    have : (n : ℝ) ≤ m := by linarith [hmV.2]
    exact_mod_cast this
  have h0 : (W m ω - VL 0 m ω) - (VR 0 m ω - W m ω) = 0 := abs_eq_zero.1 (le_antisymm hmV.1 (abs_nonneg _))
  refine ⟨m, ?_, hmζ, by linarith⟩
  rw [trialTime, zeroOn_of_notMem hω, hm, max_eq_left hnm]

end Trials

/-! ### Eventual bands -/

section Band

/-- **The eventual band** of a path: eventually the driver is at distance more than `D/4` from the nearest right
mark (`U < 3/4`), or eventually at distance more than `D/4` from the nearest left mark (`U > 1/4`); the band of
`Sec7.Band.ae_tendsto_of_eventualBand`. -/
def EventualBandPath (w vl vr : ℝ≥0 → ℝ) : Prop :=
  (∃ T : ℝ≥0, ∀ t, T ≤ t → vr t - vl t < 4 * (vr t - w t)) ∨
    ∃ T : ℝ≥0, ∀ t, T ≤ t → vr t - vl t < 4 * (w t - vl t)

/-- **Off an eventual band the driver returns to the midpoint after every time** (intermediate values of `L − R`
between a time with `3R ≤ L` and a time with `3L ≤ R`). -/
theorem exists_band_of_not_eventualBandPath {w vl vr : ℝ≥0 → ℝ}
    (hc : Continuous fun t => (w t - vl t) - (vr t - w t)) (hl : ∀ t, vl t ≤ w t) (hr : ∀ t, w t ≤ vr t)
    (h : ¬ EventualBandPath w vl vr) (T : ℝ≥0) : ∃ s, T ≤ s ∧ w s - vl s = vr s - w s := by
  simp only [EventualBandPath, not_or, not_exists, not_forall, not_lt] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨t₁, ht₁, hb₁⟩ := h1 T
  obtain ⟨t₂, ht₂, hb₂⟩ := h2 T
  have hψ1 : 0 ≤ (w t₁ - vl t₁) - (vr t₁ - w t₁) := by linarith [hr t₁]
  have hψ2 : (w t₂ - vl t₂) - (vr t₂ - w t₂) ≤ 0 := by linarith [hl t₂]
  rcases le_total t₁ t₂ with h12 | h21
  · obtain ⟨s, hs, hψs⟩ := intermediate_value_Icc' h12 hc.continuousOn ⟨hψ2, hψ1⟩
    exact ⟨s, ht₁.trans hs.1, by linarith [hψs]⟩
  · obtain ⟨s, hs, hψs⟩ := intermediate_value_Icc h21 hc.continuousOn ⟨hψ2, hψ1⟩
    exact ⟨s, ht₂.trans hs.1, by linarith [hψs]⟩

end Band

/-! ### Scaling of ordered words -/

theorem isOrderedForceWord_mul {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (h : IsOrderedForceWord xL xR)
    {c : ℝ} (hc : 0 ≤ c) : IsOrderedForceWord (fun i => c * xL i) (fun j => c * xR j) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun i j hij => mul_le_mul_of_nonneg_left (h1 hij) hc, fun i => mul_nonpos_of_nonneg_of_nonpos hc (h2 i),
    fun i j hij => mul_le_mul_of_nonneg_left (h3 hij) hc, fun j => mul_nonneg hc (h4 j)⟩

/-! ### The trials -/

section Main

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The canonical non-transience probability at a trial** is at most `1 − p`: the realized word, divided by half
the cross-gap, lies in the uniform family. -/
theorem codeLaw_wordAt_le_of_band (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    {p : ℝ} (hpU : ∀ (yL : Fin (nL + 1) → ℝ) (yR : Fin (nR + 1) → ℝ), IsOrderedForceWord yL yR →
      yL 0 = -1 → yR 0 = 1 → (∀ i, -famBound xL xR ≤ yL i) → (∀ j, yR j ≤ famBound xL xR) →
      codeLaw κ ρL ρR ntCodeSet (yL, yR) ≤ ENNReal.ofReal (1 - p))
    {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b τ) {m : ℝ≥0} (hm : (m : ℝ≥0∞) < τ)
    (hband : w m - vL 0 m = vR 0 m - w m) :
    codeLaw κ ρL ρR ntCodeSet ((fun i => vL i m - w m), fun j => vR j m - w m) ≤ ENNReal.ofReal (1 - p) := by
  obtain ⟨hD, h0L, h0R, hbL, hbR⟩ := mem_family_of_band hp hF (hsep 0 0) hm hband
  set D := vR 0 m - vL 0 m with hDdef
  have hD2 : 0 < D / 2 := by positivity
  set c : ℝ≥0 := ⟨(D / 2) ^ 2, by positivity⟩ with hcdef
  have hc : c ≠ 0 := by
    intro h
    have : (D / 2) ^ 2 = 0 := congrArg NNReal.toReal h
    exact (pow_pos hD2 2).ne' this
  have hsq : (√(c : ℝ))⁻¹ = (D / 2)⁻¹ := by
    show (√((D / 2) ^ 2))⁻¹ = (D / 2)⁻¹
    rw [Real.sqrt_sq hD2.le]
  have hord := isOrderedForceWord_at hp hm
  have hsep' : ∀ i j, vL i m - w m < vR j m - w m := fun i j => by
    have h1 := hp.isForcePath.antitone_vL hm (Fin.zero_le i)
    have h2 := hp.isForcePath.monotone_vR hm (Fin.zero_le j)
    have h3 : vL 0 m - w m < vR 0 m - w m := by linarith
    simp only at h1 h2
    linarith
  rw [← codeLaw_nt_dilate' hκ hord hsep' hc, hsq]
  refine hpU _ _ (isOrderedForceWord_mul hord (inv_nonneg.2 hD2.le)) ?_ ?_ (fun i => ?_) fun j => ?_
  · show (D / 2)⁻¹ * (vL 0 m - w m) = -1
    rw [inv_mul_eq_div]; exact h0L
  · show (D / 2)⁻¹ * (vR 0 m - w m) = 1
    rw [inv_mul_eq_div]; exact h0R
  · rw [inv_mul_eq_div]; exact hbL i
  · rw [inv_mul_eq_div]; exact hbR j

/-- **Aux. lemma 113, `τ = ∞`, by trials** (every `κ > 0`; Specification pp. 370–372, the terminal trial principle
of Astra's D.3.4). For an evolution of a separated ordered word with at least one mark on each side, if the weights
satisfy the uniform trial bound (Aux. lemmas 109/111) and the evolution is almost surely not non-transient on every
eventual band (the one-sided phases, Aux. lemma 101), then almost surely it is not non-transient: on an infinite
lifetime every continuous generating trace on `[0, ∞)` tends to infinity. -/
theorem ae_not_nonTransientEvent_of_trials [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hF : IsOrderedForceWord xL xR)
    (hsep : ∀ i j, xL i < xR j) (hU : UniformTrialBound κ ρL ρR)
    (hband : ∀ᵐ ω ∂P, ζ ω = ⊤ → EventualBandPath (fun t => W t ω) (fun t => VL 0 t ω) (fun t => VR 0 t ω) →
      ¬ NonTransientEvent (fun t => W t ω) (ζ ω)) :
    ∀ᵐ ω ∂P, ¬ NonTransientEvent (fun t => W t ω) (ζ ω) := by
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  -- the good set and its null complement
  set Good : Ω → Prop := fun ω => IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (fun t => B t ω) (ζ ω) ∧ (ζ ω = ⊤ →
      EventualBandPath (fun t => W t ω) (fun t => VL 0 t ω) (fun t => VR 0 t ω) →
      ¬ NonTransientEvent (fun t => W t ω) (ζ ω)) with hGood
  have hgood : ∀ᵐ ω ∂P, Good ω := by
    filter_upwards [hE.2.2.2.2, hband] with ω h1 h2 using ⟨h1, h2⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hN𝓖 : ∀ t, MeasurableSet[𝓖 t] N := fun t => Ito.measurableSet_usualAugmentation_of_null hNm hN0 t
  have hgN : ∀ ω ∉ N, Good ω := fun ω hω => by
    by_contra h
    exact hω (hNsub h)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hcN : ∀ ω ∉ N, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ContinuousOn (fun t => VL 0 t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ContinuousOn (fun t => VR 0 t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω => by
    have hf := (hgN ω hω).1.isForcePath
    exact ⟨hf.continuousOn_w, hf.continuousOn_vL 0, hf.continuousOn_vR 0⟩
  -- the trial times
  set ξ : ℕ → Ω → ℝ≥0∞ := fun n => trialTime N ζ W VL VR n with hξdef
  have hξ : ∀ n, IsStoppingTime 𝓖 fun ω => (ξ n ω : WithTop ℝ≥0) := fun n =>
    isStoppingTime_trialTime hEa.2.1 (hEa.2.2.1 0) (hEa.2.2.2.1 0) hN𝓖 hcN n
  have hmono : ∀ ω, Monotone fun n => (ξ n ω : WithTop ℝ≥0) := fun ω => monotone_trialTime ω
  have hinf : ∀ ω (t : ℝ≥0), ∃ n, (t : WithTop ℝ≥0) < ξ n ω := fun ω t => by
    obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
    refine ⟨n, lt_of_lt_of_le ?_ (le_trialTime n ω)⟩
    have : t < (n : ℝ≥0) := by rw [← NNReal.coe_lt_coe]; exact_mod_cast hn
    exact ENNReal.coe_lt_coe.2 this
  -- the success event
  set G : Set Ω := {ω | ¬ NonTransientEvent (fun t => W t ω) (ζ ω)} with hGdef
  have hζs : IsStoppingTime 𝓖 fun ω => (ζ ω : WithTop ℝ≥0) := Ito.isStoppingTime_lifetime hEa.2.1
  have hGm : MeasurableSet[⨆ t, 𝓖 t] G := (measurableSet_nonTransient hEa.2.1 hζs).compl
  have hGm' : MeasurableSet G := (iSup_le fun t => 𝓖.le t) _ hGm
  -- the uniform bound at the trials
  obtain ⟨p₀, hp₀, hpU₀⟩ := hU (famBound xL xR)
  set p : ℝ := min p₀ 1 with hpdef
  have hp0 : 0 < p := lt_min hp₀ one_pos
  have hp1 : p ≤ 1 := min_le_right _ _
  have hpU : ∀ (yL : Fin (nL + 1) → ℝ) (yR : Fin (nR + 1) → ℝ), IsOrderedForceWord yL yR →
      yL 0 = -1 → yR 0 = 1 → (∀ i, -famBound xL xR ≤ yL i) → (∀ j, yR j ≤ famBound xL xR) →
      codeLaw κ ρL ρR ntCodeSet (yL, yR) ≤ ENNReal.ofReal (1 - p) := fun yL yR h1 h2 h3 h4 h5 =>
    (hpU₀ yL yR h1 h2 h3 h4 h5).trans (ENNReal.ofReal_le_ofReal (by linarith [min_le_left p₀ 1]))
  have hsum : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
    rw [← ENNReal.ofReal_add hp0.le (by linarith), add_sub_cancel, ENNReal.ofReal_one]
  -- the trial bound
  have htrial : ∀ n, ∀ᵐ ω ∂P, ω ∉ G →
      p ≤ (P[G.indicator (fun _ => (1 : ℝ)) | (hξ n).measurableSpace]) ω := by
    intro n
    set E : Set Ω := Nᶜ ∩ {ω | ξ n ω < ζ ω} with hEdef
    have hEm : MeasurableSet[(hξ n).measurableSpace] E := by
      refine MeasurableSet.inter ?_ ?_
      · rw [(hξ n).measurableSet]
        refine ⟨le_iSup (fun t => 𝓖 t) 0 _ (hN𝓖 0).compl, fun i => (hN𝓖 i).compl.inter ?_⟩
        exact (hξ n).measurableSet_le i
      · have h2 := (hζs.measurableSet_stopping_time_le (hξ n)).compl
        have e : {ω | ξ n ω < ζ ω} = {ω | (ζ ω : WithTop ℝ≥0) ≤ (ξ n ω : WithTop ℝ≥0)}ᶜ := by
          ext ω
          simp only [mem_ofPred_eq, mem_compl_iff, not_le]
        rw [e]
        exact h2
    have hbound := ae_le_condExp_indicator_of_forall (P := P) (hξ n).measurableSpace_le hGm' hEm hp0.le ?_
    · filter_upwards [hbound, hNae] with ω hω hωN hωG
      refine hω ⟨hωN, ?_⟩
      obtain ⟨hp, hb⟩ := hgN ω hωN
      have hnt : NonTransientEvent (fun t => W t ω) (ζ ω) := not_not.1 hωG
      have hζ : ζ ω = ⊤ := hnt.1
      have hf := hp.isForcePath
      have hwc : Continuous fun t => W t ω :=
        continuousOn_univ.1 (hf.continuousOn_w.mono fun t _ => by rw [hζ]; exact ENNReal.coe_lt_top)
      have hlc : Continuous fun t => VL 0 t ω :=
        continuousOn_univ.1 ((hf.continuousOn_vL 0).mono fun t _ => by rw [hζ]; exact ENNReal.coe_lt_top)
      have hrc : Continuous fun t => VR 0 t ω :=
        continuousOn_univ.1 ((hf.continuousOn_vR 0).mono fun t _ => by rw [hζ]; exact ENNReal.coe_lt_top)
      have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζ]; exact ENNReal.coe_lt_top
      obtain ⟨s, hns, hs⟩ := exists_band_of_not_eventualBandPath ((hwc.sub hlc).sub (hrc.sub hwc))
        (fun t => hf.vL_le_w (hlt t) 0) (fun t => hf.w_le_vR (hlt t) 0)
        (fun h => hb hζ h hnt) (n : ℝ≥0)
      have hmeet : firstMeet zeroProc (bandTest n W VL VR) ζ ω ≤ s := by
        refine firstMeet_le_of (hlt s) ?_
        simp only [bandTest, zeroProc, max_le_iff]
        constructor
        · rw [hs, sub_self, abs_zero]
        · have : (n : ℝ) ≤ s := by exact_mod_cast hns
          linarith
      have hξs : ξ n ω ≤ s := by
        simp only [hξdef, trialTime, zeroOn_of_notMem hωN]
        exact max_le hmeet (by exact_mod_cast hns)
      exact lt_of_le_of_lt hξs (hlt s)
    · intro A hA hAE
      set AK : ℕ → Set Ω := fun K => A ∩ {ω | ξ n ω ≤ ((K : ℝ≥0) : ℝ≥0∞)} with hAKdef
      have hAKmono : Monotone AK := fun K K' hK => inter_subset_inter_right _ fun ω (hω : ξ n ω ≤ _) =>
        le_trans hω (by exact_mod_cast hK)
      have hcov : A = ⋃ K, AK K := by
        ext ω
        refine ⟨fun hω => ?_, fun hω => (mem_iUnion.1 hω).elim fun K h => h.1⟩
        have hfin : ξ n ω ≠ ⊤ := ne_top_of_lt (hAE hω).2
        obtain ⟨K, hK⟩ := exists_nat_gt (ξ n ω).toReal
        refine mem_iUnion.2 ⟨K, hω, ?_⟩
        show ξ n ω ≤ ((K : ℝ≥0) : ℝ≥0∞)
        rw [← ENNReal.ofReal_toReal hfin]
        exact (ENNReal.ofReal_le_ofReal hK.le).trans (by simp)
      have hstep : ∀ K, ENNReal.ofReal p * P (AK K) ≤ P (AK K ∩ G) := by
        intro K
        set T : Ω → ℝ≥0 := fun ω => (min (ξ n ω) ((K : ℝ≥0) : ℝ≥0∞)).toNNReal with hTdef
        have hT_coe : ∀ ω, ((T ω : ℝ≥0) : ℝ≥0∞) = min (ξ n ω) ((K : ℝ≥0) : ℝ≥0∞) := fun ω =>
          ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
        have hTs : IsStoppingTime 𝓖 fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0) := by
          have h := (hξ n).min_const (K : ℝ≥0)
          have he : (fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0)) =
              fun ω => min (ξ n ω : WithTop ℝ≥0) (K : ℝ≥0) := funext fun ω => hT_coe ω
          rw [he]; exact h
        have hTA : ∀ ω ∈ AK K, ((T ω : ℝ≥0) : ℝ≥0∞) = ξ n ω := fun ω hω => by
          rw [hT_coe]; exact min_eq_left hω.2
        have hAKm : MeasurableSet[hTs.measurableSpace] (AK K) := by
          have hA' := ((hξ n).measurableSet A).1 hA
          rw [hTs.measurableSet]
          refine ⟨hA'.1.inter (le_iSup (fun t => 𝓖 t) (K : ℝ≥0) _ ((hξ n).measurableSet_le (K : ℝ≥0))),
            fun i => ?_⟩
          have heq : AK K ∩ {ω | ((T ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} =
              (A ∩ {ω | (ξ n ω : WithTop ℝ≥0) ≤ i}) ∩ {ω | ξ n ω ≤ ((K : ℝ≥0) : ℝ≥0∞)} := by
            ext ω
            constructor
            · rintro ⟨⟨h1, h2⟩, h3⟩
              have h3' : ((T ω : ℝ≥0) : ℝ≥0∞) ≤ i := h3
              rw [hTA ω ⟨h1, h2⟩] at h3'
              exact ⟨⟨h1, h3'⟩, h2⟩
            · rintro ⟨⟨h1, h3⟩, h2⟩
              refine ⟨⟨h1, h2⟩, ?_⟩
              show ((T ω : ℝ≥0) : ℝ≥0∞) ≤ i
              rw [hTA ω ⟨h1, h2⟩]; exact h3
          rw [heq]
          rcases le_total i (K : ℝ≥0) with hiK | hKi
          · have he : (A ∩ {ω | (ξ n ω : WithTop ℝ≥0) ≤ i}) ∩ {ω | ξ n ω ≤ ((K : ℝ≥0) : ℝ≥0∞)} =
                A ∩ {ω | (ξ n ω : WithTop ℝ≥0) ≤ i} :=
              inter_eq_left.2 fun ω hω => by
                show ξ n ω ≤ ((K : ℝ≥0) : ℝ≥0∞)
                exact le_trans (show ξ n ω ≤ (i : ℝ≥0∞) from hω.2) (by exact_mod_cast hiK)
            rw [he]; exact hA'.2 i
          · have he : (A ∩ {ω | (ξ n ω : WithTop ℝ≥0) ≤ i}) ∩ {ω | ξ n ω ≤ ((K : ℝ≥0) : ℝ≥0∞)} =
                A ∩ {ω | (ξ n ω : WithTop ℝ≥0) ≤ (K : ℝ≥0)} := by
              ext ω
              constructor
              · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
              · rintro ⟨h1, h2⟩
                refine ⟨⟨h1, ?_⟩, h2⟩
                show ξ n ω ≤ (i : ℝ≥0∞)
                exact le_trans (show ξ n ω ≤ ((K : ℝ≥0) : ℝ≥0∞) from h2) (by exact_mod_cast hKi)
            rw [he]; exact 𝓖.mono hKi _ (hA'.2 (K : ℝ≥0))
        have hAT : ∀ ω ∈ AK K, ((T ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j) :=
          fun ω hω => ⟨by rw [hTA ω hω]; exact (hAE hω.1).2, Or.inr hsep⟩
        have hlaw := measure_restart_codeEvent hκ hEa hTs hAKm hAT (Φ := NonTransientEvent)
          measurableSet_ntCodeSet (fun _ _ _ => Iff.rfl) nonTransientEvent_congr
        -- the failures of the trial are failures of the restarted driver
        have hsub : AK K ∩ Gᶜ ⊆ AK K ∩ {ω | NonTransientEvent (fun t => W (T ω + t) ω - W (T ω) ω)
            (ζ ω - T ω)} := by
          rintro ω ⟨hωA, hωG⟩
          refine ⟨hωA, ?_⟩
          have hnt : NonTransientEvent (fun t => W t ω) (ζ ω) := not_not.1 hωG
          have hζ : ζ ω = ⊤ := hnt.1
          have hp := (hgN ω (hAE hωA.1).1).1
          have hwc : Continuous fun t => W t ω :=
            continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => by
              rw [hζ]; exact ENNReal.coe_lt_top)
          rw [hζ] at hnt
          have h2 := nonTransientEvent_shiftNN hwc hp.1 hnt (T ω)
          show NonTransientEvent (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)
          rw [hζ, ENNReal.top_sub_coe]
          exact h2
        -- the bound at the trial
        have hint : ∫⁻ ω in AK K, codeLaw κ ρL ρR ntCodeSet (wordAt W VL VR T ω) ∂P ≤
            ENNReal.ofReal (1 - p) * P (AK K) := by
          rw [← setLIntegral_const]
          refine setLIntegral_mono measurable_const fun ω hω => ?_
          have hωN := (hAE hω.1).1
          have hp := (hgN ω hωN).1
          obtain ⟨m, hm, hmζ, hmb⟩ := exists_trialTime_eq hωN
            (continuousOn_bandTest (hcN ω hωN).1 (hcN ω hωN).2.1 (hcN ω hωN).2.2 n) (hAE hω.1).2
          have hTm : T ω = m := by
            have := (hTA ω hω).trans hm
            exact_mod_cast this
          simp only [wordAt, hTm]
          exact codeLaw_wordAt_le_of_band hκ hF hsep hpU hp hmζ hmb
        have hfail : P (AK K ∩ Gᶜ) ≤ ENNReal.ofReal (1 - p) * P (AK K) :=
          (measure_mono hsub).trans (hlaw.le.trans hint)
        have hsplit : P (AK K ∩ G) + P (AK K ∩ Gᶜ) = P (AK K) := by
          rw [← sdiff_eq]; exact measure_inter_add_sdiff _ hGm'
        have hfin : ENNReal.ofReal (1 - p) * P (AK K) ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P _)
        refine ENNReal.le_of_add_le_add_right hfin ?_
        calc ENNReal.ofReal p * P (AK K) + ENNReal.ofReal (1 - p) * P (AK K) = P (AK K) := by
              rw [← add_mul, hsum, one_mul]
          _ = P (AK K ∩ G) + P (AK K ∩ Gᶜ) := hsplit.symm
          _ ≤ P (AK K ∩ G) + ENNReal.ofReal (1 - p) * P (AK K) := add_le_add le_rfl hfail
      have hPA : P A = ⨆ K, P (AK K) := by
        conv_lhs => rw [hcov]
        exact hAKmono.measure_iUnion
      calc ENNReal.ofReal p * P A = ⨆ K, ENNReal.ofReal p * P (AK K) := by rw [hPA, ENNReal.mul_iSup]
        _ ≤ P (A ∩ G) := iSup_le fun K =>
          (hstep K).trans (measure_mono (inter_subset_inter_left _ inter_subset_left))
  have hfinal := Trial.measure_compl_eq_zero_of_trials hGm hξ hmono hinf htrial
    (p := fun _ => p) (ae_of_all _ fun _ _ => hp0)
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hfinal
  exact hω

end Main

end TrialsHi

end Sec7

end InteractingSLE
