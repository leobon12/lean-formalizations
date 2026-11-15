/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtKSeed
import InteractingSLE.Spec.Sec2.AddMarksGirsanov

/-!
# The `1 + 1` seed word through the local stop, and the coupling clause for modified processes

Packet PROVE-LOCEXT-M (clause (a) of `RestartDrivingLocalityInput`). After a restart at a cell with seed pattern
`(S_L, S_R)`, the seed marks of a side all start at the driver and coincide afterwards. Under the Girsanov measure that
removes the distant drift, the driver and the chosen seed marks satisfy the driving equation of the `1 + 1` seed word
(`oneSeedY`, weights `oneSeedWts`). This file proves the pathwise step and a congruence lemma:

* `oneSeedIdx_eq`: the chosen seed mark of a side is unique;
* **`IsSLEPathUpTo.oneSeed`**: a local path of a word whose seed marks (positions `0`) are `S_L`, `S_R`, together with a
  Brownian path `b'` absorbing the drift of the distant marks (`√κ b' = √κ b − Σ (ρ' − ρ) ∫ 1/(w − v)`, `ρ'` the seed
  weights), is a local path of the `1 + 1` seed word with the seed sums as weights (if both seed sums are `> −2`);
* **`MartMeans.IsCouplingCharFun.congr_ae`**: the coupling clause only depends on the processes almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec2

/-! ### The chosen seed mark -/

section SeedIdx

variable {n : ℕ}

theorem oneSeedCount_le_one (S : Finset (Fin n)) : oneSeedCount S ≤ 1 := by
  classical
  unfold oneSeedCount; split_ifs <;> omega

theorem fin_oneSeedCount_eq {S : Finset (Fin n)} (k k' : Fin (oneSeedCount S)) : k = k' :=
  Fin.ext (by have := oneSeedCount_le_one S; omega)

/-- The seed weights of a pattern: `ρ` on the seed, `0` off it. -/
def patWt (S : Finset (Fin n)) (ρ : Fin n → ℝ) : Fin n → ℝ := fun i => if i ∈ S then ρ i else 0

theorem seedWt_oneSeedY_L (S : Finset (Fin n)) (ρ : Fin n → ℝ) :
    seedWtL (oneSeedY S) (oneSeedWts S ρ) = oneSeedWts S ρ := by
  funext k; simp [seedWtL, oneSeedY]

theorem seedWt_oneSeedY_R (S : Finset (Fin n)) (ρ : Fin n → ℝ) :
    seedWtR (oneSeedY S) (oneSeedWts S ρ) = oneSeedWts S ρ := by
  funext k; simp [seedWtR, oneSeedY]

/-- **Merging the seed drifts**: if the seed marks agree on `[0, t]`, the drift of the seed weights is the drift of the
merged mark. -/
theorem sum_integral_patWt_eq {S : Finset (Fin n)} (ρ : Fin n → ℝ) (w : ℝ≥0 → ℝ) (v : Fin n → ℝ≥0 → ℝ) (t : ℝ)
    (hv : ∀ (h : S.Nonempty), ∀ i ∈ S, ∀ s ∈ Set.uIcc (0 : ℝ) t, v i s.toNNReal = v (S.min' h) s.toNNReal) :
    ∑ i, ∫ s in (0 : ℝ)..t, patWt S ρ i / (w s.toNNReal - v i s.toNNReal) =
      ∑ k, ∫ s in (0 : ℝ)..t, oneSeedWts S ρ k / (w s.toNNReal - v (oneSeedIdx S k) s.toNNReal) := by
  classical
  by_cases hS : S.Nonempty
  · have hk : oneSeedCount S = 1 := oneSeedCount_of_nonempty hS
    have e1 : ∀ i, ∫ s in (0 : ℝ)..t, patWt S ρ i / (w s.toNNReal - v i s.toNNReal) =
        (if i ∈ S then ρ i else 0) * ∫ s in (0 : ℝ)..t, (w s.toNNReal - v (S.min' hS) s.toNNReal)⁻¹ := fun i => by
      by_cases hi : i ∈ S
      · simp only [patWt, hi, ↓reduceIte, div_eq_mul_inv]
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun s hs => ?_
        simp only [hv hS i hi s hs]
      · simp [patWt, hi]
    simp only [e1]
    rw [← Finset.sum_mul, Fintype.sum_ite_mem]
    have e2 : ∀ k : Fin (oneSeedCount S), ∫ s in (0 : ℝ)..t,
        oneSeedWts S ρ k / (w s.toNNReal - v (oneSeedIdx S k) s.toNNReal) =
        (∑ i ∈ S, ρ i) * ∫ s in (0 : ℝ)..t, (w s.toNNReal - v (S.min' hS) s.toNNReal)⁻¹ := fun k => by
      simp only [oneSeedWts, oneSeedIdx, div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul]
    simp only [e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hk, one_smul]
  · have h0 : oneSeedCount S = 0 := by simp [oneSeedCount, hS]
    have hS' : S = ∅ := Finset.not_nonempty_iff_eq_empty.1 hS
    have e : ∀ i, patWt S ρ i = 0 := fun i => by simp [patWt, hS']
    simp only [e, zero_div, intervalIntegral.integral_zero, Finset.sum_const_zero]
    exact (Finset.sum_eq_zero fun k _ => (h0 ▸ k).elim0).symm

end SeedIdx

/-! ### The `1 + 1` seed path -/

section OneSeed

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}
  {SL : Finset (Fin nL)} {SR : Finset (Fin nR)}

theorem thresholdCondition_oneSeed_false (hSL : -2 < ∑ i ∈ SL, ρL i) (hSR : -2 < ∑ j ∈ SR, ρR j) (w₀ : ℝ)
    (uL : Fin (oneSeedCount SL) → ℝ) (uR : Fin (oneSeedCount SR) → ℝ) :
    ¬ ForceWord.ThresholdCondition (oneSeedWts SL ρL) (oneSeedWts SR ρR) w₀ uL uR := by
  classical
  have key : ∀ {n : ℕ} {S : Finset (Fin n)} {ρ : Fin n → ℝ} (u : Fin (oneSeedCount S) → ℝ),
      -2 < ∑ i ∈ S, ρ i → -2 < ∑ k ∈ Finset.univ.filter (fun k => u k = w₀), oneSeedWts S ρ k := by
    intro n S ρ u h
    simp only [oneSeedWts, Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.univ.filter (fun k => u k = w₀)).card : ℝ) ≤ 1 := by
      have h1 := Finset.card_filter_le Finset.univ (fun k => u k = w₀)
      rw [Finset.card_univ, Fintype.card_fin] at h1
      exact_mod_cast h1.trans (oneSeedCount_le_one S)
    rcases Nat.lt_or_ge ((Finset.univ.filter (fun k => u k = w₀)).card) 1 with h0 | h1
    · have : (Finset.univ.filter (fun k => u k = w₀)).card = 0 := by omega
      rw [this]; simp
    · have : ((Finset.univ.filter (fun k => u k = w₀)).card : ℝ) = 1 :=
        le_antisymm hc (by exact_mod_cast h1)
      rw [this, one_mul]; exact h
  rintro (h | h)
  · exact absurd h (not_le.2 (key uL hSL))
  · exact absurd h (not_le.2 (key uR hSR))

/-- **The `1 + 1` seed path** (pathwise step of clause (a)): a local path of a word whose seed marks are `S_L`, `S_R`,
whose distant marks avoid the driver, together with a path `b'` that absorbs the distant drift, is a local path of the
`1 + 1` seed word (the chosen seed marks, weights the seed sums) driven by `b'`. -/
theorem _root_.InteractingSLE.Sec2.IsSLEPathUpTo.oneSeed (hp : IsSLEPathUpTo κ xL xR ρL ρR w vL vR b τ)
    (hxL : ∀ i, xL i = 0 ↔ i ∈ SL) (hxR : ∀ j, xR j = 0 ↔ j ∈ SR)
    (hsepL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ i, patWt SL ρL i ≠ ρL i → vL i t ≠ w t)
    (hsepR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ j, patWt SR ρR j ≠ ρR j → vR j t ≠ w t)
    (hSL : -2 < ∑ i ∈ SL, ρL i) (hSR : -2 < ∑ j ∈ SR, ρR j) {b' : ℝ≥0 → ℝ}
    (hb' : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      Real.sqrt κ * b' t = Real.sqrt κ * b t
        + (∑ i, ∫ s in (0 : ℝ)..t, (ρL i - patWt SL ρL i) / (w s.toNNReal - vL i s.toNNReal))
        + (∑ i, ∫ s in (0 : ℝ)..t, (ρR i - patWt SR ρR i) / (w s.toNNReal - vR i s.toNNReal))) :
    IsSLEPathUpTo κ (oneSeedY SL) (oneSeedY SR) (seedWtL (oneSeedY SL) (oneSeedWts SL ρL))
      (seedWtR (oneSeedY SR) (oneSeedWts SR ρR)) w (fun k => vL (oneSeedIdx SL k))
      (fun k => vR (oneSeedIdx SR k)) b' τ := by
  classical
  have hp' := hp.changeWeights (patWt SL ρL) (patWt SR ρR) hsepL hsepR hb'
  have hxi : ∀ k, xL (oneSeedIdx SL k) = 0 := fun k => (hxL _).2 (oneSeedIdx_mem SL k)
  have hxj : ∀ k, xR (oneSeedIdx SR k) = 0 := fun k => (hxR _).2 (oneSeedIdx_mem SR k)
  rw [seedWt_oneSeedY_L, seedWt_oneSeedY_R]
  refine ⟨hp.w_zero, fun k => by rw [hp.vL_zero, hxi k]; rfl, fun k => by rw [hp.vR_zero, hxj k]; rfl,
    hp.continuousOn_w, fun k => hp.continuousOn_vL _, fun k => hp.continuousOn_vR _,
    fun {t} _ k k' _ => by rw [fin_oneSeedCount_eq k k'], fun ht k => hp.vL_le_w ht _,
    fun ht k => hp.w_le_vR ht _, fun {t} _ k k' _ => by rw [fin_oneSeedCount_eq k k'],
    fun ht k => hp.integrable_gapL ht _, fun ht k => hp.integrable_gapR ht _, fun {t} ht => ?_,
    fun ht k => by rw [hp.vL_eq ht, hxi k]; rfl, fun ht k => by rw [hp.vR_eq ht, hxj k]; rfl,
    fun k => hp.volume_collisionL _, fun k => hp.volume_collisionR _,
    fun ht => thresholdCondition_oneSeed_false hSL hSR _ _ _⟩
  have hw := hp'.w_eq ht
  have hcoe : ∀ s ∈ Set.uIcc (0 : ℝ) t, (s.toNNReal : ℝ≥0∞) < τ := fun s hs => by
    rw [Set.uIcc_of_le t.coe_nonneg] at hs
    refine lt_of_le_of_lt ?_ ht
    exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2
  rw [sum_integral_patWt_eq ρL w vL t (fun h i hi s hs => vL_eq_vL_of_xL_eq_zero hp' ((hxL i).2 hi)
      ((hxL _).2 (SL.min'_mem h)) (hcoe s hs)),
    sum_integral_patWt_eq ρR w (fun j u => vR j u) t (fun h j hj s hs => ?_)] at hw
  · exact hw
  · exact vR_eq_vR_of_xR_eq_zero hp' ((hxR j).2 hj) ((hxR _).2 (SR.min'_mem h)) (hcoe s hs)

end OneSeed

/-! ### The coupling clause depends on the processes only almost surely -/

section Congr

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W W' : ℝ≥0 → Ω → ℝ} {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **The coupling clause for almost surely equal processes.** -/
theorem _root_.InteractingSLE.Coupling.MartMeans.IsCouplingCharFun.congr_ae
    (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h)
    (hEq : ∀ᵐ ω ∂P, (∀ t, W' t ω = W t ω) ∧ (∀ i t, VL' i t ω = VL i t ω) ∧ ∀ j t, VR' j t ω = VR j t ω) :
    Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W' VL' VR' ζ h := by
  classical
  intro τ hτ hτζ u hu φ
  set E : Set Ω := {ω | (∀ t, W' t ω = W t ω) ∧ (∀ i t, VL' i t ω = VL i t ω) ∧ ∀ j t, VR' j t ω = VR j t ω}
    with hEdef
  set u' : Ω → ℂ → ℝ := fun ω => if ω ∈ E then u ω else
    bheAt κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
      (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω) with hu'def
  have hu' : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u' ω) := fun ω => by
    by_cases hω : ω ∈ E
    · simp only [hu'def, hω, ↓reduceIte]
      have h1 := hu ω
      simp only [hω.1, hω.2.1, hω.2.2] at h1
      exact h1
    · simp only [hu'def, hω, ↓reduceIte]
      exact isBoundedHarmonicExtension_bheAt κ ρL ρR _ _
  filter_upwards [hcf τ hτ hτζ u' hu' φ, hEq] with ω h1 hω hdisj
  have hpath : (fun s : ℝ => W' s.toNNReal ω) = fun s : ℝ => W s.toNNReal ω := funext fun s => hω.1 _
  have hωE : ω ∈ E := hω
  rw [hpath] at hdisj ⊢
  have h2 := h1 hdisj
  simp only [hu'def, hωE, ↓reduceIte] at h2
  exact h2

end Congr

end LocalExt

end InteractingSLE
