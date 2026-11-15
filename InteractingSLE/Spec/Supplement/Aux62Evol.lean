/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux62Compare
import InteractingSLE.Spec.Sec2.CriticalLifetime
import InteractingSLE.Spec.Ito.FiltrationBasic

/-!
# Aux. lemma 62 for integrated SLE evolutions: the cumulative-weight comparison

Packet PROVE-GB7A2. The Girsanov comparison `measure_eq_zero_of_cmp` specialized to an integrated `SLE_κ(ρ)`
evolution (Definition 2.1) and the comparison weights of Aux. lemma 64: weight `S` on a right mark `k` and `−S` on a
later right mark `k₂` (if any), all other weights `0`. If `κ ≤ 4` and `S ≥ κ/2 − 2`, the gap `V_k − W` is repelled
(`β = (2 + S)/Y − S/(V_{k₂} − W) ≥ κ/(2Y)`), so (`measure_eq_zero_of_evolution`) almost surely `V_k` does not collide
with the driver at a time `T > q` before which, after `q`, the marks of nonzero old or new weight stay off the driver
with bounded drift energy.

The comparison runs in the usual augmentation of the filtration, with the lifetime set to `0` off an augmented null
set, so that the paths are continuous on `[0, ζ)` for every `ω`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace GB7a

open Girsanov Sec2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}

/-- The comparison weights on the right: `S` at `k`, `−S` at `k₂`. -/
def refWeightR (k : Fin nR) (k2 : Option (Fin nR)) (S : ℝ) (j : Fin nR) : ℝ :=
  (if j = k then S else 0) - (if k2 = some j then S else 0)

theorem allMarks_castAdd (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (i : Fin nL) :
    allMarks VL VR (Fin.castAdd nR i) = VL i := by
  simp [allMarks]

theorem allMarks_natAdd (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (j : Fin nR) :
    allMarks VL VR (Fin.natAdd nL j) = VR j := by
  simp [allMarks]

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- An integrated path with its threshold limit is a comparison path for all marks. -/
theorem cmpPath_of_isIntegratedSLEPath {ω : Ω} {ζ₀ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) ζ₀)
    (hthr : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ₀ →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) :
    CmpPath κ (Fin.append ρL ρR) (W · ω) (B · ω) (fun j t => allMarks VL VR j t ω) ζ₀ := by
  have hq := hp.isSLEPathUpTo le_rfl
  refine ⟨fun ht j => ?_, fun ht => ?_, fun ht j => ?_, fun T hT hTζ => ?_⟩
  · cases j using Fin.addCases with
    | left i => simpa [allMarks_castAdd] using hq.integrable_gapL ht i
    | right i => simpa [allMarks_natAdd] using hq.integrable_gapR ht i
  · rw [hq.w_eq ht, Fin.sum_univ_add, add_assoc]
    simp [allMarks_castAdd, allMarks_natAdd]
  · cases j using Fin.addCases with
    | left i =>
      simp only [allMarks_castAdd]
      rw [hq.vL_eq ht i, hq.vL_zero i]
    | right i =>
      simp only [allMarks_natAdd]
      rw [hq.vR_eq ht i, hq.vR_zero i]
  · obtain ⟨w₀, vL₀, vR₀, hlim, hth⟩ := hthr T hT hTζ
    have hw : Tendsto (fun t => W t ω) (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
    have hL : ∀ i, Tendsto (fun t => VL i t ω) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
      ((continuous_apply i).tendsto _).comp ((continuous_fst.tendsto _).comp
        ((continuous_snd.tendsto _).comp hlim))
    have hR : ∀ i, Tendsto (fun t => VR i t ω) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
      ((continuous_apply i).tendsto _).comp ((continuous_snd.tendsto _).comp
        ((continuous_snd.tendsto _).comp hlim))
    rcases hth with h | h
    · obtain ⟨i, hi, hρ⟩ : ∃ i, vL₀ i = w₀ ∧ ρL i ≠ 0 := by
        by_contra hno
        push Not at hno
        have : (∑ i ∈ Finset.univ.filter (fun i => vL₀ i = w₀), ρL i) = 0 :=
          Finset.sum_eq_zero fun i hi => hno i (Finset.mem_filter.1 hi).2
        linarith
      refine ⟨Fin.castAdd nR i, by simpa using hρ, ?_⟩
      have := hw.sub (hL i)
      rw [hi, sub_self] at this
      simpa [allMarks_castAdd] using this
    · obtain ⟨i, hi, hρ⟩ : ∃ i, vR₀ i = w₀ ∧ ρR i ≠ 0 := by
        by_contra hno
        push Not at hno
        have : (∑ i ∈ Finset.univ.filter (fun i => vR₀ i = w₀), ρR i) = 0 :=
          Finset.sum_eq_zero fun i hi => hno i (Finset.mem_filter.1 hi).2
        linarith
      refine ⟨Fin.natAdd nL i, by simpa using hρ, ?_⟩
      have := hw.sub (hR i)
      rw [hi, sub_self] at this
      simpa [allMarks_natAdd] using this

/-- **The repulsion of the comparison weights** (pointwise): for `κ ≤ 4`, `S ≥ κ/2 − 2`, right marks ordered and
right of the driver, with `V_k ≠ W`, the gap drift is at least `κ/(2(V_k − W))`. -/
theorem refWeight_drift_ge (hκ4 : κ ≤ 4) {S : ℝ} (hS : κ / 2 - 2 ≤ S) {k : Fin nR} {k2 : Option (Fin nR)}
    (hk2 : ∀ j, k2 = some j → k < j) {w : ℝ} {vR : Fin nR → ℝ} (hmono : Monotone vR)
    (hle : ∀ j, w ≤ vR j) (hne : w ≠ vR k) :
    0 < vR k - w ∧ κ / (2 * (vR k - w)) ≤
      2 / (vR k - w) - ∑ j, refWeightR k k2 S j / (w - vR j) := by
  have hY : 0 < vR k - w := sub_pos.2 (lt_of_le_of_ne (hle k) hne)
  refine ⟨hY, ?_⟩
  set Y := vR k - w with hYdef
  have hsum : ∑ j, refWeightR k k2 S j / (w - vR j) =
      -(S / Y) - ∑ j, (if k2 = some j then S else 0) / (w - vR j) := by
    simp only [refWeightR, sub_div, Finset.sum_sub_distrib, ite_div, zero_div, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    rw [hYdef, show S / (w - vR k) = -(S / (vR k - w)) by rw [← neg_sub, div_neg]]
  rw [hsum]
  have hκY : κ / (2 * Y) ≤ 2 / Y + S / Y + (if S < 0 then 0 else -(S / Y)) := by
    split_ifs with hS0
    · rw [add_zero, ← add_div, div_le_div_iff₀ (by positivity) hY]
      nlinarith
    · rw [add_neg_cancel_right, div_le_div_iff₀ (by positivity) hY]
      nlinarith
  cases k2 with
  | none =>
    simp only [reduceCtorEq, ↓reduceIte, zero_div, Finset.sum_const_zero, sub_zero, sub_neg_eq_add]
    split_ifs at hκY with hS0
    · linarith
    · have : 0 ≤ S / Y := div_nonneg (not_lt.1 hS0) hY.le
      linarith
  | some j₂ =>
    have hj : k < j₂ := hk2 j₂ rfl
    have hZ : Y ≤ vR j₂ - w := by
      rw [hYdef]
      linarith [hmono hj.le]
    have hZpos : 0 < vR j₂ - w := hY.trans_le hZ
    simp only [Option.some.injEq, ite_div, zero_div, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [show S / (w - vR j₂) = -(S / (vR j₂ - w)) by rw [← neg_sub, div_neg]]
    split_ifs at hκY with hS0
    · have : S / (vR j₂ - w) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hS0.le hZpos.le
      linarith
    · have : S / (vR j₂ - w) ≤ S / Y := div_le_div_of_nonneg_left (not_lt.1 hS0) hY hZ
      linarith

/-! ### The comparison for an integrated evolution -/

variable {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}

/-- Killing the lifetime off a set of `𝓖₀` preserves adaptedness before the lifetime. -/
theorem adaptedBefore_ite_lifetime {𝓖 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓖 ζ X)
    {G : Set Ω} [DecidablePred (· ∈ G)] (hG : MeasurableSet[𝓖 0] G) :
    AdaptedBefore 𝓖 (fun ω => if ω ∈ G then ζ ω else 0) X := by
  intro t A hA
  have e : {ω | (t : ℝ≥0∞) < (if ω ∈ G then ζ ω else 0) ∧ X t ω ∈ A} =
      G ∩ {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} := by
    ext ω
    by_cases hω : ω ∈ G <;> simp [hω]
  rw [e]
  exact (𝓖.mono bot_le _ hG).inter (hX t A hA)

theorem continuousOn_ite_lifetime {X : ℝ≥0 → ℝ} {G : Set Ω} [DecidablePred (· ∈ G)] {ω : Ω}
    (h : ω ∈ G → ContinuousOn X {t | (t : ℝ≥0∞) < ζ ω}) :
    ContinuousOn X {t | (t : ℝ≥0∞) < (if ω ∈ G then ζ ω else 0)} := by
  by_cases hω : ω ∈ G
  · simpa [hω] using h hω
  · simp [hω]

/-- **Aux. lemma 62–64's comparison for an integrated `SLE_κ(ρ)` evolution** (`κ ≤ 4`, `S ≥ κ/2 − 2`): almost
surely there is no time `T > q` such that, on `[q, T)`, the marks of nonzero old or comparison weight (and `k`)
stay off the driver with bounded drift energy, while the gap `V_k − W` tends to `0` at `T`. -/
theorem measure_eq_zero_of_evolution {P : Measure Ω} [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {k : Fin nR} {k2 : Option (Fin nR)} (hk2 : ∀ j, k2 = some j → k < j) {S : ℝ} (hS : κ / 2 - 2 ≤ S)
    (q : ℝ≥0) {A : Set Ω}
    (hA : ∀ ω ∈ A, ∃ T : ℝ≥0, q < T ∧ (T : ℝ≥0∞) ≤ ζ ω ∧
      (∀ t : ℝ≥0, q ≤ t → t < T → (∀ i, ρL i ≠ 0 → W t ω ≠ VL i t ω) ∧
        ∀ j, (ρR j ≠ 0 ∨ refWeightR k k2 S j ≠ 0 ∨ j = k) → W t ω ≠ VR j t ω) ∧
      (∃ C : ℝ, ∀ t : ℝ≥0, q ≤ t → t < T →
        (∫ s in (q : ℝ)..t, ((∑ i, -ρL i / (W s.toNNReal ω - VL i s.toNNReal ω)) +
          ∑ j, (refWeightR k k2 S j - ρR j) / (W s.toNNReal ω - VR j s.toNNReal ω)) ^ 2) ≤ C) ∧
      Tendsto (fun t => VR k t ω - W t ω) (𝓝[<] T) (𝓝 0)) :
    P A = 0 := by
  classical
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  -- the good set
  have hgood : ∀ᵐ ω ∂P, IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (B · ω) (ζ ω) ∧ ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
        ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
          Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
          ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ :=
    hE.2.2.2.2.and (hE.ae_tendsto_threshold hκ)
  set N := toMeasurable P {ω | ¬ (IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (B · ω) (ζ ω) ∧ ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
        ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
          Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
          ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)} with hNdef
  have hN0 : P N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 hgood
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hG𝓖 : MeasurableSet[𝓖 0] Nᶜ := (Ito.measurableSet_usualAugmentation_of_null hNm hN0 0).compl
  have hgoodG : ∀ ω ∈ Nᶜ, _ := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P _ h)
  have haeG : ∀ᵐ ω ∂P, ω ∈ Nᶜ := compl_mem_ae_iff.2 hN0
  set ζ' : Ω → ℝ≥0∞ := fun ω => if ω ∈ Nᶜ then ζ ω else 0 with hζ'
  set ρa : Fin (nL + nR) → ℝ := Fin.append ρL ρR with hρa
  set ρb : Fin (nL + nR) → ℝ := Fin.append (fun _ => 0) (refWeightR k k2 S) with hρb
  set k' : Fin (nL + nR) := Fin.natAdd nL k with hk'
  -- the generic hypotheses
  have hB' : IsFilteredBrownianReal 𝓖 B P := hE𝓖.1
  have hW' : AdaptedBefore 𝓖 ζ' W := adaptedBefore_ite_lifetime hE𝓖.2.1 hG𝓖
  have hU' : ∀ j, AdaptedBefore 𝓖 ζ' (allMarks VL VR j) := fun j => by
    cases j using Fin.addCases with
    | left i => rw [allMarks_castAdd]; exact adaptedBefore_ite_lifetime (hE𝓖.2.2.1 i) hG𝓖
    | right i => rw [allMarks_natAdd]; exact adaptedBefore_ite_lifetime (hE𝓖.2.2.2.1 i) hG𝓖
  have hWc' : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ' ω} := fun ω =>
    continuousOn_ite_lifetime fun hω => ((hgoodG ω hω).1.isSLEPathUpTo le_rfl).continuousOn_w
  have hUc' : ∀ j ω, ContinuousOn (allMarks VL VR j · ω) {t | (t : ℝ≥0∞) < ζ' ω} := fun j ω => by
    cases j using Fin.addCases with
    | left i =>
      rw [allMarks_castAdd]
      exact continuousOn_ite_lifetime fun hω => ((hgoodG ω hω).1.isSLEPathUpTo le_rfl).continuousOn_vL i
    | right i =>
      rw [allMarks_natAdd]
      exact continuousOn_ite_lifetime fun hω => ((hgoodG ω hω).1.isSLEPathUpTo le_rfl).continuousOn_vR i
  have hζ'G : ∀ ω ∈ Nᶜ, ζ' ω = ζ ω := fun ω hω => by simp only [hζ', hω, ↓reduceIte]
  have hpath' : ∀ᵐ ω ∂P, CmpPath κ ρa (W · ω) (B · ω) (fun j t => allMarks VL VR j t ω) (ζ' ω) := by
    filter_upwards [haeG] with ω hω
    rw [hζ'G ω hω]
    exact cmpPath_of_isIntegratedSLEPath (hgoodG ω hω).1 (hgoodG ω hω).2
  have hsumb : ∀ (w : ℝ) (u : Fin (nL + nR) → ℝ), ∑ j, ρb j / (w - u j) =
      ∑ j, refWeightR k k2 S j / (w - u (Fin.natAdd nL j)) := fun w u => by
    rw [Fin.sum_univ_add]
    simp [hρb]
  have hdrift' : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ω →
      (∀ j, IsMon ρa ρb k' j → W t ω ≠ allMarks VL VR j t ω) →
      0 < allMarks VL VR k' t ω - W t ω ∧ κ / (2 * (allMarks VL VR k' t ω - W t ω)) ≤
        cmpBeta ρb k' (W · ω) (fun j t => allMarks VL VR j t ω) t := by
    filter_upwards [haeG] with ω hω t ht hne
    rw [hζ'G ω hω] at ht
    have hp := (hgoodG ω hω).1.isSLEPathUpTo le_rfl
    have hk := hne k' (Or.inr (Or.inr rfl))
    rw [hk', allMarks_natAdd] at hk
    simp only [cmpBeta, hk', allMarks_natAdd]
    rw [hsumb]
    simp only [allMarks_natAdd]
    exact refWeight_drift_ge hκ4 hS hk2 (hp.monotone_vR ht) (hp.w_le_vR ht) hk
  have hA' : ∀ ω ∈ A ∩ Nᶜ, ∃ T : ℝ≥0, q < T ∧ (T : ℝ≥0∞) ≤ ζ' ω ∧
      (∀ t : ℝ≥0, q ≤ t → t < T → ∀ j, IsMon ρa ρb k' j → W t ω ≠ allMarks VL VR j t ω) ∧
      (∃ C : ℝ, ∀ t : ℝ≥0, q ≤ t → t < T →
        (∫ s in (q : ℝ)..t, (∑ j, (ρb j - ρa j) / (W s.toNNReal ω - allMarks VL VR j s.toNNReal ω)) ^ 2) ≤ C) ∧
      Tendsto (fun t => allMarks VL VR k' t ω - W t ω) (𝓝[<] T) (𝓝 0) := by
    intro ω ⟨hωA, hωG⟩
    obtain ⟨T, hqT, hTζ, hgap, ⟨C, hC⟩, hlim⟩ := hA ω hωA
    refine ⟨T, hqT, by rw [hζ'G ω hωG]; exact hTζ, fun t hqt htT j hj => ?_, ⟨C, fun t hqt htT => ?_⟩, ?_⟩
    · cases j using Fin.addCases with
      | left i =>
        rw [allMarks_castAdd]
        refine (hgap t hqt htT).1 i ?_
        rcases hj with h | h | h
        · simpa [hρa] using h
        · simp [hρb] at h
        · exfalso
          have := congrArg Fin.val h
          simp only [hk', Fin.val_castAdd, Fin.val_natAdd] at this
          omega
      | right i =>
        rw [allMarks_natAdd]
        refine (hgap t hqt htT).2 i ?_
        rcases hj with h | h | h
        · exact Or.inl (by simpa [hρa] using h)
        · exact Or.inr (Or.inl (by simpa [hρb] using h))
        · exact Or.inr (Or.inr ((Fin.natAdd_inj nL).1 h))
    · convert hC t hqt htT using 4
      rw [Fin.sum_univ_add]
      simp [hρa, hρb, allMarks_castAdd, allMarks_natAdd, neg_div]
    · simpa [hk', allMarks_natAdd] using hlim
  have h0 := measure_eq_zero_of_cmp (P' := P) (𝓖 := 𝓖) (ζ := ζ') (W := W) (U := allMarks VL VR) (B := B)
    (ρ := ρa) (ρ' := ρb) (k := k') hκ hB' hW' hU' hWc' hUc' hpath' hdrift' q hA'
  refine measure_mono_null (fun ω hω => ?_) (measure_union_null h0 hN0)
  by_cases hωG : ω ∈ Nᶜ
  · exact Or.inl ⟨hω, hωG⟩
  · exact Or.inr (not_not.1 hωG)

end GB7a

end InteractingSLE
