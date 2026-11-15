/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedK2Clause
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# The stopped K2, part 4: a process frozen after its stop

Packet PROVE-STOPPEDK2. A coupling through a stop `V` only constrains its coordinates on `[0, V]`. The clause at
`τ = V` concerns the hull `K_V`, which depends on the driver slightly after `V` (`QuantumZipper.fwdHull` is defined
through forward solutions on `[0, T]`, `T > V`). Freezing the coordinates after `V` makes the driver continuous on all
of `ℝ≥0`, so that the hull results proved for stopping times before a lifetime (lifetime `⊤`) apply at `τ ≤ V`:

* `dyBelow k v`: the dyadic time `(⌈2ᵏ v⌉ − 1)/2ᵏ`, strictly below `v ∈ (0, ∞)` and converging to it;
* **`frz V Y`**: `Y` before `V`, and from `V` on the limit of `Y` killed at `V` along `dyBelow k V`;
* `frz_eq_min`: with `Y` continuous on `[0, V]` (finite, positive `V`), `frz V Y t = Y (min t V)`;
  `continuous_frz`: the frozen path is continuous;
* **`measurable_frz`**: if `Y` is adapted before `V` to a filtration, the frozen process is adapted at every time (the
  limit at `V` is read from the killed values at the dyadic times below `V`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.StoppedK2

open Sec7.Aux122Disint (killAt measurable_killAt_of_adaptedBefore)

/-! ### Dyadic times below a time -/

/-- The index `⌈2ᵏ v⌉ − 1` of the dyadic time below `v`. -/
def dyIdx (k : ℕ) (v : ℝ≥0∞) : ℕ := ⌈(2 : ℝ) ^ k * v.toReal⌉₊ - 1

/-- The dyadic time `(⌈2ᵏ v⌉ − 1)/2ᵏ` below `v`. -/
def dyBelow (k : ℕ) (v : ℝ≥0∞) : ℝ≥0 := (dyIdx k v : ℝ≥0) / 2 ^ k

theorem measurable_dyIdx (k : ℕ) : Measurable (dyIdx k) :=
  ((measurable_const.mul ENNReal.measurable_toReal).nat_ceil).sub_const 1

theorem coe_dyBelow (k : ℕ) (v : ℝ≥0∞) : ((dyBelow k v : ℝ≥0) : ℝ) = (dyIdx k v : ℝ) / 2 ^ k := by
  simp [dyBelow]

/-- `2ᵏ v − 1 ≤ ⌈2ᵏ v⌉ − 1 ≤ 2ᵏ v`, and `< 2ᵏ v` when `v > 0`. -/
theorem dyIdx_bounds (k : ℕ) (v : ℝ≥0∞) :
    (2 : ℝ) ^ k * v.toReal - 1 ≤ dyIdx k v ∧ (dyIdx k v : ℝ) ≤ (2 : ℝ) ^ k * v.toReal ∧
      (0 < v.toReal → (dyIdx k v : ℝ) < (2 : ℝ) ^ k * v.toReal) := by
  set x : ℝ := (2 : ℝ) ^ k * v.toReal with hx
  have hx0 : 0 ≤ x := mul_nonneg (pow_nonneg zero_le_two k) ENNReal.toReal_nonneg
  have hc1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hc2 : x ≤ ⌈x⌉₊ := Nat.le_ceil x
  rcases Nat.eq_zero_or_pos ⌈x⌉₊ with h0 | hpos
  · have hx00 : x = 0 := le_antisymm (by simpa [h0] using hc2) hx0
    have : dyIdx k v = 0 := by simp only [dyIdx, ← hx, h0, Nat.zero_sub]
    rw [this, Nat.cast_zero]
    refine ⟨by linarith, hx0, fun hv => ?_⟩
    exact absurd hx00 (mul_pos (pow_pos two_pos k) hv).ne'
  · have e : (dyIdx k v : ℝ) = (⌈x⌉₊ : ℝ) - 1 := by
      simp only [dyIdx, ← hx]
      rw [Nat.cast_sub hpos, Nat.cast_one]
    rw [e]
    exact ⟨by linarith, by linarith, fun _ => by linarith⟩

theorem coe_dyBelow_le (k : ℕ) (v : ℝ≥0∞) : ((dyBelow k v : ℝ≥0) : ℝ) ≤ v.toReal := by
  rw [coe_dyBelow, div_le_iff₀ (pow_pos two_pos k), mul_comm]
  exact (dyIdx_bounds k v).2.1

theorem coe_dyBelow_lt (k : ℕ) {v : ℝ≥0∞} (hv : 0 < v.toReal) : ((dyBelow k v : ℝ≥0) : ℝ) < v.toReal := by
  rw [coe_dyBelow, div_lt_iff₀ (pow_pos two_pos k), mul_comm]
  exact (dyIdx_bounds k v).2.2 hv

/-- For `0 < v < ∞`, the dyadic times below `v` are strictly below `v`. -/
theorem dyBelow_lt {k : ℕ} {v : ℝ≥0∞} (hv0 : 0 < v) (hvt : v ≠ ⊤) : ((dyBelow k v : ℝ≥0) : ℝ≥0∞) < v := by
  have hpos : 0 < v.toReal := ENNReal.toReal_pos hv0.ne' hvt
  calc ((dyBelow k v : ℝ≥0) : ℝ≥0∞) < (v.toNNReal : ℝ≥0∞) := ENNReal.coe_lt_coe.2 (by
        rw [← NNReal.coe_lt_coe, ENNReal.coe_toNNReal_eq_toReal]; exact coe_dyBelow_lt k hpos)
    _ = v := ENNReal.coe_toNNReal hvt

theorem dyBelow_le_toNNReal (k : ℕ) (v : ℝ≥0∞) : dyBelow k v ≤ v.toNNReal := by
  rw [← NNReal.coe_le_coe, ENNReal.coe_toNNReal_eq_toReal]
  exact coe_dyBelow_le k v

/-- The dyadic times below `v` converge to `v`. -/
theorem tendsto_dyBelow (v : ℝ≥0∞) : Tendsto (fun k => dyBelow k v) atTop (𝓝 v.toNNReal) := by
  rw [← NNReal.tendsto_coe, ENNReal.coe_toNNReal_eq_toReal]
  have h2 : Tendsto (fun k : ℕ => v.toReal - 1 / (2 : ℝ) ^ k) atTop (𝓝 v.toReal) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_sub
      v.toReal
    simpa [one_div, inv_pow] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h2 tendsto_const_nhds (fun k => ?_) (fun k => coe_dyBelow_le k v)
  rw [coe_dyBelow, le_div_iff₀ (pow_pos two_pos k), sub_mul, one_div,
    inv_mul_cancel₀ (pow_pos two_pos k).ne', mul_comm]
  exact (dyIdx_bounds k v).1

/-! ### The frozen process -/

section Frz

variable {Ω : Type*}

/-- **`Y` frozen at `V`**: `Y t` for `t < V`, and from `V` on the limit of `Y` killed at `V` along the dyadic times
below `V`. -/
def frz (V : Ω → ℝ≥0∞) (Y : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω =>
  if (t : ℝ≥0∞) < V ω then Y t ω else limUnder atTop fun k => killAt V Y (dyBelow k (V ω)) ω

theorem frz_of_lt {V : Ω → ℝ≥0∞} {Y : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {ω : Ω} (h : (t : ℝ≥0∞) < V ω) :
    frz V Y t ω = Y t ω := by
  simp [frz, h]

/-- **The frozen path at a finite positive stop**: if `Y` is continuous on `[0, V]`, `frz V Y t = Y (min t V)`. -/
theorem frz_eq_min {V : Ω → ℝ≥0∞} {Y : ℝ≥0 → Ω → ℝ} {ω : Ω} (hV0 : 0 < V ω) (hVt : V ω ≠ ⊤)
    (hc : ContinuousOn (Y · ω) (Iic (V ω).toNNReal)) (t : ℝ≥0) : frz V Y t ω = Y (min t (V ω).toNNReal) ω := by
  set a := (V ω).toNNReal with ha
  have hVa : V ω = (a : ℝ≥0∞) := (ENNReal.coe_toNNReal hVt).symm
  by_cases ht : (t : ℝ≥0∞) < V ω
  · rw [frz_of_lt ht, min_eq_left (by rw [hVa] at ht; exact_mod_cast ht.le)]
  · simp only [frz, ht, ↓reduceIte]
    rw [min_eq_right (by rw [hVa, not_lt] at ht; exact_mod_cast ht)]
    have hk : ∀ k, killAt V Y (dyBelow k (V ω)) ω = Y (dyBelow k (V ω)) ω := fun k => by
      simp [killAt, dyBelow_lt hV0 hVt]
    simp_rw [hk]
    refine Tendsto.limUnder_eq ?_
    have hlim : Tendsto (fun k => dyBelow k (V ω)) atTop (𝓝[Iic a] a) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_dyBelow (V ω), Eventually.of_forall fun k => dyBelow_le_toNNReal k _⟩
    exact (hc a self_mem_Iic).tendsto.comp hlim

/-- The frozen path is continuous (finite positive stop, `Y` continuous on `[0, V]`). -/
theorem continuous_frz {V : Ω → ℝ≥0∞} {Y : ℝ≥0 → Ω → ℝ} {ω : Ω} (hV0 : 0 < V ω) (hVt : V ω ≠ ⊤)
    (hc : ContinuousOn (Y · ω) (Iic (V ω).toNNReal)) : Continuous (frz V Y · ω) := by
  have e : (frz V Y · ω) = (Y · ω) ∘ fun t => min t (V ω).toNNReal := funext fun t => frz_eq_min hV0 hVt hc t
  rw [e]
  exact hc.comp_continuous (continuous_id.min continuous_const) fun t => mem_Iic.2 (min_le_right _ _)

/-- At an infinite stop the frozen path is the path. -/
theorem frz_of_eq_top {V : Ω → ℝ≥0∞} {Y : ℝ≥0 → Ω → ℝ} {ω : Ω} (hVt : V ω = ⊤) (t : ℝ≥0) :
    frz V Y t ω = Y t ω :=
  frz_of_lt (by rw [hVt]; exact ENNReal.coe_lt_top)

variable [mΩ : MeasurableSpace Ω]

/-- **The frozen process is adapted at every time** to a filtration in which `Y` is adapted before `V`. -/
theorem measurable_frz {𝓚 : Filtration ℝ≥0 mΩ} {V : Ω → ℝ≥0∞} {Y : ℝ≥0 → Ω → ℝ} (hY : AdaptedBefore 𝓚 V Y)
    (t : ℝ≥0) : Measurable[𝓚 t] (frz V Y t) := by
  have hle : ∀ s : ℝ≥0, MeasurableSet[𝓚 s] {ω | V ω ≤ s} := fun s => by
    have := (hY s univ MeasurableSet.univ).compl
    convert this using 1
    ext ω
    simp
  -- `min V t` is `𝓚 t`-measurable
  have hmin : Measurable[𝓚 t] fun ω => min (V ω) (t : ℝ≥0∞) := by
    refine measurable_of_Iic (mδ := 𝓚 t) fun x => ?_
    by_cases hx : (t : ℝ≥0∞) ≤ x
    · convert @MeasurableSet.univ _ (𝓚 t)
      ext ω
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (min_le_right _ _).trans hx
    · push Not at hx
      have hxt : x ≠ ⊤ := ne_top_of_lt hx
      have e : (fun ω => min (V ω) (t : ℝ≥0∞)) ⁻¹' Iic x = {ω | V ω ≤ (x.toNNReal : ℝ≥0∞)} := by
        ext ω
        simp only [mem_preimage, mem_Iic, mem_ofPred_eq, ENNReal.coe_toNNReal hxt]
        constructor
        · intro h
          rcases le_total (V ω) t with h' | h'
          · rwa [min_eq_left h'] at h
          · rw [min_eq_right h'] at h; exact absurd h (not_le.2 hx)
        · intro h; exact (min_le_left _ _).trans h
      rw [e]
      exact 𝓚.mono (by rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hxt]; exact hx.le) _ (hle _)
  have hidx : ∀ k, Measurable[𝓚 t] fun ω => dyIdx k (min (V ω) (t : ℝ≥0∞)) := fun k =>
    (measurable_dyIdx k).comp hmin
  -- the killed values at the dyadic times below `V`, on `{V ≤ t}`
  set g : ℕ → Ω → ℝ := fun k ω => if V ω ≤ t then killAt V Y (dyBelow k (V ω)) ω else 0 with hg
  have hgm : ∀ k, Measurable[𝓚 t] (g k) := by
    intro k A hA
    have e : g k ⁻¹' A = ({ω | V ω ≤ t}ᶜ ∩ {_ω | (0 : ℝ) ∈ A}) ∪
        ⋃ j : ℕ, ({ω | V ω ≤ t} ∩ {ω | dyIdx k (min (V ω) (t : ℝ≥0∞)) = j} ∩
          {ω | (j : ℝ≥0) / 2 ^ k ≤ t ∧ killAt V Y ((j : ℝ≥0) / 2 ^ k) ω ∈ A}) := by
      ext ω
      simp only [hg, mem_preimage, mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, mem_iUnion]
      by_cases hVt : V ω ≤ t
      · simp only [hVt, ↓reduceIte, not_true_eq_false, false_and, false_or, true_and, min_eq_left hVt]
        constructor
        · intro h
          refine ⟨dyIdx k (V ω), rfl, ?_, h⟩
          have h1 : dyBelow k (V ω) ≤ (V ω).toNNReal := dyBelow_le_toNNReal k _
          have h2 : (V ω).toNNReal ≤ t := by
            rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top hVt)]
            exact hVt
          exact h1.trans h2
        · rintro ⟨j, hj, -, h⟩
          rw [← hj] at h
          exact h
      · simp only [hVt, ↓reduceIte, not_false_eq_true, true_and, false_and, exists_false, or_false]
    rw [e]
    refine MeasurableSet.union ((hle t).compl.inter ?_) (MeasurableSet.iUnion fun j => ?_)
    · by_cases h0 : (0 : ℝ) ∈ A
      · simp only [h0, ofPred_true]; exact @MeasurableSet.univ _ (𝓚 t)
      · simp only [h0, ofPred_false]; exact @MeasurableSet.empty _ (𝓚 t)
    · refine ((hle t).inter (hidx k (measurableSet_singleton j))).inter ?_
      by_cases hj : (j : ℝ≥0) / 2 ^ k ≤ t
      · simp only [hj, true_and]
        exact 𝓚.mono hj _ (measurable_killAt_of_adaptedBefore hY _ hA)
      · simp only [hj, false_and, ofPred_false]; exact @MeasurableSet.empty _ (𝓚 t)
  have hL : StronglyMeasurable[𝓚 t] fun ω => limUnder atTop fun k => g k ω :=
    @StronglyMeasurable.limUnder ℕ Ω ℝ (𝓚 t) _ _ atTop _ g _ _ fun k => (hgm k).stronglyMeasurable
  intro A hA
  have e : frz V Y t ⁻¹' A = ({ω | (t : ℝ≥0∞) < V ω} ∩ killAt V Y t ⁻¹' A) ∪
      ({ω | (t : ℝ≥0∞) < V ω}ᶜ ∩ (fun ω => limUnder atTop fun k => g k ω) ⁻¹' A) := by
    ext ω
    simp only [frz, mem_preimage, mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
    by_cases h : (t : ℝ≥0∞) < V ω
    · simp [h, killAt]
    · have hV : V ω ≤ t := not_lt.1 h
      simp only [h, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or, hg, hV]
  rw [e]
  have hlt : MeasurableSet[𝓚 t] {ω | (t : ℝ≥0∞) < V ω} := by
    have := (hle t).compl
    convert this using 1
    ext ω
    simp
  exact (hlt.inter (measurable_killAt_of_adaptedBefore hY t hA)).union (hlt.compl.inter (hL.measurable hA))

/-- The frozen process is adapted before `⊤`. -/
theorem adaptedBefore_frz {𝓚 : Filtration ℝ≥0 mΩ} {V : Ω → ℝ≥0∞} {Y : ℝ≥0 → Ω → ℝ} (hY : AdaptedBefore 𝓚 V Y) :
    AdaptedBefore 𝓚 (fun _ => ⊤) (frz V Y) := fun t A hA => by
  have e : {ω | (t : ℝ≥0∞) < (⊤ : ℝ≥0∞) ∧ frz V Y t ω ∈ A} = frz V Y t ⁻¹' A := by
    ext ω
    simp
  rw [e]
  exact measurable_frz hY t hA

end Frz

end InteractingSLE.Restart.StoppedK2
