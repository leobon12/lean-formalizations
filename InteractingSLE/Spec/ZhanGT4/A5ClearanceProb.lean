/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A5ClearanceState
import InteractingSLE.Spec.ZhanGT4.NoClusterRec

/-!
# Protected-ray clearance, V: the right gap eventually dominates its clock-weighted level

Packet PROVE-ZHAN-CLEAR. For the separated two-force law (`κ > 0`, marks `x_L < 0 < x_R`, weights `≥ κ/2 − 2`), write
`Z = V^R − W` and `s_t = ∫₀ᵗ Z⁻²`. **`ae_exists_clearTime`**: almost surely, for every `A ∈ ℕ` there is a time `t₀`
with `2A · exp(−(s_t − s_{t₀})/3) < Z_t` for all `t ≥ t₀`. This is the probabilistic input of the deterministic
clearance argument (`A5ClearanceGeom`).

## Proof (added here)

With `λ, q` from `exists_lyapunov` and `V = log Z + s/3 + q(v)`, the observable `Φ = e^{−λV}` of the state process
(`A5ClearanceState`) satisfies the hitting bound `measure_hit_after_le` at every deterministic time. Fix `A`, a level
`L` and a dyadic grid `2^{−j} ℕ`; decompose the event "`Z ≥ L` at some grid point" by the first such grid point
`q_i` and the integer part `k` of `V_{q_i}` (`F_{i,k} ∈ 𝓖_{q_i}`, disjoint). If the conclusion fails from `t₀ = q_i`,
then `V` drops below `V_{q_i} − m_L` after `q_i`, `m_L = log L − 2 sup|q| − log(2A + 1)`; each such event has probability
`≤ e^{λ(1 − m_L)} P(F_{i,k})` (`measure_iUnion_hit_le`). Refining the grid exhausts `{sup Z > L}`, which has full
probability because the gap ratio recurs (`ae_realRec_sep`) while `(V^R − V^L)² ≥ 8t`; finally `L → ∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A5Clear

open QuantumZipper Zhan

/-! ### A countable decomposition of the hitting bound -/

section Union

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}

/-- **Summing the hitting bound over disjoint events at deterministic times.** -/
theorem measure_iUnion_hit_le {Y : ℝ≥0 → Ω → ℝ}
    (hhit : ∀ (q : ℝ≥0) (A : Set Ω), MeasurableSet[𝓖 q] A → ∀ ℓ Lv : ℝ, 0 ≤ ℓ → 0 < Lv →
      (∀ ω ∈ A, Y q ω ≤ ℓ) → Lv * P.real (A ∩ {ω | ∃ t, q ≤ t ∧ Lv ≤ Y t ω}) ≤ ℓ * P.real A)
    {ι : Type*} [Countable ι] (qs : ι → ℝ≥0) (F : ι → Set Ω) (hF : ∀ i, MeasurableSet[𝓖 (qs i)] (F i))
    (hdisj : Pairwise (Function.onFun Disjoint F)) (ℓ Lv : ι → ℝ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hLv : ∀ i, 0 < Lv i)
    (hℓ : ∀ i, ∀ ω ∈ F i, Y (qs i) ω ≤ ℓ i) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ i, ℓ i ≤ c * Lv i) :
    P (⋃ i, F i ∩ {ω | ∃ t, qs i ≤ t ∧ Lv i ≤ Y t ω}) ≤ ENNReal.ofReal c := by
  have hFm : ∀ i, MeasurableSet (F i) := fun i => 𝓖.le _ _ (hF i)
  have hone : ∀ i, P (F i ∩ {ω | ∃ t, qs i ≤ t ∧ Lv i ≤ Y t ω}) ≤ ENNReal.ofReal c * P (F i) := by
    intro i
    have h := hhit (qs i) (F i) (hF i) (ℓ i) (Lv i) (hℓ0 i) (hLv i) (hℓ i)
    have h2 : P.real (F i ∩ {ω | ∃ t, qs i ≤ t ∧ Lv i ≤ Y t ω}) ≤ c * P.real (F i) := by
      have h3 : ℓ i * P.real (F i) ≤ c * Lv i * P.real (F i) :=
        mul_le_mul_of_nonneg_right (hc i) measureReal_nonneg
      have h4 := h.trans h3
      rw [mul_comm c, mul_assoc] at h4
      exact le_of_mul_le_mul_left h4 (hLv i)
    rw [← ofReal_measureReal, ← ofReal_measureReal, ← ENNReal.ofReal_mul hc0]
    exact ENNReal.ofReal_le_ofReal h2
  calc P (⋃ i, F i ∩ {ω | ∃ t, qs i ≤ t ∧ Lv i ≤ Y t ω})
      ≤ ∑' i, P (F i ∩ {ω | ∃ t, qs i ≤ t ∧ Lv i ≤ Y t ω}) := measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal c * P (F i) := ENNReal.tsum_le_tsum hone
    _ = ENNReal.ofReal c * P (⋃ i, F i) := by rw [ENNReal.tsum_mul_left, measure_iUnion hdisj hFm]
    _ ≤ ENNReal.ofReal c * 1 := by gcongr; exact prob_le_one
    _ = ENNReal.ofReal c := mul_one _

end Union

/-! ### Measurability along a path in an open set -/

theorem measurable_comp_of_continuousOn {Ω E : Type*} {m : MeasurableSpace Ω} [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ContinuousOn f U)
    {X : Ω → E} (hX : Measurable X) (hin : ∀ ω, X ω ∈ U) : Measurable fun ω => f (X ω) := by
  classical
  have hp := (hf.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hU.measurableSet).comp hX
  have heq : (fun ω => f (X ω)) = (U.piecewise f fun _ => (0 : ℝ)) ∘ X := by
    funext ω; simp only [Function.comp_apply, Set.piecewise_eq_of_mem _ _ _ (hin ω)]
  rw [heq]; exact hp

/-! ### The right gap is unbounded -/

section Gap

variable {κ : ℝ} {xL xR ρL ρR : Fin 1 → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The right gap `V^R − W` is unbounded**: at a late time where `R > rL` (gap-ratio recurrence,
`ae_realRec_sep`), `R > r(R + L)/(1 + r) ≥ r √(8t)/(1 + r)` (`eight_mul_le_sep_sq`). -/
theorem ae_exists_lt_gap [IsProbabilityMeasure P] (hκ : 0 < κ) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hwL : κ / 2 - 2 ≤ ρL 0) (hwR : κ / 2 - 2 ≤ ρR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ L : ℝ, ∃ t : ℝ≥0, L < VR 0 t ω - W t ω := by
  have hadm := hasAdmissiblePartialSums_one (xL := xL) (xR := xR) hwL hwR
  obtain ⟨G, -, hGc, hgood⟩ := exists_good_clr hκ hxL hxR hwL hwR hE
  filter_upwards [IsIntegratedSLEEvolution.ae_realRec_sep hκ hxL hxR hadm hE, (ae_iff.2 hGc : ∀ᵐ ω ∂P, ω ∈ G)] with ω hrec hωG L
  have h := hgood ω hωG
  set r : ℝ := xR 0 / (-xL 0) with hr
  have hr0 : 0 < r := div_pos hxR (by linarith)
  set M : ℝ := (|L| + 1) * (1 + r) / r with hM
  have hM0 : 0 < M := by positivity
  obtain ⟨t₁, t₂, -, hNt, -, hpos⟩ := hrec (M ^ 2 / 8).toNNReal
  refine ⟨t₂, ?_⟩
  have hp : IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) ⊤ := by
    rw [← h.2.1]; exact h.1
  have hsep := eight_mul_le_sep_sq hp (fun t => (h.2.2.1 t).1) (fun t => (h.2.2.1 t).2) t₂
  have hY : 0 < W t₂ ω - VL 0 t₂ ω := by linarith [(h.2.2.1 t₂).1]
  have hZ : 0 < VR 0 t₂ ω - W t₂ ω := by linarith [(h.2.2.1 t₂).2]
  simp only [rgap] at hpos
  -- `S = R + L ≥ M`
  have ht₂ : M ^ 2 / 8 ≤ (t₂ : ℝ) := by
    have := (Real.toNNReal_le_iff_le_coe).1 hNt
    exact this
  have hS : M ≤ VR 0 t₂ ω - VL 0 t₂ ω := by
    have h1 : M ^ 2 ≤ (VR 0 t₂ ω - VL 0 t₂ ω) ^ 2 := by linarith
    have h2 : 0 ≤ VR 0 t₂ ω - VL 0 t₂ ω := by linarith
    nlinarith [sq_nonneg (M - (VR 0 t₂ ω - VL 0 t₂ ω)), sq_nonneg (M + (VR 0 t₂ ω - VL 0 t₂ ω))]
  -- `(1 + r) R > r S ≥ r M = (|L| + 1)(1 + r)`
  have h3 : r * M = (|L| + 1) * (1 + r) := by rw [hM]; field_simp
  have h4 : (|L| + 1) * (1 + r) < (1 + r) * (VR 0 t₂ ω - W t₂ ω) := by nlinarith
  have h5 : |L| + 1 < VR 0 t₂ ω - W t₂ ω := by nlinarith
  linarith [le_abs_self L]

end Gap

/-! ### Dyadic grids -/

/-- The dyadic grid point `i/2^j`. -/
def gridPt (j i : ℕ) : ℝ≥0 := (i : ℝ≥0) / 2 ^ j

theorem gridPt_mono {j i i' : ℕ} (h : i ≤ i') : gridPt j i ≤ gridPt j i' := by
  unfold gridPt
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

theorem gridPt_succ (j i : ℕ) : gridPt (j + 1) (2 * i) = gridPt j i := by
  unfold gridPt
  rw [pow_succ]
  push_cast
  field_simp

/-- Every time is approached from the right by dyadic grid points. -/
theorem exists_gridPt_near (t : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ j i : ℕ, t ≤ gridPt j i ∧ (gridPt j i : ℝ) < t + δ := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨j, ⌈(t : ℝ) * 2 ^ j⌉₊, ?_, ?_⟩
  · have h2 : (0 : ℝ) < 2 ^ j := by positivity
    have h := Nat.le_ceil ((t : ℝ) * 2 ^ j)
    rw [← NNReal.coe_le_coe, gridPt, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_two,
      le_div_iff₀ h2]
    exact h
  · have h2 : (0 : ℝ) < 2 ^ j := by positivity
    have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (t : ℝ) * 2 ^ j)
    rw [gridPt, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_two, div_lt_iff₀ h2]
    have : (1 / 2 : ℝ) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
    nlinarith

/-! ### The main estimate -/

section Main

open scoped Classical

variable {κ : ℝ} {xL xR ρL ρR : Fin 1 → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The right gap eventually dominates its clock-weighted level** (added here). For the separated two-force law,
almost surely, for every `A ∈ ℕ` there is `t₀` with `2A exp(−(s_t − s_{t₀})/3) < V^R_t − W_t` for all `t ≥ t₀`,
`s_t = ∫₀ᵗ (V^R − W)⁻²`. -/
theorem ae_exists_clearTime [IsProbabilityMeasure P] (hκ : 0 < κ) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hwL : κ / 2 - 2 ≤ ρL 0) (hwR : κ / 2 - 2 ≤ ρR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ A : ℕ, ∃ t₀ : ℝ≥0, ∀ t, t₀ ≤ t →
      2 * (A : ℝ) * Real.exp (-(clrClock W VR t ω - clrClock W VR t₀ ω) / 3) < VR 0 t ω - W t ω := by
  obtain ⟨q, q1, q2, lam, Q, hlam, hQ0, hq, hq1, hq2, hqb, hineq⟩ := exists_lyapunov hκ hwL hwR
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_good_clr hκ hxL hxR hwL hwR hE
  obtain ⟨hB', hB'c⟩ := Ito.isFilteredBrownianReal_modify hE.1 hGm hGc fun ω hω => (hgood ω hω).2.2.2.1
  set 𝓖 := Ito.nullAugmented 𝓕 P with h𝓖
  have hG0 : MeasurableSet[𝓖 0] G := by
    have := (Ito.measurableSet_nullAugmented_of_null (𝓕 := 𝓕) hGm.compl hGc 0).compl
    rwa [compl_compl] at this
  have hB0 : ∀ ω, clockBrown G B 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [clockBrown, hω, ↓reduceIte]; exact (hgood ω hω).2.2.2.2
    · simp [clockBrown, hω]
  set X := pathX (clrState κ G xL xR W VL VR B ζ) (clockBrown G B) with hX
  have hin : ∀ ω t, X t ω ∈ clrRegion κ := fun ω t => clrState_mem_region hgood hxL hxR ω t
  have hXm : ∀ t, Measurable[𝓖 t] (X t) := fun t =>
    (measurable_clrState hE hgood hGm hGc t).prodMk (hB'.2.1 t)
  have hXc : ∀ ω, Continuous fun t => X t ω :=
    continuous_pathX (continuous_clrState hgood hxR) hB'c
  have hp₀ : ((clrInit xL xR, 0) : CE × ℝ) ∈ clrRegion κ := by
    refine ⟨?_, ?_⟩ <;> simp only [zC, yC, clrInit, mul_zero, sub_zero, zero_add] <;> linarith
  -- the hitting bound for the Lyapunov observable
  have hhit : ∀ (q₀ : ℝ≥0) (A : Set Ω), MeasurableSet[𝓖 q₀] A → ∀ ℓ Lv : ℝ, 0 ≤ ℓ → 0 < Lv →
      (∀ ω ∈ A, lyapObs κ lam q (X q₀ ω) ≤ ℓ) →
      Lv * P.real (A ∩ {ω | ∃ t, q₀ ≤ t ∧ Lv ≤ lyapObs κ lam q (X t ω)}) ≤ ℓ * P.real A := by
    intro q₀ A hA ℓ Lv hℓ0 hLv hℓ
    exact measure_hit_after_le hB' hB'c (isOpen_clrRegion κ) (contDiffOn_lyapObs κ (hq 3) lam)
      (fun p _ => (lyapObs_pos κ lam p).le) (continuousOn_clrField κ (ρL 0) (ρR 0))
      (fun ω _ t => itoGen_lyapObs_nonpos κ hκ.le hlam.le (hq 2) hq1 hq2 hineq (hin ω t))
      (measurable_clrState hE hgood hGm hGc) (continuous_clrState hgood hxR) hG0 hGc
      (clrState_zero hgood) hB0 (fun ω hω t => clrState_eq_integral hgood hω t) hin
      ⟨((0, 0, 0, 0), 0), by simp [clrRegion, zC]⟩ hp₀ hA hℓ0 hLv hℓ
  -- the gap and the Lyapunov function along the path
  set Zf : ℝ≥0 → Ω → ℝ := fun t ω => zC κ (X t ω) with hZf
  set Vf : ℝ≥0 → Ω → ℝ := fun t ω => lyapV κ q (X t ω) with hVf
  have hVcont : ContinuousOn (lyapV κ q) (clrRegion κ) := fun p hp =>
    (contDiffAt_lyapV κ (hq 0) hp).continuousAt.continuousWithinAt
  have hZm : ∀ t, Measurable[𝓖 t] (Zf t) := fun t => (continuous_zC κ).measurable.comp (hXm t)
  have hVm : ∀ t, Measurable[𝓖 t] (Vf t) := fun t =>
    measurable_comp_of_continuousOn (isOpen_clrRegion κ) hVcont (hXm t) fun ω => hin ω t
  have hZfG : ∀ ω ∈ G, ∀ t, Zf t ω = VR 0 t ω - W t ω := fun ω hω t => zC_clrState hω (hgood ω hω) t
  have hVfG : ∀ ω ∈ G, ∀ t, Vf t ω = Real.log (Zf t ω) + clrClock W VR t ω / 3 + q (vC κ (X t ω)) :=
    fun ω hω t => by
      simp only [hVf, lyapV]
      rw [sC_clrState hω (hgood ω hω) t]
  have hqX : ∀ ω t, |q (vC κ (X t ω))| ≤ Q := by
    intro ω t
    refine hqb _ ⟨?_, ?_⟩
    · exact div_nonneg (hin ω t).2.le (dC_pos κ (hin ω t)).le
    · rw [vC, div_le_one (dC_pos κ (hin ω t)), ← yC_add_zC]; linarith [(hin ω t).1]
  have hZc : ∀ ω, Continuous fun t => Zf t ω := fun ω => (continuous_zC κ).comp (hXc ω)
  have hgap := ae_exists_lt_gap hκ hxL hxR hwL hwR hE
  -- the bad event for a fixed `A`
  have hbad : ∀ A : ℕ, P {ω | ω ∈ G ∧ ¬ ∃ t₀ : ℝ≥0, ∀ t, t₀ ≤ t →
      2 * (A : ℝ) * Real.exp (-(clrClock W VR t ω - clrClock W VR t₀ ω) / 3) < VR 0 t ω - W t ω} = 0 := by
    intro A
    set bad := {ω | ω ∈ G ∧ ¬ ∃ t₀ : ℝ≥0, ∀ t, t₀ ≤ t →
      2 * (A : ℝ) * Real.exp (-(clrClock W VR t ω - clrClock W VR t₀ ω) / 3) < VR 0 t ω - W t ω} with hbad_def
    have hL : ∀ L : ℕ, 1 ≤ L →
        P bad ≤ ENNReal.ofReal (Real.exp (lam * (1 - (Real.log L - 2 * Q - Real.log (2 * A + 1))))) := by
      intro L hL1
      set m := Real.log L - 2 * Q - Real.log (2 * A + 1) with hm
      set c := Real.exp (lam * (1 - m)) with hc
      set E : ℕ → Set Ω := fun j => {ω | ∃ i : ℕ, (L : ℝ) ≤ Zf (gridPt j i) ω} with hE_def
      have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast hL1
      -- the bound on each grid
      have hEj : ∀ j, P (bad ∩ E j) ≤ ENNReal.ofReal c := by
        intro j
        set F : ℕ × ℤ → Set Ω := fun ik => {ω | (L : ℝ) ≤ Zf (gridPt j ik.1) ω ∧
          (∀ i' < ik.1, Zf (gridPt j i') ω < L) ∧ (ik.2 : ℝ) ≤ Vf (gridPt j ik.1) ω ∧
            Vf (gridPt j ik.1) ω < ik.2 + 1} with hFdef
        have hF : ∀ ik : ℕ × ℤ, MeasurableSet[𝓖 (gridPt j ik.1)] (F ik) := by
          intro ik
          have h1 : MeasurableSet[𝓖 (gridPt j ik.1)] {ω | (L : ℝ) ≤ Zf (gridPt j ik.1) ω} :=
            measurableSet_le measurable_const (hZm _)
          have h2 : MeasurableSet[𝓖 (gridPt j ik.1)] {ω | ∀ i' < ik.1, Zf (gridPt j i') ω < L} := by
            rw [Set.ofPred_forall]
            refine MeasurableSet.iInter fun i' => ?_
            by_cases hi' : i' < ik.1
            · simp only [hi', true_imp_iff]
              exact 𝓖.mono (gridPt_mono hi'.le) _ (measurableSet_lt (hZm _) measurable_const)
            · simp only [hi', false_imp_iff, Set.ofPred_true]
              exact MeasurableSet.univ
          have h3 : MeasurableSet[𝓖 (gridPt j ik.1)] {ω | (ik.2 : ℝ) ≤ Vf (gridPt j ik.1) ω} :=
            measurableSet_le measurable_const (hVm _)
          have h4 : MeasurableSet[𝓖 (gridPt j ik.1)] {ω | Vf (gridPt j ik.1) ω < ik.2 + 1} :=
            measurableSet_lt (hVm _) measurable_const
          exact h1.inter (h2.inter (h3.inter h4))
        have hdisj : Pairwise (Function.onFun Disjoint F) := by
          rintro ⟨i, k⟩ ⟨i', k'⟩ hne
          rw [Function.onFun, Set.disjoint_left]
          rintro ω ⟨hZ, hmin, hk1, hk2⟩ ⟨hZ', hmin', hk1', hk2'⟩
          rcases lt_trichotomy i i' with h | h | h
          · exact absurd hZ (not_le.2 (hmin' i h))
          · subst h
            have h1 : (k : ℝ) < k' + 1 := lt_of_le_of_lt hk1 hk2'
            have h2 : (k' : ℝ) < k + 1 := lt_of_le_of_lt hk1' hk2
            have h1' : k < k' + 1 := by exact_mod_cast h1
            have h2' : k' < k + 1 := by exact_mod_cast h2
            have hkk : k = k' := by omega
            exact hne (by rw [hkk])
          · exact absurd hZ' (not_le.2 (hmin i' h))
        refine (measure_mono ?_).trans (measure_iUnion_hit_le (𝓖 := 𝓖)
          (Y := fun t ω => lyapObs κ lam q (X t ω)) hhit (fun ik : ℕ × ℤ => gridPt j ik.1) F hF hdisj
          (fun ik => Real.exp (-(lam * ik.2))) (fun ik => Real.exp (-(lam * (ik.2 + 1 - m))))
          (fun _ => (Real.exp_pos _).le) (fun _ => Real.exp_pos _) ?_ (Real.exp_pos _).le ?_)
        · rintro ω ⟨⟨hωG, hng⟩, hωE⟩
          push Not at hng
          have hspec : (L : ℝ) ≤ Zf (gridPt j (Nat.find hωE)) ω := Nat.find_spec hωE
          have hmin : ∀ i' < Nat.find hωE, Zf (gridPt j i') ω < L := fun i' hi' =>
            not_le.1 (Nat.find_min hωE hi')
          set i₀ := Nat.find hωE with hi₀
          set t₀ := gridPt j i₀ with ht₀
          set k₀ : ℤ := ⌊Vf t₀ ω⌋ with hk₀
          obtain ⟨t, ht, hle⟩ := hng t₀
          refine mem_iUnion.2 ⟨(i₀, k₀), ⟨hspec, hmin, Int.floor_le _, Int.lt_floor_add_one _⟩, t, ht, ?_⟩
          show Real.exp (-(lam * (k₀ + 1 - m))) ≤ Real.exp (-(lam * Vf t ω))
          refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ hlam.le))
          have hZt : 0 < Zf t ω := (hin ω t).1
          have hZt' : Zf t ω ≤ 2 * A * Real.exp (-(clrClock W VR t ω - clrClock W VR t₀ ω) / 3) := by
            rw [hZfG ω hωG]; exact hle
          have hexp := Real.exp_pos (-(clrClock W VR t ω - clrClock W VR t₀ ω) / 3)
          have hA0 : 0 < 2 * (A : ℝ) := by
            by_contra h
            push Not at h
            nlinarith
          have hlog1 : Real.log (Zf t ω) ≤
              Real.log (2 * A + 1) - (clrClock W VR t ω - clrClock W VR t₀ ω) / 3 := by
            have h1 := Real.log_le_log hZt hZt'
            rw [Real.log_mul hA0.ne' hexp.ne', Real.log_exp] at h1
            have h2 : Real.log (2 * A) ≤ Real.log (2 * A + 1) := Real.log_le_log hA0 (by linarith)
            linarith
          have hlog2 : Real.log L ≤ Real.log (Zf t₀ ω) := Real.log_le_log (by linarith) hspec
          have hq1' := (abs_le.1 (hqX ω t)).2
          have hq2' := (abs_le.1 (hqX ω t₀)).1
          have hV1 := hVfG ω hωG t
          have hV0 := hVfG ω hωG t₀
          have hfl : Vf t₀ ω < k₀ + 1 := Int.lt_floor_add_one _
          rw [hm]
          linarith
        · rintro ik ω ⟨-, -, hk, -⟩
          show Real.exp (-(lam * Vf (gridPt j ik.1) ω)) ≤ Real.exp (-(lam * ik.2))
          exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hk hlam.le))
        · intro ik
          rw [hc, ← Real.exp_add]
          exact le_of_eq (by congr 1; ring)
      -- the grids increase
      have hEmono : Monotone fun j => bad ∩ E j := by
        refine monotone_nat_of_le_succ fun j => ?_
        rintro ω ⟨hb, i, hi⟩
        exact ⟨hb, 2 * i, by rw [gridPt_succ]; exact hi⟩
      -- they exhaust the bad event up to a null set
      have hcover : bad ⊆ (⋃ j, bad ∩ E j) ∪ {ω | ¬ ∀ L' : ℝ, ∃ t : ℝ≥0, L' < VR 0 t ω - W t ω} := by
        intro ω hb
        by_cases hω : ∀ L' : ℝ, ∃ t : ℝ≥0, L' < VR 0 t ω - W t ω
        · left
          obtain ⟨t, ht⟩ := hω L
          have hZt : (L : ℝ) < Zf t ω := by rw [hZfG ω hb.1]; exact ht
          obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
            ((hZc ω).continuousAt.eventually (lt_mem_nhds hZt))
          obtain ⟨j, i, hti, hti'⟩ := exists_gridPt_near t hε
          refine mem_iUnion.2 ⟨j, hb, i, (hball ?_).le⟩
          rw [NNReal.dist_eq, abs_lt]
          have : (t : ℝ) ≤ gridPt j i := by exact_mod_cast hti
          constructor <;> linarith
        · right; exact hω
      calc P bad ≤ P ((⋃ j, bad ∩ E j) ∪ {ω | ¬ ∀ L' : ℝ, ∃ t : ℝ≥0, L' < VR 0 t ω - W t ω}) :=
            measure_mono hcover
        _ ≤ P (⋃ j, bad ∩ E j) + P {ω | ¬ ∀ L' : ℝ, ∃ t : ℝ≥0, L' < VR 0 t ω - W t ω} :=
            measure_union_le _ _
        _ = P (⋃ j, bad ∩ E j) := by rw [ae_iff.1 hgap, add_zero]
        _ = ⨆ j, P (bad ∩ E j) := hEmono.measure_iUnion
        _ ≤ ENNReal.ofReal c := iSup_le hEj
    -- let `L → ∞`
    have hlim : Tendsto (fun L : ℕ => ENNReal.ofReal
        (Real.exp (lam * (1 - (Real.log L - 2 * Q - Real.log (2 * A + 1)))))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun L : ℕ => Real.log L) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun L : ℕ => lam * (1 - (Real.log L - 2 * Q - Real.log (2 * A + 1)))) atTop atBot := by
        have h3 : Tendsto (fun L : ℕ => -(lam * Real.log L) + lam * (1 + 2 * Q + Real.log (2 * A + 1))) atTop
            atBot := tendsto_atBot_add_const_right _ _ (tendsto_neg_atTop_atBot.comp (h1.const_mul_atTop hlam))
        refine h3.congr fun L => ?_
        ring
      have h4 := ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp h2)
      simpa using h4
    exact le_zero_iff.1 (ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hL⟩))
  -- conclude
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGc
  rw [ae_all_iff]
  intro A
  have hae : ∀ᵐ ω ∂P, ω ∈ G → ∃ t₀ : ℝ≥0, ∀ t, t₀ ≤ t →
      2 * (A : ℝ) * Real.exp (-(clrClock W VR t ω - clrClock W VR t₀ ω) / 3) < VR 0 t ω - W t ω := by
    rw [ae_iff]
    simpa only [not_imp] using hbad A
  filter_upwards [hae, hGae] with ω h1 h2 using h1 h2

end Main

end InteractingSLE.ZhanGT4.A5Clear
