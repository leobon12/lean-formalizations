/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12RemPassiveGlue

/-!
# A passive zero-weight mark at a real point: the adapted process

Packet PROVE-G12B. The passive mark of `G12RemPassiveGlue.lean` as a process on the probability space, adapted
before the lifetime exactly (no augmentation, ruling R15 Q2), in the manner of `Sec2.AddMarksFlow`:

* `passCut y ζ W n = Sec2.markFlow (Sec2.rightMarkDrift δ_n) y ζ W`: the cut flows (each `𝓕_t`-measurable);
* `passAliveSet`: "alive at level `n` at time `t`" tested at the rational times of `[0, t]` and at `t` (an
  `𝓕_t`-measurable event), with `mem_passAliveSet_iff`: on a path along which `W` is continuous it is
  `IsAliveAt`;
* `passMark y ζ W V`: the passive mark, glued to `V` (the mark below `y`) after the life of `y`;
  `adaptedBefore_passMark`; `passMark_eq_path`: on such a path it is `passMarkPath` before `ζ`;
* `markFlow_eq_of_solution`: uniqueness of the cut equation (the Euler scheme converges to every continuous
  solution, `Sec2.tendsto_eulerAt`), and `passHyp_of_continuousOn`: the cut flows of a continuous path satisfy
  `PassHyp`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {y : ℝ}

/-- **Uniqueness of the cut equation.** On `[0, t₁]`, `t₁ < ζ(ω)`, along a path where `W` is continuous, every
continuous solution of `u = y + ∫ F(u − W)` is the mark `Sec2.markFlow F y ζ W`. -/
theorem markFlow_eq_of_solution {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) {ω : Ω}
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) {t₁ : ℝ≥0} (ht₁ : (t₁ : ℝ≥0∞) < ζ ω)
    (u : ℝ → ℝ) (huc : ContinuousOn u (Icc 0 (t₁ : ℝ)))
    (hu : ∀ s ∈ Icc (0 : ℝ) t₁, u s = y + ∫ r in (0 : ℝ)..s, F (u r - W r.toNNReal ω)) :
    ∀ s ∈ Icc (0 : ℝ) t₁, Sec2.markFlow F y ζ W s.toNNReal ω = u s := by
  intro s hs
  have hmaps : MapsTo Real.toNNReal (Icc (0 : ℝ) s) {r : ℝ≥0 | (r : ℝ≥0∞) < ζ ω} := fun r hr =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 (hr.2.trans hs.2))) ht₁
  have hwc : ContinuousOn (fun r : ℝ => W r.toNNReal ω) (Icc 0 s) :=
    hWc.comp continuous_real_toNNReal.continuousOn hmaps
  have hT := Sec2.tendsto_eulerAt (y := y) (t := s) hF hs.1 hwc
    (huc.mono (Icc_subset_Icc le_rfl hs.2)) (fun r hr => hu r ⟨hr.1, hr.2.trans hs.2⟩)
    (wk := fun n k => Girsanov.killed ζ W (Girsanov.grid n k) ω) fun n k hk => by
      have hgk : ((Girsanov.grid n k : ℝ≥0) : ℝ) = k / 2 ^ n := Girsanov.coe_grid n k
      have hle : Girsanov.grid n k ≤ t₁ := by
        rw [← NNReal.coe_le_coe, hgk]; exact hk.trans hs.2
      rw [Girsanov.killed_of_lt (lt_of_le_of_lt (by exact_mod_cast hle) ht₁)]
      congr 1
      rw [← hgk, Real.toNNReal_coe]
  unfold Sec2.markFlow Sec2.markEuler
  rw [Real.coe_toNNReal _ hs.1]
  exact hT.limsup_eq

/-- The cut flows of `y` at the levels `δ_n`. -/
def passCut (y : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  Sec2.markFlow (Sec2.rightMarkDrift (passDelta n)) y ζ W

/-- **The cut flows of a continuous path satisfy `PassHyp`.** -/
theorem passHyp_of_continuousOn (hy : 0 < y) {ω : Ω} (hW0 : W 0 ω = 0)
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) :
    PassHyp (fun s => W s ω) (ζ ω) y (fun n t => passCut y ζ W n t ω) where
  y_pos := hy
  w_zero := hW0
  cont_w := hWc
  cont_U n := (Sec2.markFlow_eq_of_continuousOn (Sec2.lipschitzWith_rightMarkDrift (passDelta_pos n))
    (Sec2.abs_rightMarkDrift_le (passDelta_pos n)) hWc).1
  zero_U _ := Sec2.markFlow_zero _ _ _ _ _
  eq_U n _ ht := (Sec2.markFlow_eq_of_continuousOn (Sec2.lipschitzWith_rightMarkDrift (passDelta_pos n))
    (Sec2.abs_rightMarkDrift_le (passDelta_pos n)) hWc).2 _ ht
  uniq_U n _ ht₁ u huc hu := markFlow_eq_of_solution (Sec2.lipschitzWith_rightMarkDrift (passDelta_pos n)) hWc ht₁
    u huc hu

/-- The event "alive at level `n` at time `t`", tested at `t` and at the rational times of `[0, t]` (with the killed
driver). -/
def passAliveSet (y : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) : Set Ω :=
  {ω | 2 * passDelta n ≤ passCut y ζ W n t ω - Girsanov.killed ζ W t ω} ∩
    ⋂ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ t),
      {ω | 2 * passDelta n ≤ passCut y ζ W n (q : ℝ).toNNReal ω - Girsanov.killed ζ W (q : ℝ).toNNReal ω}

theorem measurableSet_passAliveSet (hW : AdaptedBefore 𝓕 ζ W) (n : ℕ) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] (passAliveSet y ζ W n t) := by
  have hm : ∀ s ≤ t, Measurable[𝓕 t] fun ω => passCut y ζ W n s ω - Girsanov.killed ζ W s ω := fun s hs =>
    ((Sec2.measurable_markFlow (Sec2.lipschitzWith_rightMarkDrift
      (passDelta_pos n)).continuous.measurable hW s).mono (𝓕.mono hs) le_rfl).sub
      ((Girsanov.measurable_killed hW s).mono (𝓕.mono hs) le_rfl)
  refine (measurableSet_le measurable_const (hm t le_rfl)).inter (MeasurableSet.iInter fun q =>
    MeasurableSet.iInter fun hq => measurableSet_le measurable_const (hm _ ?_))
  exact Real.toNNReal_le_iff_le_coe.2 hq.2

/-- **On a continuous path, the tested event is `IsAliveAt`** (for `t < ζ(ω)`). -/
theorem mem_passAliveSet_iff (hy : 0 < y) {ω : Ω} (hW0 : W 0 ω = 0)
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) {n : ℕ} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ ω) :
    ω ∈ passAliveSet y ζ W n t ↔ IsAliveAt (fun s => W s ω) (ζ ω) (fun n t => passCut y ζ W n t ω) n t := by
  have hH := passHyp_of_continuousOn hy hW0 hWc
  have hk : ∀ s ≤ t, Girsanov.killed ζ W s ω = W s ω := fun s hs =>
    Girsanov.killed_of_lt (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) ht)
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Set.mem_ofPred_eq, hk t le_rfl] at h1
    refine ⟨ht, fun s hs => ?_⟩
    rcases hs.lt_or_eq with hst | rfl
    · -- approximate `s` by rational times in `(s, t)`
      by_contra hlt
      push Not at hlt
      have hopen : IsOpen {r : ℝ≥0 | (r : ℝ≥0∞) < ζ ω} := isOpen_lt ENNReal.continuous_coe continuous_const
      have hc : ContinuousAt (fun r => passCut y ζ W n r ω - W r ω) s :=
        ((hH.cont_U n).sub hWc).continuousAt (hopen.mem_nhds (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) ht))
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (gt_mem_nhds hlt))
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (show (s : ℝ) < s + ε by linarith)
        (show (s : ℝ) < t from hst))
      have hq0 : 0 ≤ (q : ℝ) := s.coe_nonneg.trans hq1.le
      have hqt : (q : ℝ) ≤ t := hq2.le.trans (min_le_right _ _)
      have h := Set.mem_iInter₂.1 h2 q ⟨hq0, hqt⟩
      simp only [Set.mem_ofPred_eq, hk _ (Real.toNNReal_le_iff_le_coe.2 hqt)] at h
      have hd : dist (q : ℝ).toNNReal s < ε := by
        rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_of_pos (by linarith)]
        linarith [min_le_left ((s : ℝ) + ε) t]
      linarith [hball hd]
    · exact h1
  · intro ha
    refine ⟨?_, Set.mem_iInter₂.2 fun q hq => ?_⟩
    · simp only [Set.mem_ofPred_eq, hk t le_rfl]; exact ha.2 t le_rfl
    · have hqt := Real.toNNReal_le_iff_le_coe.2 hq.2
      simp only [Set.mem_ofPred_eq, hk _ hqt]; exact ha.2 _ hqt

open Classical in
/-- **The passive mark at `y`**: the flow of `y` (the limit of the cut flows) at time `0` and while `y` is alive, the
process `V` (the mark below `y`) afterwards. -/
def passMark (y : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (V : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if t = 0 ∨ ω ∈ ⋃ n, passAliveSet y ζ W n t then limsup (fun n => passCut y ζ W n t ω) atTop else V t ω

/-- **The passive mark is adapted before the lifetime.** -/
theorem adaptedBefore_passMark (hW : AdaptedBefore 𝓕 ζ W) {V : ℝ≥0 → Ω → ℝ} (hV : AdaptedBefore 𝓕 ζ V) :
    AdaptedBefore 𝓕 ζ (passMark y ζ W V) := by
  classical
  intro t A hA
  set S : Set Ω := {ω | t = 0 ∨ ω ∈ ⋃ n, passAliveSet y ζ W n t} with hS
  have hSm : MeasurableSet[𝓕 t] S :=
    (MeasurableSet.const (t = 0)).union (MeasurableSet.iUnion fun n => measurableSet_passAliveSet hW n t)
  have hζm : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    have := hW t univ MeasurableSet.univ
    simpa using this
  have hL : Measurable[𝓕 t] fun ω => limsup (fun n => passCut y ζ W n t ω) atTop :=
    @Sec2.measurable_limsup_aux Ω (𝓕 t) _ fun n => Sec2.measurable_markFlow
      (Sec2.lipschitzWith_rightMarkDrift (passDelta_pos n)).continuous.measurable hW t
  have e : {ω | (t : ℝ≥0∞) < ζ ω ∧ passMark y ζ W V t ω ∈ A} =
      (S ∩ {ω | (t : ℝ≥0∞) < ζ ω} ∩ (fun ω => limsup (fun n => passCut y ζ W n t ω) atTop) ⁻¹' A) ∪
        (Sᶜ ∩ {ω | (t : ℝ≥0∞) < ζ ω ∧ V t ω ∈ A}) := by
    ext ω
    by_cases hω : ω ∈ S
    · have hω' : t = 0 ∨ ω ∈ ⋃ n, passAliveSet y ζ W n t := hω
      have hv : passMark y ζ W V t ω = limsup (fun n => passCut y ζ W n t ω) atTop := by
        unfold passMark; exact ite_eq_left hω'
      simp only [Set.mem_ofPred_eq, hv, Set.mem_union, Set.mem_inter_iff, hω, true_and, Set.mem_preimage,
        Set.mem_compl_iff, not_true_eq_false, false_and, or_false]
    · have hω' : ¬ (t = 0 ∨ ω ∈ ⋃ n, passAliveSet y ζ W n t) := hω
      have hv : passMark y ζ W V t ω = V t ω := by
        unfold passMark; exact ite_eq_right hω'
      simp only [Set.mem_ofPred_eq, hv, Set.mem_union, Set.mem_inter_iff, hω, false_and, Set.mem_compl_iff,
        not_false_eq_true, true_and, false_or]
  rw [e]
  exact ((hSm.inter hζm).inter (hL hA)).union (hSm.compl.inter (hV t A hA))

/-- **On a continuous path, the passive mark is `passMarkPath` before `ζ`.** -/
theorem passMark_eq_path (hy : 0 < y) {V : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW0 : W 0 ω = 0)
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ ω) :
    passMark y ζ W V t ω =
      passMarkPath (fun s => W s ω) (ζ ω) (fun n t => passCut y ζ W n t ω) (fun s => V s ω) t := by
  have hiff : (t = 0 ∨ ω ∈ ⋃ n, passAliveSet y ζ W n t) ↔
      (t = 0 ∨ Alive (fun s => W s ω) (ζ ω) (fun n t => passCut y ζ W n t ω) t) := by
    rw [Set.mem_iUnion]
    exact or_congr Iff.rfl (exists_congr fun n => mem_passAliveSet_iff hy hW0 hWc ht)
  classical
  unfold passMark passMarkPath pflow
  by_cases h : t = 0 ∨ ω ∈ ⋃ n, passAliveSet y ζ W n t
  · rw [ite_eq_left h, ite_eq_left (hiff.1 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.2 h'))]

/-- The passive mark starts at `y` (for every `ω`). -/
theorem passMark_zero {V : ℝ≥0 → Ω → ℝ} (ω : Ω) : passMark y ζ W V 0 ω = y := by
  classical
  simp only [passMark, true_or, ↓reduceIte]
  simp only [passCut, Sec2.markFlow_zero]
  exact limsup_const y

end G12

end Supp7

end InteractingSLE
