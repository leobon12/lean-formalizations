/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.YuanCorollary13
import InteractingSLE.Foundations.Loewner.YuanShift
import InteractingSLE.Foundations.SLE.All
import InteractingSLE.Spec.ZhanGT4.TwoForceRecur

/-!
# §7.3: traces of restarted drivers, both directions of the pullback at infinity

Packet PROVE-SEC7-C6. Specification p. 355 (Aux. lemma 106): "A continuous Loewner trace remains a continuous trace
under its own mapping-out operation by Corollary 1.3 of [Yua22]. Its future is transient because a hydrodynamically
normalized mapping-out map fixes infinity. […] Pull this trace back through the inverse hydrodynamic map of the
actual finite prefix […]. It joins the future continuously and transfers its terminal limit at infinity."

* `exists_isGeneratingTrace_shiftNN_of_isGeneratingTrace`: if `w` (continuous, `w 0 = 0`) has a continuous
  generating trace on `[0, ∞)`, so does the restarted driver `shiftNN w σ` for every `σ ≥ 0` ([Yua22] Corollary 1.3,
  `IsLoewnerTrace.isLoewnerTrace_shift`, read through the frozen `IsGeneratingTrace`).
* `tendsto_norm_of_shiftNN_tendsto`: if the restarted trace tends to `∞`, so does the original one (the join
  `IsGeneratingTraceIcc.join` and uniqueness of the trace). The converse is ZhanGT4's `tendsto_norm_of_shift`.
* `exists_rat_lt_sep`: before an infinite lifetime, a path of a word with one mark on each side has a positive
  rational time at which the driver is strictly between the two marks (the collision sets are Lebesgue-null).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Positive

open QuantumZipper.RS (shiftDrive)

/-! ### Mapping out a prefix of a trace ([Yua22] Corollary 1.3) -/

/-- **[Yua22] Corollary 1.3 for the frozen generating trace**: if a continuous driver `w` with `w 0 = 0` has a
continuous generating trace on `[0, ∞)`, then so does the restarted driver `shiftNN w σ`, for every `σ`. -/
theorem exists_isGeneratingTrace_shiftNN_of_isGeneratingTrace {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) (σ : ℝ≥0) :
    ∃ η₂ : ℝ≥0 → ℂ, IsGeneratingTrace (shiftNN w σ) ⊤ η₂ := by
  have hW : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [hw0]
  have hS := (isLoewnerTrace_of_isGeneratingTrace hη).isLoewnerTrace_shift hW hW0 σ.2
  have hS' : IsLoewnerTrace (fun s : ℝ => shiftNN w σ s.toNNReal)
      (loewnerTip (shiftDrive (fun s : ℝ => w s.toNNReal) σ)) := by
    refine (isLoewnerTrace_congr_drive fun t ht => ?_).1 hS
    have h1 : ((σ : ℝ) + t).toNNReal = σ + t.toNNReal := by
      have : (σ : ℝ) + t = ((σ + t.toNNReal : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_add, Real.coe_toNNReal _ ht]
      rw [this, Real.toNNReal_coe]
    show w ((σ : ℝ) + t).toNNReal - w (σ : ℝ).toNNReal = w (σ + t.toNNReal) - w σ
    rw [h1, Real.toNNReal_coe]
  exact ⟨_, IsLoewnerTrace.isGeneratingTrace hS'⟩

/-! ### Pullback at infinity -/

/-- **Transience of the restarted trace gives transience of the original one**: `η(σ + s) = F̄_σ(η₂(s))` (the join of
the prefix on `[0, σ]` with the restarted trace is a generating trace on `[0, ∞)`, so it is `η`), and the join of a
transient future is transient. -/
theorem tendsto_norm_of_shiftNN_tendsto {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {σ : ℝ≥0} {η₂ : ℝ≥0 → ℂ} (hη₂ : IsGeneratingTrace (shiftNN w σ) ⊤ η₂)
    (htr : Tendsto (fun t => ‖η₂ t‖) atTop atTop) : Tendsto (fun t => ‖η t‖) atTop atTop := by
  have hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ⊤} := hw.continuousOn
  have h₁ := IsGeneratingTrace.isGeneratingTraceIcc hη hwc hw0 (σ := σ) ENNReal.coe_lt_top
  have hwc' : ContinuousOn w {s | (s : ℝ≥0∞) < (σ : ℝ≥0∞) + ⊤} := by rw [add_top]; exact hwc
  obtain ⟨hJ, hJt⟩ := h₁.join hwc' hw0 hη₂
  rw [add_top] at hJ
  refine (hJt rfl htr).congr fun t => ?_
  rw [hη.eq_of_le hJ hwc hw0 le_top]

/-- **Transience through a restart**: if `w` has a generating trace on `[0, ∞)` and the restarted driver at some `σ`
has a transient one, then every generating trace of `w` on `[0, ∞)` is transient. -/
theorem tendsto_norm_of_hasTransTrace_shiftNN {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {σ : ℝ≥0}
    (h : ZhanGT4.HasTransTrace (shiftNN w σ)) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) :
    Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain ⟨η₂, hη₂, htr⟩ := h
  exact tendsto_norm_of_shiftNN_tendsto hw hw0 hη hη₂ htr

/-! ### A rational time with the driver strictly between the marks -/

/-- **A positive rational time strictly between the marks.** For continuous `w`, `v_L ≤ w ≤ v_R` on `[0, ∞)` whose
collision sets `{w = v_L}`, `{w = v_R}` are Lebesgue-null, there is a rational `q > 0` with
`v_L(q) < w(q) < v_R(q)`. -/
theorem exists_rat_lt_sep {w vL vR : ℝ≥0 → ℝ} (hw : Continuous w) (hvL : Continuous vL) (hvR : Continuous vR)
    (hlw : ∀ t, vL t ≤ w t) (hwr : ∀ t, w t ≤ vR t)
    (hcL : volume {s : ℝ | 0 ≤ s ∧ w s.toNNReal = vL s.toNNReal} = 0)
    (hcR : volume {s : ℝ | 0 ≤ s ∧ w s.toNNReal = vR s.toNNReal} = 0) :
    ∃ q : ℚ, 0 < q ∧ vL (q : ℝ).toNNReal < w (q : ℝ).toNNReal ∧ w (q : ℝ).toNNReal < vR (q : ℝ).toNNReal := by
  set U : Set ℝ := {s | vL s.toNNReal < w s.toNNReal ∧ w s.toNNReal < vR s.toNNReal} with hU
  have hUo : IsOpen U := by
    have h1 := hw.comp continuous_real_toNNReal
    have h2 := hvL.comp continuous_real_toNNReal
    have h3 := hvR.comp continuous_real_toNNReal
    exact (isOpen_lt h2 h1).inter (isOpen_lt h1 h3)
  -- a point of `(0, 1)` off both collision sets
  obtain ⟨s, hs, hsU⟩ : ∃ s ∈ Ioo (0 : ℝ) 1, s ∈ U := by
    by_contra hall
    push Not at hall
    have hsub : Ioo (0 : ℝ) 1 ⊆ {s : ℝ | 0 ≤ s ∧ w s.toNNReal = vL s.toNNReal} ∪
        {s : ℝ | 0 ≤ s ∧ w s.toNNReal = vR s.toNNReal} := by
      intro s hs
      have hn := hall s hs
      simp only [hU, mem_ofPred_eq, not_and_or, not_lt] at hn
      rcases hn with h | h
      · exact Or.inl ⟨hs.1.le, le_antisymm h (hlw _)⟩
      · exact Or.inr ⟨hs.1.le, le_antisymm (hwr _) h⟩
    have h0 := measure_mono_null hsub (measure_union_null hcL hcR)
    rw [Real.volume_Ioo] at h0
    norm_num at h0
  -- a rational point of `U ∩ (s, ∞)`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo s hsU
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < s + ε by linarith)
  have hqU : (q : ℝ) ∈ U := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  refine ⟨q, ?_, hqU.1, hqU.2⟩
  exact_mod_cast (hs.1.trans hq1)

end Positive

end Sec7

end InteractingSLE
