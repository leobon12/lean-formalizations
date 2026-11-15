/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.PatchingConcat
import InteractingSLE.Spec.Sec2.Assembly2Stage

/-!
# Theorem 2.2, existence: continuing a local solution from the limit at its horizon

Packet PROVE-SEC2-PATCH3. PROVE-SEC2-TERM2's `IsSLEPathUpTo.concat` restarts a local solution at a
time `σ` strictly before its horizon. The maximal-solution argument restarts at the horizon itself,
from the limit of the state there:

* `IsSLEPathUpTo.closed_of_tendsto`: if a local solution before `σ > 0` (driven by a path continuous
  at `σ`) has a limit state at `σ⁻`, the reciprocal gaps are integrable on `[0, σ]` (each mark is
  monotone and bounded by its limit) and the integrated equations hold at `σ` with the limit state;
* `continuousOn_concatAt_Iic`, `IsSLEPathUpTo.concat_of_closed`: `concat` with the first piece known
  only on the closed interval `[0, σ]` (a copy of PROVE-SEC2-TERM2's proof with the facts at `σ` as
  hypotheses);
* **`IsSLEPathUpTo.concat_of_tendsto`**: a local solution before `σ` whose state tends to
  `(w₀, vL₀, vR₀)`, followed by a local solution started from `(vL₀ − w₀, vR₀ − w₀)` driven by the
  increments of the path after `σ`, is a local solution before `σ + τ₂`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Interval

namespace InteractingSLE

namespace Sec2

/-- **Continuity of a concatenation** whose first piece is continuous on the closed `[0, σ]`. -/
theorem continuousOn_concatAt_Iic {σ : ℝ≥0} {τ₂ : ℝ≥0∞} {f g : ℝ≥0 → ℝ} {c : ℝ}
    (hf : ContinuousOn f (Iic σ)) (hg : ContinuousOn g {t | (t : ℝ≥0∞) < τ₂})
    (hc : c + g 0 = f σ) :
    ContinuousOn (concatAt σ f c g) {t | (t : ℝ≥0∞) < (σ : ℝ≥0∞) + τ₂} := by
  have hg' : ∀ t : ℝ≥0, σ ≤ t → (t : ℝ≥0∞) < (σ : ℝ≥0∞) + τ₂ →
      ContinuousAt (fun s : ℝ≥0 => c + g (s - σ)) t := fun t hσt ht => by
    have hgt : ContinuousAt g (t - σ) :=
      hg.continuousAt ((isOpen_setOf_coe_lt τ₂).mem_nhds (coe_sub_lt_of_lt_add hσt ht))
    have hsub : Continuous fun s : ℝ≥0 => s - σ := by fun_prop
    exact continuousAt_const.add (ContinuousAt.comp (g := g) (f := fun s : ℝ≥0 => s - σ)
      (x := t) hgt hsub.continuousAt)
  refine (isOpen_setOf_coe_lt _).continuousOn_iff.2 fun t ht => ?_
  rcases lt_trichotomy t σ with htσ | rfl | htσ
  · have hft : ContinuousAt f t := hf.continuousAt (Iic_mem_nhds htσ)
    refine hft.congr ?_
    filter_upwards [Iio_mem_nhds htσ] with s hs using (concatAt_of_lt hs).symm
  · rw [continuousAt_iff_continuous_left_right]
    constructor
    · exact (hf t (mem_Iic.2 le_rfl)).congr (fun s hs => concatAt_of_le' hc hs) (concatAt_of_le' hc le_rfl)
    · refine ((hg' t le_rfl ht).continuousWithinAt).congr (fun s hs => concatAt_of_le hs)
        (concatAt_of_le le_rfl)
  · refine (hg' t htσ.le ht).congr ?_
    filter_upwards [Ioi_mem_nhds htσ] with s hs using (concatAt_of_le hs.le).symm

/-- The path `f` before `σ`, closed up by the value `c` from `σ` on. -/
def closeAt (σ : ℝ≥0) (f : ℝ≥0 → ℝ) (c : ℝ) : ℝ≥0 → ℝ := fun t => if t < σ then f t else c

theorem closeAt_of_lt {σ t : ℝ≥0} {f : ℝ≥0 → ℝ} {c : ℝ} (ht : t < σ) : closeAt σ f c t = f t := by
  simp [closeAt, ht]

theorem closeAt_self {σ : ℝ≥0} {f : ℝ≥0 → ℝ} {c : ℝ} : closeAt σ f c σ = c := by
  simp [closeAt]

/-- Functions of real time that agree before `σ` agree almost everywhere on `Ι 0 σ`. -/
theorem ae_eq_of_lt {σ : ℝ≥0} {F G : ℝ≥0 → ℝ} (hFG : ∀ t : ℝ≥0, t < σ → F t = G t) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0 : ℝ) σ → F s.toNNReal = G s.toNNReal := by
  refine ae_iff.2 (measure_mono_null (fun s hs => ?_) (measure_singleton (σ : ℝ)))
  simp only [mem_ofPred_eq, Classical.not_imp] at hs
  obtain ⟨hs1, hs2⟩ := hs
  rw [uIoc_of_le σ.coe_nonneg] at hs1
  rcases eq_or_lt_of_le hs1.2 with h | h
  · exact h
  · exact absurd (hFG _ (by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs1.1.le]; exact h)) hs2

/-- `concatAt` does not see the first piece from `σ` on. -/
theorem concatAt_closeAt {σ : ℝ≥0} {f g : ℝ≥0 → ℝ} {c c' : ℝ} :
    concatAt σ (closeAt σ f c') c g = concatAt σ f c g := by
  funext t
  unfold concatAt closeAt
  split_ifs <;> rfl

theorem ae_restrict_eq_of_lt {σ : ℝ≥0} {F G : ℝ≥0 → ℝ} (hFG : ∀ t : ℝ≥0, t < σ → F t = G t) :
    (fun s : ℝ => F s.toNNReal) =ᵐ[volume.restrict (Ι (0 : ℝ) σ)] fun s => G s.toNNReal :=
  (ae_restrict_iff' measurableSet_uIoc).2 (ae_eq_of_lt hFG)

/-- `σ − σ/(n+2) ↑ σ`. -/
def belowSeq (σ : ℝ≥0) (n : ℕ) : ℝ := σ - σ / ((n : ℝ) + 2)

theorem belowSeq_nonneg (σ : ℝ≥0) (n : ℕ) : 0 ≤ belowSeq σ n := by
  have : (σ : ℝ) / ((n : ℝ) + 2) ≤ σ :=
    div_le_self σ.coe_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  unfold belowSeq; linarith

theorem toNNReal_belowSeq_lt {σ : ℝ≥0} (hσ : 0 < σ) (n : ℕ) : (belowSeq σ n).toNNReal < σ := by
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (belowSeq_nonneg σ n)]
  have : 0 < (σ : ℝ) / ((n : ℝ) + 2) := div_pos (by exact_mod_cast hσ) (by positivity)
  unfold belowSeq; linarith

theorem tendsto_belowSeq (σ : ℝ≥0) : Tendsto (belowSeq σ) atTop (𝓝 σ) := by
  have h1 : Tendsto (fun n : ℕ => (σ : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have := (tendsto_const_nhds (x := (σ : ℝ))).sub h1
  rw [sub_zero] at this
  exact this

/-- The primitive of a function integrable on `[0, σ]` is left continuous at `σ`. -/
theorem tendsto_primitive_nhdsLT {σ : ℝ≥0} {F : ℝ → ℝ} (hF : IntervalIntegrable F volume 0 σ) :
    Tendsto (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, F s) (𝓝[<] σ) (𝓝 (∫ s in (0 : ℝ)..σ, F s)) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' hF (left_mem_uIcc)
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[<] σ) (𝓝[uIcc 0 (σ : ℝ)] (σ : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(NNReal.continuous_coe.tendsto σ).mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [uIcc_of_le σ.coe_nonneg]
    exact ⟨t.coe_nonneg, by exact_mod_cast (le_of_lt ht)⟩
  exact (hc σ right_mem_uIcc).tendsto.comp hcoe

namespace IsSLEPathUpTo

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {τ₂ : ℝ≥0∞} {σ : ℝ≥0} {w' : ℝ≥0 → ℝ} {vL' : Fin nL → ℝ≥0 → ℝ}
  {vR' : Fin nR → ℝ≥0 → ℝ} {b' : ℝ≥0 → ℝ} {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}

/-- **Closing a local solution at its horizon.** If a local solution before `σ > 0`, driven by a
path continuous at `σ`, has a limit state at `σ⁻`, the reciprocal gaps are integrable on `[0, σ]`
and the integrated equations hold at `σ` with the limit state. -/
theorem closed_of_tendsto (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b σ) (hσ : 0 < σ)
    (hb : ContinuousAt b σ)
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t)) (𝓝[<] σ)
      (𝓝 (w₀, vL₀, vR₀))) :
    (∀ i, IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 σ) ∧
    (∀ j, IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vR j s.toNNReal)⁻¹) volume 0 σ) ∧
    w₀ = Real.sqrt a * b σ
      + (∑ i, ∫ s in (0 : ℝ)..σ, ρL i / (w s.toNNReal - vL i s.toNNReal))
      + (∑ i, ∫ s in (0 : ℝ)..σ, ρR i / (w s.toNNReal - vR i s.toNNReal)) ∧
    (∀ i, vL₀ i = xL i + ∫ s in (0 : ℝ)..σ, 2 / (vL i s.toNNReal - w s.toNNReal)) ∧
    (∀ j, vR₀ j = xR j + ∫ s in (0 : ℝ)..σ, 2 / (vR j s.toNNReal - w s.toNNReal)) := by
  have : NeBot (𝓝[<] σ) := nhdsLT_neBot_of_exists_lt ⟨0, hσ⟩
  have hlt : ∀ {t : ℝ≥0}, t < σ → (t : ℝ≥0∞) < σ := fun ht => by exact_mod_cast ht
  have hwl : Tendsto w (𝓝[<] σ) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hLl : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] σ) (𝓝 (vL₀ i)) := fun i =>
    ((continuous_apply i).tendsto _).comp (((continuous_fst.comp continuous_snd).tendsto _).comp
      hlim)
  have hRl : ∀ j, Tendsto (fun t => vR j t) (𝓝[<] σ) (𝓝 (vR₀ j)) := fun j =>
    ((continuous_apply j).tendsto _).comp (((continuous_snd.comp continuous_snd).tendsto _).comp
      hlim)
  have hLge : ∀ i (t : ℝ≥0), t < σ → vL₀ i ≤ vL i t := fun i t ht => by
    refine le_of_tendsto (hLl i) ?_
    filter_upwards [Ioo_mem_nhdsLT ht] with u hu
    exact h.vL_le_of_le hu.1.le (hlt hu.2) i
  have hRle : ∀ j (t : ℝ≥0), t < σ → vR j t ≤ vR₀ j := fun j t ht => by
    refine ge_of_tendsto (hRl j) ?_
    filter_upwards [Ioo_mem_nhdsLT ht] with u hu
    exact h.le_vR_of_le hu.1.le (hlt hu.2) j
  have hintL : ∀ i (t : ℝ≥0), t < σ →
      ∫ s in (0 : ℝ)..t, (w s.toNNReal - vL i s.toNNReal)⁻¹ = (xL i - vL i t) / 2 :=
    fun i t ht => by
      have e := h.vL_eq (hlt ht) i
      have e2 : (∫ s in (0 : ℝ)..t, 2 / (vL i s.toNNReal - w s.toNNReal)) =
          -2 * ∫ s in (0 : ℝ)..t, (w s.toNNReal - vL i s.toNNReal)⁻¹ := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun s _ => two_div_sub_eq _ _
      rw [e2] at e
      linarith
  have hintR : ∀ j (t : ℝ≥0), t < σ →
      ∫ s in (0 : ℝ)..t, -(w s.toNNReal - vR j s.toNNReal)⁻¹ = (vR j t - xR j) / 2 :=
    fun j t ht => by
      have e := h.vR_eq (hlt ht) j
      have e2 : (∫ s in (0 : ℝ)..t, 2 / (vR j s.toNNReal - w s.toNNReal)) =
          2 * ∫ s in (0 : ℝ)..t, -(w s.toNNReal - vR j s.toNNReal)⁻¹ := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun s _ => by rw [two_div_sub_eq]; ring
      rw [e2] at e
      linarith
  have hmem : ∀ (n : ℕ) {s : ℝ}, s ∈ Ioc (0 : ℝ) (belowSeq σ n) → s.toNNReal < σ := fun n s hs =>
    lt_of_le_of_lt (Real.toNNReal_le_toNNReal hs.2) (toNNReal_belowSeq_lt hσ n)
  have hiL : ∀ i, IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹)
      volume 0 σ := by
    intro i
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le σ.coe_nonneg]
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_right (l := atTop)
      (b := belowSeq σ) (I := (xL i - vL₀ i) / 2) (fun n => ?_) (tendsto_belowSeq σ)
      (Eventually.of_forall fun n => ?_)
    · have := h.integrable_gapL (hlt (toNNReal_belowSeq_lt hσ n)) i
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg _),
        Real.coe_toNNReal _ (belowSeq_nonneg σ n)] at this
      exact this
    · have hnn : EqOn (fun s : ℝ => ‖(w s.toNNReal - vL i s.toNNReal)⁻¹‖)
          (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹) (Ioc (0 : ℝ) (belowSeq σ n)) :=
        fun s hs => by
          simp only
          rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (sub_nonneg.2
            (h.vL_le_w (hlt (hmem n hs)) i)))]
      rw [setIntegral_congr_fun measurableSet_Ioc hnn,
        ← intervalIntegral.integral_of_le (belowSeq_nonneg σ n)]
      have e := hintL i (belowSeq σ n).toNNReal (toNNReal_belowSeq_lt hσ n)
      rw [Real.coe_toNNReal _ (belowSeq_nonneg σ n)] at e
      rw [e]
      have := hLge i _ (toNNReal_belowSeq_lt hσ n)
      linarith
  have hiR : ∀ j, IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vR j s.toNNReal)⁻¹)
      volume 0 σ := by
    intro j
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le σ.coe_nonneg]
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_right (l := atTop)
      (b := belowSeq σ) (I := (vR₀ j - xR j) / 2) (fun n => ?_) (tendsto_belowSeq σ)
      (Eventually.of_forall fun n => ?_)
    · have := h.integrable_gapR (hlt (toNNReal_belowSeq_lt hσ n)) j
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg _),
        Real.coe_toNNReal _ (belowSeq_nonneg σ n)] at this
      exact this
    · have hnn : EqOn (fun s : ℝ => ‖(w s.toNNReal - vR j s.toNNReal)⁻¹‖)
          (fun s : ℝ => -(w s.toNNReal - vR j s.toNNReal)⁻¹) (Ioc (0 : ℝ) (belowSeq σ n)) :=
        fun s hs => by
          simp only
          rw [Real.norm_eq_abs, abs_of_nonpos (inv_nonpos.2 (sub_nonpos.2
            (h.w_le_vR (hlt (hmem n hs)) j)))]
      rw [setIntegral_congr_fun measurableSet_Ioc hnn,
        ← intervalIntegral.integral_of_le (belowSeq_nonneg σ n)]
      have e := hintR j (belowSeq σ n).toNNReal (toNNReal_belowSeq_lt hσ n)
      rw [Real.coe_toNNReal _ (belowSeq_nonneg σ n)] at e
      rw [e]
      have := hRle j _ (toNNReal_belowSeq_lt hσ n)
      linarith
  have hdivL : ∀ i (c : ℝ), IntervalIntegrable
      (fun s : ℝ => c / (w s.toNNReal - vL i s.toNNReal)) volume 0 σ := fun i c => by
    simpa only [div_eq_mul_inv] using (hiL i).const_mul c
  have hdivR : ∀ j (c : ℝ), IntervalIntegrable
      (fun s : ℝ => c / (w s.toNNReal - vR j s.toNNReal)) volume 0 σ := fun j c => by
    simpa only [div_eq_mul_inv] using (hiR j).const_mul c
  have hfL : ∀ i, IntervalIntegrable
      (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) volume 0 σ := fun i => by
    simpa only [two_div_sub_eq] using (hiL i).const_mul (-2)
  have hfR : ∀ j, IntervalIntegrable
      (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal)) volume 0 σ := fun j => by
    simpa only [two_div_sub_eq] using (hiR j).const_mul (-2)
  refine ⟨hiL, hiR, ?_, fun i => ?_, fun j => ?_⟩
  · have hR : Tendsto (fun t : ℝ≥0 => Real.sqrt a * b t
        + (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal))
        + (∑ i, ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal))) (𝓝[<] σ)
        (𝓝 (Real.sqrt a * b σ
          + (∑ i, ∫ s in (0 : ℝ)..σ, ρL i / (w s.toNNReal - vL i s.toNNReal))
          + (∑ i, ∫ s in (0 : ℝ)..σ, ρR i / (w s.toNNReal - vR i s.toNNReal)))) :=
      ((tendsto_const_nhds.mul (hb.tendsto.mono_left nhdsWithin_le_nhds)).add
        (tendsto_finsetSum _ fun i _ => tendsto_primitive_nhdsLT (hdivL i (ρL i)))).add
        (tendsto_finsetSum _ fun j _ => tendsto_primitive_nhdsLT (hdivR j (ρR j)))
    refine tendsto_nhds_unique hwl (hR.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h.w_eq (hlt ht)).symm
  · refine tendsto_nhds_unique (hLl i) ((tendsto_const_nhds.add
      (tendsto_primitive_nhdsLT (hfL i))).congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h.vL_eq (hlt ht) i).symm
  · refine tendsto_nhds_unique (hRl j) ((tendsto_const_nhds.add
      (tendsto_primitive_nhdsLT (hfR j))).congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h.vR_eq (hlt ht) j).symm

/-- **Concatenation with the first piece closed at `σ`**: `IsSLEPathUpTo.concat` with the facts at
`σ` (continuity on `[0, σ]`, integrability on `[0, σ]`, the equations at `σ`) as hypotheses. -/
theorem concat_of_closed (h₁ : IsSLEPathUpTo a xL xR ρL ρR w vL vR b σ)
    (hcw : ContinuousOn w (Iic σ)) (hcL : ∀ i, ContinuousOn (vL i) (Iic σ))
    (hcR : ∀ j, ContinuousOn (vR j) (Iic σ))
    (hiL : ∀ i, IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 σ)
    (hiR : ∀ j, IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vR j s.toNNReal)⁻¹) volume 0 σ)
    (hweq : w σ = Real.sqrt a * b σ
      + (∑ i, ∫ s in (0 : ℝ)..σ, ρL i / (w s.toNNReal - vL i s.toNNReal))
      + (∑ i, ∫ s in (0 : ℝ)..σ, ρR i / (w s.toNNReal - vR i s.toNNReal)))
    (hvL : ∀ i, vL i σ = xL i + ∫ s in (0 : ℝ)..σ, 2 / (vL i s.toNNReal - w s.toNNReal))
    (hvR : ∀ j, vR j σ = xR j + ∫ s in (0 : ℝ)..σ, 2 / (vR j s.toNNReal - w s.toNNReal))
    (h₂ : IsSLEPathUpTo a (fun i => vL i σ - w σ) (fun j => vR j σ - w σ) ρL ρR w' vL' vR' b' τ₂)
    (hb' : ∀ t, b' t = b (σ + t) - b σ) :
    IsSLEPathUpTo a xL xR ρL ρR (concatAt σ w (w σ) w')
      (fun i => concatAt σ (vL i) (w σ) (vL' i)) (fun j => concatAt σ (vR j) (w σ) (vR' j)) b
      ((σ : ℝ≥0∞) + τ₂) := by
  have cw : w σ + w' 0 = w σ := by rw [h₂.w_zero, add_zero]
  have cL : ∀ i, w σ + vL' i 0 = vL i σ := fun i => by rw [h₂.vL_zero i]; ring
  have cR : ∀ j, w σ + vR' j 0 = vR j σ := fun j => by rw [h₂.vR_zero j]; ring
  have hlt1 : ∀ {t : ℝ≥0}, t < σ → (t : ℝ≥0∞) < σ := fun ht => by exact_mod_cast ht
  have hdivL : ∀ i (c : ℝ), IntervalIntegrable
      (fun s : ℝ => c / (w s.toNNReal - vL i s.toNNReal)) volume 0 σ := fun i c => by
    simpa only [div_eq_mul_inv] using (hiL i).const_mul c
  have hdivR : ∀ j (c : ℝ), IntervalIntegrable
      (fun s : ℝ => c / (w s.toNNReal - vR j s.toNNReal)) volume 0 σ := fun j c => by
    simpa only [div_eq_mul_inv] using (hiR j).const_mul c
  have hfL : ∀ i, IntervalIntegrable
      (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) volume 0 σ := fun i => by
    simpa only [two_div_sub_eq] using (hiL i).const_mul (-2)
  have hfR : ∀ j, IntervalIntegrable
      (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal)) volume 0 σ := fun j => by
    simpa only [two_div_sub_eq] using (hiR j).const_mul (-2)
  have hlt2 : ∀ {t : ℝ≥0}, σ ≤ t → (t : ℝ≥0∞) < (σ : ℝ≥0∞) + τ₂ →
      ((t - σ : ℝ≥0) : ℝ≥0∞) < τ₂ := fun hσt ht => coe_sub_lt_of_lt_add hσt ht
  -- integrals of translation-invariant functions of `(w, v)`, split at `σ`
  have hsplit : ∀ (F : ℝ → ℝ → ℝ), (∀ c x y, F (c + x) (c + y) = F x y) →
      ∀ (v v' : ℝ≥0 → ℝ), w σ + v' 0 = v σ → ∀ {t : ℝ≥0}, σ ≤ t →
      IntervalIntegrable (fun s : ℝ => F (w s.toNNReal) (v s.toNNReal)) volume 0 σ →
      IntervalIntegrable (fun s : ℝ => F (w' s.toNNReal) (v' s.toNNReal)) volume 0
        ((t - σ : ℝ≥0) : ℝ) →
      IntervalIntegrable (fun s : ℝ => F (concatAt σ w (w σ) w' s.toNNReal)
        (concatAt σ v (w σ) v' s.toNNReal)) volume 0 t ∧
      ∫ s in (0 : ℝ)..t, F (concatAt σ w (w σ) w' s.toNNReal) (concatAt σ v (w σ) v' s.toNNReal) =
        (∫ s in (0 : ℝ)..σ, F (w s.toNNReal) (v s.toNNReal)) +
          ∫ s in (0 : ℝ)..((t - σ : ℝ≥0) : ℝ), F (w' s.toNNReal) (v' s.toNNReal) :=
    fun F hF v v' cv t hσt hi1 hi2 => integral_concat_split hσt
      (H := fun s => F (concatAt σ w (w σ) w' s) (concatAt σ v (w σ) v' s))
      (G₁ := fun s => F (w s) (v s)) (G₂ := fun s => F (w' s) (v' s))
      (fun s hs => by simp only [concatAt_of_le' cw hs, concatAt_of_le' cv hs])
      (fun s hs => by simp only [concatAt_of_le hs, hF]) hi1 hi2
  have hbefore : ∀ (F : ℝ → ℝ → ℝ) (v v' : ℝ≥0 → ℝ) {t : ℝ≥0}, t < σ →
      EqOn (fun s : ℝ => F (concatAt σ w (w σ) w' s.toNNReal) (concatAt σ v (w σ) v' s.toNNReal))
        (fun s : ℝ => F (w s.toNNReal) (v s.toNNReal)) (uIcc 0 (t : ℝ)) :=
    fun F v v' t ht => eqOn_toNNReal_of_lt ht
      (H := fun s => F (concatAt σ w (w σ) w' s) (concatAt σ v (w σ) v' s))
      (F := fun s => F (w s) (v s)) fun s hs => by simp only [concatAt_of_lt hs]
  have hinvF : ∀ c x y : ℝ, ((c + x) - (c + y))⁻¹ = (x - y)⁻¹ := fun c x y => by
    rw [add_sub_add_left_eq_sub]
  have hdivF : ∀ ρ c x y : ℝ, ρ / ((c + x) - (c + y)) = ρ / (x - y) := fun ρ c x y => by
    rw [add_sub_add_left_eq_sub]
  have hforceF : ∀ c x y : ℝ, 2 / ((c + y) - (c + x)) = 2 / (y - x) := fun c x y => by
    rw [add_sub_add_left_eq_sub]
  refine
    { w_zero := ?_, vL_zero := ?_, vR_zero := ?_, continuousOn_w := ?_, continuousOn_vL := ?_,
      continuousOn_vR := ?_, antitone_vL := ?_, vL_le_w := ?_, w_le_vR := ?_, monotone_vR := ?_,
      integrable_gapL := ?_, integrable_gapR := ?_, w_eq := ?_, vL_eq := ?_, vR_eq := ?_,
      volume_collisionL := ?_, volume_collisionR := ?_, not_threshold := ?_ }
  · rw [concatAt_of_le' cw (zero_le : (0 : ℝ≥0) ≤ σ)]; exact h₁.w_zero
  · intro i; rw [concatAt_of_le' (cL i) (zero_le : (0 : ℝ≥0) ≤ σ)]; exact h₁.vL_zero i
  · intro j; rw [concatAt_of_le' (cR j) (zero_le : (0 : ℝ≥0) ≤ σ)]; exact h₁.vR_zero j
  · exact continuousOn_concatAt_Iic hcw h₂.continuousOn_w cw
  · exact fun i => continuousOn_concatAt_Iic (hcL i) (h₂.continuousOn_vL i) (cL i)
  · exact fun j => continuousOn_concatAt_Iic (hcR j) (h₂.continuousOn_vR j) (cR j)
  · intro t ht
    rcases lt_or_ge t σ with h | h
    · simp only [concatAt_of_lt h]; exact h₁.antitone_vL (hlt1 h)
    · simp only [concatAt_of_le h]
      exact fun i j hij => (add_le_add_iff_left (w σ)).2 (h₂.antitone_vL (hlt2 h ht) hij)
  · intro t ht i
    rcases lt_or_ge t σ with h | h
    · simp only [concatAt_of_lt h]; exact h₁.vL_le_w (hlt1 h) i
    · simp only [concatAt_of_le h]; exact (add_le_add_iff_left (w σ)).2 (h₂.vL_le_w (hlt2 h ht) i)
  · intro t ht j
    rcases lt_or_ge t σ with h | h
    · simp only [concatAt_of_lt h]; exact h₁.w_le_vR (hlt1 h) j
    · simp only [concatAt_of_le h]; exact (add_le_add_iff_left (w σ)).2 (h₂.w_le_vR (hlt2 h ht) j)
  · intro t ht
    rcases lt_or_ge t σ with h | h
    · simp only [concatAt_of_lt h]; exact h₁.monotone_vR (hlt1 h)
    · simp only [concatAt_of_le h]
      exact fun i j hij => (add_le_add_iff_left (w σ)).2 (h₂.monotone_vR (hlt2 h ht) hij)
  · intro t ht i
    rcases lt_or_ge t σ with h | h
    · exact (h₁.integrable_gapL (hlt1 h) i).congr
        ((hbefore (fun x y => (x - y)⁻¹) (vL i) (vL' i) h).symm.mono uIoc_subset_uIcc)
    · exact (hsplit (fun x y => (x - y)⁻¹) hinvF (vL i) (vL' i) (cL i) h
        (hiL i) (h₂.integrable_gapL (hlt2 h ht) i)).1
  · intro t ht j
    rcases lt_or_ge t σ with h | h
    · exact (h₁.integrable_gapR (hlt1 h) j).congr
        ((hbefore (fun x y => (x - y)⁻¹) (vR j) (vR' j) h).symm.mono uIoc_subset_uIcc)
    · exact (hsplit (fun x y => (x - y)⁻¹) hinvF (vR j) (vR' j) (cR j) h
        (hiR j) (h₂.integrable_gapR (hlt2 h ht) j)).1
  · intro t ht
    rcases lt_or_ge t σ with h | h
    · rw [concatAt_of_lt h, h₁.w_eq (hlt1 h)]
      rw [Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr
          (hbefore (fun x y => ρL i / (x - y)) (vL i) (vL' i) h),
        Finset.sum_congr rfl fun j _ => intervalIntegral.integral_congr
          (hbefore (fun x y => ρR j / (x - y)) (vR j) (vR' j) h)]
    · have eL : ∀ i, ∫ s in (0 : ℝ)..t, ρL i / (concatAt σ w (w σ) w' s.toNNReal -
          concatAt σ (vL i) (w σ) (vL' i) s.toNNReal) =
          (∫ s in (0 : ℝ)..σ, ρL i / (w s.toNNReal - vL i s.toNNReal)) +
            ∫ s in (0 : ℝ)..((t - σ : ℝ≥0) : ℝ), ρL i / (w' s.toNNReal - vL' i s.toNNReal) :=
        fun i => (hsplit (fun x y => ρL i / (x - y)) (hdivF (ρL i)) (vL i) (vL' i) (cL i) h
          (hdivL i (ρL i))
          ((intervalIntegrable_div_gap h₂ (hlt2 h ht)).1 i (ρL i))).2
      have eR : ∀ j, ∫ s in (0 : ℝ)..t, ρR j / (concatAt σ w (w σ) w' s.toNNReal -
          concatAt σ (vR j) (w σ) (vR' j) s.toNNReal) =
          (∫ s in (0 : ℝ)..σ, ρR j / (w s.toNNReal - vR j s.toNNReal)) +
            ∫ s in (0 : ℝ)..((t - σ : ℝ≥0) : ℝ), ρR j / (w' s.toNNReal - vR' j s.toNNReal) :=
        fun j => (hsplit (fun x y => ρR j / (x - y)) (hdivF (ρR j)) (vR j) (vR' j) (cR j) h
          (hdivR j (ρR j))
          ((intervalIntegrable_div_gap h₂ (hlt2 h ht)).2 j (ρR j))).2
      rw [concatAt_of_le h, Finset.sum_congr rfl fun i _ => eL i,
        Finset.sum_congr rfl fun j _ => eR j, Finset.sum_add_distrib, Finset.sum_add_distrib,
        h₂.w_eq (hlt2 h ht), hb', add_tsub_cancel_of_le h]
      nth_rewrite 1 [hweq]
      ring
  · intro t ht i
    rcases lt_or_ge t σ with h | h
    · rw [concatAt_of_lt h, h₁.vL_eq (hlt1 h) i, intervalIntegral.integral_congr
        (hbefore (fun x y => 2 / (y - x)) (vL i) (vL' i) h)]
    · have e := (hsplit (fun x y => 2 / (y - x)) hforceF (vL i) (vL' i) (cL i) h
        (hfL i) (h₂.intervalIntegrable_forceL (hlt2 h ht) i)).2
      beta_reduce at e
      rw [concatAt_of_le h, e, h₂.vL_eq (hlt2 h ht) i, hvL i]
      ring
  · intro t ht j
    rcases lt_or_ge t σ with h | h
    · rw [concatAt_of_lt h, h₁.vR_eq (hlt1 h) j, intervalIntegral.integral_congr
        (hbefore (fun x y => 2 / (y - x)) (vR j) (vR' j) h)]
    · have e := (hsplit (fun x y => 2 / (y - x)) hforceF (vR j) (vR' j) (cR j) h
        (hfR j) (h₂.intervalIntegrable_forceR (hlt2 h ht) j)).2
      beta_reduce at e
      rw [concatAt_of_le h, e, h₂.vR_eq (hlt2 h ht) j, hvR j]
      ring
  · intro i
    refine measure_mono_null (fun s hs => ?_) (measure_union_null (h₁.volume_collisionL i)
      ((measure_preimage_add_right volume (-(σ : ℝ)) _).trans (h₂.volume_collisionL i)))
    obtain ⟨hs0, hsτ, he⟩ := hs
    rcases lt_or_ge s.toNNReal σ with h | h
    · rw [concatAt_of_lt h, concatAt_of_lt h] at he
      exact Or.inl ⟨hs0, hlt1 h, he⟩
    · rw [concatAt_of_le h, concatAt_of_le h, add_right_inj] at he
      have hσs : (σ : ℝ) ≤ s := (Real.le_toNNReal_iff_coe_le hs0).1 h
      have hu : 0 ≤ s + -(σ : ℝ) := by linarith
      have e : (s + -(σ : ℝ)).toNNReal = s.toNNReal - σ := by
        have := toNNReal_add_sub (σ := σ) hu
        rw [show (σ : ℝ) + (s + -(σ : ℝ)) = s by ring] at this
        exact this.symm
      refine Or.inr ⟨hu, ?_, ?_⟩
      · rw [e]; exact hlt2 h hsτ
      · rw [e]; exact he
  · intro j
    refine measure_mono_null (fun s hs => ?_) (measure_union_null (h₁.volume_collisionR j)
      ((measure_preimage_add_right volume (-(σ : ℝ)) _).trans (h₂.volume_collisionR j)))
    obtain ⟨hs0, hsτ, he⟩ := hs
    rcases lt_or_ge s.toNNReal σ with h | h
    · rw [concatAt_of_lt h, concatAt_of_lt h] at he
      exact Or.inl ⟨hs0, hlt1 h, he⟩
    · rw [concatAt_of_le h, concatAt_of_le h, add_right_inj] at he
      have hσs : (σ : ℝ) ≤ s := (Real.le_toNNReal_iff_coe_le hs0).1 h
      have hu : 0 ≤ s + -(σ : ℝ) := by linarith
      have e : (s + -(σ : ℝ)).toNNReal = s.toNNReal - σ := by
        have := toNNReal_add_sub (σ := σ) hu
        rw [show (σ : ℝ) + (s + -(σ : ℝ)) = s by ring] at this
        exact this.symm
      refine Or.inr ⟨hu, ?_, ?_⟩
      · rw [e]; exact hlt2 h hsτ
      · rw [e]; exact he
  · intro t ht
    rcases lt_or_ge t σ with h | h
    · simp only [concatAt_of_lt h]; exact h₁.not_threshold (hlt1 h)
    · simp only [concatAt_of_le h]
      have := h₂.not_threshold (hlt2 h ht)
      simpa only [ForceWord.ThresholdCondition, add_right_inj] using this

/-- **Continuing a local solution from the limit at its horizon.** A local solution before `σ > 0`,
driven by a path continuous at `σ`, whose state tends to `(w₀, vL₀, vR₀)` at `σ⁻`, followed by a
local solution started from `(vL₀ − w₀, vR₀ − w₀)` and driven by the increments of the path after
`σ`, is a local solution before `σ + τ₂`. -/
theorem concat_of_tendsto (h₁ : IsSLEPathUpTo a xL xR ρL ρR w vL vR b σ) (hσ : 0 < σ)
    (hb : ContinuousAt b σ)
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t)) (𝓝[<] σ)
      (𝓝 (w₀, vL₀, vR₀)))
    (h₂ : IsSLEPathUpTo a (fun i => vL₀ i - w₀) (fun j => vR₀ j - w₀) ρL ρR w' vL' vR' b' τ₂)
    (hb' : ∀ t, b' t = b (σ + t) - b σ) :
    IsSLEPathUpTo a xL xR ρL ρR (concatAt σ w w₀ w') (fun i => concatAt σ (vL i) w₀ (vL' i))
      (fun j => concatAt σ (vR j) w₀ (vR' j)) b ((σ : ℝ≥0∞) + τ₂) := by
  obtain ⟨hiL, hiR, hweq, hvL, hvR⟩ := h₁.closed_of_tendsto hσ hb hlim
  have hσ' : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < σ → t < σ := fun ht => by exact_mod_cast ht
  set wc := closeAt σ w w₀ with hwc
  set vLc : Fin nL → ℝ≥0 → ℝ := fun i => closeAt σ (vL i) (vL₀ i) with hvLc
  set vRc : Fin nR → ℝ≥0 → ℝ := fun j => closeAt σ (vR j) (vR₀ j) with hvRc
  have h₁' : IsSLEPathUpTo a xL xR ρL ρR wc vLc vRc b σ :=
    Assembly2.isSLEPathUpTo_congr h₁ (closeAt_of_lt hσ) (fun _ => closeAt_of_lt hσ)
      (fun _ => closeAt_of_lt hσ) (fun _ ht => closeAt_of_lt (hσ' ht))
      (fun _ ht _ => closeAt_of_lt (hσ' ht)) (fun _ ht _ => closeAt_of_lt (hσ' ht)) fun _ _ => rfl
  have hcont : ∀ {f : ℝ≥0 → ℝ} {c : ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < σ} →
      Tendsto f (𝓝[<] σ) (𝓝 c) → ContinuousOn (closeAt σ f c) (Iic σ) := by
    intro f c hf hfc t ht
    rcases eq_or_lt_of_le (show t ≤ σ from ht) with rfl | htσ
    · rw [← continuousWithinAt_Iio_iff_Iic]
      show Tendsto (closeAt t f c) (𝓝[<] t) (𝓝 (closeAt t f c t))
      rw [closeAt_self]
      refine hfc.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs using (closeAt_of_lt hs).symm
    · have hft : ContinuousAt f t := hf.continuousAt
        ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds (by exact_mod_cast htσ))
      have : ContinuousAt (closeAt σ f c) t := by
        refine hft.congr ?_
        filter_upwards [Iio_mem_nhds htσ] with s hs using (closeAt_of_lt hs).symm
      exact this.continuousWithinAt
  have hwl : Tendsto w (𝓝[<] σ) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hLl : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] σ) (𝓝 (vL₀ i)) := fun i =>
    ((continuous_apply i).tendsto _).comp (((continuous_fst.comp continuous_snd).tendsto _).comp
      hlim)
  have hRl : ∀ j, Tendsto (fun t => vR j t) (𝓝[<] σ) (𝓝 (vR₀ j)) := fun j =>
    ((continuous_apply j).tendsto _).comp (((continuous_snd.comp continuous_snd).tendsto _).comp
      hlim)
  have hagree : ∀ t : ℝ≥0, t < σ → wc t = w t ∧ (∀ i, vLc i t = vL i t) ∧ ∀ j, vRc j t = vR j t :=
    fun t ht => ⟨closeAt_of_lt ht, fun _ => closeAt_of_lt ht, fun _ => closeAt_of_lt ht⟩
  have hiL' : ∀ i, IntervalIntegrable (fun s : ℝ => (wc s.toNNReal - vLc i s.toNNReal)⁻¹)
      volume 0 σ := fun i => (hiL i).congr_ae (ae_restrict_eq_of_lt
        (F := fun t => (w t - vL i t)⁻¹) (G := fun t => (wc t - vLc i t)⁻¹) fun t ht => by
          simp only [(hagree t ht).1, (hagree t ht).2.1 i])
  have hiR' : ∀ j, IntervalIntegrable (fun s : ℝ => (wc s.toNNReal - vRc j s.toNNReal)⁻¹)
      volume 0 σ := fun j => (hiR j).congr_ae (ae_restrict_eq_of_lt
        (F := fun t => (w t - vR j t)⁻¹) (G := fun t => (wc t - vRc j t)⁻¹) fun t ht => by
          simp only [(hagree t ht).1, (hagree t ht).2.2 j])
  have hweq' : wc σ = Real.sqrt a * b σ
      + (∑ i, ∫ s in (0 : ℝ)..σ, ρL i / (wc s.toNNReal - vLc i s.toNNReal))
      + (∑ i, ∫ s in (0 : ℝ)..σ, ρR i / (wc s.toNNReal - vRc i s.toNNReal)) := by
    have hwcσ : wc σ = w₀ := closeAt_self
    have eL : (∑ i, ∫ s in (0 : ℝ)..σ, ρL i / (w s.toNNReal - vL i s.toNNReal)) =
        ∑ i, ∫ s in (0 : ℝ)..σ, ρL i / (wc s.toNNReal - vLc i s.toNNReal) :=
      Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr_ae
        (ae_eq_of_lt (F := fun t => ρL i / (w t - vL i t))
          (G := fun t => ρL i / (wc t - vLc i t)) fun t ht => by
            simp only [(hagree t ht).1, (hagree t ht).2.1 i])
    have eR : (∑ j, ∫ s in (0 : ℝ)..σ, ρR j / (w s.toNNReal - vR j s.toNNReal)) =
        ∑ j, ∫ s in (0 : ℝ)..σ, ρR j / (wc s.toNNReal - vRc j s.toNNReal) :=
      Finset.sum_congr rfl fun j _ => intervalIntegral.integral_congr_ae
        (ae_eq_of_lt (F := fun t => ρR j / (w t - vR j t))
          (G := fun t => ρR j / (wc t - vRc j t)) fun t ht => by
            simp only [(hagree t ht).1, (hagree t ht).2.2 j])
    rw [hwcσ, hweq, eL, eR]
  have hvL' : ∀ i, vLc i σ = xL i + ∫ s in (0 : ℝ)..σ, 2 / (vLc i s.toNNReal - wc s.toNNReal) :=
    fun i => by
      show closeAt σ (vL i) (vL₀ i) σ = _
      rw [closeAt_self, hvL i]
      congr 1
      refine intervalIntegral.integral_congr_ae ?_
      exact ae_eq_of_lt (F := fun t => 2 / (vL i t - w t))
        (G := fun t => 2 / (vLc i t - wc t)) fun t ht => by
          simp only [(hagree t ht).1, (hagree t ht).2.1 i]
  have hvR' : ∀ j, vRc j σ = xR j + ∫ s in (0 : ℝ)..σ, 2 / (vRc j s.toNNReal - wc s.toNNReal) :=
    fun j => by
      show closeAt σ (vR j) (vR₀ j) σ = _
      rw [closeAt_self, hvR j]
      congr 1
      refine intervalIntegral.integral_congr_ae ?_
      exact ae_eq_of_lt (F := fun t => 2 / (vR j t - w t))
        (G := fun t => 2 / (vRc j t - wc t)) fun t ht => by
          simp only [(hagree t ht).1, (hagree t ht).2.2 j]
  have e1 : (fun i => vLc i σ - wc σ) = fun i => vL₀ i - w₀ := funext fun i => by
    simp only [hvLc, hwc, closeAt_self]
  have e2 : (fun j => vRc j σ - wc σ) = fun j => vR₀ j - w₀ := funext fun j => by
    simp only [hvRc, hwc, closeAt_self]
  have h₂' : IsSLEPathUpTo a (fun i => vLc i σ - wc σ) (fun j => vRc j σ - wc σ) ρL ρR w' vL' vR'
      b' τ₂ := by rw [e1, e2]; exact h₂
  have key := concat_of_closed h₁' (hcont h₁.continuousOn_w hwl)
    (fun i => hcont (h₁.continuousOn_vL i) (hLl i)) (fun j => hcont (h₁.continuousOn_vR j) (hRl j))
    hiL' hiR' hweq' hvL' hvR' h₂' hb'
  have hwcσ : wc σ = w₀ := closeAt_self
  rw [hwcσ] at key
  simpa only [hwc, hvLc, hvRc, concatAt_closeAt] using key

end IsSLEPathUpTo

end Sec2

end InteractingSLE
