/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Two uniqueness tools for recovering a driving history from its trace

Packet PROVE-FLOWEXIST (step "recover `W` and `V` measurably from the trace" of `exists_isFlowLine`).

* **`eq_zero_of_mul_integrand_nonpos`**: a primitive `D(t) = ∫₀ᵗ g` with `D g ≤ 0` almost everywhere vanishes.
  This is the uniqueness argument for the force-point equation `v(t) = x + ∫₀ᵗ 2/(v − w)` given the driver `w`:
  the drift `v ↦ 2/(v − w)` is decreasing on each side of `w`, so two solutions on the same side cannot separate
  (`eqOn_of_force_eq`). The collision sets `{v = w}` (where Lean's `2/0 = 0` breaks monotonicity) are null.
* **`exists_measurable_leftInverse_of_injOn`** (Lusin–Souslin): a measurable map from a standard Borel space,
  injective on a measurable set, has a measurable left inverse on that set.

Mathematical step added (not in the specification): the two solutions `v₁, v₂` of the force-point equation with the
same driver and initial value agree. Proof: `D = v₁ − v₂` is the primitive of `g = 2/(v₁ − w) − 2/(v₂ − w)`, and off
the null collision sets `D g = −2 D² / ((v₁ − w)(v₂ − w)) ≤ 0`. If `D(t₁) > 0`, let `s₀` be the last zero of `D⁺`
before `t₁`; then `g ≤ 0` a.e. on `(s₀, t₁]`, so `D(t₁) = D(s₀) + ∫_{s₀}^{t₁} g ≤ 0`, a contradiction (and
symmetrically for `D(t₁) < 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

/-! ### A primitive with `D g ≤ 0` vanishes -/

theorem not_pos_of_mul_integrand_nonpos {D g : ℝ → ℝ} {t₀ : ℝ}
    (hg : IntervalIntegrable g volume 0 t₀)
    (hD : ∀ t ∈ Icc (0 : ℝ) t₀, D t = ∫ s in (0 : ℝ)..t, g s)
    (hsign : ∀ᵐ s ∂volume, s ∈ Icc (0 : ℝ) t₀ → D s * g s ≤ 0) :
    ∀ t ∈ Icc (0 : ℝ) t₀, ¬ 0 < D t := by
  intro t₁ ht₁ hpos
  have ht₀ : 0 ≤ t₀ := ht₁.1.trans ht₁.2
  have hcont : ContinuousOn D (Icc 0 t₀) := by
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := g) (a := 0) (b := t₀)
      (by rw [uIcc_of_le ht₀]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le ht₀).1 hg)
    rw [uIcc_of_le ht₀] at h
    exact h.congr hD
  set S := {s ∈ Icc (0 : ℝ) t₁ | D s ≤ 0} with hS
  have hsub : Icc (0 : ℝ) t₁ ⊆ Icc 0 t₀ := Icc_subset_Icc le_rfl ht₁.2
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, ht₁.1⟩, by
    rw [hD 0 ⟨le_rfl, ht₀⟩, intervalIntegral.integral_same]⟩
  have hSc : IsClosed S := (hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSb : BddAbove S := ⟨t₁, fun s hs => hs.1.2⟩
  set s₀ := sSup S with hs₀
  have hs₀S : s₀ ∈ S := hSc.csSup_mem ⟨0, h0S⟩ hSb
  have hs₀t : s₀ < t₁ := lt_of_le_of_ne hs₀S.1.2 fun he => by
    have := hs₀S.2
    rw [he] at this
    exact absurd hpos (not_lt.2 this)
  have hDpos : ∀ s ∈ Ioc s₀ t₁, 0 < D s := fun s hs => by
    by_contra hns
    have : s ∈ S := ⟨⟨hs₀S.1.1.trans hs.1.le, hs.2⟩, not_lt.1 hns⟩
    exact absurd (le_csSup hSb this) (not_le.2 hs.1)
  have hgi : ∀ c ∈ Icc (0 : ℝ) t₀, IntervalIntegrable g volume 0 c := fun c hc =>
    hg.mono_set (by rw [uIcc_of_le hc.1, uIcc_of_le ht₀]; exact Icc_subset_Icc le_rfl hc.2)
  have hdiff : D t₁ - D s₀ = ∫ s in s₀..t₁, g s := by
    rw [hD t₁ (hsub ⟨ht₁.1, le_rfl⟩), hD s₀ (hsub hs₀S.1),
      intervalIntegral.integral_interval_sub_left (hgi t₁ (hsub ⟨ht₁.1, le_rfl⟩)) (hgi s₀ (hsub hs₀S.1))]
  have hnp : ∫ s in s₀..t₁, g s ≤ 0 := by
    suffices h : 0 ≤ ∫ s in s₀..t₁, -g s by
      rw [intervalIntegral.integral_neg] at h
      linarith
    refine intervalIntegral.integral_nonneg_of_ae_restrict hs₀t.le ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    have hIoc : ∀ᵐ s ∂volume, s ≠ s₀ := measure_eq_zero_iff_ae_notMem.1 (measure_singleton s₀)
    filter_upwards [hsign, hIoc] with s hs hne hsI
    have hsI' : s ∈ Ioc s₀ t₁ := ⟨lt_of_le_of_ne hsI.1 (Ne.symm hne), hsI.2⟩
    have hDs := hDpos s hsI'
    have hm := hs (hsub ⟨hs₀S.1.1.trans hsI'.1.le, hsI'.2⟩)
    by_contra hgs
    exact absurd hm (not_le.2 (mul_pos hDs (by simpa using (not_le.1 hgs))))
  have := hs₀S.2
  linarith

/-- **A primitive `D = ∫₀ g` with `D g ≤ 0` almost everywhere vanishes.** -/
theorem eq_zero_of_mul_integrand_nonpos {D g : ℝ → ℝ} {t₀ : ℝ}
    (hg : IntervalIntegrable g volume 0 t₀)
    (hD : ∀ t ∈ Icc (0 : ℝ) t₀, D t = ∫ s in (0 : ℝ)..t, g s)
    (hsign : ∀ᵐ s ∂volume, s ∈ Icc (0 : ℝ) t₀ → D s * g s ≤ 0) :
    ∀ t ∈ Icc (0 : ℝ) t₀, D t = 0 := by
  intro t ht
  have h1 := not_pos_of_mul_integrand_nonpos hg hD hsign t ht
  have h2 := not_pos_of_mul_integrand_nonpos (D := fun s => -D s) (g := fun s => -g s) hg.neg
    (fun s hs => by rw [hD s hs, intervalIntegral.integral_neg])
    (by filter_upwards [hsign] with s hs hsI; have := hs hsI; nlinarith) t ht
  simp only [neg_pos, not_lt] at h2
  exact le_antisymm (not_lt.1 h1) h2

/-! ### Uniqueness of the force-point equation given the driver -/

theorem mul_two_div_sub_two_div_nonpos {a b : ℝ} (hab : 0 < a * b) :
    (a - b) * (2 / a - 2 / b) ≤ 0 := by
  have ha : a ≠ 0 := fun h => by simp [h] at hab
  have hb : b ≠ 0 := fun h => by simp [h] at hab
  have e : (a - b) * (2 / a - 2 / b) = -(2 * (a - b) ^ 2) / (a * b) := by
    field_simp
    ring
  rw [e]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) hab.le

theorem intervalIntegrable_two_div {w v : ℝ≥0 → ℝ} {t : ℝ}
    (hi : IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 t) :
    IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume 0 t := by
  refine (hi.const_mul (-2)).congr fun s _ => ?_
  change -2 * (w s.toNNReal - v s.toNNReal)⁻¹ = 2 / (v s.toNNReal - w s.toNNReal)
  rw [div_eq_mul_inv, ← neg_sub, inv_neg]
  ring

/-- **Two solutions of the force-point equation `v(t) = x₀ + ∫₀ᵗ 2/(v − w)` with the same driver `w`, both on the
same side of `w` at every time, with absolutely integrable reciprocal gaps and null collision sets, agree** before
the lifetime. -/
theorem eqOn_of_force_eq {w v₁ v₂ : ℝ≥0 → ℝ} {T : ℝ≥0∞} {x₀ : ℝ}
    (hside : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → (w t ≤ v₁ t ∧ w t ≤ v₂ t) ∨ (v₁ t ≤ w t ∧ v₂ t ≤ w t))
    (hi₁ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v₁ s.toNNReal)⁻¹) volume 0 t)
    (hi₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v₂ s.toNNReal)⁻¹) volume 0 t)
    (he₁ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → v₁ t = x₀ + ∫ s in (0 : ℝ)..t, 2 / (v₁ s.toNNReal - w s.toNNReal))
    (he₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → v₂ t = x₀ + ∫ s in (0 : ℝ)..t, 2 / (v₂ s.toNNReal - w s.toNNReal))
    (hn₁ : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = v₁ s.toNNReal} = 0)
    (hn₂ : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = v₂ s.toNNReal} = 0) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → v₁ t = v₂ t := by
  intro t ht
  set g : ℝ → ℝ := fun s => 2 / (v₁ s.toNNReal - w s.toNNReal) - 2 / (v₂ s.toNNReal - w s.toNNReal) with hg
  set D : ℝ → ℝ := fun s => v₁ s.toNNReal - v₂ s.toNNReal with hDdef
  have hlt : ∀ r ∈ Icc (0 : ℝ) t, (r.toNNReal : ℝ≥0∞) < T := fun r hr =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2)) ht
  have hint : ∀ r ∈ Icc (0 : ℝ) t, IntervalIntegrable g volume 0 r := fun r hr => by
    have h1 := intervalIntegrable_two_div (hi₁ _ (hlt r hr))
    have h2 := intervalIntegrable_two_div (hi₂ _ (hlt r hr))
    rw [Real.coe_toNNReal _ hr.1] at h1 h2
    exact h1.sub h2
  have hD : ∀ r ∈ Icc (0 : ℝ) t, D r = ∫ s in (0 : ℝ)..r, g s := fun r hr => by
    have h1 := he₁ _ (hlt r hr)
    have h2 := he₂ _ (hlt r hr)
    rw [Real.coe_toNNReal _ hr.1] at h1 h2
    have i1 := intervalIntegrable_two_div (hi₁ _ (hlt r hr))
    have i2 := intervalIntegrable_two_div (hi₂ _ (hlt r hr))
    rw [Real.coe_toNNReal _ hr.1] at i1 i2
    simp only [hDdef, hg]
    rw [intervalIntegral.integral_sub i1 i2, h1, h2]
    ring
  have hsign : ∀ᵐ s ∂volume, s ∈ Icc (0 : ℝ) t → D s * g s ≤ 0 := by
    have hn₁' := measure_eq_zero_iff_ae_notMem.1 hn₁
    have hn₂' := measure_eq_zero_iff_ae_notMem.1 hn₂
    filter_upwards [hn₁', hn₂'] with s hs₁ hs₂ hsI
    have hT := hlt s hsI
    have h1 : w s.toNNReal ≠ v₁ s.toNNReal := fun h => hs₁ ⟨hsI.1, hT, h⟩
    have h2 : w s.toNNReal ≠ v₂ s.toNNReal := fun h => hs₂ ⟨hsI.1, hT, h⟩
    have hab : 0 < (v₁ s.toNNReal - w s.toNNReal) * (v₂ s.toNNReal - w s.toNNReal) := by
      rcases hside _ hT with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · exact mul_pos (sub_pos.2 (lt_of_le_of_ne a1 h1)) (sub_pos.2 (lt_of_le_of_ne a2 h2))
      · exact mul_pos_of_neg_of_neg (sub_neg.2 (lt_of_le_of_ne a1 (Ne.symm h1)))
          (sub_neg.2 (lt_of_le_of_ne a2 (Ne.symm h2)))
    have e : D s = (v₁ s.toNNReal - w s.toNNReal) - (v₂ s.toNNReal - w s.toNNReal) := by
      simp only [hDdef]; ring
    rw [e]
    exact mul_two_div_sub_two_div_nonpos hab
  have h0 := eq_zero_of_mul_integrand_nonpos (hint t ⟨t.2, le_rfl⟩) hD hsign t ⟨t.2, le_rfl⟩
  simp only [hDdef, Real.toNNReal_coe] at h0
  linarith

/-! ### Lusin–Souslin: a measurable left inverse -/

/-- **A measurable map from a standard Borel space, injective on a measurable set, has a measurable left inverse on
that set** (Lusin–Souslin, Mathlib's `Measurable.measurableEmbedding`). -/
theorem exists_measurable_leftInverse_of_injOn {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y] [Nonempty X] {F : X → Y}
    (hF : Measurable F) {A : Set X} (hA : MeasurableSet A) (hinj : InjOn F A) :
    ∃ G : Y → X, Measurable G ∧ ∀ x ∈ A, G (F x) = x := by
  have := hA.standardBorel
  have hf : Measurable (F ∘ ((↑) : A → X)) := hF.comp measurable_subtype_coe
  have hinj' : Function.Injective (F ∘ ((↑) : A → X)) := fun a b h => Subtype.ext (hinj a.2 b.2 h)
  obtain ⟨G, hG, hGe⟩ := (hf.measurableEmbedding hinj').exists_measurable_extend measurable_subtype_coe
    fun _ => inferInstance
  exact ⟨G, hG, fun x hx => congrFun hGe ⟨x, hx⟩⟩

end Exist

end InteractingSLE
