/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import InteractingSLE.Frozen.Spec.IsIntegratedSLEPath

/-!
# Aux. lemma 54, empty seed sides: the marks are determined by the driver

Packet PROVE-LOCEXT-N. A mark of an integrated `SLE_κ(ρ)` path solves `v_t = x + ∫₀ᵗ 2/(v − w)`, stays on one side of
the driver and collides with it only on a Lebesgue-null set. Two such solutions for the same driver coincide (the
equation is singular at the start for a seed `x = w₀`, so the Lipschitz uniqueness does not apply): if `v₁ > v₂` on
`(s₀, t₀]` with `v₁(s₀) ≤ v₂(s₀)`, then a.e. on `(s₀, t₀)` both gaps have the same sign and `2/(v₁ − w) < 2/(v₂ − w)`,
so `(v₁ − v₂)(t₀) ≤ (v₁ − v₂)(s₀) ≤ 0`.

A second, measure-theoretic, fact (Lusin separation): on a standard Borel space, a measurable set that does not
distinguish points with the same value of a measurable map `f` into a Polish space is, on a measurable set of such
points, the preimage under `f` of a Borel set.

## Main results

* `le_of_singularMarkEq`, `eqOn_of_singularMarkEq`: uniqueness for the singular mark equation;
* `IsIntegratedSLEPath.vL_eq_of_w_eq`, `IsIntegratedSLEPath.vR_eq_of_w_eq`: two paths of infinite lifetime whose drivers
  agree on `[0, T]` have the same marks on `[0, T]`;
* `exists_measurableSet_preimage_of_saturated`: the separation step.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

/-! ### The singular mark equation -/

section Uniq

variable {w u₁ u₂ : ℝ → ℝ} {T : ℝ}

theorem two_div_sub_le_of_lt {a b : ℝ} (hab : b < a) (hp : 0 < a * b) : 2 / a ≤ 2 / b := by
  have ha : a ≠ 0 := by rintro rfl; simp at hp
  have hb : b ≠ 0 := by rintro rfl; simp at hp
  have e : 2 / b - 2 / a = 2 * (a - b) / (a * b) := by field_simp
  have : 0 ≤ 2 * (a - b) / (a * b) := div_nonneg (by linarith) hp.le
  linarith

/-- **Comparison for the singular mark equation**: two continuous solutions of `u t = u 0 + ∫₀ᵗ 2/(u − w)` on `[0, T]`
with the same start, integrable drifts and gaps of the same sign almost everywhere satisfy `u₁ ≤ u₂`. -/
theorem le_of_singularMarkEq (hc₁ : ContinuousOn u₁ (Icc 0 T)) (hc₂ : ContinuousOn u₂ (Icc 0 T))
    (h0 : u₁ 0 = u₂ 0)
    (he₁ : ∀ t ∈ Icc 0 T, u₁ t = u₁ 0 + ∫ s in (0 : ℝ)..t, 2 / (u₁ s - w s))
    (he₂ : ∀ t ∈ Icc 0 T, u₂ t = u₂ 0 + ∫ s in (0 : ℝ)..t, 2 / (u₂ s - w s))
    (hi₁ : IntervalIntegrable (fun s => 2 / (u₁ s - w s)) volume 0 T)
    (hi₂ : IntervalIntegrable (fun s => 2 / (u₂ s - w s)) volume 0 T)
    (hside : ∀ᵐ s ∂volume, s ∈ Icc 0 T → 0 < (u₁ s - w s) * (u₂ s - w s)) :
    ∀ t ∈ Icc 0 T, u₁ t ≤ u₂ t := by
  intro t₀ ht₀
  by_contra hlt
  push Not at hlt
  -- the last time before `t₀` with `u₁ ≤ u₂`
  set S : Set ℝ := Icc 0 t₀ ∩ {s | u₁ s - u₂ s ≤ 0} with hSdef
  have hsub : Icc 0 t₀ ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht₀.2
  have hcd : ContinuousOn (fun s => u₁ s - u₂ s) (Icc 0 t₀) := (hc₁.mono hsub).sub (hc₂.mono hsub)
  have hScl : IsClosed S := hcd.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, ht₀.1⟩, by simp [h0]⟩
  have hSbdd : BddAbove S := ⟨t₀, fun s hs => hs.1.2⟩
  set s₀ := sSup S with hs₀def
  have hs₀S : s₀ ∈ S := hScl.csSup_mem ⟨0, h0S⟩ hSbdd
  have hs₀0 : 0 ≤ s₀ := le_csSup hSbdd h0S
  have hs₀t : s₀ < t₀ := by
    refine lt_of_le_of_ne hs₀S.1.2 fun he => ?_
    have := hs₀S.2
    rw [he] at this
    simp only [mem_ofPred_eq] at this
    linarith
  have hgt : ∀ s, s₀ < s → s ≤ t₀ → u₂ s < u₁ s := by
    intro s hs hst
    by_contra hle
    push Not at hle
    have : s ∈ S := ⟨⟨hs₀0.trans hs.le, hst⟩, by simp only [mem_ofPred_eq]; linarith⟩
    exact absurd (le_csSup hSbdd this) (not_le.2 hs)
  -- the increments
  have hs₀I : s₀ ∈ Icc 0 T := ⟨hs₀0, hs₀t.le.trans ht₀.2⟩
  have hsubI : ∀ {a b : ℝ}, a ∈ Icc 0 T → b ∈ Icc 0 T → uIcc a b ⊆ uIcc 0 T := fun ha hb =>
    uIcc_subset_uIcc (by rw [uIcc_of_le (ha.1.trans ha.2)]; exact ha) (by rw [uIcc_of_le (hb.1.trans hb.2)]; exact hb)
  have h0I : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht₀.1.trans ht₀.2⟩
  have hinc : ∀ (u : ℝ → ℝ), (∀ t ∈ Icc 0 T, u t = u 0 + ∫ s in (0 : ℝ)..t, 2 / (u s - w s)) →
      IntervalIntegrable (fun s => 2 / (u s - w s)) volume 0 T →
      u t₀ - u s₀ = ∫ s in s₀..t₀, 2 / (u s - w s) := by
    intro u he hi
    rw [he t₀ ht₀, he s₀ hs₀I, add_sub_add_left_eq_sub]
    exact intervalIntegral.integral_interval_sub_left (hi.mono_set (hsubI h0I ht₀))
      (hi.mono_set (hsubI h0I hs₀I))
  have hd : (u₁ t₀ - u₂ t₀) - (u₁ s₀ - u₂ s₀) =
      ∫ s in s₀..t₀, (2 / (u₁ s - w s) - 2 / (u₂ s - w s)) := by
    rw [intervalIntegral.integral_sub (hi₁.mono_set (hsubI hs₀I ht₀)) (hi₂.mono_set (hsubI hs₀I ht₀)),
      ← hinc u₁ he₁ hi₁, ← hinc u₂ he₂ hi₂]
    ring
  have hnp : ∫ s in s₀..t₀, (2 / (u₁ s - w s) - 2 / (u₂ s - w s)) ≤ 0 := by
    have hne : ∀ᵐ s ∂volume, s ≠ s₀ := by
      rw [ae_iff]
      simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton]
    have hnn : 0 ≤ ∫ s in s₀..t₀, (2 / (u₂ s - w s) - 2 / (u₁ s - w s)) := by
      refine intervalIntegral.integral_nonneg_of_ae_restrict hs₀t.le ?_
      rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hside, hne] with s hs hsne hsI
      have hs' : s₀ < s := lt_of_le_of_ne hsI.1 (Ne.symm hsne)
      have hp := hs ⟨hs₀0.trans hs'.le, hsI.2.trans ht₀.2⟩
      have := two_div_sub_le_of_lt (show u₂ s - w s < u₁ s - w s by linarith [hgt s hs' hsI.2]) hp
      simp only [Pi.zero_apply]
      linarith
    have e : (fun s => 2 / (u₁ s - w s) - 2 / (u₂ s - w s)) =
        fun s => -(2 / (u₂ s - w s) - 2 / (u₁ s - w s)) := funext fun s => by ring
    rw [e, intervalIntegral.integral_neg]
    linarith
  have := hs₀S.2
  simp only [mem_ofPred_eq] at this
  linarith

/-- **Uniqueness for the singular mark equation.** -/
theorem eqOn_of_singularMarkEq (hc₁ : ContinuousOn u₁ (Icc 0 T)) (hc₂ : ContinuousOn u₂ (Icc 0 T))
    (h0 : u₁ 0 = u₂ 0)
    (he₁ : ∀ t ∈ Icc 0 T, u₁ t = u₁ 0 + ∫ s in (0 : ℝ)..t, 2 / (u₁ s - w s))
    (he₂ : ∀ t ∈ Icc 0 T, u₂ t = u₂ 0 + ∫ s in (0 : ℝ)..t, 2 / (u₂ s - w s))
    (hi₁ : IntervalIntegrable (fun s => 2 / (u₁ s - w s)) volume 0 T)
    (hi₂ : IntervalIntegrable (fun s => 2 / (u₂ s - w s)) volume 0 T)
    (hside : ∀ᵐ s ∂volume, s ∈ Icc 0 T → 0 < (u₁ s - w s) * (u₂ s - w s)) :
    EqOn u₁ u₂ (Icc 0 T) := fun t ht =>
  le_antisymm (le_of_singularMarkEq hc₁ hc₂ h0 he₁ he₂ hi₁ hi₂ hside t ht)
    (le_of_singularMarkEq hc₂ hc₁ h0.symm he₂ he₁ hi₂ hi₁
      (by filter_upwards [hside] with s hs hsI; rw [mul_comm]; exact hs hsI) t ht)

end Uniq

/-! ### Marks of two paths with the same driver -/

section Path

/-- **A mark is determined by the driver** (one mark of two paths): two continuous solutions of
`v t = x + ∫₀ᵗ 2/(v − w)` with integrable reciprocal gaps, null collision sets and gaps of the same sign wherever both are
nonzero, whose drivers agree on `[0, T]`, agree on `[0, T]`. -/
theorem mark_eq_of_w_eq {v v' w w' : ℝ≥0 → ℝ} {x : ℝ} {T : ℝ≥0} (hw : ∀ s ≤ T, w s = w' s)
    (hc : Continuous v) (hc' : Continuous v') (h0 : v 0 = x) (h0' : v' 0 = x)
    (he : ∀ t ≤ T, v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (he' : ∀ t ≤ T, v' t = x + ∫ s in (0 : ℝ)..t, 2 / (v' s.toNNReal - w' s.toNNReal))
    (hi : IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 T)
    (hi' : IntervalIntegrable (fun s : ℝ => (w' s.toNNReal - v' s.toNNReal)⁻¹) volume 0 T)
    (hcol : volume {s : ℝ | 0 ≤ s ∧ w s.toNNReal = v s.toNNReal} = 0)
    (hcol' : volume {s : ℝ | 0 ≤ s ∧ w' s.toNNReal = v' s.toNNReal} = 0)
    (hside : ∀ s ≤ T, v s ≠ w s → v' s ≠ w' s → 0 < (v s - w s) * (v' s - w' s)) :
    ∀ s ≤ T, v s = v' s := by
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  set u₁ : ℝ → ℝ := fun s => v s.toNNReal with hu₁def
  set u₂ : ℝ → ℝ := fun s => v' s.toNNReal with hu₂def
  have hTI : ∀ {s : ℝ}, s ∈ Icc (0 : ℝ) T → s.toNNReal ≤ T := fun hs =>
    Real.toNNReal_le_iff_le_coe.2 hs.2
  have hwW : ∀ s ∈ Icc (0 : ℝ) T, w' s.toNNReal = W s := fun s hs => (hw _ (hTI hs)).symm
  have hgap : ∀ (u : ℝ → ℝ) (ww : ℝ → ℝ), (fun s => 2 / (u s - ww s)) = fun s => -2 * (ww s - u s)⁻¹ :=
    fun u ww => funext fun s => by rw [div_eq_mul_inv, ← neg_sub, inv_neg]; ring
  have hcoeT : ∀ {t : ℝ}, t ∈ Icc (0 : ℝ) T → ((t.toNNReal : ℝ≥0) : ℝ) = t := fun ht =>
    Real.coe_toNNReal _ ht.1
  have hEq := eqOn_of_singularMarkEq (w := W) (u₁ := u₁) (u₂ := u₂) (T := (T : ℝ))
    (hc.comp continuous_real_toNNReal).continuousOn (hc'.comp continuous_real_toNNReal).continuousOn
    (by simp only [hu₁def, hu₂def, Real.toNNReal_zero, h0, h0'])
    (fun t ht => by
      simp only [hu₁def, Real.toNNReal_zero, h0]
      have := he t.toNNReal (hTI ht)
      rwa [hcoeT ht] at this)
    (fun t ht => by
      simp only [hu₂def, Real.toNNReal_zero, h0']
      have := he' t.toNNReal (hTI ht)
      rw [hcoeT ht] at this
      rw [this]
      congr 1
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' : s ∈ Icc (0 : ℝ) T := by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      simp only [hwW s hs'])
    (by rw [hgap]; exact hi.const_mul _)
    (by
      rw [hgap]
      refine (hi'.const_mul (-2)).congr fun s hs => ?_
      have hs' : s ∈ Icc (0 : ℝ) T := by
        rw [uIoc_of_le (NNReal.coe_nonneg T)] at hs
        exact ⟨hs.1.le, hs.2⟩
      simp only [hwW s hs', hu₂def])
    (by
      have h1 := measure_eq_zero_iff_ae_notMem.1 hcol
      have h2 := measure_eq_zero_iff_ae_notMem.1 hcol'
      filter_upwards [h1, h2] with s hs1 hs2 hsI
      have hn1 : v s.toNNReal ≠ w s.toNNReal := fun h => hs1 ⟨hsI.1, h.symm⟩
      have hn2 : v' s.toNNReal ≠ w' s.toNNReal := fun h => hs2 ⟨hsI.1, h.symm⟩
      have := hside s.toNNReal (hTI hsI) hn1 hn2
      simp only [hu₁def, hu₂def, hWdef]
      rw [← hw _ (hTI hsI)] at this; exact this)
  intro s hs
  have := hEq (show (s : ℝ) ∈ Icc (0 : ℝ) T from ⟨s.2, by exact_mod_cast hs⟩)
  simpa only [hu₁def, hu₂def, Real.toNNReal_coe] using this

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ} {b b' : ℝ≥0 → ℝ}

theorem continuous_of_continuousOn_top {f : ℝ≥0 → ℝ} (h : ContinuousOn f {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤}) :
    Continuous f := by
  have e : {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun t => ENNReal.coe_lt_top
  rw [e] at h
  exact continuousOn_univ.1 h

theorem collision_eq_of_top {w v : ℝ≥0 → ℝ} :
    {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ⊤ ∧ w s.toNNReal = v s.toNNReal} =
      {s : ℝ | 0 ≤ s ∧ w s.toNNReal = v s.toNNReal} := by
  ext s
  simp only [mem_ofPred_eq, ENNReal.coe_lt_top, true_and]

/-- **The left marks of two paths with infinite lifetime are determined by the driver on `[0, T]`.** -/
theorem IsIntegratedSLEPath.vL_eq_of_w_eq (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ⊤)
    (hp' : IsIntegratedSLEPath a xL xR ρL ρR w' vL' vR' b' ⊤) {T : ℝ≥0} (hw : ∀ s ≤ T, w s = w' s) (i : Fin nL) :
    ∀ s ≤ T, vL i s = vL' i s := by
  obtain ⟨-, hv0, -, -, hc, -, -, hle, -, -, hi, -, -, he, -, hcol, -⟩ := hp
  obtain ⟨-, hv0', -, -, hc', -, -, hle', -, -, hi', -, -, he', -, hcol', -⟩ := hp'
  refine mark_eq_of_w_eq hw (continuous_of_continuousOn_top (hc i)) (continuous_of_continuousOn_top (hc' i))
    (hv0 i) (hv0' i) (fun t _ => he t ENNReal.coe_lt_top i) (fun t _ => he' t ENNReal.coe_lt_top i)
    (hi T ENNReal.coe_lt_top i) (hi' T ENNReal.coe_lt_top i) (by rw [← collision_eq_of_top]; exact hcol i)
    (by rw [← collision_eq_of_top]; exact hcol' i) fun s _ h1 h2 => ?_
  have a1 := hle s ENNReal.coe_lt_top i
  have a2 := hle' s ENNReal.coe_lt_top i
  exact mul_pos_of_neg_of_neg (sub_neg.2 (lt_of_le_of_ne a1 h1)) (sub_neg.2 (lt_of_le_of_ne a2 h2))

/-- **The right marks of two paths with infinite lifetime are determined by the driver on `[0, T]`.** -/
theorem IsIntegratedSLEPath.vR_eq_of_w_eq (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ⊤)
    (hp' : IsIntegratedSLEPath a xL xR ρL ρR w' vL' vR' b' ⊤) {T : ℝ≥0} (hw : ∀ s ≤ T, w s = w' s) (i : Fin nR) :
    ∀ s ≤ T, vR i s = vR' i s := by
  obtain ⟨-, -, hv0, -, -, hc, -, -, hle, -, -, hi, -, -, he, -, hcol, -⟩ := hp
  obtain ⟨-, -, hv0', -, -, hc', -, -, hle', -, -, hi', -, -, he', -, hcol', -⟩ := hp'
  refine mark_eq_of_w_eq hw (continuous_of_continuousOn_top (hc i)) (continuous_of_continuousOn_top (hc' i))
    (hv0 i) (hv0' i) (fun t _ => he t ENNReal.coe_lt_top i) (fun t _ => he' t ENNReal.coe_lt_top i)
    (hi T ENNReal.coe_lt_top i) (hi' T ENNReal.coe_lt_top i) (by rw [← collision_eq_of_top]; exact hcol i)
    (by rw [← collision_eq_of_top]; exact hcol' i) fun s _ h1 h2 => ?_
  have a1 := hle s ENNReal.coe_lt_top i
  have a2 := hle' s ENNReal.coe_lt_top i
  exact mul_pos (sub_pos.2 (lt_of_le_of_ne a1 (Ne.symm h1))) (sub_pos.2 (lt_of_le_of_ne a2 (Ne.symm h2)))

end Path

/-! ### Lusin separation -/

section Separation

/-- **Saturated sets are preimages** (Lusin separation): on a standard Borel space, if a measurable set `A` does not
distinguish points of a measurable set `G` with the same value of a measurable map `f` into a Polish space, then on `G`
the set `A` is the preimage under `f` of a Borel set. -/
theorem exists_measurableSet_preimage_of_saturated {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {Y : Type*} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y] {f : Ω → Y}
    (hf : Measurable f) {G A : Set Ω} (hG : MeasurableSet G) (hA : MeasurableSet A)
    (hsat : ∀ ω ∈ G, ∀ ω' ∈ G, f ω = f ω' → ω ∈ A → ω' ∈ A) :
    ∃ Γ : Set Y, MeasurableSet Γ ∧ ∀ ω ∈ G, (ω ∈ A ↔ f ω ∈ Γ) := by
  have h₁ : AnalyticSet (f '' (G ∩ A)) := (hG.inter hA).analyticSet_image hf
  have h₂ : AnalyticSet (f '' (G \ A)) := (hG.diff hA).analyticSet_image hf
  have hdisj : Disjoint (f '' (G ∩ A)) (f '' (G \ A)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨ω, ⟨hωG, hωA⟩, rfl⟩ ⟨ω', ⟨hω'G, hω'A⟩, he⟩
    exact hω'A (hsat ω hωG ω' hω'G he.symm hωA)
  obtain ⟨u, hsu, htu, hu⟩ := h₁.measurablySeparable h₂ hdisj
  refine ⟨u, hu, fun ω hω => ⟨fun hωA => hsu ⟨ω, ⟨hω, hωA⟩, rfl⟩, fun hωu => ?_⟩⟩
  by_contra hωA
  exact Set.disjoint_left.1 htu ⟨ω, ⟨hω, hωA⟩, rfl⟩ hωu

end Separation

end LocalExt

end InteractingSLE
