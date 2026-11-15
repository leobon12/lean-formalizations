/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.OneForceExists

/-!
# One force point: pathwise uniqueness of the evolution

Packet PROVE-SEC2-ONE. Specification p. 21 (`source/spec/p001-048.md` L484, "When there is only a
single force point, Theorem 2.2 follows from standard facts about Bessel processes"): an
integrated path of Definition 2.1 with one force point is determined by its driving path. Its
lifetime is the lifetime of the construction (2.3), and before it the path is (2.3).

* `IsKilledPath.unique`: two killed paths with the same data are equal before their lifetimes,
  and the lifetimes agree, given the threshold behaviour of each (the one coming from
  Definition 2.1 in the weak form `hE1`–`hE3`, the one of the construction in the strong form).
* `IsIntegratedSLEPath.threshold_left` / `threshold_right`: the threshold clauses of
  Definition 2.1 for `X = |V − W|/√a`.
* `IsIntegratedSLEPath.eq_left` / `eq_right`: **pathwise uniqueness** of the integrated path with
  one force point.

Everything here is deterministic.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace OneForce

variable {c x : ℝ} {b : ℝ≥0 → ℝ} {X X' : ℝ≥0 → ℝ} {ζ ζ' : ℝ≥0∞}

theorem isOpen_lt_coe (ζ : ℝ≥0∞) : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} :=
  isOpen_lt ENNReal.continuous_coe continuous_const

/-- If `X = X'` before `T < ζ'`, then `X` and `∫ X⁻¹` converge at `T⁻` to the values of `X'`. -/
theorem IsKilledPath.tendsto_of_eqOn (hX' : IsKilledPath c x b X' ζ') {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < ζ') (hagree : ∀ t : ℝ≥0, t < T → X t = X' t) :
    Tendsto X (𝓝[<] T) (𝓝 (X' T)) ∧
      Tendsto (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, (X s.toNNReal)⁻¹) (𝓝[<] T)
        (𝓝 (∫ s in (0 : ℝ)..T, (X' s.toNNReal)⁻¹)) := by
  have hnhds : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ'} ∈ 𝓝 T := (isOpen_lt_coe ζ').mem_nhds hT
  have hev : ∀ᶠ t in 𝓝[<] T, t < T := self_mem_nhdsWithin
  constructor
  · have h := ((hX'.continuousOn.continuousAt hnhds).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Iio T))
    exact h.congr' (hev.mono fun t ht => (hagree t ht).symm)
  · have hprim := continuousOn_primitive (g := fun s : ℝ => (X' s.toNNReal)⁻¹) (ζ := ζ')
      hX'.integrable
    have h := ((hprim.continuousAt hnhds).tendsto).mono_left (nhdsWithin_le_nhds (s := Iio T))
    refine h.congr' (hev.mono fun t ht => ?_)
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    rw [hagree _ (lt_of_le_of_lt (Real.toNNReal_le_iff_le_coe.2 hs.2) ht)]

/-- **Uniqueness of killed paths with the threshold behaviour of Definition 2.1.** `X` (with the
weak threshold clauses `hE1`–`hE3` that Definition 2.1 gives) and `X'` (with the strong clauses
of the construction (2.3)) have the same lifetime and agree before it. -/
theorem IsKilledPath.unique (hb : Continuous b) (hX : IsKilledPath c x b X ζ)
    (hE1 : c ≤ 0 → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → X t ≠ 0)
    (hE2 : ζ = 0 → x = 0 ∧ c ≤ 0)
    (hE3 : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∀ L I : ℝ, Tendsto X (𝓝[<] T) (𝓝 L) →
      Tendsto (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, (X s.toNNReal)⁻¹) (𝓝[<] T) (𝓝 I) →
      c ≤ 0 ∧ L = 0)
    (hX' : IsKilledPath c x b X' ζ')
    (hP1 : c ≤ 0 → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' → X' t ≠ 0)
    (hP2 : ζ' = 0 → x = 0 ∧ c ≤ 0)
    (hP3 : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ' → c ≤ 0 ∧ Tendsto X' (𝓝[<] T) (𝓝 0)) :
    ζ = ζ' ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → X t = X' t := by
  -- agreement before both lifetimes
  have hagree : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → (t : ℝ≥0∞) < ζ' → X t = X' t := by
    intro t ht ht'
    by_cases hc : 0 < c
    · exact hX.eq_of_pos hc hX' ht ht'
    have hc' : c ≤ 0 := not_lt.1 hc
    by_cases hxp : 0 < x
    · set w : ℝ → ℝ := fun s => b s.toNNReal with hwdef
      have hw : Continuous w := hb.comp continuous_real_toNNReal
      have hbw : (fun t : ℝ≥0 => w t) = b := funext fun t => by simp [hwdef]
      rw [← hbw] at hX hX'
      rw [(hX.eq_killPath hc' hxp hw (hE1 hc') ht).1, (hX'.eq_killPath hc' hxp hw (hP1 hc') ht').1]
    · exfalso
      have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by simp) ht
      have hX0 := hX.nonneg 0 h0
      rw [hX.zero] at hX0
      have hx0 : x = 0 := le_antisymm (not_lt.1 hxp) hX0
      exact hE1 hc' 0 h0 (by rw [hX.zero, hx0])
  have hlt_of : ∀ T : ℝ≥0, (T : ℝ≥0∞) ≤ ζ → (T : ℝ≥0∞) ≤ ζ' →
      ∀ t : ℝ≥0, t < T → X t = X' t := fun T hT hT' t ht =>
    hagree t (lt_of_lt_of_le (by exact_mod_cast ht) hT) (lt_of_lt_of_le (by exact_mod_cast ht) hT')
  have hζ : ζ = ζ' := by
    rcases lt_trichotomy ζ ζ' with h | h | h
    · exfalso
      obtain ⟨T, rfl⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ := ⟨ζ.toNNReal, ENNReal.coe_toNNReal h.ne_top⟩
      rcases (zero_le (a := T)).lt_or_eq with hT | hT
      · obtain ⟨L, hL⟩ := hX'.tendsto_of_eqOn h (hlt_of T le_rfl h.le)
        obtain ⟨hc, hL0⟩ := hE3 T hT rfl _ _ L hL
        exact hP1 hc T h hL0
      · subst hT
        obtain ⟨hx0, hc⟩ := hE2 (by simp)
        exact hP1 hc 0 h (by rw [hX'.zero, hx0])
    · exact h
    · exfalso
      obtain ⟨T, rfl⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ' :=
        ⟨ζ'.toNNReal, ENNReal.coe_toNNReal h.ne_top⟩
      rcases (zero_le (a := T)).lt_or_eq with hT | hT
      · obtain ⟨hc, hlim'⟩ := hP3 T hT rfl
        have hnhds : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} ∈ 𝓝 T := (isOpen_lt_coe ζ).mem_nhds h
        have hlim : Tendsto X (𝓝[<] T) (𝓝 (X T)) :=
          ((hX.continuousOn.continuousAt hnhds).tendsto).mono_left nhdsWithin_le_nhds
        have hlim2 : Tendsto X (𝓝[<] T) (𝓝 0) := hlim'.congr'
          (eventually_nhdsWithin_of_forall fun t ht => (hlt_of T h.le le_rfl t ht).symm)
        have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
        exact hE1 hc T h (tendsto_nhds_unique hlim hlim2)
      · subst hT
        obtain ⟨hx0, hc⟩ := hP2 (by simp)
        exact hE1 hc 0 h (by rw [hX.zero, hx0])
  exact ⟨hζ, fun t ht => hagree t ht (hζ ▸ ht)⟩


/-! ### Definition 2.1 with one force point: threshold clauses and uniqueness -/

section Evolution

variable {a : ℝ}

theorem leftV_congr {x₀ : ℝ} {ζ : ℝ≥0∞} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (h : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → X s = X' s) : leftV a x₀ X t = leftV a x₀ X' t := by
  unfold leftV
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le t.coe_nonneg] at hs
  rw [h _ (IsKilledPath.toNNReal_lt ht hs)]

theorem rightV_congr {x₀ : ℝ} {ζ : ℝ≥0∞} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (h : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → X s = X' s) : rightV a x₀ X t = rightV a x₀ X' t := by
  unfold rightV
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le t.coe_nonneg] at hs
  rw [h _ (IsKilledPath.toNNReal_lt ht hs)]

variable {w : ℝ≥0 → ℝ}

/-- **The threshold clauses of Definition 2.1, one force point on the left**, for the gap
`X = (W − V)/√a`. -/
theorem IsIntegratedSLEPath.threshold_left (ha : 0 < a) {xL : Fin 1 → ℝ} {xR : Fin 0 → ℝ}
    {ρL : Fin 1 → ℝ} {ρR : Fin 0 → ℝ} {vL : Fin 1 → ℝ≥0 → ℝ} {vR : Fin 0 → ℝ≥0 → ℝ}
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    ((ρL 0 + 2) / a ≤ 0 → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → (w t - vL 0 t) / Real.sqrt a ≠ 0) ∧
    (ζ = 0 → -xL 0 / Real.sqrt a = 0 ∧ (ρL 0 + 2) / a ≤ 0) ∧
    (∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∀ L I : ℝ,
      Tendsto (fun t => (w t - vL 0 t) / Real.sqrt a) (𝓝[<] T) (𝓝 L) →
      Tendsto (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, ((w s.toNNReal - vL 0 s.toNNReal) /
        Real.sqrt a)⁻¹) (𝓝[<] T) (𝓝 I) → (ρL 0 + 2) / a ≤ 0 ∧ L = 0) := by
  have hr0 : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hform := (isKilledPath_left ha h).2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnot, hzero, hlim⟩ := h
  refine ⟨fun hc t ht hX0 => ?_, fun hζ => ?_, fun T hT hTζ L I hXL hI => ?_⟩
  · have hwv : vL 0 t = w t := by
      rw [div_eq_zero_iff, or_iff_left hr0, sub_eq_zero] at hX0
      exact hX0.symm
    exact hnot t ht (thresholdCondition_left_iff.2 ⟨hwv, (div_nonpos_iff_le ha).1 hc⟩)
  · obtain ⟨hx, hρ⟩ := thresholdCondition_left_iff.1 (hzero hζ)
    exact ⟨by rw [hx]; simp, (div_nonpos_iff_le ha).2 hρ⟩
  · set X : ℝ≥0 → ℝ := fun t => (w t - vL 0 t) / Real.sqrt a with hXdef
    have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ :=
      eventually_nhdsWithin_of_forall fun t ht => by rw [← hTζ]; exact_mod_cast ht
    have hv : Tendsto (fun t => vL 0 t) (𝓝[<] T) (𝓝 (xL 0 - 2 / Real.sqrt a * I)) :=
      (tendsto_const_nhds.sub (hI.const_mul _)).congr'
        (hev.mono fun t ht => by show _ = vL 0 t; rw [(hform t ht).1, leftV_eq_sub])
    have hw : Tendsto w (𝓝[<] T) (𝓝 (xL 0 - 2 / Real.sqrt a * I + Real.sqrt a * L)) :=
      (hv.add (hXL.const_mul _)).congr' (Eventually.of_forall fun t => by
        show vL 0 t + Real.sqrt a * ((w t - vL 0 t) / Real.sqrt a) = w t
        field_simp
        ring)
    have hvL : Tendsto (fun t => fun i => vL i t) (𝓝[<] T)
        (𝓝 (fun _ : Fin 1 => xL 0 - 2 / Real.sqrt a * I)) :=
      tendsto_pi_nhds.2 fun i => by rw [Fin.fin_one_eq_zero i]; exact hv
    have hvR : Tendsto (fun t => fun i => vR i t) (𝓝[<] T) (𝓝 (fun i : Fin 0 => i.elim0)) :=
      tendsto_pi_nhds.2 fun i => i.elim0
    obtain ⟨heq, hρ⟩ := thresholdCondition_left_iff.1
      (hlim T hT hTζ _ _ _ (hw.prodMk_nhds (hvL.prodMk_nhds hvR)))
    refine ⟨(div_nonpos_iff_le ha).2 hρ, ?_⟩
    have : Real.sqrt a * L = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hr0

/-- **The threshold clauses of Definition 2.1, one force point on the right**, for the gap
`X = (V − W)/√a`. -/
theorem IsIntegratedSLEPath.threshold_right (ha : 0 < a) {xL : Fin 0 → ℝ} {xR : Fin 1 → ℝ}
    {ρL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ} {vL : Fin 0 → ℝ≥0 → ℝ} {vR : Fin 1 → ℝ≥0 → ℝ}
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    ((ρR 0 + 2) / a ≤ 0 → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → (vR 0 t - w t) / Real.sqrt a ≠ 0) ∧
    (ζ = 0 → xR 0 / Real.sqrt a = 0 ∧ (ρR 0 + 2) / a ≤ 0) ∧
    (∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∀ L I : ℝ,
      Tendsto (fun t => (vR 0 t - w t) / Real.sqrt a) (𝓝[<] T) (𝓝 L) →
      Tendsto (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, ((vR 0 s.toNNReal - w s.toNNReal) /
        Real.sqrt a)⁻¹) (𝓝[<] T) (𝓝 I) → (ρR 0 + 2) / a ≤ 0 ∧ L = 0) := by
  have hr0 : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hform := (isKilledPath_right ha h).2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnot, hzero, hlim⟩ := h
  refine ⟨fun hc t ht hX0 => ?_, fun hζ => ?_, fun T hT hTζ L I hXL hI => ?_⟩
  · have hwv : vR 0 t = w t := by
      rw [div_eq_zero_iff, or_iff_left hr0, sub_eq_zero] at hX0
      exact hX0
    exact hnot t ht (thresholdCondition_right_iff.2 ⟨hwv, (div_nonpos_iff_le ha).1 hc⟩)
  · obtain ⟨hx, hρ⟩ := thresholdCondition_right_iff.1 (hzero hζ)
    exact ⟨by rw [hx]; simp, (div_nonpos_iff_le ha).2 hρ⟩
  · have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ :=
      eventually_nhdsWithin_of_forall fun t ht => by rw [← hTζ]; exact_mod_cast ht
    have hv : Tendsto (fun t => vR 0 t) (𝓝[<] T) (𝓝 (xR 0 + 2 / Real.sqrt a * I)) :=
      (tendsto_const_nhds.add (hI.const_mul _)).congr'
        (hev.mono fun t ht => by show _ = vR 0 t; rw [(hform t ht).1, rightV_eq_add])
    have hw : Tendsto w (𝓝[<] T) (𝓝 (xR 0 + 2 / Real.sqrt a * I - Real.sqrt a * L)) :=
      (hv.sub (hXL.const_mul _)).congr' (Eventually.of_forall fun t => by
        show vR 0 t - Real.sqrt a * ((vR 0 t - w t) / Real.sqrt a) = w t
        field_simp
        ring)
    have hvR : Tendsto (fun t => fun i => vR i t) (𝓝[<] T)
        (𝓝 (fun _ : Fin 1 => xR 0 + 2 / Real.sqrt a * I)) :=
      tendsto_pi_nhds.2 fun i => by rw [Fin.fin_one_eq_zero i]; exact hv
    have hvL : Tendsto (fun t => fun i => vL i t) (𝓝[<] T) (𝓝 (fun i : Fin 0 => i.elim0)) :=
      tendsto_pi_nhds.2 fun i => i.elim0
    obtain ⟨heq, hρ⟩ := thresholdCondition_right_iff.1
      (hlim T hT hTζ _ _ _ (hw.prodMk_nhds (hvL.prodMk_nhds hvR)))
    refine ⟨(div_nonpos_iff_le ha).2 hρ, ?_⟩
    have : Real.sqrt a * L = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hr0

/-- **Pathwise uniqueness, one force point on the left.** An integrated path of Definition 2.1
driven by a continuous `b` has the lifetime of any killed path `X'` with the threshold behaviour
of (2.3) driven by `b`, and before it equals the construction (2.3) from `X'`. -/
theorem IsIntegratedSLEPath.eq_left (ha : 0 < a) {xL : Fin 1 → ℝ} {xR : Fin 0 → ℝ}
    {ρL : Fin 1 → ℝ} {ρR : Fin 0 → ℝ} {vL : Fin 1 → ℝ≥0 → ℝ} {vR : Fin 0 → ℝ≥0 → ℝ}
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hb : Continuous b)
    (hX' : IsKilledPath ((ρL 0 + 2) / a) (-xL 0 / Real.sqrt a) b X' ζ')
    (hP1 : (ρL 0 + 2) / a ≤ 0 → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' → X' t ≠ 0)
    (hP2 : ζ' = 0 → -xL 0 / Real.sqrt a = 0 ∧ (ρL 0 + 2) / a ≤ 0)
    (hP3 : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ' →
      (ρL 0 + 2) / a ≤ 0 ∧ Tendsto X' (𝓝[<] T) (𝓝 0)) :
    ζ = ζ' ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      w t = leftW a (xL 0) X' t ∧ vL 0 t = leftV a (xL 0) X' t := by
  obtain ⟨hK, hform⟩ := isKilledPath_left ha h
  obtain ⟨hE1, hE2, hE3⟩ := IsIntegratedSLEPath.threshold_left ha h
  obtain ⟨hζ, hagree⟩ := hK.unique hb hE1 hE2 hE3 hX' hP1 hP2 hP3
  refine ⟨hζ, fun t ht => ?_⟩
  have hV := leftV_congr (a := a) (x₀ := xL 0) ht hagree
  refine ⟨?_, by rw [(hform t ht).1, hV]⟩
  rw [(hform t ht).2, leftW, leftW, hV, hagree t ht]

/-- **Pathwise uniqueness, one force point on the right** (`X'` driven by `−b`). -/
theorem IsIntegratedSLEPath.eq_right (ha : 0 < a) {xL : Fin 0 → ℝ} {xR : Fin 1 → ℝ}
    {ρL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ} {vL : Fin 0 → ℝ≥0 → ℝ} {vR : Fin 1 → ℝ≥0 → ℝ}
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hb : Continuous b)
    (hX' : IsKilledPath ((ρR 0 + 2) / a) (xR 0 / Real.sqrt a) (fun t => -b t) X' ζ')
    (hP1 : (ρR 0 + 2) / a ≤ 0 → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' → X' t ≠ 0)
    (hP2 : ζ' = 0 → xR 0 / Real.sqrt a = 0 ∧ (ρR 0 + 2) / a ≤ 0)
    (hP3 : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ' →
      (ρR 0 + 2) / a ≤ 0 ∧ Tendsto X' (𝓝[<] T) (𝓝 0)) :
    ζ = ζ' ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      w t = rightW a (xR 0) X' t ∧ vR 0 t = rightV a (xR 0) X' t := by
  obtain ⟨hK, hform⟩ := isKilledPath_right ha h
  obtain ⟨hE1, hE2, hE3⟩ := IsIntegratedSLEPath.threshold_right ha h
  obtain ⟨hζ, hagree⟩ := hK.unique hb.neg hE1 hE2 hE3 hX' hP1 hP2 hP3
  refine ⟨hζ, fun t ht => ?_⟩
  have hV := rightV_congr (a := a) (x₀ := xR 0) ht hagree
  refine ⟨?_, by rw [(hform t ht).1, hV]⟩
  rw [(hform t ht).2, rightW, rightW, hV, hagree t ht]

end Evolution

end OneForce

end InteractingSLE
