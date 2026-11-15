/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.ItoAdapted

/-!
# Itô's formula for a random field up to a stopping time

Packet PROVE-ZHAN-GT4-A5 (Astra, *Follow-up proofs*, Part A.1.3, `source/external/AstraIG1/ig1_followup_proofs.txt`
L333–L341: the factors of the dual-coupling density have uniform bounds only on a *protected rectangle*, i.e. up to the
first exit `S` of the hull from its enclosure). This file proves the random-field Itô formula of
`Stochastic/ItoAdapted.lean` for a field that is regular only up to a stopping time `S`:

**`integral_mul_fieldStopped_sub_eq_zero`.** Let `B` be an `𝓕`-Brownian motion with continuous paths, `s ≤ t`, and
`S ≥ s` an `𝓕`-stopping time. Suppose that for every `ω` the fields `Φ, Φ₁, Φ₂, Ψ` satisfy the hypotheses of
`integral_mul_fieldIncr_eq_zero` on the random time interval `[s, t ∧ S(ω)]` only (space derivatives, `C`-Lipschitz
`Φ₂`, time derivative `Ψ`, joint continuity of `Ψ, Φ₂`, bounds by `C`), that `Φ₁(r, B_r)` and `Φ₂(r, B_r)` are
`𝓕_r`-measurable, and that the stopped process is measurable. Then, for the stopped process
`X_r = Φ(r ∧ S, B_{r ∧ S}) − ∫_s^{r ∧ S} (Ψ(u, B_u) + ½ Φ₂(u, B_u)) du` (`fieldStopped`),
`E[ξ (X_t − X_s)] = 0` for every `𝓕_s`-measurable `|ξ| ≤ 1`.

The proof feeds the abstract engine `integral_mul_sub_eq_zero_of_defectExcess` with the frozen coefficients
`1{r < S} Φ₁(r, B_r)`, `1{r < S} Φ₂(r, B_r)`: cells before `S` are controlled by the pathwise Taylor step, cells after
`S` have zero defect, and the single cell containing `S` has a bounded defect that tends to `0` along every path.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Ito

section Stopped

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

/-- The random-field process stopped at `S`:
`Φ(r ∧ S, B_{r ∧ S}) − ∫_s^{r ∧ S} (Ψ(u, B_u) + ½ Φ₂(u, B_u)) du`. -/
def fieldStopped (Φ Φ2 Ψ : ℝ → Ω → ℝ → ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (s : ℝ) (r : ℝ≥0)
    (ω : Ω) : ℝ :=
  Φ ((min r (S ω) : ℝ≥0) : ℝ) ω (B (min r (S ω)) ω) -
    ∫ u in s..((min r (S ω) : ℝ≥0) : ℝ), fieldGen Φ2 Ψ B u ω

/-- The frozen coefficient stopped at `S`: `1{r < S} F(r, B_r)`. -/
def stopCoef (F : ℝ → Ω → ℝ → ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (r : ℝ≥0) (ω : Ω) : ℝ :=
  if r < S ω then F r ω (B r ω) else 0

theorem abs_le_one_add_abs_pow_three (x : ℝ) : |x| ≤ 1 + |x| ^ 3 := by
  rcases le_total |x| 1 with h | h
  · have : 0 ≤ |x| ^ 3 := by positivity
    linarith
  · have h1 : 1 ≤ |x| ^ 2 := by nlinarith
    have h2 : |x| ≤ |x| ^ 3 := by
      calc |x| = |x| * 1 := (mul_one _).symm
        _ ≤ |x| * |x| ^ 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg x)
        _ = |x| ^ 3 := by ring
    linarith

theorem sq_le_one_add_abs_pow_three (x : ℝ) : x ^ 2 ≤ 1 + |x| ^ 3 := by
  rw [← sq_abs]
  rcases le_total |x| 1 with h | h
  · have : |x| ^ 2 ≤ 1 := by nlinarith [abs_nonneg x]
    have : 0 ≤ |x| ^ 3 := by positivity
    linarith
  · have h2 : |x| ^ 2 ≤ |x| ^ 3 := by
      calc |x| ^ 2 = |x| ^ 2 * 1 := (mul_one _).symm
        _ ≤ |x| ^ 2 * |x| := mul_le_mul_of_nonneg_left h (by positivity)
        _ = |x| ^ 3 := by ring
    linarith

/-- Lipschitz bound in space from a bounded derivative. -/
theorem abs_sub_le_of_hasDerivAt {f f' : ℝ → ℝ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hb : ∀ x, |f' x| ≤ C) (x y : ℝ) : |f y - f x| ≤ C * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := univ) (f := f)
    (fun z _ => (hf z).hasDerivWithinAt) (fun z _ => by rw [Real.norm_eq_abs]; exact hb z)
    convex_univ (mem_univ x) (mem_univ y)
  simpa only [Real.norm_eq_abs] using h

/-- Lipschitz bound in time from a bounded time derivative (integrated form). -/
theorem abs_integral_le_of_abs_le {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (hb : ∀ u ∈ Icc a b, |g u| ≤ C) : |∫ u in a..b, g u| ≤ C * (b - a) := by
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) fun u hu => ?_).trans_eq ?_
  · rw [uIoc_of_le hab] at hu
    rw [Real.norm_eq_abs]; exact hb u ⟨hu.1.le, hu.2⟩
  · rw [abs_of_nonneg (sub_nonneg.2 hab)]

end Stopped

/-! ### The three kinds of cells, along one path -/

section Cells

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {Φ Φ1 Φ2 Ψ : ℝ → Ω → ℝ → ℝ} {S : Ω → ℝ≥0} {s t : ℝ≥0} {C : ℝ}
  {ω : Ω}

/-- The generator along the path is continuous on any time interval where `Ψ, Φ₂` are jointly continuous. -/
theorem continuousOn_fieldGen {I : Set ℝ} (hBc : Continuous (B · ω))
    (hΨc : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω p.2) (I ×ˢ univ))
    (hΦ2c : ContinuousOn (fun p : ℝ × ℝ => Φ2 p.1 ω p.2) (I ×ˢ univ)) :
    ContinuousOn (fun u => fieldGen Φ2 Ψ B u ω) I := by
  have hβ : ContinuousOn (fun r : ℝ => B r.toNNReal ω) I :=
    (hBc.comp continuous_real_toNNReal).continuousOn
  exact (continuousOn_field_path (ψ := fun u x => Ψ u ω x) hΨc hβ).add
    (continuousOn_const.mul (continuousOn_field_path (ψ := fun u x => Φ2 u ω x) hΦ2c hβ))

/-- Before the stopping time the stopped process has the increments of the unstopped one. -/
theorem fieldStopped_sub_of_le {a b : ℝ≥0} (hsa : s ≤ a) (hab : a ≤ b) (hbS : b ≤ S ω)
    (hBc : Continuous (B · ω))
    (hΨc : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω p.2) (Icc (s : ℝ) b ×ˢ univ))
    (hΦ2c : ContinuousOn (fun p : ℝ × ℝ => Φ2 p.1 ω p.2) (Icc (s : ℝ) b ×ˢ univ)) :
    fieldStopped Φ Φ2 Ψ B S s b ω - fieldStopped Φ Φ2 Ψ B S s a ω =
      Φ b ω (B b ω) - Φ a ω (B a ω) - ∫ u in (a : ℝ)..b, fieldGen Φ2 Ψ B u ω := by
  have hgc := continuousOn_fieldGen hBc hΨc hΦ2c
  have hsb : (s : ℝ) ≤ b := NNReal.coe_le_coe.2 (hsa.trans hab)
  have hi1 : IntervalIntegrable (fun u => fieldGen Φ2 Ψ B u ω) volume (s : ℝ) b :=
    hgc.intervalIntegrable_of_Icc hsb
  have hi2 : IntervalIntegrable (fun u => fieldGen Φ2 Ψ B u ω) volume (s : ℝ) a :=
    (hgc.mono (Icc_subset_Icc le_rfl (NNReal.coe_le_coe.2 hab))).intervalIntegrable_of_Icc
      (NNReal.coe_le_coe.2 hsa)
  have h := intervalIntegral.integral_interval_sub_left hi1 hi2
  unfold fieldStopped
  rw [min_eq_left hbS, min_eq_left (hab.trans hbS), ← h]; ring

/-- **A cell before the stopping time**: the pathwise Taylor step. -/
theorem abs_itoDefect_stopped_le_of_le {a b : ℝ≥0} (hsa : s ≤ a) (hab : a ≤ b) (haS : a < S ω)
    (hbS : b ≤ S ω) (hbt : b ≤ t) (hBc : Continuous (B · ω))
    (hd1 : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, HasDerivAt (Φ r ω) (Φ1 r ω x) x)
    (hd2 : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, HasDerivAt (Φ1 r ω) (Φ2 r ω x) x)
    (hlip : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x y, |Φ2 r ω x - Φ2 r ω y| ≤ C * |x - y|)
    (htime : ∀ x a b : ℝ, (s : ℝ) ≤ a → a ≤ b → b ≤ min t (S ω) →
      Φ b ω x - Φ a ω x = ∫ u in a..b, Ψ u ω x)
    (hΨc : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω p.2) (Icc (s : ℝ) (min t (S ω)) ×ˢ univ))
    (hΦ2c : ContinuousOn (fun p : ℝ × ℝ => Φ2 p.1 ω p.2) (Icc (s : ℝ) (min t (S ω)) ×ˢ univ)) :
    |itoDefect (fieldStopped Φ Φ2 Ψ B S s) (stopCoef Φ1 B S) (stopCoef Φ2 B S) B a b ω| ≤
      C * |B b ω - B a ω| ^ 3 + fieldStepRem (fun u x => Ψ u ω x) (fun u x => Φ2 u ω x)
        (fun r => B r.toNNReal ω) a b := by
  have hbτ : (b : ℝ) ≤ min (t : ℝ) (S ω) := le_min (NNReal.coe_le_coe.2 hbt) (NNReal.coe_le_coe.2 hbS)
  have hsub : Icc (a : ℝ) b ⊆ Icc (s : ℝ) (min t (S ω)) :=
    Icc_subset_Icc (NNReal.coe_le_coe.2 hsa) hbτ
  have hsubb : Icc (s : ℝ) b ⊆ Icc (s : ℝ) (min t (S ω)) := Icc_subset_Icc le_rfl hbτ
  have hmem : (a : ℝ) ∈ Icc (s : ℝ) (min t (S ω)) := hsub (left_mem_Icc.2 (NNReal.coe_le_coe.2 hab))
  have hstep := field_pathwise_step (Φ := fun r x => Φ r ω x) (Φ1 := fun r x => Φ1 r ω x)
    (Φ2 := fun r x => Φ2 r ω x) (Ψ := fun r x => Ψ r ω x) (β := fun r => B r.toNNReal ω)
    (C := C) (NNReal.coe_le_coe.2 hab) (fun x => hd1 _ hmem x) (fun x => hd2 _ hmem x)
    (hlip _ hmem) (htime _ _ _ hmem.1 (NNReal.coe_le_coe.2 hab) hbτ)
    (hΨc.mono (prod_mono hsub le_rfl)) (hΦ2c.mono (prod_mono hsub le_rfl))
    ((hBc.comp continuous_real_toNNReal).continuousOn)
  simp only [Real.toNNReal_coe] at hstep
  have hX := fieldStopped_sub_of_le (Φ := Φ) hsa hab hbS hBc (hΨc.mono (prod_mono hsubb le_rfl))
    (hΦ2c.mono (prod_mono hsubb le_rfl))
  simp only [itoDefect, stopCoef, haS, ite_true]
  rw [hX]
  exact hstep

/-- **A cell after the stopping time** has zero defect. -/
theorem itoDefect_stopped_eq_zero_of_le {a b : ℝ≥0} (hab : a ≤ b) (hSa : S ω ≤ a) :
    itoDefect (fieldStopped Φ Φ2 Ψ B S s) (stopCoef Φ1 B S) (stopCoef Φ2 B S) B a b ω = 0 := by
  have h1 : ¬ a < S ω := not_lt.2 hSa
  unfold itoDefect fieldStopped stopCoef
  rw [min_eq_right hSa, min_eq_right (hSa.trans hab)]
  simp only [h1, ite_false]
  ring

/-- The stopped process is bounded by `C + (3C/2)(t − s)` on `[s, t]`. -/
theorem abs_fieldStopped_le {r : ℝ≥0} (hsr : s ≤ r) (hrt : r ≤ t) (hsS : s ≤ S ω)
    (hb0 : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Φ r ω x| ≤ C)
    (hb2 : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Φ2 r ω x| ≤ C)
    (hbΨ : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Ψ r ω x| ≤ C) :
    |fieldStopped Φ Φ2 Ψ B S s r ω| ≤ C + 3 * C / 2 * ((t : ℝ) - s) := by
  set m := min r (S ω) with hm
  have hsm : s ≤ m := le_min hsr hsS
  have hmτ : (m : ℝ) ≤ min (t : ℝ) (S ω) :=
    le_min (NNReal.coe_le_coe.2 ((min_le_left _ _).trans hrt)) (NNReal.coe_le_coe.2 (min_le_right _ _))
  have hmem : (m : ℝ) ∈ Icc (s : ℝ) (min t (S ω)) := ⟨NNReal.coe_le_coe.2 hsm, hmτ⟩
  have hmt : (m : ℝ) ≤ t := hmτ.trans (min_le_left _ _)
  have hI : |∫ u in (s : ℝ)..m, fieldGen Φ2 Ψ B u ω| ≤ (C + 1 / 2 * C) * ((m : ℝ) - s) := by
    refine abs_integral_le_of_abs_le (NNReal.coe_le_coe.2 hsm) fun u hu => ?_
    have hu' : u ∈ Icc (s : ℝ) (min t (S ω)) := ⟨hu.1, hu.2.trans hmτ⟩
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact add_le_add (hbΨ u hu' _) (mul_le_mul_of_nonneg_left (hb2 u hu' _) (by norm_num))
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb0 _ hmem 0)
  have h0 := hb0 _ hmem (B m ω)
  unfold fieldStopped
  rw [← hm]
  refine (abs_sub _ _).trans ?_
  have : (C + 1 / 2 * C) * ((m : ℝ) - s) ≤ 3 * C / 2 * ((t : ℝ) - s) := by
    have : (m : ℝ) - s ≤ (t : ℝ) - s := by linarith
    have h3 : 0 ≤ (m : ℝ) - s := sub_nonneg.2 (NNReal.coe_le_coe.2 hsm)
    nlinarith
  linarith

/-- The stopped coefficient is bounded by `C` on `[s, t]`. -/
theorem abs_stopCoef_le {F : ℝ → Ω → ℝ → ℝ} {r : ℝ≥0} (hsr : s ≤ r) (hrt : r ≤ t) (hC0 : 0 ≤ C)
    (hb : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |F r ω x| ≤ C) :
    |stopCoef F B S r ω| ≤ C := by
  unfold stopCoef
  split_ifs with h
  · exact hb _ ⟨NNReal.coe_le_coe.2 hsr, le_min (NNReal.coe_le_coe.2 hrt) (NNReal.coe_le_coe.2 h.le)⟩ _
  · simpa using hC0

/-- **The crude bound on any cell**: `|defect| ≤ 4C + 4C(t − s) + 2C |ΔB|³`. -/
theorem abs_itoDefect_stopped_le_crude {a b : ℝ≥0} (hsa : s ≤ a) (hab : a ≤ b) (hbt : b ≤ t)
    (hsS : s ≤ S ω)
    (hb0 : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Φ r ω x| ≤ C)
    (hb1 : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Φ1 r ω x| ≤ C)
    (hb2 : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Φ2 r ω x| ≤ C)
    (hbΨ : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Ψ r ω x| ≤ C) :
    |itoDefect (fieldStopped Φ Φ2 Ψ B S s) (stopCoef Φ1 B S) (stopCoef Φ2 B S) B a b ω| ≤
      (4 * C + 4 * C * ((t : ℝ) - s)) + 2 * C * |B b ω - B a ω| ^ 3 := by
  have hs0 : (s : ℝ) ∈ Icc (s : ℝ) (min t (S ω)) :=
    ⟨le_rfl, le_min (NNReal.coe_le_coe.2 (hsa.trans (hab.trans hbt))) (NNReal.coe_le_coe.2 hsS)⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb0 _ hs0 0)
  have hXa := abs_fieldStopped_le (B := B) (Φ := Φ) hsa (hab.trans hbt) hsS hb0 hb2 hbΨ
  have hXb := abs_fieldStopped_le (B := B) (Φ := Φ) (hsa.trans hab) hbt hsS hb0 hb2 hbΨ
  have hc1 := abs_stopCoef_le (B := B) (S := S) hsa (hab.trans hbt) hC0 hb1
  have hc2 := abs_stopCoef_le (B := B) (S := S) hsa (hab.trans hbt) hC0 hb2
  set Δ := B b ω - B a ω
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (NNReal.coe_le_coe.2 (hsa.trans (hab.trans hbt)))
  have hba : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.2 (NNReal.coe_le_coe.2 hab)
  have hbats : (b : ℝ) - a ≤ (t : ℝ) - s := by
    have := NNReal.coe_le_coe.2 hsa; have := NNReal.coe_le_coe.2 hbt; linarith
  have h1 := abs_le_one_add_abs_pow_three Δ
  have h2 := sq_le_one_add_abs_pow_three Δ
  have hΔ3 : 0 ≤ |Δ| ^ 3 := by positivity
  have hq : |Δ ^ 2 - ((b : ℝ) - a)| ≤ Δ ^ 2 + ((b : ℝ) - a) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hba]
  have e1 : |stopCoef Φ1 B S a ω * Δ| ≤ C * |Δ| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
  have e2 : |1 / 2 * stopCoef Φ2 B S a ω * (Δ ^ 2 - ((b : ℝ) - a))| ≤
      1 / 2 * C * (Δ ^ 2 + ((b : ℝ) - a)) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hc2 hq (abs_nonneg _) hC0) (by norm_num)
  unfold itoDefect
  calc _ ≤ |fieldStopped Φ Φ2 Ψ B S s b ω| + |fieldStopped Φ Φ2 Ψ B S s a ω| +
        |stopCoef Φ1 B S a ω * Δ| + |1 / 2 * stopCoef Φ2 B S a ω * (Δ ^ 2 - ((b : ℝ) - a))| := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
          (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ (C + 3 * C / 2 * ((t : ℝ) - s)) + (C + 3 * C / 2 * ((t : ℝ) - s)) + C * |Δ| +
        1 / 2 * C * (Δ ^ 2 + ((b : ℝ) - a)) := by gcongr
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h1 hC0, mul_le_mul_of_nonneg_left h2 hC0,
        mul_le_mul_of_nonneg_left hbats hC0]

/-- **The cell containing the stopping time** has a small defect:
`|defect| ≤ 3C (b − a) + C |B_S − B_a| + C |ΔB| + (C/2) ΔB²`. -/
theorem abs_itoDefect_stopped_le_of_mem {a b : ℝ≥0} (hsa : s ≤ a) (haS : a < S ω) (hSb : S ω < b)
    (hbt : b ≤ t) (hBc : Continuous (B · ω))
    (hd1 : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, HasDerivAt (Φ r ω) (Φ1 r ω x) x)
    (htime : ∀ x a b : ℝ, (s : ℝ) ≤ a → a ≤ b → b ≤ min t (S ω) →
      Φ b ω x - Φ a ω x = ∫ u in a..b, Ψ u ω x)
    (hΨc : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω p.2) (Icc (s : ℝ) (min t (S ω)) ×ˢ univ))
    (hΦ2c : ContinuousOn (fun p : ℝ × ℝ => Φ2 p.1 ω p.2) (Icc (s : ℝ) (min t (S ω)) ×ˢ univ))
    (hb1 : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Φ1 r ω x| ≤ C)
    (hb2 : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Φ2 r ω x| ≤ C)
    (hbΨ : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Ψ r ω x| ≤ C) :
    |itoDefect (fieldStopped Φ Φ2 Ψ B S s) (stopCoef Φ1 B S) (stopCoef Φ2 B S) B a b ω| ≤
      3 * C * ((b : ℝ) - a) + C * |B (S ω) ω - B a ω| + C * |B b ω - B a ω| +
        C / 2 * (B b ω - B a ω) ^ 2 := by
  have hSt : S ω ≤ t := hSb.le.trans hbt
  have hτ : min (t : ℝ) (S ω) = S ω := min_eq_right (NNReal.coe_le_coe.2 hSt)
  have hmemS : (S ω : ℝ) ∈ Icc (s : ℝ) (min t (S ω)) :=
    ⟨NNReal.coe_le_coe.2 (hsa.trans haS.le), hτ.ge⟩
  have hmema : (a : ℝ) ∈ Icc (s : ℝ) (min t (S ω)) :=
    ⟨NNReal.coe_le_coe.2 hsa, by rw [hτ]; exact NNReal.coe_le_coe.2 haS.le⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb1 _ hmema 0)
  have haS' : (a : ℝ) ≤ S ω := NNReal.coe_le_coe.2 haS.le
  have hSb' : (S ω : ℝ) ≤ b := NNReal.coe_le_coe.2 hSb.le
  have hsubI : Icc (a : ℝ) (S ω) ⊆ Icc (s : ℝ) (min t (S ω)) := by
    rw [hτ]; exact Icc_subset_Icc (NNReal.coe_le_coe.2 hsa) le_rfl
  -- the increment of the stopped process
  have hgc : ContinuousOn (fun u => fieldGen Φ2 Ψ B u ω) (Icc (s : ℝ) (S ω)) := by
    have h := continuousOn_fieldGen hBc hΨc hΦ2c
    rwa [hτ] at h
  have hX : fieldStopped Φ Φ2 Ψ B S s b ω - fieldStopped Φ Φ2 Ψ B S s a ω =
      Φ (S ω) ω (B (S ω) ω) - Φ a ω (B a ω) - ∫ u in (a : ℝ)..(S ω), fieldGen Φ2 Ψ B u ω := by
    have hi1 : IntervalIntegrable (fun u => fieldGen Φ2 Ψ B u ω) volume (s : ℝ) (S ω) :=
      hgc.intervalIntegrable_of_Icc (NNReal.coe_le_coe.2 (hsa.trans haS.le))
    have hi2 : IntervalIntegrable (fun u => fieldGen Φ2 Ψ B u ω) volume (s : ℝ) a :=
      (hgc.mono (Icc_subset_Icc le_rfl haS')).intervalIntegrable_of_Icc (NNReal.coe_le_coe.2 hsa)
    have h := intervalIntegral.integral_interval_sub_left hi1 hi2
    unfold fieldStopped
    rw [min_eq_right hSb.le, min_eq_left haS.le, ← h]; ring
  have hgI : |∫ u in (a : ℝ)..(S ω), fieldGen Φ2 Ψ B u ω| ≤ (C + 1 / 2 * C) * ((S ω : ℝ) - a) := by
    refine abs_integral_le_of_abs_le haS' fun u hu => ?_
    have hu' := hsubI hu
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact add_le_add (hbΨ u hu' _) (mul_le_mul_of_nonneg_left (hb2 u hu' _) (by norm_num))
  -- Lipschitz bounds for `Φ` in time and in space
  have hT : |Φ (S ω) ω (B (S ω) ω) - Φ a ω (B (S ω) ω)| ≤ C * ((S ω : ℝ) - a) := by
    rw [htime _ _ _ hmema.1 haS' hmemS.2]
    exact abs_integral_le_of_abs_le haS' fun u hu => hbΨ u (hsubI hu) _
  have hX' : |Φ a ω (B (S ω) ω) - Φ a ω (B a ω)| ≤ C * |B (S ω) ω - B a ω| :=
    abs_sub_le_of_hasDerivAt (hd1 _ hmema) (hb1 _ hmema) _ _
  have hc1 : stopCoef Φ1 B S a ω = Φ1 a ω (B a ω) := by simp only [stopCoef, haS, ite_true]
  have hc2 : stopCoef Φ2 B S a ω = Φ2 a ω (B a ω) := by simp only [stopCoef, haS, ite_true]
  have hb1a := hb1 _ hmema (B a ω)
  have hb2a := hb2 _ hmema (B a ω)
  set Δ := B b ω - B a ω
  have hba : (0 : ℝ) ≤ (b : ℝ) - a := by linarith
  have hq : |Δ ^ 2 - ((b : ℝ) - a)| ≤ Δ ^ 2 + ((b : ℝ) - a) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hba]
  have e1 : |Φ1 a ω (B a ω) * Δ| ≤ C * |Δ| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb1a (abs_nonneg _)
  have e2 : |1 / 2 * Φ2 a ω (B a ω) * (Δ ^ 2 - ((b : ℝ) - a))| ≤
      1 / 2 * C * (Δ ^ 2 + ((b : ℝ) - a)) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hb2a hq (abs_nonneg _) hC0) (by norm_num)
  have hSa : (S ω : ℝ) - a ≤ (b : ℝ) - a := by linarith
  unfold itoDefect
  rw [hX, hc1, hc2]
  have hsplit : Φ (S ω) ω (B (S ω) ω) - Φ a ω (B a ω) =
      (Φ (S ω) ω (B (S ω) ω) - Φ a ω (B (S ω) ω)) + (Φ a ω (B (S ω) ω) - Φ a ω (B a ω)) := by ring
  rw [hsplit]
  calc _ ≤ |Φ (S ω) ω (B (S ω) ω) - Φ a ω (B (S ω) ω)| + |Φ a ω (B (S ω) ω) - Φ a ω (B a ω)| +
        |∫ u in (a : ℝ)..(S ω), fieldGen Φ2 Ψ B u ω| + |Φ1 a ω (B a ω) * Δ| +
        |1 / 2 * Φ2 a ω (B a ω) * (Δ ^ 2 - ((b : ℝ) - a))| := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
          (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ C * ((S ω : ℝ) - a) + C * |B (S ω) ω - B a ω| + (C + 1 / 2 * C) * ((S ω : ℝ) - a) +
        C * |Δ| + 1 / 2 * C * (Δ ^ 2 + ((b : ℝ) - a)) := by gcongr
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hSa hC0]

/-- **The excess of one cell** is at most its Taylor remainder (cells before `S`) plus its own excess if it
contains `S` (cells after `S` contribute nothing). -/
theorem excess_stopped_le {a b : ℝ≥0} (hsa : s ≤ a) (hab : a ≤ b) (hbt : b ≤ t) (hBc : Continuous (B · ω))
    (hd1 : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, HasDerivAt (Φ r ω) (Φ1 r ω x) x)
    (hd2 : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, HasDerivAt (Φ1 r ω) (Φ2 r ω x) x)
    (hlip : ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x y, |Φ2 r ω x - Φ2 r ω y| ≤ C * |x - y|)
    (htime : ∀ x a b : ℝ, (s : ℝ) ≤ a → a ≤ b → b ≤ min t (S ω) →
      Φ b ω x - Φ a ω x = ∫ u in a..b, Ψ u ω x)
    (hΨc : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω p.2) (Icc (s : ℝ) (min t (S ω)) ×ˢ univ))
    (hΦ2c : ContinuousOn (fun p : ℝ × ℝ => Φ2 p.1 ω p.2) (Icc (s : ℝ) (min t (S ω)) ×ˢ univ))
    (hC0 : 0 ≤ C) :
    max (|itoDefect (fieldStopped Φ Φ2 Ψ B S s) (stopCoef Φ1 B S) (stopCoef Φ2 B S) B a b ω| -
        2 * C * |B b ω - B a ω| ^ 3) 0 ≤
      (if a < S ω ∧ b ≤ S ω then fieldStepRem (fun u x => Ψ u ω x) (fun u x => Φ2 u ω x)
          (fun r => B r.toNNReal ω) a b else 0) +
      (if a < S ω ∧ S ω < b then
          max (|itoDefect (fieldStopped Φ Φ2 Ψ B S s) (stopCoef Φ1 B S) (stopCoef Φ2 B S) B a b ω| -
            2 * C * |B b ω - B a ω| ^ 3) 0 else 0) := by
  rcases lt_or_ge a (S ω) with haS | hSa
  · rcases le_or_gt b (S ω) with hbS | hSb
    · have h := abs_itoDefect_stopped_le_of_le (Ψ := Ψ) hsa hab haS hbS hbt hBc hd1 hd2 hlip htime
        hΨc hΦ2c
      have hfs : 0 ≤ fieldStepRem (fun u x => Ψ u ω x) (fun u x => Φ2 u ω x)
          (fun r => B r.toNNReal ω) a b := fieldStepRem_nonneg (NNReal.coe_le_coe.2 hab)
      have h3 : 0 ≤ C * |B b ω - B a ω| ^ 3 := by positivity
      rw [ite_eq_left ⟨haS, hbS⟩, ite_eq_right (fun h => absurd h.2 (not_lt.2 hbS)), add_zero]
      exact max_le (by linarith) hfs
    · rw [ite_eq_right (fun h => absurd h.2 (not_le.2 hSb)), ite_eq_left ⟨haS, hSb⟩, zero_add]
  · have h0 := itoDefect_stopped_eq_zero_of_le (Φ := Φ) (Φ1 := Φ1) (Φ2 := Φ2) (Ψ := Ψ) (B := B)
      (s := s) hab hSa
    rw [ite_eq_right (fun h => absurd h.1 (not_lt.2 hSa)), ite_eq_right (fun h => absurd h.1 (not_lt.2 hSa)),
      add_zero, h0, abs_zero, zero_sub]
    exact max_le (by have : 0 ≤ 2 * C * |B b ω - B a ω| ^ 3 := by positivity
                     linarith) le_rfl

end Cells

/-- A sum over `range n` of terms supported on at most one index is bounded by the bound of that term. -/
theorem sum_ite_le_of_unique {n : ℕ} {p : ℕ → Prop} [DecidablePred p] {f : ℕ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ k < n, p k → f k ≤ M) (huniq : ∀ k k', p k → p k' → k = k') :
    ∑ k ∈ Finset.range n, (if p k then f k else 0) ≤ M := by
  rw [← Finset.sum_filter]
  have hcard : (Finset.filter p (Finset.range n)).card ≤ 1 :=
    Finset.card_le_one.2 fun a ha b hb =>
      huniq a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
  calc ∑ k ∈ Finset.filter p (Finset.range n), f k
      ≤ ∑ _k ∈ Finset.filter p (Finset.range n), M :=
        Finset.sum_le_sum fun k hk => hf k (Finset.mem_range.1 (Finset.mem_filter.1 hk).1)
          (Finset.mem_filter.1 hk).2
    _ = (Finset.filter p (Finset.range n)).card * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
    _ = M := one_mul M

theorem unifGrid_mono {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) : Monotone (unifGrid s t n) :=
  monotone_nat_of_le_succ (unifGrid_le_succ hst n)

/-- At most one cell of a grid contains a given time strictly inside. -/
theorem unique_cell {s t σ : ℝ≥0} (hst : s ≤ t) {n k k' : ℕ}
    (hk : unifGrid s t n k < σ ∧ σ < unifGrid s t n (k + 1))
    (hk' : unifGrid s t n k' < σ ∧ σ < unifGrid s t n (k' + 1)) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := unifGrid_mono hst n (Nat.succ_le_of_lt h)
    exact absurd (hk.2.trans_le this) (not_lt.2 hk'.1.le)
  · have := unifGrid_mono hst n (Nat.succ_le_of_lt h)
    exact absurd (hk'.2.trans_le this) (not_lt.2 hk.1.le)

/-! ### The stopped martingale identity -/

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

/-- **Itô's formula for a random field up to a stopping time** (martingale form). Let `B` be an
`𝓕`-Brownian motion with continuous paths, `s ≤ t`, and `S ≥ s` an `𝓕`-stopping time. Suppose that for
every `ω`, on the random time interval `[s, t ∧ S(ω)]`, `∂ₓΦ = Φ₁`, `∂ₓΦ₁ = Φ₂` with `Φ₂` `C`-Lipschitz, `Ψ` is
the time derivative of `Φ` (integrated form), `Ψ` and `Φ₂` are jointly continuous, and `|Φ|, |Φ₁|, |Φ₂|, |Ψ| ≤ C`;
that `Φ₁(r, B_r)`, `Φ₂(r, B_r)` are `𝓕_r`-measurable and the stopped process is measurable. Then
`E[ξ (X_t − X_s)] = 0` for every `𝓕_s`-measurable `|ξ| ≤ 1`, where
`X_r = Φ(r ∧ S, B_{r ∧ S}) − ∫_s^{r ∧ S} (Ψ(u, B_u) + ½ Φ₂(u, B_u)) du` (`fieldStopped`). -/
theorem integral_mul_fieldStopped_sub_eq_zero (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) {Φ Φ1 Φ2 Ψ : ℝ → Ω → ℝ → ℝ} {C : ℝ} {s t : ℝ≥0}
    (hst : s ≤ t) {S : Ω → ℝ≥0} (hS : ∀ r : ℝ≥0, MeasurableSet[𝓕 r] {ω | S ω ≤ r})
    (hsS : ∀ ω, s ≤ S ω)
    (hd1 : ∀ ω, ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, HasDerivAt (Φ r ω) (Φ1 r ω x) x)
    (hd2 : ∀ ω, ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, HasDerivAt (Φ1 r ω) (Φ2 r ω x) x)
    (hlip : ∀ ω, ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x y, |Φ2 r ω x - Φ2 r ω y| ≤ C * |x - y|)
    (htime : ∀ ω x a b, (s : ℝ) ≤ a → a ≤ b → b ≤ min t (S ω) →
      Φ b ω x - Φ a ω x = ∫ u in a..b, Ψ u ω x)
    (hΨc : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω p.2) (Icc (s : ℝ) (min t (S ω)) ×ˢ univ))
    (hΦ2c : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Φ2 p.1 ω p.2) (Icc (s : ℝ) (min t (S ω)) ×ˢ univ))
    (hb0 : ∀ ω, ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Φ r ω x| ≤ C)
    (hb1 : ∀ ω, ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Φ1 r ω x| ≤ C)
    (hb2 : ∀ ω, ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Φ2 r ω x| ≤ C)
    (hbΨ : ∀ ω, ∀ r ∈ Icc (s : ℝ) (min t (S ω)), ∀ x, |Ψ r ω x| ≤ C)
    (hm1 : ∀ r : ℝ≥0, s ≤ r → r ≤ t → Measurable[𝓕 r] fun ω => Φ1 r ω (B r ω))
    (hm2 : ∀ r : ℝ≥0, s ≤ r → r ≤ t → Measurable[𝓕 r] fun ω => Φ2 r ω (B r ω))
    (hXm : ∀ r : ℝ≥0, s ≤ r → r ≤ t → Measurable (fieldStopped Φ Φ2 Ψ B S s r))
    {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (fieldStopped Φ Φ2 Ψ B S s t ω - fieldStopped Φ Φ2 Ψ B S s s ω) ∂P = 0 := by
  have hP := hB.isProbabilityMeasure'
  obtain ⟨ω₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hP.measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  have hτs : ∀ ω, (s : ℝ) ∈ Icc (s : ℝ) (min t (S ω)) := fun ω =>
    ⟨le_rfl, le_min (NNReal.coe_le_coe.2 hst) (NNReal.coe_le_coe.2 (hsS ω))⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb0 ω₀ _ (hτs ω₀) 0)
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (NNReal.coe_le_coe.2 hst)
  set K₀ := 4 * C + 4 * C * ((t : ℝ) - s) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  -- adaptedness of the stopped coefficients
  have hlt : ∀ r : ℝ≥0, MeasurableSet[𝓕 r] {ω | r < S ω} := fun r => by
    have h := (hS r).compl
    have he : {ω | S ω ≤ r}ᶜ = {ω | r < S ω} := by ext ω; simp
    rwa [he] at h
  have hcm : ∀ F : ℝ → Ω → ℝ → ℝ, (∀ r : ℝ≥0, s ≤ r → r ≤ t →
      Measurable[𝓕 r] fun ω => F r ω (B r ω)) →
      ∀ r, s ≤ r → r ≤ t → Measurable[𝓕 r] (stopCoef F B S r) := fun F hF r hsr hrt =>
    Measurable.ite (hlt r) (hF r hsr hrt) measurable_const
  -- the engine
  refine integral_mul_sub_eq_zero_of_defectExcess (C := 2 * C) (K := 3 * C * ((t : ℝ) - s) + K₀) hB
    hst hXm (fun r hsr hrt => ?_) (hcm Φ1 hm1) (hcm Φ2 hm2)
    (fun r hsr hrt ω => (abs_stopCoef_le hsr hrt hC0 (hb1 ω)).trans (by linarith))
    (fun r hsr hrt ω => (abs_stopCoef_le hsr hrt hC0 (hb2 ω)).trans (by linarith))
    (fun n hn ω => ?_) (fun ω => ?_) hξ hξb
  · exact (integrable_const (C + 3 * C / 2 * ((t : ℝ) - s))).mono' (hXm r hsr hrt).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_fieldStopped_le hsr hrt (hsS ω) (hb0 ω) (hb2 ω) (hbΨ ω))
  · -- the uniform bound
    set g := unifGrid s t n with hg
    have hsg : ∀ k, s ≤ g k := le_unifGrid hst n
    have hgt : ∀ k ≤ n, g k ≤ t := fun k hk => unifGrid_le hst hn hk
    have hgle : ∀ k, g k ≤ g (k + 1) := unifGrid_le_succ hst n
    set A : ℕ → ℝ := fun k => if g k < S ω ∧ g (k + 1) ≤ S ω then fieldStepRem (fun u x => Ψ u ω x)
      (fun u x => Φ2 u ω x) (fun r => B r.toNNReal ω) (g k) (g (k + 1)) else 0 with hA
    set E : ℕ → ℝ := fun k => max (|itoDefect (fieldStopped Φ Φ2 Ψ B S s) (stopCoef Φ1 B S)
      (stopCoef Φ2 B S) B (g k) (g (k + 1)) ω| - 2 * C * |B (g (k + 1)) ω - B (g k) ω| ^ 3) 0 with hE
    have hsplit : ∀ k ∈ Finset.range n, E k ≤ A k + (if g k < S ω ∧ S ω < g (k + 1) then E k else 0) :=
      fun k hk => excess_stopped_le (hsg k) (hgle k) (hgt (k + 1) (Finset.mem_range.1 hk)) (hBc ω)
        (hd1 ω) (hd2 ω) (hlip ω) (htime ω) (hΨc ω) (hΦ2c ω) hC0
    have hAle : ∀ k ∈ Finset.range n, A k ≤ 3 * C * ((g (k + 1) : ℝ) - g k) := by
      intro k hk
      have hΔ : (0 : ℝ) ≤ (g (k + 1) : ℝ) - g k := sub_nonneg.2 (NNReal.coe_le_coe.2 (hgle k))
      simp only [hA]
      split_ifs with hc
      · have hτ : ((g (k + 1) : ℝ≥0) : ℝ) ≤ min (t : ℝ) (S ω) :=
          le_min (NNReal.coe_le_coe.2 (hgt (k + 1) (Finset.mem_range.1 hk))) (NNReal.coe_le_coe.2 hc.2)
        have hsub : Icc ((g k : ℝ≥0) : ℝ) (g (k + 1)) ⊆ Icc (s : ℝ) (min t (S ω)) :=
          Icc_subset_Icc (NNReal.coe_le_coe.2 (hsg k)) hτ
        have h := fieldStepRem_le (ψ := fun u x => Ψ u ω x) (φ := fun u x => Φ2 u ω x)
          (β := fun r => B r.toNNReal ω) (NNReal.coe_le_coe.2 (hgle k))
          ((hΨc ω).mono (prod_mono hsub le_rfl)) ((hΦ2c ω).mono (prod_mono hsub le_rfl))
          (((hBc ω).comp continuous_real_toNNReal).continuousOn) (α := 2 * C) (γ := 2 * C)
          (fun u hu => (abs_sub _ _).trans ((add_le_add (hbΨ ω u (hsub hu) _)
            (hbΨ ω u (hsub hu) _)).trans_eq (two_mul C).symm))
          (fun u hu => (abs_sub _ _).trans ((add_le_add
            (hb2 ω _ (hsub (left_mem_Icc.2 (NNReal.coe_le_coe.2 (hgle k)))) _)
            (hb2 ω u (hsub hu) _)).trans_eq (two_mul C).symm))
        linarith
      · positivity
    have hsumL : ∑ k ∈ Finset.range n, ((g (k + 1) : ℝ) - g k) = (t : ℝ) - s := by
      rw [Finset.sum_range_sub (f := fun k => ((g k : ℝ≥0) : ℝ)), hg, unifGrid_self hst hn,
        unifGrid_zero hst]
    have hCle : ∑ k ∈ Finset.range n, (if g k < S ω ∧ S ω < g (k + 1) then E k else 0) ≤ K₀ :=
      sum_ite_le_of_unique hK₀0 (fun k hkn _ => by
        have h := abs_itoDefect_stopped_le_crude (Φ := Φ) (Φ1 := Φ1) (Ψ := Ψ) (B := B) (hsg k) (hgle k)
          (hgt (k + 1) hkn) (hsS ω) (hb0 ω) (hb1 ω) (hb2 ω) (hbΨ ω)
        simp only [hE]
        exact max_le (by linarith) hK₀0) (fun k k' hk hk' => unique_cell hst hk hk')
    unfold defectExcess
    calc ∑ k ∈ Finset.range n, E k
        ≤ ∑ k ∈ Finset.range n, (A k + (if g k < S ω ∧ S ω < g (k + 1) then E k else 0)) :=
          Finset.sum_le_sum hsplit
      _ = ∑ k ∈ Finset.range n, A k +
          ∑ k ∈ Finset.range n, (if g k < S ω ∧ S ω < g (k + 1) then E k else 0) :=
          Finset.sum_add_distrib
      _ ≤ 3 * C * ((t : ℝ) - s) + K₀ := by
          refine add_le_add ((Finset.sum_le_sum hAle).trans_eq ?_) hCle
          rw [← Finset.mul_sum, hsumL]
  · -- the pathwise limit
    rw [Metric.tendsto_atTop]
    intro ε hε
    set τ : ℝ := min (t : ℝ) (S ω) with hτ
    have hsτ : (s : ℝ) ≤ τ := (hτs ω).2
    have hτt : τ ≤ t := min_le_left _ _
    set β : ℝ → ℝ := fun r => B r.toNNReal ω with hβ
    have hβc : Continuous β := (hBc ω).comp continuous_real_toNNReal
    set ε₁ := ε / (2 * ((t : ℝ) - s) + 2) with hε₁
    have hε₁0 : 0 < ε₁ := div_pos hε (by linarith)
    obtain ⟨δ₁, hδ₁, hfs⟩ := exists_fieldStepRem_le (ψ := fun u x => Ψ u ω x)
      (φ := fun u x => Φ2 u ω x) (β := β) (hΨc ω) (hΦ2c ω) hβc.continuousOn hε₁0
    set η := min 1 (ε / (12 * C + 2)) with hη
    have hη0 : 0 < η := lt_min one_pos (div_pos hε (by linarith))
    obtain ⟨δ₂, hδ₂, hβu⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous (hβc.continuousOn (s := Icc (s : ℝ) t))) η hη0
    set δ := min (min δ₁ δ₂) η with hδ
    have hδ0 : 0 < δ := lt_min (lt_min hδ₁ hδ₂) hη0
    obtain ⟨N, hN⟩ := exists_nat_gt (((t : ℝ) - s) / δ)
    refine ⟨N + 1, fun n hn => ?_⟩
    have hn0 : 0 < n := (Nat.succ_pos N).trans_le hn
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    set g := unifGrid s t n with hg
    have hsg : ∀ k, s ≤ g k := le_unifGrid hst n
    have hgt : ∀ k ≤ n, g k ≤ t := fun k hk => unifGrid_le hst hn0 hk
    have hgle : ∀ k, g k ≤ g (k + 1) := unifGrid_le_succ hst n
    have hstep : ∀ k, (g (k + 1) : ℝ) - g k = ((t : ℝ) - s) / n := unifGrid_succ_sub hst n
    have hmesh : ((t : ℝ) - s) / n < δ := by
      rw [div_lt_iff₀ hn0']
      rw [div_lt_iff₀ hδ0] at hN
      have : (N : ℝ) < n := by exact_mod_cast Nat.lt_of_succ_le hn
      nlinarith
    set A : ℕ → ℝ := fun k => if g k < S ω ∧ g (k + 1) ≤ S ω then fieldStepRem (fun u x => Ψ u ω x)
      (fun u x => Φ2 u ω x) (fun r => B r.toNNReal ω) (g k) (g (k + 1)) else 0 with hA
    set E : ℕ → ℝ := fun k => max (|itoDefect (fieldStopped Φ Φ2 Ψ B S s) (stopCoef Φ1 B S)
      (stopCoef Φ2 B S) B (g k) (g (k + 1)) ω| - 2 * C * |B (g (k + 1)) ω - B (g k) ω| ^ 3) 0 with hE
    have hsplit : ∀ k ∈ Finset.range n, E k ≤ A k + (if g k < S ω ∧ S ω < g (k + 1) then E k else 0) :=
      fun k hk => excess_stopped_le (hsg k) (hgle k) (hgt (k + 1) (Finset.mem_range.1 hk)) (hBc ω)
        (hd1 ω) (hd2 ω) (hlip ω) (htime ω) (hΨc ω) (hΦ2c ω) hC0
    have hEnn : ∀ k, 0 ≤ E k := fun k => le_max_right _ _
    -- cells before `S`
    have hAle : ∀ k ∈ Finset.range n, A k ≤ ε₁ * ((g (k + 1) : ℝ) - g k) := by
      intro k hk
      have hΔ : (0 : ℝ) ≤ (g (k + 1) : ℝ) - g k := sub_nonneg.2 (NNReal.coe_le_coe.2 (hgle k))
      simp only [hA]
      split_ifs with hc
      · have hτ' : ((g (k + 1) : ℝ≥0) : ℝ) ≤ τ :=
          le_min (NNReal.coe_le_coe.2 (hgt (k + 1) (Finset.mem_range.1 hk))) (NNReal.coe_le_coe.2 hc.2)
        exact hfs _ _ (NNReal.coe_le_coe.2 (hsg k)) (NNReal.coe_le_coe.2 (hgle k)) hτ'
          (by rw [hstep k]; exact hmesh.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      · positivity
    -- the cell containing `S`
    have hCle : ∑ k ∈ Finset.range n, (if g k < S ω ∧ S ω < g (k + 1) then E k else 0) ≤ ε / 2 :=
      sum_ite_le_of_unique (by positivity) (fun k hkn hk => by
        have hb := abs_itoDefect_stopped_le_of_mem (Φ := Φ) (Φ1 := Φ1) (Ψ := Ψ) (B := B) (hsg k) hk.1
          hk.2 (hgt (k + 1) hkn) (hBc ω) (hd1 ω) (htime ω) (hΨc ω) (hΦ2c ω) (hb1 ω) (hb2 ω) (hbΨ ω)
        have hΔη : (g (k + 1) : ℝ) - g k < η := by
          rw [hstep k]; exact hmesh.trans_le (min_le_right _ _)
        have hΔδ : (g (k + 1) : ℝ) - g k < δ₂ := by
          rw [hstep k]; exact hmesh.trans_le ((min_le_left _ _).trans (min_le_right _ _))
        have hmem : ∀ r : ℝ≥0, s ≤ r → r ≤ t → (r : ℝ) ∈ Icc (s : ℝ) t := fun r h1 h2 =>
          ⟨NNReal.coe_le_coe.2 h1, NNReal.coe_le_coe.2 h2⟩
        have hgk := hmem _ (hsg k) ((hgle k).trans (hgt (k + 1) hkn))
        have hgk1 := hmem _ (hsg (k + 1)) (hgt (k + 1) hkn)
        have hSm := hmem _ ((hsg k).trans hk.1.le) (hk.2.le.trans (hgt (k + 1) hkn))
        have hd1' : dist ((S ω : ℝ)) (g k : ℝ) < δ₂ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hk.1.le))]
          have := NNReal.coe_lt_coe.2 hk.2; linarith
        have hd2' : dist ((g (k + 1) : ℝ≥0) : ℝ) (g k : ℝ) < δ₂ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 (hgle k)))]; exact hΔδ
        have hB1 := hβu _ hSm _ hgk hd1'
        have hB2 := hβu _ hgk1 _ hgk hd2'
        simp only [hβ, Real.toNNReal_coe, Real.dist_eq] at hB1 hB2
        have hη1 : η ≤ 1 := min_le_left _ _
        have hηε : η ≤ ε / (12 * C + 2) := min_le_right _ _
        have hq : (B (g (k + 1)) ω - B (g k) ω) ^ 2 ≤ η := by
          rw [← sq_abs]; nlinarith [abs_nonneg (B (g (k + 1)) ω - B (g k) ω)]
        have hCη : C * η * 12 ≤ ε := by
          have := mul_le_mul_of_nonneg_left hηε (by positivity : (0 : ℝ) ≤ 12 * C + 2)
          rw [mul_div_cancel₀ _ (by positivity : (12 * C + 2 : ℝ) ≠ 0)] at this
          nlinarith
        have hEk : E k ≤ |itoDefect (fieldStopped Φ Φ2 Ψ B S s) (stopCoef Φ1 B S)
            (stopCoef Φ2 B S) B (g k) (g (k + 1)) ω| := by
          simp only [hE]
          exact max_le (by have : 0 ≤ 2 * C * |B (g (k + 1)) ω - B (g k) ω| ^ 3 := by positivity
                           linarith) (abs_nonneg _)
        refine hEk.trans (hb.trans ?_)
        nlinarith [mul_le_mul_of_nonneg_left hΔη.le hC0, mul_le_mul_of_nonneg_left hB1.le hC0,
          mul_le_mul_of_nonneg_left hB2.le hC0, mul_le_mul_of_nonneg_left hq hC0])
        (fun k k' hk hk' => unique_cell hst hk hk')
    have hsumL : ∑ k ∈ Finset.range n, ((g (k + 1) : ℝ) - g k) = (t : ℝ) - s := by
      rw [Finset.sum_range_sub (f := fun k => ((g k : ℝ≥0) : ℝ)), hg, unifGrid_self hst hn0,
        unifGrid_zero hst]
    have hDnn : 0 ≤ defectExcess (fieldStopped Φ Φ2 Ψ B S s) (stopCoef Φ1 B S) (stopCoef Φ2 B S) B
        (2 * C) s t n ω := Finset.sum_nonneg fun k _ => le_max_right _ _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hDnn]
    have hle : defectExcess (fieldStopped Φ Φ2 Ψ B S s) (stopCoef Φ1 B S) (stopCoef Φ2 B S) B
        (2 * C) s t n ω ≤ ε₁ * ((t : ℝ) - s) + ε / 2 := by
      unfold defectExcess
      calc ∑ k ∈ Finset.range n, E k
          ≤ ∑ k ∈ Finset.range n, (A k + (if g k < S ω ∧ S ω < g (k + 1) then E k else 0)) :=
            Finset.sum_le_sum hsplit
        _ = ∑ k ∈ Finset.range n, A k +
            ∑ k ∈ Finset.range n, (if g k < S ω ∧ S ω < g (k + 1) then E k else 0) :=
            Finset.sum_add_distrib
        _ ≤ ε₁ * ((t : ℝ) - s) + ε / 2 := by
            refine add_le_add ((Finset.sum_le_sum hAle).trans_eq ?_) hCle
            rw [← Finset.mul_sum, hsumL]
    have hε₁' : ε₁ * ((t : ℝ) - s) < ε / 2 := by
      rw [hε₁, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith


/-- **The martingale identity for a random field** (Itô's formula for `Φ(t, B_t)`, martingale form,
Revuz–Yor IV.3.3). Under the hypotheses of the module docstring of `Stochastic/ItoAdapted.lean` on `[s, t]`,
for every `𝓕_s`-measurable `ξ` with `|ξ| ≤ 1`:
`E[ξ (Φ(t, B_t) − Φ(s, B_s) − ∫_s^t (Ψ(u, B_u) + ½ Φ₂(u, B_u)) du)] = 0`. (The case `S ≡ t` of
`integral_mul_fieldStopped_sub_eq_zero`.) -/
theorem integral_mul_fieldIncr_eq_zero (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) {Φ Φ1 Φ2 Ψ : ℝ → Ω → ℝ → ℝ} {C : ℝ} {s t : ℝ≥0}
    (hst : s ≤ t)
    (hd1 : ∀ r ∈ Icc (s : ℝ) t, ∀ ω x, HasDerivAt (Φ r ω) (Φ1 r ω x) x)
    (hd2 : ∀ r ∈ Icc (s : ℝ) t, ∀ ω x, HasDerivAt (Φ1 r ω) (Φ2 r ω x) x)
    (hlip : ∀ r ∈ Icc (s : ℝ) t, ∀ ω x y, |Φ2 r ω x - Φ2 r ω y| ≤ C * |x - y|)
    (htime : ∀ ω x a b, (s : ℝ) ≤ a → a ≤ b → b ≤ t →
      Φ b ω x - Φ a ω x = ∫ u in a..b, Ψ u ω x)
    (hΨc : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω p.2) (Icc (s : ℝ) t ×ˢ univ))
    (hΦ2c : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Φ2 p.1 ω p.2) (Icc (s : ℝ) t ×ˢ univ))
    (hb0 : ∀ r ∈ Icc (s : ℝ) t, ∀ ω x, |Φ r ω x| ≤ C)
    (hb1 : ∀ r ∈ Icc (s : ℝ) t, ∀ ω x, |Φ1 r ω x| ≤ C)
    (hb2 : ∀ r ∈ Icc (s : ℝ) t, ∀ ω x, |Φ2 r ω x| ≤ C)
    (hbΨ : ∀ r ∈ Icc (s : ℝ) t, ∀ ω x, |Ψ r ω x| ≤ C)
    (hm0 : ∀ r ∈ Icc (s : ℝ) t, ∀ x, Measurable[𝓕 r.toNNReal] fun ω => Φ r ω x)
    (hm1 : ∀ r ∈ Icc (s : ℝ) t, ∀ x, Measurable[𝓕 r.toNNReal] fun ω => Φ1 r ω x)
    (hm2 : ∀ r ∈ Icc (s : ℝ) t, ∀ x, Measurable[𝓕 r.toNNReal] fun ω => Φ2 r ω x)
    (hmΨ : ∀ r ∈ Icc (s : ℝ) t, ∀ x, Measurable[𝓕 r.toNNReal] fun ω => Ψ r ω x)
    {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (Φ t ω (B t ω) - Φ s ω (B s ω) - ∫ u in (s : ℝ)..t, fieldGen Φ2 Ψ B u ω) ∂P
      = 0 := by
  have hBm : ∀ r, Measurable (B r) := hB.measurable'
  have hmemI : ∀ r : ℝ≥0, s ≤ r → r ≤ t → (r : ℝ) ∈ Icc (s : ℝ) t := fun r h1 h2 =>
    ⟨NNReal.coe_le_coe.2 h1, NNReal.coe_le_coe.2 h2⟩
  have hFm : ∀ F : ℝ → Ω → ℝ → ℝ,
      (∀ r ∈ Icc (s : ℝ) t, ∀ x, Measurable[𝓕 r.toNNReal] fun ω => F r ω x) →
      (∀ r ∈ Icc (s : ℝ) t, ∀ ω, Continuous (F r ω)) → ∀ r : ℝ≥0, s ≤ r → r ≤ t →
        Measurable[𝓕 r] fun ω => F r ω (B r ω) := by
    intro F hFm' hFc r h1 h2
    have h := hFm' r (hmemI r h1 h2)
    rw [Real.toNNReal_coe] at h
    exact measurable_field_comp h (hFc r (hmemI r h1 h2)) (hB.2.1 r)
  have hc0 : ∀ r ∈ Icc (s : ℝ) t, ∀ ω, Continuous (Φ r ω) := fun r hr ω =>
    continuous_iff_continuousAt.2 fun x => (hd1 r hr ω x).continuousAt
  have hc1 : ∀ r ∈ Icc (s : ℝ) t, ∀ ω, Continuous (Φ1 r ω) := fun r hr ω =>
    continuous_iff_continuousAt.2 fun x => (hd2 r hr ω x).continuousAt
  have hc2 : ∀ r ∈ Icc (s : ℝ) t, ∀ ω, Continuous (Φ2 r ω) := fun r hr ω =>
    continuous_of_continuousOn_prod (F := fun u x => Φ2 u ω x) (hΦ2c ω) hr
  have hX : ∀ r : ℝ≥0, r ≤ t → ∀ ω, fieldStopped Φ Φ2 Ψ B (fun _ => t) s r ω =
      Φ r ω (B r ω) - ∫ u in (s : ℝ)..r, fieldGen Φ2 Ψ B u ω := fun r hr ω => by
    unfold fieldStopped
    rw [min_eq_left hr]
  have h := integral_mul_fieldStopped_sub_eq_zero (P := P) (Φ := Φ) (Φ1 := Φ1) (Φ2 := Φ2) (Ψ := Ψ)
    (C := C) (S := fun _ => t) hB hBc hst (fun r => MeasurableSet.const (t ≤ r)) (fun _ => hst)
    (fun ω r hr => hd1 r (by simpa only [min_self] using hr) ω) (fun ω r hr => hd2 r (by simpa only [min_self] using hr) ω)
    (fun ω r hr => hlip r (by simpa only [min_self] using hr) ω)
    (fun ω x a b ha hab hb => htime ω x a b ha hab (by simpa only [min_self] using hb))
    (fun ω => by simpa only [min_self] using hΨc ω) (fun ω => by simpa only [min_self] using hΦ2c ω)
    (fun ω r hr => hb0 r (by simpa only [min_self] using hr) ω) (fun ω r hr => hb1 r (by simpa only [min_self] using hr) ω)
    (fun ω r hr => hb2 r (by simpa only [min_self] using hr) ω) (fun ω r hr => hbΨ r (by simpa only [min_self] using hr) ω)
    (hFm Φ1 hm1 hc1) (hFm Φ2 hm2 hc2)
    (fun r h1 h2 => by
      have heq : fieldStopped Φ Φ2 Ψ B (fun _ => t) s r =
          fun ω => Φ r ω (B r ω) - ∫ u in (s : ℝ)..r, fieldGen Φ2 Ψ B u ω := funext (hX r h2)
      rw [heq]
      have hS : Icc (s : ℝ) r ⊆ Icc (s : ℝ) t := Icc_subset_Icc le_rfl (NNReal.coe_le_coe.2 h2)
      exact ((hFm Φ hm0 hc0 r h1 h2).mono (𝓕.le r) le_rfl).sub
        (measurable_integral_fieldGen (m := mΩ) (B := B) (NNReal.coe_le_coe.2 h1)
          (fun r _ => hBm _) hBc (fun u hu x => (hm2 u (hS hu) x).mono (𝓕.le _) le_rfl)
          (fun u hu x => (hmΨ u (hS hu) x).mono (𝓕.le _) le_rfl)
          (fun ω => (hΨc ω).mono (prod_mono hS le_rfl)) (fun ω => (hΦ2c ω).mono (prod_mono hS le_rfl))))
    hξ hξb
  have hXts : ∀ ω, fieldStopped Φ Φ2 Ψ B (fun _ => t) s t ω - fieldStopped Φ Φ2 Ψ B (fun _ => t) s s ω
      = Φ t ω (B t ω) - Φ s ω (B s ω) - ∫ u in (s : ℝ)..t, fieldGen Φ2 Ψ B u ω := fun ω => by
    rw [hX t le_rfl, hX s hst, intervalIntegral.integral_same]; ring
  simp_rw [hXts] at h
  exact h

/-- **Itô's formula for an adapted random field `Φ(t, B_t)`, martingale form** (Revuz–Yor IV.3.3). Let `B`
be an `𝓕`-Brownian motion with continuous paths and let `Φ, Φ₁, Φ₂, Ψ` be random fields on times `r ≥ 0`
with `∂ₓΦ = Φ₁`, `∂ₓΦ₁ = Φ₂` (`C`-Lipschitz), time derivative `Ψ` in integrated form, `Ψ` and `Φ₂` jointly
continuous, all four bounded by `C` and adapted. Then `Φ(t, B_t) − ∫₀ᵗ (Ψ(u, B_u) + ½ Φ₂(u, B_u)) du` is an
`𝓕`-martingale. -/
theorem martingale_fieldDynkin (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) {Φ Φ1 Φ2 Ψ : ℝ → Ω → ℝ → ℝ} {C : ℝ}
    (hd1 : ∀ r ∈ Ici (0 : ℝ), ∀ ω x, HasDerivAt (Φ r ω) (Φ1 r ω x) x)
    (hd2 : ∀ r ∈ Ici (0 : ℝ), ∀ ω x, HasDerivAt (Φ1 r ω) (Φ2 r ω x) x)
    (hlip : ∀ r ∈ Ici (0 : ℝ), ∀ ω x y, |Φ2 r ω x - Φ2 r ω y| ≤ C * |x - y|)
    (htime : ∀ ω x a b, 0 ≤ a → a ≤ b → Φ b ω x - Φ a ω x = ∫ u in a..b, Ψ u ω x)
    (hΨc : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hΦ2c : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Φ2 p.1 ω p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hb0 : ∀ r ∈ Ici (0 : ℝ), ∀ ω x, |Φ r ω x| ≤ C)
    (hb1 : ∀ r ∈ Ici (0 : ℝ), ∀ ω x, |Φ1 r ω x| ≤ C)
    (hb2 : ∀ r ∈ Ici (0 : ℝ), ∀ ω x, |Φ2 r ω x| ≤ C)
    (hbΨ : ∀ r ∈ Ici (0 : ℝ), ∀ ω x, |Ψ r ω x| ≤ C)
    (hm0 : ∀ r ∈ Ici (0 : ℝ), ∀ x, Measurable[𝓕 r.toNNReal] fun ω => Φ r ω x)
    (hm1 : ∀ r ∈ Ici (0 : ℝ), ∀ x, Measurable[𝓕 r.toNNReal] fun ω => Φ1 r ω x)
    (hm2 : ∀ r ∈ Ici (0 : ℝ), ∀ x, Measurable[𝓕 r.toNNReal] fun ω => Φ2 r ω x)
    (hmΨ : ∀ r ∈ Ici (0 : ℝ), ∀ x, Measurable[𝓕 r.toNNReal] fun ω => Ψ r ω x) :
    Martingale (fieldDynkin Φ Φ2 Ψ B) 𝓕 P := by
  have hP := hB.isProbabilityMeasure'
  have hIci : ∀ {a b : ℝ}, 0 ≤ a → Icc a b ⊆ Ici (0 : ℝ) := fun ha r hr => ha.trans hr.1
  have hsub : ∀ (a b : ℝ≥0), Icc (a : ℝ) b ⊆ Ici (0 : ℝ) := fun a _ r hr =>
    le_trans a.coe_nonneg hr.1
  -- adaptedness
  have hMm : ∀ t : ℝ≥0, Measurable[𝓕 t] (fieldDynkin Φ Φ2 Ψ B t) := by
    intro t
    have hmono : ∀ r ∈ Icc (0 : ℝ) t, 𝓕 r.toNNReal ≤ 𝓕 t := fun r hr =>
      𝓕.mono (Real.toNNReal_le_iff_le_coe.2 hr.2)
    have h1 : Measurable[𝓕 t] fun ω => Φ t ω (B t ω) := by
      have h := hm0 t t.coe_nonneg
      rw [Real.toNNReal_coe] at h
      exact measurable_field_comp h (fun ω => continuous_iff_continuousAt.2 fun x =>
        (hd1 t t.coe_nonneg ω x).continuousAt) (hB.2.1 t)
    have h2 := measurable_integral_fieldGen (m := 𝓕 t) (B := B) (Φ2 := Φ2) (Ψ := Ψ) t.coe_nonneg
      (fun r hr => (hB.2.1 _).mono (hmono r hr) le_rfl) hBc
      (fun r hr x => (hm2 r hr.1 x).mono (hmono r hr) le_rfl)
      (fun r hr x => (hmΨ r hr.1 x).mono (hmono r hr) le_rfl)
      (fun ω => (hΨc ω).mono (prod_mono (hIci le_rfl) le_rfl))
      (fun ω => (hΦ2c ω).mono (prod_mono (hIci le_rfl) le_rfl))
    exact h1.sub h2
  -- integrability
  have hMb : ∀ (t : ℝ≥0) ω, |fieldDynkin Φ Φ2 Ψ B t ω| ≤ C + 3 * C / 2 * t := by
    intro t ω
    have h := abs_integral_fieldGen_le (B := B) t.coe_nonneg (fun r hr => hb2 r hr.1)
      (fun r hr => hbΨ r hr.1) ω
    rw [sub_zero] at h
    exact (abs_sub _ _).trans (add_le_add (hb0 t t.coe_nonneg ω _) h)
  have hMi : ∀ t, Integrable (fieldDynkin Φ Φ2 Ψ B t) P := fun t =>
    (integrable_const (C + 3 * C / 2 * t)).mono' ((hMm t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hMb t ω)
  refine ⟨fun t => (hMm t).stronglyMeasurable, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hMi t)
    (fun A _ _ => (hMi s).integrableOn) (fun A hA _ => ?_)
    ((hMm s).stronglyMeasurable.aestronglyMeasurable)).symm
  have hAm : MeasurableSet A := 𝓕.le s A hA
  set ξ : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hξdef
  have hξm : Measurable[𝓕 s] ξ := measurable_const.indicator hA
  have hξb : ∀ ω, |ξ ω| ≤ 1 := fun ω => by by_cases hω : ω ∈ A <;> simp [hξdef, hω]
  have hξA : ∀ f : Ω → ℝ, ∫ ω, ξ ω * f ω ∂P = ∫ ω in A, f ω ∂P := by
    intro f
    rw [← integral_indicator hAm]
    congr 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [hξdef, hω]
  have h0 := integral_mul_fieldIncr_eq_zero (P := P) (Φ1 := Φ1) hB hBc hst
    (fun r hr => hd1 r (hsub s t hr)) (fun r hr => hd2 r (hsub s t hr))
    (fun r hr => hlip r (hsub s t hr)) (fun ω x a b ha hab _ => htime ω x a b (s.coe_nonneg.trans ha) hab)
    (fun ω => (hΨc ω).mono (prod_mono (hsub s t) le_rfl))
    (fun ω => (hΦ2c ω).mono (prod_mono (hsub s t) le_rfl))
    (fun r hr => hb0 r (hsub s t hr)) (fun r hr => hb1 r (hsub s t hr))
    (fun r hr => hb2 r (hsub s t hr)) (fun r hr => hbΨ r (hsub s t hr))
    (fun r hr => hm0 r (hsub s t hr)) (fun r hr => hm1 r (hsub s t hr))
    (fun r hr => hm2 r (hsub s t hr)) (fun r hr => hmΨ r (hsub s t hr)) hξm hξb
  -- `M_t − M_s` is the increment of the identity
  have hint : ∀ ω (r : ℝ≥0), IntervalIntegrable (fun u => fieldGen Φ2 Ψ B u ω) volume 0 r := by
    intro ω r
    have hβ : ContinuousOn (fun r : ℝ => B r.toNNReal ω) (Icc 0 r) :=
      ((hBc ω).comp continuous_real_toNNReal).continuousOn
    have hS : Icc (0 : ℝ) r ⊆ Ici 0 := hIci le_rfl
    refine ContinuousOn.intervalIntegrable_of_Icc r.coe_nonneg ?_
    exact (continuousOn_field_path (ψ := fun u x => Ψ u ω x) ((hΨc ω).mono (prod_mono hS le_rfl))
      hβ).add (continuousOn_const.mul (continuousOn_field_path (ψ := fun u x => Φ2 u ω x)
        ((hΦ2c ω).mono (prod_mono hS le_rfl)) hβ))
  have hdiff : ∀ ω, fieldDynkin Φ Φ2 Ψ B t ω - fieldDynkin Φ Φ2 Ψ B s ω =
      Φ t ω (B t ω) - Φ s ω (B s ω) - ∫ u in (s : ℝ)..t, fieldGen Φ2 Ψ B u ω := by
    intro ω
    have h := intervalIntegral.integral_interval_sub_left (hint ω t) (hint ω s)
    simp only [fieldDynkin]
    rw [← h]; ring
  have hi : ∀ r, Integrable (fun ω => ξ ω * fieldDynkin Φ Φ2 Ψ B r ω) P := fun r =>
    (hMi r).bdd_mul (hξm.mono (𝓕.le s) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)
  have h1 : ∫ ω, ξ ω * (Φ t ω (B t ω) - Φ s ω (B s ω) - ∫ u in (s : ℝ)..t, fieldGen Φ2 Ψ B u ω) ∂P
      = (∫ ω, ξ ω * fieldDynkin Φ Φ2 Ψ B t ω ∂P) - ∫ ω, ξ ω * fieldDynkin Φ Φ2 Ψ B s ω ∂P := by
    rw [← integral_sub (hi t) (hi s)]
    congr 1; funext ω; rw [← hdiff ω]; ring
  rw [h1, sub_eq_zero, hξA, hξA] at h0
  exact h0.symm

end Main

end InteractingSLE.Ito
