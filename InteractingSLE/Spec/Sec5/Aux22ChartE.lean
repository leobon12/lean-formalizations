/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22ChartEFlow
import InteractingSLE.Spec.Sec4.Remark410

/-!
# Aux. lemma 22, chart `E`, step 3: the hitting case for strip flow lines with one height on the span

Packet PROVE-SEC5-M (specification §4.1, Aux. lemma 22, `source/spec/p097-144.md#aux-22`, p. 113; PROVE-SEC5-L's
"What remains" 1). In the chart `E(z) = e^{πz} − 1` of `Sec4.IsStripFlowLine`, the strip field's transported data are
`bL` on `(−1, ∞)` and `bU + πχ` on `(−∞, −1)`; the span `I = (u, v) + i` maps to `(−1 − e^{πv}, −1 − e^{πu})`
(`(−1 − e^{πv}, −1)` for `u = −∞`). The hypotheses of Aux. lemma 22 (`Sec4.IsAux22SpanData`) become the value
conditions of `IsFlowLine.ae_exists_hit_left` with `A = 1 + e^{πu}` and `C = 1 + e^{πv}`:

* on `(−A, 0)`: lower data left of `0` (at most `−λ + πχ`) and upper data left of `u` (at most `−λ`, plus `πχ`);
* on `(−C, −A)`: one upper height `a ∈ (−λ, λ)`, plus `πχ`;
* on `(−∞, −C)`: upper data right of `v` (at least `λ`, plus `πχ`); on `(0, ∞)`: lower data right of `0`.

**`ae_hasFirstUpperEndpointIn_of_oneHeight`** proves the hitting case of Aux. lemma 22 (`HasFirstUpperEndpointIn`)
for `0 < κ ≤ 4`, finite `v`, constant upper data on `I` and vanishing seed weights (`bL(0⁻) = −λ`, `bL(0⁺) = λ`).
Consumers: Figure 4.6(a) (`ae_hasFirstUpperEndpointIn_fig46`, `ae_remark48a_top_fig46`: the input of Lemma 4.7 used
through `Sec4.ae_remark48a_top_of_aux22Hit`), Remark 4.10 with zero seeds
(`ae_hasFirstUpperEndpointIn_rem410_of_zeroSeed`).

**Nonzero seed weights** (Remark 4.10's general lower data, Figure 5.1): all the bookkeeping is done here, from one
named chordal input, `SeedSpanHitStatement κ` (`Aux22ChartESpan.lean`; it needs Zhan's strip endpoint theorem with
seed groups): `ae_hasFirstUpperEndpointIn_of_oneHeight_of_seedSpanHit`,
`ae_hasFirstUpperEndpointIn_rem410_of_seedSpanHit`, `ae_remark48a_top_of_oneHeight_of_seedSpanHit`. Both versions go
through `ae_hasFirstUpperEndpointIn_of_coreHit` (`CoreHit`: the flow-line hitting lemma for the transported data).
Several heights on `I` need Aux. lemma 21 with upper marks.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Real NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE

namespace Sec5

namespace Aux22ChartE

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)
open Sec4 (stripHData stripHJumps IsStripFlowLine IsAux22SpanData HasFirstUpperEndpointIn)

/-- `χ ≥ 0` for `κ ≤ 4`. -/
theorem chiC_nonneg {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) : 0 ≤ chiC κ := by
  have h := Sec4.pi_mul_chiC hκ
  have hl := Sec4.sleLambda_pos hκ
  have : 0 ≤ π * chiC κ := by rw [h]; exact mul_nonneg (by linarith) hl.le
  exact (mul_nonneg_iff_of_pos_left Real.pi_pos).1 this

/-- `e^{πx} < e^{πy}` gives `x < y`. -/
theorem lt_of_exp_pi_lt {x y : ℝ} (h : Real.exp (π * x) < Real.exp (π * y)) : x < y :=
  (mul_lt_mul_iff_of_pos_left Real.pi_pos).1 (Real.exp_lt_exp.1 h)

/-- `e^{π · (log r)/π} = r` for `r > 0`. -/
theorem exp_pi_mul_log_div {r : ℝ} (hr : 0 < r) : Real.exp (π * (Real.log r / π)) = r := by
  rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log hr]

variable {κ : ℝ} {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}

/-- A point `y > −1` off the transported jumps is the `E`-image `e^{πx} − 1` of a lower point `x` off the lower
jumps, and the transported data there are `bL x`. -/
theorem exists_lower_of_notMem {y : ℝ} (hy : -1 < y) (hyJ : y ∉ stripHJumps JL JU) :
    ∃ x, x ∉ JL ∧ Real.exp (π * x) = y + 1 ∧ stripHData κ bL bU y = bL x := by
  have hpos : 0 < y + 1 := by linarith
  have hxy : Real.exp (π * (Real.log (y + 1) / π)) - 1 = y := by rw [exp_pi_mul_log_div hpos]; ring
  refine ⟨Real.log (y + 1) / π, fun h => hyJ ?_, by rw [exp_pi_mul_log_div hpos], ?_⟩
  · simp only [stripHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inl ⟨_, h, hxy⟩)
  · conv_lhs => rw [← hxy]
    rw [Sec4.stripHData_lower]

/-- A point `y < −1` off the transported jumps is the `E`-image `−e^{πx} − 1` of an upper point `x + i` off the
upper jumps, and the transported data there are `bU x + πχ`. -/
theorem exists_upper_of_notMem {y : ℝ} (hy : y < -1) (hyJ : y ∉ stripHJumps JL JU) :
    ∃ x, x ∉ JU ∧ Real.exp (π * x) = -y - 1 ∧ stripHData κ bL bU y = bU x + π * chiC κ := by
  have hpos : 0 < -y - 1 := by linarith
  have hxy : -Real.exp (π * (Real.log (-y - 1) / π)) - 1 = y := by rw [exp_pi_mul_log_div hpos]; ring
  refine ⟨Real.log (-y - 1) / π, fun h => hyJ ?_, by rw [exp_pi_mul_log_div hpos], ?_⟩
  · simp only [stripHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inr ⟨_, h, hxy⟩)
  · conv_lhs => rw [← hxy]
    rw [Sec4.stripHData_upper]

/-- The strip end `−1` is a transported jump candidate. -/
theorem neg_one_mem_stripHJumps : (-1 : ℝ) ∈ stripHJumps JL JU := Finset.mem_insert_self _ _

/-- Piecewise-constant data equal their left limit at `z` on an interval `(lo, z)`. -/
theorem exists_forall_Ioo_eq_leftLim {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (z : ℝ) : ∃ lo < z, ∀ t ∈ Ioo lo z, b t = leftLim b z := by
  set M : Finset ℝ := insert (z - 1) (J.filter (· < z)) with hM
  have hMne : M.Nonempty := Finset.insert_nonempty _ _
  have hmz : M.max' hMne < z := by
    rcases Finset.mem_insert.1 (M.max'_mem hMne) with h' | h'
    · rw [h']; linarith
    · exact (Finset.mem_filter.1 h').2
  have hnoJ : ∀ w ∈ J, w ∉ Ioo (M.max' hMne) z := fun w hwJ hw =>
    absurd (M.le_max' w (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hwJ, hw.2⟩))) (not_le.2 hw.1)
  have ht₀ : (M.max' hMne + z) / 2 ∈ Ioo (M.max' hMne) z := ⟨by linarith, by linarith⟩
  have hl : leftLim b z = b ((M.max' hMne + z) / 2) := Sec4.leftLim_eq_of_forall hmz fun s hs =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ ht₀ hs
  exact ⟨_, hmz, fun t ht => by rw [hl]; exact Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ ht₀ ht⟩

/-- Piecewise-constant data equal their right limit at `z` on an interval `(z, hi)`. -/
theorem exists_forall_Ioo_eq_rightLim {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (z : ℝ) : ∃ hi > z, ∀ t ∈ Ioo z hi, b t = rightLim b z := by
  set M : Finset ℝ := insert (z + 1) (J.filter (z < ·)) with hM
  have hMne : M.Nonempty := Finset.insert_nonempty _ _
  have hzm : z < M.min' hMne := by
    rcases Finset.mem_insert.1 (M.min'_mem hMne) with h' | h'
    · rw [h']; linarith
    · exact (Finset.mem_filter.1 h').2
  have hnoJ : ∀ w ∈ J, w ∉ Ioo z (M.min' hMne) := fun w hwJ hw =>
    absurd (M.min'_le w (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hwJ, hw.1⟩))) (not_le.2 hw.2)
  have ht₀ : (z + M.min' hMne) / 2 ∈ Ioo z (M.min' hMne) := ⟨by linarith, by linarith⟩
  have hr : rightLim b z = b ((z + M.min' hMne) / 2) := Sec4.rightLim_eq_of_forall hzm fun s hs =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ ht₀ hs
  exact ⟨_, hzm, fun t ht => by rw [hr]; exact Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ ht₀ ht⟩

/-- The transported data have the lower data's left limit at the seed `0`. -/
theorem leftLim_stripHData_zero (hbL : IsPiecewiseConstantBoundaryData bL JL) :
    leftLim (stripHData κ bL bU) 0 = leftLim bL 0 := by
  obtain ⟨lo, hlo, hc⟩ := exists_forall_Ioo_eq_leftLim hbL 0
  have hlo' : Real.exp (π * lo) - 1 < 0 := by
    have : Real.exp (π * lo) < 1 := Real.exp_lt_one_iff.2 (mul_neg_of_pos_of_neg Real.pi_pos hlo)
    linarith
  refine Sec4.leftLim_eq_of_forall_notMem (stripHJumps JL ∅) hlo' fun y hy hyJ => ?_
  have hy1 : -1 < y := by linarith [hy.1, Real.exp_pos (π * lo)]
  obtain ⟨x, -, hxe, hbx⟩ := exists_lower_of_notMem (κ := κ) (bL := bL) (bU := bU) hy1 hyJ
  rw [hbx]
  refine hc x ⟨lt_of_exp_pi_lt (by linarith [hy.1]), lt_of_exp_pi_lt (by rw [mul_zero, Real.exp_zero]; linarith [hy.2])⟩

/-- The transported data have the lower data's right limit at the seed `0`. -/
theorem rightLim_stripHData_zero (hbL : IsPiecewiseConstantBoundaryData bL JL) :
    rightLim (stripHData κ bL bU) 0 = rightLim bL 0 := by
  obtain ⟨hi, hhi, hc⟩ := exists_forall_Ioo_eq_rightLim hbL 0
  have hhi' : 0 < Real.exp (π * hi) - 1 := by
    have : 1 < Real.exp (π * hi) := Real.one_lt_exp_iff.2 (mul_pos Real.pi_pos hhi)
    linarith
  refine Sec4.rightLim_eq_of_forall_notMem (stripHJumps JL ∅) hhi' fun y hy hyJ => ?_
  obtain ⟨x, -, hxe, hbx⟩ := exists_lower_of_notMem (κ := κ) (bL := bL) (bU := bU) (by linarith [hy.1]) hyJ
  rw [hbx]
  refine hc x ⟨lt_of_exp_pi_lt (by rw [mul_zero, Real.exp_zero]; linarith [hy.1]), lt_of_exp_pi_lt (by linarith [hy.2])⟩


/-- The hypothesis shape of the flow-line hitting lemmas (`IsFlowLine.ae_exists_hit_left` and its seeded form) for the
transported data, with the left end of the span at `−A` (`A ≥ 1`, `A − 1 < e^{πv}`) and the right end at
`−(1 + e^{πv})`. -/
def CoreHit (κ : ℝ) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ) (v : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∀ A : ℝ, 1 ≤ A → A - 1 < Real.exp (π * v) → ∀ a : ℝ, -sleLambda κ < a → a < sleLambda κ →
    (∀ y, -A < y → y < 0 → y ∉ stripHJumps JL JU → stripHData κ bL bU y ≤ -sleLambda κ + π * chiC κ) →
    (∀ y, -(1 + Real.exp (π * v)) < y → y < -A → y ∉ stripHJumps JL JU →
      stripHData κ bL bU y = a + π * chiC κ) →
    (∀ y, y < -(1 + Real.exp (π * v)) → y ∉ stripHJumps JL JU →
      sleLambda κ + π * chiC κ ≤ stripHData κ bL bU y) →
    (∀ y, 0 < y → y ∉ stripHJumps JL JU → sleLambda κ - π * chiC κ ≤ stripHData κ bL bU y) →
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ (∀ s : ℝ≥0, s < t → ∀ z : ℝ, z ≠ 0 → η ω s ≠ z) ∧
      ∃ x : ℝ, -(1 + Real.exp (π * v)) < x ∧ x < -A ∧ η ω t = x

/-- The hitting case with the left end of the span read through `A` (`A − 1 = e^{πu}`, or `0` for `u = −∞`), from
the flow-line hitting lemma in the form `CoreHit`. -/
theorem ae_hasFirstUpperEndpointIn_of_coreHit_aux (hκ : 0 < κ) (hκ4 : κ ≤ 4) {u : EReal} {v A : ℝ}
    (hA1 : 1 ≤ A) (hAv : A - 1 < Real.exp (π * v)) (hAu : ∀ x : ℝ, u < (x : EReal) ↔ A - 1 < Real.exp (π * x))
    (hAu' : ∀ x : ℝ, (x : EReal) < u ↔ Real.exp (π * x) < A - 1)
    (hdat : IsAux22SpanData κ u v bL bU JL JU)
    (hone : ∃ a, ∀ x : ℝ, x ∉ JU → u < (x : EReal) → x < v → bU x = a)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hcore : CoreHit κ bL bU JL JU v P η ζ) :
    ∀ᵐ ω ∂P, HasFirstUpperEndpointIn u v (η ω) (ζ ω) := by
  obtain ⟨-, -, hlow, hI, hleft, hright⟩ := hdat
  obtain ⟨a, ha⟩ := hone
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (chiC_nonneg hκ hκ4)
  have hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda κ + π * chiC κ := by
    rcases hlow with ⟨h1, -⟩ | ⟨h1, -⟩
    · intro x hx _; rw [h1 x hx]; linarith
    · exact h1
  have hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda κ - π * chiC κ ≤ bL x := by
    rcases hlow with ⟨-, h2⟩ | ⟨-, h2⟩
    · intro x hx _; rw [h2 x hx]; linarith
    · exact h2
  set C := 1 + Real.exp (π * v) with hC
  -- the height on the span
  obtain ⟨y₀, hy₀1, hy₀2, hy₀J⟩ := Sec4.exists_mem_Ioo_not_mem (stripHJumps JL JU) (show -C < -A by linarith)
  obtain ⟨x₀, hx₀J, hx₀e, -⟩ := exists_upper_of_notMem (κ := κ) (bL := bL) (bU := bU) (by linarith : y₀ < -1)
    hy₀J
  have hux₀ : u < (x₀ : EReal) := (hAu x₀).2 (by linarith)
  have hx₀v : x₀ < v := lt_of_exp_pi_lt (by linarith)
  have hav := hI x₀ hx₀J hux₀ (by exact_mod_cast hx₀v)
  rw [ha x₀ hx₀J hux₀ hx₀v] at hav
  -- the value conditions
  have h1 : ∀ y, -A < y → y < 0 → y ∉ stripHJumps JL JU →
      stripHData κ bL bU y ≤ -sleLambda κ + π * chiC κ := by
    intro y hy1 hy2 hyJ
    rcases lt_trichotomy y (-1) with hlt | heq | hgt
    · obtain ⟨x, hxJ, hxe, hbx⟩ := exists_upper_of_notMem (κ := κ) (bL := bL) (bU := bU) hlt hyJ
      rw [hbx]
      linarith [hleft x hxJ ((hAu' x).2 (by linarith))]
    · exact absurd (heq ▸ neg_one_mem_stripHJumps) hyJ
    · obtain ⟨x, hxJ, hxe, hbx⟩ := exists_lower_of_notMem (κ := κ) (bL := bL) (bU := bU) hgt hyJ
      rw [hbx]
      exact hlowL x (lt_of_exp_pi_lt (by rw [mul_zero, Real.exp_zero]; linarith)) hxJ
  have h2 : ∀ y, -C < y → y < -A → y ∉ stripHJumps JL JU → stripHData κ bL bU y = a + π * chiC κ := by
    intro y hy1 hy2 hyJ
    obtain ⟨x, hxJ, hxe, hbx⟩ := exists_upper_of_notMem (κ := κ) (bL := bL) (bU := bU) (by linarith) hyJ
    rw [hbx, ha x hxJ ((hAu x).2 (by linarith)) (lt_of_exp_pi_lt (by linarith))]
  have h3 : ∀ y, y < -C → y ∉ stripHJumps JL JU → sleLambda κ + π * chiC κ ≤ stripHData κ bL bU y := by
    intro y hy hyJ
    obtain ⟨x, hxJ, hxe, hbx⟩ := exists_upper_of_notMem (κ := κ) (bL := bL) (bU := bU)
      (by linarith [Real.exp_pos (π * v)]) hyJ
    rw [hbx]
    have hvx : v < x := lt_of_exp_pi_lt (by linarith)
    linarith [hright x hxJ (by exact_mod_cast hvx)]
  have h4 : ∀ y, 0 < y → y ∉ stripHJumps JL JU → sleLambda κ - π * chiC κ ≤ stripHData κ bL bU y := by
    intro y hy hyJ
    obtain ⟨x, hxJ, hxe, hbx⟩ := exists_lower_of_notMem (κ := κ) (bL := bL) (bU := bU) (by linarith) hyJ
    rw [hbx]
    exact hlowR x (lt_of_exp_pi_lt (by rw [mul_zero, Real.exp_zero]; linarith)) hxJ
  filter_upwards [hcore A hA1 hAv a hav.1 hav.2 h1 h2 h3 h4] with ω ⟨t, htζ, havoid, x, hx1, hx2, hxt⟩
  have hpos : 0 < -x - 1 := by linarith
  have he := exp_pi_mul_log_div hpos
  refine ⟨t, htζ, fun s hs hmem => ?_, Real.log (-x - 1) / π, (hAu _).2 (by rw [he]; linarith),
    by exact_mod_cast lt_of_exp_pi_lt (by rw [he]; linarith), ?_⟩
  · obtain ⟨r, hr, hre⟩ := hmem
    exact havoid s hs r (by linarith [show r < -1 from hr]) hre.symm
  · rw [hxt, he]
    congr 1
    ring

/-- **Aux. lemma 22, hitting case, one height on `I`, from the flow-line hitting lemma** (the case split on the left
end `u ∈ [−∞, v)` of the span). -/
theorem ae_hasFirstUpperEndpointIn_of_coreHit (hκ : 0 < κ) (hκ4 : κ ≤ 4) {u : EReal} {v : ℝ}
    (huv : u < v) (hdat : IsAux22SpanData κ u v bL bU JL JU)
    (hone : ∃ a, ∀ x : ℝ, x ∉ JU → u < (x : EReal) → x < v → bU x = a)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hcore : CoreHit κ bL bU JL JU v P η ζ) :
    ∀ᵐ ω ∂P, HasFirstUpperEndpointIn u v (η ω) (ζ ω) := by
  induction u using EReal.rec with
  | bot =>
    refine ae_hasFirstUpperEndpointIn_of_coreHit_aux hκ hκ4 (A := 1) le_rfl
      (by rw [sub_self]; exact Real.exp_pos _) (fun x => ?_) (fun x => ?_) hdat hone hcore
    · rw [sub_self]
      exact ⟨fun _ => Real.exp_pos _, fun _ => EReal.bot_lt_coe x⟩
    · rw [sub_self]
      exact ⟨fun hx => absurd hx not_lt_bot, fun hx => absurd hx (not_lt.2 (Real.exp_pos _).le)⟩
  | coe u₀ =>
    have hu₀ : u₀ < v := by exact_mod_cast huv
    refine ae_hasFirstUpperEndpointIn_of_coreHit_aux hκ hκ4 (A := 1 + Real.exp (π * u₀))
      (by linarith [Real.exp_pos (π * u₀)])
      (by rw [add_sub_cancel_left]; exact Real.exp_lt_exp.2 ((mul_lt_mul_iff_of_pos_left Real.pi_pos).2 hu₀))
      (fun x => ?_) (fun x => ?_) hdat hone hcore
    · rw [add_sub_cancel_left, EReal.coe_lt_coe_iff]
      exact ⟨fun hx => Real.exp_lt_exp.2 ((mul_lt_mul_iff_of_pos_left Real.pi_pos).2 hx), lt_of_exp_pi_lt⟩
    · rw [add_sub_cancel_left, EReal.coe_lt_coe_iff]
      exact ⟨fun hx => Real.exp_lt_exp.2 ((mul_lt_mul_iff_of_pos_left Real.pi_pos).2 hx), lt_of_exp_pi_lt⟩
  | top => exact absurd huv (not_lt.2 le_top)

/-- **Aux. lemma 22, hitting case, one height on `I`, zero seed weights** (`0 < κ ≤ 4`, chart `E`). For the strip
flow line of data satisfying `IsAux22SpanData κ u v` with `v` finite, constant upper data on `I = (u, v) + i`
(off the jumps) and lower data with `bL(0⁻) = −λ`, `bL(0⁺) = λ`, almost surely the trace has an actual first upper
endpoint at a finite point of `I`. -/
theorem ae_hasFirstUpperEndpointIn_of_oneHeight (hκ : 0 < κ) (hκ4 : κ ≤ 4) {u : EReal} {v : ℝ}
    (huv : u < v) (hdat : IsAux22SpanData κ u v bL bU JL JU)
    (hone : ∃ a, ∀ x : ℝ, x ∉ JU → u < (x : EReal) → x < v → bU x = a)
    (hsL : leftLim bL 0 = -sleLambda κ) (hsR : rightLim bL 0 = sleLambda κ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsStripFlowLine κ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, HasFirstUpperEndpointIn u v (η ω) (ζ ω) := by
  have hb := Sec4.isPiecewiseConstantBoundaryData_stripHData κ hdat.1 hdat.2.1
  refine ae_hasFirstUpperEndpointIn_of_coreHit hκ hκ4 huv hdat hone
    fun A hA1 hAv a ha ha' h1 h2 h3 h4 => ?_
  exact IsFlowLine.ae_exists_hit_left hκ hκ4 hb (by rw [leftLim_stripHData_zero hdat.1, hsL])
    (by rw [rightLim_stripHData_zero hdat.1, hsR]) (by linarith) (by linarith) ha ha' h1 h2 h3 h4 hfl

/-- **Aux. lemma 22, hitting case, one height on `I`, any seed weights, from the named chordal input**
(`SeedSpanHitStatement κ`, `0 < κ ≤ 4`). Same as `ae_hasFirstUpperEndpointIn_of_oneHeight` without the condition on
the seed weights. -/
theorem ae_hasFirstUpperEndpointIn_of_oneHeight_of_seedSpanHit (hseed : SeedSpanHitStatement.{u} κ) (hκ : 0 < κ)
    (hκ4 : κ ≤ 4) {u : EReal} {v : ℝ} (huv : u < v) (hdat : IsAux22SpanData κ u v bL bU JL JU)
    (hone : ∃ a, ∀ x : ℝ, x ∉ JU → u < (x : EReal) → x < v → bU x = a)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsStripFlowLine κ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, HasFirstUpperEndpointIn u v (η ω) (ζ ω) := by
  have hb := Sec4.isPiecewiseConstantBoundaryData_stripHData κ hdat.1 hdat.2.1
  refine ae_hasFirstUpperEndpointIn_of_coreHit hκ hκ4 huv hdat hone
    fun A hA1 hAv a ha ha' h1 h2 h3 h4 => ?_
  exact IsFlowLine.ae_exists_hit_left_of_seedSpanHit hseed hκ hb (by linarith) (by linarith) ha ha' h1 h2 h3 h4
    hfl

/-- **Remark 4.8 (a) at `T_top`** for one height on `I` and zero seed weights (unconditional form of
`Sec4.ae_remark48a_top_of_aux22Hit` for these data). -/
theorem ae_remark48a_top_of_oneHeight (hκ : 0 < κ) (hκ4 : κ ≤ 4) {u : EReal} {v : ℝ}
    (huv : u < v) (hdat : IsAux22SpanData κ u v bL bU JL JU)
    (hone : ∃ a, ∀ x : ℝ, x ∉ JU → u < (x : EReal) → x < v → bU x = a)
    (hsL : leftLim bL 0 = -sleLambda κ) (hsR : rightLim bL 0 = sleLambda κ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsStripFlowLine κ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, Sec4.firstUpperContact (η ω) ≠ ⊤ ∧ Sec4.firstUpperContact (η ω) ≤ ζ ω ∧
      0 < (Sec4.firstUpperContact (η ω)).toReal ∧
      ContinuousOn (fun s : ℝ => η ω s.toNNReal) (Icc 0 (Sec4.firstUpperContact (η ω)).toReal) := by
  have h22 := ae_hasFirstUpperEndpointIn_of_oneHeight hκ hκ4 huv hdat hone hsL hsR hfl
  obtain ⟨-, -, W, -, -, -, -, -, htr⟩ := hfl
  filter_upwards [h22, htr] with ω hω hη
  have hη' : IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω) := by
    simpa only [Complex.ofReal_zero, sub_zero] using hη
  exact Sec4.remark48a_top_of_hasFirstUpperEndpointIn hη' hω

/-- The basic lower data have left limit `−λ` at the seed. -/
theorem leftLim_fig46Lower (κ : ℝ) : leftLim (Sec4.fig46Lower κ) 0 = -sleLambda κ :=
  Sec4.leftLim_eq_of_forall (by norm_num : (-1 : ℝ) < 0) fun t ht => by simp [Sec4.fig46Lower, ht.2]

/-- The basic lower data have right limit `λ` at the seed. -/
theorem rightLim_fig46Lower (κ : ℝ) : rightLim (Sec4.fig46Lower κ) 0 = sleLambda κ :=
  Sec4.rightLim_eq_of_forall (by norm_num : (0 : ℝ) < 1) fun t ht => by
    simp [Sec4.fig46Lower, not_lt.2 ht.1.le]

/-- **Figure 4.6(a)** (`0 < κ < 4`; Lemma 4.7 proof, p. 118): almost surely the flow line has an actual finite first
upper endpoint strictly left of `z₀`. -/
theorem ae_hasFirstUpperEndpointIn_fig46 (hκ : 0 < κ) (hκ4 : κ < 4) (x₀ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripFlowLine κ (Sec4.fig46Lower κ) (Sec4.fig46Upper κ x₀) {0} {x₀} P h η ζ) :
    ∀ᵐ ω ∂P, HasFirstUpperEndpointIn ⊥ (x₀ : EReal) (η ω) (ζ ω) :=
  ae_hasFirstUpperEndpointIn_of_oneHeight hκ hκ4.le (EReal.bot_lt_coe x₀) (Sec4.isAux22SpanData_fig46 hκ hκ4 x₀)
    ⟨-sleLambda κ + π * chiC κ, fun x _ _ hx => by simp [Sec4.fig46Upper, hx]⟩ (leftLim_fig46Lower κ)
    (rightLim_fig46Lower κ) hfl

/-- **Remark 4.8 (a) at `T_top` for Figure 4.6(a)** (`0 < κ < 4`): `T_top` is almost surely finite, positive, at
most the lifetime, and the trace is continuous on `[0, T_top]`. -/
theorem ae_remark48a_top_fig46 (hκ : 0 < κ) (hκ4 : κ < 4) (x₀ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripFlowLine κ (Sec4.fig46Lower κ) (Sec4.fig46Upper κ x₀) {0} {x₀} P h η ζ) :
    ∀ᵐ ω ∂P, Sec4.firstUpperContact (η ω) ≠ ⊤ ∧ Sec4.firstUpperContact (η ω) ≤ ζ ω ∧
      0 < (Sec4.firstUpperContact (η ω)).toReal ∧
      ContinuousOn (fun s : ℝ => η ω s.toNNReal) (Icc 0 (Sec4.firstUpperContact (η ω)).toReal) :=
  ae_remark48a_top_of_oneHeight hκ hκ4.le (EReal.bot_lt_coe x₀) (Sec4.isAux22SpanData_fig46 hκ hκ4 x₀)
    ⟨-sleLambda κ + π * chiC κ, fun x _ _ hx => by simp [Sec4.fig46Upper, hx]⟩ (leftLim_fig46Lower κ)
    (rightLim_fig46Lower κ) hfl

/-- **Remark 4.10, the actual first contact in the exposed left interval, zero seed weights** (unconditional form
of `Sec4.ae_hasFirstUpperEndpointIn_rem410_of_aux22Hit` when `bL(0⁻) = −λ`, `bL(0⁺) = λ`). -/
theorem ae_hasFirstUpperEndpointIn_rem410_of_zeroSeed (hκ : 0 < κ) (hκ4 : κ < 4) {u v : ℝ} (huv : u < v)
    (hbL : IsPiecewiseConstantBoundaryData bL JL) (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda κ + π * chiC κ)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda κ ≤ bL x)
    (hleft : ∀ x : ℝ, x ∉ JU → x < u → bU x ≤ -sleLambda κ)
    (hspan : ∀ x : ℝ, x ∉ JU → u < x → x < v → bU x = -sleLambda κ + π * chiC κ)
    (hright : ∀ x : ℝ, x ∉ JU → v < x → sleLambda κ ≤ bU x)
    (hsL : leftLim bL 0 = -sleLambda κ) (hsR : rightLim bL 0 = sleLambda κ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsStripFlowLine κ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, HasFirstUpperEndpointIn (u : EReal) (v : EReal) (η ω) (ζ ω) :=
  ae_hasFirstUpperEndpointIn_of_oneHeight hκ hκ4.le (by exact_mod_cast huv)
    (Sec4.isAux22SpanData_rem410 hκ hκ4 hbL hbU hlowL hlowR hleft hspan hright)
    ⟨_, fun x hxJ hux hxv => hspan x hxJ (by exact_mod_cast hux) hxv⟩ hsL hsR hfl

/-- **Remark 4.10, the actual first contact in the exposed left interval, any seed weights, from the named chordal
input** (`SeedSpanHitStatement κ`): `Sec4.ae_hasFirstUpperEndpointIn_rem410_of_aux22Hit` with `Sec4.Aux22HitStatement`
replaced by the chordal seeded span statement. -/
theorem ae_hasFirstUpperEndpointIn_rem410_of_seedSpanHit (hseed : SeedSpanHitStatement.{u} κ) (hκ : 0 < κ)
    (hκ4 : κ < 4) {u v : ℝ} (huv : u < v)
    (hbL : IsPiecewiseConstantBoundaryData bL JL) (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda κ + π * chiC κ)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda κ ≤ bL x)
    (hleft : ∀ x : ℝ, x ∉ JU → x < u → bU x ≤ -sleLambda κ)
    (hspan : ∀ x : ℝ, x ∉ JU → u < x → x < v → bU x = -sleLambda κ + π * chiC κ)
    (hright : ∀ x : ℝ, x ∉ JU → v < x → sleLambda κ ≤ bU x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsStripFlowLine κ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, HasFirstUpperEndpointIn (u : EReal) (v : EReal) (η ω) (ζ ω) :=
  ae_hasFirstUpperEndpointIn_of_oneHeight_of_seedSpanHit hseed hκ hκ4.le (by exact_mod_cast huv)
    (Sec4.isAux22SpanData_rem410 hκ hκ4 hbL hbU hlowL hlowR hleft hspan hright)
    ⟨_, fun x hxJ hux hxv => hspan x hxJ (by exact_mod_cast hux) hxv⟩ hfl

/-- **Remark 4.8 (a) at `T_top`, one height on `I`, any seed weights, from the named chordal input**. -/
theorem ae_remark48a_top_of_oneHeight_of_seedSpanHit (hseed : SeedSpanHitStatement.{u} κ) (hκ : 0 < κ)
    (hκ4 : κ ≤ 4) {u : EReal} {v : ℝ} (huv : u < v) (hdat : IsAux22SpanData κ u v bL bU JL JU)
    (hone : ∃ a, ∀ x : ℝ, x ∉ JU → u < (x : EReal) → x < v → bU x = a)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsStripFlowLine κ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, Sec4.firstUpperContact (η ω) ≠ ⊤ ∧ Sec4.firstUpperContact (η ω) ≤ ζ ω ∧
      0 < (Sec4.firstUpperContact (η ω)).toReal ∧
      ContinuousOn (fun s : ℝ => η ω s.toNNReal) (Icc 0 (Sec4.firstUpperContact (η ω)).toReal) := by
  have h22 := ae_hasFirstUpperEndpointIn_of_oneHeight_of_seedSpanHit hseed hκ hκ4 huv hdat hone hfl
  obtain ⟨-, -, W, -, -, -, -, -, htr⟩ := hfl
  filter_upwards [h22, htr] with ω hω hη
  have hη' : IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω) := by
    simpa only [Complex.ofReal_zero, sub_zero] using hη
  exact Sec4.remark48a_top_of_hasFirstUpperEndpointIn hη' hω

end Aux22ChartE

end Sec5

end InteractingSLE
