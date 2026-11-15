/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Prob41Lemmas

/-!
# Lemma 4.3 for `a ≥ Λ`, Lemma 4.5, and Aux. lemma 22 with all upper heights `≥ Λ`

Packet PROVE-SEC4-A3. Specification §4.1 (`source/spec/p097-144.md`, pp. 105–108, 115). The flow lines in the two
charts used by the source proofs, with the transported boundary data (rule (1.4); the arguments of the chart
derivatives are SEC4-A's `StripMaps.lean`):

* the chart `ψ(z) = 1 − e^{−πz}` (proof of Lemma 4.3, case `a ≥ Λ`, and of the all-upper-positive alternative
  of Aux. lemma 22): target the **left** strip end; the lower line goes to `(−∞, 1)` with unchanged values, the
  upper line to `(1, ∞)` with values decreased by `πX` (`leftEndHData`);
* the chart `ψ(z) = (e^{πz} − 1)/(e^{πz} + q)`, `q = e^{πx₀}` (proof of Lemma 4.5): target the upper point
  `z₀ = x₀ + i`; the lower line goes to `(−1/q, 1)` unchanged, the upper arc left of `z₀` to `(−∞, −1/q)` with
  values increased by `πX`, the upper arc right of `z₀` to `(1, ∞)` with values decreased by `πX`
  (`stripQHData`).

In each chart, Remark 4.1's lower-data condition and the upper-height condition of the lemma give the boundary
condition of `IsFlowLine.ae_trace_ne_real`: the flow line has infinite lifetime and never touches `ℝ \ {0}`, so in
particular never hits the images of the upper arcs. With Aux. lemma 7 (`Aux7Statement`) it tends to the target.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE

namespace Sec4

variable {k : ℝ}

/-! ### The chart `1 − e^{−πz}` (target the left strip end) -/

/-- The boundary data on `∂ℍ` of the image under `1 − e^{−πz}` of a strip field with lower data `bL` and upper
data `bU`: `bL(ψ⁻¹ y)` on `(−∞, 1)` and `bU(Re ψ⁻¹ y) − πX` on `(1, ∞)` (`arg ψ′ = −π` on the upper line,
`leftEndChart_upper_height_ge`). The value at `1` is irrelevant. -/
def leftEndHData (k : ℝ) (bL bU : ℝ → ℝ) (y : ℝ) : ℝ :=
  if y < 1 then bL (-Real.log (1 - y) / π) else bU (-Real.log (y - 1) / π) - π * chiC k

/-- The jump candidates of `leftEndHData`: the image `1` of the right strip end and the images of the lower and
upper jump candidates. -/
def leftEndHJumps (JL JU : Finset ℝ) : Finset ℝ :=
  insert 1 (JL.image (fun x => 1 - Real.exp (-(π * x))) ∪
    JU.image (fun x => 1 + Real.exp (-(π * x))))

theorem leftEndHData_of_lt {bL bU : ℝ → ℝ} {y : ℝ} (hy : y < 1) :
    leftEndHData k bL bU y = bL (-Real.log (1 - y) / π) := ite_eq_left hy

theorem leftEndHData_of_gt {bL bU : ℝ → ℝ} {y : ℝ} (hy : 1 < y) :
    leftEndHData k bL bU y = bU (-Real.log (y - 1) / π) - π * chiC k :=
  ite_eq_right (not_lt.2 hy.le)

theorem one_sub_exp_neg_log {y : ℝ} (hy : y < 1) :
    1 - Real.exp (-(π * (-Real.log (1 - y) / π))) = y := by
  rw [mul_div_cancel₀ _ Real.pi_pos.ne', neg_neg, Real.exp_log (by linarith)]
  ring

theorem one_add_exp_neg_log {y : ℝ} (hy : 1 < y) :
    1 + Real.exp (-(π * (-Real.log (y - 1) / π))) = y := by
  rw [mul_div_cancel₀ _ Real.pi_pos.ne', neg_neg, Real.exp_log (by linarith)]
  ring

/-- Piecewise-constant strip data transport to piecewise-constant data on `∂ℍ`. -/
theorem isPiecewiseConstantBoundaryData_leftEndHData {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hL : IsPiecewiseConstantBoundaryData bL JL) (hU : IsPiecewiseConstantBoundaryData bU JU) :
    IsPiecewiseConstantBoundaryData (leftEndHData k bL bU) (leftEndHJumps JL JU) := by
  intro y hy
  simp only [leftEndHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hy
  obtain ⟨hy1, hyL, hyU⟩ := hy
  rcases lt_or_gt_of_ne hy1 with hlt | hgt
  · set x := -Real.log (1 - y) / π with hx
    have hxJ : x ∉ JL := fun h => hyL ⟨x, h, one_sub_exp_neg_log hlt⟩
    have hcont : ContinuousAt (fun y' : ℝ => -Real.log (1 - y') / π) y := by
      have hf : ContinuousAt (fun y' : ℝ => 1 - y') y := by fun_prop
      exact ((ContinuousAt.comp (g := Real.log) (x := y)
        (Real.continuousAt_log (by linarith)) hf).neg).div_const π
    filter_upwards [hcont.eventually (hL x hxJ), Iio_mem_nhds hlt] with y' hy' hy'lt
    rw [leftEndHData_of_lt hy'lt, leftEndHData_of_lt hlt, hy']
  · set x := -Real.log (y - 1) / π with hx
    have hxJ : x ∉ JU := fun h => hyU ⟨x, h, one_add_exp_neg_log hgt⟩
    have hcont : ContinuousAt (fun y' : ℝ => -Real.log (y' - 1) / π) y := by
      have hf : ContinuousAt (fun y' : ℝ => y' - 1) y := by fun_prop
      exact ((ContinuousAt.comp (g := Real.log) (x := y)
        (Real.continuousAt_log (by linarith)) hf).neg).div_const π
    filter_upwards [hcont.eventually (hU x hxJ), Ioi_mem_nhds hgt] with y' hy' hy'lt
    rw [leftEndHData_of_gt hy'lt, leftEndHData_of_gt hgt, hy']

/-- Remark 4.1's left bound for the transported data (only the lower line lies left of `0`). -/
theorem leftEndHData_le_of_neg {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k) {y : ℝ} (hy : y < 0)
    (hyJ : y ∉ leftEndHJumps JL JU) : leftEndHData k bL bU y ≤ -sleLambda k + π * chiC k := by
  simp only [leftEndHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨-, hyL, -⟩ := hyJ
  have hy1 : y < 1 := by linarith
  rw [leftEndHData_of_lt hy1]
  have hx0 : -Real.log (1 - y) / π < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (Real.log_pos (by linarith))) Real.pi_pos
  exact hlowL _ hx0 fun h => hyL ⟨_, h, one_sub_exp_neg_log hy1⟩

/-- Remark 4.1's right bound for the transported data when every upper height is at least `Λ`. -/
theorem le_leftEndHData_of_pos {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hU : ∀ x : ℝ, x ∉ JU → sleLambda k ≤ bU x)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x) {y : ℝ} (hy : 0 < y)
    (hyJ : y ∉ leftEndHJumps JL JU) : sleLambda k - π * chiC k ≤ leftEndHData k bL bU y := by
  simp only [leftEndHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨hy1, hyL, hyU⟩ := hyJ
  rcases lt_or_gt_of_ne hy1 with hlt | hgt
  · rw [leftEndHData_of_lt hlt]
    have hx0 : 0 < -Real.log (1 - y) / π :=
      div_pos (neg_pos.2 (Real.log_neg (by linarith) (by linarith))) Real.pi_pos
    exact hlowR _ hx0 fun h => hyL ⟨_, h, one_sub_exp_neg_log hlt⟩
  · rw [leftEndHData_of_gt hgt]
    have := hU _ fun h => hyU ⟨_, h, one_add_exp_neg_log hgt⟩
    linarith

/-- `η` (lifetime `ζ`) is, in the chart `1 − e^{−πz}`, the flow line from `0` towards the **left** end `−∞` of
the strip field with lower data `bL` and upper data `bU`. The physical strip curve is `−log(1 − η)/π`. -/
def IsLeftEndFlowLine (k : ℝ) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ)
    (ζ : Ω → ℝ≥0∞) : Prop :=
  IsFlowLine k (leftEndHData k bL bU) (leftEndHJumps JL JU) 0 0 P h η ζ

/-- **Lemma 4.3, `a ≥ Λ`, boundary part; Aux. lemma 22, all upper heights `≥ Λ`, boundary part.** For the flow
line from `0` towards the left strip end, with lower data as in Remark 4.1 and every upper height at least `Λ`
(equality included): almost surely the lifetime is infinite and the flow line never hits the image `(1, ∞)` of
`∂_U𝒮` — indeed it never touches `∂ℍ` away from its seed. -/
theorem ae_notMem_upper_of_isLeftEndFlowLine (hk : 0 < k) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hbL : IsPiecewiseConstantBoundaryData bL JL) (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hU : ∀ x : ℝ, x ∉ JU → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsLeftEndFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' Ioi 1 ∧
      ∀ x : ℝ, x ≠ 0 → η ω t ≠ x := by
  filter_upwards [IsFlowLine.ae_trace_ne_real hk
    (isPiecewiseConstantBoundaryData_leftEndHData hbL hbU)
    (fun y hy hyJ => leftEndHData_le_of_neg hlowL hy hyJ)
    (fun y hy hyJ => le_leftEndHData_of_pos hU hlowR hy hyJ) hfl] with ω hω
  refine ⟨hω.1, fun t => ⟨?_, hω.2 t⟩⟩
  rintro ⟨y, hy, hyt⟩
  exact hω.2 t y (ne_of_gt (lt_trans zero_lt_one (mem_Ioi.1 hy))) hyt.symm

/-- **Lemma 4.3, `a ≥ Λ`; Aux. lemma 22, all upper heights `≥ Λ`** (from Aux. lemma 7). For the flow line from `0`
towards the left strip end, with lower data as in Remark 4.1 and every upper height at least `Λ`: almost surely
the lifetime is infinite, the flow line never hits `∂_U𝒮`, and it accumulates at `−∞` (in the chart,
`‖η(t)‖ → ∞`; in the strip, `Re(−log(1 − η(t))/π) → −∞`). -/
theorem lemma43_left_of_aux7 (h7 : Aux7Statement.{u} k) (hk : 0 < k) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU) (hU : ∀ x : ℝ, x ∉ JU → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsLeftEndFlowLine k bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' Ioi 1) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧
        Tendsto (fun t => (-Complex.log (1 - η ω t) / π).re) atTop atBot := by
  filter_upwards [ae_notMem_upper_of_isLeftEndFlowLine hk hbL hbU hU hlowL hlowR hfl,
    IsFlowLine.ae_tendsto_of_aux7 h7 hk (isPiecewiseConstantBoundaryData_leftEndHData hbL hbU)
      (fun y hy hyJ => leftEndHData_le_of_neg hlowL hy hyJ)
      (fun y hy hyJ => le_leftEndHData_of_pos hU hlowR hy hyJ) hfl] with ω h1 h2
  refine ⟨h1.1, fun t => (h1.2 t).1, h2.2.2, ?_⟩
  have hre : ∀ w : ℂ, (-Complex.log (1 - w) / π).re = -(Real.log ‖1 - w‖ / π) := fun w => by
    rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re, neg_div]
  simp only [hre]
  refine tendsto_neg_atTop_atBot.comp (Tendsto.atTop_div_const Real.pi_pos
    (Real.tendsto_log_atTop.comp ?_))
  refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-1) h2.2.2)
  have := norm_sub_norm_le (η ω t) 1
  rw [norm_one, norm_sub_rev] at this
  linarith

/-! ### The chart `(e^{πz} − 1)/(e^{πz} + q)` (target the upper point `z₀`, `q = e^{π Re z₀}`) -/

/-- The boundary data on `∂ℍ` of the image under `(e^{πz} − 1)/(e^{πz} + q)` of a strip field with lower data
`bL` and upper data `bU`: `bL(ψ⁻¹ y)` on `(−1/q, 1)`, `bU(Re ψ⁻¹ y) + πX` on `(−∞, −1/q)` (upper arc left of
`z₀`, `arg ψ′ = π`) and `bU(Re ψ⁻¹ y) − πX` on `(1, ∞)` (upper arc right of `z₀`, `arg ψ′ = −π`;
`stripQ_upper_left_height_le`, `stripQ_upper_right_height_ge`). Values at `−1/q` and `1` are irrelevant. -/
def stripQHData (k q : ℝ) (bL bU : ℝ → ℝ) (y : ℝ) : ℝ :=
  if -(1 / q) < y ∧ y < 1 then bL (Real.log ((1 + q * y) / (1 - y)) / π)
  else if y < -(1 / q) then bU (Real.log ((q * y + 1) / (y - 1)) / π) + π * chiC k
  else bU (Real.log ((q * y + 1) / (y - 1)) / π) - π * chiC k

/-- The jump candidates of `stripQHData`: the images `−1/q`, `1` of the strip ends and the images of the lower
and upper jump candidates. -/
def stripQHJumps (q : ℝ) (JL JU : Finset ℝ) : Finset ℝ :=
  insert (-(1 / q)) (insert 1
    (JL.image (fun x => (Real.exp (π * x) - 1) / (Real.exp (π * x) + q)) ∪
      JU.image (fun x => (Real.exp (π * x) + 1) / (Real.exp (π * x) - q))))

variable {q : ℝ}

/-- `−1/q < y ⟺ −1 < q y` for `q > 0`. -/
theorem neg_one_lt_mul_iff (hq : 0 < q) {y : ℝ} : -(1 / q) < y ↔ -1 < q * y := by
  have key : q * -(1 / q) = -1 := by field_simp
  constructor
  · intro h
    have := mul_lt_mul_of_pos_left h hq
    rwa [key] at this
  · intro h
    by_contra hy
    have := mul_le_mul_of_nonneg_left (not_lt.1 hy) hq.le
    rw [key] at this
    linarith

/-- `y < −1/q ⟺ q y < −1` for `q > 0`. -/
theorem lt_neg_one_div_iff (hq : 0 < q) {y : ℝ} : y < -(1 / q) ↔ q * y < -1 := by
  rw [← not_le, ← not_le, not_iff_not]
  constructor
  · intro h
    rcases h.lt_or_eq with h | h
    · exact ((neg_one_lt_mul_iff hq).1 h).le
    · rw [← h]; field_simp; rfl
  · intro h
    rcases h.lt_or_eq with h | h
    · exact ((neg_one_lt_mul_iff hq).2 h).le
    · have : y = -(1 / q) := by field_simp; linarith
      exact this.ge

theorem stripQHData_of_mem {bL bU : ℝ → ℝ} {y : ℝ} (h1 : -(1 / q) < y) (h2 : y < 1) :
    stripQHData k q bL bU y = bL (Real.log ((1 + q * y) / (1 - y)) / π) := by
  simp only [stripQHData, h1, h2, and_self, ↓reduceIte]

theorem stripQHData_of_lt {bL bU : ℝ → ℝ} {y : ℝ} (hy : y < -(1 / q)) :
    stripQHData k q bL bU y = bU (Real.log ((q * y + 1) / (y - 1)) / π) + π * chiC k := by
  have : ¬ (-(1 / q) < y ∧ y < 1) := fun h => absurd h.1 (not_lt.2 hy.le)
  simp only [stripQHData, this, hy, ↓reduceIte]

theorem stripQHData_of_gt (hq : 0 < q) {bL bU : ℝ → ℝ} {y : ℝ} (hy : 1 < y) :
    stripQHData k q bL bU y = bU (Real.log ((q * y + 1) / (y - 1)) / π) - π * chiC k := by
  have hq' : -(1 / q) < 0 := neg_neg_of_pos (one_div_pos.2 hq)
  have h1 : ¬ (-(1 / q) < y ∧ y < 1) := fun h => absurd h.2 (not_lt.2 hy.le)
  have h2 : ¬ (y < -(1 / q)) := not_lt.2 (by linarith)
  simp only [stripQHData, h1, h2, ↓reduceIte]

theorem stripQ_lower_inv (hq : 0 < q) {y : ℝ} (h1 : -(1 / q) < y) (h2 : y < 1) :
    (Real.exp (π * (Real.log ((1 + q * y) / (1 - y)) / π)) - 1) /
      (Real.exp (π * (Real.log ((1 + q * y) / (1 - y)) / π)) + q) = y := by
  have hqy : 0 < 1 + q * y := by linarith [(neg_one_lt_mul_iff hq).1 h1]
  have hd : 0 < 1 - y := by linarith
  rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log (div_pos hqy hd)]
  have hden : (1 + q * y) / (1 - y) + q ≠ 0 := by positivity
  rw [div_eq_iff hden]
  field_simp
  ring

theorem stripQ_upper_inv (hq : 0 < q) {y : ℝ} (hpos : 0 < (q * y + 1) / (y - 1)) (hy1 : y ≠ 1) :
    (Real.exp (π * (Real.log ((q * y + 1) / (y - 1)) / π)) + 1) /
      (Real.exp (π * (Real.log ((q * y + 1) / (y - 1)) / π)) - q) = y := by
  rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log hpos]
  have hd : y - 1 ≠ 0 := sub_ne_zero.2 hy1
  have hden : (q * y + 1) / (y - 1) - q ≠ 0 := by
    rw [div_sub' hd]
    refine div_ne_zero ?_ hd
    ring_nf
    linarith
  rw [div_eq_iff hden]
  field_simp
  ring

theorem neg_one_div_neg (hq : 0 < q) : -(1 / q) < 0 := neg_neg_of_pos (one_div_pos.2 hq)

theorem stripQ_upper_left_pos (hq : 0 < q) {y : ℝ} (hy : y < -(1 / q)) :
    0 < (q * y + 1) / (y - 1) :=
  div_pos_of_neg_of_neg (by linarith [(lt_neg_one_div_iff hq).1 hy])
    (by linarith [neg_one_div_neg hq])

theorem stripQ_upper_right_pos (hq : 0 < q) {y : ℝ} (hy : 1 < y) :
    0 < (q * y + 1) / (y - 1) :=
  div_pos (by nlinarith) (by linarith)

/-- Piecewise-constant strip data transport to piecewise-constant data on `∂ℍ`. -/
theorem isPiecewiseConstantBoundaryData_stripQHData (hq : 0 < q) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hL : IsPiecewiseConstantBoundaryData bL JL)
    (hU : IsPiecewiseConstantBoundaryData bU JU) :
    IsPiecewiseConstantBoundaryData (stripQHData k q bL bU) (stripQHJumps q JL JU) := by
  intro y hy
  simp only [stripQHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hy
  obtain ⟨hyq, hy1, hyL, hyU⟩ := hy
  have hcontU : ∀ y : ℝ, y ≠ 1 → 0 < (q * y + 1) / (y - 1) →
      ContinuousAt (fun y' : ℝ => Real.log ((q * y' + 1) / (y' - 1)) / π) y := fun y hy1 hpos => by
    have hf : ContinuousAt (fun y' : ℝ => (q * y' + 1) / (y' - 1)) y :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (sub_ne_zero.2 hy1)
    exact (ContinuousAt.comp (g := Real.log) (x := y) (Real.continuousAt_log hpos.ne') hf).div_const π
  rcases lt_or_gt_of_ne hyq with hlt | hgt
  · have hpos := stripQ_upper_left_pos hq hlt
    set x := Real.log ((q * y + 1) / (y - 1)) / π with hx
    have hxJ : x ∉ JU := fun h => hyU ⟨x, h, stripQ_upper_inv hq hpos hy1⟩
    filter_upwards [(hcontU y hy1 hpos).eventually (hU x hxJ), Iio_mem_nhds hlt] with y' hy' hy'lt
    rw [stripQHData_of_lt hy'lt, stripQHData_of_lt hlt, hy']
  · rcases lt_or_gt_of_ne hy1 with hlt1 | hgt1
    · have hqy : 0 < 1 + q * y := by linarith [(neg_one_lt_mul_iff hq).1 hgt]
      have hd : 0 < 1 - y := by linarith
      have hpos : 0 < (1 + q * y) / (1 - y) := div_pos hqy hd
      set x := Real.log ((1 + q * y) / (1 - y)) / π with hx
      have hxJ : x ∉ JL := fun h => hyL ⟨x, h, stripQ_lower_inv hq hgt hlt1⟩
      have hcont : ContinuousAt (fun y' : ℝ => Real.log ((1 + q * y') / (1 - y')) / π) y := by
        have hf : ContinuousAt (fun y' : ℝ => (1 + q * y') / (1 - y')) y :=
          ContinuousAt.div (by fun_prop) (by fun_prop) hd.ne'
        exact (ContinuousAt.comp (g := Real.log) (x := y) (Real.continuousAt_log hpos.ne')
          hf).div_const π
      filter_upwards [hcont.eventually (hL x hxJ), Ioo_mem_nhds hgt hlt1] with y' hy' hy'm
      rw [stripQHData_of_mem hy'm.1 hy'm.2, stripQHData_of_mem hgt hlt1, hy']
    · have hpos := stripQ_upper_right_pos hq hgt1
      set x := Real.log ((q * y + 1) / (y - 1)) / π with hx
      have hxJ : x ∉ JU := fun h => hyU ⟨x, h, stripQ_upper_inv hq hpos hy1⟩
      filter_upwards [(hcontU y hy1 hpos).eventually (hU x hxJ), Ioi_mem_nhds hgt1] with y' hy' hy'lt
      rw [stripQHData_of_gt hq hy'lt, stripQHData_of_gt hq hgt1, hy']

/-- Remark 4.1's left bound for the transported data when the upper heights left of `z₀` are at most `−Λ`. -/
theorem stripQHData_le_of_neg (hq : 0 < q) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hUle : ∀ x : ℝ, x ∉ JU → Real.exp (π * x) < q → bU x ≤ -sleLambda k)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k) {y : ℝ} (hy : y < 0)
    (hyJ : y ∉ stripQHJumps q JL JU) : stripQHData k q bL bU y ≤ -sleLambda k + π * chiC k := by
  simp only [stripQHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨hyq, hy1, hyL, hyU⟩ := hyJ
  rcases lt_or_gt_of_ne hyq with hlt | hgt
  · rw [stripQHData_of_lt hlt]
    have hpos := stripQ_upper_left_pos hq hlt
    have hy1' : y - 1 < 0 := by linarith
    have hexp : Real.exp (π * (Real.log ((q * y + 1) / (y - 1)) / π)) < q := by
      rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log hpos, div_lt_iff_of_neg hy1']
      linarith
    have := hUle _ (fun h => hyU ⟨_, h, stripQ_upper_inv hq hpos hy1⟩) hexp
    linarith
  · have hy1' : y < 1 := by linarith
    rw [stripQHData_of_mem hgt hy1']
    have hqy : 0 < 1 + q * y := by linarith [(neg_one_lt_mul_iff hq).1 hgt]
    have hd : 0 < 1 - y := by linarith
    have hlt1 : (1 + q * y) / (1 - y) < 1 := by
      rw [div_lt_one hd]
      linarith [mul_neg_of_pos_of_neg hq hy]
    have hx0 : Real.log ((1 + q * y) / (1 - y)) / π < 0 :=
      div_neg_of_neg_of_pos (Real.log_neg (div_pos hqy hd) hlt1) Real.pi_pos
    exact hlowL _ hx0 fun h => hyL ⟨_, h, stripQ_lower_inv hq hgt hy1'⟩

/-- Remark 4.1's right bound for the transported data when the upper heights right of `z₀` are at least `Λ`. -/
theorem le_stripQHData_of_pos (hq : 0 < q) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hUge : ∀ x : ℝ, x ∉ JU → q < Real.exp (π * x) → sleLambda k ≤ bU x)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x) {y : ℝ} (hy : 0 < y)
    (hyJ : y ∉ stripQHJumps q JL JU) : sleLambda k - π * chiC k ≤ stripQHData k q bL bU y := by
  simp only [stripQHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hyJ
  obtain ⟨-, hy1, hyL, hyU⟩ := hyJ
  have hgt : -(1 / q) < y := (neg_one_div_neg hq).trans hy
  rcases lt_or_gt_of_ne hy1 with hlt1 | hgt1
  · rw [stripQHData_of_mem hgt hlt1]
    have hd : 0 < 1 - y := by linarith
    have hlt : 1 < (1 + q * y) / (1 - y) := by
      rw [one_lt_div hd]
      linarith [mul_pos hq hy]
    have hx0 : 0 < Real.log ((1 + q * y) / (1 - y)) / π :=
      div_pos (Real.log_pos hlt) Real.pi_pos
    exact hlowR _ hx0 fun h => hyL ⟨_, h, stripQ_lower_inv hq hgt hlt1⟩
  · rw [stripQHData_of_gt hq hgt1]
    have hpos := stripQ_upper_right_pos hq hgt1
    have hexp : q < Real.exp (π * (Real.log ((q * y + 1) / (y - 1)) / π)) := by
      rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log hpos, lt_div_iff₀ (by linarith)]
      linarith
    have := hUge _ (fun h => hyU ⟨_, h, stripQ_upper_inv hq hpos hy1⟩) hexp
    linarith

/-- `η` (lifetime `ζ`) is, in the chart `(e^{πz} − 1)/(e^{πz} + e^{πx₀})`, the flow line from `0` towards the
upper boundary point `z₀ = x₀ + i` of the strip field with lower data `bL` and upper data `bU`. -/
def IsStripQFlowLine (k x₀ : ℝ) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ)
    (ζ : Ω → ℝ≥0∞) : Prop :=
  IsFlowLine k (stripQHData k (Real.exp (π * x₀)) bL bU) (stripQHJumps (Real.exp (π * x₀)) JL JU) 0 0
    P h η ζ

theorem exp_lt_exp_mul_pi_iff {x x₀ : ℝ} : Real.exp (π * x) < Real.exp (π * x₀) ↔ x < x₀ := by
  rw [Real.exp_lt_exp, mul_lt_mul_iff_right₀ Real.pi_pos]

/-- **Lemma 4.5, boundary part.** For the flow line from `0` towards `z₀ = x₀ + i`, with upper heights at most
`−Λ` left of `z₀` and at least `Λ` right of `z₀` and lower data as in Remark 4.1: almost surely the lifetime is
infinite and the flow line never hits the images `(−∞, −e^{−πx₀})` and `(1, ∞)` of the two open upper arcs —
indeed it never touches `∂ℍ` away from its seed. -/
theorem ae_notMem_upper_of_isStripQFlowLine (hk : 0 < k) {x₀ : ℝ} {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hUle : ∀ x : ℝ, x ∉ JU → x < x₀ → bU x ≤ -sleLambda k)
    (hUge : ∀ x : ℝ, x ∉ JU → x₀ < x → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripQFlowLine k x₀ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0,
      η ω t ∉ ((↑) : ℝ → ℂ) '' (Iio (-(1 / Real.exp (π * x₀))) ∪ Ioi 1) ∧
        ∀ x : ℝ, x ≠ 0 → η ω t ≠ x := by
  have hq : 0 < Real.exp (π * x₀) := Real.exp_pos _
  filter_upwards [IsFlowLine.ae_trace_ne_real hk
    (isPiecewiseConstantBoundaryData_stripQHData hq hbL hbU)
    (fun y hy hyJ => stripQHData_le_of_neg hq
      (fun x hx hlt => hUle x hx (exp_lt_exp_mul_pi_iff.1 hlt)) hlowL hy hyJ)
    (fun y hy hyJ => le_stripQHData_of_pos hq
      (fun x hx hlt => hUge x hx (exp_lt_exp_mul_pi_iff.1 hlt)) hlowR hy hyJ) hfl] with ω hω
  refine ⟨hω.1, fun t => ⟨?_, hω.2 t⟩⟩
  rintro ⟨y, hy, hyt⟩
  refine hω.2 t y ?_ hyt.symm
  rcases hy with hy | hy
  · exact ne_of_lt (lt_trans (mem_Iio.1 hy) (neg_one_div_neg hq))
  · exact ne_of_gt (lt_trans zero_lt_one (mem_Ioi.1 hy))

/-- **Lemma 4.5** (from Aux. lemma 7). For the flow line from `0` towards `z₀ = x₀ + i`, with upper heights at
most `−Λ` left of `z₀` and at least `Λ` right of `z₀` and lower data as in Remark 4.1: almost surely the lifetime
is infinite, the flow line never hits either open upper arc, and it tends to its target `z₀` (in the chart,
`‖η(t)‖ → ∞`). -/
theorem lemma45_of_aux7 (h7 : Aux7Statement.{u} k) (hk : 0 < k) {x₀ : ℝ} {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hUle : ∀ x : ℝ, x ∉ JU → x < x₀ → bU x ≤ -sleLambda k)
    (hUge : ∀ x : ℝ, x ∉ JU → x₀ < x → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripQFlowLine k x₀ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧
      (∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' (Iio (-(1 / Real.exp (π * x₀))) ∪ Ioi 1)) ∧
        Tendsto (fun t => ‖η ω t‖) atTop atTop := by
  have hq : 0 < Real.exp (π * x₀) := Real.exp_pos _
  filter_upwards [ae_notMem_upper_of_isStripQFlowLine hk hbL hbU hUle hUge hlowL hlowR hfl,
    IsFlowLine.ae_tendsto_of_aux7 h7 hk (isPiecewiseConstantBoundaryData_stripQHData hq hbL hbU)
      (fun y hy hyJ => stripQHData_le_of_neg hq
        (fun x hx hlt => hUle x hx (exp_lt_exp_mul_pi_iff.1 hlt)) hlowL hy hyJ)
      (fun y hy hyJ => le_stripQHData_of_pos hq
        (fun x hx hlt => hUge x hx (exp_lt_exp_mul_pi_iff.1 hlt)) hlowR hy hyJ) hfl] with ω h1 h2
  exact ⟨h1.1, fun t => (h1.2 t).1, h2.2.2⟩

/-! ### Lemma 4.5 in strip coordinates: the exit point `z₀` -/

/-- The inverse of the chart `(e^{πz} − 1)/(e^{πz} + q)`: `w ↦ log((1 + q w)/(1 − w))/π` (principal logarithm;
`(1 + q w)/(1 − w) ∈ ℍ` for `w ∈ ℍ`). -/
def stripQInv (q : ℝ) (w : ℂ) : ℂ := Complex.log ((1 + q * w) / (1 - w)) / π

/-- The Möbius part of `stripQInv` preserves the closed upper half-plane. -/
theorem im_stripQ_mobius_nonneg (hq : 0 < q) {w : ℂ} (hw : 0 ≤ w.im) :
    0 ≤ ((1 + q * w) / (1 - w)).im := by
  rw [Complex.div_im, ← sub_div]
  refine div_nonneg ?_ (Complex.normSq_nonneg _)
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.sub_im,
    Complex.sub_re, Complex.one_im, Complex.one_re, Complex.ofReal_im, Complex.ofReal_re, zero_mul,
    sub_zero, add_zero, zero_add, zero_sub]
  nlinarith [mul_nonneg hq.le hw]

/-- If `‖w‖ → ∞` in the closed upper half-plane, the strip point `stripQInv q w` tends to `z₀ = x₀ + i`
(`q = e^{πx₀}`). -/
theorem tendsto_stripQInv {x₀ : ℝ} {f : ℝ≥0 → ℂ} (hf : Tendsto (fun t => ‖f t‖) atTop atTop)
    (him : ∀ t, 0 ≤ (f t).im) :
    Tendsto (fun t => stripQInv (Real.exp (π * x₀)) (f t)) atTop (𝓝 ((x₀ : ℂ) + I)) := by
  set q := Real.exp (π * x₀) with hqdef
  have hq : 0 < q := Real.exp_pos _
  have hinv : Tendsto (fun t => (f t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.1 hf)
  have hcont : Tendsto (fun u : ℂ => (u + q) / (u - 1)) (𝓝 0) (𝓝 ((0 + q) / (0 - 1))) :=
    ((continuous_id.add continuous_const).continuousAt.div
      (continuous_id.sub continuous_const).continuousAt (by norm_num)).tendsto
  have hg : Tendsto (fun t => (1 + q * f t) / (1 - f t)) atTop (𝓝 (-(q : ℂ))) := by
    have h := hcont.comp hinv
    rw [zero_add, zero_sub, div_neg, div_one] at h
    refine h.congr' ?_
    filter_upwards [hf.eventually_gt_atTop 1] with t ht
    have h0 : f t ≠ 0 := fun h => by rw [h, norm_zero] at ht; linarith
    have h1 : f t ≠ 1 := fun h => by rw [h, norm_one] at ht; linarith
    have hd1 : (f t)⁻¹ - 1 ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => h1 (inv_eq_one.1 h)
    have hd2 : 1 - f t ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    simp only [Function.comp_apply]
    rw [div_eq_div_iff hd1 hd2]
    field_simp
  have hg' : Tendsto (fun t => (1 + q * f t) / (1 - f t)) atTop
      (𝓝[{z : ℂ | 0 ≤ z.im}] (-(q : ℂ))) :=
    tendsto_nhdsWithin_iff.2 ⟨hg, Filter.Eventually.of_forall fun t =>
      im_stripQ_mobius_nonneg hq (him t)⟩
  have hlog := Complex.continuousWithinAt_log_of_re_neg_of_im_zero (z := -(q : ℂ))
    (by simp [hq]) (by simp)
  have hlim := (hlog.tendsto.comp hg').div_const (π : ℂ)
  have hval : Complex.log (-(q : ℂ)) / π = (x₀ : ℂ) + I := by
    have hneg : -(q : ℂ) = ((-q : ℝ) : ℂ) := by push_cast; ring
    rw [hneg]
    apply Complex.ext
    · rw [Complex.div_ofReal_re, Complex.log_ofReal_re, Real.log_neg_eq_log, hqdef, Real.log_exp,
        mul_div_cancel_left₀ _ Real.pi_pos.ne']
      simp
    · rw [Complex.div_ofReal_im, Complex.log_im, Complex.arg_ofReal_of_neg (by linarith),
        div_self Real.pi_pos.ne']
      simp
  rw [hval] at hlim
  exact hlim

/-- **Lemma 4.5** (from Aux. lemma 7), in strip coordinates: for the flow line from `0` towards `z₀ = x₀ + i`,
with upper heights at most `−Λ` left of `z₀` and at least `Λ` right of `z₀` and lower data as in Remark 4.1,
almost surely the lifetime is infinite, the flow line never hits either open upper arc, and the strip curve
`stripQInv q ∘ η` exits the strip at `z₀`. -/
theorem lemma45_strip_of_aux7 (h7 : Aux7Statement.{u} k) (hk : 0 < k) {x₀ : ℝ} {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hUle : ∀ x : ℝ, x ∉ JU → x < x₀ → bU x ≤ -sleLambda k)
    (hUge : ∀ x : ℝ, x ∉ JU → x₀ < x → sleLambda k ≤ bU x)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda k - π * chiC k ≤ bL x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripQFlowLine k x₀ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧
      (∀ t : ℝ≥0, η ω t ∉ ((↑) : ℝ → ℂ) '' (Iio (-(1 / Real.exp (π * x₀))) ∪ Ioi 1)) ∧
        Tendsto (fun t => stripQInv (Real.exp (π * x₀)) (η ω t)) atTop (𝓝 ((x₀ : ℂ) + I)) := by
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := IsFlowLine.exists_evolution hfl
  filter_upwards [lemma45_of_aux7 h7 hk hbL hbU hUle hUge hlowL hlowR hfl, htr, hev.2.2.2.2]
    with ω h1 hω hp
  obtain ⟨hζ, havoid, hlim⟩ := h1
  rw [hζ] at hω hp
  have hW := continuous_toNNReal_of_isIntegratedSLEPath hp
  exact ⟨hζ, havoid, tendsto_stripQInv hlim
    (im_nonneg_of_isGeneratingTrace hW hp.1 hω)⟩

end Sec4

end InteractingSLE
