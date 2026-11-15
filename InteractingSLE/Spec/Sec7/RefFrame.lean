/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripMarks513K

/-!
# The Figure 5.1 frame of Aux. lemma 130 for the strip words of Lemma 7.25's reference

Packet PROVE-REFFRAME. Lemma 7.25's proof (p. 413) constructs ONE strip coupling, that of Aux. lemma 130 (p. 408):
"Choose the four original boundary heights so that every original-boundary cumulative force value is nonnegative for
every angle in `[−π/2, π/2]`. For example, it suffices to take `a, b ≥ λ + πχ/2`, `a', b' ≥ λ + 3πχ/2`." This file
fixes that choice and checks it:

* **`aux130Frame κ`**: the frame `x₀ = 0` (`z₀ = i`), `a = b = λ + πχ/2`, `a' = b' = λ + 3πχ/2`;
* **`isFig51Bounds_aux130Frame`**: it satisfies the standing bounds `IsFig51Bounds` of Proposition 5.1 / §5.2
  (`λ' = λ − πχ/2`, (4.2));
* **`Frame.word`**: the strip word (half-plane boundary data of the strip system) whose counterflow word is the
  Figure 5.1 counterflow word of a frame — the return data `returnData (cfOffset κ) (cfCoeff κ)` of
  `stripCounterflowData κ 0 e^{πx₀} (fig51Lower a b) (fig51Upper x₀ a' b')`; its four explicit levels
  (`Frame.word_of_lt_neg`, `…_of_mem_Ioo_neg`, `…_of_mem_Ioo_pos`, `…_of_one_lt`): `−a' + πχ`, `−a`, `b`, `b' − πχ`
  on `(−∞, −e^{−πx₀})`, `(−e^{−πx₀}, 0)`, `(0, 1)`, `(1, ∞)`; piecewise constant off `{−e^{−πx₀}, 0, 1}`;
* **`Frame.word_left`, `Frame.word_right`**: the source's "substitution in (5.4)–(5.5)": for Aux. lemma 130's heights
  the strip word satisfies the pocket word's non-hit height hypotheses (`hWordleft`, `hWordright` of
  `StripMarksTopK`) at every angle in `[−π/2, π/2]`;
* **`refWord_of_boundary_eq`**: the Figure 5.1 identity `hRefWord` of `StripMarksTopK` for a strip word chosen as
  `Frame.word` (`hword_of_eq_returnData`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped Real
open QuantumZipper (chiC)

namespace InteractingSLE.Sec7.StripMarks

open StripSysField Sec4 Sec5

/-! ### The frame -/

/-- **Aux. lemma 130's Figure 5.1 frame** for the flow parameter `κ` (p. 408): counterflow seed `z₀ = i` (`x₀ = 0`),
lower heights `a = b = λ + πχ/2`, upper heights `a' = b' = λ + 3πχ/2` (`λ = λ(κ)`, `χ = χ(κ)`). -/
def aux130Frame (κ : ℝ) : Frame where
  x₀ := 0
  a := sleLambda κ + π * chiC κ / 2
  b := sleLambda κ + π * chiC κ / 2
  a' := sleLambda κ + 3 * π * chiC κ / 2
  b' := sleLambda κ + 3 * π * chiC κ / 2

@[simp] theorem aux130Frame_x₀ (κ : ℝ) : (aux130Frame κ).x₀ = 0 := rfl

/-- **The standing Figure 5.1 bounds for Aux. lemma 130's heights**: `a, b ≥ λ'` and `a', b' ≥ λ' + πχ`, because
`λ' = λ − πχ/2` ((4.2)) and `χ > 0` for `0 < κ < 4`. -/
theorem isFig51Bounds_aux130Frame {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    IsFig51Bounds κ (aux130Frame κ).a (aux130Frame κ).b (aux130Frame κ).a' (aux130Frame κ).b' := by
  have hl := sleLambda_sixteen_div_eq_sub hκ
  have hχ : 0 < π * chiC κ := mul_pos Real.pi_pos (Sec4.chiC_pos hκ hκ4)
  simp only [IsFig51Bounds, aux130Frame]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### The strip word of a frame -/

/-- **The strip word of a Figure 5.1 frame**: the half-plane boundary data of the strip system whose counterflow word
(`counterflowData κ`) is the Figure 5.1 counterflow word `stripCounterflowData κ 0 e^{πx₀} (fig51Lower a b)
(fig51Upper x₀ a' b')`, i.e. its return data (`counterflowData_returnData`). -/
def Frame.word (κ : ℝ) (f : Frame) : ℝ → ℝ :=
  returnData (cfOffset κ) (cfCoeff κ)
    (stripCounterflowData κ 0 (Real.exp (π * f.x₀)) (fig51Lower f.a f.b) (fig51Upper f.x₀ f.a' f.b'))

/-- The three exceptional points `−e^{−πx₀}`, `0`, `1` of the strip word of a frame. -/
def Frame.wordJumps (f : Frame) : Finset ℝ := {-(Real.exp (π * f.x₀))⁻¹, 0, 1}

theorem aux130Frame_wordJumps (κ : ℝ) : (aux130Frame κ).wordJumps = {-1, 0, 1} := by
  simp only [Frame.wordJumps, aux130Frame_x₀, mul_zero, Real.exp_zero, inv_one]

variable {κ : ℝ} (f : Frame)

/-- `(0, 1)`: the strip word is the lower height `b` right of the flow seed. -/
theorem Frame.word_of_mem_Ioo_pos {x : ℝ} (hx : x ∈ Ioo 0 1) : f.word κ x = f.b := by
  have hq := Real.exp_pos (π * f.x₀)
  have hy : -x⁻¹ < -1 := by
    rw [neg_lt_neg_iff]
    exact one_lt_inv_iff₀.2 hx
  have hy1 : -x⁻¹ + 1 < 0 := by linarith
  have hr : 1 < (-x⁻¹ - Real.exp (π * f.x₀)) / (-x⁻¹ + 1) := (one_lt_div_of_neg hy1).2 (by linarith)
  have hpos : 0 < Real.log ((-x⁻¹ - Real.exp (π * f.x₀)) / (-x⁻¹ + 1)) / π :=
    div_pos (Real.log_pos hr) Real.pi_pos
  have hl : liftBoundary x = 0 := ite_eq_right (not_lt.2 hx.1.le)
  rw [Frame.word, returnData, stripCounterflowData_of_lt_neg_one hq hy, fig51Lower_of_pos hpos, hl, cfOffset]
  ring

/-- `(1, ∞)`: the strip word is `b' − πχ` (the upper height right of `z₀`, seen from the flow seed). -/
theorem Frame.word_of_one_lt {x : ℝ} (hx : 1 < x) : f.word κ x = f.b' - π * chiC κ := by
  have hq := Real.exp_pos (π * f.x₀)
  have hx0 : 0 < x := by linarith
  have hxi : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hxi0 : 0 < x⁻¹ := inv_pos.2 hx0
  have hy : -x⁻¹ ∈ Ioo (-1) 0 := ⟨by linarith, by linarith⟩
  have hy1 : 0 < -x⁻¹ + 1 := by linarith
  have hr : Real.exp (π * f.x₀) < (Real.exp (π * f.x₀) - -x⁻¹) / (-x⁻¹ + 1) := by
    rw [lt_div_iff₀ hy1]
    nlinarith
  have hr0 : 0 < (Real.exp (π * f.x₀) - -x⁻¹) / (-x⁻¹ + 1) := lt_trans hq hr
  have hgt : f.x₀ < Real.log ((Real.exp (π * f.x₀) - -x⁻¹) / (-x⁻¹ + 1)) / π := by
    rw [lt_div_iff₀ Real.pi_pos, mul_comm, Real.lt_log_iff_exp_lt hr0]
    exact hr
  have hl : liftBoundary x = 0 := ite_eq_right (not_lt.2 hx0.le)
  rw [Frame.word, returnData, stripCounterflowData_of_mem_Ioo_neg_one_zero hq hy, fig51Upper_of_gt hgt, hl,
    cfOffset]
  ring

/-- `(−∞, −e^{−πx₀})`: the strip word is `−a' + πχ` (the upper height left of `z₀`, seen from the flow seed). -/
theorem Frame.word_of_lt_neg (hκ : 0 < κ) {x : ℝ} (hx : x < -(Real.exp (π * f.x₀))⁻¹) :
    f.word κ x = -f.a' + π * chiC κ := by
  have hq := Real.exp_pos (π * f.x₀)
  have hqi : 0 < (Real.exp (π * f.x₀))⁻¹ := inv_pos.2 hq
  have hx0 : x < 0 := by linarith
  have hy0 : 0 < -x⁻¹ := neg_pos.2 (inv_lt_zero'.2 hx0)
  have hyq : -x⁻¹ < Real.exp (π * f.x₀) := by
    rw [← inv_neg]
    calc (-x)⁻¹ < ((Real.exp (π * f.x₀))⁻¹)⁻¹ := inv_strictAnti₀ hqi (by linarith)
      _ = Real.exp (π * f.x₀) := inv_inv _
  have hy : -x⁻¹ ∈ Ioo 0 (Real.exp (π * f.x₀)) := ⟨hy0, hyq⟩
  have hy1 : 0 < -x⁻¹ + 1 := by linarith
  have hr0 : 0 < (Real.exp (π * f.x₀) - -x⁻¹) / (-x⁻¹ + 1) := div_pos (by linarith) hy1
  have hr : (Real.exp (π * f.x₀) - -x⁻¹) / (-x⁻¹ + 1) < Real.exp (π * f.x₀) := by
    rw [div_lt_iff₀ hy1]
    nlinarith
  have hlt : Real.log ((Real.exp (π * f.x₀) - -x⁻¹) / (-x⁻¹ + 1)) / π < f.x₀ := by
    rw [div_lt_iff₀ Real.pi_pos, mul_comm f.x₀, Real.log_lt_iff_lt_exp hr0]
    exact hr
  have hl : liftBoundary x = -(2 * π) := ite_eq_left hx0
  rw [Frame.word, returnData, stripCounterflowData_of_mem_Ioo_zero hy, fig51Upper_of_lt hlt, hl, cfOffset, cfCoeff,
    Sec4.chiC_sixteen_div hκ]
  ring

/-- `(−e^{−πx₀}, 0)`: the strip word is the lower height `−a` left of the flow seed. -/
theorem Frame.word_of_mem_Ioo_neg (hκ : 0 < κ) {x : ℝ} (hx : x ∈ Ioo (-(Real.exp (π * f.x₀))⁻¹) 0) :
    f.word κ x = -f.a := by
  have hq := Real.exp_pos (π * f.x₀)
  have hy0 : 0 < -x := by linarith [hx.2]
  have hqy : Real.exp (π * f.x₀) < -x⁻¹ := by
    rw [← inv_neg]
    calc Real.exp (π * f.x₀) = ((Real.exp (π * f.x₀))⁻¹)⁻¹ := (inv_inv _).symm
      _ < (-x)⁻¹ := inv_strictAnti₀ hy0 (by linarith [hx.1])
  have hy1 : 0 < -x⁻¹ + 1 := by linarith
  have hr0 : 0 < (-x⁻¹ - Real.exp (π * f.x₀)) / (-x⁻¹ + 1) := div_pos (by linarith) hy1
  have hr : (-x⁻¹ - Real.exp (π * f.x₀)) / (-x⁻¹ + 1) < 1 := (div_lt_one hy1).2 (by linarith)
  have hneg : Real.log ((-x⁻¹ - Real.exp (π * f.x₀)) / (-x⁻¹ + 1)) / π < 0 :=
    div_neg_of_neg_of_pos (Real.log_neg hr0 hr) Real.pi_pos
  have hl : liftBoundary x = -(2 * π) := ite_eq_left hx.2
  rw [Frame.word, returnData, stripCounterflowData_of_lt hq hqy, fig51Lower_of_neg hneg, hl, cfOffset, cfCoeff,
    Sec4.chiC_sixteen_div hκ]
  ring

/-- **The strip word of a frame is piecewise constant off `{−e^{−πx₀}, 0, 1}`** (its four explicit levels). -/
theorem Frame.isPiecewiseConstantBoundaryData_word (hκ : 0 < κ) :
    IsPiecewiseConstantBoundaryData (f.word κ) f.wordJumps := by
  intro y hy
  have hq := Real.exp_pos (π * f.x₀)
  have hqi : 0 < (Real.exp (π * f.x₀))⁻¹ := inv_pos.2 hq
  simp only [Frame.wordJumps, Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨hyc, hy0, hy1⟩ := hy
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · rcases lt_or_gt_of_ne hyc with hlt | hgt
    · filter_upwards [Iio_mem_nhds hlt] with z hz
      rw [f.word_of_lt_neg hκ hz, f.word_of_lt_neg hκ hlt]
    · filter_upwards [Ioo_mem_nhds hgt hneg] with z hz
      rw [f.word_of_mem_Ioo_neg hκ hz, f.word_of_mem_Ioo_neg hκ ⟨hgt, hneg⟩]
  · rcases lt_or_gt_of_ne hy1 with hlt | hgt
    · filter_upwards [Ioo_mem_nhds hpos hlt] with z hz
      rw [f.word_of_mem_Ioo_pos hz, f.word_of_mem_Ioo_pos ⟨hpos, hlt⟩]
    · filter_upwards [Ioi_mem_nhds hgt] with z hz
      rw [f.word_of_one_lt hz, f.word_of_one_lt hgt]

/-- **The Figure 5.1 identity of a strip word chosen as the frame's word** (`hRefWord` of `StripMarksTopK`): its
counterflow word is the Figure 5.1 counterflow word off `counterflowJumps J ∪ T`, for every `J` and `T`
(`hword_of_eq_returnData`). -/
theorem Frame.refWord_of_boundary_eq {b : ℝ → ℝ} (J T : Finset ℝ) (hb : b = f.word κ) :
    ∀ y ∉ counterflowJumps J ∪ T, counterflowData κ b y = stripCounterflowData κ 0 (Real.exp (π * f.x₀))
      (fig51Lower f.a f.b) (fig51Upper f.x₀ f.a' f.b') y :=
  hword_of_eq_returnData J T hb

/-! ### Aux. lemma 130's heights: the substitution in (5.4)–(5.5) -/

/-- **Aux. lemma 130's strip word on the negative half-line** is `−λ − πχ/2` off `−1` (both the lower height `−a`
and the transported upper height `−a' + πχ`). -/
theorem aux130Frame_word_of_neg (hκ : 0 < κ) {y : ℝ} (hy : y < 0) (hy1 : y ≠ -1) :
    (aux130Frame κ).word κ y = -sleLambda κ - π * chiC κ / 2 := by
  have e : (Real.exp (π * (aux130Frame κ).x₀))⁻¹ = 1 := by
    simp only [aux130Frame_x₀, mul_zero, Real.exp_zero, inv_one]
  rcases lt_or_gt_of_ne hy1 with hlt | hgt
  · rw [(aux130Frame κ).word_of_lt_neg hκ (by rw [e]; exact hlt)]
    simp only [aux130Frame]
    ring
  · rw [(aux130Frame κ).word_of_mem_Ioo_neg hκ ⟨by rw [e]; exact hgt, hy⟩]
    simp only [aux130Frame]
    ring

/-- **Aux. lemma 130's strip word on the positive half-line** is `λ + πχ/2` off `1` (both the lower height `b` and
the transported upper height `b' − πχ`). -/
theorem aux130Frame_word_of_pos {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) :
    (aux130Frame κ).word κ y = sleLambda κ + π * chiC κ / 2 := by
  rcases lt_or_gt_of_ne hy1 with hlt | hgt
  · rw [(aux130Frame κ).word_of_mem_Ioo_pos ⟨hy, hlt⟩]
    rfl
  · rw [(aux130Frame κ).word_of_one_lt hgt]
    simp only [aux130Frame]
    ring

/-- **Aux. lemma 130's non-hit check, left side** (`hWordleft` of `StripMarksTopK`): for every angle `a ∈ [−π/2, π/2]`
and `y < 0` off the jumps (which contain `−1`), `word(y) + aχ ≤ −λ`. -/
theorem aux130Frame_word_left (hκ : 0 < κ) (hκ4 : κ < 4) {J : Finset ℝ} (hJ : (-1 : ℝ) ∈ J) :
    ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      (aux130Frame κ).word κ y + a * chiC κ ≤ -sleLambda κ := by
  intro a ha y hy hyJ
  have hχ := Sec4.chiC_pos hκ hκ4
  have h1 : a * chiC κ ≤ π / 2 * chiC κ := mul_le_mul_of_nonneg_right ha.2 hχ.le
  rw [aux130Frame_word_of_neg hκ hy (fun h => hyJ (h ▸ hJ))]
  linarith

/-- **Aux. lemma 130's non-hit check, right side** (`hWordright` of `StripMarksTopK`): for every angle
`a ∈ [−π/2, π/2]` and `y > 0` off the jumps (which contain `1`), `λ ≤ word(y) + aχ`. -/
theorem aux130Frame_word_right (hκ : 0 < κ) (hκ4 : κ < 4) {J : Finset ℝ} (hJ : (1 : ℝ) ∈ J) :
    ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ (aux130Frame κ).word κ y + a * chiC κ := by
  intro a ha y hy hyJ
  have hχ := Sec4.chiC_pos hκ hκ4
  have h1 : -(π / 2) * chiC κ ≤ a * chiC κ := mul_le_mul_of_nonneg_right ha.1 hχ.le
  rw [aux130Frame_word_of_pos hy (fun h => hyJ (h ▸ hJ))]
  linarith

theorem aux130Frame_isPiecewiseConstantBoundaryData (hκ : 0 < κ) :
    IsPiecewiseConstantBoundaryData ((aux130Frame κ).word κ) {-1, 0, 1} := by
  rw [← aux130Frame_wordJumps κ]
  exact (aux130Frame κ).isPiecewiseConstantBoundaryData_word hκ

end InteractingSLE.Sec7.StripMarks
