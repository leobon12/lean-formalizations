/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Counterflow
import InteractingSLE.Spec.Sec5.Heights
import InteractingSLE.Frozen.Spec.rightSideOf
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import Mathlib.Analysis.Complex.Convex

/-!
# §5 carriers: the strip field, its counterflow line and flow lines, and the sides of a strip curve

Packet PROVE-SEC5-C (specification §5, `source/spec/p097-144.md` L692–L1004 and `p145-192.md` L1–L157,
pp. 127–152). The objects of §5 live on the strip `𝒮 = ℝ × (0, 1)`. Following ruling R36 (strip coordinates only
through the half-plane) and the strip carriers of PROVE-SEC4-B2 (`Sec4/Strip.lean`, `Sec4/Counterflow.lean`), every
object is read in the exponential chart `E(z) = e^{πz} − 1` (`Sec4.expChart`), which maps `𝒮` onto `ℍ`, the lower
line `∂_L𝒮` onto `(−1, ∞)` (the seed `0` to `0`), the upper line `∂_U𝒮` onto `(−∞, −1)` (order reversed;
`z₀ = x₀ + i ↦ −1 − e^{πx₀}`), the strip end `−∞` to `−1` and the end `+∞` to `∞`.

* **Data of Figures 5.1, 5.3, 5.5.** `fig51Lower a b` (`−a` left of `0`, `b` right) and `fig51Upper x₀ a' b'`
  (`−a'` left of `z₀`, `b'` right); their `E`-transport `stripHData κ …` takes the four values `−a`, `b`, `−a' + πχ`,
  `b' + πχ` on `(−1, 0)`, `(0, ∞)`, `(−1 − q, −1)`, `(−∞, −1 − q)` (`q = e^{πx₀}`; `stripHData_fig51_*`).
* **Frames.** §5 applies its statements to the fields `h + αχ` (Proposition 5.5 uses `α = θ₁ − π/2`). The frozen
  carriers never form `h + αχ`: the flow line of `h + αχ` with angle `θ` is the frozen `IsFlowLine` of `h` with angle
  `α + θ` (Specification p. 2, "a flow line of `h` with real angle `θ` means the flow line coupled to `h + θχ`"), and
  the counterflow `CF_d(h + αχ)` is `Sec4.IsStripCounterflowDriver κ α q` of `h`. The field `h + αχ` has the data of
  Figure 5.1 exactly when `h` has the data `fig51Lower a b − αχ`, `fig51Upper x₀ a' b' − αχ` (`IsFig51Field`).
* **Ranges.** `pathRange η ζ = η([0, ζ))` (the points of an available trace before its lifetime);
  `stripCounterflowRange q γ` the physical points `M_q⁻¹(γ(t))` of the counterflow from `z₀` whose trace in the
  chart `M_q` is `γ`.
* **Sides of a strip curve** (`stripLeftSide`, `stripRightSide`): the points of `ℍ \ A` whose complementary
  component reaches the lower boundary left of the seed, `E(∂_L𝒮 ∩ {x < 0}) = (−1, 0)`, resp. right of it,
  `E(∂_L𝒮 ∩ {x > 0}) = (0, ∞)` (the frozen `rightSideOf`). For a curve from `0` that separates the strip (it reaches
  `∂_U𝒮`, or a strip end) these are its two complementary sides; the frozen `leftSideOf` (`x < 0`) is not the left
  side in the strip chart, because `(−∞, −1)` is the image of the upper line.
* **"Passes to the left/right of"** (Proposition 5.1; Figure 5.1): `LiesRightOf K A` (no point of `K` is strictly on
  the left of `A`) and `LiesLeftOf K A`. Proposition 5.1's conclusion "`η_θ` passes to the left of `η'`" is
  `LiesRightOf (range η') (range η_θ)`; its proof shows exactly this ("`η'(τ')` almost surely lies to the right of
  `η_θ`" for every `η'`-stopping time `τ'`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

namespace InteractingSLE

namespace Sec5

open Sec4 (stripHData stripHJumps IsStripGFF stripCounterflowChart IsStripCounterflowDriver)

/-! ### The boundary data of Figures 5.1, 5.3 and 5.5 -/

/-- Lower data of Figures 5.1, 5.3, 5.5 (the lower boundary `∂_L𝒮`): `−a` left of the seed `0`, `b` right of it. -/
def fig51Lower (a b : ℝ) (x : ℝ) : ℝ := if x < 0 then -a else b

/-- Upper data of Figures 5.1, 5.3, 5.5 (the upper boundary `∂_U𝒮`, `z₀ = x₀ + i`): `−a'` left of `z₀`, `b'` right
of it. -/
def fig51Upper (x₀ a' b' : ℝ) (x : ℝ) : ℝ := if x < x₀ then -a' else b'

theorem fig51Lower_of_neg {a b x : ℝ} (hx : x < 0) : fig51Lower a b x = -a := ite_eq_left hx

theorem fig51Lower_of_pos {a b x : ℝ} (hx : 0 < x) : fig51Lower a b x = b :=
  ite_eq_right (not_lt.2 hx.le)

theorem fig51Upper_of_lt {x₀ a' b' x : ℝ} (hx : x < x₀) : fig51Upper x₀ a' b' x = -a' := ite_eq_left hx

theorem fig51Upper_of_gt {x₀ a' b' x : ℝ} (hx : x₀ < x) : fig51Upper x₀ a' b' x = b' :=
  ite_eq_right (not_lt.2 hx.le)

theorem isPiecewiseConstantBoundaryData_fig51Lower (a b : ℝ) :
    IsPiecewiseConstantBoundaryData (fig51Lower a b) {0} :=
  Sec4.isPiecewiseConstantBoundaryData_ite_lt 0 _ _

theorem isPiecewiseConstantBoundaryData_fig51Upper (x₀ a' b' : ℝ) :
    IsPiecewiseConstantBoundaryData (fig51Upper x₀ a' b') {x₀} :=
  Sec4.isPiecewiseConstantBoundaryData_ite_lt x₀ _ _

/-- Shifting data by a constant keeps it piecewise constant off the same jump set. -/
theorem isPiecewiseConstantBoundaryData_sub_const {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (c : ℝ) :
    IsPiecewiseConstantBoundaryData (fun x => b x - c) J := by
  intro y hy
  filter_upwards [hb y hy] with z hz
  rw [hz]

/-- The lower data of Figure 5.1 for the field `h + αχ`, read as data of `h`: `fig51Lower a b − αχ`. -/
def fig51LowerFrame (κ α a b : ℝ) (x : ℝ) : ℝ := fig51Lower a b x - α * chiC κ

/-- The upper data of Figure 5.1 for the field `h + αχ`, read as data of `h`: `fig51Upper x₀ a' b' − αχ`. -/
def fig51UpperFrame (κ α x₀ a' b' : ℝ) (x : ℝ) : ℝ := fig51Upper x₀ a' b' x - α * chiC κ

theorem isPiecewiseConstantBoundaryData_fig51LowerFrame (κ α a b : ℝ) :
    IsPiecewiseConstantBoundaryData (fig51LowerFrame κ α a b) {0} :=
  isPiecewiseConstantBoundaryData_sub_const (isPiecewiseConstantBoundaryData_fig51Lower a b) _

theorem isPiecewiseConstantBoundaryData_fig51UpperFrame (κ α x₀ a' b' : ℝ) :
    IsPiecewiseConstantBoundaryData (fig51UpperFrame κ α x₀ a' b') {x₀} :=
  isPiecewiseConstantBoundaryData_sub_const (isPiecewiseConstantBoundaryData_fig51Upper x₀ a' b') _

@[simp] theorem fig51LowerFrame_zero (κ a b : ℝ) : fig51LowerFrame κ 0 a b = fig51Lower a b := by
  funext x; simp [fig51LowerFrame]

@[simp] theorem fig51UpperFrame_zero (κ x₀ a' b' : ℝ) :
    fig51UpperFrame κ 0 x₀ a' b' = fig51Upper x₀ a' b' := by
  funext x; simp [fig51UpperFrame]

/-- The data of `h` in the frame `α` are the data `(a + αχ, b − αχ, a' + αχ, b' − αχ)` of Figure 5.1 in the frame
`0`: the field `h` itself has Figure 5.1 data with these parameters. -/
theorem fig51LowerFrame_eq (κ α a b : ℝ) :
    fig51LowerFrame κ α a b = fig51Lower (a + α * chiC κ) (b - α * chiC κ) := by
  funext x; unfold fig51LowerFrame fig51Lower; split_ifs <;> ring

theorem fig51UpperFrame_eq (κ α x₀ a' b' : ℝ) :
    fig51UpperFrame κ α x₀ a' b' = fig51Upper x₀ (a' + α * chiC κ) (b' - α * chiC κ) := by
  funext x; unfold fig51UpperFrame fig51Upper; split_ifs <;> ring

/-! ### The four transported heights -/

/-- The image `E(z₀) = −1 − q` of the upper marked point `z₀ = x₀ + i`, `q = e^{πx₀}` (`Sec4.expChart_upper`). -/
theorem expChart_upper_marked (x₀ : ℝ) :
    Sec4.expChart (x₀ + I) = ((-1 - Real.exp (π * x₀) : ℝ) : ℂ) := by
  rw [Sec4.expChart_upper]; congr 1; ring

/-- On `(0, ∞)` (the lower boundary right of the seed) the transported data is `b`. -/
theorem stripHData_fig51_of_pos (κ x₀ a b a' b' : ℝ) {y : ℝ} (hy : 0 < y) :
    stripHData κ (fig51Lower a b) (fig51Upper x₀ a' b') y = b := by
  rw [Sec4.stripHData_of_lt (by linarith)]
  apply fig51Lower_of_pos
  exact div_pos (Real.log_pos (by linarith)) Real.pi_pos

/-- On `(−1, 0)` (the lower boundary left of the seed) the transported data is `−a`. -/
theorem stripHData_fig51_of_mem_Ioo (κ x₀ a b a' b' : ℝ) {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 0) :
    stripHData κ (fig51Lower a b) (fig51Upper x₀ a' b') y = -a := by
  rw [Sec4.stripHData_of_lt hy.1]
  apply fig51Lower_of_neg
  exact div_neg_of_neg_of_pos (Real.log_neg (by linarith [hy.1]) (by linarith [hy.2])) Real.pi_pos

/-- On `(−1 − q, −1)` (the image of the upper boundary left of `z₀`) the transported data is `−a' + πχ`. -/
theorem stripHData_fig51_of_upper_left (κ x₀ a b a' b' : ℝ) {y : ℝ}
    (hy : y ∈ Ioo (-1 - Real.exp (π * x₀)) (-1)) :
    stripHData κ (fig51Lower a b) (fig51Upper x₀ a' b') y = -a' + π * chiC κ := by
  rw [Sec4.stripHData_of_lt_neg_one hy.2]
  congr 1
  apply fig51Upper_of_lt
  rw [div_lt_iff₀ Real.pi_pos, mul_comm, ← Real.exp_lt_exp, Real.exp_log (by linarith [hy.2])]
  linarith [hy.1]

/-- On `(−∞, −1 − q)` (the image of the upper boundary right of `z₀`) the transported data is `b' + πχ`. -/
theorem stripHData_fig51_of_upper_right (κ x₀ a b a' b' : ℝ) {y : ℝ}
    (hy : y < -1 - Real.exp (π * x₀)) :
    stripHData κ (fig51Lower a b) (fig51Upper x₀ a' b') y = b' + π * chiC κ := by
  have hpos : 0 < Real.exp (π * x₀) := Real.exp_pos _
  rw [Sec4.stripHData_of_lt_neg_one (by linarith)]
  congr 1
  apply fig51Upper_of_gt
  rw [lt_div_iff₀ Real.pi_pos, mul_comm, ← Real.exp_lt_exp, Real.exp_log (by linarith)]
  linarith

/-! ### The field of §5 -/

/-- `h` is the `E`-image (rule (1.4)) of a GFF on `𝒮` such that `h + αχ` has the boundary data of Figure 5.1:
`−a`, `b` on `∂_L𝒮` left and right of the seed `0`, and `−a'`, `b'` on `∂_U𝒮` left and right of `z₀ = x₀ + i`
(Proposition 5.1: "`h` is a GFF on `𝒮` with boundary data as described in Figure 5.1"; at `α = 0` this is literally
that hypothesis; Proposition 5.5 applies it to `h + (θ₁ − π/2)χ`). -/
def IsFig51Field (κ α x₀ a b a' b' : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  IsStripGFF κ P h (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀}

/-- The standing bounds of Proposition 5.1 and §5.2: `a, b ≥ λ'` (the counterflow meets `∂_L𝒮` only when it
terminates at `0`) and `a', b' ≥ λ' + πχ` (it meets `∂_U𝒮` only at `z₀`), `λ' = λ(16/κ)`. -/
def IsFig51Bounds (κ a b a' b' : ℝ) : Prop :=
  sleLambda (16 / κ) ≤ a ∧ sleLambda (16 / κ) ≤ b ∧ sleLambda (16 / κ) + π * chiC κ ≤ a' ∧
    sleLambda (16 / κ) + π * chiC κ ≤ b'

/-- Condition (5.1) on the angle `θ`: `(λ − πχ − b)/χ ≤ θ ≤ (a + πχ − λ)/χ`, written without division (`χ > 0` for
`0 < κ < 4`; `eq51_iff` translates it to cumulative weights). -/
def Eq51 (κ a b θ : ℝ) : Prop :=
  sleLambda κ - π * chiC κ - b ≤ θ * chiC κ ∧ θ * chiC κ ≤ a + π * chiC κ - sleLambda κ

/-- The angle-`θ` flow line from the seed `0` of the field `h + αχ` (its own lifetime `ζ`, its trace `η` in the
chart `E`), when `h` is the `E`-image of a strip field with lower data `bL` and upper data `bU`: the frozen
`IsFlowLine` of `h` at angle `α + θ` with the transported data (the flow line of `h + αχ` with angle `θ` is the flow
line coupled to `h + (α + θ)χ`). At `α = θ = 0` this is `Sec4.IsStripFlowLine`. -/
def IsStripFlowLineAt (κ α θ : ℝ) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ)
    (ζ : Ω → ℝ≥0∞) : Prop :=
  IsFlowLine κ (stripHData κ bL bU) (stripHJumps JL JU) 0 (α + θ) P h η ζ

theorem isStripFlowLineAt_zero_zero_iff {κ : ℝ} {bL bU : ℝ → ℝ} {JL JU : Finset ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} :
    IsStripFlowLineAt κ 0 0 bL bU JL JU P h η ζ ↔ Sec4.IsStripFlowLine κ bL bU JL JU P h η ζ := by
  rw [IsStripFlowLineAt, zero_add]; rfl

/-- The flow line of `h + αχ` with angle `θ` is the flow line of `h + α'χ` with angle `θ + α − α'` (the same
frozen object). -/
theorem isStripFlowLineAt_frame_iff {κ α α' θ : ℝ} {bL bU : ℝ → ℝ} {JL JU : Finset ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} :
    IsStripFlowLineAt κ α θ bL bU JL JU P h η ζ ↔
      IsStripFlowLineAt κ α' (θ + α - α') bL bU JL JU P h η ζ := by
  unfold IsStripFlowLineAt
  rw [show α' + (θ + α - α') = α + θ by ring]


/-! ### Ranges -/

/-- The points `η([0, ζ))` of an available trace `η` before its lifetime `ζ`. -/
def pathRange (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) : Set ℂ := η '' {t | (t : ℝ≥0∞) < ζ}

theorem pathRange_mono {η : ℝ≥0 → ℂ} {ζ ζ' : ℝ≥0∞} (h : ζ ≤ ζ') : pathRange η ζ ⊆ pathRange η ζ' :=
  image_mono fun _ ht => lt_of_lt_of_le ht h

/-- The physical points, in the chart `E`, of the counterflow from `z₀ = (log q)/π + i` whose trace in the chart
`M_q` is `γ` with lifetime `ζ'` (`Sec4.IsStripCounterflowDriver`; "the physical counterflow is `M_q⁻¹(γ)`"):
`M_q⁻¹(γ([0, ζ')))`. -/
def stripCounterflowRange (q : ℝ) (γ : ℝ≥0 → ℂ) (ζ' : ℝ≥0∞) : Set ℂ :=
  (stripCounterflowChart q).2.1 '' pathRange γ ζ'

/-! ### Sides of a strip curve and "passes to the left/right of" -/

/-- The points of `ℍ \ A` strictly on the left of `A` in the strip, read in the chart `E`: those whose complementary
component has in its closure a point of `E(∂_L𝒮 ∩ {x < 0}) = (−1, 0)` (the lower boundary left of the seed) not in
`A`. -/
def stripLeftSide (A : Set ℂ) : Set ℂ :=
  {z | z ∈ H \ A ∧ ∃ x : ℝ, x ∈ Ioo (-1 : ℝ) 0 ∧ (x : ℂ) ∉ A ∧
    (x : ℂ) ∈ closure (connectedComponentIn (H \ A) z)}

/-- The points of `ℍ \ A` strictly on the right of `A` in the strip, read in the chart `E`: those whose
complementary component has in its closure a point of `E(∂_L𝒮 ∩ {x > 0}) = (0, ∞)` not in `A` (the frozen
`rightSideOf`). -/
def stripRightSide (A : Set ℂ) : Set ℂ := rightSideOf A

/-- `K` lies (weakly) to the right of `A`: no point of `K` is strictly on the left of `A`. Proposition 5.1: "`η_θ`
passes to the left of `η'`" is `LiesRightOf (range η') (range η_θ)` (its proof: "`η'(τ')` lies to the right of
`η_θ`" for every `η'`-stopping time `τ'`). -/
def LiesRightOf (K A : Set ℂ) : Prop := Disjoint K (stripLeftSide A)

/-- `K` lies (weakly) to the left of `A`: no point of `K` is strictly on the right of `A`. -/
def LiesLeftOf (K A : Set ℂ) : Prop := Disjoint K (stripRightSide A)

theorem stripLeftSide_subset (A : Set ℂ) : stripLeftSide A ⊆ H \ A := fun _ hz => hz.1

theorem stripRightSide_subset (A : Set ℂ) : stripRightSide A ⊆ H \ A := fun _ hz => hz.1

theorem connectedComponentIn_subset_stripLeftSide {A : Set ℂ} {z : ℂ} (hz : z ∈ stripLeftSide A) :
    connectedComponentIn (H \ A) z ⊆ stripLeftSide A := by
  intro w hw
  refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
  rw [← connectedComponentIn_eq hw]
  exact hz.2

theorem connectedComponentIn_subset_stripRightSide {A : Set ℂ} {z : ℂ} (hz : z ∈ stripRightSide A) :
    connectedComponentIn (H \ A) z ⊆ stripRightSide A := by
  intro w hw
  refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
  rw [← connectedComponentIn_eq hw]
  exact hz.2

theorem isOpen_stripLeftSide {A : Set ℂ} (hA : IsClosed A) : IsOpen (stripLeftSide A) := by
  have hU : IsOpen (H \ A) := (isOpen_lt continuous_const Complex.continuous_im).sdiff hA
  exact isOpen_iff_forall_mem_open.2 fun z hz => ⟨_, connectedComponentIn_subset_stripLeftSide hz,
    hU.connectedComponentIn, mem_connectedComponentIn hz.1⟩

theorem isOpen_stripRightSide {A : Set ℂ} (hA : IsClosed A) : IsOpen (stripRightSide A) := by
  have hU : IsOpen (H \ A) := (isOpen_lt continuous_const Complex.continuous_im).sdiff hA
  exact isOpen_iff_forall_mem_open.2 fun z hz => ⟨_, connectedComponentIn_subset_stripRightSide hz,
    hU.connectedComponentIn, mem_connectedComponentIn hz.1⟩

theorem liesRightOf_iff {K A : Set ℂ} : LiesRightOf K A ↔ ∀ z ∈ K, z ∉ stripLeftSide A :=
  Set.disjoint_left

theorem liesLeftOf_iff {K A : Set ℂ} : LiesLeftOf K A ↔ ∀ z ∈ K, z ∉ stripRightSide A :=
  Set.disjoint_left

/-- A subset of a set lying to the right of `A` lies to the right of `A` (the deduction of Proposition 5.5: the
flow line `η_{θ₁}` is contained in the counterflow `η'_{θ₁}`, Proposition 4.11, which lies to the right of
`η_{θ₂}`, Proposition 5.1). -/
theorem LiesRightOf.mono {K K' A : Set ℂ} (h : LiesRightOf K A) (hK : K' ⊆ K) : LiesRightOf K' A :=
  h.mono_left hK

theorem LiesLeftOf.mono {K K' A : Set ℂ} (h : LiesLeftOf K A) (hK : K' ⊆ K) : LiesLeftOf K' A :=
  h.mono_left hK

/-- Points of `K` outside the open upper half-plane, or on `A`, never obstruct: only `K ∩ (ℍ \ A)` matters. -/
theorem liesRightOf_inter_iff {K A : Set ℂ} : LiesRightOf (K ∩ (H \ A)) A ↔ LiesRightOf K A := by
  refine ⟨fun h => ?_, fun h => h.mono inter_subset_left⟩
  rw [liesRightOf_iff] at h ⊢
  intro z hz hzL
  exact h z ⟨hz, hzL.1⟩ hzL

theorem LiesRightOf.union {K₁ K₂ A : Set ℂ} (h₁ : LiesRightOf K₁ A) (h₂ : LiesRightOf K₂ A) :
    LiesRightOf (K₁ ∪ K₂) A :=
  Disjoint.union_left h₁ h₂

theorem LiesLeftOf.union {K₁ K₂ A : Set ℂ} (h₁ : LiesLeftOf K₁ A) (h₂ : LiesLeftOf K₂ A) :
    LiesLeftOf (K₁ ∪ K₂) A :=
  Disjoint.union_left h₁ h₂

/-! ### Sanity check: the sides of the curve from the seed to the right strip end along `i[0, ∞)` -/

/-- The ray `i[0, ∞)`: in the chart `E` a curve from the seed to the strip end `+∞`. -/
def imagRay : Set ℂ := {z | z.re = 0 ∧ 0 ≤ z.im}

/-- The open left quadrant `{Re z < 0, Im z > 0}`. -/
def leftQuadrant : Set ℂ := {z | z.re < 0} ∩ {z | 0 < z.im}

/-- The open right quadrant `{Re z > 0, Im z > 0}`. -/
def rightQuadrant : Set ℂ := {z | 0 < z.re} ∩ {z | 0 < z.im}

theorem H_diff_imagRay : H \ imagRay = leftQuadrant ∪ rightQuadrant := by
  ext z
  change (0 < z.im ∧ ¬ (z.re = 0 ∧ 0 ≤ z.im)) ↔ (z.re < 0 ∧ 0 < z.im) ∨ (0 < z.re ∧ 0 < z.im)
  constructor
  · rintro ⟨hz, hne⟩
    rcases lt_trichotomy z.re 0 with h | h | h
    · exact Or.inl ⟨h, hz⟩
    · exact absurd ⟨h, hz.le⟩ hne
    · exact Or.inr ⟨h, hz⟩
  · rintro (⟨h, hz⟩ | ⟨h, hz⟩)
    · exact ⟨hz, fun h' => h.ne h'.1⟩
    · exact ⟨hz, fun h' => h.ne' h'.1⟩

theorem isOpen_leftQuadrant : IsOpen leftQuadrant :=
  (isOpen_lt Complex.continuous_re continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im)

theorem isOpen_rightQuadrant : IsOpen rightQuadrant :=
  (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const Complex.continuous_im)

theorem isPreconnected_leftQuadrant : IsPreconnected leftQuadrant :=
  ((convex_halfSpace_re_lt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected

theorem isPreconnected_rightQuadrant : IsPreconnected rightQuadrant :=
  ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected

theorem disjoint_leftQuadrant_rightQuadrant : Disjoint leftQuadrant rightQuadrant :=
  Set.disjoint_left.2 fun z h₁ h₂ => lt_asymm (show z.re < 0 from h₁.1) (show 0 < z.re from h₂.1)

theorem connectedComponentIn_imagRay_of_left {z : ℂ} (hz : z ∈ leftQuadrant) :
    connectedComponentIn (H \ imagRay) z = leftQuadrant := by
  apply Subset.antisymm
  · rw [H_diff_imagRay]
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union isOpen_leftQuadrant
      isOpen_rightQuadrant disjoint_leftQuadrant_rightQuadrant (connectedComponentIn_subset _ _)
      ⟨z, mem_connectedComponentIn (Or.inl hz), hz⟩
  · exact isPreconnected_leftQuadrant.subset_connectedComponentIn hz
      (by rw [H_diff_imagRay]; exact subset_union_left)

theorem connectedComponentIn_imagRay_of_right {z : ℂ} (hz : z ∈ rightQuadrant) :
    connectedComponentIn (H \ imagRay) z = rightQuadrant := by
  apply Subset.antisymm
  · rw [H_diff_imagRay]
    exact isPreconnected_connectedComponentIn.subset_right_of_subset_union isOpen_leftQuadrant
      isOpen_rightQuadrant disjoint_leftQuadrant_rightQuadrant (connectedComponentIn_subset _ _)
      ⟨z, mem_connectedComponentIn (Or.inr hz), hz⟩
  · exact isPreconnected_rightQuadrant.subset_connectedComponentIn hz
      (by rw [H_diff_imagRay]; exact subset_union_right)

theorem closure_rightQuadrant_subset : closure rightQuadrant ⊆ {z : ℂ | 0 ≤ z.re} :=
  closure_minimal (fun z hz => le_of_lt (show 0 < z.re from hz.1))
    (isClosed_le continuous_const Complex.continuous_re)

theorem closure_leftQuadrant_subset : closure leftQuadrant ⊆ {z : ℂ | z.re ≤ 0} :=
  closure_minimal (fun z hz => le_of_lt (show z.re < 0 from hz.1))
    (isClosed_le Complex.continuous_re continuous_const)

/-- A real point `x` is in the closure of a quadrant of the right sign. -/
theorem ofReal_mem_closure_quadrant {x : ℝ} {Q : Set ℂ}
    (hQ : ∀ ε : ℝ, 0 < ε → (x : ℂ) + (ε : ℂ) * I ∈ Q) : (x : ℂ) ∈ closure Q := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨_, hQ (ε / 2) (by positivity), ?_⟩
  rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  linarith

/-- **Sanity check of the side carriers.** For the curve `i[0, ∞)` from the seed to the strip end `+∞` (in the
chart `E`), the strict left side is the open left quadrant. -/
theorem stripLeftSide_imagRay : stripLeftSide imagRay = leftQuadrant := by
  ext z
  constructor
  · rintro ⟨hz, x, hx, -, hcl⟩
    have hz' := hz
    rw [H_diff_imagRay] at hz'
    rcases hz' with hL | hR
    · exact hL
    · rw [connectedComponentIn_imagRay_of_right hR] at hcl
      have := closure_rightQuadrant_subset hcl
      simp only [mem_ofPred_eq, Complex.ofReal_re] at this
      linarith [hx.2]
  · intro hz
    refine ⟨by rw [H_diff_imagRay]; exact Or.inl hz, -1 / 2, ⟨by norm_num, by norm_num⟩,
      fun h => by norm_num [imagRay] at h, ?_⟩
    rw [connectedComponentIn_imagRay_of_left hz]
    refine ofReal_mem_closure_quadrant fun ε hε => ⟨?_, ?_⟩
    · simp only [mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im]
      norm_num
    · simp [hε]

/-- **Sanity check of the side carriers.** For the curve `i[0, ∞)`, the strict right side is the open right
quadrant. -/
theorem stripRightSide_imagRay : stripRightSide imagRay = rightQuadrant := by
  ext z
  constructor
  · rintro ⟨hz, x, hx, -, hcl⟩
    have hz' := hz
    rw [H_diff_imagRay] at hz'
    rcases hz' with hL | hR
    · rw [connectedComponentIn_imagRay_of_left hL] at hcl
      have := closure_leftQuadrant_subset hcl
      simp only [mem_ofPred_eq, Complex.ofReal_re] at this
      linarith
    · exact hR
  · intro hz
    refine ⟨by rw [H_diff_imagRay]; exact Or.inr hz, 1, one_pos,
      fun h => by norm_num [imagRay] at h, ?_⟩
    rw [connectedComponentIn_imagRay_of_right hz]
    refine ofReal_mem_closure_quadrant fun ε hε => ⟨?_, ?_⟩ <;> simp [hε]

end Sec5

end InteractingSLE
