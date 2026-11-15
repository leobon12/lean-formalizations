/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.MarkovOther
import InteractingSLE.Spec.Sec5.Carrier
import InteractingSLE.Spec.Sec5.Prop59
import InteractingSLE.Spec.Sec4.CounterflowHeights

/-!
# Lemma 5.7 from the counterflow restart after a flow-line segment

Packet PROVE-SEC5-E. Specification §5.2, Lemma 5.7 and its proof (`source/spec/p097-144.md` L889–L893, p. 138), with
Remark 5.8 (p. 139) and Figure 5.5.

The proof of Lemma 5.7 has three inputs (Remark 5.8: "The containment proof uses a continuous counterflow which
reaches its designated target without an earlier continuation threshold, continuous relevant angle-varying pieces, and
the first-exit conditional law in the remaining component"):
* (a) the continuity and simplicity of the explored flow line (Lemma 5.6);
* the continuity of the counterflow up to its target (Lemma 4.5 for `η′` and Theorem 1.3);
* (b) "the first-exit conditional law in the remaining component": at each fixed time `σ`, conditionally on
  `η([0, σ])`, the counterflow mapped by the conformal transformation of the remaining domain is the counterflow of the
  mapped conditional field, whose boundary data are those of Figure 5.5 (right panel); Lemma 4.5 then makes it exit at
  `η(σ)`.

This file states (b) for a flow line of the Figure 5.5 field at an angle allowed by (5.3) as the named restart carrier
`CounterflowSegmentRestartStatement` (kernel form, the pattern of `Restart.FirstContactRestartStatement`), and proves
Lemma 5.7 for such a flow line from it: `MarkovOther.ae_isFirstHitPoint_of_restart` turns the carrier into the
first-exit statement at every fixed time, and `Sec4.lemma47_of_remark48` (the density argument of the proof, "By
choosing a dense collection of stopping times … we conclude that the range of `η′` contains `η` … the points of `η`
are hit by `η′` in reverse chronological order") gives the containment and the order.

## Main results

* `fig55Lower`, `fig55LowerFrame`, `IsFig55RestartDatum`: the data of Figure 5.5 (right panel) for one angle and the
  chart datum of the conditional counterflow (`Sec4.stripCounterflowData` of the mapped strip field);
* `IsBoundedRestartDatum`: the same chart datum for any mapped lower data with `≤ −λ′` left and `≥ λ′` right of the
  seed (every angle list allowed by (5.3), Figure 5.5 for general `ℓ`);
* **`stripCounterflowData_le_of_bounds`**, **`le_stripCounterflowData_of_bounds`**, **`fig55LowerFrame_bounds`**,
  **`isRestartTargetDatum_of_isBoundedRestartDatum`**, `isRestartTargetDatum_of_isFig55RestartDatum`: the proof's
  height step ("Our hypotheses on `θᵢ` imply `−λ − θᵢχ ≤ −λ′` and `λ − θᵢχ ≥ λ′`"): with the standing bounds, these
  data have the heights of Lemma 4.5 for `κ′`;
* `CounterflowSegmentRestartStatement` (**named input**): the conditional law of the counterflow after an initial
  segment of a flow line (the cross-conditioning step of Lemma 4.7's proof, p. 118, and Lemma 5.7's proof, p. 138).
* **`ae_isFirstHitPoint_of_counterflowSegmentRestart`**: from the carrier and Aux. lemma 7 for `κ′`, at every fixed
  time `σ` before the lifetime while the flow line stays in `ℍ`, the completed counterflow first hits
  `∂_L𝒮 ∪ η([0, σ])` at `η(σ)`.
* **`lemma57_of_counterflowSegmentRestart`**: Lemma 5.7 for a flow line (one angle) of the Figure 5.5 field, from the
  carrier, Aux. lemma 7 for `κ′`, the continuity and simplicity of the flow line (Lemma 5.6) and the continuity of the
  counterflow up to its target. Conditional helper: it replaces no source theorem.
* `prop59_inclusion_of_counterflowSegmentRestart`: the inclusion half of Proposition 5.9 for a countable family of
  such flow lines (with `Sec5.ae_closure_iUnion_subset_stripCounterflowPath`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Sec5

open Sec4 Restart MarkovOther

/-! ### The data of Figure 5.5 (right panel) and the heights of Lemma 4.5 -/

/-- **The lower data of the mapped conditional strip field** (Figure 5.5, right panel, one angle `θ`): after the map
`ψ : 𝒮 ∖ η([0, σ]) → 𝒮` fixing `±∞` with `η(σ) ↦ 0`, the lower boundary carries `−a` left of `pL` (the image of the
lower boundary left of the seed), `−λ − θχ` on `(pL, 0)` (the left side of the explored segment), `λ − θχ` on
`(0, pR)` (its right side) and `b` right of `pR`. -/
def fig55Lower (κ θ pL pR a b : ℝ) (x : ℝ) : ℝ :=
  if x < pL then -a else if x < 0 then -sleLambda κ - θ * chiC κ
  else if x < pR then sleLambda κ - θ * chiC κ else b

/-- The lower data of Figure 5.5 (right panel) for `h + αχ`, read as data of `h`. -/
def fig55LowerFrame (κ α θ pL pR a b : ℝ) (x : ℝ) : ℝ := fig55Lower κ θ pL pR a b x - α * chiC κ

theorem fig55Lower_of_pos {κ θ pL pR a b y : ℝ} (hp : pL ≤ 0) (hy : 0 < y) :
    fig55Lower κ θ pL pR a b y = sleLambda κ - θ * chiC κ ∨ fig55Lower κ θ pL pR a b y = b := by
  unfold fig55Lower
  split_ifs with h1 h2 h3
  · exact absurd h1 (by linarith)
  · exact absurd h2 (by linarith)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fig55Lower_of_neg {κ θ pL pR a b y : ℝ} (hy : y < 0) :
    fig55Lower κ θ pL pR a b y = -a ∨ fig55Lower κ θ pL pR a b y = -sleLambda κ - θ * chiC κ := by
  unfold fig55Lower
  by_cases h1 : y < pL
  · exact Or.inl (ite_eq_left h1)
  · rw [ite_eq_right h1, ite_eq_left hy]
    exact Or.inr rfl

/-- **The counterflow's heights after mapping out the segment, left of its start**: if the mapped strip field `ĥ`
(data of `h`, frame `α`) has lower data `bL` with `bL + αχ ≥ λ′` right of the seed and the upper data of Figure 5.1
moved to `w₀ = log Q / π + i` with `a′, b′ ≥ λ′ + πχ`, the parameter field of its counterflow `CF_d(ĥ + αχ)` in the
chart `M_Q` is at most `−λ(κ′) + πχ(κ′) = −λ′ − πχ` on `(−∞, 0)` off `−1`. -/
theorem stripCounterflowData_le_of_bounds {κ α a b a' b' Q : ℝ} {bL : ℝ → ℝ} (hκ : 0 < κ)
    (hbd : IsFig51Bounds κ a b a' b') (hpos : ∀ y, 0 < y → sleLambda (16 / κ) - α * chiC κ ≤ bL y)
    (hQ : 0 < Q) {x : ℝ} (hx : x < 0) (hx1 : x ≠ -1) :
    stripCounterflowData κ α Q bL (fig51UpperFrame κ α (Real.log Q / π) a' b') x ≤
      -sleLambda (16 / κ) + π * chiC (16 / κ) := by
  obtain ⟨-, -, -, hb'⟩ := hbd
  have hπ := Real.pi_pos
  rw [chiC_sixteen_div hκ]
  rcases lt_or_gt_of_ne hx1 with hlt | hgt
  · rw [stripCounterflowData_of_lt_neg_one hQ hlt]
    have h1 : 1 < (x - Q) / (x + 1) := by
      rw [lt_div_iff_of_neg (by linarith)]; linarith
    have := hpos _ (div_pos (Real.log_pos h1) hπ)
    linarith
  · rw [stripCounterflowData_of_mem_Ioo_neg_one_zero hQ ⟨hgt, hx⟩]
    have hx1' : 0 < x + 1 := by linarith
    have hgt' : Q < (Q - x) / (x + 1) := by
      rw [lt_div_iff₀ hx1']; nlinarith
    have hlt : Real.log Q / π < Real.log ((Q - x) / (x + 1)) / π :=
      div_lt_div_of_pos_right (Real.log_lt_log hQ hgt') hπ
    unfold fig51UpperFrame fig51Upper
    rw [ite_eq_right (not_lt.2 hlt.le)]
    linarith

/-- **The counterflow's heights after mapping out the segment, right of its start**: with lower data
`bL + αχ ≤ −λ′` left of the seed and the moved upper data, the parameter field in the chart `M_Q` is at least
`λ(κ′) − πχ(κ′) = λ′ + πχ` on `(0, ∞)` off `Q`. -/
theorem le_stripCounterflowData_of_bounds {κ α a b a' b' Q : ℝ} {bL : ℝ → ℝ} (hκ : 0 < κ)
    (hbd : IsFig51Bounds κ a b a' b') (hneg : ∀ y, y < 0 → bL y ≤ -sleLambda (16 / κ) - α * chiC κ)
    (hQ : 0 < Q) {x : ℝ} (hx : 0 < x) (hxQ : x ≠ Q) :
    sleLambda (16 / κ) - π * chiC (16 / κ) ≤
      stripCounterflowData κ α Q bL (fig51UpperFrame κ α (Real.log Q / π) a' b') x := by
  obtain ⟨-, -, ha', -⟩ := hbd
  have hπ := Real.pi_pos
  rw [chiC_sixteen_div hκ]
  rcases lt_or_gt_of_ne hxQ with hlt | hgt
  · rw [stripCounterflowData_of_mem_Ioo_zero ⟨hx, hlt⟩]
    have hx1' : 0 < x + 1 := by linarith
    have hpos : 0 < (Q - x) / (x + 1) := div_pos (by linarith) hx1'
    have hlt' : (Q - x) / (x + 1) < Q := by
      rw [div_lt_iff₀ hx1']; nlinarith
    have hlt2 : Real.log ((Q - x) / (x + 1)) / π < Real.log Q / π :=
      div_lt_div_of_pos_right (Real.log_lt_log hpos hlt') hπ
    unfold fig51UpperFrame fig51Upper
    rw [ite_eq_left hlt2]
    linarith
  · rw [stripCounterflowData_of_lt hQ hgt]
    have hx1' : 0 < x + 1 := by linarith
    have hpos : 0 < (x - Q) / (x + 1) := div_pos (by linarith) hx1'
    have hlt1 : (x - Q) / (x + 1) < 1 := by
      rw [div_lt_one hx1']; linarith
    have := hneg _ (div_neg_of_neg_of_pos (Real.log_neg hpos hlt1) hπ)
    linarith

/-- **The lower data of Figure 5.5 (right panel) satisfies the bounds** (Lemma 5.7's proof: "Our hypotheses on `θᵢ`
imply `−λ − θᵢχ ≤ −λ′` and `λ − θᵢχ ≥ λ′`", with `a, b ≥ λ′`): right of the seed `fig55Lower ≥ λ′`, left of it
`fig55Lower ≤ −λ′`, for `θ ∈ [−π/2, π/2]` and `pL ≤ 0` (`λ′ = λ − πχ/2`, (4.2)). -/
theorem fig55LowerFrame_bounds {κ α θ pL pR a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hbd : IsFig51Bounds κ a b a' b') (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2) (hp : pL ≤ 0) :
    (∀ y, 0 < y → sleLambda (16 / κ) - α * chiC κ ≤ fig55LowerFrame κ α θ pL pR a b y) ∧
      ∀ y, y < 0 → fig55LowerFrame κ α θ pL pR a b y ≤ -sleLambda (16 / κ) - α * chiC κ := by
  obtain ⟨ha, hb, -, -⟩ := hbd
  have hχ := chiC_pos hκ hκ4
  have hlam := sleLambda_sixteen_div_eq_sub hκ
  have hθχ₂ : θ * chiC κ ≤ π / 2 * chiC κ := mul_le_mul_of_nonneg_right hθ₂ hχ.le
  have hθχ₁ : -(π / 2) * chiC κ ≤ θ * chiC κ := mul_le_mul_of_nonneg_right hθ₁ hχ.le
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · unfold fig55LowerFrame
    rcases fig55Lower_of_pos (κ := κ) (θ := θ) (pR := pR) (a := a) (b := b) hp hy with h | h <;> rw [h] <;>
      linarith
  · unfold fig55LowerFrame
    rcases fig55Lower_of_neg (κ := κ) (θ := θ) (pL := pL) (pR := pR) (a := a) (b := b) hy with h | h <;>
      rw [h] <;> linarith

/-- **The chart datum of a conditional counterflow after a flow-line segment, with bounded lower data**: `Q > 0` (the
chart image of the strip end `−∞`; the counterflow's start `w₀` is at `log Q / π + i`), the strip ends `−1` and `Q`
are jump candidates of the word `c`, and off its jumps `c` is the parameter-field data `stripCounterflowData κ α Q`
of the counterflow `CF_d(ĥ + αχ)` of a mapped strip field `ĥ` with lower data `bL` satisfying `bL + αχ ≤ −λ′` left
of the seed and `bL + αχ ≥ λ′` right of it, and with the original upper data `fig51UpperFrame` moved to `w₀`. -/
def IsBoundedRestartDatum (κ α a' b' : ℝ) (d : ℝ × BoundaryWord) : Prop :=
  0 < d.1 ∧ -1 ∈ d.2.jumps ∧ d.1 ∈ d.2.jumps ∧ ∃ bL : ℝ → ℝ,
    (∀ y, y < 0 → bL y ≤ -sleLambda (16 / κ) - α * chiC κ) ∧
    (∀ y, 0 < y → sleLambda (16 / κ) - α * chiC κ ≤ bL y) ∧
    ∀ x ∉ d.2.jumps, d.2.fn x = stripCounterflowData κ α d.1 bL (fig51UpperFrame κ α (Real.log d.1 / π) a' b') x

/-- **The chart datum of the conditional counterflow is that of Figure 5.5 (right panel)**, one angle `θ`: as
`IsBoundedRestartDatum`, with the lower data of the mapped strip field the explicit `fig55LowerFrame κ α θ pL pR a b`
(`pL ≤ 0 ≤ pR` the images of the two sides of the seed). -/
def IsFig55RestartDatum (κ α θ a b a' b' : ℝ) (d : ℝ × BoundaryWord) : Prop :=
  0 < d.1 ∧ -1 ∈ d.2.jumps ∧ d.1 ∈ d.2.jumps ∧ ∃ pL pR : ℝ, pL ≤ 0 ∧ 0 ≤ pR ∧
    ∀ x ∉ d.2.jumps, d.2.fn x = stripCounterflowData κ α d.1 (fig55LowerFrame κ α θ pL pR a b)
      (fig51UpperFrame κ α (Real.log d.1 / π) a' b') x

/-- The Figure 5.5 datum is a bounded restart datum (for `θ ∈ [−π/2, π/2]`, (5.3)). -/
theorem IsFig55RestartDatum.isBoundedRestartDatum {κ α θ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hbd : IsFig51Bounds κ a b a' b') (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2) {d : ℝ × BoundaryWord}
    (hd : IsFig55RestartDatum κ α θ a b a' b' d) : IsBoundedRestartDatum κ α a' b' d := by
  obtain ⟨hQ, hJ1, hJQ, pL, pR, hp, -, hfn⟩ := hd
  obtain ⟨hpos, hneg⟩ := fig55LowerFrame_bounds (α := α) (pR := pR) hκ hκ4 hbd hθ₁ hθ₂ hp
  exact ⟨hQ, hJ1, hJQ, _, hneg, hpos, hfn⟩

/-- **A bounded restart datum has the heights of Lemma 4.5 for `κ′`**: Remark 4.1's bounds hold on both sides, the
data on `(−1, 0)` is `−b′ < −λ′` and the data on `(0, Q)` is `a′ > λ′` (standing bounds `a′, b′ ≥ λ′ + πχ`). -/
theorem isRestartTargetDatum_of_isBoundedRestartDatum {κ α a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hbd : IsFig51Bounds κ a b a' b') {d : ℝ × BoundaryWord} (hd : IsBoundedRestartDatum κ α a' b' d) :
    IsRestartTargetDatum (16 / κ) d := by
  obtain ⟨hQ, hJ1, hJQ, bL, hneg, hpos, hfn⟩ := hd
  have hχ := chiC_pos hκ hκ4
  have hπ := Real.pi_pos
  have hκ' : 0 < 16 / κ := by positivity
  have hlam := sleLambda_pos hκ'
  have hχ' : π * chiC (16 / κ) < 0 := by rw [chiC_sixteen_div hκ]; nlinarith
  refine ⟨fun x hx hxJ _ => ?_, fun x hx hxJ _ => ?_, ?_, ?_⟩
  · rw [hfn x hxJ]
    exact stripCounterflowData_le_of_bounds hκ hbd hpos hQ hx fun h => hxJ (h ▸ hJ1)
  · rw [hfn x hxJ]
    exact le_stripCounterflowData_of_bounds hκ hbd hneg hQ hx fun h => hxJ (h ▸ hJQ)
  · obtain ⟨y, hy1, hy0, hyJ⟩ := exists_mem_Ioo_not_mem d.2.jumps (show (-1 : ℝ) < 0 by norm_num)
    refine ⟨y, hy1.le, hy0, hyJ, ?_⟩
    rw [hfn y hyJ]
    have := stripCounterflowData_le_of_bounds (a := a) (b := b) hκ hbd hpos hQ hy0 hy1.ne'
    intro heq
    rw [heq] at this
    linarith
  · obtain ⟨y, hy0, hyQ, hyJ⟩ := exists_mem_Ioo_not_mem d.2.jumps hQ
    refine ⟨y, hy0, hyQ.le, hyJ, ?_⟩
    rw [hfn y hyJ]
    have := le_stripCounterflowData_of_bounds (a := a) (b := b) hκ hbd hneg hQ hy0 hyQ.ne
    intro heq
    rw [heq] at this
    linarith

/-- **The Figure 5.5 datum has the heights of Lemma 4.5 for `κ′`** (Lemma 5.7's proof, "Our hypotheses on `θᵢ` imply
`−λ − θᵢχ ≤ −λ′` and `λ − θᵢχ ≥ λ′`", with the standing bounds `a, b ≥ λ′` and `a′, b′ ≥ λ′ + πχ`). -/
theorem isRestartTargetDatum_of_isFig55RestartDatum {κ α θ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hbd : IsFig51Bounds κ a b a' b') (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2) {d : ℝ × BoundaryWord}
    (hd : IsFig55RestartDatum κ α θ a b a' b' d) : IsRestartTargetDatum (16 / κ) d :=
  isRestartTargetDatum_of_isBoundedRestartDatum hκ hκ4 hbd (hd.isBoundedRestartDatum hκ hκ4 hbd hθ₁ hθ₂)

/-! ### The named input -/

/-- **Named input: the counterflow after an initial segment of a flow line** (the cross-conditioning step of the
proofs of Lemma 4.7, p. 118: "Proposition 3.7 and Proposition 3.8 together tell us that the boundary data for the
conditional law of `h` given both `η|[0,τ]` and `η′|[0,t]` … agree with those of the conditional law of `h` given just
`η|[0,τ]` … This allows us to use Theorem 2.4 to compute the conditional law of `η′` given `η([0, τ])`", and of
Lemma 5.7, p. 138: "We apply a conformal transformation `ψ : 𝒮 ∖ η([0, σ]) → 𝒮` which fixes `±∞` and sends `η(σ)` to
`0`; the boundary data for the GFF which describes the evolution of `ψ(η′)` is as in the right panel of Figure 5.5 …
Our hypotheses on `θᵢ` imply `−λ − θᵢχ ≤ −λ′` and `λ − θᵢχ ≥ λ′`").

Setting (Figure 5.5 with one angle, in the frame `α` of `Carrier.lean`): `0 < κ < 4`; `h + αχ` has the Figure 5.5
data with the standing bounds `a, b ≥ λ′`, `a′, b′ ≥ λ′ + πχ`; `η` is the flow line of `h + αχ` from `0` with angle
`θ ∈ [−π/2, π/2]` ((5.3)); `η′ = CF_d(h + αχ)` is the counterflow from `z₀ = x₀ + i` with driver `W′` and trace `γ′`
(chart `M_q`, `q = e^{πx₀}`); `η` and `η′` are conditionally independent given `h` (Lemma 4.7's coupling; for
`κ < 4` the flow line is determined by `h`, Theorem 1.2). At every fixed time `σ` there are:
* a canonical space `S` with measurable coordinates: the chart path `γ` and its lifetime `U`, every path continuous
  up to its lifetime;
* a measurable event `M`, the chart datum `β = (Q, c)` (measurable) and the restart variable `X` (measurable), and a
  Markov kernel `K` that is the conditional law of `X` given `β` on `M`;
* for almost every datum `d = (Q, c)`: the data of Figure 5.5, right panel (`IsFig55RestartDatum`: `c` is the
  parameter-field data of the counterflow of the mapped strip field in the chart `M_Q`), and under
  `K d` the chart path has the law of the trace of the flow line from `0` (parameter `κ′`, angle `0`) of a field
  with data `c` (`IsFlowLineTraceLaw`: the driver is an integrated `SLE_κ′(ρ)` evolution from that force word, as
  Theorem 2.4's converse gives it). This is "the counterflow of the mapped conditional field", in its restart chart
  normalized to start `0`, target `∞`, strip ends `−1` (`+∞`) and `Q` (`−∞`); only the driver's law is asked (the
  frozen `IsFlowLine` of the chart field implies it, `MarkovOther.IsFlowLine.isFlowLineTraceLaw`);
* almost surely, if `σ` is before the lifetime of `η` and `η((0, σ])` stays in `ℍ` (no boundary contact), then
  `ω ∈ M` and the completed counterflow is the chart path in the restart chart of `ℍ ∖ η([0, σ])`
  (`IsCounterflowChartContinuation` with tip `η(σ)`).

Only the first-exit consequence is used (`ae_isFirstHitPoint_of_counterflowSegmentRestart`). -/
def CounterflowSegmentRestartStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ α x₀ a b a' b' θ : ℝ, IsFig51Bounds κ a b a' b' →
    -(π / 2) ≤ θ → θ ≤ π / 2 →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hhm : Measurable h),
      IsFig51Field κ α x₀ a b a' b' P h →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
      IsStripFlowLineAt κ α θ (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h η ζ →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (γ' : Ω → ℝ≥0 → ℂ),
      IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ' →
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω)) →
      CondIndep (MeasurableSpace.comap h inferInstance)
        (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
        (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P →
    ∀ σ : ℝ≥0,
    ∃ (S : Type) (_ : MeasurableSpace S) (γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) (M : Set Ω)
      (β : Ω → ℝ × BoundaryWord) (X : Ω → S) (K : Kernel (ℝ × BoundaryWord) S),
      (∀ t, Measurable fun s => γ s t) ∧ Measurable U ∧
      (∀ s, ContinuousOn (γ s) {u | (u : ℝ≥0∞) ≤ U s}) ∧
      MeasurableSet M ∧ Measurable β ∧ Measurable X ∧ IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ d ∂(P.restrict M).map β,
        IsFig55RestartDatum κ α θ a b a' b' d ∧ IsFlowLineTraceLaw (16 / κ) d.2 (K d) γ U) ∧
      ∀ᵐ ω ∂P, (σ : ℝ≥0∞) < ζ ω → (∀ t : ℝ≥0, 0 < t → t ≤ σ → η ω t ∈ H) →
        ω ∈ M ∧ IsCounterflowChartContinuation ((fun s : ℝ => η ω s.toNNReal) '' Icc 0 (σ : ℝ)) (η ω σ)
          (stripCounterflowPath (Real.exp (π * x₀)) (γ' ω)) (β ω).1 (γ (X ω)) (U (X ω))

/-! ### The first exit at a fixed time -/

variable {κ α x₀ a b a' b' θ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {γ' : Ω → ℝ≥0 → ℂ}

/-- **The first exit after a flow-line segment** (Lemma 5.7's proof, p. 138: "This implies that `η′` almost surely
exits `𝒮 ∖ η([0, σ])` at `η(σ)`"), from the restart carrier and Aux. lemma 7 for `κ′ = 16/κ` (Lemma 4.5 for the
conditional counterflow). Almost surely, if `σ` is before the lifetime of the flow line and `η((0, σ])` stays in `ℍ`,
the completed counterflow (continuous on `[0, 1]`) first hits `∂_L𝒮 ∪ η([0, σ])` at `η(σ)`. -/
theorem ae_isFirstHitPoint_of_counterflowSegmentRestart (hR : CounterflowSegmentRestartStatement.{u})
    (h7 : Aux7Statement.{0} (16 / κ)) (hκ : 0 < κ) (hκ4 : κ < 4) (hbd : IsFig51Bounds κ a b a' b')
    (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2) (hhm : Measurable h) (hh : IsFig51Field κ α x₀ a b a' b' P h)
    (hη : IsStripFlowLineAt κ α θ (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h η ζ)
    (hcf : IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ')
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (hci : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hγ : ∀ᵐ ω ∂P, Continuous (γ' ω) ∧ (∀ t, γ' ω t ≠ -1) ∧ Tendsto (fun t => ‖γ' ω t‖) atTop atTop)
    (σ : ℝ≥0) :
    ∀ᵐ ω ∂P, (σ : ℝ≥0∞) < ζ ω → (∀ t : ℝ≥0, 0 < t → t ≤ σ → η ω t ∈ H) →
      IsFirstHitPoint (stripCounterflowPath (Real.exp (π * x₀)) (γ' ω)) 1
        (lowerLineH ∪ (fun s : ℝ => η ω s.toNNReal) '' Icc 0 (σ : ℝ)) (η ω σ) := by
  obtain ⟨S, mS, γ, U, M, β, X, K, hγm, hUm, hγc, hM, hβ, hX, hK, hlaw, hdat, hpath⟩ :=
    hR κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ P h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ
  have hκ' : 0 < 16 / κ := by positivity
  have hξ : ∀ᵐ ω ∂P, ContinuousOn (stripCounterflowPath (Real.exp (π * x₀)) (γ' ω)) (Icc 0 1) := by
    filter_upwards [hγ] with ω ⟨h1, h2, h3⟩
    exact continuousOn_stripCounterflowPath h1 h2 h3
  have hdat' : ∀ᵐ d ∂(P.restrict M).map β,
      IsRestartTargetDatum (16 / κ) d ∧ IsFlowLineTraceLaw (16 / κ) d.2 (K d) γ U :=
    hdat.mono fun d hd => ⟨isRestartTargetDatum_of_isFig55RestartDatum hκ hκ4 hbd hθ₁ hθ₂ hd.1, hd.2⟩
  have hz : ∀ ω, η ω σ ∈ (fun s : ℝ => η ω s.toNNReal) '' Icc 0 (σ : ℝ) := fun ω =>
    ⟨σ, ⟨σ.coe_nonneg, le_rfl⟩, by simp⟩
  exact ae_isFirstHitPoint_of_restart hκ' h7 hγm hUm hγc hM hβ hX hlaw hdat' hξ hz
    (A := fun ω => (fun s : ℝ => η ω s.toNNReal) '' Icc 0 (σ : ℝ)) (z := fun ω => η ω σ)
    (G := fun ω => (σ : ℝ≥0∞) < ζ ω ∧ ∀ t : ℝ≥0, 0 < t → t ≤ σ → η ω t ∈ H)
    (by filter_upwards [hpath] with ω hω hG using hω hG.1 hG.2) |>.mono fun ω hω h1 h2 => hω ⟨h1, h2⟩

/-! ### Lemma 5.7 -/

/-- **Lemma 5.7 for a flow line of the Figure 5.5 field** (one angle `θ ∈ [−π/2, π/2]`, (5.3)), from the restart
carrier (conditional helper; specification p. 138: "The counterflow line `η′` of `h` starting at `z₀` almost surely
contains `η` and, moreover, hits the points of `η` in reverse chronological order").

Inputs besides the carrier, as listed in Remark 5.8:
* Aux. lemma 7 for `κ′ = 16/κ` (Lemma 4.5 for the conditional counterflow);
* the counterflow is continuous up to its target: its trace `γ′` in the chart `M_q` is continuous, avoids `−1` and
  tends to `∞` ("a continuous counterflow which reaches its designated target");
* (a) Lemma 5.6 for the explored segment `η|[0, T]`: `0 < T`, `η` continuous on `[0, T]` and simple on `[0, T)`; the
  horizon `T` is before the lifetime of `η` and `η((0, T))` stays in `ℍ` (non-boundary-intersecting).

Conclusion (almost surely, simultaneously for all times): for every `τ ∈ [0, T]` the completed counterflow first hits
`∂_L𝒮 ∪ η([0, τ])` at `η(τ)`; it contains `η([0, T])`; and it visits `η(t)` strictly before its first visit to `η(s)`
whenever `s < t` (reverse chronological order). -/
theorem lemma57_of_counterflowSegmentRestart (hR : CounterflowSegmentRestartStatement.{u})
    (h7 : Aux7Statement.{0} (16 / κ)) (hκ : 0 < κ) (hκ4 : κ < 4) (hbd : IsFig51Bounds κ a b a' b')
    (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2) (hhm : Measurable h) (hh : IsFig51Field κ α x₀ a b a' b' P h)
    (hη : IsStripFlowLineAt κ α θ (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h η ζ)
    (hcf : IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ')
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (hci : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hγ : ∀ᵐ ω ∂P, Continuous (γ' ω) ∧ (∀ t, γ' ω t ≠ -1) ∧ Tendsto (fun t => ‖γ' ω t‖) atTop atTop)
    {T : Ω → ℝ}
    (hT : ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ) < T ω → (t : ℝ≥0∞) < ζ ω) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ) < T ω → η ω t ∈ H)
    (ha : ∀ᵐ ω ∂P, 0 < T ω ∧ ContinuousOn (fun s : ℝ => η ω s.toNNReal) (Icc 0 (T ω)) ∧
      InjOn (fun s : ℝ => η ω s.toNNReal) (Ico 0 (T ω))) :
    ∀ᵐ ω ∂P,
      (∀ τ ∈ Icc 0 (T ω), IsFirstHitPoint (stripCounterflowPath (Real.exp (π * x₀)) (γ' ω)) 1
          (lowerLineH ∪ (fun s : ℝ => η ω s.toNNReal) '' Icc 0 τ) (η ω τ.toNNReal)) ∧
      (fun s : ℝ => η ω s.toNNReal) '' Icc 0 (T ω) ⊆
        stripCounterflowPath (Real.exp (π * x₀)) (γ' ω) '' Icc 0 1 ∧
      ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T ω →
        ∃ v ∈ Icc (0 : ℝ) 1, stripCounterflowPath (Real.exp (π * x₀)) (γ' ω) v = η ω t.toNNReal ∧
          ∀ w ∈ Icc 0 v, stripCounterflowPath (Real.exp (π * x₀)) (γ' ω) w ≠ η ω s.toNNReal := by
  have ha' : ∀ᵐ ω ∂P, 0 < T ω ∧ ContinuousOn (fun s : ℝ => η ω s.toNNReal) (Icc 0 (T ω)) ∧
      InjOn (fun s : ℝ => η ω s.toNNReal) (Ico 0 (T ω)) ∧
      ContinuousOn (stripCounterflowPath (Real.exp (π * x₀)) (γ' ω)) (Icc 0 1) := by
    filter_upwards [ha, hγ] with ω h1 ⟨h2, h3, h4⟩
    exact ⟨h1.1, h1.2.1, h1.2.2, continuousOn_stripCounterflowPath h2 h3 h4⟩
  refine lemma47_of_remark48 (ξ := fun ω => stripCounterflowPath (Real.exp (π * x₀)) (γ' ω))
    (η := fun ω s => η ω s.toNNReal) ha' fun q hq => ?_
  have hexit := ae_isFirstHitPoint_of_counterflowSegmentRestart hR h7 hκ hκ4 hbd hθ₁ hθ₂ hhm hh hη hcf
    htr' hci hγ q.toNNReal
  have hqc : ((q.toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal q hq
  filter_upwards [hexit, hT] with ω hω ⟨hTζ, hTH⟩ hqT
  rw [hqc] at hω
  refine hω (hTζ _ (by rw [hqc]; exact hqT)) fun t ht htq => hTH t ht ?_
  have : (t : ℝ) ≤ q := by rw [← hqc]; exact_mod_cast htq
  linarith

/-- **The inclusion half of Proposition 5.9 for a countable family of flow lines** (conditional helper; p. 141:
"Lemma 5.7, applied to the countably many allowed finite lists, gives the inclusion of this closed accessible set in
the indicated counterflow range"): for countably many flow lines `ηₖ` of the Figure 5.5 field, with angles in
`[−π/2, π/2]` and horizons `Tₖ` as in `lemma57_of_counterflowSegmentRestart`, almost surely the closure of
`⋃ₖ ηₖ([0, Tₖ])` lies in the completed counterflow range. -/
theorem prop59_inclusion_of_counterflowSegmentRestart (hR : CounterflowSegmentRestartStatement.{u})
    (h7 : Aux7Statement.{0} (16 / κ)) (hκ : 0 < κ) (hκ4 : κ < 4) (hbd : IsFig51Bounds κ a b a' b')
    (hhm : Measurable h) (hh : IsFig51Field κ α x₀ a b a' b' P h)
    (hcf : IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ')
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (hγ : ∀ᵐ ω ∂P, Continuous (γ' ω) ∧ (∀ t, γ' ω t ≠ -1) ∧ Tendsto (fun t => ‖γ' ω t‖) atTop atTop)
    {ι : Type*} [Countable ι] {θs : ι → ℝ} (hθ₁ : ∀ k, -(π / 2) ≤ θs k) (hθ₂ : ∀ k, θs k ≤ π / 2)
    {ηs : ι → Ω → ℝ≥0 → ℂ} {ζs : ι → Ω → ℝ≥0∞}
    (hηs : ∀ k, IsStripFlowLineAt κ α (θs k) (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0}
      {x₀} P h (ηs k) (ζs k))
    (hci : ∀ k, CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => ηs k ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    {Ts : ι → Ω → ℝ}
    (hT : ∀ k, ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ) < Ts k ω → (t : ℝ≥0∞) < ζs k ω) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ) < Ts k ω → ηs k ω t ∈ H)
    (ha : ∀ k, ∀ᵐ ω ∂P, 0 < Ts k ω ∧ ContinuousOn (fun s : ℝ => ηs k ω s.toNNReal) (Icc 0 (Ts k ω)) ∧
      InjOn (fun s : ℝ => ηs k ω s.toNNReal) (Ico 0 (Ts k ω))) :
    ∀ᵐ ω ∂P, closure (⋃ k, (fun s : ℝ => ηs k ω s.toNNReal) '' Icc 0 (Ts k ω)) ⊆
      stripCounterflowPath (Real.exp (π * x₀)) (γ' ω) '' Icc 0 1 :=
  ae_closure_iUnion_subset_stripCounterflowPath hγ fun k => by
    filter_upwards [lemma57_of_counterflowSegmentRestart hR h7 hκ hκ4 hbd (hθ₁ k) (hθ₂ k) hhm hh (hηs k)
      hcf htr' (hci k) hγ (hT k) (ha k)] with ω hω using hω.2.1

end InteractingSLE.Sec5
