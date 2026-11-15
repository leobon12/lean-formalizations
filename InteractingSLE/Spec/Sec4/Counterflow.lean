/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Strip
import InteractingSLE.Frozen.Spec.IsChartTransport
import InteractingSLE.Frozen.Spec.IsFlowLineDriver

/-!
# §4.2: the reverse counterflow `CF_d` on the strip and the left boundary

Packet PROVE-SEC4-B2 (specification §4.2, p. 116, "Fixed frame for the strip constructions"; (FD11.1), (FD11.5),
Aux. lemma 1, pp. 12–13).

A strip counterflow of a displayed flow field `u` is `CF_d(u) = CF_lit(u + πχ)`, coupled to the parameter-`κ′` field
`F_d(u) = −u − πχ` (FD11.1), from `z₀ = (log q)/π + i` to `0`. In the strip coordinate, Aux. lemma 1 uses
`P(z) = −(e^{πz} + q)/(e^{πz} − 1)` with lift `L_P = log(π(q+1)) + πz − 2 Log(e^{πz} − 1)` (FD11.5). Fields of this
file are read in the exponential chart `E(z) = e^{πz} − 1` (`Strip.lean`), and `P = M_q ∘ E` with

  `M_q(w) = −1 − (1 + q)/w`,  `M_q⁻¹(z) = −(1 + q)/(z + 1)`,  `L_{M_q}(w) = log(1 + q) − 2 Log w`,

so `L_P = L_{M_q} ∘ E + L_E` and, by (FD11.2), `F_d(u)^P = −(u^E)^{M_q} …`: the parameter field in the chart `P` is the
chart transport (frozen `IsChartTransport`, coefficient `χ(κ′) = −χ`) of `−h − (α + π)χ` by `M_q`, where `h` is the
`E`-image of the strip field and `u = h + αχ`. `M_q` sends `E(z₀) = −1 − q` to `0`, the target `E(0) = 0` to `∞`,
the strip end `−∞` (`w = −1`) to `q` and the end `+∞` (`w = ∞`) to `−1`.

* `stripCounterflowChart q`: the chart `(M_q, M_q⁻¹, Im L_{M_q})`, with its basic identities.
* `IsStripCounterflowDriver κ α q P h W ζ`: `W` (lifetime `ζ`) drives `CF_d(h + αχ)` from `z₀` to `0` (the pattern
  of the frozen `IsCenteredCounterflowDriver`: data `b′` of the parameter field, chart transport, Theorem 1.1
  coupling with parameter `16/κ`). Lemma 4.7 uses `α = −π/2`: `CF_d(h − π/2 χ) = CF_lit(h + π/2 χ)`, coupled to
  `F = −h − π/2 χ`.
* `stripCounterflowPath q γ`: the completed counterflow in the chart `E`, parametrized on `[0, 1]` (Lemma 4.7 proof,
  p. 118: "parametrize the completed counterflow line on a compact time interval"), terminal point `0`.
* `leftEndSide A`: the points of `ℍ \ A` whose complementary component reaches the strip end `−∞` (`w = −1`);
  `IsStripLeftBoundary`: the left boundary statement of Proposition 4.9, with `leftEndSide_eq_of_isStripLeftBoundary`
  (the left complementary region of the counterflow range is that of `η`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

namespace InteractingSLE

namespace Sec4

/-! ### The chart `M_q` -/

/-- The chart of the reverse strip exploration from `z₀ = (log q)/π + i` to `0`, read in the exponential chart:
`fwd = M_q`, `M_q(w) = −1 − (1 + q)/w`; `inv = M_q⁻¹`, `M_q⁻¹(z) = −(1 + q)/(z + 1)`; lift
`Im L_{M_q}(w) = Im(log(1 + q) − 2 Log w) = −2 arg w` (FD11.5 with `P = M_q ∘ E`). -/
def stripCounterflowChart (q : ℝ) : Chart :=
  (fun w => -1 - (1 + q) * w⁻¹, fun z => -(1 + q) * (z + 1)⁻¹, fun w => (-2 * Complex.log w).im)

theorem stripCounterflowChart_fwd (q : ℝ) (w : ℂ) :
    (stripCounterflowChart q).1 w = -1 - (1 + q) * w⁻¹ := rfl

theorem stripCounterflowChart_inv (q : ℝ) (z : ℂ) :
    (stripCounterflowChart q).2.1 z = -(1 + q) * (z + 1)⁻¹ := rfl

theorem stripCounterflowChart_lift (q : ℝ) (w : ℂ) :
    (stripCounterflowChart q).2.2 w = -2 * arg w := by
  simp [stripCounterflowChart, log_im]

variable {q : ℝ}

theorem one_add_ne_zero_of_pos (hq : 0 < q) : (1 + q : ℂ) ≠ 0 := by
  rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.2 (by linarith)

/-- `M_q` sends `E(z₀) = −1 − q` to `0`. -/
theorem stripCounterflowChart_fwd_seed (hq : 0 < q) : (stripCounterflowChart q).1 (-1 - q) = 0 := by
  have h : (-1 - q : ℂ) = -(1 + q) := by ring
  rw [stripCounterflowChart_fwd, h, inv_neg, mul_neg, mul_inv_cancel₀ (one_add_ne_zero_of_pos hq)]
  ring

/-- `M_q⁻¹(0) = −1 − q = E(z₀)`. -/
theorem stripCounterflowChart_inv_zero (q : ℝ) : (stripCounterflowChart q).2.1 0 = -1 - q := by
  simp [stripCounterflowChart_inv]; ring

theorem stripCounterflowChart_fwd_inv (hq : 0 < q) {z : ℂ} (hz : z ≠ -1) :
    (stripCounterflowChart q).1 ((stripCounterflowChart q).2.1 z) = z := by
  have hz1 : z + 1 ≠ 0 := fun h => hz (eq_neg_of_add_eq_zero_left h)
  have hq1 := one_add_ne_zero_of_pos hq
  rw [stripCounterflowChart_fwd, stripCounterflowChart_inv]
  field_simp
  ring

theorem stripCounterflowChart_inv_fwd (hq : 0 < q) {w : ℂ} (hw : w ≠ 0) :
    (stripCounterflowChart q).2.1 ((stripCounterflowChart q).1 w) = w := by
  have hq1 := one_add_ne_zero_of_pos hq
  rw [stripCounterflowChart_fwd, stripCounterflowChart_inv,
    show -1 - (1 + q) * w⁻¹ + 1 = -((1 + q) * w⁻¹) by ring, inv_neg, mul_inv, inv_inv]
  field_simp

theorem stripCounterflowChart_inv_mem_H (hq : 0 < q) {z : ℂ} (hz : z ∈ H) :
    (stripCounterflowChart q).2.1 z ∈ H := by
  have hz1 : 0 < z.im := hz
  have hne : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hns : 0 < Complex.normSq (z + 1) := Complex.normSq_pos.2 hne
  show 0 < (-(1 + (q : ℂ)) * (z + 1)⁻¹).im
  simp only [neg_mul, neg_im, mul_im, inv_re, inv_im, add_re, add_im, one_re, one_im, ofReal_re,
    ofReal_im]
  have h3 : -((1 + q) * (-(z.im + 0) / normSq (z + 1)) + (0 + 0) * ((z.re + 1) / normSq (z + 1)))
      = (1 + q) * (z.im / normSq (z + 1)) := by ring
  rw [h3]
  exact mul_pos (by linarith) (div_pos hz1 hns)

theorem stripCounterflowChart_fwd_mem_H (hq : 0 < q) {w : ℂ} (hw : w ∈ H) :
    (stripCounterflowChart q).1 w ∈ H := by
  have hw1 : 0 < w.im := hw
  have hne : w ≠ 0 := DerivLog.ne_zero_of_mem_H hw
  have hns : 0 < Complex.normSq w := Complex.normSq_pos.2 hne
  show 0 < (-1 - (1 + (q : ℂ)) * w⁻¹).im
  simp only [sub_im, neg_im, one_im, mul_im, inv_re, inv_im, add_re, add_im, one_re, ofReal_re,
    ofReal_im]
  have h3 : -0 - ((1 + q) * (-w.im / normSq w) + (0 + 0) * (w.re / normSq w))
      = (1 + q) * (w.im / normSq w) := by ring
  rw [h3]
  exact mul_pos (by linarith) (div_pos hw1 hns)

/-- The exploration domain of the chart is all of `ℍ`. -/
theorem image_stripCounterflowChart_inv (hq : 0 < q) : (stripCounterflowChart q).2.1 '' H = H := by
  refine Subset.antisymm (image_subset_iff.2 fun z hz => stripCounterflowChart_inv_mem_H hq hz)
    fun w hw => ⟨_, stripCounterflowChart_fwd_mem_H hq hw,
      stripCounterflowChart_inv_fwd hq (DerivLog.ne_zero_of_mem_H hw)⟩

/-! ### The reverse counterflow -/

/-- `W` (lifetime `ζ`) drives, in the chart `M_q ∘ E`, the reverse strip counterflow `CF_d(h_𝒮 + αχ)` from
`z₀ = (log q)/π + i` to `0` of the strip field whose `E`-image is `h` (§4.2, p. 116, "Fixed frame for the strip
constructions"; (FD11.1), Aux. lemma 1): the parameter-`κ′` field `F_d(h + αχ)` (`κ′ = 16/κ`), written in the chart
`M_q` by the coordinate rule with coefficient `χ(κ′)`, is `h′ = (−h − (α + π)χ) ∘ M_q⁻¹ + χ(κ′) Im L_{M_q} ∘ M_q⁻¹`;
its boundary data `b′` is locally constant off `jumps′`; and `W` drives the Theorem 1.1 curve (parameter `16/κ`,
angle `0`) of `h′` from `0` to `∞`. The physical counterflow is `M_q⁻¹(γ)` for the trace `γ` of `W`. Same pattern as
the frozen `IsCenteredCounterflowDriver` (`α = 0`, chart `R`). Lemma 4.7 and Proposition 4.11 use `α = −π/2`. -/
def IsStripCounterflowDriver (κ α q : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b' jumps' ∧
    (∀ ω, IsChartTransport (stripCounterflowChart q) (-1) (-((α + π) * chiC κ)) (chiC (16 / κ))
      (h ω) (h' ω)) ∧
    IsFlowLineDriver (16 / κ) b' jumps' 0 P h' W ζ

/-- The completed reverse counterflow in the chart `E`, parametrized on `[0, 1]`: for `s < 1` the physical point
`M_q⁻¹(γ(s/(1 − s)))` of the trace `γ` (in the chart `M_q`) at capacity time `s/(1 − s)`, and the terminal point
`0` at `s = 1` (Lemma 4.7 proof, p. 118). -/
def stripCounterflowPath (q : ℝ) (γ : ℝ≥0 → ℂ) (s : ℝ) : ℂ :=
  if s < 1 then (stripCounterflowChart q).2.1 (γ (s / (1 - s)).toNNReal) else 0

theorem stripCounterflowPath_of_lt {γ : ℝ≥0 → ℂ} {s : ℝ} (hs : s < 1) :
    stripCounterflowPath q γ s = (stripCounterflowChart q).2.1 (γ (s / (1 - s)).toNNReal) :=
  ite_eq_left hs

theorem stripCounterflowPath_one (γ : ℝ≥0 → ℂ) : stripCounterflowPath q γ 1 = 0 :=
  ite_eq_right (lt_irrefl 1)

/-- The counterflow starts at `E(z₀) = −1 − q` when its trace starts at `0`. -/
theorem stripCounterflowPath_zero {γ : ℝ≥0 → ℂ} (hγ : γ 0 = 0) : stripCounterflowPath q γ 0 = -1 - q := by
  rw [stripCounterflowPath_of_lt one_pos, zero_div, Real.toNNReal_zero, hγ, stripCounterflowChart_inv_zero]

/-! ### Left side of a crossing and the left boundary -/

/-- The points of `ℍ \ A` whose complementary component reaches the strip end `−∞`, i.e. `w = −1` in the chart `E`
(the left of a curve crossing the strip from `∂_L𝒮` to `∂_U𝒮`). -/
def leftEndSide (A : Set ℂ) : Set ℂ :=
  {z | z ∈ H \ A ∧ (-1 : ℂ) ∈ closure (connectedComponentIn (H \ A) z)}

theorem leftEndSide_subset (A : Set ℂ) : leftEndSide A ⊆ H \ A := fun _ hz => hz.1

theorem connectedComponentIn_subset_leftEndSide {A : Set ℂ} {z : ℂ} (hz : z ∈ leftEndSide A) :
    connectedComponentIn (H \ A) z ⊆ leftEndSide A := by
  intro w hw
  refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
  rw [← connectedComponentIn_eq hw]
  exact hz.2

theorem isOpen_leftEndSide {A : Set ℂ} (hA : IsClosed A) : IsOpen (leftEndSide A) := by
  have hU : IsOpen (H \ A) := (isOpen_lt continuous_const Complex.continuous_im).sdiff hA
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨_, connectedComponentIn_subset_leftEndSide hz,
    hU.connectedComponentIn, mem_connectedComponentIn hz.1⟩

/-- `η` (a curve crossing the strip, as the set `A` of its points in the chart `E`) is the left boundary of the
closed set `K` (the completed counterflow range): `A ⊆ K` and no point of `K` lies strictly on the left of `A`
(Proposition 4.9, "`η` is equal to the left boundary of `η′`"; its proof shows exactly these two facts: "the range
of `η′` contains `η`" and "`η` is to the left of `η′`"). By `leftEndSide_eq_of_isStripLeftBoundary` the left
complementary region of `K` is then that of `A`. -/
def IsStripLeftBoundary (A K : Set ℂ) : Prop := A ⊆ K ∧ K ∩ leftEndSide A = ∅

/-- If `A` is the left boundary of `K`, the left complementary regions of `K` and of `A` coincide (so the frontier
of the left region of `K` is that of `A`). -/
theorem leftEndSide_eq_of_isStripLeftBoundary {A K : Set ℂ} (h : IsStripLeftBoundary A K) :
    leftEndSide K = leftEndSide A := by
  obtain ⟨hAK, hKA⟩ := h
  have hsub : H \ K ⊆ H \ A := sdiff_subset_sdiff_right hAK
  apply Subset.antisymm
  · intro z hz
    exact ⟨hsub hz.1, closure_mono (connectedComponentIn_mono z hsub) hz.2⟩
  · intro z hz
    have hC : connectedComponentIn (H \ A) z ⊆ H \ K := by
      intro w hw
      have hwL := connectedComponentIn_subset_leftEndSide hz hw
      refine ⟨hwL.1.1, fun hwK => ?_⟩
      have : w ∈ K ∩ leftEndSide A := ⟨hwK, hwL⟩
      rw [hKA] at this
      exact this
    have hzK : z ∈ H \ K := hC (mem_connectedComponentIn hz.1)
    refine ⟨hzK, closure_mono ?_ hz.2⟩
    exact (isPreconnected_connectedComponentIn).subset_connectedComponentIn
      (mem_connectedComponentIn hz.1) hC

/-! ### Continuity of the completed path -/

/-- The time change `s ↦ s/(1 − s)` sends `s → 1⁻` to `+∞`. -/
theorem tendsto_div_one_sub_nhdsLT_one :
    Tendsto (fun s : ℝ => s / (1 - s)) (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun s : ℝ => 1 - s) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) := (continuous_const.sub continuous_id).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [mem_Ioi, sub_pos]; exact hs
  have h2 : Tendsto (fun s : ℝ => s) (𝓝[<] 1) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have := h2.pos_mul_atTop one_pos (tendsto_inv_nhdsGT_zero.comp h1)
  simpa [div_eq_mul_inv] using this

/-- `M_q⁻¹(z) → 0` as `z → ∞`: the counterflow target `0` corresponds to `∞` in the chart `M_q`. -/
theorem tendsto_stripCounterflowChart_inv_cocompact {q : ℝ} :
    Tendsto (fun z : ℂ => (stripCounterflowChart q).2.1 z) (Bornology.cobounded ℂ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hn : Tendsto (fun z : ℂ => ‖z + 1‖) (Bornology.cobounded ℂ) atTop := by
    refine tendsto_atTop_mono (fun z => ?_) ((tendsto_norm_cobounded_atTop).atTop_add (tendsto_const_nhds (x := (-1 : ℝ))))
    have := norm_sub_norm_le z (-1)
    simp only [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  have := (tendsto_inv_atTop_zero.comp hn).const_mul ‖(-(1 + (q : ℂ)))‖
  simp only [mul_zero] at this
  refine this.congr fun z => ?_
  simp [stripCounterflowChart_inv, norm_inv]

/-- The completed counterflow path is continuous on `[0, 1]` when the trace `γ` (in the chart `M_q`) is continuous,
avoids `−1` (the strip end `+∞`) and tends to `∞` (actual endpoint `0`, Lemma 4.5): the continuity input of Lemma 4.7
(`lemma47_of_remark48`) from Theorem 1.3 and the endpoint. -/
theorem continuousOn_stripCounterflowPath {q : ℝ} {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (hne : ∀ t, γ t ≠ -1) (hinf : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    ContinuousOn (stripCounterflowPath q γ) (Icc 0 1) := by
  set f : ℝ → ℂ := fun s => (stripCounterflowChart q).2.1 (γ (s / (1 - s)).toNNReal) with hf
  have hinvc : ∀ z : ℂ, z ≠ -1 → ContinuousAt (fun z : ℂ => (stripCounterflowChart q).2.1 z) z := by
    intro z hz
    have hz1 : z + 1 ≠ 0 := fun h => hz (eq_neg_of_add_eq_zero_left h)
    simp only [stripCounterflowChart_inv]
    exact continuousAt_const.mul ((continuousAt_id.add continuousAt_const).inv₀ hz1)
  intro s hs
  rcases eq_or_lt_of_le hs.2 with rfl | hlt
  · -- the terminal point
    refine ContinuousWithinAt.mono ?_ (Icc_subset_Iic_self)
    rw [← continuousWithinAt_Iio_iff_Iic]
    rw [ContinuousWithinAt, stripCounterflowPath_one]
    have hu : Tendsto (fun s : ℝ => γ (s / (1 - s)).toNNReal) (𝓝[<] 1) (Bornology.cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      exact hinf.comp (tendsto_real_toNNReal_atTop.comp tendsto_div_one_sub_nhdsLT_one)
    refine ((tendsto_stripCounterflowChart_inv_cocompact (q := q)).comp hu).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (stripCounterflowPath_of_lt hs).symm
  · have hcont : ContinuousAt f s := by
      have hd : ContinuousAt (fun s : ℝ => (s / (1 - s)).toNNReal) s :=
        continuous_real_toNNReal.continuousAt.comp
          (continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by linarith))
      have hg : ContinuousAt (fun s : ℝ => γ (s / (1 - s)).toNNReal) s :=
        ContinuousAt.comp (g := γ) (f := fun s : ℝ => (s / (1 - s)).toNNReal) hγ.continuousAt hd
      exact ContinuousAt.comp (g := fun z : ℂ => (stripCounterflowChart q).2.1 z) (hinvc _ (hne _)) hg
    refine (hcont.congr ?_).continuousWithinAt
    filter_upwards [Iio_mem_nhds hlt] with s' hs'
    exact (stripCounterflowPath_of_lt hs').symm
end Sec4

end InteractingSLE
