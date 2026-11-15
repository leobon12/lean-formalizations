/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsRule
import InteractingSLE.Spec.Supplement.WalkInfMeas

/-!
# The inverse of a measurable random chart is measurable at every point of `ℍ`

Packet PROVE-AUX61-NOJUMP (D19, step 4's record). A measurable random chart (`WalkInf.IsMeasChart`) has measurable
domain events and masked forward maps. Its inverse at a point `w ∈ ℍ` is read as the limit of the first grid points
`z_N` of the domain with `|c.1 z_N − w| < 1/(N + 1)`. Since the chart is conformal, `z_N = c.2.1 (c.1 z_N)` and
`c.1 z_N → w`, so `z_N → c.2.1 w`.

* **`measurable_inv_of_isMeasChart`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Vs

/-- An enumeration of the grid. -/
def gridEnum (n : ℕ) : ℚ × ℚ := (Encodable.decode n).getD (0, 0)

theorem gridEnum_encode (p : ℚ × ℚ) : gridEnum (Encodable.encode p) = p := by
  simp [gridEnum, Encodable.encodek]

/-- The grid points are dense. -/
theorem exists_gridPt_mem_ball (z : ℂ) {δ : ℝ} (hδ : 0 < δ) : ∃ p : ℚ × ℚ, gridPt p ∈ ball z δ := by
  obtain ⟨q₁, hq₁⟩ := exists_rat_btwn (show z.re - δ / 2 < z.re + δ / 2 by linarith)
  obtain ⟨q₂, hq₂⟩ := exists_rat_btwn (show z.im - δ / 2 < z.im + δ / 2 by linarith)
  refine ⟨(q₁, q₂), ?_⟩
  rw [mem_ball, Complex.dist_eq]
  have h1 : |(gridPt (q₁, q₂) - z).re| < δ / 2 := by
    rw [Complex.sub_re, gridPt_re, abs_lt]; constructor <;> linarith [hq₁.1, hq₁.2]
  have h2 : |(gridPt (q₁, q₂) - z).im| < δ / 2 := by
    rw [Complex.sub_im, gridPt_im, abs_lt]; constructor <;> linarith [hq₂.1, hq₂.2]
  calc ‖gridPt (q₁, q₂) - z‖ ≤ |(gridPt (q₁, q₂) - z).re| + |(gridPt (q₁, q₂) - z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ < δ / 2 + δ / 2 := add_lt_add h1 h2
    _ = δ := by ring

/-- The `N`-th approximate preimage test at the `n`-th grid point. -/
def preTest (c : Chart) (w : ℂ) (N n : ℕ) : Prop :=
  gridPt (gridEnum n) ∈ (c.dom : Set ℂ) ∧ dist (c.1 (gridPt (gridEnum n))) w < 1 / ((N : ℝ) + 1)

theorem exists_preTest {c : Chart} (hc : c.IsConformal) {w : ℂ} (hw : w ∈ H) (N : ℕ) : ∃ n, preTest c w N n := by
  have hz₀ : c.2.1 w ∈ (c.dom : Set ℂ) := hc.inv_mem_dom hw
  have hfw : c.1 (c.2.1 w) = w := hc.2.2 w hw
  have hdomo : IsOpen (c.dom : Set ℂ) := c.dom.isOpen
  have hcont : ContinuousAt c.1 (c.2.1 w) :=
    (hc.differentiableOn_fwd.differentiableAt (hdomo.mem_nhds hz₀)).continuousAt
  have hev : ∀ᶠ z in 𝓝 (c.2.1 w), z ∈ (c.dom : Set ℂ) ∧ dist (c.1 z) w < 1 / ((N : ℝ) + 1) := by
    have h1 : ∀ᶠ z in 𝓝 (c.2.1 w), z ∈ (c.dom : Set ℂ) := hdomo.mem_nhds hz₀
    have h2 : ∀ᶠ z in 𝓝 (c.2.1 w), c.1 z ∈ ball w (1 / ((N : ℝ) + 1)) := by
      have := hcont.eventually (ball_mem_nhds (c.1 (c.2.1 w)) (show (0 : ℝ) < 1 / ((N : ℝ) + 1) by positivity))
      rw [hfw] at this
      exact this
    filter_upwards [h1, h2] with z hz1 hz2
    exact ⟨hz1, mem_ball.1 hz2⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨p, hp⟩ := exists_gridPt_mem_ball (c.2.1 w) hδ
  refine ⟨Encodable.encode p, ?_⟩
  rw [preTest, gridEnum_encode]
  exact hball (mem_ball.1 hp)

theorem tendsto_preSel {c : Chart} (hc : c.IsConformal) {w : ℂ} (hw : w ∈ H) {z : ℕ → ℂ}
    (hz : ∀ N, z N ∈ (c.dom : Set ℂ) ∧ dist (c.1 (z N)) w < 1 / ((N : ℝ) + 1)) :
    Tendsto z atTop (𝓝 (c.2.1 w)) := by
  have hy : Tendsto (fun N => c.1 (z N)) atTop (𝓝 w) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun N => (hz N).2.le) ?_)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hcont : ContinuousAt c.2.1 w := (hc.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hw)).continuousAt
  have hyH : ∀ N, c.1 (z N) ∈ H := fun N => hc.fwd_mem (hz N).1
  have hcw : Tendsto (fun N => c.2.1 (c.1 (z N))) atTop (𝓝 (c.2.1 w)) := hcont.tendsto.comp hy
  refine hcw.congr fun N => ?_
  exact hc.inv_fwd (hz N).1

/-- **The inverse of a measurable random chart is measurable at every point of `ℍ`.** -/
theorem measurable_inv_of_isMeasChart {Ω : Type*} {m : MeasurableSpace Ω} {c : Ω → Chart}
    (hc : WalkInf.IsMeasChart m c) {w : ℂ} (hw : w ∈ H) : Measurable[m] fun ω => (c ω).2.1 w := by
  classical
  have hex : ∀ N, ∀ ω, ∃ n, preTest (c ω) w N n := fun N ω => exists_preTest (hc.1 ω) hw N
  have hset : ∀ N n, MeasurableSet[m] {ω | preTest (c ω) w N n} := fun N n => by
    have h1 := hc.2.2.2.1 (gridPt (gridEnum n))
    have h2 := hc.2.2.2.2.1 (gridPt (gridEnum n))
    have e : {ω | preTest (c ω) w N n} = {ω | gridPt (gridEnum n) ∈ ((c ω).dom : Set ℂ)} ∩
        {ω | dist ({ω | gridPt (gridEnum n) ∈ ((c ω).dom : Set ℂ)}.indicator
          (fun ω => (c ω).1 (gridPt (gridEnum n))) ω) w < 1 / ((N : ℝ) + 1)} := by
      ext ω
      simp only [preTest, mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro ⟨hd, hdist⟩
        refine ⟨hd, ?_⟩
        rw [indicator_of_mem (show ω ∈ {ω | gridPt (gridEnum n) ∈ ((c ω).dom : Set ℂ)} from hd)]
        exact hdist
      · rintro ⟨hd, hdist⟩
        refine ⟨hd, ?_⟩
        rw [indicator_of_mem (show ω ∈ {ω | gridPt (gridEnum n) ∈ ((c ω).dom : Set ℂ)} from hd)] at hdist
        exact hdist
    rw [e]
    exact h1.inter (measurableSet_lt (h2.dist measurable_const) measurable_const)
  have hsel : ∀ N, Measurable[m] fun ω => gridPt (gridEnum (Nat.find (hex N ω))) := fun N =>
    Measurable.find (f := fun n _ => gridPt (gridEnum n)) (fun _ => measurable_const) (hset N) (hex N)
  have hlim : ∀ ω, (c ω).2.1 w = limUnder atTop fun N => gridPt (gridEnum (Nat.find (hex N ω))) := fun ω =>
    (tendsto_preSel (hc.1 ω) hw fun N => Nat.find_spec (hex N ω)).limUnder_eq.symm
  simp_rw [hlim]
  exact (StronglyMeasurable.limUnder fun N => (hsel N).stronglyMeasurable).measurable

end InteractingSLE.Theorem14.SB.Vs
