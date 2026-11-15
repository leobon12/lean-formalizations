/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VgBad
import InteractingSLE.Spec.Supplement.SB2VfReadAe

/-!
# SB2(1)'s version half: good rational readings are dense after the entrance

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108).

* `exists_good_rat` (deterministic): if the flow is continuous before the horizon `t_L + S₁` and its bad times on
  `(0, S₁)` (outside an open set `D'`) have empty interior, then every interval `(t_L + a, t_L + b)`,
  `0 ≤ a < b ≤ S₁`, contains a rational time `q` with `η q − u ∈ D'`;
* **`ae_good_rat`**: almost surely at a launch on the entrance event, every interval `(a, b)` with `T_L ≤ a < b` and
  `b < ζ` contains a rational time `q` whose line-mark reading is in the chart domain
  (`Vh.etaRead D q ω ∈ dom (I.chart ω)`), from `Vg.ae_bad_interior_empty`, the flow's continuity
  (`Lw.ae_flowLine_regular`) and the chart glue (`Vf.relGood_iff`).

This is the density input for reading the lift and its capacity from the line marks. Theorem 1.3 and the named S3
input as before (R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vg

open Lv Exist.Staged Exist.StagedLaw

/-- **A good rational time in every interval after the entrance** (deterministic). -/
theorem exists_good_rat {η : ℝ≥0 → ℂ} {u : ℝ} {D' : Set ℂ} (hD' : IsOpen D') {tL : ℝ≥0} {S₁ : ℝ}
    (hc : ∀ x : ℝ≥0, (x : ℝ) < tL + S₁ → ContinuousAt η x)
    (hbad : interior {r ∈ Ioo (0 : ℝ) S₁ | η (tL + r.toNNReal) - u ∉ D'} = ∅)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ S₁) :
    ∃ q : ℚ≥0, (tL : ℝ) + a < ((q : ℝ≥0) : ℝ) ∧ ((q : ℝ≥0) : ℝ) < tL + b ∧ η q - u ∈ D' := by
  -- a good time in `(a, b)`
  have hsub : ¬ Ioo a b ⊆ {r ∈ Ioo (0 : ℝ) S₁ | η (tL + r.toNNReal) - u ∉ D'} := by
    intro hs
    have hI := interior_maximal hs isOpen_Ioo
    rw [hbad] at hI
    obtain ⟨x, hx⟩ := nonempty_Ioo.2 hab
    exact hI hx
  rw [not_subset] at hsub
  obtain ⟨r, hr, hrbad⟩ := hsub
  have hr0 : 0 < r := lt_of_le_of_lt ha hr.1
  have hgood : η (tL + r.toNNReal) - u ∈ D' := by
    by_contra hn
    exact hrbad ⟨⟨hr0, lt_of_lt_of_le hr.2 hb⟩, hn⟩
  set x₀ : ℝ≥0 := tL + r.toNNReal with hx₀
  have hx₀r : (x₀ : ℝ) = tL + r := by rw [hx₀, NNReal.coe_add, Real.coe_toNNReal _ hr0.le]
  -- a neighbourhood of `x₀` of good times
  have hcont : ContinuousAt (fun x => η x - u) x₀ := (hc x₀ (by rw [hx₀r]; linarith [hr.2])).sub continuousAt_const
  have hev := hcont.preimage_mem_nhds (hD'.mem_nhds hgood)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hev
  -- a rational time in the neighbourhood and in `(t_L + a, t_L + b)`
  have hlo : max ((tL : ℝ) + a) ((x₀ : ℝ) - ε) < min ((tL : ℝ) + b) ((x₀ : ℝ) + ε) := by
    rw [hx₀r]
    exact max_lt (lt_min (by linarith [hr.1, hr.2]) (by linarith [hr.1])) (lt_min (by linarith [hr.2]) (by linarith))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlo
  have hq0 : (0 : ℚ) ≤ q := by
    have : (0 : ℝ) ≤ q := (by positivity : (0 : ℝ) ≤ (tL : ℝ) + a).trans ((le_max_left _ _).trans hq1.le)
    exact_mod_cast this
  have hqr : ((q.toNNRat : ℝ≥0) : ℝ) = q := by
    have h1 : ((q.toNNRat : ℚ) : ℝ) = q := by rw [Rat.coe_toNNRat q hq0]
    rw [← h1]
    norm_cast
  refine ⟨q.toNNRat, ?_, ?_, ?_⟩
  · rw [hqr]; exact (le_max_left _ _).trans_lt hq1
  · rw [hqr]; exact hq2.trans_le (min_le_left _ _)
  · have hd : dist (q.toNNRat : ℝ≥0) x₀ < ε := by
      rw [NNReal.dist_eq, hqr, abs_lt]
      constructor
      · linarith [(le_max_right ((tL : ℝ) + a) ((x₀ : ℝ) - ε)).trans_lt hq1]
      · linarith [hq2.trans_le (min_le_right ((tL : ℝ) + b) ((x₀ : ℝ) + ε))]
    exact hball hd

/-- **Good rational readings are dense after the entrance**, almost surely at a launch on the entrance event. -/
theorem ae_good_rat (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ}
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ a c : ℝ, (Ve.entT κ b jumps E k u η ζ ω).toReal ≤ a → a < c → ENNReal.ofReal c < ζ ω →
        ∃ q : ℚ≥0, a < ((q : ℝ≥0) : ℝ) ∧ ((q : ℝ≥0) : ℝ) < c ∧ Vh.etaRead D q ω ∈ (I.chart ω).dom := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hwp := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hR := HP.pieces_regular _ hwp
  filter_upwards [ae_bad_interior_empty h13 hS3 HP, Lw.ae_flowLine_regular h13 HP.kappa_pos HP.flow,
    I.chart_eq, Vh.ae_etaRead_eq D, hR.ae_pieceRegular] with ω hbadω hfl hch hη hpr hF hT a c ha hac hcζ
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  set S₁ : ℝ := c - TL.toReal with hS₁
  have hS₁pos : 0 < S₁ := by rw [hS₁]; linarith
  have hS₁ζ : ENNReal.ofReal (TL.toReal + S₁) < ζ ω := by rw [hS₁, add_sub_cancel]; exact hcζ
  have hbad := hbadω hF hT S₁ hS₁pos hS₁ζ
  -- the flow is continuous before `c`
  have hc : ∀ x : ℝ≥0, (x : ℝ) < TL.toNNReal + S₁ → ContinuousAt (η ω) x := by
    intro x hx
    have hxc : ((x : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      refine lt_of_le_of_lt ?_ hcζ
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (by rw [hS₁, hTLr] at hx; linarith)
    obtain ⟨y, hxy, hyζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hxc
    have hnhds : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ ω} ∈ 𝓝 x :=
      mem_of_superset (Iio_mem_nhds (ENNReal.coe_lt_coe.1 hxy)) fun t ht =>
        (ENNReal.coe_lt_coe.2 ht).le.trans hyζ.le
    exact hfl.1.continuousAt hnhds
  -- the chart glue at a launch
  have hreg : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c', θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2) :=
    fun j c' θ' hlj => hpr j c' θ' hlj
  obtain ⟨hcl, -⟩ := Tc.chartClause_of_launch (u := u) hreg hF
  have hconf := Vf.isConformal_of_shift hcl.1.1
  have hD'open : IsOpen (H \ fillH ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)) := by
    rw [← hcl.1.coe_dom]; exact (Lw.shiftChart _ u _).dom.isOpen
  obtain ⟨q, hq1, hq2, hqg⟩ := exists_good_rat hD'open hc hbad (a := a - TL.toReal) (b := c - TL.toReal)
    (by linarith) (by linarith) (by rw [hS₁])
  rw [hTLr] at hq1 hq2
  refine ⟨q, by linarith, by linarith, ?_⟩
  have hqζ : ((q : ℝ≥0) : ℝ≥0∞) ≤ ζ ω := by
    refine (lt_of_le_of_lt ?_ hcζ).le
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact (Vf.relGood_iff D I hconf hcl.1 (hch hF) (hη q hqζ)).2 hqg

end InteractingSLE.Theorem14.SB.Vg
