import HigherDimLQGMetric.Determ.PathCompare
import LQGMetric.Papers.LM.T1_7N1

/-! A path-length bound when one translated cube is resampled. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {d : ℕ}

private lemma edist_le {D D' : ContMetric d} {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ x y : Rd d, D'.1 (x, y) ≤ c * D.1 (x, y)) (x y : Rd d) :
    edist (D'.pt x) (D'.pt y) ≤ ENNReal.ofReal c * edist (D.pt x) (D.pt y) := by
  rw [ContMetric.edist_pt, ContMetric.edist_pt, ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal (hle x y)

private lemma curve_of_le {D D' : ContMetric d} {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ x y : Rd d, D'.1 (x, y) ≤ c * D.1 (x, y)) {P : ℝ → Rd d} {a b : ℝ}
    (h : LQGMetric.LM.T17Curve (D.pt ∘ P) a b) (hP : ContinuousOn P (Icc a b)) :
    LQGMetric.LM.T17Curve (D'.pt ∘ P) a b ∧
      D'.len P a b ≤ ENNReal.ofReal c * D.len P a b := by
  have hv : eVariationOn (D'.pt ∘ P) (Icc a b) ≤
      ENNReal.ofReal c * eVariationOn (D.pt ∘ P) (Icc a b) :=
    LQGMetric.LM.t17_eVariationOn_le_mul fun x _ y _ => edist_le hc hle (P x) (P y)
  exact ⟨⟨h.1, D'.continuous_pt.comp_continuousOn hP,
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h.2.2) hv⟩, hv⟩

/-- The length outside the resampled cube is unchanged, and the inside length
increases by at most the global Lipschitz factor. -/
theorem determ_resample {D D' : ContMetric d} {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ x y : Rd d, D'.1 (x, y) ≤ c * D.1 (x, y))
    {ε R : ℝ} (hε : 0 < ε) {θ : Fin d → ℝ}
    (hθ : θ ∈ determUnitShift d) {P : ℝ → Rd d} (hP : Continuous P)
    {a b : ℝ} (hab : a ≤ b) (hfin : D.len P a b ≠ ⊤)
    (hPR : MapsTo P (Icc a b) (Metric.closedBall 0 R))
    (hnull : LQGMetric.LM.t17LenMeas (D.pt ∘ P) a b
      (Icc a b ∩ P ⁻¹' determGrid ε θ) = 0)
    {k₀ : Fin d → ℤ}
    (hS : ∀ k ∈ determFixedBox ε R, k ≠ k₀ →
      ∀ u ∈ determCube ε θ k, ∀ v ∈ determCube ε θ k,
      D.internal (determCube ε θ k) u v =
        D'.internal (determCube ε θ k) u v) :
    (∀ k ∈ determFixedBox ε R, k ≠ k₀ →
      determPiece D' P a b ε θ k = determPiece D P a b ε θ k) ∧
    determPiece D' P a b ε θ k₀ ≤ c * determPiece D P a b ε θ k₀ ∧
    (D'.len P a b).toReal = ∑ k ∈ determFixedBox ε R,
      determPiece D' P a b ε θ k ∧
    (D.len P a b).toReal = ∑ k ∈ determFixedBox ε R,
      determPiece D P a b ε θ k ∧ D'.len P a b ≠ ⊤ := by
  have hPc : ContinuousOn P (Icc a b) := hP.continuousOn
  have h : LQGMetric.LM.T17Curve (D.pt ∘ P) a b :=
    ⟨hab, D.continuous_pt.comp_continuousOn hPc, hfin⟩
  obtain ⟨h', hlen'⟩ := curve_of_le hc hle h hPc
  have hsm : LQGMetric.LM.t17LenMeas (D'.pt ∘ P) a b ≤
      (Real.toNNReal c) • LQGMetric.LM.t17LenMeas (D.pt ∘ P) a b :=
    LQGMetric.LM.t17LenMeas_le_smul h h' _ fun x _ y _ => edist_le hc hle (P x) (P y)
  have hnull' : LQGMetric.LM.t17LenMeas (D'.pt ∘ P) a b
      (Icc a b ∩ P ⁻¹' determGrid ε θ) = 0 := by
    refine le_antisymm ((hsm _).trans ?_) zero_le
    rw [Measure.smul_apply, hnull, smul_zero]
  have hfin' : ∀ k, LQGMetric.LM.t17LenMeas (D'.pt ∘ P) a b
      (Icc a b ∩ P ⁻¹' determCube ε θ k) ≠ ⊤ :=
    fun k => ne_top_of_le_ne_top h'.2.2 ((measure_mono inter_subset_left).trans
      (LQGMetric.LM.t17LenMeas_Icc h').le)
  have hfin0 : ∀ k, LQGMetric.LM.t17LenMeas (D.pt ∘ P) a b
      (Icc a b ∩ P ⁻¹' determCube ε θ k) ≠ ⊤ :=
    fun k => ne_top_of_le_ne_top h.2.2 ((measure_mono inter_subset_left).trans
      (LQGMetric.LM.t17LenMeas_Icc h).le)
  have hsum : ∀ (e : ContMetric d), LQGMetric.LM.T17Curve (e.pt ∘ P) a b →
      (∀ k, LQGMetric.LM.t17LenMeas (e.pt ∘ P) a b
        (Icc a b ∩ P ⁻¹' determCube ε θ k) ≠ ⊤) →
      LQGMetric.LM.t17LenMeas (e.pt ∘ P) a b
        (Icc a b ∩ P ⁻¹' determGrid ε θ) = 0 →
      (e.len P a b).toReal = ∑ k ∈ determFixedBox ε R,
        determPiece e P a b ε θ k := by
    intro e he hfe hne
    have hsum' := determ_sum_cubes (LQGMetric.LM.t17LenMeas (e.pt ∘ P) a b)
      hε hθ hP hPR hne
    rw [LQGMetric.LM.t17LenMeas_Icc he] at hsum'
    unfold ContMetric.len curveLength determPiece
    rw [hsum', ENNReal.toReal_sum fun k _ => hfe k]
  refine ⟨fun k hk hk0 => ?_, ?_, hsum D' h' hfin' hnull',
    hsum D h hfin0 hnull, h'.2.2⟩
  · unfold determPiece
    rw [determ_lenMeas_eq_of_internal_eq (determ_isOpen_cube ε θ k)
      (hS k hk hk0) hPc h h']
  · unfold determPiece
    have h1 := hsm (Icc a b ∩ P ⁻¹' determCube ε θ k₀)
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (hfin0 k₀)) h1
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal _ hc] at h2

/-- Countable-chain presentation of the internal distance in an open ball. -/
def determF (m : ℕ) (z w : Rd d) (D : ContMetric d) : ℝ≥0∞ :=
  D.chainInf (Metric.ball 0 (m : ℝ)) z w

theorem determ_measurableF (m : ℕ) (z w : Rd d) : Measurable (determF m z w) :=
  (ContMetric.measurable_chainInf _).comp
    (measurable_id.prodMk (measurable_const (a := (z, w))))

/-- One-cell resampling increases the internal distance by at most the
near-minimality slack plus the excess length spent in that cell. -/
theorem determ_A_bound {D D' : ContMetric d} {c : ℝ} (hc1 : 1 ≤ c)
    (hle : ∀ x y : Rd d, D'.1 (x, y) ≤ c * D.1 (x, y))
    {ε R : ℝ} (hε : 0 < ε) {θ : Fin d → ℝ}
    (hθ : θ ∈ determUnitShift d) {P : ℝ → Rd d} (hP : Continuous P)
    {a b : ℝ} (hab : a ≤ b) (hfin : D.len P a b ≠ ⊤)
    (hPR : MapsTo P (Icc a b) (Metric.closedBall 0 R))
    {m : ℕ} {z w : Rd d}
    (hPm : MapsTo P (Icc a b) (Metric.ball 0 (m : ℝ)))
    (hPa : P a = z) (hPb : P b = w)
    (hnull : LQGMetric.LM.t17LenMeas (D.pt ∘ P) a b
      (Icc a b ∩ P ⁻¹' determGrid ε θ) = 0)
    {k₀ : Fin d → ℤ} (hk₀ : k₀ ∈ determFixedBox ε R)
    (hS : ∀ k ∈ determFixedBox ε R, k ≠ k₀ →
      ∀ u ∈ determCube ε θ k, ∀ v ∈ determCube ε θ k,
      D.internal (determCube ε θ k) u v =
        D'.internal (determCube ε θ k) u v) :
    max ((determF m z w D').toReal - (determF m z w D).toReal) 0 ≤
      (D.len P a b).toReal - (determF m z w D).toReal +
        (c - 1) * determPiece D P a b ε θ k₀ := by
  have hc : (0 : ℝ) ≤ c := zero_le_one.trans hc1
  obtain ⟨hne, hk, hs', hs, hfin'⟩ :=
    determ_resample hc hle hε hθ hP hab hfin hPR hnull hS
  have hint : ∀ e : ContMetric d, determF m z w e ≤ e.len P a b := by
    intro e
    refine (e.chainInf_le_internal Metric.isOpen_ball z w).trans ?_
    have hh := internalEDist_le_curveLength
      (X := e.Space) (Y := e.pt '' Metric.ball 0 (m : ℝ))
      (P := e.pt ∘ P) hab (e.continuous_pt.comp_continuousOn hP.continuousOn)
      (fun t ht => ⟨P t, hPm ht, rfl⟩)
    rw [← hPa, ← hPb]
    exact hh
  have hF : (determF m z w D).toReal ≤ (D.len P a b).toReal :=
    ENNReal.toReal_mono hfin (hint D)
  have hF' : (determF m z w D').toReal ≤ (D'.len P a b).toReal :=
    ENNReal.toReal_mono hfin' (hint D')
  have hℓ : 0 ≤ determPiece D P a b ε θ k₀ := ENNReal.toReal_nonneg
  have h := LQGMetric.LM.t17_A_le_b (determFixedBox ε R) hk₀
    (determPiece D P a b ε θ) (determPiece D' P a b ε θ)
    (c := c) (DS := (determF m z w D').toReal)
    (F := (determF m z w D).toReal) (G := (D.len P a b).toReal)
    (e := 0) hne hk (hF'.trans_eq hs') (by rw [hs, add_zero]) (by nlinarith)
  simpa only [add_zero] using h

end HigherDimLQGMetric
