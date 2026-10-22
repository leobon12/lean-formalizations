import HigherDimLQGContinuity.Core.Interfaces

/-!
# The Euclidean endpoint (packet E3), part 1: sup-distances and logarithmic profiles

Blueprint Part C `c:lem-profiles` (c)–(d) and Convention `c:conv`(iii); NA4 §1.2 ("passage from logarithmic
profiles"). Deterministic facts about the frozen `supDistLU` and the interface `logProfile`, used by the endpoint
(5.8):

* the pointwise description of `supDistLU` (`endpt_edist_le_supDistLU`, `endpt_supDistLU_le_iff`), symmetry and the
  triangle inequality;
* `c:lem-profiles` (c): `supDistLU d R (logProfile F) (logProfile G) ≤ supDistLU d R F G`
  (`endpt_supDistLU_logProfile_le`);
* `c:lem-profiles` (d), pointwise and with the constant `2(1 + 2R)` in place of `e(1 + 2R)` (from
  `Real.abs_exp_sub_one_le`): `endpt_abs_sub_euclid_le`;
* measurability of `ω ↦ supDistLU d R (F ω) (G ω)` through a countable dense subset of `B̄_R × B̄_R`
  (`endpt_measurable_supDistLU`);
* Markov's inequality in the form used with `MarginalEuclidStmt` (`endpt_meas_lt_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## `supDistLU` -/

section SupDist

variable {R : ℝ} {F G H : C(Rd d × Rd d, ℝ)}

theorem endpt_edist_le_supDistLU {p : Rd d × Rd d}
    (hp : p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) :
    edist (F p) (G p) ≤ supDistLU d R F G :=
  le_iSup₂ (f := fun p (_ : p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) =>
    edist (F p) (G p)) p hp

theorem endpt_supDistLU_le_iff {c : ℝ≥0∞} :
    supDistLU d R F G ≤ c ↔
      ∀ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R, edist (F p) (G p) ≤ c :=
  iSup₂_le_iff

theorem endpt_supDistLU_comm : supDistLU d R F G = supDistLU d R G F := by
  simp only [supDistLU, edist_comm]

theorem endpt_supDistLU_triangle :
    supDistLU d R F H ≤ supDistLU d R F G + supDistLU d R G H :=
  endpt_supDistLU_le_iff.2 fun _ hp =>
    (edist_triangle _ _ _).trans (add_le_add (endpt_edist_le_supDistLU hp) (endpt_edist_le_supDistLU hp))

/-- `supDistLU d R F G ≤ u` bounds `|F - G|` pointwise on `B̄_R × B̄_R`. -/
theorem endpt_abs_sub_le_of_supDistLU_le {u : ℝ} (hu : 0 ≤ u) (h : supDistLU d R F G ≤ ENNReal.ofReal u)
    {p : Rd d × Rd d} (hp : p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) :
    |F p - G p| ≤ u := by
  have h1 := (endpt_edist_le_supDistLU hp).trans h
  rwa [edist_dist, Real.dist_eq, ENNReal.ofReal_le_ofReal_iff hu] at h1

end SupDist

/-! ## Logarithmic profiles (`c:lem-profiles` (c), (d)) -/

theorem endpt_logProfile_apply (F : C(Rd d × Rd d, ℝ)) (p : Rd d × Rd d) :
    logProfile F p = Real.log (1 + |F p|) := rfl

/-- `u ↦ log (1 + u)` is `1`-Lipschitz on `[0, ∞)`. -/
theorem endpt_abs_log_one_add_sub_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.log (1 + u) - Real.log (1 + v)| ≤ |u - v| := by
  have key : ∀ {u v : ℝ}, 0 ≤ u → 0 ≤ v → v ≤ u → Real.log (1 + u) - Real.log (1 + v) ≤ u - v := by
    intro u v hu hv hvu
    have h1 : 0 < 1 + v := by linarith
    have h2 : 0 < 1 + u := by linarith
    rw [← Real.log_div h2.ne' h1.ne']
    have h3 := Real.log_le_sub_one_of_pos (div_pos h2 h1)
    have h4 : (1 + u) / (1 + v) - 1 ≤ u - v := by
      rw [div_sub_one h1.ne', div_le_iff₀ h1]
      nlinarith
    linarith
  rcases le_total v u with h | h
  · have hlog : Real.log (1 + v) ≤ Real.log (1 + u) := Real.log_le_log (by linarith) (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact key hu hv h
  · have hlog : Real.log (1 + u) ≤ Real.log (1 + v) := Real.log_le_log (by linarith) (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    have := key hv hu h
    linarith

/-- **`c:lem-profiles` (c)**: `supDistLU d R (lp F) (lp G) ≤ supDistLU d R F G`. -/
theorem endpt_supDistLU_logProfile_le {R : ℝ} (F G : C(Rd d × Rd d, ℝ)) :
    supDistLU d R (logProfile F) (logProfile G) ≤ supDistLU d R F G :=
  endpt_supDistLU_le_iff.2 fun p hp => by
    refine le_trans ?_ (endpt_edist_le_supDistLU hp)
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, endpt_logProfile_apply, endpt_logProfile_apply]
    exact ENNReal.ofReal_le_ofReal
      ((endpt_abs_log_one_add_sub_le (abs_nonneg _) (abs_nonneg _)).trans (abs_abs_sub_abs_le_abs_sub _ _))

/-- Inversion of a logarithmic bound: if `u, v ≥ 0` and `|log(1+u) - log(1+v)| ≤ η ≤ 1`, then
`|u - v| ≤ 2(1 + v)η`. -/
theorem endpt_abs_sub_le_of_abs_log_sub_le {u v η : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hη : η ≤ 1)
    (h : |Real.log (1 + u) - Real.log (1 + v)| ≤ η) : |u - v| ≤ 2 * (1 + v) * η := by
  have h1 : 0 < 1 + v := by linarith
  have h2 : 0 < 1 + u := by linarith
  have ht : Real.exp (Real.log (1 + u) - Real.log (1 + v)) = (1 + u) / (1 + v) := by
    rw [Real.exp_sub, Real.exp_log h2, Real.exp_log h1]
  have hexp := Real.abs_exp_sub_one_le (h.trans hη)
  have heq : u - v = (1 + v) * (Real.exp (Real.log (1 + u) - Real.log (1 + v)) - 1) := by
    rw [ht]
    field_simp
    ring
  rw [heq, abs_mul, abs_of_pos h1]
  calc (1 + v) * |Real.exp (Real.log (1 + u) - Real.log (1 + v)) - 1|
      ≤ (1 + v) * (2 * |Real.log (1 + u) - Real.log (1 + v)|) := by gcongr
    _ ≤ (1 + v) * (2 * η) := by gcongr
    _ = 2 * (1 + v) * η := by ring

/-- `|x - y| ≤ 2R` on `B̄_R × B̄_R`. -/
theorem endpt_euclidDistC_le {R : ℝ} {p : Rd d × Rd d}
    (hp : p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) : euclidDistC d p ≤ 2 * R := by
  obtain ⟨h1, h2⟩ := hp
  rw [mem_closedBall, dist_zero_right] at h1 h2
  show dist p.1 p.2 ≤ 2 * R
  calc dist p.1 p.2 ≤ dist p.1 0 + dist 0 p.2 := dist_triangle _ _ _
    _ = ‖p.1‖ + ‖p.2‖ := by rw [dist_zero_right, dist_zero_left]
    _ ≤ 2 * R := by linarith

theorem endpt_euclidDistC_nonneg (p : Rd d × Rd d) : 0 ≤ euclidDistC d p :=
  show 0 ≤ dist p.1 p.2 from dist_nonneg

/-- **`c:lem-profiles` (d)**, pointwise: if `F ≥ 0` at `p ∈ B̄_R × B̄_R` and the profile of `F` is within `η ≤ 1` of
the Euclidean profile on `B̄_R × B̄_R`, then `|F p - |p.1 - p.2|| ≤ 2(1 + 2R)η`. -/
theorem endpt_abs_sub_euclid_le {R η : ℝ} {F : C(Rd d × Rd d, ℝ)} (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (h : supDistLU d R (logProfile F) (logProfile (euclidDistC d)) ≤ ENNReal.ofReal η)
    {p : Rd d × Rd d} (hp : p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) (hF : 0 ≤ F p) :
    |F p - euclidDistC d p| ≤ 2 * (1 + 2 * R) * η := by
  have he := endpt_euclidDistC_nonneg (d := d) p
  have h1 := endpt_abs_sub_le_of_supDistLU_le hη0 h hp
  rw [endpt_logProfile_apply, endpt_logProfile_apply, abs_of_nonneg hF, abs_of_nonneg he] at h1
  calc |F p - euclidDistC d p| ≤ 2 * (1 + euclidDistC d p) * η :=
        endpt_abs_sub_le_of_abs_log_sub_le hF he hη h1
    _ ≤ 2 * (1 + 2 * R) * η := by gcongr; exact endpt_euclidDistC_le hp

/-! ## Measurability (Convention `c:conv`(iii)) -/

/-- `ω ↦ supDistLU d R (F ω) (G ω)` is measurable as soon as all evaluations are: the supremum over `B̄_R × B̄_R`
equals the supremum over a countable dense subset, by continuity. -/
theorem endpt_measurable_supDistLU {Ω : Type*} [MeasurableSpace Ω] {F G : Ω → C(Rd d × Rd d, ℝ)}
    (hF : ∀ p, Measurable fun ω => F ω p) (hG : ∀ p, Measurable fun ω => G ω p) (R : ℝ) :
    Measurable fun ω => supDistLU d R (F ω) (G ω) := by
  obtain ⟨T, hTc, hTK, hKT⟩ := TopologicalSpace.exists_countable_dense_subset
    (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)
  have heq : ∀ ω, supDistLU d R (F ω) (G ω) = ⨆ p ∈ T, edist (F ω p) (G ω p) := by
    intro ω
    refine le_antisymm ?_ (biSup_mono fun p hp => hTK hp)
    refine endpt_supDistLU_le_iff.2 fun p hp => ?_
    have hcont : Continuous fun q => edist (F ω q) (G ω q) :=
      (F ω).continuous.edist (G ω).continuous
    have hclosed : IsClosed {q | edist (F ω q) (G ω q) ≤ ⨆ p ∈ T, edist (F ω p) (G ω p)} :=
      isClosed_le hcont continuous_const
    have hsub : T ⊆ {q | edist (F ω q) (G ω q) ≤ ⨆ p ∈ T, edist (F ω p) (G ω p)} := fun q hq =>
      le_iSup₂ (f := fun q (_ : q ∈ T) => edist (F ω q) (G ω q)) q hq
    exact hclosed.closure_subset_iff.2 hsub (hKT hp)
  simp_rw [heq]
  exact Measurable.biSup T hTc fun p _ => (hF p).edist (hG p)

/-! ## Markov's inequality -/

/-- Markov's inequality with a real moment: `μ{x < f} ≤ B / x^p` when `∫⁻ f^p ≤ B`. -/
theorem endpt_meas_lt_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ≥0∞}
    (hf : AEMeasurable f μ) {x p B : ℝ} (hx : 0 < x) (hp : 0 < p)
    (hB : ∫⁻ ω, f ω ^ p ∂μ ≤ ENNReal.ofReal B) :
    μ {ω | ENNReal.ofReal x < f ω} ≤ ENNReal.ofReal (B / x ^ p) := by
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx p
  have hsub : {ω | ENNReal.ofReal x < f ω} ⊆ {ω | ENNReal.ofReal (x ^ p) ≤ f ω ^ p} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [← ENNReal.ofReal_rpow_of_nonneg hx.le hp.le]
    exact ENNReal.rpow_le_rpow hω.le hp.le
  calc μ {ω | ENNReal.ofReal x < f ω} ≤ μ {ω | ENNReal.ofReal (x ^ p) ≤ f ω ^ p} := measure_mono hsub
    _ ≤ (∫⁻ ω, f ω ^ p ∂μ) / ENNReal.ofReal (x ^ p) :=
        meas_ge_le_lintegral_div (hf.pow_const p) (ENNReal.ofReal_pos.2 hxp).ne' ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal (x ^ p) := by gcongr
    _ = ENNReal.ofReal (B / x ^ p) := (ENNReal.ofReal_div_of_pos hxp).symm

end HigherDimLQGContinuity
