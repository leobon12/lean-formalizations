import HigherDimLQGContinuity.Concentration.Core

/-!
# Confinement radius and the geodesic-energy majorant (packet N4; blueprint Part C `c:lem-confine`)

NA4 A1 Step 2; Part C Lemma `c:lem-confine`. For a metric family `ρ` (in use `ρ = rho D`):

* `sphereDense d t`: a countable dense subset of the sphere `∂B_t` (spheres of `ℝ^d` are separable).
* `confineGood ρ k g`: `ρ_g(0, q) > ρ_g(0, e₁)` for every `q` in the dense subset of `∂B_{2^(k+1)}`; a measurable
  event (`measurableSet_confineGood`).
* `confinementExp ρ g`: the least `k` with `confineGood ρ k g` (junk `0` if there is none, a null event);
  measurable (`measurable_confinementExp`). The confinement radius is `S = 2^(K+1)`.
* Deterministic confinement (`range_subset_closedBall_of_confineGood`): if `confineGood` holds at scale `S`, every
  constant-speed geodesic from `0` to `e₁` stays in `B̄_S` (a geodesic leaving `B̄_S` crosses `∂B_S` at a time
  `t' < 1`, where `ρ(0, η t') = t' ρ(0, e₁) < ρ(0, e₁) ≤ min_{∂B_S} ρ(0, ·)`).
* `geodMajorant σ H K g = 1 + (log B + 1)/σ + log(2 + S)` with `B = 2 H_K H_0`, `S = 2^(K+1)` for an envelope
  family `H_k` (the (U1) envelopes at radii `2^(k+1)`).

The probabilistic statements (`geodMajorant_spec`, the exponential moment and tail) are in
`Concentration/Majorant.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ## Countable dense subsets of spheres -/

/-- A countable dense subset of the sphere `∂B_t` of `ℝ^d` (spheres are separable). -/
def sphereDense (d : ℕ) (t : ℝ) : Set (Rd d) :=
  Classical.choose (TopologicalSpace.IsSeparable.exists_countable_dense_subset
    (TopologicalSpace.IsSeparable.of_separableSpace (sphere (0 : Rd d) t)))

theorem sphereDense_spec (d : ℕ) (t : ℝ) :
    sphereDense d t ⊆ sphere (0 : Rd d) t ∧ (sphereDense d t).Countable ∧
      sphere (0 : Rd d) t ⊆ closure (sphereDense d t) :=
  Classical.choose_spec (TopologicalSpace.IsSeparable.exists_countable_dense_subset
    (TopologicalSpace.IsSeparable.of_separableSpace (sphere (0 : Rd d) t)))

theorem sphereDense_subset (d : ℕ) (t : ℝ) : sphereDense d t ⊆ sphere (0 : Rd d) t :=
  (sphereDense_spec d t).1

theorem sphereDense_countable (d : ℕ) (t : ℝ) : (sphereDense d t).Countable :=
  (sphereDense_spec d t).2.1

theorem sphere_subset_closure_sphereDense (d : ℕ) (t : ℝ) :
    sphere (0 : Rd d) t ⊆ closure (sphereDense d t) :=
  (sphereDense_spec d t).2.2

/-! ## The confinement test and the confinement exponent -/

/-- The confinement test at scale `k`: `ρ_g(0, e₁) < ρ_g(0, q)` for every `q` in the countable dense subset of
the sphere of radius `2^(k+1)`. -/
def confineGood (ρ : DistRd d → ContMetric d) (k : ℕ) (g : DistRd d) : Prop :=
  ∀ q ∈ sphereDense d ((2 : ℝ) ^ (k + 1)), (ρ g).1 (0, e₁ d) < (ρ g).1 (0, q)

theorem measurableSet_confineGood {ρ : DistRd d → ContMetric d} (hρ : Measurable ρ) (k : ℕ) :
    MeasurableSet {g | confineGood ρ k g} := by
  have he : {g | confineGood ρ k g} =
      ⋂ q ∈ sphereDense d ((2 : ℝ) ^ (k + 1)), {g | (ρ g).1 (0, e₁ d) < (ρ g).1 (0, q)} := by
    ext g
    simp only [confineGood, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact MeasurableSet.biInter (sphereDense_countable d _) fun q _ =>
    measurableSet_lt (p2_measurable_contMetric_apply hρ _) (p2_measurable_contMetric_apply hρ _)

/-- The defining predicate of the confinement exponent (made total). -/
def confinePred (ρ : DistRd d → ContMetric d) (g : DistRd d) (k : ℕ) : Prop :=
  confineGood ρ k g ∨ ∀ j, ¬ confineGood ρ j g

theorem exists_confinePred (ρ : DistRd d → ContMetric d) (g : DistRd d) :
    ∃ k, confinePred ρ g k := by
  by_cases h : ∃ k, confineGood ρ k g
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Or.inl hk⟩
  · push Not at h
    exact ⟨0, Or.inr h⟩

open Classical in
/-- **The confinement exponent** `K` (blueprint `c:lem-confine`): the least `k` with `confineGood ρ k g`, junk `0`
if there is none. The confinement radius is `S = 2^(K+1)`. -/
def confinementExp (ρ : DistRd d → ContMetric d) (g : DistRd d) : ℕ :=
  Nat.find (exists_confinePred ρ g)

open Classical in
theorem measurable_confinementExp {ρ : DistRd d → ContMetric d} (hρ : Measurable ρ) :
    Measurable (confinementExp ρ) := by
  refine measurable_find (p := confinePred ρ) (exists_confinePred ρ) fun k => ?_
  have he : {g | confinePred ρ g k} =
      {g | confineGood ρ k g} ∪ ⋂ j, {g | confineGood ρ j g}ᶜ := by
    ext g
    simp only [confinePred, mem_ofPred_eq, mem_union, mem_iInter, mem_compl_iff]
  rw [he]
  exact (measurableSet_confineGood hρ k).union
    (MeasurableSet.iInter fun j => (measurableSet_confineGood hρ j).compl)

open Classical in
/-- If some scale passes the confinement test, the confinement exponent passes it. -/
theorem confineGood_confinementExp {ρ : DistRd d → ContMetric d} {g : DistRd d}
    (h : ∃ k, confineGood ρ k g) : confineGood ρ (confinementExp ρ g) g := by
  have hs := Nat.find_spec (exists_confinePred ρ g)
  rcases hs with hs | hs
  · exact hs
  · obtain ⟨k, hk⟩ := h
    exact absurd hk (hs k)

open Classical in
/-- Below the confinement exponent the test fails. -/
theorem not_confineGood_of_lt_confinementExp {ρ : DistRd d → ContMetric d} {g : DistRd d} {k : ℕ}
    (hk : k < confinementExp ρ g) : ¬ confineGood ρ k g := fun h =>
  Nat.find_min (exists_confinePred ρ g) hk (Or.inl h)

/-- A failed test produces a point at distance `2^(k+1)` that is `ρ`-closer to `0` than `e₁`. -/
theorem exists_of_not_confineGood {ρ : DistRd d → ContMetric d} {g : DistRd d} {k : ℕ}
    (h : ¬ confineGood ρ k g) :
    ∃ y : Rd d, (2 : ℝ) ^ (k + 1) ≤ ‖y‖ ∧ (ρ g).1 (0, y) ≤ (ρ g).1 (0, e₁ d) := by
  simp only [confineGood, not_forall, not_lt] at h
  obtain ⟨q, hq, hle⟩ := h
  exact ⟨q, (mem_sphere_zero_iff_norm.1 (sphereDense_subset d _ hq)).ge, hle⟩

/-! ## Deterministic confinement -/

/-- Along a path, between a time with `‖P s‖ ≤ a` and a time with `a ≤ ‖P t‖`, the norm takes the value `a`. -/
theorem n4_exists_norm_eq_of (P : C(unitInterval, Rd d)) {a : ℝ} {s t : unitInterval}
    (hs : ‖P s‖ ≤ a) (ht : a ≤ ‖P t‖) : ∃ u : unitInterval, ‖P u‖ = a := by
  have hg : Continuous fun u : unitInterval => ‖P u‖ := continuous_norm.comp P.continuous
  obtain ⟨u, hu⟩ := intermediate_value_univ s t hg ⟨hs, ht⟩
  exact ⟨u, hu⟩

/-- If `ρ(0, q) > ρ(0, e₁)` on a dense subset of `∂B_S`, then `ρ(0, y) ≥ ρ(0, e₁)` on all of `∂B_S`. -/
theorem le_apply_of_dense {G : ContMetric d} {S : ℝ}
    (hgood : ∀ q ∈ sphereDense d S, G.1 (0, e₁ d) < G.1 (0, q)) {y : Rd d}
    (hy : y ∈ sphere (0 : Rd d) S) : G.1 (0, e₁ d) ≤ G.1 (0, y) := by
  have hcl : IsClosed {x : Rd d | G.1 (0, e₁ d) ≤ G.1 (0, x)} :=
    isClosed_le continuous_const (G.1.continuous.comp (continuous_const.prodMk continuous_id))
  have hsub : sphereDense d S ⊆ {x : Rd d | G.1 (0, e₁ d) ≤ G.1 (0, x)} := fun q hq =>
    (hgood q hq).le
  exact closure_minimal hsub hcl (sphere_subset_closure_sphereDense d S hy)

/-- **Deterministic confinement** (blueprint `c:lem-confine` (a), first part): if `ρ(0, q) > ρ(0, e₁)` on a
dense subset of `∂B_S` with `S > 1`, then every constant-speed geodesic from `0` to `e₁` stays in `B̄_S`. -/
theorem range_subset_closedBall_of_dense (hd : 1 ≤ d) {G : ContMetric d} {S : ℝ} (hS : 1 < S)
    (hgood : ∀ q ∈ sphereDense d S, G.1 (0, e₁ d) < G.1 (0, q)) {η : C(unitInterval, Rd d)}
    (hη : IsConstSpeedGeod G 0 (e₁ d) η) : range η ⊆ closedBall (0 : Rd d) S := by
  rintro _ ⟨t, rfl⟩
  rw [mem_closedBall_zero_iff]
  by_contra hcon
  push Not at hcon
  have h0 : ‖η 0‖ ≤ S := by rw [hη.1, norm_zero]; linarith
  obtain ⟨u, hu⟩ := n4_exists_norm_eq_of η h0 hcon.le
  have hL : 0 < G.1 (0, e₁ d) := G.apply_pos (p2_zero_ne_e₁ hd)
  have hge := le_apply_of_dense hgood (mem_sphere_zero_iff_norm.2 hu)
  have hgeo : G.1 (η 0, η u) = |((0 : unitInterval) : ℝ) - u| * G.1 (0, e₁ d) := hη.2.2 0 u
  rw [hη.1, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg u.2.1] at hgeo
  rw [hgeo] at hge
  have hu1 : (1 : ℝ) ≤ u := by
    by_contra h
    push Not at h
    have := mul_lt_mul_of_pos_right h hL
    linarith
  have hu_eq : u = 1 := Subtype.ext (le_antisymm u.2.2 hu1)
  rw [hu_eq, hη.2.1, HigherDimLFPP.norm_e₁ (by omega)] at hu
  linarith

/-- The ball bound along a confined geodesic (blueprint `c:lem-confine` (a), second part): with the `σ`-Hölder
bound `G(x, y) ≤ H |x - y|^σ` on `B̄_S` (`|x - y| ≤ 1`) and `G(0, e₁) ≥ H₀⁻¹`,
`ν_η(B̄_r(u)) ≤ 2 H H₀ r^σ` for `0 < r ≤ 1/2`. -/
theorem pathMeasure_closedBall_le_of_confined (hd : 1 ≤ d) {G : ContMetric d} {S H H₀ σ : ℝ}
    (hH : 0 ≤ H) (hH₀ : 0 < H₀) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hHol : ∀ x ∈ closedBall (0 : Rd d) S, ∀ y ∈ closedBall (0 : Rd d) S, ‖x - y‖ ≤ 1 →
      G.1 (x, y) ≤ H * ‖x - y‖ ^ σ)
    (hlow : H₀⁻¹ ≤ G.1 (0, e₁ d)) {η : C(unitInterval, Rd d)} (hη : IsConstSpeedGeod G 0 (e₁ d) η)
    (hηS : range η ⊆ closedBall (0 : Rd d) S) (u : Rd d) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) :
    (pathMeasure η (closedBall u r)).toReal ≤ 2 * H * H₀ * r ^ σ := by
  have hL : 0 < G.1 (0, e₁ d) := G.apply_pos (p2_zero_ne_e₁ hd)
  have h1 := pathMeasure_closedBall_le_of_isConstSpeedGeod hη hL hηS hH hσ.le hHol u hr hr2
  have h2 : (2 * r) ^ σ ≤ 2 * r ^ σ := by
    rw [Real.mul_rpow (by norm_num) hr.le]
    have : (2 : ℝ) ^ σ ≤ 2 := by
      calc (2 : ℝ) ^ σ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h3 : 1 / G.1 (0, e₁ d) ≤ H₀ := by
    rw [div_le_iff₀ hL]
    have := mul_le_mul_of_nonneg_left hlow hH₀.le
    rwa [mul_inv_cancel₀ hH₀.ne'] at this
  calc (pathMeasure η (closedBall u r)).toReal ≤ H * (2 * r) ^ σ / G.1 (0, e₁ d) := h1
    _ = H * (2 * r) ^ σ * (1 / G.1 (0, e₁ d)) := by ring
    _ ≤ H * (2 * r ^ σ) * H₀ := by
        gcongr
    _ = 2 * H * H₀ * r ^ σ := by ring

/-! ## The majorant -/

/-- **The geodesic-energy majorant** (blueprint `c:lem-confine`): for an envelope family `H : ℕ → DistRd d → ℝ`
(in use, the (U1) envelopes at radii `2^(k+1)`) and a confinement exponent `K`,
`U = 1 + (log B + 1)/σ + log (2 + S)` with `B = 2 H_K H_0` and `S = 2^(K+1)`. -/
def geodMajorant (σ : ℝ) (H : ℕ → DistRd d → ℝ) (K : DistRd d → ℕ) (g : DistRd d) : ℝ :=
  1 + (Real.log (2 * H (K g) g * H 0 g) + 1) / σ + Real.log (2 + (2 : ℝ) ^ (K g + 1))

theorem measurable_geodMajorant {σ : ℝ} {H : ℕ → DistRd d → ℝ} (hH : ∀ k, Measurable (H k))
    {K : DistRd d → ℕ} (hK : Measurable K) : Measurable (geodMajorant σ H K) := by
  have hHK : Measurable fun g => H (K g) g := by
    have h2 : Measurable fun q : DistRd d × ℕ => H q.2 q.1 :=
      measurable_from_prod_countable_left fun k => hH k
    exact h2.comp (measurable_id.prodMk hK)
  have hpow : Measurable fun g => (2 : ℝ) ^ (K g + 1) :=
    (measurable_from_top (f := fun k : ℕ => (2 : ℝ) ^ (k + 1))).comp hK
  unfold geodMajorant
  refine (measurable_const.add ?_).add ((measurable_const.add hpow).log)
  exact (((measurable_const.mul hHK).mul (hH 0)).log.add measurable_const).div_const σ

/-- The majorant is at least `1` when the envelopes are at least `1` (and `σ > 0`). -/
theorem one_le_geodMajorant {σ : ℝ} (hσ : 0 < σ) {H : ℕ → DistRd d → ℝ} (hH1 : ∀ k g, 1 ≤ H k g)
    (K : DistRd d → ℕ) (g : DistRd d) : 1 ≤ geodMajorant σ H K g := by
  unfold geodMajorant
  have h1 : 0 ≤ Real.log (2 * H (K g) g * H 0 g) :=
    Real.log_nonneg (by nlinarith [hH1 (K g) g, hH1 0 g])
  have h2 : 0 ≤ Real.log (2 + (2 : ℝ) ^ (K g + 1)) :=
    Real.log_nonneg (by have := pow_pos (two_pos : (0 : ℝ) < 2) (K g + 1); linarith)
  have h3 : 0 ≤ (Real.log (2 * H (K g) g * H 0 g) + 1) / σ := by positivity
  linarith

end HigherDimLQGContinuity
