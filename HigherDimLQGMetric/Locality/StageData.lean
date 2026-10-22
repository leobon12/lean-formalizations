import HigherDimLQGMetric.Locality.TruncField
import Mathlib.Topology.UrysohnsLemma

/-!
# Spatial cutoff for one locality stage

Port of `LQGMetric.DFGPS.L217.exists_bump_of_isCompact` from the plane to
`Rd d`. It gives the smooth-space margin needed for truncated LFPP locality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- A compact set inside an open set admits a continuous cutoff equal to one
near the compact set, with its support a positive distance inside the open set. -/
theorem l7a_exists_cutoff_of_isCompact {d : ℕ} {K U : Set (Rd d)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (φ : C(Rd d, ℝ)) (U₁ : Set (Rd d)) (δ : ℝ),
      HasCompactSupport φ ∧ tsupport φ ⊆ U ∧ IsOpen U₁ ∧ K ⊆ U₁ ∧
      (∀ x ∈ U₁, φ x = 1) ∧ 0 < δ ∧
      ∀ x, φ x ≠ 0 → closedBall x δ ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hr2 : 0 < r / 2 := by positivity
  obtain ⟨φ, h1, h0, hc, -⟩ := exists_continuous_one_zero_of_isCompact
    (hK.cthickening (r := r / 2)) (isOpen_thickening (δ := r)).isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2
      (cthickening_subset_thickening' hr (by linarith) K))
  have hts : tsupport φ ⊆ U := by
    refine (closure_minimal (fun x hx => ?_) isClosed_cthickening).trans hrU
    by_contra hx'
    exact hx (h0 (fun h => hx' (thickening_subset_cthickening r K h)))
  obtain ⟨δ, hδ, hδU⟩ := hc.exists_cthickening_subset_open hU hts
  refine ⟨φ, thickening (r / 2) K, δ, hc, hts, isOpen_thickening,
    self_subset_thickening hr2 K,
    fun x hx => h1 (thickening_subset_cthickening _ K hx), hδ,
    fun x hx => ?_⟩
  exact (closedBall_subset_cthickening (subset_tsupport _ hx) δ).trans hδU

/-- A single finite locality stage admits one scale shift after which every
truncation support stays in the appropriate side of the spatial split. -/
theorem l7a_exists_stage_data {d : ℕ} {V U : Set (Rd d)}
    (hV : IsOpen V) (hU : IsOpen U)
    {K K' : Set (Rd d)} (hK : IsCompact K) (hK' : IsCompact K')
    (hKV : K ⊆ V) (hK'U : K' ⊆ U)
    {εs : ℕ → ℝ} (hεt : Tendsto εs atTop (𝓝 0)) :
    ∃ (φ : C(Rd d, ℝ)) (U₁ : Set (Rd d)) (δ : ℝ) (m : ℕ),
      HasCompactSupport φ ∧ IsOpen U₁ ∧ K' ⊆ U₁ ∧
      (∀ x ∈ U₁, φ x = 1) ∧ 0 < δ ∧
      (∀ x, φ x ≠ 0 → closedBall x δ ⊆ U) ∧
      (∀ k, ∀ y ∈ K, closedBall y (Real.sqrt (εs (k + m))) ⊆ V) ∧
      (∀ k, ∀ y ∈ K', closedBall y (Real.sqrt (εs (k + m))) ⊆ U₁) := by
  obtain ⟨φ, U₁, δ, hφc, _, hU₁, hK'U₁, hφ1, hδ, hφU⟩ :=
    l7a_exists_cutoff_of_isCompact hK' hU hK'U
  obtain ⟨η, hη, hηV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨η', hη', hη'U⟩ := hK'.exists_cthickening_subset_open hU₁ hK'U₁
  have hsq : Tendsto (fun n => Real.sqrt (εs n)) atTop (𝓝 0) := by
    have ht := (Real.continuous_sqrt.tendsto 0).comp hεt
    rwa [Real.sqrt_zero] at ht
  obtain ⟨m, hm⟩ := eventually_atTop.1
    (hsq.eventually (gt_mem_nhds (lt_min hη hη')))
  refine ⟨φ, U₁, δ, m, hφc, hU₁, hK'U₁, hφ1, hδ, hφU,
    fun k y hy => ?_, fun k y hy => ?_⟩
  · have hlt := hm (k + m) (by omega)
    exact (closedBall_subset_closedBall (hlt.le.trans (min_le_left _ _))).trans
      ((closedBall_subset_cthickening hy η).trans hηV)
  · have hlt := hm (k + m) (by omega)
    exact (closedBall_subset_closedBall (hlt.le.trans (min_le_right _ _))).trans
      ((closedBall_subset_cthickening hy η').trans hη'U)

/-- The support radius of the truncated kernel eventually fits around every
point of a fixed compact subset of an open set. -/
theorem l7a_eventually_sqrt_margin {d : ℕ} {K U : Set (Rd d)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {εs : ℕ → ℝ} (hεt : Tendsto εs atTop (𝓝 0)) :
    ∃ m : ℕ, ∀ k, ∀ z ∈ K, closedBall z (Real.sqrt (εs (k + m))) ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hsq : Tendsto (fun n => Real.sqrt (εs n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hεt
  obtain ⟨m, hm⟩ := eventually_atTop.1 (hsq.eventually (gt_mem_nhds hδ))
  refine ⟨m, fun k z hz => ?_⟩
  have hlt := hm (k + m) (by omega)
  exact (closedBall_subset_closedBall hlt.le).trans
    ((closedBall_subset_cthickening hz δ).trans hδU)

/-- A cutoff supported where the Markov harmonic part is continuous extends
their product continuously by zero across the boundary. -/
theorem l7a_continuous_cutoffH {d : ℕ} {U : Set (Rd d)} (hU : IsOpen U)
    (φ : C(Rd d, ℝ)) (H : Rd d → ℝ) (hH : ContinuousOn H U)
    (hsup : tsupport φ ⊆ U) :
    Continuous (fun x => φ x * H x) := by
  apply continuous_of_tsupport
  intro x hx
  have hxU : x ∈ U := hsup (tsupport_mul_subset_left hx)
  exact (φ.continuousAt x).mul (hH.continuousAt (hU.mem_nhds hxU))

/-- The cutoff harmonic correction is globally bounded for each sample. -/
theorem l7a_bounded_cutoffH {d : ℕ} {U : Set (Rd d)} (hU : IsOpen U)
    (φ : C(Rd d, ℝ)) (H : Rd d → ℝ) (hH : ContinuousOn H U)
    (hsup : tsupport φ ⊆ U) (hcompact : HasCompactSupport φ) :
    ∃ M : ℝ, ∀ x, |φ x * H x| ≤ M := by
  have hc := l7a_continuous_cutoffH hU φ H hH hsup
  have hcs : HasCompactSupport (fun x => φ x * H x) := hcompact.mul_right
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨M, fun x => by simpa only [Real.norm_eq_abs] using hM x⟩

/-- On the open set where the cutoff is one, subtracting the global cutoff
correction is exactly the restriction of the Markov exterior residual. -/
theorem l7a_cutoff_residual_restrict {d : ℕ}
    (V U₁ : TopologicalSpace.Opens (Rd d))
    (hU₁ : U₁ ≤ extOpen V) (φ : C(Rd d, ℝ)) (H : Rd d → ℝ)
    (hHc : ContinuousOn H (extOpen V))
    (hsup : tsupport φ ⊆ extOpen V)
    (hφ1 : ∀ x ∈ U₁, φ x = 1) (g : DistRd d) :
    restrictTo U₁ (g - ofCont ⟨fun x => φ x * H x,
      l7a_continuous_cutoffH (extOpen V).isOpen φ H hHc hsup⟩) =
      restrictOn hU₁ (restrictTo (extOpen V) g - ofFunOn (extOpen V) H) := by
  ext ψ
  rw [restrictTo_sub, sub_apply, restrictOn_apply, sub_apply,
    ← restrictOn_restrictTo hU₁ g, restrictOn_apply, restrictTo_ofCont_apply]
  have hHi : LocallyIntegrableOn H (extOpen V) volume :=
    hHc.locallyIntegrableOn (extOpen V).isOpen.measurableSet
  rw [ofFunOn, Distribution.ofFun_apply hHi]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [coe_testInclOn, ContinuousMap.coe_mk, smul_eq_mul]
  by_cases hx : x ∈ U₁
  · rw [hφ1 x hx, one_mul]
  · rw [ψ.zero_on_compl hx, Pi.zero_apply, zero_mul, zero_mul]

end HigherDimLQGMetric
