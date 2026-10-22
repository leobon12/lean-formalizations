import HigherDimLQGMetric.Field.SphereAvgBasic
import HigherDimLQGMetric.Field.TestIntegral

/-!
# Mollified sphere averages are pairings with one test function

Packet F1 (basic sphere-average layer). Port of LQGMetric's
`lqg_metric/LQGMetric/Field/CircleAvgPairing.lean`
(`ballK`, `bumpCurve`, `circBump`, `circleAverage_pairing`, `integral_circBump`) from circles in
`ℂ` to spheres in `Rd d` (ruling M10).

For a distribution `h`, the `n`-th mollified sphere average `sphereAvgSeq h r z n =
∫ ⟨h, ψ_{n, z + r u}⟩ dσ(u)` is the pairing of `h` with the single test function
`sphBump n z r = σ_{z,r} * ψ_n`, `y ↦ ∫ ψ_{n, z + r u}(y) dσ(u)` (`sphereAvgSeq_eq_apply_sphBump`).
Proof: `TestIntegral.exists_testIntegral` for the continuous family `u ↦ ψ_{n, z + r u}` in
`𝓓_K`, `K = B̄(z, |r| + 1)`, parametrized by the unit sphere with the normalized cone measure
`sphereMeasure d` (whose image in `ℝ^d` is `unitSphereProb d`).

Consequences: `sphBump` is nonnegative, supported in `B̄(z, |r| + 1)`, of unit mass (`d ≥ 1`), and
the differences of mollified sphere averages are pairings with mean-zero test functions
(`sphDiff`), the input of the Gaussian computations of packet F3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Function TopologicalSpace Filter Topology Metric
open scoped Distributions ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### The sphere as a parameter space -/

/-- The normalized cone measure on the unit sphere (as a subtype). -/
def sphereMeasure (d : ℕ) : Measure (sphere (0 : Rd d) 1) :=
  ((volume : Measure (Rd d)).toSphere univ)⁻¹ • (volume : Measure (Rd d)).toSphere

instance isFiniteMeasure_sphereMeasure (d : ℕ) : IsFiniteMeasure (sphereMeasure d) := by
  refine ⟨lt_of_le_of_lt ?_ ENNReal.one_lt_top⟩
  simp only [sphereMeasure, Measure.smul_apply, smul_eq_mul]
  set a := (volume : Measure (Rd d)).toSphere univ
  rcases eq_or_ne a 0 with ha | ha
  · rw [ha, mul_zero]; exact zero_le_one
  rcases eq_or_ne a ⊤ with ha' | ha'
  · rw [ha', ENNReal.inv_top, zero_mul]; exact zero_le_one
  · rw [ENNReal.inv_mul_cancel ha ha']

theorem map_sphereMeasure (d : ℕ) :
    (sphereMeasure d).map Subtype.val = unitSphereProb d := by
  rw [sphereMeasure, Measure.map_smul _ measurable_subtype_coe.aemeasurable]
  rfl

theorem integral_unitSphereProb_eq_sphereMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : Rd d → E} (hg : Continuous g) :
    ∫ x, g x ∂(unitSphereProb d) = ∫ u, g (u : Rd d) ∂(sphereMeasure d) := by
  rw [← map_sphereMeasure, integral_map measurable_subtype_coe.aemeasurable
    hg.aestronglyMeasurable]

/-! ### The family `u ↦ ψ_{n, z + r u}` in `𝓓_K` -/

/-- the compact `B̄(z, |r| + 1)` -/
def ballK (z : Rd d) (r : ℝ) : Compacts (Rd d) := ⟨closedBall z (|r| + 1), isCompact_closedBall _ _⟩

theorem bumpTest_eq_zero_of_not_mem_ballK (n : ℕ) (z : Rd d) (r : ℝ) {u : Rd d} (hu : ‖u‖ = 1)
    {y : Rd d} (hy : y ∉ (ballK z r : Set (Rd d))) : bumpTest n (z + r • u) y = 0 := by
  apply bumpTest_eq_zero
  have h1 : |r| + 1 < dist y z := by simpa [ballK] using hy
  have h2 : dist (z + r • u) z = |r| := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs]
  have h3 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  rw [← dist_eq_norm]
  linarith [dist_triangle y (z + r • u) z]

theorem support_bumpTest_sphere (n : ℕ) (z : Rd d) (r : ℝ) (u : sphere (0 : Rd d) 1) :
    support (⇑(bumpTest n (z + r • (u : Rd d)))) ⊆ (ballK z r : Set (Rd d)) := by
  intro y hy
  by_contra hK
  exact hy (bumpTest_eq_zero_of_not_mem_ballK n z r (mem_sphere_zero_iff_norm.1 u.2) hK)

/-- `u ↦ ψ_{n, z + r u}` as a family in `𝓓_{B̄(z, |r|+1)}`. -/
def bumpFam (n : ℕ) (z : Rd d) (r : ℝ) (u : sphere (0 : Rd d) 1) :
    𝓓^{⊤}_{ballK z r}(Rd d, ℝ) :=
  ContDiffMapSupportedIn.of_support_subset (bumpTest n (z + r • (u : Rd d))).contDiff
    (support_bumpTest_sphere n z r u)

@[simp]
theorem bumpFam_apply (n : ℕ) (z : Rd d) (r : ℝ) (u : sphere (0 : Rd d) 1) (y : Rd d) :
    bumpFam n z r u y = bumpTest n (z + r • (u : Rd d)) y := rfl

theorem continuous_bumpFam (n : ℕ) (z : Rd d) (r : ℝ) : Continuous (bumpFam n z r) := by
  let g := bumpTest (d := d) n 0
  let Ψ : sphere (0 : Rd d) 1 → Rd d → ℝ := fun u y => g (y + -(z + r • (u : Rd d)))
  have hΨ : ∀ u y, Ψ u y = bumpTest n (z + r • (u : Rd d)) y := fun u y => by
    simp only [Ψ, g]; rw [bumpTest_apply_sub n (z + r • (u : Rd d)) y, sub_eq_add_neg]
  have hs : ∀ u, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ u) :=
    fun u => g.contDiff.comp (contDiff_id.add contDiff_const)
  have hK : ∀ u, ∀ y ∉ (ballK z r : Set (Rd d)), Ψ u y = 0 := fun u y hy => by
    rw [hΨ]; exact bumpTest_eq_zero_of_not_mem_ballK n z r (mem_sphere_zero_iff_norm.1 u.2) hy
  have hD : ∀ i : ℕ, Continuous fun p : sphere (0 : Rd d) 1 × Rd d =>
      iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
    intro i
    simp only [Ψ]
    simp_rw [iteratedFDeriv_comp_add_right]
    exact (g.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_snd.add (continuous_const.add
        ((continuous_subtype_val.comp continuous_fst).const_smul r)).neg)
  have hc := continuous_testFamK (ballK z r) Ψ hs hK hD
  have e : bumpFam n z r = testFamK (ballK z r) Ψ hs hK := by
    funext u
    ext y
    exact (hΨ u y).symm
  rw [e]
  exact hc

/-! ### The test function `σ_{z,r} * ψ_n` -/

theorem exists_sphBump (n : ℕ) (z : Rd d) (r : ℝ) :
    ∃ I : 𝓓^{⊤}_{ballK z r}(Rd d, ℝ), (∀ y, I y = ∫ u, bumpFam n z r u y ∂(sphereMeasure d)) ∧
      ∀ T : 𝓓^{⊤}_{ballK z r}(Rd d, ℝ) →L[ℝ] ℝ,
        T I = ∫ u, T (bumpFam n z r u) ∂(sphereMeasure d) :=
  TestIntegral.exists_testIntegral (sphereMeasure d) (continuous_bumpFam n z r)

/-- `σ_{z,r} * ψ_n`: `y ↦ ∫ ψ_{n, z + r u}(y) dσ(u)`, as a test function. -/
def sphBump (n : ℕ) (z : Rd d) (r : ℝ) : TestRd d :=
  TestFunction.ofSupportedIn (subset_univ _) (exists_sphBump n z r).choose

theorem continuous_bumpTest_apply_affine (n : ℕ) (z : Rd d) (r : ℝ) (y : Rd d) :
    Continuous fun u : Rd d => bumpTest n (z + r • u) y :=
  (continuous_eval_const y).comp
    ((continuous_bumpTest n).comp (continuous_const.add (continuous_id.const_smul r)))

theorem sphBump_apply (n : ℕ) (z : Rd d) (r : ℝ) (y : Rd d) :
    sphBump n z r y = ∫ u, bumpTest n (z + r • u) y ∂(unitSphereProb d) := by
  change (exists_sphBump n z r).choose y = _
  rw [(exists_sphBump n z r).choose_spec.1 y,
    integral_unitSphereProb_eq_sphereMeasure (continuous_bumpTest_apply_affine n z r y)]
  rfl

/-- **Mollified sphere averages are pairings.** -/
theorem sphereAvgSeq_eq_apply_sphBump (h : DistRd d) (r : ℝ) (z : Rd d) (n : ℕ) :
    sphereAvgSeq h r z n = h (sphBump n z r) := by
  have := (exists_sphBump n z r).choose_spec.2 (h.comp (TestFunction.ofSupportedInCLM ℝ
    (subset_univ ((ballK z r : Set (Rd d))))))
  rw [sphereAvgSeq, integral_unitSphereProb_eq_sphereMeasure
    (continuous_apply_bumpTest_affine h n r z)]
  change h (TestFunction.ofSupportedIn (subset_univ _) (exists_sphBump n z r).choose) = _ at this
  rw [sphBump, this]
  rfl

theorem sphBump_nonneg (n : ℕ) (z : Rd d) (r : ℝ) (y : Rd d) : 0 ≤ sphBump n z r y := by
  rw [sphBump_apply]
  exact integral_nonneg fun u => bumpTest_nonneg n _ y

theorem tsupport_sphBump_subset (n : ℕ) (z : Rd d) (r : ℝ) :
    tsupport (⇑(sphBump n z r)) ⊆ closedBall z (|r| + 1) :=
  ((exists_sphBump n z r).choose).tsupport_subset

/-- Unit mass (`d ≥ 1`). -/
theorem integral_sphBump (hd : 1 ≤ d) (n : ℕ) (z : Rd d) (r : ℝ) :
    ∫ y, sphBump n z r y = 1 := by
  have h := sphereAvgSeq_eq_apply_sphBump (ofCont (ContinuousMap.const (Rd d) 1)) r z n
  rw [ofCont_const_apply, one_mul] at h
  rw [← h, sphereAvgSeq]
  simp only [ofCont_const_apply, one_mul, integral_bumpTest]
  exact integral_unitSphereProb_const hd 1

/-- `sphBump n z r - sphBump m w s`, the test function behind a difference of mollified sphere
averages. -/
def sphDiff (n : ℕ) (z : Rd d) (r : ℝ) (m : ℕ) (w : Rd d) (s : ℝ) : TestRd d :=
  sphBump n z r - sphBump m w s

theorem integral_sphDiff (hd : 1 ≤ d) (n : ℕ) (z : Rd d) (r : ℝ) (m : ℕ) (w : Rd d) (s : ℝ) :
    ∫ y, sphDiff n z r m w s y = 0 := by
  change ∫ y, (sphBump n z r y - sphBump m w s y) = 0
  rw [integral_sub (integrable_testOn _) (integrable_testOn _), integral_sphBump hd,
    integral_sphBump hd, sub_self]

/-- The difference of two mollified sphere averages is a pairing with a mean-zero test function. -/
theorem sphereAvgSeq_sub_eq_apply_sphDiff (h : DistRd d) (n : ℕ) (z : Rd d) (r : ℝ) (m : ℕ)
    (w : Rd d) (s : ℝ) :
    sphereAvgSeq h r z n - sphereAvgSeq h s w m = h (sphDiff n z r m w s) := by
  rw [sphereAvgSeq_eq_apply_sphBump, sphereAvgSeq_eq_apply_sphBump, sphDiff, map_sub]

/-- `sphDiff` as a mean-zero test function (`d ≥ 1`). -/
def sphDiff0 (hd : 1 ≤ d) (n : ℕ) (z : Rd d) (r : ℝ) (m : ℕ) (w : Rd d) (s : ℝ) : TestRd0 d :=
  ⟨sphDiff n z r m w s, integral_sphDiff hd n z r m w s⟩

/-! ### Locality of sphere averages -/

/-- `σ_{z,r} * ψ_n` is supported in the `2^{-n}`-neighbourhood of the sphere `∂B(z, |r|)`. -/
theorem support_sphBump_subset (n : ℕ) (z : Rd d) (r : ℝ) :
    support (⇑(sphBump n z r)) ⊆ thickening ((2 : ℝ) ^ n)⁻¹ (sphere z |r|) := by
  intro y hy
  by_contra hyt
  apply hy
  rw [sphBump_apply]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
  apply bumpTest_eq_zero
  have hmem : z + r • u ∈ sphere z |r| := by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs]
  rw [← dist_eq_norm]
  by_contra hlt
  exact hyt (mem_thickening_iff.2 ⟨_, hmem, not_le.1 hlt⟩)

theorem tsupport_sphBump_subset_cthickening (n : ℕ) (z : Rd d) (r : ℝ) :
    tsupport (⇑(sphBump n z r)) ⊆ cthickening ((2 : ℝ) ^ n)⁻¹ (sphere z |r|) :=
  (closure_mono (support_sphBump_subset n z r)).trans (closure_thickening_subset_cthickening _ _)

/-- If `U` is an open neighbourhood of the sphere `∂B(z, |r|)`, then `σ_{z,r} * ψ_n` is supported
in `U` for all large `n`. -/
theorem exists_tsupport_sphBump_subset {U : Opens (Rd d)} {r : ℝ} {z : Rd d}
    (hU : sphere z |r| ⊆ U) : ∃ N : ℕ, ∀ n, N ≤ n → tsupport (⇑(sphBump n z r)) ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_sphere z |r|).exists_cthickening_subset_open U.isOpen hU
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨N, fun n hn => (tsupport_sphBump_subset_cthickening n z r).trans
    ((cthickening_mono ?_ _).trans hδU)⟩
  rw [← inv_pow]
  exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans hN.le

/-- **Sphere averages are local.** If `U` is an open neighbourhood of the sphere `∂B(z, |r|)`,
then `h ↦ sphereAvg h r z` is a measurable function of `h|_U`. -/
theorem exists_measurable_sphereAvg_eq_restrictTo {U : Opens (Rd d)} {r : ℝ} {z : Rd d}
    (hU : sphere z |r| ⊆ U) :
    ∃ F : DistOn U → ℝ, Measurable F ∧ ∀ h : DistRd d, sphereAvg h r z = F (restrictTo U h) := by
  obtain ⟨N, hN⟩ := exists_tsupport_sphBump_subset hU
  let φ : ℕ → TestOn U := fun n =>
    testOnOf U (sphBump (n + N) z r) (hN (n + N) (Nat.le_add_left N n))
  refine ⟨fun k => limUnder atTop fun n => k (φ n), ?_, fun h => ?_⟩
  · have hn : ∀ n : ℕ, StronglyMeasurable fun k : DistOn U => k (φ n) :=
      fun n => (measurable_distOn_apply (φ n)).stronglyMeasurable
    exact (StronglyMeasurable.limUnder (l := atTop) hn).measurable
  · rw [sphereAvg_eq_limUnder, ← limUnder_comp_add_nat _ N]
    congr 1
    funext n
    rw [sphereAvgSeq_eq_apply_sphBump, restrictTo_testOnOf]

end HigherDimLQGMetric
