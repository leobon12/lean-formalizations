import HigherDimLQGMetric.Field.Bump
import HigherDimLQGMetric.Frozen.SphereAvg
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Sphere averages: the basic (deterministic) layer

Packet F1. Port of LQGMetric's `lqg_metric/LQGMetric/Field/CircleAvgCont.lean` (`circleAvg` of a
continuous function is its classical circle average), `Field/CircleAvgGauss.lean` (`mollAvg`,
`circleAvg_eq_of_tendsto`, `circleAvg_addConst_of_tendsto`) and `Field/MeasurableAvg.lean`
(`measurable_circleAvg`) from circles in `ℂ` to spheres in `Rd d` (ruling M10), for the frozen
`sphereAvg h r z = limUnder atTop (n ↦ ∫ ⟨h, ψ_{n, z + r u}⟩ dσ(u))`.

* `unitSphereProb d` is a finite measure, a probability measure for `d ≥ 1`, carried by the unit
  sphere; continuous functions are integrable for it.
* `sphereAvgSeq h r z n` is the `n`-th mollified sphere average (the sequence inside `sphereAvg`);
  it is linear in `h`.
* `sphereAvg_ofCont`: for continuous `f`, `sphereAvg (ofCont f) r z = ∫ f(z + r u) dσ(u)` (the
  spherical mean), and the defining sequence converges (`tendsto_sphereAvgSeq_ofCont`).
* Additivity, wherever the defining limit of `h` exists (`sphereAvg_addFun_of_tendsto`,
  `sphereAvg_addConst_of_tendsto`, `sphereAvg_add_of_tendsto`); the limit for `h + f` exists iff
  the one for `h` does (`exists_tendsto_sphereAvgSeq_addFun_iff`).
* Affine maps: translation is exact for every distribution
  (`sphereAvg_affineComp_one : (h(· + z))_r(w) = h_r(w + z)`), and so is every dyadic rescaling
  (`sphereAvg_affineComp_two_zpow`, `r = 2^k`, `k ∈ ℤ`: the mollification scales `2^{-n}` are
  shifted by `k`); for continuous fields every `r > 0` works (`sphereAvg_affineComp_ofCont`).
  For a general distribution and a non-dyadic `r` the identity `(h(r·+z))_s(w) = h_{rs}(rw+z)`
  is false (the defining limit depends on the sequence of mollification scales); for the LGF it
  holds almost surely (packet F3).
* Measurability: `(h, r, z) ↦ sphereAvgSeq h r z n` and `(h, r, z) ↦ sphereAvg h r z` are jointly
  measurable (`measurable_sphereAvg`), and the convergence set is measurable
  (`measurableSet_exists_tendsto_sphereAvgSeq`).

Standard facts; own elementary proofs as in the 2D layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Function TopologicalSpace Filter Topology Metric
open scoped Distributions ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### The uniform probability measure on the unit sphere -/

theorem unitSphereProb_univ_le_one (d : ℕ) : unitSphereProb d univ ≤ 1 := by
  simp only [unitSphereProb, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ]
  set a := (volume : Measure (Rd d)).toSphere univ
  rcases eq_or_ne a 0 with ha | ha
  · rw [ha, mul_zero]; exact zero_le_one
  rcases eq_or_ne a ⊤ with ha' | ha'
  · rw [ha', ENNReal.inv_top, zero_mul]; exact zero_le_one
  · rw [ENNReal.inv_mul_cancel ha ha']

instance isFiniteMeasure_unitSphereProb (d : ℕ) : IsFiniteMeasure (unitSphereProb d) :=
  ⟨(unitSphereProb_univ_le_one d).trans_lt ENNReal.one_lt_top⟩

theorem isProbabilityMeasure_unitSphereProb (hd : 1 ≤ d) :
    IsProbabilityMeasure (unitSphereProb d) := by
  have : Nontrivial (Rd d) := by
    rw [← Module.finrank_pos_iff (R := ℝ), finrank_rd]; omega
  constructor
  simp only [unitSphereProb, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ]
  apply ENNReal.inv_mul_cancel
  · rw [Measure.toSphere_apply_univ, finrank_rd]
    exact mul_ne_zero (by simpa using (show d ≠ 0 by omega))
      (measure_ball_pos volume (0 : Rd d) one_pos).ne'
  · rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne

/-- `unitSphereProb d` is carried by the unit sphere. -/
theorem unitSphereProb_compl_sphere (d : ℕ) :
    unitSphereProb d (sphere (0 : Rd d) 1)ᶜ = 0 := by
  simp only [unitSphereProb, Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply measurable_subtype_coe isClosed_sphere.measurableSet.compl]
  have : (Subtype.val ⁻¹' (sphere (0 : Rd d) 1)ᶜ : Set (sphere (0 : Rd d) 1)) = ∅ := by
    ext u; simp
  rw [this, measure_empty, mul_zero]

theorem ae_unitSphereProb_mem_sphere (d : ℕ) :
    ∀ᵐ u ∂(unitSphereProb d), u ∈ sphere (0 : Rd d) 1 :=
  measure_eq_zero_iff_ae_notMem.1 (unitSphereProb_compl_sphere d) |>.mono fun _ hu => not_not.1 hu

theorem ae_unitSphereProb_norm_eq_one (d : ℕ) : ∀ᵐ u ∂(unitSphereProb d), ‖u‖ = 1 :=
  (ae_unitSphereProb_mem_sphere d).mono fun _ hu => mem_sphere_zero_iff_norm.1 hu

theorem restrict_sphere_unitSphereProb (d : ℕ) :
    (unitSphereProb d).restrict (sphere (0 : Rd d) 1) = unitSphereProb d :=
  Measure.restrict_eq_self_of_ae_mem (ae_unitSphereProb_mem_sphere d)

/-- Continuous functions are integrable for the sphere measure. -/
theorem integrable_unitSphereProb_of_continuous {E : Type*} [NormedAddCommGroup E]
    {g : Rd d → E} (hg : Continuous g) : Integrable g (unitSphereProb d) := by
  rw [← restrict_sphere_unitSphereProb d]
  exact hg.continuousOn.integrableOn_compact (isCompact_sphere _ _)

theorem integral_unitSphereProb_const (hd : 1 ≤ d) (c : ℝ) : ∫ _u, c ∂(unitSphereProb d) = c := by
  have := isProbabilityMeasure_unitSphereProb hd
  simp

/-! ### The mollified sphere averages -/

/-- `n`-th mollified sphere average `∫ ⟨h, ψ_{n, z + r u}⟩ dσ(u)`, the sequence whose limit
defines `sphereAvg h r z`. -/
def sphereAvgSeq (h : DistRd d) (r : ℝ) (z : Rd d) (n : ℕ) : ℝ :=
  ∫ u, h (bumpTest n (z + r • u)) ∂(unitSphereProb d)

theorem sphereAvg_eq_limUnder (h : DistRd d) (r : ℝ) (z : Rd d) :
    sphereAvg h r z = limUnder atTop (sphereAvgSeq h r z) := rfl

/-- `sphereAvg` is the limit wherever the mollified sphere averages converge. -/
theorem sphereAvg_eq_of_tendsto {h : DistRd d} {r : ℝ} {z : Rd d} {a : ℝ}
    (ha : Tendsto (sphereAvgSeq h r z) atTop (𝓝 a)) : sphereAvg h r z = a :=
  ha.limUnder_eq

theorem tendsto_sphereAvgSeq_sphereAvg {h : DistRd d} {r : ℝ} {z : Rd d}
    (ha : ∃ a, Tendsto (sphereAvgSeq h r z) atTop (𝓝 a)) :
    Tendsto (sphereAvgSeq h r z) atTop (𝓝 (sphereAvg h r z)) := by
  obtain ⟨a, ha⟩ := ha
  rwa [sphereAvg_eq_of_tendsto ha]

theorem continuous_apply_bumpTest_affine (h : DistRd d) (n : ℕ) (r : ℝ) (z : Rd d) :
    Continuous fun u : Rd d => h (bumpTest n (z + r • u)) :=
  (continuous_apply_bumpTest h n).comp (continuous_const.add (continuous_id.const_smul r))

theorem integrable_apply_bumpTest_sphere (h : DistRd d) (n : ℕ) (r : ℝ) (z : Rd d) :
    Integrable (fun u => h (bumpTest n (z + r • u))) (unitSphereProb d) :=
  integrable_unitSphereProb_of_continuous (continuous_apply_bumpTest_affine h n r z)

theorem sphereAvgSeq_add (h k : DistRd d) (r : ℝ) (z : Rd d) (n : ℕ) :
    sphereAvgSeq (h + k) r z n = sphereAvgSeq h r z n + sphereAvgSeq k r z n := by
  simp only [sphereAvgSeq, add_apply]
  exact integral_add (integrable_apply_bumpTest_sphere h n r z)
    (integrable_apply_bumpTest_sphere k n r z)

theorem sphereAvgSeq_neg (h : DistRd d) (r : ℝ) (z : Rd d) (n : ℕ) :
    sphereAvgSeq (-h) r z n = -sphereAvgSeq h r z n := by
  simp only [sphereAvgSeq, neg_apply]
  exact integral_neg _

theorem sphereAvgSeq_sub (h k : DistRd d) (r : ℝ) (z : Rd d) (n : ℕ) :
    sphereAvgSeq (h - k) r z n = sphereAvgSeq h r z n - sphereAvgSeq k r z n := by
  rw [sub_eq_add_neg, sphereAvgSeq_add, sphereAvgSeq_neg, sub_eq_add_neg]

theorem sphereAvgSeq_smul (c : ℝ) (h : DistRd d) (r : ℝ) (z : Rd d) (n : ℕ) :
    sphereAvgSeq (c • h) r z n = c * sphereAvgSeq h r z n := by
  simp only [sphereAvgSeq, smul_apply, smul_eq_mul]
  exact integral_const_mul _ _

@[simp]
theorem sphereAvgSeq_zero (r : ℝ) (z : Rd d) (n : ℕ) : sphereAvgSeq (0 : DistRd d) r z n = 0 := by
  simp [sphereAvgSeq]

/-! ### Continuous functions -/

/-- For continuous `f` the mollified sphere averages converge to the spherical mean
`∫ f(z + r u) dσ(u)`. -/
theorem tendsto_sphereAvgSeq_ofCont (f : C(Rd d, ℝ)) (r : ℝ) (z : Rd d) :
    Tendsto (sphereAvgSeq (ofCont f) r z) atTop
      (𝓝 (∫ u, f (z + r • u) ∂(unitSphereProb d))) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall z (|r| + 1)).exists_bound_of_continuousOn
    f.continuous.continuousOn
  have hM' : ∀ u ∈ sphere (0 : Rd d) 1, ∀ y ∈ closedBall (z + r • u) 1, |f y| ≤ M := by
    intro u hu y hy
    have := hM y ?_
    · simpa [Real.norm_eq_abs] using this
    rw [mem_closedBall] at hy ⊢
    have h2 : dist (z + r • u) z = |r| := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, mem_sphere_zero_iff_norm.1 hu, mul_one,
        Real.norm_eq_abs]
    linarith [dist_triangle y (z + r • u) z]
  refine tendsto_integral_of_dominated_convergence (fun _ => M)
    (fun n => (integrable_apply_bumpTest_sphere (ofCont f) n r z).aestronglyMeasurable)
    (integrable_const M) (fun n => ?_) ?_
  · filter_upwards [ae_unitSphereProb_mem_sphere d] with u hu
    rw [Real.norm_eq_abs]
    exact abs_ofCont_bumpTest_le f n (hM' u hu)
  · exact Eventually.of_forall fun u => tendsto_ofCont_bumpTest f (z + r • u)

/-- `sphereAvg` of a continuous function is its spherical mean. -/
theorem sphereAvg_ofCont (f : C(Rd d, ℝ)) (r : ℝ) (z : Rd d) :
    sphereAvg (ofCont f) r z = ∫ u, f (z + r • u) ∂(unitSphereProb d) :=
  sphereAvg_eq_of_tendsto (tendsto_sphereAvgSeq_ofCont f r z)

/-- `h_r(z)` of the constant field `c` is `c` (`d ≥ 1`). -/
theorem sphereAvg_const (hd : 1 ≤ d) (c r : ℝ) (z : Rd d) :
    sphereAvg (ofCont (ContinuousMap.const (Rd d) c)) r z = c := by
  rw [sphereAvg_ofCont]
  exact integral_unitSphereProb_const hd c

@[simp]
theorem sphereAvg_zero (r : ℝ) (z : Rd d) : sphereAvg (0 : DistRd d) r z = 0 := by
  rw [← ofCont_zero, sphereAvg_ofCont]
  simp

theorem sphereAvgSeq_addFun (h : DistRd d) (f : C(Rd d, ℝ)) (r : ℝ) (z : Rd d) (n : ℕ) :
    sphereAvgSeq (addFun h f) r z n = sphereAvgSeq h r z n + sphereAvgSeq (ofCont f) r z n :=
  sphereAvgSeq_add h (ofCont f) r z n

/-- The defining sequence of `h + f` converges to `a + (mean of f)` iff that of `h` converges
to `a`. -/
theorem tendsto_sphereAvgSeq_addFun_iff (h : DistRd d) (f : C(Rd d, ℝ)) (r : ℝ) (z : Rd d)
    (a : ℝ) :
    Tendsto (sphereAvgSeq (addFun h f) r z) atTop
        (𝓝 (a + ∫ u, f (z + r • u) ∂(unitSphereProb d))) ↔
      Tendsto (sphereAvgSeq h r z) atTop (𝓝 a) := by
  have hf := tendsto_sphereAvgSeq_ofCont f r z
  have e : sphereAvgSeq (addFun h f) r z = sphereAvgSeq h r z + sphereAvgSeq (ofCont f) r z :=
    funext fun n => sphereAvgSeq_addFun h f r z n
  rw [e]
  constructor
  · intro H
    have := H.sub hf
    simpa only [Pi.add_apply, add_sub_cancel_right] using this
  · intro H
    exact H.add hf

theorem exists_tendsto_sphereAvgSeq_addFun_iff (h : DistRd d) (f : C(Rd d, ℝ)) (r : ℝ)
    (z : Rd d) :
    (∃ a, Tendsto (sphereAvgSeq (addFun h f) r z) atTop (𝓝 a)) ↔
      ∃ a, Tendsto (sphereAvgSeq h r z) atTop (𝓝 a) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b - ∫ u, f (z + r • u) ∂(unitSphereProb d), ?_⟩
    rw [← tendsto_sphereAvgSeq_addFun_iff h f r z, sub_add_cancel]
    exact hb
  · rintro ⟨a, ha⟩
    exact ⟨_, (tendsto_sphereAvgSeq_addFun_iff h f r z a).2 ha⟩

/-- `(h + f)_r(z) = h_r(z) + (spherical mean of f)` wherever the defining limit of `h` exists. -/
theorem sphereAvg_addFun_of_tendsto {h : DistRd d} {r : ℝ} {z : Rd d} {a : ℝ}
    (ha : Tendsto (sphereAvgSeq h r z) atTop (𝓝 a)) (f : C(Rd d, ℝ)) :
    sphereAvg (addFun h f) r z = sphereAvg h r z + ∫ u, f (z + r • u) ∂(unitSphereProb d) := by
  rw [sphereAvg_eq_of_tendsto ha,
    sphereAvg_eq_of_tendsto ((tendsto_sphereAvgSeq_addFun_iff h f r z a).2 ha)]

theorem sphereAvgSeq_addConst (hd : 1 ≤ d) (h : DistRd d) (c r : ℝ) (z : Rd d) (n : ℕ) :
    sphereAvgSeq (addConst h c) r z n = sphereAvgSeq h r z n + c := by
  have := isProbabilityMeasure_unitSphereProb hd
  simp only [sphereAvgSeq, addConst_apply, integral_bumpTest, mul_one]
  rw [integral_add (integrable_apply_bumpTest_sphere h n r z) (integrable_const c)]
  simp

/-- `(h + c)_r(z) = h_r(z) + c` wherever the defining limit of `h` exists (`d ≥ 1`). -/
theorem sphereAvg_addConst_of_tendsto (hd : 1 ≤ d) {h : DistRd d} {r : ℝ} {z : Rd d} {a : ℝ}
    (ha : Tendsto (sphereAvgSeq h r z) atTop (𝓝 a)) (c : ℝ) :
    sphereAvg (addConst h c) r z = sphereAvg h r z + c := by
  rw [sphereAvg_eq_of_tendsto ha]
  apply sphereAvg_eq_of_tendsto
  have e : sphereAvgSeq (addConst h c) r z = fun n => sphereAvgSeq h r z n + c :=
    funext fun n => sphereAvgSeq_addConst hd h c r z n
  rw [e]
  exact ha.add_const c

theorem sphereAvg_add_of_tendsto {h k : DistRd d} {r : ℝ} {z : Rd d} {a b : ℝ}
    (ha : Tendsto (sphereAvgSeq h r z) atTop (𝓝 a))
    (hb : Tendsto (sphereAvgSeq k r z) atTop (𝓝 b)) :
    sphereAvg (h + k) r z = sphereAvg h r z + sphereAvg k r z := by
  rw [sphereAvg_eq_of_tendsto ha, sphereAvg_eq_of_tendsto hb]
  apply sphereAvg_eq_of_tendsto
  have e : sphereAvgSeq (h + k) r z = fun n => sphereAvgSeq h r z n + sphereAvgSeq k r z n :=
    funext fun n => sphereAvgSeq_add h k r z n
  rw [e]
  exact ha.add hb

theorem sphereAvg_smul_of_tendsto {h : DistRd d} {r : ℝ} {z : Rd d} {a : ℝ}
    (ha : Tendsto (sphereAvgSeq h r z) atTop (𝓝 a)) (c : ℝ) :
    sphereAvg (c • h) r z = c * sphereAvg h r z := by
  rw [sphereAvg_eq_of_tendsto ha]
  apply sphereAvg_eq_of_tendsto
  have e : sphereAvgSeq (c • h) r z = fun n => c * sphereAvgSeq h r z n :=
    funext fun n => sphereAvgSeq_smul c h r z n
  rw [e]
  exact ha.const_mul c

/-! ### Translations and dyadic rescalings -/

theorem sphereAvgSeq_affineComp_one (z : Rd d) (h : DistRd d) (r : ℝ) (w : Rd d) (n : ℕ) :
    sphereAvgSeq (affineComp 1 z h) r w n = sphereAvgSeq h r (w + z) n := by
  simp only [sphereAvgSeq, affineComp_one_apply, testAffinePull_one_bumpTest]
  congr 1
  funext u
  rw [add_right_comm]

/-- Translation: `(h(· + z))_r(w) = h_r(w + z)`, for every distribution `h`. -/
theorem sphereAvg_affineComp_one (z : Rd d) (h : DistRd d) (r : ℝ) (w : Rd d) :
    sphereAvg (affineComp 1 z h) r w = sphereAvg h r (w + z) := by
  rw [sphereAvg_eq_limUnder, sphereAvg_eq_limUnder]
  congr 1
  funext n
  exact sphereAvgSeq_affineComp_one z h r w n

theorem affineComp_apply_eq_apply_smul (r : ℝ) (z : Rd d) (h : DistRd d) (φ : TestRd d) :
    affineComp r z h φ = h ((r ^ d)⁻¹ • testAffinePull r z φ) := by
  rw [affineComp_apply, map_smul, smul_eq_mul]

theorem sphereAvgSeq_affineComp_two_pow (k : ℕ) (z : Rd d) (h : DistRd d) (r : ℝ) (w : Rd d)
    (n : ℕ) :
    sphereAvgSeq (affineComp ((2 : ℝ) ^ k) z h) r w (n + k) =
      sphereAvgSeq h ((2 : ℝ) ^ k * r) ((2 : ℝ) ^ k • w + z) n := by
  simp only [sphereAvgSeq, affineComp_apply_eq_apply_smul,
    smul_testAffinePull_two_pow_bumpTest]
  congr 1
  funext u
  rw [smul_add, smul_smul, add_right_comm]

theorem sphereAvgSeq_affineComp_two_pow_inv (k : ℕ) (z : Rd d) (h : DistRd d) (r : ℝ)
    (w : Rd d) (n : ℕ) :
    sphereAvgSeq (affineComp ((2 : ℝ) ^ k)⁻¹ z h) r w n =
      sphereAvgSeq h (((2 : ℝ) ^ k)⁻¹ * r) (((2 : ℝ) ^ k)⁻¹ • w + z) (n + k) := by
  simp only [sphereAvgSeq, affineComp_apply_eq_apply_smul,
    smul_testAffinePull_two_pow_inv_bumpTest]
  congr 1
  funext u
  rw [smul_add, smul_smul, add_right_comm]

theorem limUnder_comp_add_nat (s : ℕ → ℝ) (k : ℕ) :
    limUnder atTop (fun n => s (n + k)) = limUnder atTop s := by
  simp only [limUnder]
  congr 1
  rw [show (fun n => s (n + k)) = s ∘ (fun n => n + k) from rfl, ← Filter.map_map,
    Filter.map_add_atTop_eq_nat]

/-- Dyadic rescaling: `(h(2^k · + z))_r(w) = h_{2^k r}(2^k w + z)`, for every distribution `h`. -/
theorem sphereAvg_affineComp_two_pow (k : ℕ) (z : Rd d) (h : DistRd d) (r : ℝ) (w : Rd d) :
    sphereAvg (affineComp ((2 : ℝ) ^ k) z h) r w =
      sphereAvg h ((2 : ℝ) ^ k * r) ((2 : ℝ) ^ k • w + z) := by
  rw [sphereAvg_eq_limUnder, sphereAvg_eq_limUnder, ← limUnder_comp_add_nat _ k]
  congr 1
  funext n
  exact sphereAvgSeq_affineComp_two_pow k z h r w n

theorem sphereAvg_affineComp_two_pow_inv (k : ℕ) (z : Rd d) (h : DistRd d) (r : ℝ)
    (w : Rd d) :
    sphereAvg (affineComp ((2 : ℝ) ^ k)⁻¹ z h) r w =
      sphereAvg h (((2 : ℝ) ^ k)⁻¹ * r) (((2 : ℝ) ^ k)⁻¹ • w + z) := by
  rw [sphereAvg_eq_limUnder, sphereAvg_eq_limUnder,
    ← limUnder_comp_add_nat (sphereAvgSeq h _ _) k]
  congr 1
  funext n
  exact sphereAvgSeq_affineComp_two_pow_inv k z h r w n

/-- Dyadic rescaling for every `k ∈ ℤ`. -/
theorem sphereAvg_affineComp_two_zpow (k : ℤ) (z : Rd d) (h : DistRd d) (r : ℝ) (w : Rd d) :
    sphereAvg (affineComp ((2 : ℝ) ^ k) z h) r w =
      sphereAvg h ((2 : ℝ) ^ k * r) ((2 : ℝ) ^ k • w + z) := by
  rcases k with m | m
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact sphereAvg_affineComp_two_pow m z h r w
  · simp only [zpow_negSucc]
    exact sphereAvg_affineComp_two_pow_inv (m + 1) z h r w

/-- Convergence of the defining sequence is preserved by dyadic rescalings. -/
theorem tendsto_sphereAvgSeq_affineComp_two_pow_iff (k : ℕ) (z : Rd d) (h : DistRd d) (r : ℝ)
    (w : Rd d) (a : ℝ) :
    Tendsto (sphereAvgSeq (affineComp ((2 : ℝ) ^ k) z h) r w) atTop (𝓝 a) ↔
      Tendsto (sphereAvgSeq h ((2 : ℝ) ^ k * r) ((2 : ℝ) ^ k • w + z)) atTop (𝓝 a) := by
  rw [← tendsto_add_atTop_iff_nat k]
  simp only [sphereAvgSeq_affineComp_two_pow]

theorem tendsto_sphereAvgSeq_affineComp_one_iff (z : Rd d) (h : DistRd d) (r : ℝ) (w : Rd d)
    (a : ℝ) :
    Tendsto (sphereAvgSeq (affineComp 1 z h) r w) atTop (𝓝 a) ↔
      Tendsto (sphereAvgSeq h r (w + z)) atTop (𝓝 a) := by
  have e : sphereAvgSeq (affineComp 1 z h) r w = sphereAvgSeq h r (w + z) :=
    funext fun n => sphereAvgSeq_affineComp_one z h r w n
  rw [e]

/-- For a continuous field every rescaling `ρ > 0` works:
`(f(ρ · + z))_r(w) = f_{ρ r}(ρ w + z)`. -/
theorem sphereAvg_affineComp_ofCont {ρ : ℝ} (hρ : 0 < ρ) (z : Rd d) (f : C(Rd d, ℝ)) (r : ℝ)
    (w : Rd d) :
    sphereAvg (affineComp ρ z (ofCont f)) r w = sphereAvg (ofCont f) (ρ * r) (ρ • w + z) := by
  rw [affineComp_ofCont hρ, sphereAvg_ofCont, sphereAvg_ofCont]
  congr 1
  funext u
  simp only [ContinuousMap.comp_apply, affinePt_apply]
  rw [smul_add, smul_smul, add_right_comm]

/-! ### Measurability -/

theorem measurable_sphereAvgSeq (n : ℕ) :
    Measurable fun p : DistRd d × ℝ × Rd d => sphereAvgSeq p.1 p.2.1 p.2.2 n := by
  have h1 : Measurable fun q : (DistRd d × ℝ × Rd d) × Rd d => q.1.2.2 + q.1.2.1 • q.2 := by
    fun_prop
  have h2 : Measurable fun q : (DistRd d × ℝ × Rd d) × Rd d => q.1.1 := by fun_prop
  have hm : Measurable fun q : (DistRd d × ℝ × Rd d) × Rd d =>
      q.1.1 (bumpTest n (q.1.2.2 + q.1.2.1 • q.2)) :=
    (measurable_apply_bumpTest n).comp (h2.prodMk h1)
  have hs : StronglyMeasurable fun q : (DistRd d × ℝ × Rd d) × Rd d =>
      q.1.1 (bumpTest n (q.1.2.2 + q.1.2.1 • q.2)) := hm.stronglyMeasurable
  exact (hs.integral_prod_right' (ν := unitSphereProb d)).measurable

/-- `(h, r, z) ↦ h_r(z)` is jointly measurable. -/
theorem measurable_sphereAvg :
    Measurable fun p : DistRd d × ℝ × Rd d => sphereAvg p.1 p.2.1 p.2.2 := by
  have hn : ∀ n : ℕ, StronglyMeasurable fun p : DistRd d × ℝ × Rd d =>
      sphereAvgSeq p.1 p.2.1 p.2.2 n :=
    fun n => (measurable_sphereAvgSeq n).stronglyMeasurable
  exact (StronglyMeasurable.limUnder (l := atTop) hn).measurable

theorem measurable_sphereAvg_left (r : ℝ) (z : Rd d) :
    Measurable fun h : DistRd d => sphereAvg h r z :=
  measurable_sphereAvg.comp (f := fun h : DistRd d => (h, r, z))
    (measurable_id.prodMk (measurable_const (a := ((r, z) : ℝ × Rd d))))

theorem measurable_sphereAvgSeq_left (r : ℝ) (z : Rd d) (n : ℕ) :
    Measurable fun h : DistRd d => sphereAvgSeq h r z n :=
  (measurable_sphereAvgSeq n).comp (f := fun h : DistRd d => (h, r, z))
    (measurable_id.prodMk (measurable_const (a := ((r, z) : ℝ × Rd d))))

theorem Measurable.sphereAvg {α : Type*} [MeasurableSpace α] {h : α → DistRd d}
    (hh : Measurable h) (r : ℝ) (z : Rd d) : Measurable fun a => sphereAvg (h a) r z :=
  (measurable_sphereAvg_left r z).comp hh

/-- The set of distributions whose defining sequence converges at `(r, z)` is measurable. -/
theorem measurableSet_exists_tendsto_sphereAvgSeq (r : ℝ) (z : Rd d) :
    MeasurableSet {h : DistRd d | ∃ a, Tendsto (sphereAvgSeq h r z) atTop (𝓝 a)} :=
  measurableSet_exists_tendsto fun n => measurable_sphereAvgSeq_left r z n

end HigherDimLQGMetric
