import HigherDimLQGMetric.Sphere.Growth
import HigherDimLQGMetric.LGF.Density

/-!
# Mollified sphere measures as laws of `z + r U + ε V`

Packet F3 (Phase A, block A1). MA0 Details (a) D-F3; blueprint Lemma `lem:potential`.

With `U ∼ σ` (uniform on the unit sphere, `unitSphereProb d`) and `V ∼ ψ_{0,0} dz`
(`bumpLaw d`, the unit radial bump of radius `1`) independent:

* `sphLaw r z ε` is the law of `z + r U + ε V`; for `ε = 0` it is the uniform measure
  `sphMeas r z = σ_{r,z}` on `∂B(z, |r|)` (`sphLaw_zero`), and for `ε > 0` it has the density
  `σ_{r,z} * ψ_ε` (packet F3 `Sphere/Mol.lean`);
* it is a probability measure (`d ≥ 1`) carried by `B̄(0, ‖z‖ + |r| + |ε|)`, with HigherDimLFPP's
  linear growth bound at scale `r` and constant `2^d` (`growthBound_sphLaw`, `d ≥ 2`);
* two of them are coupled within `‖z - z'‖ + |r - r'| + |ε - ε'|` (same `U, V`,
  `coupledWithin_sphLaw`);
* hence (HigherDimLFPP's `transport_logCov_bound`, the source's Lemma 3.1 for the log kernel)
  `|logCov (sphLaw p₁) (sphLaw p₂) (sphLaw p₃) (sphLaw p₄)| ≤ C √(u v) / min(r₁, r₂)` with
  `u, v` the two coupling distances (`exists_abs_logCov_sphLaw_le`); this is the only analytic
  estimate behind the a.s. convergence, the covariances and the continuity of sphere averages.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### The base bump law -/

/-- The probability measure with density `ψ_{0,0} = bumpTest 0 0` (radius `1`). -/
def bumpLaw (d : ℕ) : Measure (Rd d) := posM (bumpTest 0 (0 : Rd d))

theorem exists_isBddSupp_bumpTest_zero :
    ∃ M : ℝ, IsBddSupp (fun y => bumpTest 0 (0 : Rd d) y) M 1 := by
  obtain ⟨M, D, hMD⟩ := exists_isBddSupp_testOn (bumpTest 0 (0 : Rd d))
  refine ⟨M, ⟨hMD.measurable, hMD.abs_le, fun y hy => bumpTest_eq_zero ?_⟩⟩
  rw [pow_zero, inv_one, sub_zero]
  exact hy.le

instance isProbabilityMeasure_bumpLaw : IsProbabilityMeasure (bumpLaw d) := by
  constructor
  rw [bumpLaw, posM_univ, ← ofReal_integral_eq_lintegral_ofReal (integrable_testOn _)
    (ae_of_all _ fun y => bumpTest_nonneg 0 0 y), integral_bumpTest, ENNReal.ofReal_one]

theorem ae_bumpLaw_norm_le : ∀ᵐ v ∂(bumpLaw d), ‖v‖ ≤ 1 := by
  obtain ⟨M, hM⟩ := exists_isBddSupp_bumpTest_zero (d := d)
  exact ae_posM_norm_le hM

/-! ### The laws `sphLaw` and `sphMeas` -/

/-- The law of `z + r U + ε V` (`U ∼ σ`, `V ∼ bumpLaw d` independent). -/
def sphLaw (r : ℝ) (z : Rd d) (ε : ℝ) : Measure (Rd d) :=
  ((unitSphereProb d).prod (bumpLaw d)).map fun p => z + r • p.1 + ε • p.2

/-- `σ_{r,z}`: the uniform probability measure on the sphere `∂B(z, |r|)` (`d ≥ 1`). -/
def sphMeas (r : ℝ) (z : Rd d) : Measure (Rd d) := (unitSphereProb d).map fun u => z + r • u

theorem measurable_sphLawFun (r : ℝ) (z : Rd d) (ε : ℝ) :
    Measurable fun p : Rd d × Rd d => z + r • p.1 + ε • p.2 := by fun_prop

instance isFiniteMeasure_sphLaw (r : ℝ) (z : Rd d) (ε : ℝ) : IsFiniteMeasure (sphLaw r z ε) := by
  unfold sphLaw; infer_instance

instance isFiniteMeasure_sphMeas (r : ℝ) (z : Rd d) : IsFiniteMeasure (sphMeas r z) := by
  unfold sphMeas; infer_instance

theorem isProbabilityMeasure_sphLaw (hd : 1 ≤ d) (r : ℝ) (z : Rd d) (ε : ℝ) :
    IsProbabilityMeasure (sphLaw r z ε) := by
  have := isProbabilityMeasure_unitSphereProb hd
  unfold sphLaw
  infer_instance

theorem isProbabilityMeasure_sphMeas (hd : 1 ≤ d) (r : ℝ) (z : Rd d) :
    IsProbabilityMeasure (sphMeas r z) := by
  have := isProbabilityMeasure_unitSphereProb hd
  unfold sphMeas
  infer_instance

/-- Almost surely `‖U‖ = 1` and `‖V‖ ≤ 1`. -/
theorem ae_prod_norm (d : ℕ) :
    ∀ᵐ p ∂((unitSphereProb d).prod (bumpLaw d)), ‖p.1‖ = 1 ∧ ‖p.2‖ ≤ 1 := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := unitSphereProb d)
    (ν := bumpLaw d)).ae (ae_unitSphereProb_norm_eq_one d)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := unitSphereProb d)
    (ν := bumpLaw d)).ae (ae_bumpLaw_norm_le (d := d))
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

theorem norm_sphLawFun_le {p : Rd d × Rd d} (hp : ‖p.1‖ = 1 ∧ ‖p.2‖ ≤ 1) (r : ℝ) (z : Rd d)
    (ε : ℝ) : ‖z + r • p.1 + ε • p.2‖ ≤ ‖z‖ + |r| + |ε| := by
  calc ‖z + r • p.1 + ε • p.2‖ ≤ ‖z‖ + ‖r • p.1‖ + ‖ε • p.2‖ := norm_add₃_le
    _ ≤ ‖z‖ + |r| + |ε| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hp.1, mul_one]
        have : |ε| * ‖p.2‖ ≤ |ε| := mul_le_of_le_one_right (abs_nonneg _) hp.2
        linarith

/-- `sphLaw r z ε` is carried by `B̄(0, ‖z‖ + |r| + |ε|)`. -/
theorem ae_sphLaw_norm_le (r : ℝ) (z : Rd d) (ε : ℝ) :
    ∀ᵐ x ∂(sphLaw r z ε), ‖x‖ ≤ ‖z‖ + |r| + |ε| := by
  unfold sphLaw
  rw [ae_map_iff (measurable_sphLawFun r z ε).aemeasurable
    (measurableSet_le measurable_norm measurable_const)]
  filter_upwards [ae_prod_norm d] with p hp
  exact norm_sphLawFun_le hp r z ε

/-- `sphLaw r z 0 = σ_{r,z}`. -/
theorem sphLaw_zero (r : ℝ) (z : Rd d) : sphLaw r z 0 = sphMeas r z := by
  unfold sphLaw sphMeas
  have e : (fun p : Rd d × Rd d => z + r • p.1 + (0 : ℝ) • p.2) =
      (fun u => z + r • u) ∘ Prod.fst := by
    funext p; simp
  rw [e, ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod, measure_univ,
    one_smul]

/-- The value of `sphLaw` on a measurable set (Tonelli). -/
theorem sphLaw_apply (r : ℝ) (z : Rd d) (ε : ℝ) {A : Set (Rd d)} (hA : MeasurableSet A) :
    sphLaw r z ε A = ∫⁻ v, unitSphereProb d {u | z + r • u + ε • v ∈ A} ∂(bumpLaw d) := by
  rw [sphLaw, Measure.map_apply (measurable_sphLawFun r z ε) hA,
    Measure.prod_apply_symm (measurable_sphLawFun r z ε hA)]
  rfl

theorem preimage_closedBall_subset {r : ℝ} (hr : 0 < r) (z x v : Rd d) (ε s : ℝ) :
    {u : Rd d | z + r • u + ε • v ∈ closedBall x s} ⊆
      closedBall (r⁻¹ • (x - z - ε • v)) (s / r) := by
  intro u hu
  simp only [mem_ofPred_eq, mem_closedBall, dist_eq_norm] at hu ⊢
  have e : u - r⁻¹ • (x - z - ε • v) = r⁻¹ • (z + r • u + ε • v - x) := by
    rw [smul_sub r⁻¹ (z + r • u + ε • v) x, smul_add, smul_add, smul_smul, inv_mul_cancel₀ hr.ne',
      one_smul, smul_sub, smul_sub]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hu (inv_nonneg.2 hr.le)

/-- **Growth bound** of `sphLaw r z ε` at scale `r` (`d ≥ 2`, `r > 0`). -/
theorem growthBound_sphLaw (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) (z : Rd d) (ε : ℝ) :
    HigherDimLFPP.GrowthBound (sphLaw r z ε) (2 ^ d) r := by
  intro x s hs
  have := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  have hb : ∀ v : Rd d, unitSphereProb d {u | z + r • u + ε • v ∈ closedBall x s} ≤
      ENNReal.ofReal (2 ^ d * min 1 (s / r)) := by
    intro v
    calc unitSphereProb d {u | z + r • u + ε • v ∈ closedBall x s}
        ≤ unitSphereProb d (closedBall (r⁻¹ • (x - z - ε • v)) (s / r)) :=
          measure_mono (preimage_closedBall_subset hr z x v ε s)
      _ = ENNReal.ofReal ((unitSphereProb d).real (closedBall (r⁻¹ • (x - z - ε • v)) (s / r))) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (2 ^ d * min 1 (s / r)) :=
          ENNReal.ofReal_le_ofReal (unitSphereProb_closedBall_le hd _ (div_pos hs hr))
  have hle : sphLaw r z ε (closedBall x s) ≤ ENNReal.ofReal (2 ^ d * min 1 (s / r)) := by
    rw [sphLaw_apply r z ε measurableSet_closedBall]
    calc ∫⁻ v, unitSphereProb d {u | z + r • u + ε • v ∈ closedBall x s} ∂(bumpLaw d)
        ≤ ∫⁻ _v, ENNReal.ofReal (2 ^ d * min 1 (s / r)) ∂(bumpLaw d) := lintegral_mono hb
      _ = ENNReal.ofReal (2 ^ d * min 1 (s / r)) := by
          rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (by positivity) (le_min zero_le_one (div_nonneg hs.le hr.le))) hle

/-- A growth bound at scale `R` is one at every smaller scale. -/
theorem growthBound_mono_scale {μ : Measure (Rd d)} {B R R' : ℝ}
    (h : HigherDimLFPP.GrowthBound μ B R) (hB : 0 ≤ B) (hR' : 0 < R') (hRR : R' ≤ R) :
    HigherDimLFPP.GrowthBound μ B R' := by
  intro z t ht
  refine (h z t ht).trans (mul_le_mul_of_nonneg_left (min_le_min le_rfl ?_) hB)
  exact div_le_div_of_nonneg_left ht.le hR' hRR

/-- **Coupling**: `sphLaw r z ε` and `sphLaw r' z' ε'` are coupled within
`‖z - z'‖ + |r - r'| + |ε - ε'|` (same `U` and `V`). -/
theorem coupledWithin_sphLaw (r : ℝ) (z : Rd d) (ε r' : ℝ) (z' : Rd d) (ε' : ℝ) :
    HigherDimLFPP.CoupledWithin (sphLaw r z ε) (sphLaw r' z' ε')
      (‖z - z'‖ + |r - r'| + |ε - ε'|) := by
  set F : Rd d × Rd d → Rd d × Rd d := fun p => (z + r • p.1 + ε • p.2, z' + r' • p.1 + ε' • p.2)
    with hF
  have hFm : Measurable F := by fun_prop
  refine ⟨((unitSphereProb d).prod (bumpLaw d)).map F, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hFm]; rfl
  · rw [Measure.map_map measurable_snd hFm]; rfl
  · rw [ae_map_iff hFm.aemeasurable (measurableSet_le (by fun_prop) measurable_const)]
    filter_upwards [ae_prod_norm d] with p hp
    simp only [hF]
    have e : z + r • p.1 + ε • p.2 - (z' + r' • p.1 + ε' • p.2) =
        (z - z') + (r - r') • p.1 + (ε - ε') • p.2 := by
      rw [sub_smul, sub_smul]; abel
    rw [e]
    calc ‖(z - z') + (r - r') • p.1 + (ε - ε') • p.2‖ ≤ ‖z - z'‖ + |r - r'| + |ε - ε'| :=
          norm_sphLawFun_le hp _ _ _

/-- `LogPairable` for four `sphLaw`s (`d ≥ 2`, positive radii). -/
theorem logPairable_sphLaw (hd : 2 ≤ d) {r₁ r₂ r₃ r₄ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h₃ : 0 < r₃) (h₄ : 0 < r₄) (z₁ z₂ z₃ z₄ : Rd d) (ε₁ ε₂ ε₃ ε₄ : ℝ) :
    HigherDimLFPP.LogPairable (sphLaw r₁ z₁ ε₁) (sphLaw r₂ z₂ ε₂) (sphLaw r₃ z₃ ε₃)
      (sphLaw r₄ z₄ ε₄) := by
  set D := (‖z₁‖ + |r₁| + |ε₁|) + (‖z₂‖ + |r₂| + |ε₂|) + (‖z₃‖ + |r₃| + |ε₃|) +
    (‖z₄‖ + |r₄| + |ε₄|) with hD
  have hsupp : ∀ (r : ℝ) (z : Rd d) (ε : ℝ), ‖z‖ + |r| + |ε| ≤ D →
      ∀ᵐ x ∂(sphLaw r z ε), ‖x‖ ≤ D := fun r z ε hle => by
    filter_upwards [ae_sphLaw_norm_le r z ε] with x hx
    exact hx.trans hle
  have n₁ : 0 ≤ ‖z₁‖ + |r₁| + |ε₁| := by positivity
  have n₂ : 0 ≤ ‖z₂‖ + |r₂| + |ε₂| := by positivity
  have n₃ : 0 ≤ ‖z₃‖ + |r₃| + |ε₃| := by positivity
  have n₄ : 0 ≤ ‖z₄‖ + |r₄| + |ε₄| := by positivity
  have hB : (0 : ℝ) ≤ 2 ^ d := by positivity
  set R := min r₁ r₂
  set ρ := min r₃ r₄
  exact HigherDimLFPP.logPairable_of_growthBound (B := 2 ^ d) (R := R) (r := ρ) (D := D)
    (lt_min h₁ h₂) (lt_min h₃ h₄)
    (growthBound_mono_scale (growthBound_sphLaw hd h₁ z₁ ε₁) hB (lt_min h₁ h₂) (min_le_left _ _))
    (growthBound_mono_scale (growthBound_sphLaw hd h₂ z₂ ε₂) hB (lt_min h₁ h₂) (min_le_right _ _))
    (growthBound_mono_scale (growthBound_sphLaw hd h₃ z₃ ε₃) hB (lt_min h₃ h₄) (min_le_left _ _))
    (growthBound_mono_scale (growthBound_sphLaw hd h₄ z₄ ε₄) hB (lt_min h₃ h₄) (min_le_right _ _))
    (hsupp _ _ _ (by linarith)) (hsupp _ _ _ (by linarith)) (hsupp _ _ _ (by linarith))
    (hsupp _ _ _ (by linarith))

/-- **The transport bound for mollified sphere laws** (`d ≥ 2`): there is `C = C(d)` such that
`|logCov (sphLaw r₁ z₁ ε₁) (sphLaw r₂ z₂ ε₂) (sphLaw r₃ z₃ ε₃) (sphLaw r₄ z₄ ε₄)| ≤
C √(u v) / min(r₁, r₂)` with `u = ‖z₁ - z₂‖ + |r₁ - r₂| + |ε₁ - ε₂|` and
`v = ‖z₃ - z₄‖ + |r₃ - r₄| + |ε₃ - ε₄|`. -/
theorem exists_abs_logCov_sphLaw_le (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r₁ r₂ r₃ r₄ : ℝ), 0 < r₁ → 0 < r₂ → 0 < r₃ → 0 < r₄ →
      ∀ (z₁ z₂ z₃ z₄ : Rd d) (ε₁ ε₂ ε₃ ε₄ : ℝ),
        |HigherDimLFPP.logCov (sphLaw r₁ z₁ ε₁) (sphLaw r₂ z₂ ε₂) (sphLaw r₃ z₃ ε₃)
            (sphLaw r₄ z₄ ε₄)| ≤
          C * Real.sqrt ((‖z₁ - z₂‖ + |r₁ - r₂| + |ε₁ - ε₂|) *
            (‖z₃ - z₄‖ + |r₃ - r₄| + |ε₃ - ε₄|)) / min r₁ r₂ := by
  obtain ⟨C, hC0, hC⟩ := HigherDimLFPP.transport_logCov_bound d (2 ^ d)
  refine ⟨C, hC0, fun r₁ r₂ r₃ r₄ h₁ h₂ h₃ h₄ z₁ z₂ z₃ z₄ ε₁ ε₂ ε₃ ε₄ => ?_⟩
  have := isProbabilityMeasure_sphLaw (show 1 ≤ d by omega) r₁ z₁ ε₁
  have := isProbabilityMeasure_sphLaw (show 1 ≤ d by omega) r₂ z₂ ε₂
  have := isProbabilityMeasure_sphLaw (show 1 ≤ d by omega) r₃ z₃ ε₃
  have := isProbabilityMeasure_sphLaw (show 1 ≤ d by omega) r₄ z₄ ε₄
  have hB : (0 : ℝ) ≤ 2 ^ d := by positivity
  exact hC _ _ _ _ (min r₁ r₂) (min r₃ r₄) _ _ (lt_min h₁ h₂) (lt_min h₃ h₄) (by positivity)
    (by positivity)
    (growthBound_mono_scale (growthBound_sphLaw hd h₁ z₁ ε₁) hB (lt_min h₁ h₂) (min_le_left _ _))
    (growthBound_mono_scale (growthBound_sphLaw hd h₂ z₂ ε₂) hB (lt_min h₁ h₂) (min_le_right _ _))
    (growthBound_mono_scale (growthBound_sphLaw hd h₃ z₃ ε₃) hB (lt_min h₃ h₄) (min_le_left _ _))
    (growthBound_mono_scale (growthBound_sphLaw hd h₄ z₄ ε₄) hB (lt_min h₃ h₄) (min_le_right _ _))
    (coupledWithin_sphLaw _ _ _ _ _ _) (coupledWithin_sphLaw _ _ _ _ _ _)
    (logPairable_sphLaw hd h₁ h₂ h₃ h₄ _ _ _ _ _ _ _ _)

end HigherDimLQGMetric
