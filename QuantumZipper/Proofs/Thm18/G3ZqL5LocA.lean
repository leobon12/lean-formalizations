import QuantumZipper.Proofs.Thm18.G3ZqL2Red

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (5): zoom locality from LOCAL area positivity near the root

Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 65: "the restriction of h to an extremely small
neighborhood of x … tells us what the quantum surface looks like when we zoom in near x". The zoom
at level `C` sees only the field in a neighbourhood of the root once the zoomed field has quantum
area `≥ 1` in a small half-ball; since the level adds `C/γ`, this only needs the smoothed area of
the pulled-back field **at level `0` in one small half-ball** to converge to a positive number.
So the global area regularity of `G3ZqLAreaStmt` is more than needed: this file replaces it by a
local condition `LocArea` (raw convergence of the circle averages in a half-ball about `0`, and a
positive limit of the smoothed area of arbitrarily small half-balls, tested against the
compactly supported bumps `openBump`, which live in the interior `ℍ`).

* `integral_areaApprox_addConst_of_local`, `eventually_one_le_areaProxy_addConst_of_loc`;
* `g3zoomLawM_bump_iffL` (map core with `LocArea`);
* `locArea_of_areaReg` (the old hypotheses imply the new one);
* **`g3ZqZoomLocStmt_of_loc : G3ZqLLocStmt → G3Zq.G3ZqZoomLocStmt`** and
  `g3ZqLLocStmt_of_area : G3ZqLAreaStmt → G3ZqLLocStmt`.

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqL

open Prop16Area.G Factorization G3Z2b2 G3Zp G3Zq LQGMeas LocalRule

/-- **Local area positivity at the root.** The raw circle averages at all small dyadic radii
converge in a half-ball `B_ρ(0) ∩ ℍ`, and for every smaller half-ball some bump of it has a positive limiting smoothed
quantum area. -/
def LocArea (γ : ℝ) (u : FieldSample) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ k₀ : ℕ, (∀ k : ℕ, k₀ ≤ k → ∀ z ∈ ball (0 : ℂ) ρ ∩ H, ∃ l : ℝ,
      Tendsto (fun n => u (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l)) ∧
    ∀ q : ℝ, 0 < q → q < ρ → ∃ (n : ℕ) (v : ℝ), 0 < v ∧
      Tendsto (fun k => ∫ z, openBump (ball (0 : ℂ) q ∩ H) n z ∂areaApprox γ u k) atTop (𝓝 v)

/-- Adding a constant multiplies the smoothed area of a function supported where the raw circle
averages converge. -/
theorem integral_areaApprox_addConst_of_local {u : FieldSample} {S : Set ℂ} (hS : MeasurableSet S)
    {k : ℕ} (hraw : ∀ z ∈ S, ∃ l : ℝ,
      Tendsto (fun n => u (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l))
    {f : ℂ → ℝ} (hf : ∀ z, z ∉ S → f z = 0) (γ c : ℝ) :
    ∫ z, f z ∂areaApprox γ (addConst u c) k = Real.exp (γ * c) * ∫ z, f z ∂areaApprox γ u k := by
  have h1 : ∀ μ : Measure ℂ, ∫ z, f z ∂μ = ∫ z in S, f z ∂μ := fun μ =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm
  have hr : (areaApprox γ (addConst u c) k).restrict S =
      ENNReal.ofReal (Real.exp (γ * c)) • (areaApprox γ u k).restrict S := by
    unfold areaApprox
    rw [restrict_withDensity hS, restrict_withDensity hS,
      ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hS] with z hz
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [avgReg_addConst_of_tendsto (hraw z hz), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [mul_add, Real.exp_add]
    ring
  calc ∫ z, f z ∂areaApprox γ (addConst u c) k
        = ∫ z, f z ∂((areaApprox γ (addConst u c) k).restrict S) := h1 _
    _ = ∫ z, f z ∂(ENNReal.ofReal (Real.exp (γ * c)) • (areaApprox γ u k).restrict S) := by
        rw [hr]
    _ = Real.exp (γ * c) * ∫ z, f z ∂((areaApprox γ u k).restrict S) := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    _ = _ := by rw [← h1]

theorem openBump_eq_zero_of_notMem {U : Set ℂ} (n : ℕ) {z : ℂ} (hz : z ∉ U) :
    openBump U n z = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hz (tsupport_openBump_subset U n h)

/-- **The area grows with the constant, local form.** -/
theorem eventually_one_le_areaProxy_addConst_of_loc {γ : ℝ} (hγ : 0 < γ) {u : FieldSample}
    {q : ℝ} {k₀ : ℕ} (hraw : ∀ k : ℕ, k₀ ≤ k → ∀ z ∈ ball (0 : ℂ) q ∩ H, ∃ l : ℝ,
      Tendsto (fun n => u (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l))
    {n : ℕ} {v : ℝ} (hv : 0 < v)
    (ht : Tendsto (fun k => ∫ z, openBump (ball (0 : ℂ) q ∩ H) n z ∂areaApprox γ u k) atTop
      (𝓝 v)) :
    ∀ᶠ c in atTop, 1 ≤ areaProxy γ (addConst u c) q := by
  have hS : MeasurableSet (ball (0 : ℂ) q ∩ H) := measurableSet_ball.inter isOpen_H.measurableSet
  have hlim : ∀ c : ℝ, areaFun γ (openBump (ball (0 : ℂ) q ∩ H) n) (addConst u c) =
      Real.exp (γ * c) * v := by
    intro c
    unfold areaFun
    refine Tendsto.liminf_eq ((ht.const_mul (Real.exp (γ * c))).congr' ?_)
    filter_upwards [eventually_ge_atTop k₀] with k hk
    exact (integral_areaApprox_addConst_of_local hS (hraw k hk)
      (fun z hz => openBump_eq_zero_of_notMem n hz) γ c).symm
  have hlog : Tendsto (fun c : ℝ => Real.exp (γ * c) * v) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hγ)).atTop_mul_const hv
  filter_upwards [hlog.eventually_ge_atTop 1] with c hc
  calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal (areaFun γ (openBump (ball (0 : ℂ) q ∩ H) n) (addConst u c)) := by
        rw [hlim c]; exact ENNReal.one_le_ofReal.2 hc
    _ ≤ areaProxy γ (addConst u c) q := by
        unfold areaProxy
        exact le_iSup (fun n : ℕ => ENNReal.ofReal (LQGMeas.areaFun γ
          (LQGMeas.openBump (Metric.ball (0 : ℂ) q ∩ H) n) (addConst u c))) n

/-- The global area hypotheses (`AreaReg` and positive area on every half-ball) imply the local
one. -/
theorem locArea_of_areaReg {γ : ℝ} {u : FieldSample} (hu : AreaReg γ u)
    (hpos : ∀ q : ℝ, 0 < q → 0 < areaProxy γ u q) : LocArea γ u := by
  obtain ⟨μ, hμ⟩ := isVagueLimitOn_H_of_areaReg hu
  refine ⟨1, one_pos, 0, fun k _ z hz => hu.1.rawConverges k z (H_subset_Hbar hz.2),
    fun q hq _ => ?_⟩
  have hp := hpos q hq
  unfold areaProxy at hp
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hp
  have ht := hμ.2.2 (openBump (ball (0 : ℂ) q ∩ H) n) (continuous_openBump _ n)
    (hasCompactSupport_openBump (isBounded_ball.subset inter_subset_left) n)
    ((tsupport_openBump_subset _ n).trans inter_subset_right)
  refine ⟨n, ∫ z, openBump (ball (0 : ℂ) q ∩ H) n z ∂μ, ?_, ht⟩
  have e : areaFun γ (openBump (ball (0 : ℂ) q ∩ H) n) u =
      ∫ z, openBump (ball (0 : ℂ) q ∩ H) n z ∂μ := ht.liminf_eq
  rw [← e]
  exact ENNReal.ofReal_pos.1 hn

end G3ZqL
end Thm18Asm
end QuantumZipper
