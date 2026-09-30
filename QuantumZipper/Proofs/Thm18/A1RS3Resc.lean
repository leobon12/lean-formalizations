import QuantumZipper.Proofs.Thm18.A1RS2Wire

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (1): the rational Cauchy estimate through a rescaling (deterministic)

Toward `A1RSRatCauchyStmt` (A1RS2Wire.lean). The Theorem 1.8 field `Y` is the canonical rescaling
of the unscaled wedge field `Z = X + α₀(−log|·|) + G` (Sheffield arXiv:1012.4797, §1.6), and the
driver of `Y` is the Brownian rescaling of the driver `V` of `Z`. The rational Cauchy estimate is
available for `Z` (fixed-driver estimate `ae_smear_fixed_all` and `ratCauchy_Z_of_X`); it passes to
`Y` through the rescaling identity `Φ_Y(ρ, p) = Φ_Z(bρ, T p) + K`:

* `ratCauchy_of_rescale`: if `Φ_Z` satisfies the rational Cauchy estimate and (R2), `Φ_Y(0, ·)`
  satisfies (R3), and `Φ_Y(ρ, p) = Φ_Z(bρ, T p) + K` for `ρ ≥ 0` with `T` a homeomorphism of
  `smearU`, then `Φ_Y` satisfies the rational Cauchy estimate. (R3 for `Z` comes from the identity
  at `ρ = 0`; `tendstoLocallyUniformlyOn_of_ratCauchy` gives locally uniform convergence for `Z`,
  hence uniform convergence on the compact set `T(box)`.)
* `evalReg_eq_of_contData_rescale`: if `y` has the regularized averages of `rescale Z Q b` and the
  continuous-radius pairings of `Z` against `μ.map (b ·)` converge (`F1.ContData`), then
  `evalReg y μ = evalReg Z (μ.map (b ·)) + Q log b`.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

/-- **The rational Cauchy estimate through a rescaling.** -/
theorem ratCauchy_of_rescale {ΦZ Φy : ℝ → (Fin 4 → ℝ) → ℝ} {T S : (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {b K : ℝ} (hb : 0 < b) (hT : Continuous T) (hTU : MapsTo T smearU smearU)
    (hS : ContinuousOn S smearU) (hSU : MapsTo S smearU smearU)
    (hTS : ∀ p ∈ smearU, T (S p) = p)
    (hC : ∀ a c : Fin 4 → ℚ, GenUC.ratBox a c ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r →
      (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a c →
        |ΦZ r (ratPt q) - ΦZ 0 (ratPt q)| < 1 / ((n : ℝ) + 1))
    (hR2 : ContinuousOn (fun z : (Fin 4 → ℝ) × ℝ => ΦZ z.2 z.1) (smearU ×ˢ Ioi 0))
    (hR3 : ContinuousOn (Φy 0) smearU)
    (hid : ∀ ρ : ℝ, 0 ≤ ρ → ∀ p ∈ smearU, Φy ρ p = ΦZ (b * ρ) (T p) + K) :
    ∀ a c : Fin 4 → ℚ, GenUC.ratBox a c ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r →
      (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a c →
        |Φy r (ratPt q) - Φy 0 (ratPt q)| < 1 / ((n : ℝ) + 1) := by
  -- (R3) for `Z`
  have hE0 : ContinuousOn (ΦZ 0) smearU := by
    refine ((hR3.comp hS hSU).sub (continuousOn_const (c := K))).congr fun p hp => ?_
    have h := hid 0 le_rfl (S p) (hSU hp)
    rw [mul_zero, hTS p hp] at h
    show ΦZ 0 p = Φy 0 (S p) - K
    rw [h]
    ring
  have hLU := tendstoLocallyUniformlyOn_of_ratCauchy hC hR2 hE0
  intro a c hsub n
  set Kc : Set (Fin 4 → ℝ) := T '' GenUC.ratBox a c with hKc
  have hKcc : IsCompact Kc := (GenUC.isCompact_ratBox a c).image hT
  have hKcs : Kc ⊆ smearU := by rintro _ ⟨p, hp, rfl⟩; exact hTU (hsub hp)
  have hU := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_smearU).1 hLU Kc hKcs hKcc
  rw [Metric.tendstoUniformlyOn_iff] at hU
  have hev := hU (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨u, hu, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u / b from div_pos hu0 hb)
  refine ⟨N, fun r hr0 hrN q hq => ?_⟩
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hbr : b * (r : ℝ) ∈ Ioo (0 : ℝ) u := by
    refine ⟨mul_pos hb hr0', ?_⟩
    have h1 : (r : ℝ) < u / b := hrN.trans hN
    rw [lt_div_iff₀ hb] at h1
    linarith
  have hpU : ratPt q ∈ smearU := hsub hq
  have h := hIoo hbr (T (ratPt q)) ⟨ratPt q, hq, rfl⟩
  rw [dist_comm, Real.dist_eq] at h
  rw [hid r hr0'.le _ hpU, hid 0 le_rfl _ hpU, mul_zero]
  simpa using h

/-- **Regularized pairings of a rescaled field.** -/
theorem evalReg_eq_of_contData_rescale {y Z : FieldSample} (hZ : IsRegularSample Z) {Q b : ℝ}
    (hb : 0 < b) (hy : avgReg y = avgReg (rescale Z Q b)) {μ : Measure ℂ}
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ u ∂μ, u ∈ Hbar)
    (hC : F1.ContData Z (μ.map fun z => (b : ℂ) * z)) :
    evalReg y μ = evalReg Z (μ.map fun z => (b : ℂ) * z) + Q * Real.log b := by
  obtain ⟨FZ, hFZ⟩ := hZ
  have hZc := hFZ.congr_evalReg
  have hres := hZc.rescale' Q hb
  obtain ⟨hint, L, hL⟩ := hC
  have hm : Measurable fun z : ℂ => (b : ℂ) * z := measurable_const_mul _
  set ν := μ.map fun z => (b : ℂ) * z with hν
  have hνH : ∀ᵐ v ∂ν, v ∈ Hbar := by
    refine (ae_map_iff hm.aemeasurable isClosed_Hbar.measurableSet).2 (hμ.mono fun u hu => ?_)
    show 0 ≤ ((b : ℂ) * u).im
    rw [Complex.im_ofReal_mul]
    exact mul_nonneg hb.le hu
  have hEm : ∀ ρ : ℝ, Measurable fun v : ℂ => evalReg Z (foldedCircle v ρ) := fun ρ =>
    B3d.ZipLen.measurable_evalReg_fc Z ρ
  -- the dyadic pairings of `Z`
  have hZk : ∀ k : ℕ, ∫ v, avgReg Z k v ∂ν = ∫ v, evalReg Z (foldedCircle v (radius k)) ∂ν :=
    fun k => integral_congr_ae (hνH.mono fun v hv => hZc.avgReg_eq k hv)
  have hZt : Tendsto (fun k : ℕ => ∫ v, avgReg Z k v ∂ν) atTop (𝓝 L) :=
    (hL.comp RegClosure.tendsto_radius_nhdsGT).congr fun k => (hZk k).symm
  -- the dyadic pairings of `y`
  have hyk : ∀ k : ℕ, ∫ u, avgReg y k u ∂μ =
      (∫ v, evalReg Z (foldedCircle v (b * radius k)) ∂ν) + Q * Real.log b := by
    intro k
    have hσ : 0 < b * radius k := mul_pos hb (radius_pos k)
    have hi : Integrable (fun u => evalReg Z (foldedCircle ((b : ℂ) * u) (b * radius k))) μ :=
      (hint _ hσ).comp_measurable hm
    have e : ∫ u, avgReg (rescale Z Q b) k u ∂μ =
        ∫ u, (evalReg Z (foldedCircle ((b : ℂ) * u) (b * radius k)) + Q * Real.log b) ∂μ :=
      integral_congr_ae (hμ.mono fun u hu => hres.avgReg_eq k hu)
    rw [hν, integral_map hm.aemeasurable (hEm _).aestronglyMeasurable, hy, e,
      integral_add hi (integrable_const _), integral_const]
    simp
  have hyt : Tendsto (fun k : ℕ => ∫ u, avgReg y k u ∂μ) atTop (𝓝 (L + Q * Real.log b)) := by
    have hσk : Tendsto (fun k : ℕ => b * radius k) atTop (𝓝[>] 0) :=
      (F1.tendsto_mul_nhdsGT_zero hb).comp RegClosure.tendsto_radius_nhdsGT
    exact ((hL.comp hσk).add_const _).congr fun k => (hyk k).symm
  unfold evalReg
  rw [hyt.limUnder_eq, hZt.limUnder_eq]

end A1RS
end R18
end QuantumZipper
