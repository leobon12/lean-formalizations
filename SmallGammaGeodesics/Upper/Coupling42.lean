import SmallGammaGeodesics.Upper.Coupling42Diffeo
import SmallGammaGeodesics.Upper.Coupling42Sup
import SmallGammaGeodesics.Upper.Coupling42Pairing
import LQGMetric.Field.GFFInvariance

/-!
# Lemma 4.2′ (the probe coupling) from the near-identity coupling (blueprint `lem:coupling`)

`lemma42_of_NIC : CC.NICInput → Lemma42` (packet P-G3, rulings G20, G24). For `|θ| ≤ ε₀ ℓ_j`:

1. **Steps 1–2** (`Coupling42Diffeo`): the global extension `Φ = id + c_j · iθH_{j,a}` of the probe
   map is a near-identity diffeomorphism with `‖DΦ − I‖ ≤ η = C₃|θ|/ℓ_j ≤ 1/48`, whose inverse `Ψ`
   is holomorphic on `U_j` (`isNearIdDiffeo_extMap`).
2. **Step 3**: `CC.NICInput` applied to `(Φ, Ψ, U_j, η)` gives `(h, h̄', K')` with
   `⟨h, τg⟩ = ⟨h̄', g⟩ + ∫ K' g` for `g` supported in `U_j`. Put `h̄ = h̄' + K'(1/2)` (a measurable
   random constant, `IsWholePlaneGFF.addConst`) and `K = K' − K'(1/2)`. The pullback of (b3) is the
   NIC transport (`transport_eq_of_probe`), which gives (b2) and (b3).
3. **Steps 4–5** (`Coupling42Sup.sup_bound`): (b4), with `B = C_NIC η²`.
4. **Step 6** (`Coupling42Pairing.ae_measPairing_eq`): (b5), using `probeInv = Ψ` on `[0,1]`
   (`probeInv_eq_extInv`).

The constants: `ε₀ = min(ε₁, ε_NIC/(C₃ + 1))` and `C_K = C₃ √(10⁵ C_NIC) + 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace SmallGammaGeodesics

namespace Coupling42

open LQGMetric GaussianLQG.Realization

theorem isOpen_probeRectU (j : ℕ) : IsOpen (probeRectU j) := by
  have h1 : IsOpen {z : ℂ | z.re ∈ Ioo (-1 / 4 : ℝ) (5 / 4)} :=
    isOpen_Ioo.preimage Complex.continuous_re
  have h2 : IsOpen {z : ℂ | |z.im| < ell j / 4} :=
    isOpen_lt Complex.continuous_im.abs continuous_const
  exact h1.inter h2

/-- a function continuous on an open `U` times a test function supported in `U` is continuous -/
theorem continuous_mul_of_tsupport {K : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hK : ContinuousOn K U) {f : TestC} (hf : tsupport (f : ℂ → ℝ) ⊆ U) :
    Continuous fun y => K y * f y := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ U
  · exact (hK.continuousAt (hU.mem_nhds hy)).mul f.continuous.continuousAt
  · have hev : (f : ℂ → ℝ) =ᶠ[𝓝 y] fun _ => 0 :=
      notMem_tsupport_iff_eventuallyEq.mp fun h => hy (hf h)
    have hev' : (fun y => K y * f y) =ᶠ[𝓝 y] fun _ => 0 :=
      hev.mono fun x hx => by simp only at hx ⊢; rw [hx, mul_zero]
    exact continuousAt_const.congr hev'.symm

theorem integrable_mul_of_tsupport {K : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hK : ContinuousOn K U) {f : TestC} (hf : tsupport (f : ℂ → ℝ) ⊆ U) :
    Integrable fun y => K y * f y :=
  (continuous_mul_of_tsupport hU hK hf).integrable_of_hasCompactSupport
    f.hasCompactSupport.mul_left

/-- `∫ (K − c) f = ∫ K f − c ∫ f` for `f` supported in `U` -/
theorem integral_sub_const_mul {K : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hK : ContinuousOn K U)
    {f : TestC} (hf : tsupport (f : ℂ → ℝ) ⊆ U) (c : ℝ) :
    ∫ y, (K y - c) * f y = (∫ y, K y * f y) - c * ∫ y, f y := by
  have hfi : Integrable (f : ℂ → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  rw [← integral_const_mul, ← integral_sub (integrable_mul_of_tsupport hU hK hf)
    (hfi.const_mul c)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem rectN_subset_probeRectU {j : ℕ} {r : ℝ} (hrℓ : r < ell j / 4) :
    rectN r ⊆ probeRectU j := by
  intro z hz
  rw [mem_rectN] at hz
  have hℓ1 := ell_le_one j
  refine ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, ?_⟩
  rw [abs_lt]
  constructor <;> linarith [hz.2.1, hz.2.2]

/-- the threshold `ε₀ = min(ε₁, ε_NIC/(C₃ + 1))` -/
def eps0 (εN : ℝ) : ℝ := min eps1 (εN / (C3 + 1))

/-- the constant `C_K = C₃ √(10⁵ C_NIC) + 1` -/
def CKc (CN : ℝ) : ℝ := C3 * Real.sqrt (100000 * CN) + 1

end Coupling42

open Coupling42 LQGMetric

/-- **Lemma 4.2′** (blueprint `lem:coupling`) from the near-identity coupling `CC.NICInput`
(packet P-G3, ruling G20). -/
theorem lemma42_of_NIC (hNIC : CC.NICInput) : Lemma42 := by
  obtain ⟨εN, CN, hεN, hCN, hNIC'⟩ := hNIC
  have hC3 := C3_nonneg
  have hε₀ : 0 < eps0 εN := lt_min eps1_pos (by positivity)
  have hCK : 0 < CKc CN := by unfold CKc; positivity
  refine ⟨eps0 εN, CKc CN, hε₀, hCK, fun j a θ _ha hθ => ?_⟩
  have hℓ := ell_pos j
  have hθ1 : |θ| ≤ eps1 * ell j :=
    hθ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hℓ.le)
  set η : ℝ := C3 * |θ| / ell j with hη
  have hη0 : 0 ≤ η := eta_nonneg
  have hη48 : η ≤ 1 / 48 := eta_le hθ1
  have hη32 : η ≤ 1 / 32 := hη48.trans (by norm_num)
  have hηN : η ≤ εN := by
    have h1 : |θ| / ell j ≤ εN / (C3 + 1) := by
      rw [div_le_iff₀ hℓ]
      exact hθ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hℓ.le)
    have h2 : η = C3 * (|θ| / ell j) := by rw [hη]; ring
    rw [h2]
    calc C3 * (|θ| / ell j) ≤ (C3 + 1) * (εN / (C3 + 1)) :=
          mul_le_mul (by linarith) h1 (by positivity) (by linarith)
      _ = εN := by field_simp
  have hDiff := isNearIdDiffeo_extMap (a := a) hθ1
  obtain ⟨Ω, mΩ, P, hP, h, hbar', K', hh, hhb', hKm, hKharm, hKG, hK0, hcoupN, hincN⟩ :=
    hNIC' (extMap j a θ) (extInv j a θ) (probeRectU j) η (isOpen_probeRectU j) hη0 hηN hDiff
  -- the normalization `K(1/2) = 0`
  set c : Ω → ℝ := fun ω => K' ω (1 / 2) with hcdef
  have hc : Measurable c := hKm.comp (measurable_id.prodMk measurable_const)
  set K : Ω → ℂ → ℝ := fun ω z => K' ω z - c ω with hKdef
  set hbar : Ω → DistC := fun ω => addConst (hbar' ω) (c ω) with hbardef
  have hhb : IsWholePlaneGFF hbar P := hhb'.addConst hc
  have hKcont : ∀ ω, ContinuousOn (K ω) (probeRectU j) := fun ω =>
    ((hKharm ω).sub (InnerProductSpace.harmonicOnNhd_const (c ω))).continuousOn
  have hK'cont : ∀ ω, ContinuousOn (K' ω) (probeRectU j) := fun ω => (hKharm ω).continuousOn
  have hKmeas : Measurable fun p : Ω × ℂ => K p.1 p.2 :=
    hKm.sub (hKm.comp (measurable_fst.prodMk measurable_const))
  have hKG' : IsGaussianProcess
      (fun (p : probeRectU j × probeRectU j) (ω : Ω) => K ω p.1 - K ω p.2) P := by
    have e : (fun (p : probeRectU j × probeRectU j) (ω : Ω) => K ω p.1 - K ω p.2) =
        fun (p : probeRectU j × probeRectU j) (ω : Ω) => K' ω p.1 - K' ω p.2 := by
      funext p ω; simp only [hKdef]; ring
    rw [e]; exact hKG
  have hK0' : ∀ p : probeRectU j × probeRectU j, ∫ ω, (K ω p.1 - K ω p.2) ∂P = 0 := by
    intro p
    have e : (fun ω => K ω p.1 - K ω p.2) = fun ω => K' ω p.1 - K' ω p.2 := by
      funext ω; simp only [hKdef]; ring
    rw [e]; exact hK0 p
  have hinc : ∀ z w : ℂ, ∀ s : ℝ, 0 < s → closedBall z s ⊆ probeRectU j →
      closedBall w s ⊆ probeRectU j →
        ∫ ω, (K ω z - K ω w) ^ 2 ∂P ≤
          (CN * η ^ 2) * min (‖z - w‖ / s) (1 + Real.log (1 + ‖z - w‖ / s)) := by
    intro z w s hs hz hw
    have e : (fun ω => (K ω z - K ω w) ^ 2) = fun ω => (K' ω z - K' ω w) ^ 2 := by
      funext ω; simp only [hKdef]; ring
    rw [e]
    exact hincN z w s hs hz hw
  have hKhalf : ∀ ω, K ω (1 / 2) = 0 := fun ω => by simp only [hKdef, hcdef, sub_self]
  obtain ⟨hsupm, hsupb⟩ := sup_bound (P := P) (B := CN * η ^ 2) (by positivity) hKmeas hKcont
    hKG' hK0' hKhalf hinc
  -- the near-identity pair of NIC's transport
  set D : NIC.NearIdPair := NIC.NearIdPair.ofDiffeo hDiff hη0 hη32 with hDdef
  have hDΨ : D.Ψ = extInv j a θ := rfl
  have hDlip : PsiLip D :=
    ⟨fun w w' => norm_extInv_sub_le_two hθ1 w w', fun w w' => norm_sub_le_two_extInv hθ1 w w'⟩
  refine ⟨Ω, mΩ, P, hP, h, hbar, K, hh, hhb, hKmeas, fun ω => (hKharm ω).sub
    (InnerProductSpace.harmonicOnNhd_const (c ω)), hKhalf, ?_, hsupm, ?_, ?_⟩
  · -- (b3)
    filter_upwards [hcoupN] with ω hω f g hf hg hg'
    have hτ := transport_eq_of_probe hθ1 hf hg hg'
    rw [hω f g hf hτ, hbardef]
    simp only
    rw [GFFInv.addConst_apply, hKdef]
    simp only
    rw [integral_sub_const_mul (isOpen_probeRectU j) (hK'cont ω) hf (c ω)]
    ring
  · -- (b4)
    refine hsupb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hL := one_le_Lj j
    unfold Lj
    have hsq : (Real.sqrt (100000 * CN)) ^ 2 = 100000 * CN := Real.sq_sqrt (by positivity)
    have hCKge : C3 * Real.sqrt (100000 * CN) ≤ CKc CN := by unfold CKc; linarith
    have hprod : 0 ≤ (|θ| / ell j) * (1 + Real.log (1 / ell j)) := by
      have := log_one_div_ell_nonneg j
      positivity
    have hηe : η = C3 * (|θ| / ell j) := by rw [hη]; ring
    have key : 100000 * (CN * η ^ 2) * (1 + Real.log (1 / ell j)) ^ 2 =
        (C3 * Real.sqrt (100000 * CN) * ((|θ| / ell j) * (1 + Real.log (1 / ell j)))) ^ 2 := by
      have e : (C3 * Real.sqrt (100000 * CN) * ((|θ| / ell j) * (1 + Real.log (1 / ell j)))) ^ 2 =
          C3 ^ 2 * Real.sqrt (100000 * CN) ^ 2 * (|θ| / ell j) ^ 2 *
            (1 + Real.log (1 / ell j)) ^ 2 := by ring
      rw [e, hsq, hηe]
      ring
    rw [key]
    have h0 : 0 ≤ C3 * Real.sqrt (100000 * CN) * ((|θ| / ell j) * (1 + Real.log (1 / ell j))) := by
      positivity
    calc (C3 * Real.sqrt (100000 * CN) * ((|θ| / ell j) * (1 + Real.log (1 / ell j)))) ^ 2
        ≤ (CKc CN * ((|θ| / ell j) * (1 + Real.log (1 / ell j)))) ^ 2 :=
          pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_right hCKge hprod) 2
      _ = (CKc CN * (|θ| / ell j) * (1 + Real.log (1 / ell j))) ^ 2 := by ring
  · -- (b5)
    have hr : (0 : ℝ) < ell j / 8 := by positivity
    have hrU : rectN (ell j / 8) ⊆ probeRectU j := rectN_subset_probeRectU (by linarith)
    have hcoup : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        h ω (D.transport (segBump n)) = hbar ω (segBump n) + ∫ y, K ω y * segBump n y := by
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < ell j / 4)
        (by norm_num : (2 : ℝ)⁻¹ < 1)
      filter_upwards [hcoupN] with ω hω
      filter_upwards [eventually_ge_atTop N] with n hn
      have hsmall : (2 : ℝ)⁻¹ ^ n < ell j / 4 :=
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans_lt hN
      have hsupp : tsupport (segBump n : ℂ → ℝ) ⊆ probeRectU j :=
        (tsupport_segBump n).trans (rectN_subset_probeRectU hsmall)
      have h1 := hω (segBump n) (D.transport (segBump n)) hsupp
        (fun x => NIC.NearIdPair.ofDiffeo_transport_apply hDiff hη0 hη32 (segBump n) x)
      rw [h1, hbardef]
      simp only
      rw [GFFInv.addConst_apply, integral_bumpPath, one_mul, hKdef]
      simp only
      rw [integral_sub_const_mul (isOpen_probeRectU j) (hK'cont ω) hsupp (c ω),
        integral_bumpPath]
      ring
    have hmain := ae_measPairing_eq hDlip hh hhb hr (fun ω => (hKcont ω).mono hrU) hcoup
    -- `λ.map probeInv = Ψ_*λ`
    have hmapeq : (GaussianLQG.segMeasure 0 1).map (probeInv j a θ) = pathMeas (invPath D) := by
      rw [segMeasure_eq]
      have hae : probeInv j a θ =ᵐ[pathMeas segPath] D.Ψ := by
        filter_upwards [ae_pathMeas_mem segPath.continuous.measurable
          (isCompact_rectN 0).isClosed.measurableSet
          (fun t ht => segPath_mem_rectN le_rfl ht)] with w hw
        rw [hDΨ]
        exact probeInv_eq_extInv hθ1 (rectN_subset_probeRectU (by positivity) hw)
      rw [Measure.map_congr hae, pathMeas, pathMeas,
        Measure.map_map D.continuous_inv.measurable segPath.continuous.measurable]
      rfl
    filter_upwards [hmain] with ω hω
    rw [hmapeq, segMeasure_eq]
    exact hω

end SmallGammaGeodesics
