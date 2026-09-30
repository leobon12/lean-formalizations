import QuantumZipper.Proofs.LQG.AreaP3bSup
import QuantumZipper.Proofs.LQG.AreaP3bOmega
import QuantumZipper.Proofs.LQG.AtomlessUncond

/-!
# M4-P3(b), area version, part 6: fractional moments of the interior area mass

Discharges `AtomlessUncond.P3bBoundArea` (TASKS.md R14, first theorem; handoff
`handoff/M4-AREA-P3B.md`, "Remaining" item 4).

For the normalized field `Z = aZ X R`, an interior point `z ∈ ℍ` and the dyadic scales
`δ = 4·2^{-n}`, `D = min (Im z) 1 / 2`, `d = D/2`, `S = annIC z n = B̄(z, 2^{-n})`, the
decomposition `mu_{2^{-k}}(S) = e^{γΩ} δ^{γ²/2} W_k(S)` of `AreaP3bInner`
(`ae_areaApprox_eq_omZ_mul`) holds a.s. for all `k ≥ n`, and `Ω = omZ X z δ D` is independent of
the inner field (`indepFun_omZ_innerS`). Hence the `p`-th moment of `sup_{k ≥ n} mu_{2^{-k}}(S)`
factors into the lognormal moment of `e^{γΩ} δ^{γ²/2}` (`lintegral_omZ_factor_rpow`, handoff item
3) times the `p`-th moment of `sup_m W_{n+m}(S)`, which is controlled by
`AreaP3bSup.lintegral_iSup_massFunC_inner_rpow_le`. The two deterministic factors combine into
the single power of `2` required by `P3bBoundArea`:

  `E (sup_{k ≥ n} mu_{2^{-k}}(S))^p ≤ C 2^{n(γ²p²/2 − p(2 + γ²/2))}`.

This mirrors the boundary computation `FracMom.fracMoment_dyadic`; the interior decomposition
`Ω = Z_δ(z) − Z_D(z)` is the own adaptation recorded in DEVIATIONS (L-M4 item 7).

Source: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.3, p. 18 (the circle average process
`h_{e^{-t}}(z)` is a Brownian motion, whence independent increments of the circle averages) and
§3.2, (14)–(15), p. 19 (the LQG area measure `ε^{γ²/2}e^{γh_ε}dz`); the Θ-law form of the no-atom
statement is §3.3, (25), p. 22 (`AreaNoAtom.areaLogSingNoAtom`). (AUDIT10 G10-2 corrects the
earlier "§3.1"; §3.1 of the paper is the smoothness of the circle average field, Prop. 3.1.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaP3b

open GaussTK KernelId FinArea

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ### Elementary real lemmas on `radius n = 2^{-n}` -/

/-- `radius n ^ a = 2^{-n a}`. -/
theorem radius_rpow_eq {a : ℝ} (n : ℕ) : radius n ^ a = (2 : ℝ) ^ (-(n : ℝ) * a) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hrn : radius n = (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [radius, inv_pow, ← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_neg h2.le]
  rw [hrn, ← Real.rpow_mul h2.le]

/-- `e^{(log D − log δ) t} = D^t δ^{−t}` for `D, δ > 0`. -/
theorem exp_log_sub_mul {D δ t : ℝ} (hD : 0 < D) (hδ : 0 < δ) :
    exp ((log D - log δ) * t) = D ^ t * δ ^ (-t) := by
  rw [sub_mul, exp_sub, div_eq_mul_inv, ← Real.rpow_def_of_pos hD, ← Real.rpow_def_of_pos hδ,
    ← Real.rpow_neg hδ.le]

/-- **The `n`-dependence of the `Ω`-factor.** With `δ = 4·2^{-n}`,
`δ^{pγ²/2} e^{(log D − log δ)(pγ)²/2} δ^{2p} = D^{(pγ)²/2} 4^{A} 2^{n(γ²p²/2 − p(2+γ²/2))}`,
`A = pγ²/2 + 2p − (pγ)²/2 = −(γ²p²/2 − p(2+γ²/2))`. -/
theorem u_mul_delta_eq {γ p D : ℝ} (hD : 0 < D) (n : ℕ) :
    (4 * radius n) ^ (p * (γ ^ 2 / 2)) *
        exp ((log D - log (4 * radius n)) * (p * γ) ^ 2 / 2) * (4 * radius n) ^ (2 * p) =
      D ^ ((p * γ) ^ 2 / 2) * (4 : ℝ) ^ (p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2) *
        (2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * p ^ 2 / 2 - p * (2 + γ ^ 2 / 2))) := by
  have hrn : 0 < radius n := radius_pos n
  have hδ : 0 < 4 * radius n := by positivity
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have harg : (log D - log (4 * radius n)) * (p * γ) ^ 2 / 2
      = (log D - log (4 * radius n)) * ((p * γ) ^ 2 / 2) := by ring
  rw [harg, exp_log_sub_mul hD hδ]
  have hrearr : ((4 * radius n) ^ (p * (γ ^ 2 / 2)) *
        (D ^ ((p * γ) ^ 2 / 2) * (4 * radius n) ^ (-((p * γ) ^ 2 / 2)))) *
        (4 * radius n) ^ (2 * p)
      = D ^ ((p * γ) ^ 2 / 2) * ((4 * radius n) ^ (p * (γ ^ 2 / 2)) *
        (4 * radius n) ^ (-((p * γ) ^ 2 / 2)) * (4 * radius n) ^ (2 * p)) := by ring
  rw [hrearr, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
  have hexp : p * (γ ^ 2 / 2) + -((p * γ) ^ 2 / 2) + 2 * p
      = p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2 := by ring
  rw [hexp, Real.mul_rpow h4 hrn.le, radius_rpow_eq]
  have hexp2 : -(n : ℝ) * (p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2)
      = (n : ℝ) * (γ ^ 2 * p ^ 2 / 2 - p * (2 + γ ^ 2 / 2)) := by ring
  rw [hexp2]
  ring

/-- **The real core of the interior area fractional-moment bound**: the `Ω`-factor times the sup
bound's two summands (`|S| = π 2^{-2n} = π δ²/16`), with the constants of the statement. -/
theorem u_mul_factor_eq {γ p D K Cst q : ℝ} (hD : 0 < D) (hCst : 0 ≤ Cst) (n : ℕ) :
    ((4 * radius n) ^ (p * (γ ^ 2 / 2)) *
        exp ((log D - log (4 * radius n)) * (p * γ) ^ 2 / 2)) *
      ((exp (γ ^ 2 / 2 * K) * (π * radius n ^ 2)) ^ p +
        (Cst * (4 * radius n) ^ 2) ^ p * (1 - q)⁻¹) =
      (D ^ ((p * γ) ^ 2 / 2) * (exp (γ ^ 2 / 2 * K) * (π / 16)) ^ p *
          (4 : ℝ) ^ (p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2) +
        D ^ ((p * γ) ^ 2 / 2) * Cst ^ p * (1 - q)⁻¹ *
          (4 : ℝ) ^ (p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2)) *
        (2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * p ^ 2 / 2 - p * (2 + γ ^ 2 / 2))) := by
  have hrn : 0 < radius n := radius_pos n
  have hδ : 0 < 4 * radius n := by positivity
  have h16 : (0 : ℝ) ≤ π / 16 := by positivity
  have hpt : (0 : ℝ) ≤ (4 * radius n) ^ (2 : ℝ) := rpow_nonneg hδ.le 2
  have h2 : (exp (γ ^ 2 / 2 * K) * (π * radius n ^ 2)) ^ p
      = (exp (γ ^ 2 / 2 * K) * (π / 16)) ^ p * (4 * radius n) ^ (2 * p) := by
    have hsq : π * radius n ^ 2 = π / 16 * (4 * radius n) ^ (2 : ℝ) := by
      rw [Real.rpow_two]; ring
    rw [hsq, ← mul_assoc, Real.mul_rpow (mul_nonneg (exp_pos _).le h16) hpt,
      ← Real.rpow_mul hδ.le]
  have h3 : (Cst * (4 * radius n) ^ 2) ^ p = Cst ^ p * (4 * radius n) ^ (2 * p) := by
    rw [← Real.rpow_two (4 * radius n), Real.mul_rpow hCst hpt, ← Real.rpow_mul hδ.le]
  rw [h2, h3,
    show ((4 * radius n) ^ (p * (γ ^ 2 / 2)) *
          exp ((log D - log (4 * radius n)) * (p * γ) ^ 2 / 2)) *
        ((exp (γ ^ 2 / 2 * K) * (π / 16)) ^ p * (4 * radius n) ^ (2 * p) +
          Cst ^ p * (4 * radius n) ^ (2 * p) * (1 - q)⁻¹)
        = ((4 * radius n) ^ (p * (γ ^ 2 / 2)) *
            exp ((log D - log (4 * radius n)) * (p * γ) ^ 2 / 2) *
            (4 * radius n) ^ (2 * p)) *
          ((exp (γ ^ 2 / 2 * K) * (π / 16)) ^ p + Cst ^ p * (1 - q)⁻¹) by ring,
    u_mul_delta_eq (γ := γ) (p := p) (D := D) hD n]
  ring

/-! ### The dyadic ball volume -/

theorem volumeReal_annIC (z : ℂ) (n : ℕ) :
    volume.real (AtomlessUncond.annIC z n) = π * radius n ^ 2 := by
  have hpi : (↑NNReal.pi : ℝ≥0∞).toReal = π := by
    rw [show (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal π by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]]
    exact ENNReal.toReal_ofReal pi_pos.le
  rw [AtomlessUncond.annIC, MeasureTheory.measureReal_def, Complex.volume_closedBall,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (radius_pos n).le, hpi]
  ring

/-! ### The fractional-moment bound -/

/-- **M4-P3(b), interior area version** (TASKS.md R14, first theorem): under `IsFreeGFFModConstH`,
for `0 < γ < 2` and `z ∈ ℍ`, `‖z‖ + 1 ≤ R`, the area fractional-moment bound `P3bBoundArea`
holds at `z`. -/
theorem fracMoment_area_interior [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} {z : ℂ} (hz : z ∈ H) (hR : ‖z‖ + 1 ≤ R) :
    AtomlessUncond.P3bBoundArea P X γ R z := by
  intro p hp0 hp1
  -- geometric data
  have hz0 : 0 < z.im := hz
  have hR1 : 1 ≤ R := by linarith [norm_nonneg z]
  set D : ℝ := min z.im 1 / 2 with hDdef
  set d : ℝ := D / 2 with hddef
  set V : ℝ := π / 16 with hVdef
  set Cst : ℝ := cRate γ (2 * log R - log D - log (2 * d)) V with hCstdef
  set q : ℝ := exp (-(p * (min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
      ((2 - γ) ^ 2 / 4))) * (1 / 2 * log 2)) with hqdef
  set Ctot : ℝ := D ^ ((p * γ) ^ 2 / 2) * (exp (γ ^ 2 / 2 * (2 * log R - log D - log (2 * d))) *
        (π / 16)) ^ p * (4 : ℝ) ^ (p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2) +
      D ^ ((p * γ) ^ 2 / 2) * Cst ^ p * (1 - q)⁻¹ *
        (4 : ℝ) ^ (p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2) with hCtotdef
  have hDpos : 0 < D := by rw [hDdef]; exact div_pos (lt_min hz0 one_pos) two_pos
  have hD1 : D ≤ 1 := by rw [hDdef]; have := min_le_right z.im 1; linarith
  have hDz : D ≤ z.im := by rw [hDdef]; have := min_le_left z.im 1; linarith
  have hd0 : 0 < d := by rw [hddef]; linarith
  have hd1 : 2 * d ≤ 1 := by rw [hddef]; have := min_le_right z.im 1; linarith
  have hDR : ‖z‖ + D ≤ R := by rw [hDdef]; have := min_le_right z.im 1; linarith
  have hV0 : 0 ≤ V := by rw [hVdef]; positivity
  have hCst0 : 0 ≤ Cst := by rw [hCstdef]; exact cRate_nonneg hV0
  have hqq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := by
    rw [hqdef, Real.exp_lt_one_iff]
    have hβ : 0 < min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2) ((2 - γ) ^ 2 / 4) :=
      lt_min (areaRateExp_pos hγ hγ2) (by positivity)
    have h1 : 0 < p * min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2) ((2 - γ) ^ 2 / 4) :=
      mul_pos hp0 hβ
    have h2 : 0 < (1 : ℝ) / 2 * log 2 := by
      have := log_pos one_lt_two
      positivity
    nlinarith [mul_pos h1 h2]
  have hCtot0 : 0 ≤ Ctot := by
    rw [hCtotdef]
    have h1q : (0 : ℝ) < 1 - q := by linarith
    have h1 : 0 ≤ (exp (γ ^ 2 / 2 * (2 * log R - log D - log (2 * d))) * (π / 16)) ^ p :=
      rpow_nonneg (by positivity) p
    have h2 : 0 ≤ Cst ^ p := rpow_nonneg hCst0 p
    have h3 : 0 ≤ (1 - q)⁻¹ := inv_nonneg.2 h1q.le
    have h4 : 0 ≤ (4 : ℝ) ^ (p * (γ ^ 2 / 2) + 2 * p - (p * γ) ^ 2 / 2) :=
      rpow_nonneg (by norm_num) _
    have h5 : 0 ≤ D ^ ((p * γ) ^ 2 / 2) := rpow_nonneg hDpos.le _
    exact add_nonneg (mul_nonneg (mul_nonneg h5 h1) h4)
      (mul_nonneg (mul_nonneg (mul_nonneg h5 h2) h3) h4)
  -- the dyadic scale
  obtain ⟨N₁, hN₁⟩ := AtomlessUncond.exists_radius_lt (show 0 < D / 4 by linarith)
  obtain ⟨N₂, hN₂⟩ := AtomlessUncond.exists_radius_lt (show 0 < z.im / 2 by linarith)
  refine ⟨ENNReal.ofReal Ctot, ENNReal.ofReal_ne_top, max N₁ N₂, fun n hn => ?_⟩
  have hn1 : radius n < D / 4 := hN₁ n (le_trans (le_max_left _ _) hn)
  have hn2 : radius n < z.im / 2 := hN₂ n (le_trans (le_max_right _ _) hn)
  have hrn : 0 < radius n := radius_pos n
  have hδ : 0 < 4 * radius n := by positivity
  have hδD : 4 * radius n ≤ D := by linarith
  -- `S = B̄(z, 2^{-n})` and the standing hypotheses at level `n`
  have hS : MeasurableSet (AtomlessUncond.annIC z n) := by
    rw [AtomlessUncond.annIC]; exact Metric.isClosed_closedBall.measurableSet
  have hSf : volume (AtomlessUncond.annIC z n) < ∞ := by
    rw [AtomlessUncond.annIC, Complex.volume_closedBall]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (by simp)
  have hSH : AtomlessUncond.annIC z n ⊆ H := by
    intro w hw
    have hwn : ‖w - z‖ ≤ radius n := by
      rw [AtomlessUncond.annIC, Metric.mem_closedBall, dist_eq_norm] at hw; exact hw
    have h1 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h1
    have h2 : -(w.im - z.im) ≤ |w.im - z.im| := neg_le_abs _
    show 0 < w.im
    linarith
  have hne : (AtomlessUncond.annIC z n).Nonempty :=
    ⟨z, AtomlessUncond.mem_annIC (by rw [sub_self, norm_zero]; exact hrn.le)⟩
  have hSle : volume.real (AtomlessUncond.annIC z n) ≤ V * (4 * radius n) ^ 2 := by
    rw [volumeReal_annIC, hVdef]
    exact le_of_eq (by ring)
  have hsetup : Setup z (4 * radius n) D R d (AtomlessUncond.annIC z n) n := by
    refine ⟨hδD, hDz, hDR, hD1, hR1, hd0, hd1, ?_, ?_⟩
    · intro w hw
      have hwn : ‖w - z‖ ≤ radius n := by
        rw [AtomlessUncond.annIC, Metric.mem_closedBall, dist_eq_norm] at hw; exact hw
      have h1 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im] at h1
      have h2 : -(w.im - z.im) ≤ |w.im - z.im| := neg_le_abs _
      rw [hddef]
      linarith
    · intro w hw
      have hwn : ‖w - z‖ ≤ radius n := by
        rw [AtomlessUncond.annIC, Metric.mem_closedBall, dist_eq_norm] at hw; exact hw
      linarith
  -- the two factors
  have hsup := lintegral_iSup_massFunC_inner_rpow_le hX hγ hγ2 (z := z) (δ := 4 * radius n)
    (D := D) (R := R) (d := d) (V := V) (p := p) hS hSf hV0 hSle hne hp0 hp1 hsetup
  have hom := lintegral_omZ_factor_rpow hX γ (z := z) (δ := 4 * radius n) (D := D) (p := p)
    hδ hδD hDz hp0.le
  -- the a.s. factorization of the sup
  have hlev : ∀ k : ℕ, n ≤ k → ∀ w ∈ AtomlessUncond.annIC z n,
      ‖w - z‖ + radius k < 4 * radius n := by
    intro k hk w hw
    have hwn : ‖w - z‖ ≤ radius n := by
      rw [AtomlessUncond.annIC, Metric.mem_closedBall, dist_eq_norm] at hw; exact hw
    have hk' : radius k ≤ radius n := by
      rw [radius, radius]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    linarith
  have hsupae : ∀ᵐ ω ∂P, AtomlessUncond.annTC (areaApprox γ (AreaExist.aZ X R ω)) z n =
      ENNReal.ofReal (exp (γ * omZ X z (4 * radius n) D ω) * (4 * radius n) ^ (γ ^ 2 / 2)) *
        (⨆ m, massFunC γ (AtomlessUncond.annIC z n) (4 * radius n) (n + m)
          (innerS X z (4 * radius n) D R ω)) := by
    filter_upwards [ae_areaApprox_eq_omZ_mul (z := z) (δ := 4 * radius n) (D := D) (R := R)
      hX γ hδ hS hSH] with ω hω
    have h1 : (⨆ j, areaApprox γ (AreaExist.aZ X R ω) (j + n) (AtomlessUncond.annIC z n)) =
        ⨆ j, ENNReal.ofReal (exp (γ * omZ X z (4 * radius n) D ω) *
            (4 * radius n) ^ (γ ^ 2 / 2)) *
          massFunC γ (AtomlessUncond.annIC z n) (4 * radius n) (j + n)
            (innerS X z (4 * radius n) D R ω) :=
      iSup_congr fun j => hω (j + n) (hlev (j + n) (Nat.le_add_left n j))
    have h3 : (⨆ j, massFunC γ (AtomlessUncond.annIC z n) (4 * radius n) (j + n)
          (innerS X z (4 * radius n) D R ω)) =
        ⨆ m, massFunC γ (AtomlessUncond.annIC z n) (4 * radius n) (n + m)
          (innerS X z (4 * radius n) D R ω) :=
      iSup_congr fun j => congrArg (fun k => massFunC γ (AtomlessUncond.annIC z n)
        (4 * radius n) k (innerS X z (4 * radius n) D R ω)) (Nat.add_comm j n)
    rw [AtomlessUncond.annTC, h1, ← ENNReal.mul_iSup, h3]
  -- independence and the product of moments
  set A : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (exp (γ * omZ X z (4 * radius n) D ω) * (4 * radius n) ^ (γ ^ 2 / 2)) ^ p
    with hAdef
  set W : Ω → ℝ≥0∞ := fun ω => (⨆ m, massFunC γ (AtomlessUncond.annIC z n) (4 * radius n)
    (n + m) (innerS X z (4 * radius n) D R ω)) ^ p with hWdef
  have hφ : Measurable (fun x : ℝ =>
      ENNReal.ofReal (exp (γ * x) * (4 * radius n) ^ (γ ^ 2 / 2)) ^ p) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).pow_const p
  have hψ : Measurable (fun x : FieldSample =>
      (⨆ m, massFunC γ (AtomlessUncond.annIC z n) (4 * radius n) (n + m) x) ^ p) :=
    (Measurable.iSup fun m => measurable_massFunC γ _ _ (n + m)).pow_const p
  have hind : IndepFun A W P :=
    (indepFun_omZ_innerS hX (z := z) (δ := 4 * radius n) (D := D) (R := R)
      hδ hδD hDz hDR).comp hφ hψ
  have hAm : Measurable A := hφ.comp (measurable_omZ hX z (4 * radius n) D)
  have hWm : Measurable W := hψ.comp (measurable_innerS hX z (4 * radius n) D R)
  calc ∫⁻ ω, AtomlessUncond.annTC (areaApprox γ (AreaExist.aZ X R ω)) z n ^ p ∂P
      = ∫⁻ ω, (A * W) ω ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hsupae] with ω hω
        rw [hω, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        rfl
    _ = (∫⁻ ω, A ω ∂P) * ∫⁻ ω, W ω ∂P :=
        lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hAm hWm hind
    _ ≤ ENNReal.ofReal ((4 * radius n) ^ (p * (γ ^ 2 / 2)) *
          exp ((log D - log (4 * radius n)) * (p * γ) ^ 2 / 2)) *
        ((ENNReal.ofReal (exp (γ ^ 2 / 2 * (2 * log R - log D - log (2 * d))) *
            volume.real (AtomlessUncond.annIC z n))) ^ p +
          ENNReal.ofReal ((Cst * (4 * radius n) ^ 2) ^ p) *
            (1 - ENNReal.ofReal q)⁻¹) := mul_le_mul' hom.le hsup
    _ = ENNReal.ofReal (Ctot *
        (2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * p ^ 2 / 2 - p * (2 + γ ^ 2 / 2)))) := by
        have hqsub : (1 : ℝ≥0∞) - ENNReal.ofReal q = ENNReal.ofReal (1 - q) := by
          rw [ENNReal.ofReal_sub _ hqq0, ENNReal.ofReal_one]
        rw [volumeReal_annIC, ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, hqsub,
          ← ENNReal.ofReal_inv_of_pos (by linarith : (0 : ℝ) < 1 - q),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Cst * (4 * radius n) ^ 2) ^ p),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (4 * radius n) ^ (p * (γ ^ 2 / 2)) *
            exp ((log D - log (4 * radius n)) * (p * γ) ^ 2 / 2))]
        exact congrArg ENNReal.ofReal (u_mul_factor_eq (γ := γ) (p := p) (D := D)
          (K := 2 * log R - log D - log (2 * d)) (Cst := Cst) (q := q) hDpos hCst0 n)
    _ = ENNReal.ofReal Ctot *
        ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * p ^ 2 / 2 - p * (2 + γ ^ 2 / 2)))) :=
        ENNReal.ofReal_mul hCtot0

end AreaP3b
end QuantumZipper
