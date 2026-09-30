import QuantumZipper.Proofs.Zipper.UnifUCE2Large
import QuantumZipper.Proofs.Zipper.UnifUC1Rad

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UNIF-RC3-E2 (decision D33): `EnergyParStmt T` holds

**Main result** `energyParStmt_holds : EnergyParStmt T` (all `T`): for an `a`-Hölder driver `W`
(`HolderDrv W T a CH`) and a dyadic folded circle `fc(d, 2^{-k})`, the Neumann energy of
`muUS p ρ − muUS p' ρ` is `≤ C · dist(p, p')^b` on `tri T × tri T × [0,1]`, with
`b = a · min(a₁, 1) / 96` (`a₁` the E1 exponent).

Proof (interpolation, plan D33 item 5). Let `δ = dist p p'`, `x = δ^{a/96}`.

* `δ > 1/2`: the crude bound `energyPar_small_le` (below) and `1 ≤ 2 δ^b`.
* `δ ≤ 1/2`, `ρ < x`: `energyPar_small_le`: the triangle inequality for the energy through
  `muUS p 0` and `muUS p' 0`, E1 (`energyRadStmt_holds`) for the radius legs and the `ρ = 0` time
  modulus (`energyParZero_le`) for the middle leg: `E ≤ 6 C₁ ρ^{a₁} + 4 C₀ δ^{a/12}`.
* `δ ≤ 1/2`, `ρ ≥ x`: `energyPar_large_le` with `r₀ = x`, strip width `τ = x^{24}`; the
  JointMod constants are `O(x^{-2})` (`timeK_mul_sq_le`, `spaceK_mul_sq_le`), and every term is
  `O(x²) = O(δ^{a/48})`.

Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1; Duplantier–Sheffield, Invent. Math.
185 (2011), Prop. 3.1. The interpolation over the three regimes is an own elementary argument.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint GFFExist B2

variable {W : ℝ → ℝ}

/-- The crude (small-radius) bound through `ρ = 0`. -/
theorem energyPar_small_le (hW : Continuous W) (hW0 : W 0 = 0) {T Mw C₁ a₁ C₀ e : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (d : ℂ) (k : ℕ)
    (hE1 : ∀ p ∈ tri T, ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (muUS W d k p ρ, muUS W d k p ρ') (muUS W d k p ρ, muUS W d k p ρ')| ≤
        C₁ * |ρ - ρ'| ^ a₁)
    (hE0 : ∀ p ∈ tri T, ∀ p' ∈ tri T,
      |kernelCov2 neumannH (muUS W d k p 0, muUS W d k p' 0)
        (muUS W d k p 0, muUS W d k p' 0)| ≤ C₀ * dist p p' ^ e)
    {p p' : ℝ × ℝ} (hp : p ∈ tri T) (hp' : p' ∈ tri T) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    kernelCov2 neumannH (muUS W d k p ρ, muUS W d k p' ρ) (muUS W d k p ρ, muUS W d k p' ρ) ≤
      6 * (C₁ * ρ ^ a₁) + 4 * (C₀ * dist p p' ^ e) := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨ha, hma⟩ := admissible_muUS hW hW0 hMw d k hp hρ.1 hρ.2
  obtain ⟨hb, hmb⟩ := admissible_muUS hW hW0 hMw d k hp le_rfl zero_le_one
  obtain ⟨hc, hmc⟩ := admissible_muUS hW hW0 hMw d k hp' le_rfl zero_le_one
  obtain ⟨hd, hmd⟩ := admissible_muUS hW hW0 hMw d k hp' hρ.1 hρ.2
  have t1 := kernelCov2_self_triangle ha hb hd (hma.trans hmb.symm) (hmb.trans hmd.symm)
  have t2 := kernelCov2_self_triangle hb hc hd (hmb.trans hmc.symm) (hmc.trans hmd.symm)
  have e1 := (le_abs_self _).trans (hE1 p hp ρ hρ 0 h01)
  have e2 := (le_abs_self _).trans (hE1 p' hp' 0 h01 ρ hρ)
  have e3 := (le_abs_self _).trans (hE0 p hp p' hp')
  rw [sub_zero, abs_of_nonneg hρ.1] at e1
  rw [zero_sub, abs_neg, abs_of_nonneg hρ.1] at e2
  linarith

/-- The arithmetic of the large-radius regime (pure real inequality). -/
theorem energyPar_large_arith {E tK sK G Cs c2 rk x : ℝ} (htK : 0 ≤ tK) (hsK : 0 ≤ sK)
    (hG0 : 0 ≤ G) (hCs0 : 0 ≤ Cs) (hc20 : 0 ≤ c2) (hrk : 0 < rk) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hP : tK * x ^ 2 ≤ G) (hQ : sK * x ^ 2 ≤ G)
    (hL : E ≤ 2 * (2 * (tK * x ^ 8) + 2 * (sK * (Cs * x ^ 4))) +
      2 * ((2 * (tK * x ^ 8) + 2 * (sK * c2)) * (324 * (x ^ 24 / rk)))) :
    E ≤ (4 * G + 4 * (Cs * G) + 1296 / rk * (G + c2 * G)) * x ^ 2 := by
  have hle : ∀ n : ℕ, 2 ≤ n → x ^ n ≤ x ^ 2 := fun n hn => pow_le_pow_of_le_one hx0.le hx1 hn
  have hA : tK * x ^ 8 ≤ G * x ^ 2 := by
    calc tK * x ^ 8 = (tK * x ^ 2) * x ^ 6 := by ring
      _ ≤ G * x ^ 6 := mul_le_mul_of_nonneg_right hP (by positivity)
      _ ≤ G * x ^ 2 := mul_le_mul_of_nonneg_left (hle 6 (by norm_num)) hG0
  have hB : sK * x ^ 4 ≤ G * x ^ 2 := by
    calc sK * x ^ 4 = (sK * x ^ 2) * x ^ 2 := by ring
      _ ≤ G * x ^ 2 := mul_le_mul_of_nonneg_right hQ (by positivity)
  have hC : tK * x ^ 8 * x ^ 24 ≤ G * x ^ 2 := by
    calc tK * x ^ 8 * x ^ 24 = (tK * x ^ 2) * x ^ 30 := by ring
      _ ≤ G * x ^ 30 := mul_le_mul_of_nonneg_right hP (by positivity)
      _ ≤ G * x ^ 2 := mul_le_mul_of_nonneg_left (hle 30 (by norm_num)) hG0
  have hD : sK * x ^ 24 ≤ G * x ^ 2 := by
    calc sK * x ^ 24 = (sK * x ^ 2) * x ^ 22 := by ring
      _ ≤ G * x ^ 22 := mul_le_mul_of_nonneg_right hQ (by positivity)
      _ ≤ G * x ^ 2 := mul_le_mul_of_nonneg_left (hle 22 (by norm_num)) hG0
  have eL : 2 * (2 * (tK * x ^ 8) + 2 * (sK * (Cs * x ^ 4))) +
      2 * ((2 * (tK * x ^ 8) + 2 * (sK * c2)) * (324 * (x ^ 24 / rk))) =
      4 * (tK * x ^ 8) + 4 * (Cs * (sK * x ^ 4)) +
        1296 / rk * (tK * x ^ 8 * x ^ 24 + c2 * (sK * x ^ 24)) := by
    field_simp; ring
  rw [eL] at hL
  have i1 := mul_le_mul_of_nonneg_left hB hCs0
  have i2 := mul_le_mul_of_nonneg_left hD hc20
  have i3 : tK * x ^ 8 * x ^ 24 + c2 * (sK * x ^ 24) ≤ G * x ^ 2 + c2 * (G * x ^ 2) := by
    linarith
  have i4 := mul_le_mul_of_nonneg_left i3 (by positivity : (0 : ℝ) ≤ 1296 / rk)
  have i5 : (4 * G + 4 * (Cs * G) + 1296 / rk * (G + c2 * G)) * x ^ 2 =
      4 * (G * x ^ 2) + 4 * (Cs * (G * x ^ 2)) +
      1296 / rk * (G * x ^ 2 + c2 * (G * x ^ 2)) := by ring
  linarith

/-- **The large-radius regime**: `ρ ≥ δ^{a/96}`, `0 < δ ≤ 1/2` gives `E ≤ C δ^{a/48}`. -/
theorem energyPar_large_final {T a CH : ℝ} (hWH : HolderDrv W T a CH) (hT : 0 ≤ T) {Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (d : ℂ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ tri T, ∀ p' ∈ tri T, 0 < dist p p' → dist p p' ≤ 1 / 2 →
      ∀ ρ : ℝ, dist p p' ^ (a / 96) ≤ ρ → ρ ≤ 1 →
        kernelCov2 neumannH (muUS W d k p ρ, muUS W d k p' ρ)
          (muUS W d k p ρ, muUS W d k p' ρ) ≤ C * dist p p' ^ (a / 48) := by
  have hWH' := hWH
  obtain ⟨-, -, ha, -, hCH, -⟩ := hWH'
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  have hrk0 : 0 < radius k := radius_pos k
  obtain ⟨Ra, hRa⟩ : ∃ Ra, Ra = revBound (2 * Mw) T (‖d‖ + radius k) := ⟨_, rfl⟩
  have hRa0 : 0 ≤ Ra := by rw [hRa]; exact revBound_nonneg (by linarith) hT
  obtain ⟨Cst, hCst⟩ : ∃ Cst, Cst = 4 * (CH + 2) * (1 + Real.sqrt ((‖d‖ + radius k) ^ 2 + 8 * T)) :=
    ⟨_, rfl⟩
  have hCst0 : 0 ≤ Cst := by rw [hCst]; positivity
  have hCs0 : 0 ≤ Cst ^ (1 / 12 : ℝ) := Real.rpow_nonneg hCst0 _
  have hc20 : 0 ≤ (2 * Ra) ^ (1 / 12 : ℝ) := Real.rpow_nonneg (by linarith) _
  obtain ⟨G, hG⟩ : ∃ G, G = |timeKs Mw T (Ra + 1) CH| + |spaceKs Mw T (Ra + 1)| := ⟨_, rfl⟩
  have hn1 := abs_nonneg (spaceKs Mw T (Ra + 1))
  have hn2 := abs_nonneg (timeKs Mw T (Ra + 1) CH)
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  refine ⟨4 * G + 4 * (Cst ^ (1 / 12 : ℝ) * G) + 1296 / radius k *
    (G + (2 * Ra) ^ (1 / 12 : ℝ) * G), by positivity, fun p hp p' hp' hδpos hpp ρ hρ hρ1 => ?_⟩
  have hδ0 : 0 ≤ dist p p' := hδpos.le
  have hδ1 : dist p p' ≤ 1 := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = dist p p' ^ (a / 96) := ⟨_, rfl⟩
  rw [← hx] at hρ
  have hx0 : 0 < x := by rw [hx]; exact Real.rpow_pos_of_pos hδpos _
  have hx1 : x ≤ 1 := by rw [hx]; exact Real.rpow_le_one hδ0 hδ1 (by positivity)
  have hxpow : ∀ n : ℕ, x ^ n = dist p p' ^ (a / 96 * n) := fun n => by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hδ0]
  have hL := energyPar_large_le hWH hMw d k hRa hp hp' hpp hx0 hρ hρ1
    (τ := x ^ 24) (by positivity) (pow_le_one₀ hx0.le hx1)
  rw [← hCst] at hL
  have e8 : dist p p' ^ (a / 12) = x ^ 8 := by rw [hxpow 8]; congr 1; push_cast; ring
  have e96 : dist p p' ^ a = x ^ 96 := by rw [hxpow 96]; congr 1; push_cast; ring
  have e48 : dist p p' ^ (a / 48) = x ^ 2 := by rw [hxpow 2]; congr 1; push_cast; ring
  have eC : (Cst * x ^ 96 / (x ^ 24) ^ 2) ^ (1 / 12 : ℝ) = Cst ^ (1 / 12 : ℝ) * x ^ 4 := by
    have : Cst * x ^ 96 / (x ^ 24) ^ 2 = Cst * (x ^ 4) ^ 12 := by
      field_simp
    rw [this, Real.mul_rpow hCst0 (by positivity), ← Real.rpow_natCast (x ^ 4) 12,
      ← Real.rpow_mul (by positivity)]
    norm_num
  have eS : (18 * Real.sqrt (x ^ 24 / radius k)) ^ 2 = 324 * (x ^ 24 / radius k) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  rw [e8, e96, eC, eS] at hL
  rw [e48]
  refine energyPar_large_arith (timeK_nonneg_E2 hMw0 hT hx0 hCH) (spaceK_nonneg_E2 hMw0 hT hx0)
    hG0 hCs0 hc20 hrk0 hx0 hx1 ?_ ?_ hL
  · exact (timeK_mul_sq_le hMw0 hT hx0 hx1 hCH).trans ((le_abs_self _).trans (by linarith))
  · exact (spaceK_mul_sq_le hMw0 hT hx0 hx1).trans ((le_abs_self _).trans (by linarith))

/-- **UNIF-RC3-E2: `EnergyParStmt T` holds.** -/
theorem energyParStmt_holds (T : ℝ) : EnergyParStmt T := by
  intro W a CH hWH d k
  have hWH' := hWH
  obtain ⟨hW, hW0, ha, ha1, hCH, hH⟩ := hWH'
  by_cases hT : 0 ≤ T
  swap
  · refine ⟨0, 1, le_rfl, one_pos, fun p hp => ?_⟩
    exact absurd (add_nonneg hp.1 hp.2.1 |>.trans hp.2.2) hT
  obtain ⟨Mw, hMw'⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  have hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw := fun t ht => by
    simpa [Real.norm_eq_abs] using hMw' t ht
  obtain ⟨C₁, a₁, hC₁, ha₁, hE1⟩ := energyRadStmt_holds T W hW hW0 d k
  obtain ⟨C₀, hC₀, hE0⟩ := energyParZero_le hW hW0 hT hMw ha ha1 hCH hH d k
  obtain ⟨Cb, hCb0, hbig⟩ := energyPar_large_final hWH hT hMw d k
  obtain ⟨b, hb⟩ : ∃ b, b = a * min a₁ 1 / 96 := ⟨_, rfl⟩
  have hmin0 : 0 < min a₁ 1 := lt_min ha₁ one_pos
  have hmin1 : min a₁ 1 ≤ 1 := min_le_right _ _
  have hmin2 : min a₁ 1 ≤ a₁ := min_le_left _ _
  have hb0 : 0 < b := by rw [hb]; positivity
  have hb1 : b ≤ 1 := by rw [hb]; nlinarith
  have hb48 : b ≤ a / 48 := by rw [hb]; nlinarith
  have hb12 : b ≤ a / 12 := by rw [hb]; nlinarith
  have hbaa : b ≤ a / 96 * a₁ := by rw [hb]; nlinarith
  have hCs0 : 0 ≤ 6 * C₁ + 4 * C₀ := by positivity
  have hCf0 : 0 ≤ 2 * (6 * C₁ + 4 * (C₀ * (T + 1))) := by positivity
  refine ⟨Cb + (6 * C₁ + 4 * C₀) + 2 * (6 * C₁ + 4 * (C₀ * (T + 1))), b, by positivity, hb0,
    fun p hp p' hp' ρ hρ => ?_⟩
  have hδ0 : 0 ≤ dist p p' := dist_nonneg
  have hδb : 0 ≤ dist p p' ^ b := Real.rpow_nonneg hδ0 _
  obtain ⟨hA, hmA⟩ := admissible_muUS hW hW0 hMw d k hp hρ.1 hρ.2
  obtain ⟨hB, hmB⟩ := admissible_muUS hW hW0 hMw d k hp' hρ.1 hρ.2
  rw [abs_of_nonneg (kernelCov2_self_nonneg hA hB (hmA.trans hmB.symm))]
  rcases hδ0.eq_or_lt with hδz | hδpos
  · -- `p = p'`
    have hpp : p = p' := dist_eq_zero.1 hδz.symm
    subst hpp
    have : kernelCov2 neumannH (muUS W d k p ρ, muUS W d k p ρ)
        (muUS W d k p ρ, muUS W d k p ρ) = 0 := by unfold kernelCov2; ring
    rw [this]; positivity
  have hsmall := energyPar_small_le hW hW0 hMw d k hE1 hE0 hp hp' hρ
  have hρa : ρ ^ a₁ ≤ 1 := Real.rpow_le_one hρ.1 hρ.2 ha₁.le
  have hbig' := fun (hfar : dist p p' ≤ 1 / 2) (hcase : dist p p' ^ (a / 96) ≤ ρ) =>
    hbig p hp p' hp' hδpos hfar ρ hcase hρ.2
  generalize kernelCov2 neumannH (muUS W d k p ρ, muUS W d k p' ρ)
    (muUS W d k p ρ, muUS W d k p' ρ) = E at hsmall hbig' ⊢
  have m1 := mul_nonneg hCb0 hδb
  have m2 := mul_nonneg hCs0 hδb
  have m3 := mul_nonneg hCf0 hδb
  have hsum : (Cb + (6 * C₁ + 4 * C₀) + 2 * (6 * C₁ + 4 * (C₀ * (T + 1)))) * dist p p' ^ b =
      Cb * dist p p' ^ b + (6 * C₁ + 4 * C₀) * dist p p' ^ b +
        2 * (6 * C₁ + 4 * (C₀ * (T + 1))) * dist p p' ^ b := by ring
  rw [hsum]
  by_cases hfar : 1 / 2 < dist p p'
  · -- far apart: crude bound
    have hδT : dist p p' ≤ T + 1 := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      refine max_le ?_ ?_ <;> rw [abs_le] <;> constructor <;>
        linarith [hp.1, hp.2.1, hp.2.2, hp'.1, hp'.2.1, hp'.2.2]
    have h1 : dist p p' ^ (a / 12) ≤ T + 1 := by
      refine (Real.rpow_le_rpow hδ0 hδT (by positivity)).trans ?_
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ T + 1 by linarith)
        (show a / 12 ≤ 1 by linarith)
      rwa [Real.rpow_one] at this
    have h2 : (1 : ℝ) ≤ 2 * dist p p' ^ b := by
      have h3 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ b :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hb1
      have h4 : (1 / 2 : ℝ) ^ b ≤ dist p p' ^ b := Real.rpow_le_rpow (by norm_num) hfar.le hb0.le
      rw [Real.rpow_one] at h3
      linarith
    have h5 := mul_le_mul_of_nonneg_left hρa hC₁
    have h6 := mul_le_mul_of_nonneg_left h1 hC₀
    have h7 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 6 * C₁ + 4 * (C₀ * (T + 1)))
    nlinarith
  push Not at hfar
  have hδ1 : dist p p' ≤ 1 := by linarith
  by_cases hcase : dist p p' ^ (a / 96) ≤ ρ
  · -- large radius
    have h := hbig' hfar hcase
    have h2 : dist p p' ^ (a / 48) ≤ dist p p' ^ b :=
      Real.rpow_le_rpow_of_exponent_ge hδpos hδ1 hb48
    have := mul_le_mul_of_nonneg_left h2 hCb0
    linarith
  · -- small radius
    push Not at hcase
    have h1 : ρ ^ a₁ ≤ dist p p' ^ b := by
      refine (Real.rpow_le_rpow hρ.1 hcase.le ha₁.le).trans ?_
      rw [← Real.rpow_mul hδ0]
      exact Real.rpow_le_rpow_of_exponent_ge hδpos hδ1 hbaa
    have h2 : dist p p' ^ (a / 12) ≤ dist p p' ^ b :=
      Real.rpow_le_rpow_of_exponent_ge hδpos hδ1 hb12
    have := mul_le_mul_of_nonneg_left h1 hC₁
    have := mul_le_mul_of_nonneg_left h2 hC₀
    nlinarith

end RegUnif
end QuantumZipper
