import QuantumZipper.Proofs.Zipper.XFlowEnergyE2Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-E2: the time modulus `FlowE2Stmt`, uniform over the circles of the box

**Main result** `flowE2Stmt_of_E1 : FlowAdmStmt → FlowE1Stmt → FlowE2Stmt`.

This is the D33 proof `RegUnif.energyParStmt_holds` (`UnifUCE2.lean`) with the dyadic circle
`fc(d, radius k)` replaced by the general circle `fc(d, r)` of `flowMu`, with all constants uniform
over `flowBox m` (`T = 2m + 2`): the circle enters only through `1/(m+2) ≤ r` (Frostman constant
`frostC T r₀ R`, strip bound `18 √(τ/r) ≤ 18 √(τ (m+2))`) and `‖d‖ + r ≤ 3(m+2)` (`revBound`,
the RSTAB constant). Interpolation over three regimes (`δ = dist p p'`, `x = δ^{a/96}`):
far (`δ > 1/2`), small radius (`ρ < x`, through `ρ = 0` with E1 and `flowE2_zero_le`), large
radius (`ρ ≥ x`, `flowE2_large_le` with strip width `x^{24}`).

Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1; Duplantier–Sheffield, Invent. Math.
185 (2011), Prop. 3.1. The interpolation is the own elementary argument of D33.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology

namespace QuantumZipper
namespace F1

open RegCont TwoPoint GFFExist B2 RegUnif

variable {W : ℝ → ℝ}

/-- **The large-radius regime, uniform over circles** (`energyPar_large_final` with
`rc ≤ r`, `‖d‖ + r ≤ R₀`). -/
theorem flowE2_large_final {T a CH : ℝ} (hWH : HolderDrv W T a CH) (hT : 0 ≤ T) {Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) {rc R₀ : ℝ} (hrc : 0 < rc) (hR₀ : 0 ≤ R₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℂ) (r : ℝ), rc ≤ r → ‖d‖ + r ≤ R₀ →
      ∀ P ∈ tri T, ∀ P' ∈ tri T, 0 < dist P P' → dist P P' ≤ 1 / 2 →
      ∀ ρ : ℝ, dist P P' ^ (a / 96) ≤ ρ → ρ ≤ 1 →
        kernelCov2 neumannH (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P'.1, P'.2, d, r) ρ)
          (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P'.1, P'.2, d, r) ρ) ≤
            C * dist P P' ^ (a / 48) := by
  have hWH' := hWH
  obtain ⟨-, -, ha, -, hCH, -⟩ := hWH'
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  obtain ⟨Ra, hRa⟩ : ∃ Ra, Ra = revBound (2 * Mw) T R₀ := ⟨_, rfl⟩
  have hRa0 : 0 ≤ Ra := by rw [hRa]; exact revBound_nonneg (by linarith) hT
  obtain ⟨Cst, hCst⟩ : ∃ Cst, Cst = 4 * (CH + 2) * (1 + Real.sqrt (R₀ ^ 2 + 8 * T)) :=
    ⟨_, rfl⟩
  have hCst0 : 0 ≤ Cst := by rw [hCst]; positivity
  have hCs0 : 0 ≤ Cst ^ (1 / 12 : ℝ) := Real.rpow_nonneg hCst0 _
  have hc20 : 0 ≤ (2 * Ra) ^ (1 / 12 : ℝ) := Real.rpow_nonneg (by linarith) _
  obtain ⟨G, hG⟩ : ∃ G, G = |timeKs Mw T (Ra + 1) CH| + |spaceKs Mw T (Ra + 1)| := ⟨_, rfl⟩
  have hn1 := abs_nonneg (spaceKs Mw T (Ra + 1))
  have hn2 := abs_nonneg (timeKs Mw T (Ra + 1) CH)
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  refine ⟨4 * G + 4 * (Cst ^ (1 / 12 : ℝ) * G) + 1296 / rc *
    (G + (2 * Ra) ^ (1 / 12 : ℝ) * G), by positivity,
    fun d r hr hdR P hp P' hp' hδpos hpp ρ hρ hρ1 => ?_⟩
  have hr0 : 0 < r := hrc.trans_le hr
  have hRa' : revBound (2 * Mw) T (‖d‖ + r) ≤ Ra := by
    rw [hRa]; unfold revBound
    rw [abs_of_nonneg (by positivity), abs_of_nonneg hR₀]; linarith
  have hδ0 : 0 ≤ dist P P' := hδpos.le
  have hδ1 : dist P P' ≤ 1 := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = dist P P' ^ (a / 96) := ⟨_, rfl⟩
  rw [← hx] at hρ
  have hx0 : 0 < x := by rw [hx]; exact Real.rpow_pos_of_pos hδpos _
  have hx1 : x ≤ 1 := by rw [hx]; exact Real.rpow_le_one hδ0 hδ1 (by positivity)
  have hxpow : ∀ n : ℕ, x ^ n = dist P P' ^ (a / 96 * n) := fun n => by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hδ0]
  have hL := flowE2_large_le hWH hMw hrc hr hdR hRa' hp hp' hpp hx0 hρ hρ1
    (τ := x ^ 24) (by positivity) (pow_le_one₀ hx0.le hx1)
  rw [← hCst] at hL
  have e8 : dist P P' ^ (a / 12) = x ^ 8 := by rw [hxpow 8]; congr 1; push_cast; ring
  have e96 : dist P P' ^ a = x ^ 96 := by rw [hxpow 96]; congr 1; push_cast; ring
  have e48 : dist P P' ^ (a / 48) = x ^ 2 := by rw [hxpow 2]; congr 1; push_cast; ring
  have eC : (Cst * x ^ 96 / (x ^ 24) ^ 2) ^ (1 / 12 : ℝ) = Cst ^ (1 / 12 : ℝ) * x ^ 4 := by
    have : Cst * x ^ 96 / (x ^ 24) ^ 2 = Cst * (x ^ 4) ^ 12 := by
      field_simp
    rw [this, Real.mul_rpow hCst0 (by positivity), ← Real.rpow_natCast (x ^ 4) 12,
      ← Real.rpow_mul (by positivity)]
    norm_num
  have eS : (18 * Real.sqrt (x ^ 24 / rc)) ^ 2 = 324 * (x ^ 24 / rc) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  rw [e8, e96, eC, eS] at hL
  rw [e48]
  refine energyPar_large_arith (timeK_nonneg_E2 hMw0 hT hx0 hCH) (spaceK_nonneg_E2 hMw0 hT hx0)
    hG0 hCs0 hc20 hrc hx0 hx1 ?_ ?_ hL
  · exact (timeK_mul_sq_le hMw0 hT hx0 hx1 hCH).trans ((le_abs_self _).trans (by linarith))
  · exact (spaceK_mul_sq_le hMw0 hT hx0 hx1).trans ((le_abs_self _).trans (by linarith))

/-- The crude (small-radius) bound through `ρ = 0` (`energyPar_small_le`, general circle,
parameters in a set `S`). -/
theorem flowE2_small_le {S : Set (ℝ × ℝ)} {d : ℂ} {r C₁ a₁ C₀ e : ℝ}
    (hAd : ∀ P ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1,
      IsAdmissibleH (flowMu W (P.1, P.2, d, r) ρ) ∧ flowMu W (P.1, P.2, d, r) ρ univ = 1)
    (hE1 : ∀ P ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P.1, P.2, d, r) ρ')
        (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P.1, P.2, d, r) ρ')| ≤ C₁ * |ρ - ρ'| ^ a₁)
    (hE0 : ∀ P ∈ S, ∀ P' ∈ S,
      |kernelCov2 neumannH (flowMu W (P.1, P.2, d, r) 0, flowMu W (P'.1, P'.2, d, r) 0)
        (flowMu W (P.1, P.2, d, r) 0, flowMu W (P'.1, P'.2, d, r) 0)| ≤ C₀ * dist P P' ^ e)
    {P P' : ℝ × ℝ} (hp : P ∈ S) (hp' : P' ∈ S) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    kernelCov2 neumannH (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P'.1, P'.2, d, r) ρ)
        (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P'.1, P'.2, d, r) ρ) ≤
      6 * (C₁ * ρ ^ a₁) + 4 * (C₀ * dist P P' ^ e) := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨ha, hma⟩ := hAd P hp ρ hρ
  obtain ⟨hb, hmb⟩ := hAd P hp 0 h01
  obtain ⟨hc, hmc⟩ := hAd P' hp' 0 h01
  obtain ⟨hd, hmd⟩ := hAd P' hp' ρ hρ
  have t1 := kernelCov2_self_triangle ha hb hd (hma.trans hmb.symm) (hmb.trans hmd.symm)
  have t2 := kernelCov2_self_triangle hb hc hd (hmb.trans hmc.symm) (hmc.trans hmd.symm)
  have e1 := (le_abs_self _).trans (hE1 P hp ρ hρ 0 h01)
  have e2 := (le_abs_self _).trans (hE1 P' hp' 0 h01 ρ hρ)
  have e3 := (le_abs_self _).trans (hE0 P hp P' hp')
  rw [sub_zero, abs_of_nonneg hρ.1] at e1
  rw [zero_sub, abs_neg, abs_of_nonneg hρ.1] at e2
  linarith

/-- **E2 for one circle, constants given** (the body of `energyParStmt_holds`, parameters in a
set `S ⊆ tri T`). -/
theorem flowE2_circle_le {T a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hT : 0 ≤ T)
    {S : Set (ℝ × ℝ)} (hS : S ⊆ tri T) {d : ℂ} {r C₁ a₁ C₀ Cb : ℝ}
    (hC₁ : 0 ≤ C₁) (ha₁ : 0 < a₁) (hC₀ : 0 ≤ C₀) (hCb0 : 0 ≤ Cb)
    (hAd : ∀ P ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1,
      IsAdmissibleH (flowMu W (P.1, P.2, d, r) ρ) ∧ flowMu W (P.1, P.2, d, r) ρ univ = 1)
    (hE1 : ∀ P ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P.1, P.2, d, r) ρ')
        (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P.1, P.2, d, r) ρ')| ≤ C₁ * |ρ - ρ'| ^ a₁)
    (hE0 : ∀ P ∈ S, ∀ P' ∈ S,
      |kernelCov2 neumannH (flowMu W (P.1, P.2, d, r) 0, flowMu W (P'.1, P'.2, d, r) 0)
        (flowMu W (P.1, P.2, d, r) 0, flowMu W (P'.1, P'.2, d, r) 0)| ≤
          C₀ * dist P P' ^ (a / 12))
    (hbig : ∀ P ∈ S, ∀ P' ∈ S, 0 < dist P P' → dist P P' ≤ 1 / 2 →
      ∀ ρ : ℝ, dist P P' ^ (a / 96) ≤ ρ → ρ ≤ 1 →
        kernelCov2 neumannH (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P'.1, P'.2, d, r) ρ)
          (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P'.1, P'.2, d, r) ρ) ≤
            Cb * dist P P' ^ (a / 48))
    {P P' : ℝ × ℝ} (hp : P ∈ S) (hp' : P' ∈ S) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    |kernelCov2 neumannH (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P'.1, P'.2, d, r) ρ)
        (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P'.1, P'.2, d, r) ρ)| ≤
      (Cb + (6 * C₁ + 4 * C₀) + 2 * (6 * C₁ + 4 * (C₀ * (T + 1)))) *
        dist P P' ^ (a * min a₁ 1 / 96) := by
  obtain ⟨b, hb⟩ : ∃ b, b = a * min a₁ 1 / 96 := ⟨_, rfl⟩
  rw [← hb]
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
  have hpT := hS hp
  have hp'T := hS hp'
  have hδ0 : 0 ≤ dist P P' := dist_nonneg
  have hδb : 0 ≤ dist P P' ^ b := Real.rpow_nonneg hδ0 _
  obtain ⟨hA, hmA⟩ := hAd P hp ρ hρ
  obtain ⟨hB, hmB⟩ := hAd P' hp' ρ hρ
  rw [abs_of_nonneg (kernelCov2_self_nonneg hA hB (hmA.trans hmB.symm))]
  rcases hδ0.eq_or_lt with hδz | hδpos
  · have hpp : P = P' := dist_eq_zero.1 hδz.symm
    subst hpp
    have : kernelCov2 neumannH (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P.1, P.2, d, r) ρ)
        (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P.1, P.2, d, r) ρ) = 0 := by
      unfold kernelCov2; ring
    rw [this]; positivity
  have hsmall := flowE2_small_le hAd hE1 hE0 hp hp' hρ
  have hρa : ρ ^ a₁ ≤ 1 := Real.rpow_le_one hρ.1 hρ.2 ha₁.le
  have hbig' := fun (hfar : dist P P' ≤ 1 / 2) (hcase : dist P P' ^ (a / 96) ≤ ρ) =>
    hbig P hp P' hp' hδpos hfar ρ hcase hρ.2
  generalize kernelCov2 neumannH (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P'.1, P'.2, d, r) ρ)
    (flowMu W (P.1, P.2, d, r) ρ, flowMu W (P'.1, P'.2, d, r) ρ) = E at hsmall hbig' ⊢
  have m1 := mul_nonneg hCb0 hδb
  have m2 := mul_nonneg hCs0 hδb
  have m3 := mul_nonneg hCf0 hδb
  have hsum : (Cb + (6 * C₁ + 4 * C₀) + 2 * (6 * C₁ + 4 * (C₀ * (T + 1)))) * dist P P' ^ b =
      Cb * dist P P' ^ b + (6 * C₁ + 4 * C₀) * dist P P' ^ b +
        2 * (6 * C₁ + 4 * (C₀ * (T + 1))) * dist P P' ^ b := by ring
  rw [hsum]
  by_cases hfar : 1 / 2 < dist P P'
  · have hδT : dist P P' ≤ T + 1 := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      refine max_le ?_ ?_ <;> rw [abs_le] <;> constructor <;>
        linarith [hpT.1, hpT.2.1, hpT.2.2, hp'T.1, hp'T.2.1, hp'T.2.2]
    have h1 : dist P P' ^ (a / 12) ≤ T + 1 := by
      refine (Real.rpow_le_rpow hδ0 hδT (by positivity)).trans ?_
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ T + 1 by linarith)
        (show a / 12 ≤ 1 by linarith)
      rwa [Real.rpow_one] at this
    have h2 : (1 : ℝ) ≤ 2 * dist P P' ^ b := by
      have h3 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ b :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hb1
      have h4 : (1 / 2 : ℝ) ^ b ≤ dist P P' ^ b := Real.rpow_le_rpow (by norm_num) hfar.le hb0.le
      rw [Real.rpow_one] at h3
      linarith
    have h5 := mul_le_mul_of_nonneg_left hρa hC₁
    have h6 := mul_le_mul_of_nonneg_left h1 hC₀
    have h7 := mul_le_mul_of_nonneg_left h2
      (by positivity : (0 : ℝ) ≤ 6 * C₁ + 4 * (C₀ * (T + 1)))
    nlinarith
  push Not at hfar
  have hδ1 : dist P P' ≤ 1 := by linarith
  by_cases hcase : dist P P' ^ (a / 96) ≤ ρ
  · have h := hbig' hfar hcase
    have h2 : dist P P' ^ (a / 48) ≤ dist P P' ^ b :=
      Real.rpow_le_rpow_of_exponent_ge hδpos hδ1 hb48
    have := mul_le_mul_of_nonneg_left h2 hCb0
    linarith
  · push Not at hcase
    have h1 : ρ ^ a₁ ≤ dist P P' ^ b := by
      refine (Real.rpow_le_rpow hρ.1 hcase.le ha₁.le).trans ?_
      rw [← Real.rpow_mul hδ0]
      exact Real.rpow_le_rpow_of_exponent_ge hδpos hδ1 hbaa
    have h2 : dist P P' ^ (a / 12) ≤ dist P P' ^ b :=
      Real.rpow_le_rpow_of_exponent_ge hδpos hδ1 hb12
    have := mul_le_mul_of_nonneg_left h1 hC₁
    have := mul_le_mul_of_nonneg_left h2 hC₀
    nlinarith

/-- **XFLOW-E2: the time modulus uniform over the box**, from the admissibility node and the
uniform radius modulus E1. -/
theorem flowE2Stmt_of_E1 (hA : FlowAdmStmt) (h1 : FlowE1Stmt) : FlowE2Stmt := by
  intro m W a CH hWH
  have hWH' := hWH
  obtain ⟨hW, hW0, ha, ha1, hCH, hH⟩ := hWH'
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 2 * (m : ℝ) + 2 := ⟨_, rfl⟩
  rw [← hTdef] at hWH hH
  have hT : 0 ≤ T := by rw [hTdef]; positivity
  obtain ⟨Mw, hMw'⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  have hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw := fun t ht => by
    simpa [Real.norm_eq_abs] using hMw' t ht
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  obtain ⟨rc, hrcdef⟩ : ∃ rc : ℝ, rc = 1 / ((m : ℝ) + 2) := ⟨_, rfl⟩
  have hrc : 0 < rc := by rw [hrcdef]; positivity
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = 3 * ((m : ℝ) + 2) := ⟨_, rfl⟩
  have hR₀ : 0 ≤ R₀ := by rw [hR₀def]; positivity
  have hbox : ∀ p ∈ flowBox m, (p.1, p.2.1) ∈ tri T ∧ rc ≤ p.2.2.2 ∧
      ‖p.2.2.1‖ + p.2.2.2 ≤ R₀ := by
    intro p hp
    obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩, ⟨h4a, h4b⟩, ⟨h5a, h5b⟩⟩ := hp
    refine ⟨⟨h1a, h2a, show p.1 + p.2.1 ≤ T by linarith⟩, by rw [hrcdef]; exact h5a, ?_⟩
    have hn := Complex.norm_le_abs_re_add_abs_im p.2.2.1
    have hre : |p.2.2.1.re| ≤ (m : ℝ) + 1 := abs_le.2 ⟨h3a, h3b⟩
    have him : |p.2.2.1.im| ≤ (m : ℝ) + 1 := abs_le.2 ⟨by linarith, h4b⟩
    rw [hR₀def]; linarith
  obtain ⟨C₁, a₁, hC₁, ha₁, hE1⟩ := h1 m W hW hW0
  obtain ⟨Cb, hCb0, hbig⟩ := flowE2_large_final hWH hT hMw hrc hR₀
  have hK0 := timeK_nonneg_E2 (R := R₀) hMw0 hT hrc hCH
  have hC₀ : 0 ≤ 2 * timeK Mw T rc R₀ CH := by positivity
  refine ⟨Cb + (6 * C₁ + 4 * (2 * timeK Mw T rc R₀ CH)) +
      2 * (6 * C₁ + 4 * ((2 * timeK Mw T rc R₀ CH) * (T + 1))), a * min a₁ 1 / 96,
    by positivity, div_pos (mul_pos ha (lt_min ha₁ one_pos)) (by norm_num), ?_⟩
  rintro ⟨u, s, d, r⟩ hp ⟨u', s', d', r'⟩ hp' hpp ρ hρ
  simp only [Prod.mk.injEq] at hpp
  obtain ⟨rfl, rfl⟩ := hpp
  have hdist : dist (u, s, d, r) (u', s', d, r) = dist (u, s) (u', s') := by
    simp only [Prod.dist_eq, dist_self]
    rw [max_eq_left dist_nonneg]
  rw [hdist]
  obtain ⟨-, hr, hdR⟩ := hbox _ hp
  have hS : {P : ℝ × ℝ | (P.1, P.2, d, r) ∈ flowBox m} ⊆ tri T := fun P hP => (hbox _ hP).1
  exact flowE2_circle_le (S := {P : ℝ × ℝ | (P.1, P.2, d, r) ∈ flowBox m}) (d := d) (r := r)
    ha ha1 hT hS hC₁ ha₁ hC₀ hCb0
    (fun P hP ρ hρ => hA W hW hW0 _ (flowBox_subset_flowPar m hP) ρ hρ)
    (fun P hP => hE1 _ hP)
    (fun P hP P' hP' => flowE2_zero_le hW hW0 hT hMw ha ha1 hCH hH hrc hr hdR (hS hP) (hS hP'))
    (fun P hP P' hP' => hbig d r hr hdR P (hS hP) P' (hS hP'))
    (P := (u, s)) (P' := (u', s')) hp hp' hρ

end F1
end QuantumZipper
