import QuantumZipper.Proofs.Zipper.XFlowEnergyE3Mix
import QuantumZipper.Proofs.Zipper.XFlowEnergyAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-ENERGY, E3 (3/3): the circle modulus `FlowE3Stmt`

**Main result** `flowE3Stmt_of_E1 : FlowAdmStmt → FlowE1Stmt → FlowE3Stmt`.

Interpolation in three regimes, as the D33 E2 proof (`RegUnif.energyParStmt_holds`), with
`δ = dist p p'` (same `(u, s)`, circles `(d, r)`, `(d', r')`), `x = δ^{1/96}`:

* `δ > 1/2`: the crude bound below and `1 ≤ 2 δ^b`;
* `ρ < x`: `energyCirc_small_le`, the triangle inequality through `μ_{p,0}` and `μ_{p',0}`: the
  radius legs are E1, the middle leg is the JointMod space modulus at `ρ = 0`
  (`μ_{p,0} = νT W d r (u+s)`, `abs_kernelCov2_νT_space_unif`);
* `ρ ≥ x`: `energyCirc_large_le` with strip width `τ = x^{24}`; the space-modulus constant is
  `O(x^{-2})` (`spaceK_mul_sq_le`) and every term is `O(x²) = O(δ^{1/48})`.

The constants are uniform on `flowBox m`: `T = 2m+2`, radii `≥ 1/(m+2)`, `‖d‖ + r ≤ 3(m+2)`.
Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1 (JointMod moduli); the interpolation
is an own elementary argument (as D33).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

open RegCont TwoPoint RegUnif B2

variable {W : ℝ → ℝ}

theorem norm_add_le_box {m : ℕ} {p : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ flowBox m) :
    ‖p.2.2.1‖ + p.2.2.2 ≤ 3 * ((m : ℝ) + 2) := by
  have h1 := Complex.norm_le_abs_re_add_abs_im p.2.2.1
  have h2 : |p.2.2.1.re| ≤ (m : ℝ) + 1 := abs_le.2 ⟨hp.2.2.1.1, hp.2.2.1.2⟩
  have h3 : |p.2.2.1.im| ≤ (m : ℝ) + 1 :=
    abs_le.2 ⟨by linarith [hp.2.2.2.1.1], hp.2.2.2.1.2⟩
  linarith [hp.2.2.2.2.2]

theorem circ_dist_le {p p' : ℝ × ℝ × ℂ × ℝ} :
    ‖p.2.2.1 - p'.2.2.1‖ + |p.2.2.2 - p'.2.2.2| ≤ 2 * dist p p' := by
  have h1 : dist p.2.2.1 p'.2.2.1 ≤ dist p p' := by
    rw [Prod.dist_eq (x := p), Prod.dist_eq (x := p.2), Prod.dist_eq (x := p.2.2)]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have h2 : dist p.2.2.2 p'.2.2.2 ≤ dist p p' := by
    rw [Prod.dist_eq (x := p), Prod.dist_eq (x := p.2), Prod.dist_eq (x := p.2.2)]
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  rw [Complex.dist_eq] at h1
  rw [Real.dist_eq] at h2
  linarith

/-- **The crude (small-radius) bound through `ρ = 0`.** -/
theorem energyCirc_small_le (hA : FlowAdmStmt) (hW : Continuous W) (hW0 : W 0 = 0) {m : ℕ}
    {Mw : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) (2 * (m : ℝ) + 2), |W t| ≤ Mw) {C₁ a₁ : ℝ}
    (hE1 : ∀ p ∈ flowBox m, ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (flowMu W p ρ, flowMu W p ρ') (flowMu W p ρ, flowMu W p ρ')| ≤
        C₁ * |ρ - ρ'| ^ a₁)
    {p p' : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ flowBox m) (hp' : p' ∈ flowBox m) (h1 : p.1 = p'.1)
    (h2 : p.2.1 = p'.2.1) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    kernelCov2 neumannH (flowMu W p ρ, flowMu W p' ρ) (flowMu W p ρ, flowMu W p' ρ) ≤
      6 * (C₁ * ρ ^ a₁) + 4 * (spaceK Mw (2 * (m : ℝ) + 2) (1 / ((m : ℝ) + 2))
        (3 * ((m : ℝ) + 2)) * (2 * dist p p') ^ (1 / 12 : ℝ)) := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hpP := flowBox_subset_flowPar m hp
  have hp'P := flowBox_subset_flowPar m hp'
  obtain ⟨ha, hma⟩ := hA W hW hW0 p hpP ρ hρ
  obtain ⟨hb, hmb⟩ := hA W hW hW0 p hpP 0 h01
  obtain ⟨hc, hmc⟩ := hA W hW hW0 p' hp'P 0 h01
  obtain ⟨hd, hmd⟩ := hA W hW hW0 p' hp'P ρ hρ
  have t1 := kernelCov2_self_triangle ha hb hd (hma.trans hmb.symm) (hmb.trans hmd.symm)
  have t2 := kernelCov2_self_triangle hb hc hd (hmb.trans hmc.symm) (hmc.trans hmd.symm)
  have e1 := (le_abs_self _).trans (hE1 p hp ρ hρ 0 h01)
  have e2 := (le_abs_self _).trans (hE1 p' hp' 0 h01 ρ hρ)
  rw [sub_zero, abs_of_nonneg hρ.1] at e1
  rw [zero_sub, abs_neg, abs_of_nonneg hρ.1] at e2
  -- the middle leg at `ρ = 0`
  obtain ⟨u, s, d, r⟩ := p
  obtain ⟨u', s', d', r'⟩ := p'
  simp only at h1 h2
  subst h1 h2
  have hm2 : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
  have hus : u + s ≤ 2 * (m : ℝ) + 2 := by linarith [hp.1.2, hp.2.1.2]
  have hr0 : 0 < r := hm2.trans_le hp.2.2.2.2.1
  have hr0' : 0 < r' := hm2.trans_le hp'.2.2.2.2.1
  have hu0 : 0 ≤ u := hp.1.1
  have hs0 : 0 ≤ s := hp.2.1.1
  rw [e3_flowMu_zero_eq hW hW0 hM hu0 hs0 hus d hr0] at t1 e1
  rw [e3_flowMu_zero_eq hW hW0 hM hu0 hs0 hus d' hr0'] at e2
  rw [e3_flowMu_zero_eq hW hW0 hM hu0 hs0 hus d hr0,
    e3_flowMu_zero_eq hW hW0 hM hu0 hs0 hus d' hr0'] at t2
  have hs := abs_kernelCov2_νT_space_unif hW hW0 hm2 hM (β := 1 / 12) (by norm_num) le_rfl
    ⟨add_nonneg hp.1.1 hp.2.1.1, hus⟩ hp.2.2.2.2.1 hp'.2.2.2.2.1 (norm_add_le_box hp)
    (norm_add_le_box hp')
  have hM0 : 0 ≤ Mw := (abs_nonneg _).trans (hM 0 ⟨le_rfl, by positivity⟩)
  have hsK := spaceK_nonneg_E2 (R := 3 * ((m : ℝ) + 2)) hM0 (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ) + 2) hm2
  have hcd := circ_dist_le (p := (u, s, d, r)) (p' := (u, s, d', r'))
  have hpow := Real.rpow_le_rpow (by positivity) hcd (by norm_num : (0 : ℝ) ≤ 1 / 12)
  have e3 := (le_abs_self _).trans (hs.trans (mul_le_mul_of_nonneg_left hpow hsK))
  dsimp only at t1 t2 e1 e2 e3 ⊢
  linarith

/-- **The large-radius regime**: `ρ ≥ δ^{1/96}`, `0 < δ ≤ 1` gives `E ≤ C δ^{1/48}`. -/
theorem energyCirc_large_final {m : ℕ} (hW : Continuous W) (hW0 : W 0 = 0) {Mw : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) (2 * (m : ℝ) + 2), |W t| ≤ Mw) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ flowBox m, ∀ p' ∈ flowBox m, p.1 = p'.1 → p.2.1 = p'.2.1 →
      0 < dist p p' → dist p p' ≤ 1 →
      ∀ ρ : ℝ, dist p p' ^ (1 / 96 : ℝ) ≤ ρ → ρ ≤ 1 →
        kernelCov2 neumannH (flowMu W p ρ, flowMu W p' ρ) (flowMu W p ρ, flowMu W p' ρ) ≤
          C * dist p p' ^ (1 / 48 : ℝ) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hT : (0 : ℝ) ≤ 2 * (m : ℝ) + 2 := by positivity
  have hM0 : 0 ≤ Mw := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hr₀ : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
  have hRd1 : (1 : ℝ) ≤ 3 * ((m : ℝ) + 2) := by linarith
  have hRb0 : 0 ≤ revBound (2 * Mw) (2 * (m : ℝ) + 2) (3 * ((m : ℝ) + 2)) :=
    revBound_nonneg (by linarith) hT
  obtain ⟨Lc, hLc⟩ : ∃ Lc : ℝ, Lc = (Real.sqrt ((3 * ((m : ℝ) + 2)) ^ 2 + 4 * (2 * (m : ℝ) + 2))
      + 1) * (3 * ((m : ℝ) + 2) + 1) := ⟨_, rfl⟩
  have hLc0 : 0 ≤ Lc := by rw [hLc]; positivity
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = |spaceKs Mw (2 * (m : ℝ) + 2)
      (revBound (2 * Mw) (2 * (m : ℝ) + 2) (3 * ((m : ℝ) + 2)) + 1)| := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hG]; exact abs_nonneg _
  have hc1 : 0 ≤ (2 * Lc) ^ (1 / 12 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hc2 : 0 ≤ (2 * revBound (2 * Mw) (2 * (m : ℝ) + 2) (3 * ((m : ℝ) + 2))) ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  refine ⟨2 * (G * (2 * Lc) ^ (1 / 12 : ℝ)) + 2 * (G * (2 * revBound (2 * Mw)
    (2 * (m : ℝ) + 2) (3 * ((m : ℝ) + 2))) ^ (1 / 12 : ℝ) * (1296 / (1 / ((m : ℝ) + 2)))),
    by positivity, fun p hp p' hp' h1 h2 hδpos hδ1 ρ hρ hρ1 => ?_⟩
  have hδ0 : 0 ≤ dist p p' := hδpos.le
  obtain ⟨x, hx⟩ : ∃ x, x = dist p p' ^ (1 / 96 : ℝ) := ⟨_, rfl⟩
  rw [← hx] at hρ
  have hx0 : 0 < x := by rw [hx]; exact Real.rpow_pos_of_pos hδpos _
  have hx1 : x ≤ 1 := by rw [hx]; exact Real.rpow_le_one hδ0 hδ1 (by norm_num)
  have hxpow : ∀ n : ℕ, x ^ n = dist p p' ^ (1 / 96 * (n : ℝ)) := fun n => by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hδ0]
  have eδ : dist p p' = x ^ 96 := by rw [hxpow 96]; norm_num
  have e48 : dist p p' ^ (1 / 48 : ℝ) = x ^ 2 := by rw [hxpow 2]; norm_num
  have hcd := circ_dist_le (p := p) (p' := p')
  have hpP := hp
  have hp'P := hp'
  obtain ⟨u, s, d, r⟩ := p
  obtain ⟨u', s', d', r'⟩ := p'
  simp only at h1 h2
  subst h1 h2
  have hus : u + s ≤ 2 * (m : ℝ) + 2 := by linarith [hp.1.2, hp.2.1.2]
  have hL := energyCirc_large_le hW hW0 hM hp.1.1 hp.2.1.1 hus hr₀ hp.2.2.2.2.1
    hp'.2.2.2.2.1 hRd1 (norm_add_le_box hp) (norm_add_le_box hp') hx0 hρ hρ1
    (τ := x ^ 24) (by positivity) (pow_le_one₀ hx0.le hx1) hcd
  rw [← hLc, eδ] at hL
  have eA : (Lc / x ^ 24 * (2 * x ^ 96)) ^ (1 / 12 : ℝ) = (2 * Lc) ^ (1 / 12 : ℝ) * x ^ 6 := by
    have : Lc / x ^ 24 * (2 * x ^ 96) = (2 * Lc) * (x ^ 6) ^ 12 := by
      field_simp
    rw [this, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (x ^ 6) 12,
      ← Real.rpow_mul (by positivity)]
    norm_num
  have eS : (36 * Real.sqrt (x ^ 24 / (1 / ((m : ℝ) + 2)))) ^ 2 =
      1296 * (x ^ 24 / (1 / ((m : ℝ) + 2))) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  rw [eA, eS] at hL
  rw [e48]
  set K := spaceK Mw (2 * (m : ℝ) + 2) x
    (revBound (2 * Mw) (2 * (m : ℝ) + 2) (3 * ((m : ℝ) + 2)) + 1) with hK
  have hK0 : 0 ≤ K := spaceK_nonneg_E2 hM0 hT hx0
  have hKG : K * x ^ 2 ≤ G :=
    (spaceK_mul_sq_le hM0 hT hx0 hx1).trans (by rw [hG]; exact le_abs_self _)
  have hle : ∀ n : ℕ, 2 ≤ n → x ^ n ≤ x ^ 2 := fun n hn => pow_le_pow_of_le_one hx0.le hx1 hn
  have k1 : K * x ^ 6 ≤ G * x ^ 2 := by
    calc K * x ^ 6 = (K * x ^ 2) * x ^ 4 := by ring
      _ ≤ G * x ^ 4 := mul_le_mul_of_nonneg_right hKG (by positivity)
      _ ≤ G * x ^ 2 := mul_le_mul_of_nonneg_left (hle 4 (by norm_num)) hG0
  have k2 : K * x ^ 24 ≤ G * x ^ 2 := by
    calc K * x ^ 24 = (K * x ^ 2) * x ^ 22 := by ring
      _ ≤ G * x ^ 22 := mul_le_mul_of_nonneg_right hKG (by positivity)
      _ ≤ G * x ^ 2 := mul_le_mul_of_nonneg_left (hle 22 (by norm_num)) hG0
  have i1 := mul_le_mul_of_nonneg_left k1 hc1
  have i2 := mul_le_mul_of_nonneg_left k2
    (mul_nonneg hc2 (by positivity : (0 : ℝ) ≤ 1296 / (1 / ((m : ℝ) + 2))))
  have eL : 2 * (K * ((2 * Lc) ^ (1 / 12 : ℝ) * x ^ 6)) + 2 * (K *
      (2 * revBound (2 * Mw) (2 * (m : ℝ) + 2) (3 * ((m : ℝ) + 2))) ^ (1 / 12 : ℝ) *
      (1296 * (x ^ 24 / (1 / ((m : ℝ) + 2))))) =
      2 * ((2 * Lc) ^ (1 / 12 : ℝ) * (K * x ^ 6)) +
      2 * (((2 * revBound (2 * Mw) (2 * (m : ℝ) + 2) (3 * ((m : ℝ) + 2))) ^ (1 / 12 : ℝ) *
        (1296 / (1 / ((m : ℝ) + 2)))) * (K * x ^ 24)) := by ring
  have eR : (2 * (G * (2 * Lc) ^ (1 / 12 : ℝ)) + 2 * (G * (2 * revBound (2 * Mw)
      (2 * (m : ℝ) + 2) (3 * ((m : ℝ) + 2))) ^ (1 / 12 : ℝ) * (1296 / (1 / ((m : ℝ) + 2))))) *
      x ^ 2 = 2 * ((2 * Lc) ^ (1 / 12 : ℝ) * (G * x ^ 2)) +
      2 * (((2 * revBound (2 * Mw) (2 * (m : ℝ) + 2) (3 * ((m : ℝ) + 2))) ^ (1 / 12 : ℝ) *
        (1296 / (1 / ((m : ℝ) + 2)))) * (G * x ^ 2)) := by ring
  rw [eL] at hL
  rw [eR]
  linarith

/-- **XFLOW-E3: the circle modulus**, from admissibility and the radius modulus. -/
theorem flowE3Stmt_of_E1 (hA : FlowAdmStmt) (h1 : FlowE1Stmt) : FlowE3Stmt := by
  intro m W a CH hWH
  have hW : Continuous W := hWH.1
  have hW0 : W 0 = 0 := hWH.2.1
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hT : (0 : ℝ) ≤ 2 * (m : ℝ) + 2 := by positivity
  obtain ⟨Mw, hMw'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hW.continuousOn (s := Icc 0 (2 * (m : ℝ) + 2)))
  have hM : ∀ t ∈ Icc (0 : ℝ) (2 * (m : ℝ) + 2), |W t| ≤ Mw := fun t ht => by
    simpa [Real.norm_eq_abs] using hMw' t ht
  have hM0 : 0 ≤ Mw := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  obtain ⟨C₁, a₁, hC₁, ha₁, hE1⟩ := h1 m W hW hW0
  obtain ⟨Cb, hCb0, hbig⟩ := energyCirc_large_final (m := m) hW hW0 hM
  have hr₀ : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
  obtain ⟨S0, hS0⟩ : ∃ S0 : ℝ, S0 = spaceK Mw (2 * (m : ℝ) + 2) (1 / ((m : ℝ) + 2))
      (3 * ((m : ℝ) + 2)) := ⟨_, rfl⟩
  have hS00 : 0 ≤ S0 := by rw [hS0]; exact spaceK_nonneg_E2 hM0 hT hr₀
  set L : ℝ := 4 * ((m : ℝ) + 2) with hL
  have hL0 : 0 ≤ L := by positivity
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = min a₁ 1 / 96 := ⟨_, rfl⟩
  have hmin0 : 0 < min a₁ 1 := lt_min ha₁ one_pos
  have hmin1 : min a₁ 1 ≤ 1 := min_le_right _ _
  have hmin2 : min a₁ 1 ≤ a₁ := min_le_left _ _
  have hb0 : 0 < b := by rw [hb]; positivity
  have hb1 : b ≤ 1 := by rw [hb]; linarith
  have hb48 : b ≤ 1 / 48 := by rw [hb]; linarith
  have hb12 : b ≤ 1 / 12 := by rw [hb]; linarith
  have hbaa : b ≤ 1 / 96 * a₁ := by rw [hb]; linarith
  have hCf0 : 0 ≤ 6 * C₁ + 8 * (S0 * (L + 1)) := by positivity
  refine ⟨Cb + (6 * C₁ + 8 * S0) + 2 * (6 * C₁ + 8 * (S0 * (L + 1))), b, by positivity, hb0,
    fun p hp p' hp' h1 h2 ρ hρ => ?_⟩
  have hδ0 : 0 ≤ dist p p' := dist_nonneg
  have hδb : 0 ≤ dist p p' ^ b := Real.rpow_nonneg hδ0 _
  obtain ⟨hA1, hmA⟩ := hA W hW hW0 p (flowBox_subset_flowPar m hp) ρ hρ
  obtain ⟨hB1, hmB⟩ := hA W hW hW0 p' (flowBox_subset_flowPar m hp') ρ hρ
  rw [abs_of_nonneg (kernelCov2_self_nonneg hA1 hB1 (hmA.trans hmB.symm))]
  rcases hδ0.eq_or_lt with hδz | hδpos
  · have hpp : p = p' := dist_eq_zero.1 hδz.symm
    subst hpp
    have : kernelCov2 neumannH (flowMu W p ρ, flowMu W p ρ)
        (flowMu W p ρ, flowMu W p ρ) = 0 := by unfold kernelCov2; ring
    rw [this]; positivity
  have hsmall := energyCirc_small_le hA hW hW0 hM hE1 hp hp' h1 h2 hρ
  rw [← hS0] at hsmall
  have h2d : (2 * dist p p') ^ (1 / 12 : ℝ) ≤ 2 * dist p p' ^ (1 / 12 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hδ0]
    have h2a : (2 : ℝ) ^ (1 / 12 : ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (1 / 12 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_right h2a (Real.rpow_nonneg hδ0 _)
  have hs2 := mul_le_mul_of_nonneg_left h2d hS00
  have hρa : ρ ^ a₁ ≤ 1 := Real.rpow_le_one hρ.1 hρ.2 ha₁.le
  have hbig' := fun (hfar : dist p p' ≤ 1) (hcase : dist p p' ^ (1 / 96 : ℝ) ≤ ρ) =>
    hbig p hp p' hp' h1 h2 hδpos hfar ρ hcase hρ.2
  generalize kernelCov2 neumannH (flowMu W p ρ, flowMu W p' ρ)
    (flowMu W p ρ, flowMu W p' ρ) = E at hsmall hbig' ⊢
  have m1 := mul_nonneg hCb0 hδb
  have m2 := mul_nonneg (by positivity : (0 : ℝ) ≤ 6 * C₁ + 8 * S0) hδb
  have m3 := mul_nonneg hCf0 hδb
  have hsum : (Cb + (6 * C₁ + 8 * S0) + 2 * (6 * C₁ + 8 * (S0 * (L + 1)))) * dist p p' ^ b =
      Cb * dist p p' ^ b + (6 * C₁ + 8 * S0) * dist p p' ^ b +
        2 * (6 * C₁ + 8 * (S0 * (L + 1))) * dist p p' ^ b := by ring
  rw [hsum]
  by_cases hfar : 1 / 2 < dist p p'
  · have hδL : dist p p' ≤ L := dist_le_of_flowBox hp hp'
    have h12 : dist p p' ^ (1 / 12 : ℝ) ≤ L + 1 := by
      by_cases hd1 : dist p p' ≤ 1
      · linarith [Real.rpow_le_one hδ0 hd1 (by norm_num : (0 : ℝ) ≤ 1 / 12)]
      · push Not at hd1
        have := Real.rpow_le_rpow_of_exponent_le hd1.le (show (1 / 12 : ℝ) ≤ 1 by norm_num)
        rw [Real.rpow_one] at this
        linarith
    have h2' : (1 : ℝ) ≤ 2 * dist p p' ^ b := by
      have h3 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ b :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hb1
      have h4 : (1 / 2 : ℝ) ^ b ≤ dist p p' ^ b := Real.rpow_le_rpow (by norm_num) hfar.le hb0.le
      rw [Real.rpow_one] at h3
      linarith
    have h5 := mul_le_mul_of_nonneg_left hρa hC₁
    have h6 := mul_le_mul_of_nonneg_left h12 hS00
    have h7 := mul_le_mul_of_nonneg_left h2' hCf0
    nlinarith
  push Not at hfar
  have hδ1 : dist p p' ≤ 1 := by linarith
  by_cases hcase : dist p p' ^ (1 / 96 : ℝ) ≤ ρ
  · have h := hbig' hδ1 hcase
    have h2' : dist p p' ^ (1 / 48 : ℝ) ≤ dist p p' ^ b :=
      Real.rpow_le_rpow_of_exponent_ge hδpos hδ1 hb48
    have := mul_le_mul_of_nonneg_left h2' hCb0
    linarith
  · push Not at hcase
    have h1' : ρ ^ a₁ ≤ dist p p' ^ b := by
      refine (Real.rpow_le_rpow hρ.1 hcase.le ha₁.le).trans ?_
      rw [← Real.rpow_mul hδ0]
      exact Real.rpow_le_rpow_of_exponent_ge hδpos hδ1 hbaa
    have h2' : dist p p' ^ (1 / 12 : ℝ) ≤ dist p p' ^ b :=
      Real.rpow_le_rpow_of_exponent_ge hδpos hδ1 hb12
    have := mul_le_mul_of_nonneg_left h1' hC₁
    have := mul_le_mul_of_nonneg_left h2' hS00
    nlinarith

end F1
end QuantumZipper
