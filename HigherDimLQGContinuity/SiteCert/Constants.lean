import HigherDimLQGContinuity.SiteCert.Setup

/-!
# The constant bookkeeping (4.11)–(4.12) of the site certificate (packet Q7b)

Source: blueprint Part B `b:def-order` (O6)–(O10), `b:lem-order`(c)–(d) with ruling N29 (packet Q3's
`siteConsts_spec`), and the polynomial clauses of the frozen interface `SiteCertOfLabel`: `e^{-poly(v⁻¹)} ≤ θ`, the
Cameron–Martin bound `C_bump ς^{-k_d} ≤ poly(v⁻¹)` and the catalogue bound. Here `poly(v⁻¹) = polyB A k 0 v⁻¹ =
A (1 + v⁻¹)^k`.

* `q7b_polyB_mono`, `q7b_polyB_nonneg`, `q7b_rpow_neg_le_polyBase`: monotonicity of `polyB` in the constant and the
  exponent, `v^{-K} ≤ (1 + v⁻¹)^K`.
* `q7b_exp_neg_polyB_le`: `c v^K ≤ θ ⇒ e^{-polyB(|log c| + K, 1)} ≤ θ`.
* `q7b_cm_le_polyB`: `c v^K ≤ ς ⇒ C ς^{-k} ≤ polyB(C c^{-k}, K k)`.
* `q7b_theta_lt_one`: `θ < 1` once `C_net ≥ 1` (then `A_net ≥ 1` and `θ ≤ ε₀ ≤ 1/512`).
* `Q7bConstOK`, `q7bConstOK_of_spec`: the facts about the constants that the certificate reads, at every
  `v ∈ (0, v_site]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-! ## Polynomial bounds -/

theorem q7b_polyBase_ge_one {v : ℝ} (hv : 0 < v) : (1 : ℝ) ≤ 1 + 0 + v⁻¹ := by
  have := inv_pos.2 hv
  linarith

theorem q7b_polyB_nonneg {A k v : ℝ} (hv : 0 < v) (hA : 0 ≤ A) : 0 ≤ polyB A k 0 v⁻¹ := by
  unfold polyB
  exact mul_nonneg hA (Real.rpow_nonneg (by linarith [q7b_polyBase_ge_one hv]) _)

/-- `polyB A k 0 v⁻¹ = A (1 + v⁻¹)^k` is monotone in `A ≥ 0` and in `k` (the base is `≥ 1`). -/
theorem q7b_polyB_mono {A A' k k' v : ℝ} (hv : 0 < v) (hA : 0 ≤ A) (hAA : A ≤ A') (hkk : k ≤ k') :
    polyB A k 0 v⁻¹ ≤ polyB A' k' 0 v⁻¹ := by
  unfold polyB
  have hb := q7b_polyBase_ge_one hv
  have h1 : (1 + 0 + v⁻¹) ^ k ≤ (1 + 0 + v⁻¹) ^ k' := Real.rpow_le_rpow_of_exponent_le hb hkk
  have h0 : 0 ≤ (1 + 0 + v⁻¹) ^ k := Real.rpow_nonneg (by linarith) _
  exact mul_le_mul hAA h1 h0 (hA.trans hAA)

/-- `v^{-K} ≤ (1 + v⁻¹)^K` for `K ≥ 0`. -/
theorem q7b_rpow_neg_le_polyBase {v K : ℝ} (hv : 0 < v) (hK : 0 ≤ K) :
    v ^ (-K) ≤ (1 + 0 + v⁻¹) ^ K := by
  rw [Real.rpow_neg hv.le, ← Real.inv_rpow hv.le]
  exact Real.rpow_le_rpow (inv_pos.2 hv).le (by linarith) hK

/-- A lower power bound `c v^K ≤ θ` gives the exponential clause of the interface. -/
theorem q7b_exp_neg_polyB_le {c K v θ : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hv : 0 < v)
    (hθ : c * v ^ K ≤ θ) : Real.exp (-polyB (|Real.log c| + K) 1 0 v⁻¹) ≤ θ := by
  have hx : 0 < v⁻¹ := inv_pos.2 hv
  have hvK : 0 < v ^ K := Real.rpow_pos_of_pos hv K
  have hcv : 0 < c * v ^ K := mul_pos hc hvK
  have hlog : Real.log (c * v ^ K) = Real.log c + K * Real.log v := by
    rw [Real.log_mul hc.ne' hvK.ne', Real.log_rpow hv]
  have hlv : -v⁻¹ ≤ Real.log v := by
    have h := Real.log_le_sub_one_of_pos hx
    rw [Real.log_inv] at h
    linarith
  have hKlv : K * (-v⁻¹) ≤ K * Real.log v := mul_le_mul_of_nonneg_left hlv hK
  have habs : -|Real.log c| ≤ Real.log c := neg_abs_le _
  have hcx : 0 ≤ |Real.log c| * v⁻¹ := mul_nonneg (abs_nonneg _) hx.le
  have hpoly : polyB (|Real.log c| + K) 1 0 v⁻¹ = (|Real.log c| + K) * (1 + 0 + v⁻¹) := by
    unfold polyB
    rw [Real.rpow_one]
  calc Real.exp (-polyB (|Real.log c| + K) 1 0 v⁻¹) ≤ Real.exp (Real.log (c * v ^ K)) := by
        apply Real.exp_le_exp.2
        rw [hpoly, hlog]
        nlinarith
    _ = c * v ^ K := Real.exp_log hcv
    _ ≤ θ := hθ

/-- A lower power bound `c v^K ≤ ς` turns the Cameron–Martin constant `C ς^{-k}` into a polynomial in `v⁻¹`. -/
theorem q7b_cm_le_polyB {Cb c K k ς v : ℝ} (hCb : 0 ≤ Cb) (hc : 0 < c) (hK : 0 ≤ K) (hk : 0 ≤ k)
    (hv : 0 < v) (hς : c * v ^ K ≤ ς) :
    Cb * ς ^ (-k) ≤ polyB (Cb * c ^ (-k)) (K * k) 0 v⁻¹ := by
  have hvK : 0 < v ^ K := Real.rpow_pos_of_pos hv K
  have hcv : 0 < c * v ^ K := mul_pos hc hvK
  have h1 : ς ^ (-k) ≤ (c * v ^ K) ^ (-k) := Real.rpow_le_rpow_of_nonpos hcv hς (by linarith)
  have h2 : (c * v ^ K) ^ (-k) = c ^ (-k) * v ^ (-(K * k)) := by
    rw [Real.mul_rpow hc.le hvK.le, ← Real.rpow_mul hv.le]
    congr 2
    ring
  have h3 := q7b_rpow_neg_le_polyBase hv (mul_nonneg hK hk)
  unfold polyB
  calc Cb * ς ^ (-k) ≤ Cb * (c ^ (-k) * v ^ (-(K * k))) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left h1 hCb
    _ ≤ Cb * (c ^ (-k) * (1 + 0 + v⁻¹) ^ (K * k)) := by
        gcongr
    _ = Cb * c ^ (-k) * (1 + 0 + v⁻¹) ^ (K * k) := by ring

/-! ## `θ < 1` -/

theorem q7b_siteEps0_le (S : SiteData d) : siteEps0 S.mc S.Hlo ≤ 1 / 512 := by
  have hH : 0 < S.Hlo := by linarith [S.Hlo_ge]
  have hinv : S.Hlo⁻¹ ≤ 1 := inv_le_one_of_one_le₀ S.Hlo_ge
  unfold siteEps0 siteBtrig siteAout
  have := min_le_right S.mc S.Hlo⁻¹
  linarith

/-- `θ < 1` once `C_net ≥ 1`: then `A_net = C_net H_up ν^{-8d} ≥ 1` and `θ ≤ ε₀/4 ≤ 1/2048`. -/
theorem q7b_theta_lt_one (S : SiteData d) (hd : 2 ≤ d) {Cnet : ℝ} (hCnet : 1 ≤ Cnet) (v : ℝ) :
    (siteConsts S Cnet v).θ < 1 := by
  set C := siteConsts S Cnet v with hCdef
  have hν := siteConsts_ν_pos S hd Cnet v
  have hν1 := siteConsts_ν_le_one S hd Cnet v
  have hpow : 1 ≤ C.ν ^ (-(8 * d : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
  have hAnet : 1 ≤ C.Anet := by
    change 1 ≤ Cnet * S.Hup * C.ν ^ (-(8 * d : ℝ))
    have hH := S.Hup_ge
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ Cnet * S.Hup * C.ν ^ (-(8 * d : ℝ)) := by gcongr
  have hnum : siteThetaNumerator S C.ν ≤ 1 / 512 :=
    (min_le_left _ _).trans (q7b_siteEps0_le S)
  have hnum0 : 0 ≤ siteThetaNumerator S C.ν := by
    unfold siteThetaNumerator siteDeltaFromNu
    have h1 : 0 < siteEps0 S.mc S.Hlo := siteData_eps0_pos S
    have h2 : 0 ≤ S.Hlo⁻¹ := inv_nonneg.2 (by linarith [S.Hlo_ge])
    have h3 : 0 < Routing.gpC1 4 := Routing.gpC1_pos (by norm_num)
    have h4 : 0 ≤ (Routing.gpC1 4 * C.ν ^ 3 / 4 / 2) ^ S.b := Real.rpow_nonneg (by positivity) _
    exact le_min h1.le (mul_nonneg h2 h4)
  change siteThetaNumerator S C.ν / (4 * C.Anet) < 1
  rw [div_lt_one (by linarith)]
  linarith

/-! ## The facts about the constants that the certificate reads -/

/-- The facts about the explicit constants `C` at the tolerance `v` that the certificate reads (all of them are
consequences of `siteConsts_spec`; `q7bConstOK_of_spec`). -/
structure Q7bConstOK (S : SiteData d) (C : SiteConsts) (v : ℝ) : Prop where
  hA : SiteConstsA S C
  hB : SiteConstsB S C v
  hC : SiteConstsC S C v
  v_pos : 0 < v
  v_le : v ≤ 1 / 100
  μ_pos : 0 < C.μ
  ν_pos : 0 < C.ν
  g_pos : 0 < C.g
  ω_pos : 0 < C.ω
  ς_pos : 0 < C.ς
  θ_pos : 0 < C.θ
  θ_lt : C.θ < 1
  t₀_pos : 0 < C.t₀
  t₀_le : C.t₀ ≤ 1 / 6
  ω_le_g : C.ω ≤ C.g
  eD_cost : S.Hup * (2 * C.eD) ^ S.s = v * S.seed.d₀ / 1000
  enet_eq : C.enet = C.θ * C.Anet
  eatt_eq : C.eatt = S.Hup * (4 * C.ς) ^ S.s

theorem q7bConstOK_of_spec (S : SiteData d) (hd : 2 ≤ d) {Cnet : ℝ} (hCnet : 1 ≤ Cnet) {v : ℝ}
    (hv : 0 < v) (hv1 : v ≤ 1 / 100) (hA : SiteConstsA S (siteConsts S Cnet v))
    (hB : SiteConstsB S (siteConsts S Cnet v) v) (hC : SiteConstsC S (siteConsts S Cnet v) v) :
    Q7bConstOK S (siteConsts S Cnet v) v := by
  have hCnet0 : 0 < Cnet := by linarith
  have hν := siteConsts_ν_pos S hd Cnet v
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  refine
    { hA := hA
      hB := hB
      hC := hC
      v_pos := hv
      v_le := hv1
      μ_pos := q5_siteConsts_μ_pos S hd Cnet v
      ν_pos := hν
      g_pos := by
        change 0 < 100 * d * (siteConsts S Cnet v).ν
        positivity
      ω_pos := by
        change 0 < siteOmegaCoeff d * (siteConsts S Cnet v).ν ^ 4
        have := siteOmegaCoeff_pos d (by omega)
        positivity
      ς_pos := siteConsts_varsigma_pos S hd Cnet v hCnet0 hv (by linarith)
      θ_pos := siteConsts_theta_pos S hd Cnet v hCnet0
      θ_lt := q7b_theta_lt_one S hd hCnet v
      t₀_pos := siteConsts_t₀_pos S Cnet v hv
      t₀_le := siteConsts_t₀_le_sixth S Cnet v hv (by linarith)
      ω_le_g := by
        refine (siteConsts_omega_le_nu S hd Cnet v).trans ?_
        change (siteConsts S Cnet v).ν ≤ 100 * d * (siteConsts S Cnet v).ν
        nlinarith
      eD_cost := q7b_eD_cost S Cnet hv
      enet_eq := rfl
      eatt_eq := rfl }

end HigherDimLQGContinuity
