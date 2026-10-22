import HigherDimLQGContinuity.Amplify.BandDet
import HigherDimLQGContinuity.Amplify.Geodesic
import HigherDimLQGContinuity.Amplify.Grid

/-!
# Proposition 3.3, the deterministic step (packet P7)

Blueprint `a:prop33`, "Band recursion": on the intersection of the events (G1)–(G5), for `x, y ∈ B̄_R` take a
`ρ^D`-geodesic `P` parametrized by length; it stays in `B_W` (`W = S (R + 1)`, (G1)); the envelope (G2) gives the
two-sided modulus `(ii)` of Lemma 3.1(b) with `H = 2 H̄`; Lemma 3.2 at radius `W + 2` (G3) gives the start
`(C₀, e₀)`; each band `j < N` (radii `2^{-k} ∈ [e^{-2V_j}, e^{-V_j}]`, (G4)) provides the finite family of good grid
balls with the crossing/diameter bounds and the connector coefficient `b'` ((G5) and `connector_of_good`). The band
recursion `p7_band_iter` then gives `ρ^E(x, y) ≤ (b' + X_N) ρ^D(x, y) + e_N` (`p7_amplify_det`), for any numbers
`X_j, e_j` satisfying the one-step inequalities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)
open HigherDimLQGMetric
open scoped ENNReal

variable {d : ℕ}

/-- The two-sided modulus `(ii)` of Lemma 3.1(b) with `H = 2 H̄` from the Hölder envelope bounds with `H̄`. -/
theorem p7_mod_of_envelope (G : ContMetric d) {Renv Hbar σ β : ℝ} (hHbar : 1 ≤ Hbar) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1)
    (henvU : ∀ z ∈ closedBall (0 : Rd d) Renv, ∀ s ∈ Ioc (0 : ℝ) 1,
      diamIn G (ball z (2 * s)) (ball z s) ≤ ENNReal.ofReal (Hbar * s ^ σ))
    (henvL : ∀ x ∈ closedBall (0 : Rd d) Renv, ∀ y ∈ closedBall (0 : Rd d) Renv,
      Hbar⁻¹ * ‖x - y‖ ^ β ≤ G.1 (x, y)) :
    ∀ x ∈ closedBall (0 : Rd d) Renv, ∀ y ∈ closedBall (0 : Rd d) Renv, ‖x - y‖ ≤ 1 / 2 →
      G.1 (x, y) ≤ (2 * Hbar) * ‖x - y‖ ^ σ ∧ (2 * Hbar)⁻¹ * ‖x - y‖ ^ β ≤ G.1 (x, y) := by
  intro x hx y hy hxy
  have hH0 : 0 < Hbar := by linarith
  constructor
  · rcases eq_or_ne x y with rfl | hne
    · rw [G.apply_self, sub_self, norm_zero, Real.zero_rpow hσ.ne', mul_zero]
    · have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      set t := 2 * ‖x - y‖ with ht
      have ht0 : 0 < t := by positivity
      have ht1 : t ∈ Ioc (0 : ℝ) 1 := ⟨ht0, by linarith⟩
      have hxB : x ∈ ball x t := mem_ball_self ht0
      have hyB : y ∈ ball x t := by
        rw [mem_ball, dist_eq_norm, norm_sub_rev]; linarith
      have hle := p7_apply_le_of_diamIn_le G hxB hyB (by positivity) (henvU x hx t ht1)
      have h2 : t ^ σ ≤ 2 * ‖x - y‖ ^ σ := by
        rw [ht, Real.mul_rpow (by norm_num) hpos.le]
        have h2σ : (2 : ℝ) ^ σ ≤ 2 := by
          calc (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
            _ = 2 := Real.rpow_one 2
        exact mul_le_mul_of_nonneg_right h2σ (Real.rpow_nonneg hpos.le _)
      calc G.1 (x, y) ≤ Hbar * t ^ σ := hle
        _ ≤ Hbar * (2 * ‖x - y‖ ^ σ) := mul_le_mul_of_nonneg_left h2 hH0.le
        _ = (2 * Hbar) * ‖x - y‖ ^ σ := by ring
  · have h := henvL x hx y hy
    have hinv : (2 * Hbar)⁻¹ ≤ Hbar⁻¹ := inv_anti₀ hH0 (by linarith)
    have hnn : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
    calc (2 * Hbar)⁻¹ * ‖x - y‖ ^ β ≤ Hbar⁻¹ * ‖x - y‖ ^ β := mul_le_mul_of_nonneg_right hinv hnn
      _ ≤ G.1 (x, y) := h

/-- **Deterministic step of Proposition 3.3.** -/
theorem p7_amplify_det (hd : 2 ≤ d) (Rm Qm : ContMetric d) (hRlen : Rm.IsLength)
    (hgeod : ∀ x y : Rd d, ∃ γ : C(unitInterval, Rd d), IsConstSpeedGeod Rm x y γ)
    {R S Hbar σ β m M b' C0 e0 : ℝ} (hR : 0 ≤ R) (hS : 4 ≤ S) (hHbar : 1 ≤ Hbar) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hβ : 0 < β) (hm : 0 < m) (hM : 0 < M) (hmM : m ≤ M) (hb' : 0 ≤ b')
    (hesc : diamIn Rm (ball (0 : Rd d) (2 * (R + 1))) (ball (0 : Rd d) (R + 1)) <
      setDistIn Rm univ (sphere (0 : Rd d) (2 * (R + 1))) (sphere (0 : Rd d) (S * (R + 1))))
    (henvU : ∀ z ∈ closedBall (0 : Rd d) (S * (R + 1) + 1), ∀ s ∈ Ioc (0 : ℝ) 1,
      diamIn Rm (ball z (2 * s)) (ball z s) ≤ ENNReal.ofReal (Hbar * s ^ σ))
    (henvL : ∀ x ∈ closedBall (0 : Rd d) (S * (R + 1) + 1), ∀ y ∈ closedBall (0 : Rd d) (S * (R + 1) + 1),
      Hbar⁻¹ * ‖x - y‖ ^ β ≤ Rm.1 (x, y))
    (hrough : CompOn Qm Rm C0 e0 (S * (R + 1) + 2))
    (N : ℕ) (V : ℕ → ℝ) (good : SewBall d → Prop) (SR : SewBall d → ℝ)
    (hV : ∀ j < N, Real.log 4 ≤ V j)
    (hcov : ∀ j < N, ∀ x ∈ closedBall (0 : Rd d) (S * (R + 1)), ∃ k ∈ p4_fullScales (V j),
      ∃ i : Fin d → ℤ, ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) i‖ < p4_radius k / 10 ∧
        good (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) i, p4_radius k))
    (hgood : ∀ j < N, ∀ B ∈ p7BandSet d (V j) (S * (R + 1)) good, 0 < SR B ∧
      ENNReal.ofReal (m * SR B) ≤ setDistIn Rm univ (sphere B.1 (3 * B.2 / 4)) (sphere B.1 B.2) ∧
      diamIn Rm (ann B.1 (B.2 / 2) (7 * B.2 / 2)) (sphere B.1 B.2) ≤ ENNReal.ofReal (M * SR B) ∧
      ∀ (P' : ℝ → Rd d) (u v : ℝ), u ≤ v →
        (∀ a ∈ Icc u v, ∀ a' ∈ Icc u v, Rm.1 (P' a, P' a') = |a - a'|) →
        P' '' Icc u v ⊆ annCl B.1 (3 * B.2 / 4) B.2 →
        ((‖P' u - B.1‖ = B.2 ∧ ‖P' v - B.1‖ = 3 * B.2 / 4) ∨
          (‖P' u - B.1‖ = 3 * B.2 / 4 ∧ ‖P' v - B.1‖ = B.2)) →
        Qm.1 (P' u, P' v) ≤ b' * (v - u))
    (X e : ℕ → ℝ) (hX : ∀ j ≤ N, 0 ≤ X j) (he : ∀ j ≤ N, 0 ≤ e j) (hX0 : C0 ≤ X 0) (he0 : e0 ≤ e 0)
    (hstepC : ∀ j < N,
      (1 - m / (2 * M)) * X j + e j / ((2 * Hbar)⁻¹ * (Real.exp (-2 * V j) / 4) ^ β) ≤ X (j + 1))
    (hstepe : ∀ j < N,
      (b' + X j) * (2 * (2 * Hbar) * (2 * Real.exp (-V j)) ^ σ) + e j ≤ e (j + 1)) :
    CompOn Qm Rm (b' + X N) (e N) R := by
  intro x hx y hy
  obtain ⟨γ, hγ⟩ := hgeod x y
  obtain ⟨hP0, hPℓ, hgeo⟩ := p7_geodPath_spec Rm hγ
  set P := p7_geodPath Rm x y γ with hPdef
  set ℓ := Rm.1 (x, y) with hℓdef
  have hℓ : 0 ≤ ℓ := Rm.nonneg x y
  have hPc : Continuous P := p7_continuous_geodPath Rm x y γ
  have hxn : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
  have hyn : ‖y‖ ≤ R := mem_closedBall_zero_iff.mp hy
  have hxb : P 0 ∈ ball (0 : Rd d) (R + 1) := by rw [hP0, mem_ball_zero_iff]; linarith
  have hyb : P ℓ ∈ ball (0 : Rd d) (R + 1) := by rw [hPℓ, mem_ball_zero_iff]; linarith
  have hconf := p7_geod_confined Rm hℓ hPc (by linarith : (2 : ℝ) ≤ S) (by linarith : 0 < R + 1)
    hgeo hxb hyb hesc
  set W := S * (R + 1) with hWdef
  have hW0 : 0 ≤ W := by positivity
  have hPW : ∀ u ∈ Icc (0 : ℝ) ℓ, ‖P u‖ ≤ W := fun u hu => (hconf u hu).le
  have hd1 : 1 ≤ d := by omega
  have hV0 : ∀ j < N, 0 ≤ V j := fun j hj =>
    le_trans (Real.log_nonneg (by norm_num)) (hV j hj)
  -- the families of the bands (junk empty family for `j ≥ N`)
  classical
  let F : ℕ → Finset (SewBall d) := fun j =>
    if hj : j < N then p7BandFinset hd1 (hV0 j hj) hW0 good else ∅
  have hFmem : ∀ j (hj : j < N) (B : SewBall d), B ∈ F j ↔ B ∈ p7BandSet d (V j) W good := by
    intro j hj B
    simp only [F, hj, ↓reduceDIte]
    exact p7_mem_bandFinset hd1 (hV0 j hj) hW0
  have hmod := p7_mod_of_envelope Rm hHbar hσ hσ1 henvU henvL
  have hrp4 : ∀ j < N, Real.exp (-V j) ≤ 1 / 4 := by
    intro j hj
    have h : Real.exp (-V j) ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by linarith [hV j hj])
    have h4 : Real.exp (-Real.log 4) = 1 / 4 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    linarith
  have hbase : ∀ u ∈ Icc (0 : ℝ) ℓ, ∀ v ∈ Icc (0 : ℝ) ℓ,
      Qm.1 (P u, P v) ≤ (b' + X 0) * |u - v| + e 0 := by
    intro u hu v hv
    have hu' : P u ∈ closedBall (0 : Rd d) (W + 2) :=
      mem_closedBall_zero_iff.mpr (by linarith [hPW u hu])
    have hv' : P v ∈ closedBall (0 : Rd d) (W + 2) :=
      mem_closedBall_zero_iff.mpr (by linarith [hPW v hv])
    have h := hrough (P u) hu' (P v) hv'
    rw [hgeo u hu v hv] at h
    have habs : 0 ≤ |u - v| := abs_nonneg _
    have h1 : C0 * |u - v| ≤ (b' + X 0) * |u - v| :=
      mul_le_mul_of_nonneg_right (by linarith) habs
    linarith
  have hiter := p7_band_iter hd Rm Qm hRlen P ℓ W hℓ hW0 hgeo hPW hm hM hmM hb'
    (by linarith : (1 : ℝ) ≤ 2 * Hbar) hσ hβ hmod N (fun j => Real.exp (-2 * V j))
    (fun j => Real.exp (-V j)) X e F SR
    (fun j _ => Real.exp_pos _)
    (fun j hj => Real.exp_le_exp.mpr (by linarith [hV0 j hj]))
    hrp4
    (fun j hj B hB => by
      rw [hFmem j hj] at hB
      have hr := p7BandSet_radius (hV0 j hj) hB
      exact ⟨hr.1, hr.2, (hgood j hj B hB).1⟩)
    (fun j hj u hu => by
      obtain ⟨B, hB, hPB⟩ := p7_band_cover (hV0 j hj) (hcov j hj) (P u)
        (mem_closedBall_zero_iff.mpr (hPW u hu))
      exact ⟨B, (hFmem j hj B).mpr hB, hPB⟩)
    (fun j hj B hB => by
      rw [hFmem j hj] at hB
      exact (hgood j hj B hB).2.1)
    (fun j hj B hB => by
      rw [hFmem j hj] at hB
      exact (hgood j hj B hB).2.2.1)
    (fun j hj B hB u hu v hv huv hsub hends => by
      rw [hFmem j hj] at hB
      refine (hgood j hj B hB).2.2.2 P u v huv ?_ hsub hends
      intro a ha a' ha'
      exact hgeo a ⟨hu.1.trans ha.1, ha.2.trans hv.2⟩ a' ⟨hu.1.trans ha'.1, ha'.2.trans hv.2⟩)
    hX he hstepC hstepe hbase
  have h := hiter 0 ⟨le_rfl, hℓ⟩ ℓ ⟨hℓ, le_rfl⟩ hℓ
  rw [hP0, hPℓ, sub_zero] at h
  exact h

end HigherDimLQGContinuity
