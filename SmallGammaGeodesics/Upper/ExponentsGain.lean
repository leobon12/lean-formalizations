import SmallGammaGeodesics.Upper.Exponents
import SmallGammaGeodesics.Upper.Taylor

/-!
# The gain of one probe (blueprint `lem:gain`; BP2 detail D9; packet P-U2)

`probe_gain`: let `C₁, C₂, c_T` be the constants of Lemma T (`taylor_probe`) and
`c_* = 1/(8 max{C₁, 1})`. For every `ε > 0` there is `γ_* ∈ (0,1)` such that for `γ ∈ (0, γ_*]`,
with `ξ = ξ_γ` and `p = ξ Q_γ`: `1/2 ≤ p ≤ 2`; and for `j ≤ J_γ`, `a ∈ [0,1]`, `δ ≤ R ≤ 2ξ^{a/2}`,
`σ = ±1`, `r = c_β R ℓ_j^{1/8}` and `θ = σ c_* r`: `c_* r ≤ ε ℓ_j`, and every `Δ`-Euclidean geodesic
`η` (`ApproxGeod d η Δ`, `Δ ≤ ξ^{99/100}`) with `σ B_{j,a}(y_η) > r` satisfies
(a) `|Re η(t) − 1/2| ≤ 9/16` and `|Im η(t)| ≤ ℓ_j/16`, and
(b) `log ∫₀¹ exp(p log|ϕ'_{j,a,θ}(η(t))|) dt ≤ −(c_*/4) r²/ℓ_j`.

Proof (blueprint): take `γ_*` below the threshold of `dimension_input` (so `|p − 1| ≤ C ξ ≤ 1/2`)
and so small that `probe_exponents` holds at `ξ_γ ≤ γ` with `C₂' = C₂`, `c = c_*` and
`ε'' = min{ε, c_T}`. The clock geometry gives `|Re η(t) − t| ≤ 3Δ ≤ 3ξ^a` and
`|Im η(t)| ≤ M(η) ≤ √(3Δ) ≤ √3 ξ^{a/2}` (`ApproxGeod.clock_bounds`). Lemma T applies with
`Δ_T = 3ξ^a`, `M_T = √3 ξ^{a/2}` and `|θ| = c_* r ≤ c_T ℓ_j`: its first term is at most
`−(c_*/2) r²/ℓ` (since `θ B = c_* r · σB > c_* r²` and `p ≥ 1/2`), the second is
`C₁ c_*² r²/ℓ ≤ (c_*/8) r²/ℓ`, and the error term is at most `(c_*/8) r²/ℓ` by (X4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-- `|Im η(t)| ≤ M(η)`: every point of `[0,1]` is real. -/
theorem abs_im_le_maxDev (η : C(unitInterval, ℂ)) (t : unitInterval) :
    |(η t).im| ≤ maxDev η := by
  refine le_trans ?_ (le_maxDev η t)
  refine (Metric.le_infDist ⟨0, left_mem_segment ℝ 0 1⟩).2 fun p hp => ?_
  rw [segment_eq_image] at hp
  obtain ⟨b, -, rfl⟩ := hp
  rw [dist_eq_norm]
  refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
  simp

/-- **Clock bounds** (blueprint `lem:clock`): on a `Δ`-Euclidean geodesic with `Δ ≤ x`,
`|Re η(t) − t| ≤ 3x` and `|Im η(t)| ≤ M(η) ≤ √(3Δ) ≤ √3 √x`. -/
theorem ApproxGeod.clock_bounds {d : ℂ × ℂ → ℝ} {η : C(unitInterval, ℂ)} {Δ x : ℝ}
    (h : ApproxGeod d η Δ) (hx : Δ ≤ x) (t : unitInterval) :
    |(η t).re - t| ≤ 3 * x ∧ |(η t).im| ≤ Real.sqrt 3 * Real.sqrt x := by
  refine ⟨(h.abs_re_sub_le t).trans (by linarith), ?_⟩
  calc |(η t).im| ≤ maxDev η := abs_im_le_maxDev η t
    _ ≤ Real.sqrt (3 * Δ) := h.maxDev_le_sqrt
    _ ≤ Real.sqrt (3 * x) := Real.sqrt_le_sqrt (by linarith)
    _ = Real.sqrt 3 * Real.sqrt x := Real.sqrt_mul (by norm_num) x

/-- **Lemma `lem:gain`** (the gain of one probe; BP2 D9). -/
theorem probe_gain : ∃ cs, 0 < cs ∧ ∀ ε, 0 < ε → ∃ γs, 0 < γs ∧ γs < 1 ∧ ∀ γ ∈ Ioc (0:ℝ) γs,
    1/2 ≤ xiGamma γ * Q γ ∧ xiGamma γ * Q γ ≤ 2 ∧
    ∀ j ≤ Jg γ, ∀ a ∈ Icc (0:ℝ) 1, ∀ R, dlt γ ≤ R → R ≤ 2 * xiGamma γ ^ (99/200 : ℝ) →
      ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      cs * (cBeta * R * ell j ^ (1/8 : ℝ)) ≤ ε * ell j ∧
      ∀ (d : ℂ × ℂ → ℝ) (η : C(unitInterval, ℂ)) (Δ : ℝ), ApproxGeod d η Δ →
        Δ ≤ xiGamma γ ^ (99/100 : ℝ) →
        cBeta * R * ell j ^ (1/8 : ℝ) < σ * band (yPath η) j a →
        (∀ t, |(η t).re - 1/2| ≤ 9/16 ∧ |(η t).im| ≤ ell j / 16) ∧
        Real.log (∫ t in (0:ℝ)..1, Real.exp (xiGamma γ * Q γ * Real.log ‖deriv
            (probeMap j a (σ * cs * (cBeta * R * ell j ^ (1/8 : ℝ))))
              (η (Set.projIcc 0 1 zero_le_one t))‖)) ≤
          -(cs / 4) * (cBeta * R * ell j ^ (1/8 : ℝ)) ^ 2 / ell j := by
  obtain ⟨C₁, C₂, cT, -, -, hcT, -, htay⟩ := taylor_probe
  have hCm : 0 < max C₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set cs : ℝ := 1 / (8 * max C₁ 1) with hcsdef
  have hcs : 0 < cs := by positivity
  have hcsabs : |cs| = cs := abs_of_pos hcs
  -- `C₁ c_* ≤ 1/8`
  have hC₁cs : C₁ * cs ≤ 1 / 8 := by
    rw [hcsdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have := le_max_left C₁ 1
    linarith
  refine ⟨cs, hcs, fun ε hε => ?_⟩
  -- the thresholds: `dimension_input` and `probe_exponents`
  obtain ⟨γd, Cd, hγd, hdim⟩ := dimension_input
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (probe_exponents C₂ cs 0 (min ε cT) (lt_min hε hcT))
  have hu0 : (0 : ℝ) < u := hu
  have hCd1 : 0 < 2 * |Cd| + 2 := by positivity
  refine ⟨min (min γd (1 / 2)) (min (u / 2) (1 / (2 * |Cd| + 2))),
    lt_min (lt_min hγd (by norm_num)) (lt_min (by linarith) (by positivity)),
    (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num)), fun γ hγ => ?_⟩
  obtain ⟨hγ0, hγγs⟩ := hγ
  have hγd' : γ ≤ γd := hγγs.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγu : γ ≤ u / 2 := hγγs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγC : γ ≤ 1 / (2 * |Cd| + 2) :=
    hγγs.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hpQ, hξlo, hξγ⟩ := hdim γ ⟨hγ0, hγd'⟩
  set ξ := xiGamma γ with hξdef
  have hξ0 : 0 < ξ := lt_of_lt_of_le (by linarith) hξlo
  -- `|p − 1| ≤ C ξ ≤ 1/2`
  have hCξ : Cd * ξ ≤ 1 / 2 := by
    have h1 : Cd * ξ ≤ |Cd| * ξ := mul_le_mul_of_nonneg_right (le_abs_self Cd) hξ0.le
    have h2 : |Cd| * ξ ≤ |Cd| * (1 / (2 * |Cd| + 2)) :=
      mul_le_mul_of_nonneg_left (hξγ.trans hγC) (abs_nonneg Cd)
    have h3 : |Cd| * (1 / (2 * |Cd| + 2)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ hCd1 (by norm_num)]
      linarith [abs_nonneg Cd]
    linarith
  have hp := abs_le.1 (hpQ.trans hCξ)
  have hp1 : 1 / 2 ≤ ξ * Q γ := by linarith [hp.1]
  have hp2 : ξ * Q γ ≤ 2 := by linarith [hp.2]
  refine ⟨hp1, hp2, ?_⟩
  -- the exponents at `ξ = ξ_γ`
  obtain ⟨-, hξa, -, hlev⟩ := hsub ⟨hξ0, by linarith⟩
  have hsq : Real.sqrt (ξ ^ (99 / 100 : ℝ)) = ξ ^ (99 / 200 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hξ0.le]
    norm_num
  intro j hj a ha R hR1 hR2 σ hσ
  have hℓ := ell_pos j
  obtain ⟨hΔℓ, hMℓ, hθε, -, hX4⟩ := hlev j hj R hR1 hR2
  have hR0 : 0 < R := lt_of_lt_of_le (Real.rpow_pos_of_pos hξ0 _) hR1
  set r := cBeta * R * ell j ^ (1 / 8 : ℝ) with hrdef
  have hr0 : 0 < r := mul_pos (mul_pos cBeta_pos hR0) (Real.rpow_pos_of_pos hℓ _)
  have hθε' : cs * r ≤ min ε cT * ell j := by rwa [hcsabs] at hθε
  refine ⟨hθε'.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hℓ.le), ?_⟩
  intro d η Δ hA hΔ hband
  -- (a) the localization
  have hclock : ∀ t : unitInterval, |(η t).re - t| ≤ 3 * ξ ^ (99 / 100 : ℝ) ∧
      |(η t).im| ≤ Real.sqrt 3 * ξ ^ (99 / 200 : ℝ) := by
    intro t
    have h := hA.clock_bounds hΔ t
    rw [hsq] at h
    exact h
  have hloc : ∀ t : unitInterval, |(η t).re - 1/2| ≤ 9/16 ∧ |(η t).im| ≤ ell j / 16 := by
    intro t
    obtain ⟨h1, h2⟩ := hclock t
    refine ⟨?_, h2.trans hMℓ⟩
    have h3 : |(t : ℝ) - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
    have h4 := abs_sub_le (η t).re (t : ℝ) (1 / 2)
    linarith
  refine ⟨hloc, ?_⟩
  -- (b) Lemma T with `Δ_T = 3ξ^a`, `M_T = √3 ξ^{a/2}`, `θ = σ c_* r`
  set θ := σ * cs * r with hθdef
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hσsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hθabs : |θ| = cs * r := by
    rw [hθdef, abs_mul, abs_mul, hσabs, one_mul, hcsabs, abs_of_pos hr0]
  have hθ2 : θ ^ 2 = (cs * r) ^ 2 := by
    rw [hθdef, mul_assoc, mul_pow, hσsq, one_mul]
  have hθ4 : θ ^ 4 = (cs * r) ^ 4 := by
    rw [show θ ^ 4 = (θ ^ 2) ^ 2 by ring, hθ2]
    ring
  have hθcT : |θ| ≤ cT * ell j := by
    rw [hθabs]
    exact hθε'.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hℓ.le)
  have hM0 : 0 ≤ Real.sqrt 3 * ξ ^ (99 / 200 : ℝ) := by positivity
  have hT := htay j a ha (ξ * Q γ) θ (3 * ξ ^ (99 / 100 : ℝ)) (Real.sqrt 3 * ξ ^ (99 / 200 : ℝ))
    η hp1 hp2 hθcT (by positivity) hΔℓ hM0 (by linarith) (fun t => (hclock t).1)
    (fun t => (hclock t).2)
  -- the first term: `θ B = c_* r σB > c_* r²` and `p ≥ 1/2`
  have T1 : -(ξ * Q γ) * (θ / ell j) * band (yPath η) j a ≤ -(cs / 2) * r ^ 2 / ell j := by
    have hθB : cs * r * r ≤ θ * band (yPath η) j a := by
      have e : θ * band (yPath η) j a = cs * r * (σ * band (yPath η) j a) := by
        rw [hθdef]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hband.le (by positivity)
    have h1 : 1 / 2 * (cs * r * r) ≤ ξ * Q γ * (θ * band (yPath η) j a) := by
      have h0 : 0 ≤ cs * r * r := by positivity
      calc 1 / 2 * (cs * r * r) ≤ ξ * Q γ * (cs * r * r) := mul_le_mul_of_nonneg_right hp1 h0
        _ ≤ ξ * Q γ * (θ * band (yPath η) j a) :=
            mul_le_mul_of_nonneg_left hθB (by linarith)
    have e1 : -(ξ * Q γ) * (θ / ell j) * band (yPath η) j a =
        -(ξ * Q γ * (θ * band (yPath η) j a)) * (ell j)⁻¹ := by ring
    have e2 : -(cs / 2) * r ^ 2 / ell j = -(1 / 2 * (cs * r * r)) * (ell j)⁻¹ := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_pos.2 hℓ).le
  -- the second term: `C₁ c_*² r²/ℓ ≤ (c_*/8) r²/ℓ`
  have T2 : C₁ * θ ^ 2 / ell j ≤ cs / 8 * r ^ 2 / ell j := by
    rw [hθ2]
    refine div_le_div_of_nonneg_right ?_ hℓ.le
    have h0 : 0 ≤ cs * r ^ 2 := by positivity
    calc C₁ * (cs * r) ^ 2 = (C₁ * cs) * (cs * r ^ 2) := by ring
      _ ≤ 1 / 8 * (cs * r ^ 2) := mul_le_mul_of_nonneg_right hC₁cs h0
      _ = cs / 8 * r ^ 2 := by ring
  -- the error term: (X4)
  have T3 : C₂ * (|θ| * (Real.sqrt 3 * ξ ^ (99 / 200 : ℝ)) * (3 * ξ ^ (99 / 100 : ℝ)) / ell j ^ 2 +
      (|θ| * (Real.sqrt 3 * ξ ^ (99 / 200 : ℝ)) ^ 3 +
        θ ^ 2 * (Real.sqrt 3 * ξ ^ (99 / 200 : ℝ)) ^ 2 +
        |θ| ^ 3 * (Real.sqrt 3 * ξ ^ (99 / 200 : ℝ)) + θ ^ 4) / ell j ^ 3) ≤
      cs / 8 * r ^ 2 / ell j := by
    rw [hθabs, hθ2, hθ4]
    rw [hcsabs] at hX4
    exact hX4
  calc _ ≤ _ := hT
    _ ≤ -(cs / 2) * r ^ 2 / ell j + cs / 8 * r ^ 2 / ell j + cs / 8 * r ^ 2 / ell j :=
        add_le_add (add_le_add T1 T2) T3
    _ = -(cs / 4) * r ^ 2 / ell j := by ring

end SmallGammaGeodesics
