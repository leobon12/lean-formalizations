import HigherDimLQGMetric.Modulus.Tilt
import HigherDimLQGMetric.Modulus.Potential
import HigherDimLQGMetric.Modulus.BallDiam
import HigherDimLQGMetric.Core.Interfaces

/-!
# One ball: the moment bound of MA1 A8, Step 1 (packet W3b, [S] Lemma 2.6)

For a sharp assignment `D` satisfying (E5) (`E5SharpMoment`, the interface proved by W3),
`p ∈ (0, Q/ξ)`, `0 < 2t ≤ R` and `|z| ≤ A R` (`w3b_oneBall_moment`):

  `E[(s_R(0)⁻¹ sup_{x,y ∈ B̄_t(z)} D_h(x,y))^p] ≤ C (2t/R)^{ξQp − ξ²p²/2}`,

with `C` depending only on `d, ξ, Q, D, p, A` (uniform over LGFs, `R`, `t`, `z`).

Proof (MA1 A8, Step 1). With `X = h_{2t}(z) − h_R(0)`, `a = ξp`:
`s_R(0)⁻¹ = (2t/R)^{ξQ} e^{ξX} · (2t)^{-ξQ} e^{-ξ h_{2t}(z)}` (`w3b_sNorm_inv_eq`), so
`E[(s_R⁻¹ Δ)^p] = (2t/R)^{ξQp} e^{a² Var X/2} E'[Ψ^p]` where `E'` is the expectation under the
tilted measure `P' = e^{aX − a² Var X/2} P` and `Ψ = (2t)^{-ξQ} e^{-ξ h_{2t}(z)} Δ`. Under `P'`,
`h' = h − a k` is an LGF (`w3b_isWholeSpaceLGF_tilt`, `k = F_{2t,z} − F_{R,0}`). Weyl scaling (Axiom
III for `h'`) and `k ≤ ∫ k dσ_{2t,z} + K_A` on `B_{2t}(z)` (`w3b_sf4Potential_le_avg_add`) give
`Ψ ≤ e^{ξ a K_A} normDiam(h')` `P'`-a.s. (`w3b_prefactor_ballDiam_le`), and (E5) bounds
`E'[normDiam(h')^p] ≤ M` (`U = B_1`, `K = B̄_{1/2}`, scale `2t`, centre `z`). Finally
`Var X ≤ log(R/(2t)) + 2A + K₀` (F3). No measurability of internal metrics is used: the tilt is a
change of measure on `Ω` (`lintegral_withDensity_eq_lintegral_mul_non_measurable`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- `s_R(0)⁻¹ = (2t/R)^{ξQ} e^{ξ(h_{2t}(z) − h_R(0))} · (2t)^{-ξQ} e^{-ξ h_{2t}(z)}`. -/
theorem w3b_sNorm_inv_eq (ξ Q : ℝ) (g : DistRd d) {t R : ℝ} (ht : 0 < t) (hR : 0 < R)
    (z : Rd d) :
    (sNorm ξ Q g R 0)⁻¹ = (2 * t / R) ^ (ξ * Q) *
      Real.exp (ξ * (sphereAvg g (2 * t) z - sphereAvg g R 0)) *
      (((2 * t) ^ (ξ * Q))⁻¹ * Real.exp (-(ξ * sphereAvg g (2 * t) z))) := by
  unfold sNorm
  rw [Real.div_rpow (by positivity) hR.le, mul_sub, Real.exp_sub, Real.exp_neg]
  have h1 : 0 < (2 * t) ^ (ξ * Q) := Real.rpow_pos_of_pos (by positivity) _
  have h2 : 0 < R ^ (ξ * Q) := Real.rpow_pos_of_pos hR _
  have h3 := Real.exp_pos (ξ * sphereAvg g (2 * t) z)
  have h4 := Real.exp_pos (ξ * sphereAvg g R 0)
  field_simp

/-- **The `P'`-a.s. comparison** (deterministic form): if `D_{g'+ak} = e^{ξ a k}·D_{g'}` and the
sphere averages of `g'` converge at `(2t, z)`, then
`(2t)^{-ξQ} e^{-ξ h_{2t}(z)} sup_{B̄_t(z)} D_{g'+ak} ≤ e^{ξ a K_A} normDiam(g')`
(`U = B_1`, `K = B̄_{1/2}`, scale `2t`). -/
theorem w3b_prefactor_ballDiam_le (hd : 2 ≤ d) {ξ Q a A t R : ℝ} (hξ : 0 < ξ) (ha : 0 < a)
    (hR : 0 < R) (h2t0 : 0 < 2 * t) (h2t : 2 * t ≤ R) {z : Rd d} (hz : ‖z‖ ≤ A * R)
    (D : DistRd d → ContMetric d) (g' : DistRd d)
    (hw : ∀ x y, weylScale ξ (a • sf4Potential hd h2t0 hR z 0) (D g') x y =
      ENNReal.ofReal ((D (addFun g' (a • sf4Potential hd h2t0 hR z 0))).1 (x, y)))
    (hc : ∃ b, Tendsto (sphereAvgSeq g' (2 * t) z) atTop (𝓝 b)) :
    ENNReal.ofReal (((2 * t) ^ (ξ * Q))⁻¹ * Real.exp (-(ξ *
        sphereAvg (addFun g' (a • sf4Potential hd h2t0 hR z 0)) (2 * t) z))) *
      w3bBallDiam (D (addFun g' (a • sf4Potential hd h2t0 hR z 0))) z t ≤
    ENNReal.ofReal (Real.exp (ξ * a * w3bPotConst d A)) *
      normDiam ξ Q D g' (ball (0 : Rd d) 1) (closedBall (0 : Rd d) (1 / 2)) (2 * t) z := by
  set k := sf4Potential hd h2t0 hR z 0 with hk
  set avg := ∫ u, k (z + (2 * t) • u) ∂(unitSphereProb d) with havg
  set Kp := w3bPotConst d A with hKp
  obtain ⟨b, hb⟩ := hc
  have hsph : sphereAvg (addFun g' (a • k)) (2 * t) z = sphereAvg g' (2 * t) z + a * avg := by
    rw [sphereAvg_addFun_of_tendsto hb]
    congr 1
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    exact integral_const_mul a _
  have hbound : ∀ x ∈ affineSet (2 * t) z (ball (0 : Rd d) 1),
      ξ * (a • k) x ≤ ξ * a * (avg + Kp) := by
    rintro x ⟨v, hv, rfl⟩
    have hv' : ‖v‖ ≤ 1 := (mem_ball_zero_iff.1 hv).le
    have hle := w3b_sf4Potential_le_avg_add hd h2t0 hR h2t hz hv'
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    calc ξ * (a * k (z + (2 * t) • v)) = (ξ * a) * k (z + (2 * t) • v) := by ring
      _ ≤ (ξ * a) * (avg + Kp) := mul_le_mul_of_nonneg_left hle (mul_pos hξ ha).le
  have hS : closedBall z t ⊆ affineSet (2 * t) z (closedBall (0 : Rd d) (1 / 2)) := by
    intro x hx
    refine ⟨(2 * t)⁻¹ • (x - z), ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h2t0]
      rw [mem_closedBall, dist_eq_norm] at hx
      rw [inv_mul_le_iff₀ h2t0]
      linarith
    · show z + (2 * t) • ((2 * t)⁻¹ • (x - z)) = x
      rw [smul_smul, mul_inv_cancel₀ h2t0.ne', one_smul, add_sub_cancel]
  have hBD := w3b_ballDiam_le_of_weyl hw hbound hS
  unfold normDiam
  rw [hsph]
  set SUP := ⨆ (x ∈ affineSet (2 * t) z (closedBall (0 : Rd d) (1 / 2)))
    (y ∈ affineSet (2 * t) z (closedBall (0 : Rd d) (1 / 2))),
      (D g').internal (affineSet (2 * t) z (ball (0 : Rd d) 1)) x y with hSUP
  have hc0 : 0 ≤ ((2 * t) ^ (ξ * Q))⁻¹ := by positivity
  have hreal : ((2 * t) ^ (ξ * Q))⁻¹ * Real.exp (-(ξ * (sphereAvg g' (2 * t) z + a * avg))) *
      Real.exp (ξ * a * (avg + Kp)) =
      Real.exp (ξ * a * Kp) *
        (((2 * t) ^ (ξ * Q))⁻¹ * Real.exp (-(ξ * sphereAvg g' (2 * t) z))) := by
    have e : Real.exp (-(ξ * (sphereAvg g' (2 * t) z + a * avg))) * Real.exp (ξ * a * (avg + Kp)) =
        Real.exp (ξ * a * Kp) * Real.exp (-(ξ * sphereAvg g' (2 * t) z)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, e]
    ring
  calc ENNReal.ofReal (((2 * t) ^ (ξ * Q))⁻¹ *
          Real.exp (-(ξ * (sphereAvg g' (2 * t) z + a * avg)))) *
        w3bBallDiam (D (addFun g' (a • k))) z t
      ≤ ENNReal.ofReal (((2 * t) ^ (ξ * Q))⁻¹ *
          Real.exp (-(ξ * (sphereAvg g' (2 * t) z + a * avg)))) *
        (ENNReal.ofReal (Real.exp (ξ * a * (avg + Kp))) * SUP) := by gcongr
    _ = ENNReal.ofReal (((2 * t) ^ (ξ * Q))⁻¹ *
          Real.exp (-(ξ * (sphereAvg g' (2 * t) z + a * avg))) *
          Real.exp (ξ * a * (avg + Kp))) * SUP := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (Real.exp (ξ * a * Kp) *
          (((2 * t) ^ (ξ * Q))⁻¹ * Real.exp (-(ξ * sphereAvg g' (2 * t) z)))) * SUP := by
        rw [hreal]
    _ = ENNReal.ofReal (Real.exp (ξ * a * Kp)) *
          (ENNReal.ofReal (((2 * t) ^ (ξ * Q))⁻¹ * Real.exp (-(ξ * sphereAvg g' (2 * t) z))) *
            SUP) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]

/-- Exponent bookkeeping: `(2t/R)^{ξQp} e^{a² V/2} ≤ (2t/R)^{ξQp − ξ²p²/2} e^{a²(2A+K₀)/2}` when
`a = ξp` and `V ≤ log(R/(2t)) + 2A + K₀`. -/
theorem w3b_rpow_mul_exp_le {ξ Q p t R A K₀ V : ℝ} (ht : 0 < t) (hR : 0 < R)
    (hV : V ≤ Real.log (R / (2 * t)) + 2 * A + K₀) :
    (2 * t / R) ^ (ξ * Q * p) * Real.exp ((ξ * p) ^ 2 * V / 2) ≤
      (2 * t / R) ^ (ξ * Q * p - ξ ^ 2 * p ^ 2 / 2) *
        Real.exp ((ξ * p) ^ 2 * (2 * A + K₀) / 2) := by
  have hq : 0 < 2 * t / R := by positivity
  rw [Real.rpow_def_of_pos hq, Real.rpow_def_of_pos hq, ← Real.exp_add, ← Real.exp_add,
    Real.exp_le_exp]
  have hlog : Real.log (R / (2 * t)) = -Real.log (2 * t / R) := by
    rw [← Real.log_inv, inv_div]
  rw [hlog] at hV
  have hsq : 0 ≤ (ξ * p) ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left hV hsq
  have e : (ξ * p) ^ 2 = ξ ^ 2 * p ^ 2 := by ring
  rw [e] at this ⊢
  nlinarith [this]

/-- **One-ball moment bound** (MA1 A8, Step 1): for `p ∈ (0, Q/ξ)` and `A ≥ 0` there is `C` such
that for every LGF, every `0 < 2t ≤ R` and `|z| ≤ A R`,
`E[(s_R(0)⁻¹ sup_{x,y ∈ B̄_t(z)} D_h(x,y))^p] ≤ C (2t/R)^{ξQp − ξ²p²/2}`. -/
theorem w3b_oneBall_moment (hd : 2 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hE5 : E5SharpMoment d ξ Q D) {p : ℝ} (hp : 0 < p)
    (hpQ : p < Q / ξ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ {R t : ℝ}, 0 < t → 2 * t ≤ R →
      ∀ z : Rd d, ‖z‖ ≤ A * R →
        ∫⁻ ω, (ENNReal.ofReal (sNorm ξ Q (h ω) R 0)⁻¹ * w3bBallDiam (D (h ω)) z t) ^ p ∂P ≤
          ENNReal.ofReal (C * (2 * t / R) ^ (ξ * Q * p - ξ ^ 2 * p ^ 2 / 2)) := by
  have hW : IsWeakExpMetric d ξ D (fun r => r ^ (ξ * Q)) := hD
  have hU : IsOpen (ball (0 : Rd d) 1) := isOpen_ball
  have hK : IsCompact (closedBall (0 : Rd d) (1 / 2)) := isCompact_closedBall _ _
  have hKc : IsConnected (closedBall (0 : Rd d) (1 / 2)) :=
    (convex_closedBall _ _).isConnected (nonempty_closedBall.2 (by norm_num))
  have hKU : closedBall (0 : Rd d) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  have hpE5 : p < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ :=
    hpQ.trans_le (div_le_div_of_nonneg_right (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hξ.le)
  obtain ⟨M, hM⟩ := hE5 hU hK hKc hKU hp hpE5
  obtain ⟨K₀, hK₀⟩ := exists_variance_sphereAvg_sub_le.{0} hd
  set a : ℝ := ξ * p with ha_def
  have ha : 0 < a := mul_pos hξ hp
  set Kp := w3bPotConst d A with hKp
  refine ⟨Real.exp (a ^ 2 * (2 * A + K₀) / 2) * Real.exp (ξ * a * Kp * p) * max M 0,
    by positivity, ?_⟩
  intro Ω _ P _ h hh R t ht h2t z hz
  have hR : 0 < R := by linarith
  have h2t0 : 0 < 2 * t := by linarith
  set k := sf4Potential hd h2t0 hR z 0 with hk
  set dens := w3bTiltDensity h P (2 * t) R z 0 a with hdens_def
  have hdens_m : Measurable dens := measurable_w3bTiltDensity hh.measurable _ _ _ _ _
  set P' := P.withDensity dens with hP'
  have : IsProbabilityMeasure P' := w3b_isProbabilityMeasure_tilt hd hh h2t0 hR z 0 a
  set h' : Ω → DistRd d := fun ω => addFun (h ω) (-(a • k)) with hh'_def
  have hh' : IsWholeSpaceLGF h' P' := w3b_isWholeSpaceLGF_tilt hd hh h2t0 hR z 0 a
  have hE := hM P' h' hh' (2 * t) h2t0 z
  -- the prefactor-weighted ball diameter
  set Ψ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (((2 * t) ^ (ξ * Q))⁻¹ *
    Real.exp (-(ξ * sphereAvg (h ω) (2 * t) z))) * w3bBallDiam (D (h ω)) z t with hΨ
  set ND : Ω → ℝ≥0∞ := fun ω =>
    normDiam ξ Q D (h' ω) (ball (0 : Rd d) 1) (closedBall (0 : Rd d) (1 / 2)) (2 * t) z with hND
  have hae : ∀ᵐ ω ∂P', Ψ ω ≤ ENNReal.ofReal (Real.exp (ξ * a * Kp)) * ND ω := by
    filter_upwards [hW.weyl P' h' hh'.isLGFPlusCont,
      hh'.ae_exists_tendsto_sphereAvgSeq hd h2t0 z] with ω hw hc
    have hg : addFun (h' ω) (a • k) = h ω := by
      simp only [hh'_def]
      rw [addFun_addFun, neg_add_cancel, addFun_zero]
    have key := w3b_prefactor_ballDiam_le (Q := Q) hd hξ ha hR h2t0 h2t hz D (h' ω) (hw (a • k)) hc
    rw [hg] at key
    exact key
  -- the variance of `X = h_{2t}(z) − h_R(0)`
  set V := Var[fun ω => sphereAvg (h ω) (2 * t) z - sphereAvg (h ω) R 0; P] with hV_def
  have hVar := (hK₀ hh h2t0 hR z 0).1 h2t
  have hmax : max 0 (Real.log (‖z - 0‖ / R)) ≤ A := by
    rw [sub_zero]
    refine max_le hA ?_
    calc Real.log (‖z‖ / R) ≤ ‖z‖ / R := Real.log_le_self (by positivity)
      _ ≤ A := by rw [div_le_iff₀ hR]; exact hz
  have hV : V ≤ Real.log (R / (2 * t)) + 2 * A + K₀ := by linarith
  -- pointwise factorization of the integrand
  set c₀ : ℝ := (2 * t / R) ^ (ξ * Q * p) with hc₀
  have hpt : ∀ ω, (ENNReal.ofReal (sNorm ξ Q (h ω) R 0)⁻¹ * w3bBallDiam (D (h ω)) z t) ^ p =
      ENNReal.ofReal (c₀ * Real.exp (a ^ 2 * V / 2)) * (dens ω * Ψ ω ^ p) := by
    intro ω
    set X := sphereAvg (h ω) (2 * t) z - sphereAvg (h ω) R 0 with hX
    set x₁ := (2 * t / R) ^ (ξ * Q) with hx₁
    set x₂ := Real.exp (ξ * X) with hx₂
    set x₃ := ((2 * t) ^ (ξ * Q))⁻¹ * Real.exp (-(ξ * sphereAvg (h ω) (2 * t) z)) with hx₃
    have hx₁0 : 0 ≤ x₁ := by positivity
    have hx₂0 : 0 ≤ x₂ := (Real.exp_pos _).le
    have hreal : (x₁ * x₂) ^ p = c₀ * Real.exp (a ^ 2 * V / 2) *
        Real.exp (a * X - a ^ 2 * V / 2) := by
      rw [Real.mul_rpow hx₁0 hx₂0, hx₁, ← Real.rpow_mul (by positivity), hx₂, ← Real.exp_mul,
        mul_assoc c₀, ← Real.exp_add]
      congr 2
      rw [ha_def]
      ring
    have hdens_ω : dens ω = ENNReal.ofReal (Real.exp (a * X - a ^ 2 * V / 2)) := rfl
    rw [w3b_sNorm_inv_eq ξ Q (h ω) ht hR z]
    change (ENNReal.ofReal (x₁ * x₂ * x₃) * w3bBallDiam (D (h ω)) z t) ^ p = _
    rw [ENNReal.ofReal_mul (mul_nonneg hx₁0 hx₂0), mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hx₁0 hx₂0) hp.le, hreal, hdens_ω,
      ENNReal.ofReal_mul (by positivity), mul_assoc]
  -- the chain of (lower) integrals
  have hfin : ∀ᵐ ω ∂P, dens ω < ∞ := ae_of_all _ fun ω => ENNReal.ofReal_lt_top
  have hND : ∫⁻ ω, Ψ ω ^ p ∂P' ≤ ENNReal.ofReal (Real.exp (ξ * a * Kp * p)) * ENNReal.ofReal M := by
    calc ∫⁻ ω, Ψ ω ^ p ∂P'
        ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (ξ * a * Kp)) * ND ω) ^ p ∂P' :=
          lintegral_mono_ae (hae.mono fun ω hω => ENNReal.rpow_le_rpow hω hp.le)
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (ξ * a * Kp)) ^ p * ND ω ^ p ∂P' := by
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      _ = ENNReal.ofReal (Real.exp (ξ * a * Kp)) ^ p * ∫⁻ ω, ND ω ^ p ∂P' :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      _ ≤ ENNReal.ofReal (Real.exp (ξ * a * Kp)) ^ p * ENNReal.ofReal M := by gcongr
      _ = ENNReal.ofReal (Real.exp (ξ * a * Kp * p)) * ENNReal.ofReal M := by
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp.le, ← Real.exp_mul]
  have hexp := w3b_rpow_mul_exp_le (ξ := ξ) (Q := Q) (p := p) (A := A) (K₀ := K₀) ht hR hV
  calc ∫⁻ ω, (ENNReal.ofReal (sNorm ξ Q (h ω) R 0)⁻¹ * w3bBallDiam (D (h ω)) z t) ^ p ∂P
      = ∫⁻ ω, ENNReal.ofReal (c₀ * Real.exp (a ^ 2 * V / 2)) * (dens ω * Ψ ω ^ p) ∂P :=
        lintegral_congr hpt
    _ = ENNReal.ofReal (c₀ * Real.exp (a ^ 2 * V / 2)) * ∫⁻ ω, dens ω * Ψ ω ^ p ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (c₀ * Real.exp (a ^ 2 * V / 2)) * ∫⁻ ω, Ψ ω ^ p ∂P' := by
        rw [hP', lintegral_withDensity_eq_lintegral_mul_non_measurable P hdens_m hfin]
        rfl
    _ ≤ ENNReal.ofReal (c₀ * Real.exp (a ^ 2 * V / 2)) *
          (ENNReal.ofReal (Real.exp (ξ * a * Kp * p)) * ENNReal.ofReal (max M 0)) := by
        gcongr
        exact hND.trans (by gcongr; exact le_max_left _ _)
    _ = ENNReal.ofReal (c₀ * Real.exp (a ^ 2 * V / 2) *
          (Real.exp (ξ * a * Kp * p) * max M 0)) := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ c₀ * Real.exp (a ^ 2 * V / 2)),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.exp (ξ * a * Kp * p))]
    _ ≤ ENNReal.ofReal (Real.exp (a ^ 2 * (2 * A + K₀) / 2) * Real.exp (ξ * a * Kp * p) * max M 0 *
          (2 * t / R) ^ (ξ * Q * p - ξ ^ 2 * p ^ 2 / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have hpos : 0 ≤ Real.exp (ξ * a * Kp * p) * max M 0 := by positivity
        calc c₀ * Real.exp (a ^ 2 * V / 2) * (Real.exp (ξ * a * Kp * p) * max M 0)
            ≤ (2 * t / R) ^ (ξ * Q * p - ξ ^ 2 * p ^ 2 / 2) *
                Real.exp ((ξ * p) ^ 2 * (2 * A + K₀) / 2) *
                (Real.exp (ξ * a * Kp * p) * max M 0) :=
              mul_le_mul_of_nonneg_right hexp hpos
          _ = Real.exp (a ^ 2 * (2 * A + K₀) / 2) * Real.exp (ξ * a * Kp * p) * max M 0 *
                (2 * t / R) ^ (ξ * Q * p - ξ ^ 2 * p ^ 2 / 2) := by
              rw [ha_def]
              ring

end HigherDimLQGMetric
