import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Norm.Rho
import HigherDimLQGContinuity.Norm.Pin
import HigherDimLQGContinuity.Concentration.PathMeasure
import HigherDimLQGMetric.Sharp.ScaledMetric

/-!
# The core of Lemma 2.1 used by Lemma 5.1 (packet N4; blueprint Part C `c:lem-core`)

NA4 A0 (`UniformCore` as a projection of Lemma 2.1, ruling N7; Part C `c:lem-core`). From
`UniformEstimates d ξ̄ 1` (Part A `a:def-uniform`, interface I1) we derive, with constants depending only on `d` and
`ξ̄`, for every `ξ ∈ (0, ξ̄]` and every `D` strong at `ξ`, with `ρ = rho D` and `ℙ = normLGFLaw d`:

* (U0) `log D(0, e₁)` is integrable and `∫ log ρ(0, e₁) dℙ = 0`;
* (U1) for every `R ≥ 1` a measurable envelope `H_R ≥ 1` with `∫⁻ H_R^{p_*} ≤ C_U (1 + R)^A` such that a.s., for
  `x, y ∈ B̄_R`: `H_R⁻¹ |x - y|^β ≤ ρ(x, y)`, and `ρ(x, y) ≤ H_R |x - y|^σ` when `|x - y| ≤ 1`;
* (U2) `ℙ{∃ y, |y| ≥ S, ρ(0, y) ≤ ρ(0, e₁)} ≤ C_U S^{-p_esc}` for `S ≥ 1` (outer measure);
* (U3) a.s. `D` and `ρ` are length metrics, `(ℝ^d, ρ)` is proper, any two points are joined by a constant-speed
  `ρ`-geodesic, and Weyl scaling `D_{g+f} = e^{ξ f}·D_g` holds for every continuous `f`.

Proofs (blueprint `c:lem-core`): (U0) is (E0) with `integral_log_rho` (Part A `a:lem-rho` (c)); (U1) uses (E1), with
the upper bound from the internal diameters by a midpoint argument (`n4_apply_le_of_diamIn`: `H_R := 4 H^E`);
(U2) uses (E5) at `K = 1`, `R = 2` and a crossing argument along a geodesic from `0` to `y`
(`n4_apply_lt_of_escape`); (U3) is (E6) with axioms (I) and (III) for the input `id` under `ℙ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ## Deterministic steps -/

/-- An internal distance between two points of `A` is at most the internal diameter of `A`. -/
theorem n4_internal_le_diamIn (G : ContMetric d) {V A : Set (Rd d)} {x y : Rd d} (hx : x ∈ A)
    (hy : y ∈ A) : G.internal V x y ≤ diamIn G V A := by
  unfold diamIn
  exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)

/-- The half-scale step of (U1): `G(x, y) ≤ 2 H |x - y|^σ` for `x, y ∈ B̄_R` with `|x - y| ≤ 1/2`, from the
internal-diameter bound of (E1). -/
theorem n4_apply_le_of_diamIn_half {G : ContMetric d} {R H σ : ℝ} (hH : 0 ≤ H) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1)
    (hdiam : ∀ z ∈ closedBall (0 : Rd d) R, ∀ s ∈ Ioc (0 : ℝ) 1,
      diamIn G (ball z (2 * s)) (ball z s) ≤ ENNReal.ofReal (H * s ^ σ))
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) R) (hxy : ‖x - y‖ ≤ 1 / 2) :
    G.1 (x, y) ≤ 2 * H * ‖x - y‖ ^ σ := by
  rcases eq_or_ne x y with rfl | hne
  · rw [G.apply_self, sub_self, norm_zero, Real.zero_rpow hσ.ne', mul_zero]
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set s := 2 * ‖x - y‖ with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := by linarith
  have hxB : x ∈ ball x s := mem_ball_self hs0
  have hyB : y ∈ ball x s := by
    rw [mem_ball, dist_eq_norm, norm_sub_rev]
    linarith
  have h1 : ENNReal.ofReal (G.1 (x, y)) ≤ ENNReal.ofReal (H * s ^ σ) :=
    (G.ofReal_le_internal (ball x (2 * s)) x y).trans
      ((n4_internal_le_diamIn G hxB hyB).trans (hdiam x hx s ⟨hs0, hs1⟩))
  have h2 : G.1 (x, y) ≤ H * s ^ σ :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have h3 : s ^ σ ≤ 2 * ‖x - y‖ ^ σ := by
    rw [hs, Real.mul_rpow (by norm_num) hpos.le]
    have : (2 : ℝ) ^ σ ≤ 2 := by
      calc (2 : ℝ) ^ σ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right this (by positivity)
  calc G.1 (x, y) ≤ H * s ^ σ := h2
    _ ≤ H * (2 * ‖x - y‖ ^ σ) := mul_le_mul_of_nonneg_left h3 hH
    _ = 2 * H * ‖x - y‖ ^ σ := by ring

/-- **(U1), upper bound** (blueprint `c:lem-core`, proof of (U1)): from the internal-diameter bound of (E1) on
`B̄_R`, `G(x, y) ≤ 4 H |x - y|^σ` for `x, y ∈ B̄_R` with `|x - y| ≤ 1` (midpoint argument). -/
theorem n4_apply_le_of_diamIn {G : ContMetric d} {R H σ : ℝ} (hH : 0 ≤ H) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hdiam : ∀ z ∈ closedBall (0 : Rd d) R, ∀ s ∈ Ioc (0 : ℝ) 1,
      diamIn G (ball z (2 * s)) (ball z s) ≤ ENNReal.ofReal (H * s ^ σ))
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) R) (hy : y ∈ closedBall (0 : Rd d) R)
    (hxy : ‖x - y‖ ≤ 1) : G.1 (x, y) ≤ 4 * H * ‖x - y‖ ^ σ := by
  set w : Rd d := (1 / 2 : ℝ) • (x + y) with hw
  have hxw : x - w = (1 / 2 : ℝ) • (x - y) := by rw [hw]; module
  have hwy : w - y = (1 / 2 : ℝ) • (x - y) := by rw [hw]; module
  have hnorm : ‖(1 / 2 : ℝ) • (x - y)‖ = ‖x - y‖ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  have hwB : w ∈ closedBall (0 : Rd d) R := by
    rw [mem_closedBall_zero_iff] at hx hy ⊢
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := norm_add_le x y
    linarith
  have hhalf : ‖x - y‖ / 2 ≤ 1 / 2 := by linarith
  have h1 := n4_apply_le_of_diamIn_half hH hσ hσ1 hdiam hx (by rw [hxw, hnorm]; exact hhalf)
  have h2 := n4_apply_le_of_diamIn_half hH hσ hσ1 hdiam hwB (by rw [hwy, hnorm]; exact hhalf)
  rw [hxw, hnorm] at h1
  rw [hwy, hnorm] at h2
  have hmono : (‖x - y‖ / 2) ^ σ ≤ ‖x - y‖ ^ σ :=
    Real.rpow_le_rpow (by positivity) (by linarith [norm_nonneg (x - y)]) hσ.le
  calc G.1 (x, y) ≤ G.1 (x, w) + G.1 (w, y) := G.apply_triangle x w y
    _ ≤ 2 * H * (‖x - y‖ / 2) ^ σ + 2 * H * (‖x - y‖ / 2) ^ σ := add_le_add h1 h2
    _ = 4 * H * (‖x - y‖ / 2) ^ σ := by ring
    _ ≤ 4 * H * ‖x - y‖ ^ σ := mul_le_mul_of_nonneg_left hmono (by positivity)

/-- Along a path from `‖P 0‖ ≤ a` to `‖P 1‖ ≥ a`, some time has `‖P t‖ = a` (intermediate values). -/
theorem n4_exists_norm_eq (P : C(unitInterval, Rd d)) {a : ℝ} (h0 : ‖P 0‖ ≤ a) (h1 : a ≤ ‖P 1‖) :
    ∃ t : unitInterval, ‖P t‖ = a := by
  have hg : Continuous fun t : unitInterval => ‖P t‖ := continuous_norm.comp P.continuous
  obtain ⟨t, ht⟩ := intermediate_value_univ 0 1 hg ⟨h0, h1⟩
  exact ⟨t, ht⟩

/-- **The crossing argument of (U2)** (blueprint `c:lem-core`, proof of (U2)): for a length metric `G` with
constant-speed geodesics between any two points, if the internal diameter of `ball 0 r` (inside `V`) is smaller
than the set distance from `sphere 0 a` to `sphere 0 b` (`0 ≤ a ≤ b`), then `G(u, v) < G(0, y)` for
`u, v ∈ ball 0 r` and `‖y‖ ≥ b`. -/
theorem n4_apply_lt_of_escape {G : ContMetric d} (hG : G.IsLength)
    (hgeo : ∀ x y : Rd d, ∃ γ : C(unitInterval, Rd d), IsConstSpeedGeod G x y γ)
    {V : Set (Rd d)} {r a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hesc : diamIn G V (ball (0 : Rd d) r) <
      setDistIn G univ (sphere (0 : Rd d) a) (sphere (0 : Rd d) b))
    {u v : Rd d} (hu : u ∈ ball (0 : Rd d) r) (hv : v ∈ ball (0 : Rd d) r) {y : Rd d} (hy : b ≤ ‖y‖) :
    G.1 (u, v) < G.1 (0, y) := by
  obtain ⟨γ, hγ⟩ := hgeo 0 y
  have h0 : ‖γ 0‖ = 0 := by rw [hγ.1, norm_zero]
  have h1 : ‖γ 1‖ = ‖y‖ := by rw [hγ.2.1]
  obtain ⟨s, hs⟩ := n4_exists_norm_eq γ (h0.le.trans ha) (hab.trans (h1 ▸ hy))
  obtain ⟨t, ht⟩ := n4_exists_norm_eq γ (h0.le.trans (ha.trans hab)) (h1 ▸ hy)
  have hset : setDistIn G univ (sphere (0 : Rd d) a) (sphere (0 : Rd d) b) ≤
      ENNReal.ofReal (G.1 (γ s, γ t)) := by
    rw [← G.internal_univ_of_isLength hG]
    unfold setDistIn
    exact iInf₂_le_of_le (γ s) (mem_sphere_zero_iff_norm.2 hs)
      (iInf₂_le_of_le (γ t) (mem_sphere_zero_iff_norm.2 ht) le_rfl)
  have hlt : ENNReal.ofReal (G.1 (u, v)) < ENNReal.ofReal (G.1 (γ s, γ t)) :=
    lt_of_le_of_lt ((G.ofReal_le_internal V u v).trans (n4_internal_le_diamIn G hu hv))
      (hesc.trans_le hset)
  have hlt' : G.1 (u, v) < G.1 (γ s, γ t) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (G.nonneg u v)).1 hlt
  exact hlt'.trans_le (apply_le_of_isConstSpeedGeod hγ s t)

/-! ## Lemma 2.1's core -/

/-- **Lemma 2.1's core** (blueprint Part C `c:lem-core`; NA4 A0, the projection `UniformCore` of
`UniformEstimates d ξ̄ 1`). There are constants `p_* > 0`, `0 < σ < 1 < β`, `C_U ≥ 1`, `A ≥ 0`, `p_esc > 0`
(depending only on `d` and `ξ̄`) such that for every `ξ ∈ (0, ξ̄]` and every `D` strong at `ξ`, with
`ρ = rho D` and `ℙ = normLGFLaw d`, (U0)–(U3) hold (see the module docstring). -/
theorem lemma21_core {d : ℕ} (hd : 3 ≤ d) {ξbar : ℝ} (hU : UniformEstimates d ξbar 1) :
    ∃ pst σ β CU A pesc : ℝ, 0 < pst ∧ 0 < σ ∧ σ < 1 ∧ 1 < β ∧ 1 ≤ CU ∧ 0 ≤ A ∧ 0 < pesc ∧
    ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
      -- (U0)
      (Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d) ∧
        ∫ g, Real.log ((rho D g).1 (0, e₁ d)) ∂(normLGFLaw d) = 0) ∧
      -- (U1)
      (∀ R : ℝ, 1 ≤ R → ∃ H : DistRd d → ℝ, Measurable H ∧ (∀ g, 1 ≤ H g) ∧
        ∫⁻ g, ENNReal.ofReal (H g ^ pst) ∂(normLGFLaw d) ≤ ENNReal.ofReal (CU * (1 + R) ^ A) ∧
        ∀ᵐ g ∂(normLGFLaw d), ∀ x ∈ closedBall (0 : Rd d) R, ∀ y ∈ closedBall (0 : Rd d) R,
          (H g)⁻¹ * ‖x - y‖ ^ β ≤ (rho D g).1 (x, y) ∧
          (‖x - y‖ ≤ 1 → (rho D g).1 (x, y) ≤ H g * ‖x - y‖ ^ σ)) ∧
      -- (U2)
      (∀ S : ℝ, 1 ≤ S → normLGFLaw d {g | ∃ y : Rd d, S ≤ ‖y‖ ∧
          (rho D g).1 (0, y) ≤ (rho D g).1 (0, e₁ d)} ≤ ENNReal.ofReal (CU * S ^ (-pesc))) ∧
      -- (U3)
      (∀ᵐ g ∂(normLGFLaw d), (D g).IsLength ∧ (rho D g).IsLength ∧ ProperSpace (rho D g).Space ∧
        (∀ x y : Rd d, ∃ γ : C(unitInterval, Rd d), IsConstSpeedGeod (rho D g) x y γ) ∧
        ∀ (f : C(Rd d, ℝ)) (z w : Rd d),
          weylScale ξ f (D g) z w = ENNReal.ofReal ((D (addFun g f)).1 (z, w))) := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 0 < d := by omega
  have hspec := normLGFLaw_spec_holds d hd2
  have : IsProbabilityMeasure (normLGFLaw d) := hspec.1
  have hlgf : IsLGFPlusCont (id : DistRd d → DistRd d) (normLGFLaw d) :=
    hspec.2.1.1.isLGFPlusCont
  have hpin : pinLaw d 1 = normLGFLaw d := pinLaw_one hd2
  obtain ⟨p, σ, β, C, A, hp, hσ, hσ1, hβ, _hC, hA, henv⟩ := hU.envelope
  obtain ⟨pesc, hpesc, hesc⟩ := hU.escape
  obtain ⟨C₁, hC₁⟩ := hesc 1 le_rfl
  set CU : ℝ := max (max (4 ^ p * C) (C₁ * 2 ^ pesc)) (8 ^ pesc) with hCU
  have hCU1 : 1 ≤ CU := (Real.one_le_rpow (by norm_num) hpesc.le).trans (le_max_right _ _)
  refine ⟨p, σ, β, CU, A, pesc, hp, hσ, hσ1, hβ, hCU1, hA, hpesc, fun ξ hξ D hD => ?_⟩
  have hint := hU.logIntegrable ξ hξ D hD
  -- the length and geodesic event (U3)
  have hU3 : ∀ᵐ g ∂(normLGFLaw d), (D g).IsLength ∧ (rho D g).IsLength ∧
      ProperSpace (rho D g).Space ∧
      (∀ x y : Rd d, ∃ γ : C(unitInterval, Rd d), IsConstSpeedGeod (rho D g) x y γ) ∧
      ∀ (f : C(Rd d, ℝ)) (z w : Rd d),
        weylScale ξ f (D g) z w = ENNReal.ofReal ((D (addFun g f)).1 (z, w)) := by
    have hprop := hU.proper ξ hξ D hD
    rw [hpin] at hprop
    filter_upwards [hD.length (normLGFLaw d) id hlgf, hD.weyl (normLGFLaw d) id hlgf, hprop]
      with g hlen hw hpr
    exact ⟨hlen, ContMetric.isLength_smul (Real.exp_pos _) hlen, hpr.1, hpr.2, hw⟩
  refine ⟨⟨hint, integral_log_rho hd2 hint⟩, fun R hR => ?_, fun S hS => ?_, hU3⟩
  · -- (U1)
    obtain ⟨H, hHm, hH1, hHint, hHae⟩ := henv ξ hξ D hD R hR
    rw [hpin] at hHint hHae
    refine ⟨fun g => 4 * H g, hHm.const_mul 4, fun g => by linarith [hH1 g], ?_, ?_⟩
    · have hpt : ∀ g, ENNReal.ofReal ((4 * H g) ^ p) =
          ENNReal.ofReal (4 ^ p) * ENNReal.ofReal (H g ^ p) := fun g => by
        rw [Real.mul_rpow (by norm_num) (by linarith [hH1 g]),
          ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
      simp_rw [hpt]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal (4 ^ p) * ∫⁻ g, ENNReal.ofReal (H g ^ p) ∂(normLGFLaw d)
          ≤ ENNReal.ofReal (4 ^ p) * ENNReal.ofReal (C * (1 + R) ^ A) := by gcongr
        _ = ENNReal.ofReal (4 ^ p * C * (1 + R) ^ A) := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), mul_assoc]
        _ ≤ ENNReal.ofReal (CU * (1 + R) ^ A) := by
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
            exact (le_max_left _ _).trans (le_max_left _ _)
    · filter_upwards [hHae] with g hg x hx y hy
      have hHg : 1 ≤ H g := hH1 g
      refine ⟨?_, fun hxy => n4_apply_le_of_diamIn (by linarith) hσ hσ1.le hg.1 hx hy hxy⟩
      calc (4 * H g)⁻¹ * ‖x - y‖ ^ β ≤ (H g)⁻¹ * ‖x - y‖ ^ β := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact inv_anti₀ (by linarith) (by linarith)
        _ ≤ (rho D g).1 (x, y) := hg.2 x hx y hy
  · -- (U2)
    set A' : Set (DistRd d) := {g | ∃ y : Rd d, S ≤ ‖y‖ ∧
      (rho D g).1 (0, y) ≤ (rho D g).1 (0, e₁ d)} with hA'
    have hS0 : 0 < S := by linarith
    rcases lt_or_ge S 8 with hS8 | hS8
    · -- small `S`: the trivial bound
      calc normLGFLaw d A' ≤ 1 := prob_le_one
        _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal (CU * S ^ (-pesc)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h8 : (1 : ℝ) ≤ 8 ^ pesc * S ^ (-pesc) := by
              rw [Real.rpow_neg hS0.le, ← div_eq_mul_inv, one_le_div (by positivity)]
              exact Real.rpow_le_rpow hS0.le hS8.le hpesc.le
            exact h8.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    · -- `S ≥ 8`: escape at `K = 1`, `R = 2`, scale `S / 2 ≥ 4`
      have hS4 : 4 ≤ S / 2 := by linarith
      have hE := hC₁ ξ hξ D hD 2 (S / 2) (by norm_num) hS4
      rw [hpin] at hE
      set E : Set (DistRd d) := {g | ¬ (ENNReal.ofReal 1 * diamIn (rho D g) (ball 0 (2 * 2))
        (ball 0 2) < setDistIn (rho D g) univ (sphere 0 (2 * 2)) (sphere 0 (S / 2 * 2)))} with hEdef
      set N : Set (DistRd d) := {g | ¬ ((rho D g).IsLength ∧
        ∀ x y : Rd d, ∃ γ : C(unitInterval, Rd d), IsConstSpeedGeod (rho D g) x y γ)} with hNdef
      have hN : normLGFLaw d N = 0 := by
        have : ∀ᵐ g ∂(normLGFLaw d), (rho D g).IsLength ∧
            ∀ x y : Rd d, ∃ γ : C(unitInterval, Rd d), IsConstSpeedGeod (rho D g) x y γ := by
          filter_upwards [hU3] with g hg using ⟨hg.2.1, hg.2.2.2.1⟩
        exact ae_iff.1 this
      have hsub : A' ⊆ E ∪ N := by
        intro g hg
        by_contra hcon
        simp only [mem_union, not_or] at hcon
        obtain ⟨hgE, hgN⟩ := hcon
        simp only [hEdef, hNdef, mem_ofPred_eq, not_not] at hgE hgN
        obtain ⟨y, hy, hle⟩ := hg
        rw [ENNReal.ofReal_one, one_mul] at hgE
        have he₁ : e₁ d ∈ ball (0 : Rd d) 2 := by
          rw [mem_ball_zero_iff, HigherDimLFPP.norm_e₁ hd1]
          norm_num
        have hlt := n4_apply_lt_of_escape hgN.1 hgN.2 (by norm_num) (by linarith) hgE
          (mem_ball_self (by norm_num)) he₁ (show S / 2 * 2 ≤ ‖y‖ by linarith)
        linarith
      have hrpow : (S / 2) ^ (-pesc) = 2 ^ pesc * S ^ (-pesc) := by
        rw [Real.div_rpow hS0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
      calc normLGFLaw d A' ≤ normLGFLaw d (E ∪ N) := measure_mono hsub
        _ ≤ normLGFLaw d E + normLGFLaw d N := measure_union_le E N
        _ = normLGFLaw d E := by rw [hN, add_zero]
        _ ≤ ENNReal.ofReal (C₁ * (S / 2) ^ (-pesc)) := hE
        _ ≤ ENNReal.ofReal (CU * S ^ (-pesc)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hrpow, ← mul_assoc]
            exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _))
              (by positivity)

end HigherDimLQGContinuity
