import HigherDimLQGContinuity.Amplify.Geodesic
import HigherDimLQGContinuity.Sewing.Lemma31a

/-!
# The deterministic step of Lemma 3.2 (packet P7)

Blueprint Part A, Lemma `a:lem32`, "Deterministic step": on the intersection of the confinement, envelope, cover and
cap events, for `x, y ∈ B̄_R` take a `ρ^D`-geodesic `P` from `x` to `y` parametrized by length; `P ⊆ B_W`; the good
grid balls cover `P` in their central tenths; Lemma 3.1(a) (`lemma31a`, with `L = 2`) gives `x', y'` within `2 r₊` of
`x`, `y` with `ρ^E(x', y') ≤ 4 (M/m) ρ^D(x, y)`; the envelope of `ρ^E` attaches the endpoints:
`ρ^E(x, x') ≤ diam_{B_{2t}(x)} B_t(x) ≤ H̄ t^σ` with `t = 4 r₊ ≤ 1`.

`p7_rough_det` is stated for an abstract pair of continuous metrics `(Rm, Qm)` (primary, secondary) and an abstract
finite family of balls; the probabilistic packaging is in `Amplify/Lemma32.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric
open scoped ENNReal

variable {d : ℕ}

/-- **Deterministic step of Lemma 3.2** (`a:lem32`). Let `Rm` (primary) and `Qm` (secondary) be continuous metrics,
`x, y ∈ B̄_R` with a constant-speed `Rm`-geodesic `γ` from `x` to `y`. Assume the escape event of `Rm` at radius
`R + 1` with factor `S ≥ 4`, the envelope of `Qm` on `B̄_{R_env} ⊇ B̄_R`, and a finite family `F` of balls with radii in
`[r₋, r₊]`, `4 r₊ ≤ 1`, covering `B̄_W` (`W = S (R + 1)`) in their central tenths, whose members satisfy the crossing
bound of `Rm` with `m S_R`, the annular diameter bound of `Qm` with `M S_Q`, and `S_Q ≤ 2 S_R`. Then
`Qm(x, y) ≤ 4 (M/m) Rm(x, y) + 2 H̄ (4 r₊)^σ`. -/
theorem p7_rough_det (hd : 2 ≤ d) (Rm Qm : ContMetric d) {R S Renv Hbar σ m M rm rp : ℝ}
    (hR : 0 ≤ R) (hS : 4 ≤ S) (hRenv : R ≤ Renv) (hHbar : 0 ≤ Hbar) (hm : 0 < m) (hM : 0 ≤ M)
    (hrm : 0 < rm) (hrp : 4 * rp ≤ 1)
    (hesc : diamIn Rm (ball (0 : Rd d) (2 * (R + 1))) (ball (0 : Rd d) (R + 1)) <
      setDistIn Rm univ (sphere (0 : Rd d) (2 * (R + 1))) (sphere (0 : Rd d) (S * (R + 1))))
    (henv : ∀ z ∈ closedBall (0 : Rd d) Renv, ∀ s ∈ Ioc (0 : ℝ) 1,
      diamIn Qm (ball z (2 * s)) (ball z s) ≤ ENNReal.ofReal (Hbar * s ^ σ))
    (F : Finset (SewBall d)) (SR SQ : SewBall d → ℝ)
    (hF : ∀ B ∈ F, rm ≤ B.2 ∧ B.2 ≤ rp ∧ 0 < SR B ∧ 0 < SQ B ∧ SQ B ≤ 2 * SR B)
    (hcross : ∀ B ∈ F, ENNReal.ofReal (m * SR B) ≤
      setDistIn Rm univ (sphere B.1 (3 * B.2 / 4)) (sphere B.1 B.2))
    (hdiam : ∀ B ∈ F, diamIn Qm (ann B.1 (B.2 / 2) (7 * B.2 / 2)) (sphere B.1 B.2) ≤
      ENNReal.ofReal (M * SQ B))
    (hcov : ∀ x ∈ closedBall (0 : Rd d) (S * (R + 1)), ∃ B ∈ F, ‖x - B.1‖ < B.2 / 10)
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) R) (hy : y ∈ closedBall (0 : Rd d) R)
    {γ : C(unitInterval, Rd d)} (hγ : IsConstSpeedGeod Rm x y γ) :
    Qm.1 (x, y) ≤ 4 * (M / m) * Rm.1 (x, y) + 2 * (Hbar * (4 * rp) ^ σ) := by
  obtain ⟨hP0, hPℓ, hgeo⟩ := p7_geodPath_spec Rm hγ
  set P := p7_geodPath Rm x y γ with hPdef
  set ℓ := Rm.1 (x, y) with hℓdef
  have hℓ : 0 ≤ ℓ := Rm.nonneg x y
  have hPc : Continuous P := p7_continuous_geodPath Rm x y γ
  have hxn : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
  have hyn : ‖y‖ ≤ R := mem_closedBall_zero_iff.mp hy
  have hxb : P 0 ∈ ball (0 : Rd d) (R + 1) := by
    rw [hP0, mem_ball_zero_iff]; linarith
  have hyb : P ℓ ∈ ball (0 : Rd d) (R + 1) := by
    rw [hPℓ, mem_ball_zero_iff]; linarith
  have hconf := p7_geod_confined Rm hℓ hPc (by linarith : (2 : ℝ) ≤ S) (by linarith : 0 < R + 1)
    hgeo hxb hyb hesc
  have hlen : Rm.len P 0 ℓ ≤ ENNReal.ofReal ℓ := by
    have h := p7_len_le_of_isometry Rm (P := P) (a := 0) (b := ℓ) fun u hu v hv => (hgeo u hu v hv).le
    rwa [sub_zero] at h
  have hfin : Rm.len P 0 ℓ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlen
  have hcov' : ∀ u ∈ Icc (0 : ℝ) ℓ, ∃ B ∈ F, ‖P u - B.1‖ < B.2 / 10 := fun u hu =>
    hcov (P u) (mem_closedBall_zero_iff.mpr (hconf u hu).le)
  obtain ⟨x', y', hx', hy', hQ⟩ := lemma31a hd Rm Qm F SR SQ ℓ rm rp m M 2 hℓ hrm hm hM
    (by norm_num) hF hcross hdiam P hPc.continuousOn hfin hcov'
  have hcoef : 0 ≤ 2 * (M / m) * 2 := by positivity
  have hQ' : Qm.1 (x', y') ≤ 4 * (M / m) * ℓ := by
    have h1 : ENNReal.ofReal (Qm.1 (x', y')) ≤ ENNReal.ofReal (2 * (M / m) * 2 * ℓ) := by
      calc ENNReal.ofReal (Qm.1 (x', y')) ≤ ENNReal.ofReal (2 * (M / m) * 2) * Rm.len P 0 ℓ := hQ
        _ ≤ ENNReal.ofReal (2 * (M / m) * 2) * ENNReal.ofReal ℓ := mul_le_mul_right hlen _
        _ = ENNReal.ofReal (2 * (M / m) * 2 * ℓ) := (ENNReal.ofReal_mul hcoef).symm
    have h2 := p7_le_of_ofReal_le (by positivity) h1
    linarith
  -- endpoint attachment through the envelope of `Qm`
  have hrp0 : 0 < rp := by
    obtain ⟨u, hu⟩ : (Icc (0 : ℝ) ℓ).Nonempty := ⟨0, le_rfl, hℓ⟩
    obtain ⟨B, hB, -⟩ := hcov' u hu
    exact hrm.trans_le ((hF B hB).1.trans (hF B hB).2.1)
  set t := 4 * rp with ht
  have ht0 : 0 < t := by positivity
  have hst : t ∈ Ioc (0 : ℝ) 1 := ⟨ht0, hrp⟩
  have hHt : 0 ≤ Hbar * t ^ σ := mul_nonneg hHbar (Real.rpow_nonneg ht0.le _)
  have hxx' : Qm.1 (x, x') ≤ Hbar * t ^ σ := by
    have hxB : x ∈ ball x t := mem_ball_self ht0
    have hx'B : x' ∈ ball x t := by
      rw [mem_ball, dist_eq_norm]
      rw [hP0] at hx'
      linarith
    exact p7_apply_le_of_diamIn_le Qm hxB hx'B hHt
      (henv x (mem_closedBall_zero_iff.mpr (hxn.trans hRenv)) t hst)
  have hyy' : Qm.1 (y', y) ≤ Hbar * t ^ σ := by
    have hyB : y ∈ ball y t := mem_ball_self ht0
    have hy'B : y' ∈ ball y t := by
      rw [mem_ball, dist_eq_norm]
      rw [hPℓ] at hy'
      linarith
    rw [Qm.apply_comm]
    exact p7_apply_le_of_diamIn_le Qm hyB hy'B hHt
      (henv y (mem_closedBall_zero_iff.mpr (hyn.trans hRenv)) t hst)
  have htri : Qm.1 (x, y) ≤ Qm.1 (x, x') + Qm.1 (x', y') + Qm.1 (y', y) := by
    have h1 := Qm.apply_triangle x x' y
    have h2 := Qm.apply_triangle x' y' y
    linarith
  linarith

end HigherDimLQGContinuity
