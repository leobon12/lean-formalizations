import HigherDimLQGContinuity.Sewing.Lemma31b

/-!
# The band recursion of Proposition 3.3, deterministic part (packet P7)

Blueprint Part A, Proposition `a:prop33`, "Band recursion" (equation `a:eq-recursion`; NA1 R9). Along an
`Rm`-geodesic `P : [0, ℓ] → B̄_W` parametrized by length, start from a rough comparison
`Qm(P u, P v) ≤ (b' + X₀)|u - v| + e₀` and apply Lemma 3.1(b) (`lemma31b`) once per band: band `j` (`j < N`) is a
finite family `F j` of balls with radii in `[rm j, rp j]` covering `P` in their central tenths, with the crossing and
diameter bounds of `Rm` and the connector coefficient `b'` for `Qm`. If the numbers `X j`, `e j` satisfy the
one-step inequalities (`hstepC`, `hstepe`: the right-hand sides of (3.1) with `C = b' + X j`, `e = e j`), then
`Qm(P s, P t) ≤ (b' + X N)(t - s) + e N` on every subsegment (`p7_band_iter`).

The numbers are supplied in closed form in `Amplify/Recursion.lean`; this file is purely deterministic.
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

/-- **The band recursion** (deterministic part of Proposition 3.3): iterating Lemma 3.1(b) over `N` bands. -/
theorem p7_band_iter (hd : 2 ≤ d) (Rm Qm : ContMetric d) (hRlen : Rm.IsLength)
    (P : ℝ → Rd d) (ℓ W : ℝ) (hℓ : 0 ≤ ℓ) (hW0 : 0 ≤ W)
    (hgeo : ∀ u ∈ Icc (0 : ℝ) ℓ, ∀ v ∈ Icc (0 : ℝ) ℓ, Rm.1 (P u, P v) = |u - v|)
    (hPW : ∀ u ∈ Icc (0 : ℝ) ℓ, ‖P u‖ ≤ W)
    {H σ β m M b' : ℝ} (hm : 0 < m) (hM : 0 < M) (hmM : m ≤ M) (hb' : 0 ≤ b') (hH : 1 ≤ H)
    (hσ : 0 < σ) (hβ : 0 < β)
    (hmod : ∀ x ∈ closedBall (0 : Rd d) (W + 1), ∀ y ∈ closedBall (0 : Rd d) (W + 1), ‖x - y‖ ≤ 1 / 2 →
      Rm.1 (x, y) ≤ H * ‖x - y‖ ^ σ ∧ H⁻¹ * ‖x - y‖ ^ β ≤ Rm.1 (x, y))
    (N : ℕ) (rm rp X e : ℕ → ℝ) (F : ℕ → Finset (SewBall d)) (SR : SewBall d → ℝ)
    (hrm : ∀ j < N, 0 < rm j) (hrmp : ∀ j < N, rm j ≤ rp j) (hrp : ∀ j < N, rp j ≤ 1 / 4)
    (hF : ∀ j < N, ∀ B ∈ F j, rm j ≤ B.2 ∧ B.2 ≤ rp j ∧ 0 < SR B)
    (hcov : ∀ j < N, ∀ u ∈ Icc (0 : ℝ) ℓ, ∃ B ∈ F j, ‖P u - B.1‖ < B.2 / 10)
    (hcross : ∀ j < N, ∀ B ∈ F j, ENNReal.ofReal (m * SR B) ≤
      setDistIn Rm univ (sphere B.1 (3 * B.2 / 4)) (sphere B.1 B.2))
    (hdiam : ∀ j < N, ∀ B ∈ F j, diamIn Rm (ann B.1 (B.2 / 2) (7 * B.2 / 2)) (sphere B.1 B.2) ≤
      ENNReal.ofReal (M * SR B))
    (hconn : ∀ j < N, ∀ B ∈ F j, ∀ u ∈ Icc (0 : ℝ) ℓ, ∀ v ∈ Icc (0 : ℝ) ℓ, u ≤ v →
      P '' Icc u v ⊆ annCl B.1 (3 * B.2 / 4) B.2 →
      ((‖P u - B.1‖ = B.2 ∧ ‖P v - B.1‖ = 3 * B.2 / 4) ∨
        (‖P u - B.1‖ = 3 * B.2 / 4 ∧ ‖P v - B.1‖ = B.2)) →
      Qm.1 (P u, P v) ≤ b' * (v - u))
    (hX : ∀ j ≤ N, 0 ≤ X j) (he : ∀ j ≤ N, 0 ≤ e j)
    (hstepC : ∀ j < N, (1 - m / (2 * M)) * X j + e j / (H⁻¹ * (rm j / 4) ^ β) ≤ X (j + 1))
    (hstepe : ∀ j < N, (b' + X j) * (2 * H * (2 * rp j) ^ σ) + e j ≤ e (j + 1))
    (hbase : ∀ u ∈ Icc (0 : ℝ) ℓ, ∀ v ∈ Icc (0 : ℝ) ℓ, Qm.1 (P u, P v) ≤ (b' + X 0) * |u - v| + e 0) :
    ∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ, s ≤ t → Qm.1 (P s, P t) ≤ (b' + X N) * (t - s) + e N := by
  -- induction on the number of bands used
  have key : ∀ k ≤ N, ∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ, s ≤ t →
      Qm.1 (P s, P t) ≤ (b' + X k) * (t - s) + e k := by
    intro k
    induction k with
    | zero =>
      intro _ s hs t ht hst
      have h := hbase s hs t ht
      rwa [abs_of_nonpos (by linarith : s - t ≤ 0), neg_sub] at h
    | succ k ih =>
      intro hk s hs t ht hst
      have hkN : k < N := hk
      have ih' := ih hkN.le
      have hrough : ∀ u ∈ Icc (0 : ℝ) ℓ, ∀ v ∈ Icc (0 : ℝ) ℓ,
          Qm.1 (P u, P v) ≤ (b' + X k) * |u - v| + e k := by
        intro u hu v hv
        rcases le_total u v with huv | hvu
        · rw [abs_of_nonpos (by linarith : u - v ≤ 0), neg_sub]
          exact ih' u hu v hv huv
        · rw [abs_of_nonneg (by linarith : 0 ≤ u - v), Qm.apply_comm]
          exact ih' v hv u hu hvu
      have h31 := lemma31b hd Rm Qm hRlen (F k) P ℓ W hℓ hW0 hgeo hPW (b' + X k) (e k) H σ β
        (rm k) (rp k) m M b' SR hm hM hmM hb' (by linarith [hX k hkN.le]) (he k hkN.le) hH hσ hβ
        (hrm k hkN) (hrmp k hkN) (hrp k hkN) hrough hmod (hF k hkN) (hcov k hkN) (hcross k hkN)
        (hdiam k hkN) (hconn k hkN) hs ht hst
      have hC := hstepC k hkN
      have hE := hstepe k hkN
      have hts : 0 ≤ t - s := by linarith
      have hcoef : b' + (1 - m / (2 * M)) * (b' + X k - b') + e k / (H⁻¹ * (rm k / 4) ^ β) ≤
          b' + X (k + 1) := by
        have : b' + X k - b' = X k := by ring
        rw [this]
        linarith
      calc Qm.1 (P s, P t) ≤ (b' + (1 - m / (2 * M)) * (b' + X k - b') +
            e k / (H⁻¹ * (rm k / 4) ^ β)) * (t - s) + (b' + X k) * (2 * H * (2 * rp k) ^ σ) + e k := h31
        _ ≤ (b' + X (k + 1)) * (t - s) + e (k + 1) := by
          have := mul_le_mul_of_nonneg_right hcoef hts
          linarith
  exact key N le_rfl

end HigherDimLQGContinuity
