import SmallGammaGeodesics.CC.Prop21Det
import LQGMetric.Metric.InternalLimitC

/-!
# [3] Prop 2.1: the good events on the NIC space exclude the localized bad event
(packet CC6b; CC0 Details D10)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D10** and CC6a's recipe
(`planning/handoffs/CC6a.md`, Details §2, items 1–4). Deterministic, for one sample of the NIC
space of the zoom at `(z, r)`: `X = D_{h}` (the NIC field `h`, a length metric), `M_d = X(·,·;B)`,
`M_c` the coupled internal metric `D_{h̄ + K̃}(·,·;B)` on `B = B_{R/2}`, `c = ϕ'(z)`.

`not_locBad_of_good`: if
* (CC6a, D9) `|M_c − M_d| ≤ δ₁ E` on `K₁ = B̄_{R/4}`;
* (diameter) `X(y, y') < S 𝔰` on `B̄_{2M}`;
* (crossing) `X(y, w) > A` for `y ∈ B̄_{2M}`, `w ∈ ∂B_{R/4} ∪ ∂B_{R/2}`;
* (modulus) `X(y, y') < s₁ 𝔰` on `B̄_{2M}` when `|y − y'| ≤ C r`;
* `S 𝔰 + 2 δ₁ E ≤ A` and `κ (2 s₁ 𝔰 + δ₁ E) ≤ δ`;
and the three functions of the localized event are `κ X(c·, c·)`, `κ M_d(c·, c·)` and
`κ M_c(ϕ̃ ·, ϕ̃ ·)` with `ϕ̃ u = Ξinv(c u)` on `B_1`, `|Ξinv x − x| ≤ C r`, `ϕ̃(T) ⊆ ∂B_{R/4}`, then
the
localized bad event fails.

The three steps are D10's: **localization** (the crossing bound beats the diameter, so
`M_d = X` on `B̄_{2M}`, `ContMetric.internal_eq_of_lt_infEDist_frontier`), the **conformal
localization condition** (`M_c(y, y') ≤ M_c(y, w)` for `w ∈ ∂B_{R/4}`), and **replacing `χ⁻¹` by the
identity** (`M_d(Ξinv x, x) = X(Ξinv x, x) < s₁ 𝔰` and the triangle inequality).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.MetricGeometry

/-- `X(y, y') ≤ X(y, y'; U)` -/
theorem ContMetric.ofReal_le_internal (X : ContMetric) (U : Set ℂ) (y y' : ℂ) :
    ENNReal.ofReal (X.1 (y, y')) ≤ X.internal U y y' := by
  rw [← ContMetric.edist_pt]
  exact edist_le_internalEDist _ _ _

/-- the triangle inequality for internal metrics -/
theorem ContMetric.internal_triangle (X : ContMetric) (U : Set ℂ) (x y z : ℂ) :
    X.internal U x z ≤ X.internal U x y + X.internal U y z :=
  internalEDist_triangle _ _ _ _

theorem ContMetric.internal_comm (X : ContMetric) (U : Set ℂ) (x y : ℂ) :
    X.internal U x y = X.internal U y x :=
  internalEDist_comm _ _ _

/-- **Localization by a crossing bound**: if `X(y, y') < A ≤ X(y, w)` for every `w ∈ ∂B_ρ`,
`y ∈ B_ρ`, then `X(y, y'; B_ρ) = X(y, y')`. -/
theorem ContMetric.internal_ball_eq_of_lt {X : ContMetric} (hX : X.IsLength) {ρ A : ℝ}
    (hρ : 0 < ρ) {y y' : ℂ} (hy : y ∈ ball (0 : ℂ) ρ) (hlt : X.1 (y, y') < A)
    (hcross : ∀ w ∈ sphere (0 : ℂ) ρ, A ≤ X.1 (y, w)) :
    X.internal (ball 0 ρ) y y' = ENNReal.ofReal (X.1 (y, y')) := by
  have hA : 0 < A := lt_of_le_of_lt (ContMetric.nonneg X y y') hlt
  have hinf : ENNReal.ofReal A ≤ Metric.infEDist (X.pt y) (X.pt '' frontier (ball (0 : ℂ) ρ)) := by
    refine Metric.le_infEDist.2 fun p hp => ?_
    obtain ⟨w, hw, rfl⟩ := hp
    rw [frontier_ball (0 : ℂ) hρ.ne'] at hw
    rw [ContMetric.edist_pt]
    exact ENNReal.ofReal_le_ofReal (hcross w hw)
  have hv : edist (X.pt y) (X.pt y') < Metric.infEDist (X.pt y) (X.pt '' frontier (ball 0 ρ)) := by
    rw [ContMetric.edist_pt]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hA).2 hlt) hinf
  rw [(ContMetric.internal_eq_of_lt_infEDist_frontier hX isOpen_ball hy hv).2, ContMetric.edist_pt]

/-- **The good events on the NIC space exclude the localized bad event** (D10, deterministic). -/
theorem not_locBad_of_good {X : ContMetric} (hX : X.IsLength) {Mc : ℂ → ℂ → ℝ≥0∞}
    {c : ℂ} {ϕt Ξi : ℂ → ℂ} {T : Set ℂ} {dg dl n : ℂ → ℂ → ℝ≥0∞}
    {R M Cr κ δ δ₁ E S A s₁ 𝔰 : ℝ} (hR : 0 < R) (hM : 2 * M ≤ R / 4) (hcM : ‖c‖ ≤ M)
    (hCrM : Cr ≤ M) (hκ : 0 < κ) (hδ₁E : 0 ≤ δ₁ * E)
    (hdg : ∀ u v, dg u v = ENNReal.ofReal (κ * X.1 (c * u, c * v)))
    (hdl : ∀ u v, dl u v = ENNReal.ofReal κ * X.internal (ball 0 (R / 2)) (c * u) (c * v))
    (hn : ∀ u ∈ ball (0 : ℂ) 1, ∀ v, v ∈ ball (0 : ℂ) 1 ∪ T →
      n u v = ENNReal.ofReal κ * Mc (ϕt u) (ϕt v))
    (hϕt : ∀ u ∈ ball (0 : ℂ) 1, ϕt u = Ξi (c * u)) (hΞi : ∀ x, ‖Ξi x - x‖ ≤ Cr)
    (hT : ∀ w ∈ T, ϕt w ∈ sphere (0 : ℂ) (R / 4))
    (hcc : ∀ y ∈ closedBall (0 : ℂ) (R / 4), ∀ y' ∈ closedBall (0 : ℂ) (R / 4),
      Mc y y' ≤ X.internal (ball 0 (R / 2)) y y' + ENNReal.ofReal (δ₁ * E) ∧
      X.internal (ball 0 (R / 2)) y y' ≤ Mc y y' + ENNReal.ofReal (δ₁ * E))
    (hdiam : ∀ y ∈ closedBall (0 : ℂ) (2 * M), ∀ y' ∈ closedBall (0 : ℂ) (2 * M),
      X.1 (y, y') < S * 𝔰)
    (hcross : ∀ y ∈ closedBall (0 : ℂ) (2 * M), ∀ w ∈ sphere (0 : ℂ) (R / 4) ∪ sphere 0 (R / 2),
      A < X.1 (y, w))
    (hmod : ∀ y ∈ closedBall (0 : ℂ) (2 * M), ∀ y' ∈ closedBall (0 : ℂ) (2 * M),
      ‖y - y'‖ ≤ Cr → X.1 (y, y') < s₁ * 𝔰)
    (hSA : S * 𝔰 + 2 * (δ₁ * E) ≤ A) (hκδ : κ * (2 * (s₁ * 𝔰) + δ₁ * E) ≤ δ) :
    ¬ LocBad δ T dg dl n := by
  have hR4 : 0 < R / 4 := by positivity
  have hR2 : 0 < R / 2 := by positivity
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hcM
  set B : Set ℂ := ball (0 : ℂ) (R / 2) with hB
  set Md : ℂ → ℂ → ℝ≥0∞ := X.internal B with hMd
  have h2M : ∀ y ∈ closedBall (0 : ℂ) (2 * M), y ∈ closedBall (0 : ℂ) (R / 4) := fun y hy =>
    closedBall_subset_closedBall hM hy
  have h2MB : ∀ y ∈ closedBall (0 : ℂ) (2 * M), y ∈ B := fun y hy =>
    mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hy) (by linarith))
  -- **localization** of `M_d` on `B̄_{2M}`
  have hloc : ∀ y ∈ closedBall (0 : ℂ) (2 * M), ∀ y' ∈ closedBall (0 : ℂ) (2 * M),
      Md y y' = ENNReal.ofReal (X.1 (y, y')) := fun y hy y' hy' =>
    ContMetric.internal_ball_eq_of_lt hX hR2 (h2MB y hy)
      (lt_of_lt_of_le (hdiam y hy y' hy') (by linarith))
      fun w hw => (hcross y hy w (Or.inr hw)).le
  -- the points
  have hcu : ∀ u ∈ ball (0 : ℂ) 1, c * u ∈ closedBall (0 : ℂ) (2 * M) := fun u hu => by
    rw [mem_closedBall_zero_iff, norm_mul]
    have := mem_ball_zero_iff.1 hu
    nlinarith [norm_nonneg c, norm_nonneg u]
  have hyu : ∀ u ∈ ball (0 : ℂ) 1, ϕt u ∈ closedBall (0 : ℂ) (2 * M) := fun u hu => by
    rw [hϕt u hu, mem_closedBall_zero_iff]
    have h1 := hΞi (c * u)
    have h2 := mem_closedBall_zero_iff.1 (hcu u hu)
    have h3 : ‖c * u‖ ≤ M := by
      rw [norm_mul]
      have := mem_ball_zero_iff.1 hu
      nlinarith [norm_nonneg c, norm_nonneg u]
    calc ‖Ξi (c * u)‖ = ‖(Ξi (c * u) - c * u) + c * u‖ := by rw [sub_add_cancel]
      _ ≤ ‖Ξi (c * u) - c * u‖ + ‖c * u‖ := norm_add_le _ _
      _ ≤ 2 * M := by linarith
  have hclose : ∀ u ∈ ball (0 : ℂ) 1, ‖ϕt u - c * u‖ ≤ Cr := fun u hu => by
    rw [hϕt u hu]; exact hΞi _
  have hofE : ENNReal.ofReal (δ₁ * E) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [not_locBad_iff]
  intro u hu v hv
  have hu' := hcu u hu
  have hv' := hcu v hv
  have hyu' := hyu u hu
  have hyv' := hyu v hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (i) the global metric is realized in `A_d`
    rw [hdl, hdg, hloc _ hu' _ hv', ← ENNReal.ofReal_mul hκ.le]
  · -- (ii) the conformal localization condition
    intro w hw
    rw [hn u hu v (Or.inl hv), hn u hu w (Or.inr hw)]
    refine mul_le_mul_right ?_ _
    have hw' := hT w hw
    have hwK : ϕt w ∈ closedBall (0 : ℂ) (R / 4) := sphere_subset_closedBall hw'
    have h1 : Mc (ϕt u) (ϕt v) + ENNReal.ofReal (δ₁ * E) ≤ ENNReal.ofReal A := by
      calc Mc (ϕt u) (ϕt v) + ENNReal.ofReal (δ₁ * E)
          ≤ (Md (ϕt u) (ϕt v) + ENNReal.ofReal (δ₁ * E)) + ENNReal.ofReal (δ₁ * E) :=
            add_le_add (hcc _ (h2M _ hyu') _ (h2M _ hyv')).1 le_rfl
        _ = ENNReal.ofReal (X.1 (ϕt u, ϕt v) + δ₁ * E + δ₁ * E) := by
            rw [hloc _ hyu' _ hyv', ← ENNReal.ofReal_add (ContMetric.nonneg X _ _) hδ₁E,
              ← ENNReal.ofReal_add (by linarith [ContMetric.nonneg X (ϕt u) (ϕt v)]) hδ₁E]
        _ ≤ ENNReal.ofReal A := by
            refine ENNReal.ofReal_le_ofReal ?_
            have := hdiam _ hyu' _ hyv'
            linarith
    have h2 : ENNReal.ofReal A ≤ Mc (ϕt u) (ϕt w) + ENNReal.ofReal (δ₁ * E) :=
      (ENNReal.ofReal_le_ofReal (hcross _ hyu' _ (Or.inl hw')).le).trans
        ((ContMetric.ofReal_le_internal X B _ _).trans (hcc _ (h2M _ hyu') _ hwK).2)
    exact (ENNReal.add_le_add_iff_right hofE).1 (h1.trans h2)
  · -- (iii) upper comparison, replacing `χ⁻¹` by the identity
    rw [hn u hu v (Or.inl hv), hdl]
    have hmu : X.1 (ϕt u, c * u) < s₁ * 𝔰 := hmod _ hyu' _ hu' (hclose u hu)
    have hmv : X.1 (c * v, ϕt v) < s₁ * 𝔰 := by
      have := hmod _ hv' _ hyv' (by rw [norm_sub_rev]; exact hclose v hv)
      exact this
    have key : Mc (ϕt u) (ϕt v) ≤
        Md (c * u) (c * v) + ENNReal.ofReal (2 * (s₁ * 𝔰) + δ₁ * E) := by
      calc Mc (ϕt u) (ϕt v) ≤ Md (ϕt u) (ϕt v) + ENNReal.ofReal (δ₁ * E) :=
            (hcc _ (h2M _ hyu') _ (h2M _ hyv')).1
        _ ≤ (Md (ϕt u) (c * u) + Md (c * u) (c * v) + Md (c * v) (ϕt v)) +
            ENNReal.ofReal (δ₁ * E) := by
            refine add_le_add ?_ le_rfl
            exact (ContMetric.internal_triangle X B _ (c * v) _).trans
              (add_le_add (ContMetric.internal_triangle X B _ _ _) le_rfl)
        _ = (ENNReal.ofReal (X.1 (ϕt u, c * u)) + Md (c * u) (c * v) +
            ENNReal.ofReal (X.1 (c * v, ϕt v))) + ENNReal.ofReal (δ₁ * E) := by
            rw [hloc _ hyu' _ hu', hloc _ hv' _ hyv']
        _ ≤ (ENNReal.ofReal (s₁ * 𝔰) + Md (c * u) (c * v) + ENNReal.ofReal (s₁ * 𝔰)) +
            ENNReal.ofReal (δ₁ * E) :=
            add_le_add (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hmu.le) le_rfl)
              (ENNReal.ofReal_le_ofReal hmv.le)) le_rfl
        _ = Md (c * u) (c * v) + ENNReal.ofReal (2 * (s₁ * 𝔰) + δ₁ * E) := by
            have hs : 0 ≤ s₁ * 𝔰 := (ContMetric.nonneg X _ _).trans hmu.le
            rw [ENNReal.ofReal_add (by linarith) hδ₁E, two_mul, ENNReal.ofReal_add hs hs]
            ring
    calc ENNReal.ofReal κ * Mc (ϕt u) (ϕt v)
        ≤ ENNReal.ofReal κ * (Md (c * u) (c * v) + ENNReal.ofReal (2 * (s₁ * 𝔰) + δ₁ * E)) :=
          mul_le_mul_right key _
      _ = ENNReal.ofReal κ * Md (c * u) (c * v) +
          ENNReal.ofReal (κ * (2 * (s₁ * 𝔰) + δ₁ * E)) := by
          rw [mul_add, ← ENNReal.ofReal_mul hκ.le]
      _ ≤ ENNReal.ofReal κ * X.internal (ball 0 (R / 2)) (c * u) (c * v) + ENNReal.ofReal δ :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal hκδ)
  · -- (iii) lower comparison
    rw [hn u hu v (Or.inl hv), hdl]
    have hmu : X.1 (c * u, ϕt u) < s₁ * 𝔰 := by
      have := hmod _ hu' _ hyu' (by rw [norm_sub_rev]; exact hclose u hu)
      exact this
    have hmv : X.1 (ϕt v, c * v) < s₁ * 𝔰 := hmod _ hyv' _ hv' (hclose v hv)
    have key : Md (c * u) (c * v) ≤
        Mc (ϕt u) (ϕt v) + ENNReal.ofReal (2 * (s₁ * 𝔰) + δ₁ * E) := by
      calc Md (c * u) (c * v) ≤ Md (c * u) (ϕt u) + Md (ϕt u) (ϕt v) + Md (ϕt v) (c * v) :=
            (ContMetric.internal_triangle X B _ (ϕt v) _).trans
              (add_le_add (ContMetric.internal_triangle X B _ _ _) le_rfl)
        _ ≤ ENNReal.ofReal (X.1 (c * u, ϕt u)) + (Mc (ϕt u) (ϕt v) + ENNReal.ofReal (δ₁ * E)) +
            ENNReal.ofReal (X.1 (ϕt v, c * v)) := by
            rw [hloc _ hu' _ hyu', hloc _ hyv' _ hv']
            exact add_le_add (add_le_add le_rfl (hcc _ (h2M _ hyu') _ (h2M _ hyv')).2) le_rfl
        _ ≤ ENNReal.ofReal (s₁ * 𝔰) + (Mc (ϕt u) (ϕt v) + ENNReal.ofReal (δ₁ * E)) +
            ENNReal.ofReal (s₁ * 𝔰) :=
            add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hmu.le) le_rfl)
              (ENNReal.ofReal_le_ofReal hmv.le)
        _ = Mc (ϕt u) (ϕt v) + ENNReal.ofReal (2 * (s₁ * 𝔰) + δ₁ * E) := by
            have hs : 0 ≤ s₁ * 𝔰 := (ContMetric.nonneg X _ _).trans hmu.le
            rw [ENNReal.ofReal_add (by linarith) hδ₁E, two_mul, ENNReal.ofReal_add hs hs]
            ring
    calc ENNReal.ofReal κ * X.internal (ball 0 (R / 2)) (c * u) (c * v)
        ≤ ENNReal.ofReal κ * (Mc (ϕt u) (ϕt v) + ENNReal.ofReal (2 * (s₁ * 𝔰) + δ₁ * E)) :=
          mul_le_mul_right key _
      _ = ENNReal.ofReal κ * Mc (ϕt u) (ϕt v) +
          ENNReal.ofReal (κ * (2 * (s₁ * 𝔰) + δ₁ * E)) := by
          rw [mul_add, ← ENNReal.ofReal_mul hκ.le]
      _ ≤ ENNReal.ofReal κ * Mc (ϕt u) (ϕt v) + ENNReal.ofReal δ :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal hκδ)

end SmallGammaGeodesics.CC
