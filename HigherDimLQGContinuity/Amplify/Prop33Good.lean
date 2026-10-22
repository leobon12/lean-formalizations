import HigherDimLQGContinuity.Amplify.Prop33Det
import HigherDimLQGContinuity.Amplify.Conn

/-!
# Proposition 3.3 on the good event (packet P7)

The deterministic step of Proposition 3.3 (`p7_amplify_det`) specialized to the metrics `ρ^D_g`, `ρ^E_g` of a field
`g`, the grid families of good recentred fields (local event `(H↑(D, E; b) ∪ PairRefsᶜ)ᶜ` at the local pin `s₁`) and the
connectors of `connector_of_good` (`p7ConnA`, `p7ConnB`), with the physical connector coefficient bounded by `b'`
(`hcoef`, from the scale cap). Output: `Comp(ρ^E_g, ρ^D_g; b + δ, e, R)` once `b' + X_N ≤ b + δ` and `e_N ≤ e`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open Set Metric MeasureTheory
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)
open HigherDimLQGMetric
open scoped ENNReal

variable {d : ℕ}

/-- **Proposition 3.3 at one good field.** -/
theorem p7_prop33_good (hd : 2 ≤ d) {ξ η : ℝ} {D E : DistRd d → ContMetric d} {g : DistRd d}
    {s₁ b b' R δ e S Hbar σ β m M C0 e0 n H₀ σ₀ β₀ : ℝ} {N : ℕ} {a : ℕ → ℝ} {X Ε : ℕ → ℝ}
    (hlen : (rho D g).IsLength)
    (hgeod : ∀ x y : Rd d, ∃ γ : C(unitInterval, Rd d), IsConstSpeedGeod (rho D g) x y γ)
    (hR : 0 ≤ R) (hS : 4 ≤ S) (hHbar : 1 ≤ Hbar) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hβ : 0 < β)
    (hm : 0 < m) (hM : 0 < M) (hmM : m ≤ M) (hb' : 0 ≤ b')
    (hesc : diamIn (rho D g) (ball (0 : Rd d) (2 * (R + 1))) (ball (0 : Rd d) (R + 1)) <
      setDistIn (rho D g) univ (sphere (0 : Rd d) (2 * (R + 1))) (sphere (0 : Rd d) (S * (R + 1))))
    (henvU : ∀ z ∈ closedBall (0 : Rd d) (S * (R + 1) + 1), ∀ s ∈ Ioc (0 : ℝ) 1,
      diamIn (rho D g) (ball z (2 * s)) (ball z s) ≤ ENNReal.ofReal (Hbar * s ^ σ))
    (henvL : ∀ x ∈ closedBall (0 : Rd d) (S * (R + 1) + 1), ∀ y ∈ closedBall (0 : Rd d) (S * (R + 1) + 1),
      Hbar⁻¹ * ‖x - y‖ ^ β ≤ (rho D g).1 (x, y))
    (hrough : CompOn (rho E g) (rho D g) C0 e0 (S * (R + 1) + 2))
    (hV : ∀ j < N, Real.log 4 ≤ a (j + 1) * n)
    (hcov : ∀ j < N, ∀ x ∈ closedBall (0 : Rd d) (S * (R + 1)), ∃ k ∈ p4_fullScales (a (j + 1) * n),
      ∃ i : Fin d → ℤ, ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) i‖ < p4_radius k / 10 ∧
        recentre s₁ (p4_radius k) (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) i) g ∈
          (Hup D E b ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ)ᶜ)
    (hconn : ∀ B ∈ p7GridBall d, recentre s₁ B.2 B.1 g ∈ PairRefs D E H₀ σ₀ β₀ m M →
      p7ConnA D E ξ η s₁ m M g B ∧ (recentre s₁ B.2 B.1 g ∉ Hup D E b → p7ConnB D E ξ η s₁ b g B))
    (hcoef : ∀ j < N, ∀ B ∈ p7BandSet d (a (j + 1) * n) (S * (R + 1))
        (fun B : SewBall d => recentre s₁ B.2 B.1 g ∈ (Hup D E b ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ)ᶜ),
      b * (scaleS d η s₁ B.2 B.1 g / scaleS d ξ s₁ B.2 B.1 g) ≤ b')
    (hX : ∀ j ≤ N, 0 ≤ X j) (hΕ : ∀ j ≤ N, 0 ≤ Ε j) (hX0 : C0 ≤ X 0) (hΕ0 : e0 ≤ Ε 0)
    (hstepC : ∀ j < N,
      (1 - m / (2 * M)) * X j + Ε j / ((2 * Hbar)⁻¹ * (Real.exp (-2 * (a (j + 1) * n)) / 4) ^ β) ≤
        X (j + 1))
    (hstepE : ∀ j < N,
      (b' + X j) * (2 * (2 * Hbar) * (2 * Real.exp (-(a (j + 1) * n))) ^ σ) + Ε j ≤ Ε (j + 1))
    (hfinC : b' + X N ≤ b + δ) (hfinE : Ε N ≤ e) :
    CompOn (rho E g) (rho D g) (b + δ) e R := by
  set good : SewBall d → Prop :=
    fun B : SewBall d => recentre s₁ B.2 B.1 g ∈ (Hup D E b ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ)ᶜ with hgooddef
  have hgoodRefs : ∀ B : SewBall d, good B →
      recentre s₁ B.2 B.1 g ∈ PairRefs D E H₀ σ₀ β₀ m M ∧ recentre s₁ B.2 B.1 g ∉ Hup D E b := by
    intro B hB
    simp only [hgooddef, mem_compl_iff, mem_union, not_or, not_not] at hB
    exact ⟨hB.2, hB.1⟩
  have hdet := p7_amplify_det hd (rho D g) (rho E g) hlen hgeod (R := R) (S := S) (Hbar := Hbar)
    (σ := σ) (β := β) (m := m) (M := M) (b' := b') (C0 := C0) (e0 := e0) hR hS hHbar hσ hσ1 hβ hm hM
    hmM hb' hesc henvU henvL hrough N (fun j => a (j + 1) * n) good
    (fun B => scaleS d ξ s₁ B.2 B.1 g) hV hcov
    (fun j hj B hB => by
      have hgrid := p7BandSet_subset_gridBall hB
      obtain ⟨hrefs, hnup⟩ := hgoodRefs B hB.2.2
      obtain ⟨hA, hBc⟩ := hconn B hgrid hrefs
      refine ⟨scaleS_pos d ξ s₁ (p7GridBall_radius_pos hgrid) B.1 g, hA.1.1, hA.1.2, ?_⟩
      intro P' u v huv hgeo hsub hends
      have h1 := hBc hnup P' u v huv hgeo hsub hends
      have h2 := hcoef j hj B hB
      have huv' : 0 ≤ v - u := by linarith
      calc (rho E g).1 (P' u, P' v)
          ≤ b * (scaleS d η s₁ B.2 B.1 g / scaleS d ξ s₁ B.2 B.1 g) * (v - u) := h1
        _ ≤ b' * (v - u) := mul_le_mul_of_nonneg_right h2 huv')
    X Ε hX hΕ hX0 hΕ0 hstepC hstepE
  intro x hx y hy
  have h := hdet x hx y hy
  have hD0 : 0 ≤ (rho D g).1 (x, y) := (rho D g).nonneg x y
  have h1 : (b' + X N) * (rho D g).1 (x, y) ≤ (b + δ) * (rho D g).1 (x, y) :=
    mul_le_mul_of_nonneg_right hfinC hD0
  linarith

end HigherDimLQGContinuity
