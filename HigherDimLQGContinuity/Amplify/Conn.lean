import HigherDimLQGContinuity.Amplify.Grid
import HigherDimLQGContinuity.Events.Connector

/-!
# Connectors at all grid balls simultaneously (packet P7)

`connector_of_good` (packet P5b, blueprint `a:lem-connector`) holds for each fixed ball `B_r(z)` outside a null set
depending on `(r, z)`. Lemma 3.2 and Proposition 3.3 use it simultaneously at the countably many grid balls
`(z, r) = (latPt (κ₀ 2^{-k}) j, 2^{-k})` (`p7GridBall`), which contain every band set (`p7BandSet_subset_gridBall`).
`p7ConnA` is part (a) of its conclusion (crossings and annular diameters of both metrics), `p7ConnB` part (b) (the
physical connector of the ordered pair `(D, E)`), both at a ball `B : SewBall d` (centre `B.1`, radius `B.2`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open Set Metric MeasureTheory
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)
open HigherDimLQGMetric

variable {d : ℕ}

/-- The grid balls `(latPt (κ₀ 2^{-k}) j, 2^{-k})`, `k ∈ ℕ`, `j ∈ ℤ^d`. -/
def p7GridBall (d : ℕ) : Set (SewBall d) :=
  {B | ∃ k : ℕ, ∃ j : Fin d → ℤ,
    B.2 = p4_radius k ∧ B.1 = latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j}

theorem p7BandSet_subset_gridBall {V W : ℝ} {good : SewBall d → Prop} :
    p7BandSet d V W good ⊆ p7GridBall d := by
  intro B hB
  obtain ⟨⟨k, -, j, hr, hz⟩, -, -⟩ := hB
  exact ⟨k, j, hr, hz⟩

theorem p7GridBall_radius_pos {B : SewBall d} (hB : B ∈ p7GridBall d) : 0 < B.2 := by
  obtain ⟨k, j, hr, -⟩ := hB
  rw [hr]
  exact p7_p4_radius_pos k

/-- Part (a) of `connector_of_good` at the ball `B`: crossings and annular diameters of `ρ^D` and `ρ^E` with the
scale factors `S_D = scaleS d ξ s r z g`, `S_E = scaleS d η s r z g`. -/
def p7ConnA (D E : DistRd d → ContMetric d) (ξ η s m M : ℝ) (g : DistRd d) (B : SewBall d) : Prop :=
  (ENNReal.ofReal (m * scaleS d ξ s B.2 B.1 g) ≤
        setDistIn (rho D g) univ (sphere B.1 (3 * B.2 / 4)) (sphere B.1 B.2) ∧
      diamIn (rho D g) (ann B.1 (B.2 / 2) (7 * B.2 / 2)) (sphere B.1 B.2) ≤
        ENNReal.ofReal (M * scaleS d ξ s B.2 B.1 g)) ∧
    (ENNReal.ofReal (m * scaleS d η s B.2 B.1 g) ≤
        setDistIn (rho E g) univ (sphere B.1 (3 * B.2 / 4)) (sphere B.1 B.2) ∧
      diamIn (rho E g) (ann B.1 (B.2 / 2) (7 * B.2 / 2)) (sphere B.1 B.2) ≤
        ENNReal.ofReal (M * scaleS d η s B.2 B.1 g))

/-- Part (b) of `connector_of_good` at the ball `B`: blocks of length-parametrized `ρ^D`-geodesics crossing the
annulus `annCl z (3r/4) r` (either orientation) have `ρ^E`-distance at most `b (S_E/S_D)` times their length. -/
def p7ConnB (D E : DistRd d → ContMetric d) (ξ η s b : ℝ) (g : DistRd d) (B : SewBall d) : Prop :=
  ∀ (P : ℝ → Rd d) (u v : ℝ), u ≤ v →
    (∀ a ∈ Icc u v, ∀ a' ∈ Icc u v, (rho D g).1 (P a, P a') = |a - a'|) →
    P '' Icc u v ⊆ annCl B.1 (3 * B.2 / 4) B.2 →
    ((‖P u - B.1‖ = B.2 ∧ ‖P v - B.1‖ = 3 * B.2 / 4) ∨
      (‖P u - B.1‖ = 3 * B.2 / 4 ∧ ‖P v - B.1‖ = B.2)) →
    (rho E g).1 (P u, P v) ≤ b * (scaleS d η s B.2 B.1 g / scaleS d ξ s B.2 B.1 g) * (v - u)

/-- `connector_of_good` (a) and (b), almost surely simultaneously at all grid balls. -/
theorem p7_ae_connector_grid (hd : 2 ≤ d) {ξ η : ℝ} (hξ : 0 < ξ) (hη : 0 < η)
    {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) (hE : IsStrongExpMetric d η (distExp d η) E)
    {s s₀ : ℝ} (hs₀ : 0 < s₀) {b : ℝ} (hb : 0 ≤ b) (H₀ σ₀ β₀ m M : ℝ) :
    ∀ᵐ g ∂(pinLaw d s₀), ∀ B ∈ p7GridBall d, recentre s B.2 B.1 g ∈ PairRefs D E H₀ σ₀ β₀ m M →
      p7ConnA D E ξ η s m M g B ∧ (recentre s B.2 B.1 g ∉ Hup D E b → p7ConnB D E ξ η s b g B) := by
  have hall : ∀ᵐ g ∂(pinLaw d s₀), ∀ kj : ℕ × (Fin d → ℤ),
      recentre s (p4_radius kj.1) (latPt ((1 / (20 * Real.sqrt d)) * p4_radius kj.1) kj.2) g ∈
          PairRefs D E H₀ σ₀ β₀ m M →
        p7ConnA D E ξ η s m M g (latPt ((1 / (20 * Real.sqrt d)) * p4_radius kj.1) kj.2, p4_radius kj.1) ∧
          (recentre s (p4_radius kj.1) (latPt ((1 / (20 * Real.sqrt d)) * p4_radius kj.1) kj.2) g ∉
              Hup D E b →
            p7ConnB D E ξ η s b g
              (latPt ((1 / (20 * Real.sqrt d)) * p4_radius kj.1) kj.2, p4_radius kj.1)) := by
    rw [ae_all_iff]
    intro kj
    filter_upwards [connector_of_good hd hξ hη hD hE (s := s) hs₀ (p7_p4_radius_pos kj.1)
      (latPt ((1 / (20 * Real.sqrt d)) * p4_radius kj.1) kj.2) hb H₀ σ₀ β₀ m M] with g hg
    intro hrefs
    obtain ⟨ha, hb', -⟩ := hg hrefs
    exact ⟨ha, hb'⟩
  filter_upwards [hall] with g hg
  intro B hB hrefs
  obtain ⟨k, j, hr, hz⟩ := hB
  have hBeq : B = (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j, p4_radius k) :=
    Prod.ext hz hr
  subst hBeq
  exact hg (k, j) hrefs

end HigherDimLQGContinuity
