import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Improve.Diameter
import HigherDimLQGContinuity.Improve.Envelope
import HigherDimLQGContinuity.Improve.Barrier

/-!
# Fixed source geometry for Proposition 3.5

This packages Step 0 (P2): a local competitor, an outer barrier, and a
two-sided source envelope under the radius-ten pin. The constants precede
the parameter and metric quantifiers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open scoped ENNReal

/-- The three deterministic source conditions used in the proof of
Proposition 3.5. -/
def Q11SourceGood {d : ℕ} (G : ContMetric d) (U0 R H σ β : ℝ) : Prop :=
  diamIn G (ball 0 9) (closedBall (0 : Rd d) 8) ≤ ENNReal.ofReal (U0 / 4) ∧
  ENNReal.ofReal (2 * U0) < setDistIn G univ (sphere 0 8) (sphere 0 R) ∧
  (∀ z ∈ closedBall (0 : Rd d) (R + 1), ∀ r ∈ Ioc (0 : ℝ) 1,
    diamIn G (ball z (2 * r)) (ball z r) ≤ ENNReal.ofReal (H * r ^ σ)) ∧
  (∀ x ∈ closedBall (0 : Rd d) (R + 1), ∀ y ∈ closedBall (0 : Rd d) (R + 1),
    H⁻¹ * ‖x - y‖ ^ β ≤ G.1 (x, y))

/-- Lemma 2.1 supplies all fixed source geometry with uniformly small
failure probability. -/
theorem q11_source_good_prob {d : ℕ} (hd : 3 ≤ d) {ξbar : ℝ}
    (hU : UniformEstimates d ξbar 10) {pt : ℝ} (hpt : 0 < pt) :
    ∃ U0 R H σ β : ℝ,
      1 ≤ U0 ∧ 16 ≤ R ∧ 1 ≤ H ∧ 0 < σ ∧ σ < 1 ∧ 1 < β ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
          pinLaw d 10 {g | ¬ Q11SourceGood (rho D g) U0 R H σ β} ≤
            ENNReal.ofReal (pt / 8) := by
  let δ : ℝ := pt / 32
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨M, hM, hdiam⟩ := q11_diameter_prob (by omega : 2 ≤ d)
    (by norm_num : (0 : ℝ) < 10) hδ hU
  let U0 : ℝ := max 1 (4 * M)
  have hU01 : 1 ≤ U0 := le_max_left _ _
  have hU0 : 0 < U0 := lt_of_lt_of_le one_pos hU01
  have hMU : M ≤ U0 / 4 := by
    have h := le_max_right (1 : ℝ) (4 * M)
    dsimp [U0]
    linarith
  obtain ⟨S, hS, hbarrier⟩ := q11_barrier_prob hd
    (by norm_num : (0 : ℝ) < 10) (show 0 < U0 / 4 by positivity) hδ hU
  let R : ℝ := 4 * S
  have hR : 16 ≤ R := by dsimp [R]; linarith
  have hR1 : 1 ≤ R + 1 := by linarith
  obtain ⟨H, σ, β, hH, hσ, hσ1, hβ, henv⟩ :=
    q11_envelope_prob hR1 hδ hU
  refine ⟨U0, R, H, σ, β, hU01, hR, hH, hσ, hσ1, hβ, ?_⟩
  intro ξ hξ D hD
  let Bdiam : Set (DistRd d) := {g | ¬ diamIn (rho D g) (ball 0 9)
    (closedBall (0 : Rd d) 8) ≤ ENNReal.ofReal M}
  let Bbarrier : Set (DistRd d) := {g | ¬ ENNReal.ofReal (2 * U0) <
    setDistIn (rho D g) univ (sphere 0 8) (sphere 0 R)}
  let Benv : Set (DistRd d) := {g | ¬ ((∀ z ∈ closedBall (0 : Rd d) (R + 1),
      ∀ r ∈ Ioc (0 : ℝ) 1,
        diamIn (rho D g) (ball z (2 * r)) (ball z r) ≤ ENNReal.ofReal (H * r ^ σ)) ∧
    (∀ x ∈ closedBall (0 : Rd d) (R + 1), ∀ y ∈ closedBall (0 : Rd d) (R + 1),
      H⁻¹ * ‖x - y‖ ^ β ≤ (rho D g).1 (x, y)))}
  have hsub : {g | ¬ Q11SourceGood (rho D g) U0 R H σ β} ⊆
      Bdiam ∪ Bbarrier ∪ Benv := by
    intro g hg
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨hBd, hBb⟩, hBe⟩ := hnot
    apply hg
    refine ⟨?_, not_not.mp hBb, ?_, ?_⟩
    · exact (not_not.mp hBd).trans (ENNReal.ofReal_le_ofReal hMU)
    · exact (not_not.mp hBe).1
    · exact (not_not.mp hBe).2
  have hdiam' : pinLaw d 10 Bdiam ≤ ENNReal.ofReal δ := hdiam ξ hξ D hD
  have hbarrier' : pinLaw d 10 Bbarrier ≤ ENNReal.ofReal δ := by
    have h := hbarrier ξ hξ D hD
    simpa only [Bbarrier, R, show (8 : ℝ) * (U0 / 4) = 2 * U0 by ring,
      mul_comm S 4] using h
  have henv' : pinLaw d 10 Benv ≤ ENNReal.ofReal δ := henv ξ hξ D hD
  calc
    pinLaw d 10 {g | ¬ Q11SourceGood (rho D g) U0 R H σ β}
        ≤ pinLaw d 10 (Bdiam ∪ Bbarrier ∪ Benv) := measure_mono hsub
    _ ≤ pinLaw d 10 Bdiam + pinLaw d 10 Bbarrier + pinLaw d 10 Benv := by
          exact (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ + ENNReal.ofReal δ := by
          exact add_le_add (add_le_add hdiam' hbarrier') henv'
    _ ≤ ENNReal.ofReal (pt / 8) := by
      rw [← ENNReal.ofReal_add hδ.le hδ.le, ← ENNReal.ofReal_add (by positivity) hδ.le]
      apply ENNReal.ofReal_le_ofReal
      dsimp [δ]
      linarith

end HigherDimLQGContinuity
