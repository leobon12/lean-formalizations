import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChain
import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSitePathInU

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_good_site_chain {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n N : ℕ)
    (x : ℕ → ℂ) (U : Set ℂ) (T : ℝ) (hT : 0 < T) (ω : Ω)
    (hgood : ∀ j ≤ N, ω ∈ ptDistSiteGood P W ξ Q ζ C n j (x j) T)
    (hnear : ∀ j < N,
      dist (x (j + 1)) (x j) ≤ 3 * ((2 : ℝ)⁻¹ ^ (j + 1)) / 4)
    (hball : ∀ j ≤ N,
      ball (x j) (17 * ((2 : ℝ)⁻¹ ^ j)) ⊆ U) :
    let f : ℂ → ℝ := fun z => phiMN W P 0 n z ω
    let a (j : ℕ) : ℝ := Real.exp ((ξ : ℝ) * phiMN W P 0 j (x j) ω) *
      (T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (j : ℝ)) * lambdaN ξ W P n))
    let L (j : ℕ) : ℝ := T * (C *
      (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (j : ℝ)) * lambdaN ξ W P n) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 j (x j) ω)
    ∃ u ∈ sphere (x 0) (((2 : ℝ)⁻¹ ^ 0) / 4),
      ∃ v ∈ sphere (x N) (((2 : ℝ)⁻¹ ^ N) / 4),
        lfppDOn (ξ : ℝ) f U u v ≤
          ∑ j ∈ Finset.range N,
            (ENNReal.ofReal (2 * a (j + 1)) + ENNReal.ofReal (L (j + 1)) +
              ENNReal.ofReal (2 * a j)) := by
  dsimp
  let f : ℂ → ℝ := fun z => phiMN W P 0 n z ω
  let a (j : ℕ) : ℝ := Real.exp ((ξ : ℝ) * phiMN W P 0 j (x j) ω) *
      (T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (j : ℝ)) * lambdaN ξ W P n))
  let L (j : ℕ) : ℝ := T * (C *
      (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (j : ℝ)) * lambdaN ξ W P n) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 j (x j) ω)
  have hexists (j : ℕ) : ∃ p : ℝ → ℂ, j ≤ N →
      AdmPath U (sphere (x j) (((2 : ℝ)⁻¹ ^ j) / 4))
        (sphere (x j) (16 * ((2 : ℝ)⁻¹ ^ j))) p ∧
      lfppLen (ξ : ℝ) f p < ENNReal.ofReal (2 * a j) := by
    by_cases hj : j ≤ N
    · obtain ⟨p, hp, hlen⟩ :=
        pt_dist_site_crossing_path_in_U P W hW ξ Q ζ C n j (x j) U T hT ω
          (hgood j hj) (hball j hj)
      exact ⟨p, fun _ => ⟨hp, hlen⟩⟩
    · exact ⟨fun _ => 0, fun h => False.elim (hj h)⟩
  let p (j : ℕ) : ℝ → ℂ := Classical.choose (hexists j)
  have hp (j : ℕ) (hj : j ≤ N) :
      AdmPath U (sphere (x j) (((2 : ℝ)⁻¹ ^ j) / 4))
        (sphere (x j) (16 * ((2 : ℝ)⁻¹ ^ j))) (p j) ∧
      lfppLen (ξ : ℝ) f (p j) < ENNReal.ofReal (2 * a j) :=
    Classical.choose_spec (hexists j) hj
  have hloop (j : ℕ) (hj : j < N) :
      Inputs.HasAroundLoop (ξ : ℝ) f (x (j + 1))
        ((2 : ℝ)⁻¹ ^ (j + 1)) (by positivity)
        (ENNReal.ofReal (L (j + 1))) := (hgood (j + 1) (by omega)).2
  have hball8 (j : ℕ) (hj : j < N) :
      ball (x (j + 1)) (8 * ((2 : ℝ)⁻¹ ^ (j + 1))) ⊆ U := by
    intro z hz
    apply hball (j + 1) (by omega)
    have hr : 0 < ((2 : ℝ)⁻¹ ^ (j + 1)) := by positivity
    have hd : dist z (x (j + 1)) < 8 * ((2 : ℝ)⁻¹ ^ (j + 1)) := mem_ball.mp hz
    exact mem_ball.mpr (by linarith)
  have hchain := pt_dist_selected_crossing_chain (ξ := (ξ : ℝ)) (f := f)
    (U := U) N x p (fun j => ENNReal.ofReal (L (j + 1)))
    (fun j hj => (hp j hj).1) hnear hloop hball8
  have hcost :
      (∑ j ∈ Finset.range N,
        (lfppLen (ξ : ℝ) f (p (j + 1)) + ENNReal.ofReal (L (j + 1)) +
          lfppLen (ξ : ℝ) f (p j))) ≤
      ∑ j ∈ Finset.range N,
        (ENNReal.ofReal (2 * a (j + 1)) + ENNReal.ofReal (L (j + 1)) +
          ENNReal.ofReal (2 * a j)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    exact add_le_add (add_le_add (hp (j + 1) (by omega)).2.le le_rfl)
      (hp j (by omega)).2.le
  obtain ⟨u, hu, _, _, hpu, _⟩ := (hp 0 (Nat.zero_le N)).1
  obtain ⟨v, hv, _, _, hpv, _⟩ := (hp N le_rfl).1
  refine ⟨u, hu, v, hv, ?_⟩
  rw [← hpu.source, ← hpv.source]
  exact hchain.trans hcost

end SupercriticalLQGUniqueness.B2.DG20Pt
