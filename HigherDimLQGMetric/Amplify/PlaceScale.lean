import HigherDimLQGMetric.Amplify.Placement

/-! One geometric scale places all finitely many noise neighborhoods. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Filter Topology
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Centers selected separately in disjoint boxes are globally distinct. -/
theorem amplify_centers_injective {M N : ℕ}
    (O K : Fin M → Set (Rd d)) (hKO : ∀ i, K i ⊆ O i)
    (hO : Pairwise (fun i j => Disjoint (O i) (O j)))
    (w : Fin M → Fin N → Rd d)
    (hw : ∀ i k, w i k ∈ interior (K i))
    (hinj : ∀ i, Function.Injective (w i)) :
    Function.Injective (fun p : Fin M × Fin N => w p.1 p.2) := by
  intro p q hpq
  change w p.1 p.2 = w q.1 q.2 at hpq
  by_cases hi : p.1 = q.1
  · apply Prod.ext hi
    apply hinj p.1
    simpa only [hi] using hpq
  · have hp : w p.1 p.2 ∈ O p.1 := hKO _ (interior_subset (hw _ _))
    have hq : w q.1 q.2 ∈ O q.1 := hKO _ (interior_subset (hw _ _))
    rw [hpq] at hp
    exact False.elim ((Set.disjoint_left.mp (hO hi)) hp hq)

/-- For any prescribed finite family, a power of `1/64` makes every enlarged
noise ball lie in its compact box and makes the balls pairwise disjoint. -/
theorem amplify_exists_trial_scale (hd : 1 ≤ d) {M N : ℕ}
    (O K : Fin M → Set (Rd d))
    (hK : ∀ i, (interior (K i)).Nonempty)
    (hKO : ∀ i, K i ⊆ O i)
    (hO : Pairwise (fun i j => Disjoint (O i) (O j)))
    (Rk L : ℝ) (hRk : 0 < Rk) (hL : 0 < L) :
    ∃ (m : ℕ) (w : Fin M → Fin N → Rd d),
      let ρ : ℝ := ((64 : ℝ)⁻¹) ^ m
      0 < ρ ∧ ρ ≤ 1 ∧
      (∀ i k, Metric.ball (w i k) ((5 + Rk * L) * ρ) ⊆ K i) ∧
      Pairwise (fun p q : Fin M × Fin N => Disjoint
        (Metric.ball (w p.1 p.2) ((5 + Rk * L) * ρ))
        (Metric.ball (w q.1 q.2) ((5 + Rk * L) * ρ))) := by
  classical
  obtain ⟨w, hw, hinj⟩ := amplify_exists_centers hd K hK N
  let wp : Fin M × Fin N → Rd d := fun p => w p.1 p.2
  have hwp : Function.Injective wp := amplify_centers_injective O K hKO hO w hw hinj
  obtain ⟨ε, hε, hball, hdisj⟩ :=
    amplify_finite_ball_separation wp hwp (fun p : Fin M × Fin N => K p.1)
      (fun p => hw p.1 p.2)
  let C : ℝ := 5 + Rk * L
  have hC : 0 < C := by dsimp [C]; positivity
  have hlim : Tendsto (fun m : ℕ => ((64 : ℝ)⁻¹) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨m, hm⟩ := (hlim.eventually (eventually_lt_nhds (div_pos hε hC))).exists
  let ρ : ℝ := ((64 : ℝ)⁻¹) ^ m
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := by dsimp [ρ]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hrad : C * ρ ≤ ε := by
    have hm' : ρ < ε / C := hm
    simpa only [mul_comm] using ((lt_div_iff₀ hC).1 hm').le
  refine ⟨m, w, hρ, hρ1, ?_, ?_⟩
  · intro i k
    exact (Metric.ball_subset_ball hrad).trans (hball (i, k))
  · intro p q hpq
    exact (hdisj hpq).mono (Metric.ball_subset_ball hrad)
      (Metric.ball_subset_ball hrad)

/-- Dilation preserves pairwise separation of a finite family of balls. -/
theorem amplify_scaled_balls_disjoint {ι : Type*}
    (w : ι → Rd d) (ε : ℝ) {r : ℝ} (hr : 0 < r)
    (hdisj : Pairwise (fun i j => Disjoint
      (Metric.ball (w i) ε) (Metric.ball (w j) ε))) :
    Pairwise (fun i j => Disjoint
      (Metric.ball (r • w i) (r * ε))
      (Metric.ball (r • w j) (r * ε))) := by
  intro i j hij
  have heq (i : ι) : (fun x : Rd d => r • x) '' Metric.ball (w i) ε =
      Metric.ball (r • w i) (r * ε) := by
    rw [Metric.smul_image_ball hr.ne', Real.norm_eq_abs, abs_of_pos hr]
  rw [← heq i, ← heq j]
  exact (Set.disjoint_image_iff (smul_right_injective (Rd d) hr.ne')).2
    (hdisj hij)

end HigherDimLQGMetric
