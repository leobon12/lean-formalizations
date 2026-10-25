import SupercriticalLQGUniqueness.B2.PfeLocal.L4Fill
import SupercriticalLQGUniqueness.B2.PfeWeyl.W1Crossing

 

















set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
def l4Inv (D₁ D₂ : LSCMetric) (K : ℝ≥0∞) (ρ : ℝ) (P : ℝ → ℂ) (a τ : ℝ) (R : Set ℂ) : Prop :=
  (∀ x ∈ R, ∃ q ∈ closedBall (P a) (4 * ρ), D₂ (q, x) ≤ K * D₁.len P a τ) ∧
    ∀ Λ : Set ℂ, P τ ∈ l4Fill Λ → (Λ ∩ R).Nonempty ∨ P a ∈ l4Fill Λ

theorem l4Inv_start (D₁ D₂ : LSCMetric) (K : ℝ≥0∞) (ρ : ℝ) (P : ℝ → ℂ) (a : ℝ) :
    l4Inv D₁ D₂ K ρ P a a ∅ :=
  ⟨fun x hx => absurd hx (notMem_empty x), fun _ h => Or.inr h⟩

 
theorem l4_exists_loop (D₂ : LSCMetric) (w : ℂ) {r : ℝ} (hr : 0 < r) {M : ℝ≥0∞}
    (hM : aroundDist D₂ (outerAnnulus w r hr) < M) :
    ∃ ℓ : Set ℂ, ℓ.Nonempty ∧ IsCompact ℓ ∧ IsPreconnected ℓ ∧ ℓ ⊆ closedBall w (2 * r) ∧
      Disjoint ℓ (ball w r) ∧ closedBall w r ⊆ l4Fill ℓ ∧
      ∃ L₀ : ℝ≥0∞, L₀ < M ∧ ∀ x ∈ ℓ, ∀ y ∈ ℓ, D₂ (x, y) ≤ L₀ := by
  unfold aroundDist at hM
  simp only [iInf_lt_iff] at hM
  obtain ⟨γ, s₀, s₁, hγ, hγA, hdisc, hlen⟩ := hM
  set ℓ := γ '' Icc s₀ s₁ with hℓ
  have hA : ∀ t ∈ Icc s₀ s₁, r < dist (γ t) w ∧ dist (γ t) w < 2 * r := by
    intro t ht
    have := hγA t ht
    rw [EuclideanAnnulus.toSet_eq] at this
    exact this
  have hbdd : Bornology.IsBounded ℓ := by
    refine isBounded_closedBall (x := w) (r := 2 * r) |>.subset ?_
    rintro _ ⟨t, ht, rfl⟩
    exact mem_closedBall.2 (hA t ht).2.le
  have hγc : ContinuousOn γ (Icc s₀ s₁) := continuousOn_euclidean_of_bounded D₂ γ hγ hbdd
  refine ⟨ℓ, ⟨γ s₀, s₀, ⟨le_rfl, hγ.1⟩, rfl⟩, isCompact_Icc.image_of_continuousOn hγc,
    isPreconnected_Icc.image _ hγc, ?_, ?_, l4_closedBall_subset_fill hdisc, D₂.len γ s₀ s₁, hlen,
    ?_⟩
  · rintro _ ⟨t, ht, rfl⟩; exact mem_closedBall.2 (hA t ht).2.le
  · rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ hb
    exact absurd (mem_ball.1 hb) (not_lt.2 (hA t ht).1.le)
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rcases le_total s t with hst | hts
    · exact (edist_le_len D₂ γ hst).trans (PfeWeyl.len_mono_Icc D₂ γ hs.1 ht.2)
    · have hsym : D₂ (γ s, γ t) = D₂ (γ t, γ s) := D₂.2.1.2.2.1 (γ s) (γ t)
      rw [hsym]
      exact (edist_le_len D₂ γ hts).trans (PfeWeyl.len_mono_Icc D₂ γ ht.1 hs.2)

theorem l4_dist_le_of_mem_two_balls {x y w : ℂ} {r ρ : ℝ} (hx : x ∈ closedBall w (2 * r))
    (hy : y ∈ closedBall w (2 * r)) (hrρ : r ≤ ρ) : x ∈ closedBall y (4 * ρ) := by
  rw [mem_closedBall] at hx hy ⊢
  calc dist x y ≤ dist x w + dist w y := dist_triangle _ _ _
    _ ≤ 2 * r + 2 * r := add_le_add hx (by rw [dist_comm]; exact hy)
    _ ≤ 4 * ρ := by linarith

 
theorem l4_chain_step (D₁ D₂ : LSCMetric) (K : ℝ≥0∞) (ρ μ₀ : ℝ) (P : ℝ → ℂ) {a b : ℝ}
    (hPc : ContinuousOn P (Icc a b))
    (hgood : ∀ t ∈ Icc a b, ∃ w : ℂ, ∃ r : ℝ, ∃ hr : 0 < r, r ≤ ρ ∧ P t ∈ ball w (r / 2) ∧
      ENNReal.ofReal μ₀ ≤ acrossDist D₁ (innerAnnulus w r hr) ∧
      aroundDist D₂ (outerAnnulus w r hr) < K * acrossDist D₁ (innerAnnulus w r hr)) :
    ∀ n : ℕ, ∀ τ ∈ Icc a b, ∀ R : Set ℂ, l4Inv D₁ D₂ K ρ P a τ R →
      D₁.len P τ b < ENNReal.ofReal (n * μ₀) →
      ∃ x₁ ∈ closedBall (P a) (4 * ρ), ∃ x₂ ∈ closedBall (P b) (4 * ρ),
        D₂ (x₁, x₂) ≤ K * D₁.len P a b := by
  intro n
  induction n with
  | zero =>
    intro τ _ R _ hlt
    simp at hlt
  | succ n ih =>
    intro τ hτ R hInv hlt
    obtain ⟨w, r, hr, hrρ, hPτ, hμ, hgood'⟩ := hgood τ hτ
    obtain ⟨ℓ, hne, hcpt, hpc, hsub, hdisj, hfill, L₀, hL₀, hdiam⟩ :=
      l4_exists_loop D₂ w hr hgood'
    have hPτF : P τ ∈ l4Fill ℓ :=
      hfill (ball_subset_closedBall (ball_subset_ball (by linarith) hPτ))
    have hPτℓ : P τ ∉ ℓ := fun h =>
      Set.disjoint_left.1 hdisj h (ball_subset_ball (by linarith) hPτ)
    have hlen_aτ_le_ab : D₁.len P a τ ≤ D₁.len P a b := PfeWeyl.len_mono_Icc D₁ P le_rfl hτ.2
    
    have hreach : ∀ y ∈ ℓ, ∃ q ∈ closedBall (P a) (4 * ρ), D₂ (q, y) ≤ K * D₁.len P a τ + L₀ := by
      intro y hy
      rcases hInv.2 ℓ hPτF with ⟨x₀, hx₀ℓ, hx₀R⟩ | hPa
      · obtain ⟨q, hq, hqx⟩ := hInv.1 x₀ hx₀R
        refine ⟨q, hq, ?_⟩
        calc D₂ (q, y) ≤ D₂ (q, x₀) + D₂ (x₀, y) := D₂.2.1.2.2.2 q x₀ y
          _ ≤ K * D₁.len P a τ + L₀ := add_le_add hqx (hdiam x₀ hx₀ℓ y hy)
      · refine ⟨y, ?_, ?_⟩
        · exact l4_dist_le_of_mem_two_balls (hsub hy)
            (l4_fill_subset_closedBall (by linarith) hsub hPa) hrρ
        · rw [D₂.2.1.1 y]; exact zero_le
    by_cases hhit : ∃ t ∈ Icc τ b, P t ∈ ℓ
    · obtain ⟨t, ht, hPt⟩ := hhit
      have hτt : τ ≤ t := ht.1
      have htab : t ∈ Icc a b := ⟨hτ.1.trans hτt, ht.2⟩
      have hcross : acrossDist D₁ (innerAnnulus w r hr) ≤ D₁.len P τ t := by
        refine PfeWeyl.acrossDist_le_len_of_crossing D₁ _ hτt
          (hPc.mono (Icc_subset_Icc hτ.1 ht.2)) ?_ ?_
        · exact (mem_ball.1 hPτ).le
        · have := hsub hPt
          have h2 := Set.disjoint_left.1 hdisj hPt
          change r ≤ dist (P t) w
          exact not_lt.1 (fun h => h2 (mem_ball.2 h))
      have hadd : D₁.len P a t = D₁.len P a τ + D₁.len P τ t := lsc_len_add D₁ P hτ.1 hτt
      have hadd' : D₁.len P τ b = D₁.len P τ t + D₁.len P t b := lsc_len_add D₁ P hτt ht.2
      refine ih t htab (R ∪ ℓ) ⟨?_, ?_⟩ ?_
      · intro x hx
        rcases hx with hxR | hxℓ
        · obtain ⟨q, hq, hqx⟩ := hInv.1 x hxR
          exact ⟨q, hq, hqx.trans (mul_le_mul_right (hadd ▸ le_self_add) K)⟩
        · obtain ⟨q, hq, hqx⟩ := hreach x hxℓ
          refine ⟨q, hq, hqx.trans ?_⟩
          rw [hadd, mul_add]
          exact add_le_add le_rfl (hL₀.le.trans (mul_le_mul_right hcross K))
      · intro Λ hΛ
        by_cases hΛℓ : (Λ ∩ ℓ).Nonempty
        · obtain ⟨x, hxΛ, hxℓ⟩ := hΛℓ
          exact Or.inl ⟨x, hxΛ, Or.inr hxℓ⟩
        · have hℓF : ℓ ⊆ l4Fill Λ := by
            intro x hx
            by_contra hxF
            obtain ⟨y, hyℓ, hyΛ⟩ := l4_fill_frontier hpc ⟨P t, hPt, hΛ⟩ ⟨x, hx, hxF⟩
            exact hΛℓ ⟨y, hyΛ, hyℓ⟩
          rcases hInv.2 Λ (l4_fill_mono hℓF hPτF) with ⟨x, hxΛ, hxR⟩ | hPa
          · exact Or.inl ⟨x, hxΛ, Or.inl hxR⟩
          · exact Or.inr hPa
      · 
        by_contra hge
        push Not at hge
        have h1 : ENNReal.ofReal μ₀ + ENNReal.ofReal (n * μ₀) ≤ D₁.len P τ b := by
          rw [hadd']; exact add_le_add (hμ.trans hcross) hge
        have h2 : ENNReal.ofReal ((n + 1 : ℕ) * μ₀) ≤ ENNReal.ofReal μ₀ +
            ENNReal.ofReal (n * μ₀) := by
          calc ENNReal.ofReal ((n + 1 : ℕ) * μ₀) = ENNReal.ofReal (μ₀ + n * μ₀) := by
                congr 1; push_cast; ring
            _ ≤ _ := ENNReal.ofReal_add_le
        exact absurd hlt (not_lt.2 (h2.trans h1))
    · push Not at hhit
      have hTsub : P '' Icc τ b ⊆ l4Fill ℓ := by
        rintro _ ⟨s, hs, rfl⟩
        by_contra hsF
        obtain ⟨y, ⟨u, hu, rfl⟩, hyℓ⟩ := l4_fill_frontier
          ((isPreconnected_Icc).image _ (hPc.mono (Icc_subset_Icc hτ.1 le_rfl)))
          ⟨P τ, ⟨τ, ⟨le_rfl, hτ.2⟩, rfl⟩, hPτF⟩ ⟨P s, ⟨s, hs, rfl⟩, hsF⟩
        exact hhit u hu hyℓ
      have hPb : P b ∈ closedBall w (2 * r) :=
        l4_fill_subset_closedBall (by linarith) hsub (hTsub ⟨b, ⟨hτ.2, le_rfl⟩, rfl⟩)
      rcases hInv.2 ℓ hPτF with ⟨x₀, hx₀ℓ, hx₀R⟩ | hPa
      · obtain ⟨q, hq, hqx⟩ := hInv.1 x₀ hx₀R
        exact ⟨q, hq, x₀, l4_dist_le_of_mem_two_balls (hsub hx₀ℓ) hPb hrρ,
          hqx.trans (mul_le_mul_right hlen_aτ_le_ab K)⟩
      · obtain ⟨y, hy⟩ := hne
        refine ⟨y, l4_dist_le_of_mem_two_balls (hsub hy)
          (l4_fill_subset_closedBall (by linarith) hsub hPa) hrρ, y,
          l4_dist_le_of_mem_two_balls (hsub hy) hPb hrρ, ?_⟩
        rw [D₂.2.1.1 y]; exact zero_le

 
theorem l4_chain (D₁ D₂ : LSCMetric) (K : ℝ≥0∞) (ρ μ₀ : ℝ) (hμ₀ : 0 < μ₀) (P : ℝ → ℂ)
    {a b : ℝ} (hab : a ≤ b) (hPc : ContinuousOn P (Icc a b)) (hlen : D₁.len P a b < ∞)
    (hgood : ∀ t ∈ Icc a b, ∃ w : ℂ, ∃ r : ℝ, ∃ hr : 0 < r, r ≤ ρ ∧ P t ∈ ball w (r / 2) ∧
      ENNReal.ofReal μ₀ ≤ acrossDist D₁ (innerAnnulus w r hr) ∧
      aroundDist D₂ (outerAnnulus w r hr) < K * acrossDist D₁ (innerAnnulus w r hr)) :
    ∃ x₁ ∈ closedBall (P a) (4 * ρ), ∃ x₂ ∈ closedBall (P b) (4 * ρ),
      D₂ (x₁, x₂) ≤ K * D₁.len P a b := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((D₁.len P a b).toReal / μ₀)
  refine l4_chain_step D₁ D₂ K ρ μ₀ P hPc hgood n a ⟨le_rfl, hab⟩ ∅ (l4Inv_start D₁ D₂ K ρ P a) ?_
  rw [← ENNReal.ofReal_toReal hlen.ne]
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hn0 hμ₀)).2
  rwa [div_lt_iff₀ hμ₀] at hn

end SupercriticalLQGUniqueness.B2.PfeLocal
