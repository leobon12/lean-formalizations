import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments.DyadicEndpoint




 






set_option autoImplicit false
noncomputable section

open Set Metric Filter LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments

private theorem dyadic_component_bounded (w : ℂ) (hw : w ≠ 0)
    (K : ℕ × Bool → Set ℂ)
    (hcompact : ∀ i, IsCompact (K i))
    (hann : ∀ i, K i ⊆ {z | Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 <
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) < Objects.BoundaryUnionDyadic.dyadicOuter w i})
    (hsep : ∀ i, LQGMetric.Disconnects (K i)
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2))
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i)))
    (i : ℕ × Bool) :
    Bornology.IsBounded (connectedComponentIn (K i)ᶜ
      (Objects.BoundaryUnionDyadic.dyadicCenter w i)) := by
  have hr : 0 < Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 := by
    dsimp [Objects.BoundaryUnionDyadic.dyadicOuter, Objects.BoundaryUnionDyadic.dyadicQ]
    exact div_pos (mul_pos (pow_pos (by norm_num) _) (norm_pos_iff.mpr hw))
      (by norm_num)
  have hrR : Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 < Objects.BoundaryUnionDyadic.dyadicOuter w i := by
    linarith only [hr]
  exact Toolkit.PlanarSeparation.annular_component_isBounded hr hrR (hcompact i) (hann i) (hsep i)

 
theorem finite_dyadic_paid_path
    (D : LSCMetric) (w : ℂ) (hw : w ≠ 0)
    (K : ℕ × Bool → Set ℂ)
    (P : ℕ × Bool → ℝ → ℂ) (a b : ℕ × Bool → ℝ)
    (hcurve : ∀ i, D.IsCurve (P i) (a i) (b i))
    (hEucl : ∀ i, ContinuousOn (P i) (Icc (a i) (b i)))
    (htrace : ∀ i, K i = P i '' Icc (a i) (b i))
    (hfinite : ∀ i, D.len (P i) (a i) (b i) < ∞)
    (hcompact : ∀ i, IsCompact (K i))
    (hann : ∀ i, K i ⊆ {z | Objects.BoundaryUnionDyadic.dyadicOuter w i / 2 <
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      dist z (Objects.BoundaryUnionDyadic.dyadicCenter w i) < Objects.BoundaryUnionDyadic.dyadicOuter w i})
    (hsep : ∀ i, LQGMetric.Disconnects (K i)
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i / 2))
      (sphere (Objects.BoundaryUnionDyadic.dyadicCenter w i) (Objects.BoundaryUnionDyadic.dyadicOuter w i)))
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < 1) :
    ∃ i j : ℕ × Bool, ∃ x y : ℂ,
      s • w ∈ connectedComponentIn (K i)ᶜ (Objects.BoundaryUnionDyadic.dyadicCenter w i) ∧
      t • w ∈ connectedComponentIn (K j)ᶜ (Objects.BoundaryUnionDyadic.dyadicCenter w j) ∧
      x ∈ K i ∧ y ∈ K j ∧
      ∃ γ : Path (D.pt x) (D.pt y),
        Set.range γ ⊆ D.pt '' closedBall 0 ‖w‖ ∧
        pathLength γ ≤ ∑' i : ℕ × Bool, D.len (P i) (a i) (b i) := by
  classical
  let A : Set ℂ := (fun z : ℝ => z • w) '' Icc s t
  have hcont : Continuous (fun z : ℝ => z • w) :=
    continuous_id.smul continuous_const
  have hAne : A.Nonempty :=
    ⟨s • w, ⟨s, ⟨le_refl s, hst⟩, rfl⟩⟩
  have hA : IsPreconnected A :=
    (isPreconnected_Icc).image (fun z : ℝ => z • w) hcont.continuousOn
  obtain ⟨S₀, hcov⟩ := Objects.BoundaryUnionDyadic.dyadic_finite_component_cover w hw K
    hcompact hann hsep hs ht
  obtain ⟨S, hSS₀, hSA, hpaths⟩ :=
    Toolkit.PaidPathCompactness.paidTrace_chain_path D S₀ K P a b (Objects.BoundaryUnionDyadic.dyadicCenter w)
      A (closedBall 0 ‖w‖) hAne hA hcov
      (fun i _ => hcurve i) (fun i _ => hEucl i)
      (fun i _ => htrace i) (fun i _ => hfinite i)
      (fun i _ => dyadic_component_bounded w hw K hcompact hann hsep i)
      (fun i _ => dyadic_trace_subset_closedBall w K hann i)
  have hleft : s • w ∈ A := ⟨s, ⟨le_refl s, hst⟩, rfl⟩
  have hright : t • w ∈ A := ⟨t, ⟨hst, le_refl t⟩, rfl⟩
  have hleft' : ∃ i, ∃ (_ : i ∈ S),
      s • w ∈ connectedComponentIn (K i)ᶜ (Objects.BoundaryUnionDyadic.dyadicCenter w i) := by
    simpa only [Set.mem_iUnion] using hSA hleft
  have hright' : ∃ j, ∃ (_ : j ∈ S),
      t • w ∈ connectedComponentIn (K j)ᶜ (Objects.BoundaryUnionDyadic.dyadicCenter w j) := by
    simpa only [Set.mem_iUnion] using hSA hright
  obtain ⟨i, hiS, hiV⟩ := hleft'
  obtain ⟨j, hjS, hjV⟩ := hright'
  have hxi : P i (a i) ∈ K i := by
    rw [htrace i]
    exact ⟨a i, ⟨le_refl _, (hcurve i).1⟩, rfl⟩
  have hyj : P j (a j) ∈ K j := by
    rw [htrace j]
    exact ⟨a j, ⟨le_refl _, (hcurve j).1⟩, rfl⟩
  obtain ⟨γ, hγC, hγlen⟩ :=
    hpaths ⟨i, hiS⟩ ⟨j, hjS⟩ (P i (a i)) hxi (P j (a j)) hyj
  refine ⟨i, j, P i (a i), P j (a j), hiV, hjV, hxi, hyj, γ, hγC, ?_⟩
  calc
    pathLength γ ≤ ∑ k ∈ S, D.len (P k) (a k) (b k) := hγlen
    _ ≤ ∑' k : ℕ × Bool, D.len (P k) (a k) (b k) := ENNReal.sum_le_tsum _


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments
