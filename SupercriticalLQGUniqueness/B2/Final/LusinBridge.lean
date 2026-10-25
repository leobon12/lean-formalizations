import SupercriticalLQGUniqueness.B2.Final.CouplingData
import SupercriticalLQGUniqueness.B2.PfeLocal.L6Lusin
import SupercriticalLQGUniqueness.B2.PfeAxioms.VaryingJointCoordLaw
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedCanonicalModel

 



















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw CoordJ pairJ pairJInv)

namespace SupercriticalLQGUniqueness.B2.Final

 


def PfeLusinApprox : Prop :=
  DG20Interfaces →
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric),
    DG20CouplingData ξ Q m e c V P' h' hN L →
    ∀ Φ : DistC → LSCMetric, Measurable Φ → (∀ᵐ ω ∂P', L ω = Φ (h' ω)) →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ κ : ℝ≥0∞, 0 < κ → ∃ Ψ : DistC → LSCMetric, Measurable Ψ ∧
        normGFFLaw {g | Φ g ≠ Ψ g} < κ ∧
        ∀ᵐ ω ∂P', Tendsto (fun n => Ψ (hN (ψ n) ω)) atTop (𝓝 (Ψ (h' ω)))

 

theorem exists_subseq_ae_tendsto_comp {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (hN : ℕ → Ω' → DistC) (h' : Ω' → DistC)
    (hNm : ∀ n, Measurable (hN n)) (h'm : Measurable h')
    (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw) (h'law : P'.map h' = normGFFLaw)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω) atTop (𝓝 (h' ω)))
    {Φ : DistC → LSCMetric} (hΦ : Measurable Φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ ω ∂P', Tendsto (fun n => Φ (hN (ψ n) ω)) atTop (𝓝 (Φ (h' ω))) := by
  have hprob : IsProbabilityMeasure normGFFLaw := PfeAxioms.normalized_canonical_model.1
  let μ : Measure (CoordJ → ℝ) := normGFFLaw.map (pairJ ⊤)
  have : IsProbabilityMeasure μ := inferInstance
  let _ : MetricSpace LSCMetric := TopologicalSpace.metrizableSpaceMetric LSCMetric
  obtain ⟨x, hx⟩ := TopologicalSpace.exists_dense_seq LSCMetric
  let Y : ℕ → Ω' → CoordJ → ℝ := fun n ω => pairJ ⊤ (hN n ω)
  let Y₀ : Ω' → CoordJ → ℝ := fun ω => pairJ ⊤ (h' ω)
  have hY : ∀ n, Measurable (Y n) := fun n => (LQGMetric.measurable_pairJ ⊤).comp (hNm n)
  have hY₀ : Measurable Y₀ := (LQGMetric.measurable_pairJ ⊤).comp h'm
  have hlaw : ∀ n, P'.map (Y n) = μ := by
    intro n
    change P'.map (pairJ ⊤ ∘ hN n) = μ
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) (hNm n), hNlaw n]
  have hlaw₀ : P'.map Y₀ = μ := by
    change P'.map (pairJ ⊤ ∘ h') = μ
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) h'm, h'law]
  have hYc : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Y₀ ω)) :=
    hconv.mono fun ω hω => (PfeAxioms.continuous_pairJ_top.tendsto _).comp hω
  have hdistm : ∀ k, Measurable fun y : LSCMetric => dist y (x k) := fun k =>
    (continuous_id.dist continuous_const).measurable
  have hcoord : ∀ k, ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P' {ω | ENNReal.ofReal δ ≤
      ‖dist (Φ (hN n ω)) (x k) - dist (Φ (h' ω)) (x k)‖ₑ}) atTop (𝓝 0) := by
    intro k δ hδ
    have h := PfeLocal.l6_tendstoInMeasure_comp (μ := μ) P' Y Y₀ hY hY₀ hlaw hlaw₀ hYc
      (fun a => dist (Φ (pairJInv ⊤ a)) (x k))
      ((hdistm k).comp (hΦ.comp (LQGMetric.measurable_pairJInv ⊤))) δ hδ
    simpa only [Y, Y₀, LQGMetric.pairJInv_pairJ] using h
  have hTIM : TendstoInMeasure P' (fun n ω => Φ (hN n ω)) atTop (fun ω => Φ (h' ω)) := by
    refine tendstoInMeasure_of_ne_top fun ε hε hεtop => ?_
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    set η : ℝ := ε.toReal / 3 with hηdef
    have hη : 0 < η := by positivity
    rw [ENNReal.tendsto_nhds_zero]
    intro κ hκ
    have hκ2 : 0 < κ / 2 := ENNReal.half_pos hκ.ne'
    
    let A : ℕ → Set Ω' := fun K =>
      ⋂ k ∈ Finset.range (K + 1), {ω | η ≤ dist (x k) (Φ (h' ω))}
    have hAm : ∀ K, MeasurableSet (A K) := fun K =>
      Finset.measurableSet_biInter _ fun k _ =>
        measurableSet_le measurable_const
          ((continuous_const.dist continuous_id).measurable.comp (hΦ.comp h'm))
    have hAanti : Antitone A := by
      intro K K' hKK' ω hω
      simp only [A, Set.mem_iInter] at hω ⊢
      intro k hk
      exact hω k (Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hk)
        (Nat.succ_le_succ hKK')))
    have hAempty : ⋂ K, A K = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 hx (Φ (h' ω)) η hη
      refine ⟨k, fun hω => ?_⟩
      have h1 : η ≤ dist (x k) (Φ (h' ω)) := by
        simp only [A, Set.mem_iInter] at hω
        exact hω k (Finset.mem_range.2 (Nat.lt_succ_self k))
      rw [dist_comm] at h1
      exact absurd hk (not_lt.2 h1)
    have hA : Tendsto (fun K => P' (A K)) atTop (𝓝 0) := by
      have h := tendsto_measure_iInter_atTop (μ := P') (s := A)
        (fun K => (hAm K).nullMeasurableSet) hAanti ⟨0, measure_ne_top _ _⟩
      rwa [hAempty, measure_empty] at h
    obtain ⟨K, hK⟩ := (ENNReal.tendsto_nhds_zero.1 hA (κ / 2) hκ2).exists
    let B : ℕ → ℕ → Set Ω' := fun n k => {ω | ENNReal.ofReal η ≤
      ‖dist (Φ (hN n ω)) (x k) - dist (Φ (h' ω)) (x k)‖ₑ}
    have hsum : Tendsto (fun n => ∑ k ∈ Finset.range (K + 1), P' (B n k)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (Finset.range (K + 1)) fun k _ => hcoord k η hη
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hsum (κ / 2) hκ2] with n hn
    have hsub : {ω | ε ≤ edist (Φ (hN n ω)) (Φ (h' ω))} ⊆
        A K ∪ ⋃ k ∈ Finset.range (K + 1), B n k := by
      intro ω hω
      by_contra hcon
      simp only [Set.mem_union, not_or, Set.mem_iUnion, not_exists] at hcon
      obtain ⟨hnA, hnB⟩ := hcon
      simp only [A, Set.mem_iInter, not_forall] at hnA
      obtain ⟨k, hk, hlt⟩ := hnA
      simp only [Set.mem_ofPred_eq, not_le] at hlt
      have hBk := hnB k hk
      simp only [B, Set.mem_ofPred_eq, not_le, Real.enorm_eq_ofReal_abs] at hBk
      have habs : |dist (Φ (hN n ω)) (x k) - dist (Φ (h' ω)) (x k)| < η :=
        (ENNReal.ofReal_lt_ofReal_iff hη).1 hBk
      have hd : dist (Φ (hN n ω)) (Φ (h' ω)) < ε.toReal := by
        have h1 := dist_triangle (Φ (hN n ω)) (x k) (Φ (h' ω))
        have h2 := (abs_lt.1 habs).2
        have h3 : dist (Φ (h' ω)) (x k) < η := by rwa [dist_comm]
        linarith
      have hω' : ε ≤ ENNReal.ofReal (dist (Φ (hN n ω)) (Φ (h' ω))) := by
        rw [← edist_dist]
        exact hω
      have : ENNReal.ofReal (dist (Φ (hN n ω)) (Φ (h' ω))) < ε := by
        rw [← ENNReal.ofReal_toReal hεtop]
        exact (ENNReal.ofReal_lt_ofReal_iff hεr).2 hd
      exact absurd hω' (not_le.2 this)
    calc P' {ω | ε ≤ edist (Φ (hN n ω)) (Φ (h' ω))}
        ≤ P' (A K ∪ ⋃ k ∈ Finset.range (K + 1), B n k) := measure_mono hsub
      _ ≤ P' (A K) + P' (⋃ k ∈ Finset.range (K + 1), B n k) := measure_union_le _ _
      _ ≤ P' (A K) + ∑ k ∈ Finset.range (K + 1), P' (B n k) := by
          gcongr
          exact measure_biUnion_finset_le _ _
      _ ≤ κ / 2 + κ / 2 := add_le_add hK hn
      _ = κ := ENNReal.add_halves κ
  exact hTIM.exists_seq_tendsto_ae

 
theorem pfeLusinApprox_proved : PfeLusinApprox := by
  intro _hI ξ Q m e c V Ω' _ _ P' _ h' hN L hB Φ hΦ _hII
  obtain ⟨ψ, hψ, hae⟩ := exists_subseq_ae_tendsto_comp P' hN h' hB.field_measurable
    hB.limit_field.1.measurable hB.field_law
    (PfeAxioms.normGFFLaw_eq_of_normalized P' h' hB.limit_field).symm hB.field_tendsto hΦ
  refine ⟨ψ, hψ, fun κ hκ => ⟨Φ, hΦ, ?_, hae⟩⟩
  simpa using hκ

end SupercriticalLQGUniqueness.B2.Final
