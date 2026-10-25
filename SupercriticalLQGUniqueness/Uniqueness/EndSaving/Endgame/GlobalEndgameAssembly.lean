import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.FixedEndgameAssembly
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Determinism.HDet




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

theorem hMAIN_common_pbar_of_sections
    (hS36upper : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cPlus : ℝ≥0∞, 0 < cPlus → cPlus < ⊤ →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        ∃ θ : Set.Ioi (0 : ℝ),
        ∃ a : Set.Ioo (3 / 4 : ℝ) 1,
          ∃ p : Set.Ioo (0 : ℝ) 1,
            ∀ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
              ∃ n₁ : ℕ, ∀ n ≥ n₁,
                3 * n ≤ 4 * (upperGood P h D D' ξ Q a θ
                  ⟨Ctop, Ctop.property.1⟩ p n).card)
    (hS36lower : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus : ℝ≥0∞, 0 < cMinus → cMinus < ⊤ →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        ∀ Cmid : {x : ℝ // cMinus.toReal < x},
          ∃ κ : Set.Ioi (0 : ℝ), ∃ n₂ : ℕ, ∀ n ≥ n₂,
            3 * n ≤ 4 * (lowerGood P h D D' κ
              ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ n).card)
    (hT58 : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞,
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        cMinus < cPlus → ∀ pbar : Set.Ioo (0 : ℝ) 1,
          T58DataV2 P h D D' ξ Q cMinus cPlus pbar)
    (hC45 : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        (hD : IsWeakLQGMetric ξ Q D) → (hD' : IsWeakLQGMetric ξ Q D') →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), (hGFF : IsNormalizedWholePlaneGFF h P) →
      ∀ (cMinus cPlus : ℝ≥0∞),
        (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        ∀ (hstrict : cMinus < cPlus) (pbar : Set.Ioo (0 : ℝ) 1)
          (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar),
            C45CorrectedNonemptyInternal P h ξ Q D D' hD hD' hGFF
              cMinus cPlus hMinus hPlus hstrict pbar objs.radii objs.params objs.family) :
    ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ),
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞,
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        cMinus = cPlus := by
  intro ξ Q D D' hD hD' Ω _ P _ h hGFF cMinus cPlus hMinus hPlus
  have hQ : 0 < Q := EndSaving.InterfaceV2.q_pos_of_weak_metric ξ Q D hD
  obtain ⟨m, M, hmPos, hmFin, hMPos, hMFin, hm, hM⟩ :=
    OptimalConstants.Determinism.hDET_proved ξ Q hQ D D' hD hD' P h hGFF
  obtain ⟨θ, a, p, hUpper⟩ :=
    hS36upper ξ Q hQ D D' hD hD' P h hGFF M hMPos hMFin hM
  have hLower := hS36lower ξ Q hQ D D' hD hD' P h hGFF m hmPos hmFin hm
  have hObjects : ∀ pbar : Set.Ioo (0 : ℝ) 1, m < M →
      ObjectsExistV2 P h D D' ξ Q m M pbar := by
    intro pbar hstrict
    exact (hT58 ξ Q hQ D D' hD hD' P h hGFF m M hm hM hstrict pbar).toObjectsExistV2
  have hC45Here : ∀ (hstrict : m < M) (pbar : Set.Ioo (0 : ℝ) 1)
      (objs : ObjectsExistV2 P h D D' ξ Q m M pbar),
        C45CorrectedNonemptyInternal P h ξ Q D D' hD hD' hGFF
          m M hm hM hstrict pbar objs.radii objs.params objs.family := by
    intro hstrict pbar objs
    exact hC45 ξ Q hQ D D' hD hD' P h hGFF m M hm hM hstrict pbar objs
  have hmEqM := hMAIN_fixed_from_selected_endgame_C45 P h D D' ξ Q hD hD'
    hGFF m M hMPos hm hM ⟨θ, a, p, hUpper⟩ hLower hObjects hC45Here
  have hcMinus : cMinus = m := by
    obtain ⟨ω, hω, hω'⟩ := (hMinus.and hm).exists
    exact hω.symm.trans hω'
  have hcPlus : cPlus = M := by
    obtain ⟨ω, hω, hω'⟩ := (hPlus.and hM).exists
    exact hω.symm.trans hω'
  exact hcMinus.trans (hmEqM.trans hcPlus.symm)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
