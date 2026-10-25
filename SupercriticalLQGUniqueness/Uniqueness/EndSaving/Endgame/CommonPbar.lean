import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.AssemblyV2




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

private theorem ratioPair_of_upperOptimal_pos (d e : LSCMetric)
    (hp : 0 < OptimalConstants.Ratios.upperOptimal d e) :
    ∃ z w : ℂ, OptimalConstants.Ratios.RatioPair d z w := by
  by_contra hn
  have hz : OptimalConstants.Ratios.upperOptimal d e = 0 := by
    apply le_antisymm
    · unfold OptimalConstants.Ratios.upperOptimal
      refine iSup_le fun z => iSup_le fun w => iSup_le fun hpair => ?_
      exact False.elim (hn ⟨z, w, hpair⟩)
    · exact bot_le
  exact hp.ne' hz

theorem hMAIN_fixed_common_pbar_v2 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cMinus cPlus : ℝ≥0∞) (hPlusPos : 0 < cPlus)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (θ : Set.Ioi (0 : ℝ))
    (pbar : Set.Ioo (0 : ℝ) 1)
    (hS36upper : ∃ a : Set.Ioo (3 / 4 : ℝ) 1,
      ∃ p : Set.Ioo (0 : ℝ) 1,
        ∀ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
          ∃ n₁ : ℕ, ∀ n ≥ n₁,
            3 * n ≤ 4 * (upperGood P h D D' ξ Q a θ
              ⟨Ctop, Ctop.property.1⟩ p n).card)
    (hS36lower : ∀ Cmid : {x : ℝ // cMinus.toReal < x},
      ∃ κ : Set.Ioi (0 : ℝ), ∃ n₂ : ℕ, ∀ n ≥ n₂,
        3 * n ≤ 4 * (lowerGood P h D D' κ
          ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ n).card)
    (hT58 : cMinus < cPlus →
      ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
    (hR53 : cMinus < cPlus → ∀ (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
      (a : Set.Ioo (3 / 4 : ℝ) 1) (κ : Set.Ioi (0 : ℝ))
      (p : Set.Ioo (0 : ℝ) 1),
        ∃ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
          ∀ j : ℕ,
            ENNReal.ofReal (κ : ℝ) ≤
              P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D'
                (dyadicRadius j) κ
                  ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩) →
            P (h ⁻¹' {g | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
              ⟨Ctop, Ctop.property.1⟩ θ g}) <
                ENNReal.ofReal ((p : ℝ) / 2)) :
    cMinus = cPlus := by
  have hCommon : ∀ᵐ ω ∂P,
      OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus ∧
      OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus := hMinus.and hPlus
  obtain ⟨ω, hωMinus, hωPlus⟩ := hCommon.exists
  have hUpperPos : 0 < OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) := by
    rw [hωPlus]
    exact hPlusPos
  obtain ⟨z, w, hpair⟩ := ratioPair_of_upperOptimal_pos _ _ hUpperPos
  have hle : cMinus ≤ cPlus := by
    calc
      cMinus = OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) := hωMinus.symm
      _ ≤ OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) :=
        OptimalConstants.Ratios.lowerOptimal_le_upperOptimal ⟨z, w, hpair⟩
      _ = cPlus := hωPlus
  rcases lt_or_eq_of_le hle with hstrict | heq
  · let objs := hT58 hstrict
    obtain ⟨a, p, hUpper⟩ := hS36upper
    obtain ⟨κ, n₂, hLower⟩ := hS36lower ⟨objs.cMid', objs.cMid'_lower⟩
    obtain ⟨Ctop, hCompare⟩ := hR53 hstrict objs a κ p
    obtain ⟨n₁, hUpperN⟩ := hUpper Ctop
    let n := max (max n₁ n₂) 5
    have hn : 4 < n := by dsimp [n]; omega
    have hn₁ : n₁ ≤ n := by dsimp [n]; omega
    have hn₂ : n₂ ≤ n := by dsimp [n]; omega
    have hcollision := Assembly.Collision.dyadic_collision hn
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (hUpperN n hn₁) (hLower n hn₂)
    obtain ⟨j, hj⟩ := hcollision
    have hU : ENNReal.ofReal (p : ℝ) ≤
        P (h ⁻¹' {g | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
          ⟨Ctop, Ctop.property.1⟩ θ g}) :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hj).1).2
    have hG : ENNReal.ofReal (κ : ℝ) ≤
        P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D'
          (dyadicRadius j) κ
            ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩) :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hj).2).2
    have hpHalf : ENNReal.ofReal ((p : ℝ) / 2) < ENNReal.ofReal (p : ℝ) := by
      exact (ENNReal.ofReal_lt_ofReal_iff p.property.1).2
        (by have hp := p.property.1; linarith)
    exact False.elim (not_lt_of_ge hU (lt_trans (hCompare j hG) hpHalf))
  · exact heq


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
