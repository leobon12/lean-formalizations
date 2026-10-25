import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces.Section4Interfaces
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Determinism.HDet
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.EndpointGap.Section4End




 





set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.RepairedInterfaces
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces

 


structure T58Data {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cMinus cPlus : ℝ≥0∞) (pbar : Set.Ioo (0 : ℝ) 1) where
  cMid' : ℝ
  cMid'_lower : cMinus.toReal < cMid'
  cMid'_upper : cMid' < midpoint cMinus cPlus
  radii : AdmissibleRadii
  params : Parameters ξ
  family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ radii.radii →
    ObjectAt P h D D' ξ Q (midpoint cMinus cPlus) params pbar z r
  density : ∀ κ : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ b : Set.Ioi (0 : ℝ),
      ENNReal.ofReal (κ : ℝ) ≤
        P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) b κ
          ⟨cMid', lt_of_le_of_lt ENNReal.toReal_nonneg cMid'_lower⟩} →
      ∃ F : Finset ℝ,
        (F : Set ℝ) = radii.radii ∩
          Set.Icc (ε ^ 2 * (b : ℝ)) (ε * (b : ℝ)) ∧
        (5 / 8 : ℝ) * (Real.log ε⁻¹ / Real.log 8) ≤ F.card

 

def T58Data.toObjectsExist
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {cMinus cPlus : ℝ≥0∞} {pbar : Set.Ioo (0 : ℝ) 1}
    (data : T58Data P h D D' ξ Q cMinus cPlus pbar) :
    ObjectsExist P h D D' ξ Q cMinus cPlus pbar := by
  refine ⟨data.cMid', data.cMid'_lower, data.cMid'_upper,
    data.radii, data.params, data.family, ?_⟩
  intro κ
  obtain ⟨ε₀, hε₀⟩ := data.density κ
  refine ⟨ε₀, ?_⟩
  intro ε hε hεsmall j
  exact hε₀ ε hε hεsmall (dyadicRadius j)

 


def C45Statement {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (_hD : IsWeakLQGMetric ξ Q D) (_hD' : IsWeakLQGMetric ξ Q D')
    (_hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (_hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (_hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (_hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1) (R : AdmissibleRadii)
    (params : Parameters ξ)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ObjectAt P h D D' ξ Q (midpoint cMinus cPlus) params pbar z r) : Prop :=
  ∀ (μ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
    ∃ C : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
      ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ → ∀ b : Set.Ioi (0 : ℝ),
      ∀ K₁ K₂ : Set ℂ,
        K₁.Nonempty → K₂.Nonempty → IsCompact K₁ → IsCompact K₂ →
        Disjoint K₁ K₂ →
        K₁ ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
        K₂ ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
        ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ euclidSetDist K₁ K₂ →
        ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤
          euclidSetDist K₁ (Metric.sphere (0 : ℂ) b) →
        P (CountingBadEvent h D D' ξ Q cPlus R
          (fun z r hr => (family z r hr).E) b ⟨ε, hε⟩ K₁ K₂) ≤
          ENNReal.ofReal ((C : ℝ) * ε ^ (μ : ℝ))

 

def AuxiliaryGood {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (R : AdmissibleRadii)
    (event : ∀ _z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → Set Ω)
    (b ε : Set.Ioi (0 : ℝ)) : Set Ω :=
  {ω | ∃ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr ∧
    (∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ε ^ 2 * (b : ℝ) ≤ (r : ℝ) → (r : ℝ) ≤ ε * (b : ℝ) →
      ∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)),
        ∃ hrz : ℝ, IsCircleAverage (h ω) r z hrz ∧
          SizeWindow ξ Q ε b r hbr hrz) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)),
      ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii) (i : ℤ × ℤ),
        ε ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
        LQGMetric.GM.gridPt ((r : ℝ) / 100) i ∈
          Metric.ball z ((r : ℝ) / 25) ∧
        ω ∈ event (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr)}

 

def PrintedEndSaving {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cPlus : ℝ≥0∞) (b ν δ κ : Set.Ioi (0 : ℝ)) : Set Ω :=
  {ω | ∃ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr ∧
    ∀ i j : ℤ × ℤ,
      let s := (δ : ℝ) ^ (ν : ℝ) * (b : ℝ)
      let z := LQGMetric.GM.gridPt (s / 100) i
      let w := LQGMetric.GM.gridPt (s / 100) j
      z ∈ Metric.ball (0 : ℂ) b → w ∈ Metric.ball (0 : ℂ) b →
      κ * (b : ℝ) ≤ dist z w →
      κ * (b : ℝ) ≤ Metric.infDist z (Metric.sphere (0 : ℂ) b) →
      OptimalConstants.Ratios.setDist (D' (h ω)) (Metric.ball z s) (Metric.ball w s) ≤
        cPlus * OptimalConstants.Ratios.setDist (D (h ω))
          (Metric.ball z s) (Metric.ball w s) -
        ENNReal.ofReal (δ * (b : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * hbr))}

 


def R52Statement {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (_hQ : 0 < Q)
    (D D' : DistC → LSCMetric)
    (_hD : IsWeakLQGMetric ξ Q D) (_hD' : IsWeakLQGMetric ξ Q D')
    (_hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (_hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (_hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (_hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1)
    (data : T58Data P h D D' ξ Q cMinus cPlus pbar) : Prop :=
  ∀ (ν κG κEnd : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
    ∃ δ₀ : Set.Ioo (0 : ℝ) 1,
      ∀ δ : ℝ, (hδ : 0 < δ) → δ ≤ δ₀ → ∀ b : Set.Ioi (0 : ℝ),
        ENNReal.ofReal (κG : ℝ) ≤
          P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) b κG
            ⟨data.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg
              data.cMid'_lower⟩} →
        ENNReal.ofReal (1 - (η : ℝ)) ≤
          P (PrintedEndSaving h D D' ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd)

 

theorem closed_gap_of_auxiliary_and_counting_exclusion
    {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cPlus : ℝ≥0∞) (R : AdmissibleRadii)
    (event : ∀ _z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → Set Ω)
    (b ε : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) (ω : Ω)
    (hAux : ω ∈ AuxiliaryGood h ξ Q R event b ε)
    (hnot : ω ∉ CountingBadEvent h D D' ξ Q cPlus R event b ε K₁ K₂)
    {saving : ℝ≥0∞}
    (hsaving : ∀ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr →
      saving ≤ ENNReal.ofReal ((1 / 2 : ℝ) * (ε : ℝ) ^
        (2 * (ξ : ℝ) * (Q + 3)) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * hbr))) :
    OptimalConstants.Ratios.setDist (D' (h ω)) K₁ K₂ + saving <
      cPlus * OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ := by
  obtain ⟨hbr, hCircle, hsize, hcover⟩ := hAux
  exact EndSaving.EndpointGap.strict_gap_of_not_countingBadEvent h D D' ξ Q cPlus R
    event b ε K₁ K₂ ω hbr hCircle hsize hcover hnot
    (hsaving hbr hCircle)

private theorem finite_pair_of_positive_upper (d e : LSCMetric)
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

private theorem biLipBound_of_ebl (d e : LSCMetric) (K : ℝ) (hK : 0 < K)
    (h : ∀ z w : ℂ, e (z, w) ≤ ENNReal.ofReal K * d (z, w) ∧
      d (z, w) ≤ ENNReal.ofReal K * e (z, w)) :
    OptimalConstants.Ratios.BiLipBound d e (ENNReal.ofReal K⁻¹) (ENNReal.ofReal K) := by
  intro z w
  constructor
  · have hmul := mul_le_mul_left (h z w).2 (ENNReal.ofReal K⁻¹)
    calc
      ENNReal.ofReal K⁻¹ * d (z, w)
          ≤ ENNReal.ofReal K⁻¹ * (ENNReal.ofReal K * e (z, w)) := by
            simpa only [mul_comm] using hmul
      _ = e (z, w) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.mpr hK).le,
              inv_mul_cancel₀ hK.ne', ENNReal.ofReal_one, one_mul]
  · exact (h z w).1

 

theorem optimal_global_upper
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞) (hPlusPos : 0 < cPlus)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) :
    ∀ᵐ ω ∂P, ∀ z w : ℂ,
      (D' (h ω)) (z, w) ≤ cPlus * (D (h ω)) (z, w) := by
  obtain ⟨K, hK, hEBL⟩ := BiLipschitz.EqualNormalizer.ebl ξ Q D D' hD hD'
  have hPlusField : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.detGFFPlusCont hGFF.1
  have hB : ∀ᵐ ω ∂P,
      OptimalConstants.Ratios.BiLipBound (D (h ω)) (D' (h ω))
        (ENNReal.ofReal K⁻¹) (ENNReal.ofReal K) := by
    filter_upwards [hEBL P h hPlusField] with ω hw
    exact biLipBound_of_ebl _ _ K (lt_of_lt_of_le (by norm_num) hK) hw
  have hpair : ∀ᵐ ω ∂P,
      ∃ z w : ℂ, OptimalConstants.Ratios.RatioPair (D (h ω)) z w := by
    filter_upwards [hPlus] with ω hω
    exact finite_pair_of_positive_upper (D (h ω)) (D' (h ω))
      (by rw [hω]; exact hPlusPos)
  have hKinv : 0 < ENNReal.ofReal K⁻¹ :=
    ENNReal.ofReal_pos.mpr (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hK))
  have hall := OptimalConstants.Ratios.ae_allPairs_of_ae_optima P (fun ω => D (h ω))
    (fun ω => D' (h ω)) hKinv hB hpair hMinus hPlus
  filter_upwards [hall] with ω hω z w
  exact (hω z w).2

 


theorem hMAIN_fixed_of_repaired_sections
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞) (hPlusPos : 0 < cPlus)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (θ : Set.Ioi (0 : ℝ))
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
    (hT58 : ∀ pbar : Set.Ioo (0 : ℝ) 1, cMinus < cPlus →
      T58Data P h D D' ξ Q cMinus cPlus pbar)
    (hR53 : cMinus < cPlus →
      (∀ᵐ ω ∂P, ∀ z w : ℂ,
        (D' (h ω)) (z, w) ≤ cPlus * (D (h ω)) (z, w)) →
      ∀ (pbar : Set.Ioo (0 : ℝ) 1)
        (objs : ObjectsExist P h D D' ξ Q cMinus cPlus pbar)
        (a : Set.Ioo (3 / 4 : ℝ) 1) (κ : Set.Ioi (0 : ℝ))
        (p : Set.Ioo (0 : ℝ) 1),
          ∃ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
            ∀ j : ℕ,
              ENNReal.ofReal (κ : ℝ) ≤
                P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω))
                  (dyadicRadius j) κ
                    ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
              P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
                ⟨Ctop, Ctop.property.1⟩ θ (h ω)} <
                  ENNReal.ofReal ((p : ℝ) / 2)) :
    cMinus = cPlus := by
  have hCommon := hMinus.and hPlus
  obtain ⟨ω, hωMinus, hωPlus⟩ := hCommon.exists
  have hUpperPos : 0 < OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) := by
    rw [hωPlus]
    exact hPlusPos
  obtain ⟨z, w, hpair⟩ := finite_pair_of_positive_upper _ _ hUpperPos
  have hle : cMinus ≤ cPlus := by
    calc
      cMinus = OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) := hωMinus.symm
      _ ≤ OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) :=
        OptimalConstants.Ratios.lowerOptimal_le_upperOptimal ⟨z, w, hpair⟩
      _ = cPlus := hωPlus
  have hGlobal := optimal_global_upper P h ξ Q D D' hD hD' hGFF
    cMinus cPlus hPlusPos hMinus hPlus
  have hOldR53 : ∀ (pbar : Set.Ioo (0 : ℝ) 1)
      (objs : ObjectsExist P h D D' ξ Q cMinus cPlus pbar)
      (a : Set.Ioo (3 / 4 : ℝ) 1) (κ : Set.Ioi (0 : ℝ))
      (p : Set.Ioo (0 : ℝ) 1),
        ∃ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
          ∀ j : ℕ,
            ENNReal.ofReal (κ : ℝ) ≤
              P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω))
                (dyadicRadius j) κ
                  ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
            P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
              ⟨Ctop, Ctop.property.1⟩ θ (h ω)} <
                ENNReal.ofReal ((p : ℝ) / 2) := by
    intro pbar objs a κ p
    have hstrict : cMinus < cPlus := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exfalso
        rw [heq] at objs
        have hlo := objs.cMid'_lower
        have hhi := objs.cMid'_upper
        unfold EndSaving.Interfaces.midpoint at hhi
        linarith
    exact hR53 hstrict hGlobal pbar objs a κ p
  exact EndSaving.Interfaces.hMAIN_fixed_of_sections P h D D' ξ Q cMinus cPlus
    hPlusPos hMinus hPlus θ hS36upper hS36lower
    (fun pbar hstrict => (hT58 pbar hstrict).toObjectsExist) hOldR53

 


theorem hMAIN_of_repaired_sections
    (θFixed : ∀ (_ξ : Set.Ioi (0 : ℝ)) (_Q : ℝ)
      (_D : DistC → LSCMetric), Set.Ioi (0 : ℝ))
    (hS36upper : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cPlus : ℝ≥0∞, 0 < cPlus → cPlus < ⊤ →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        ∃ a : Set.Ioo (3 / 4 : ℝ) 1,
          ∃ p : Set.Ioo (0 : ℝ) 1,
            ∀ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
              ∃ n₁ : ℕ, ∀ n ≥ n₁,
                3 * n ≤ 4 * (upperGood P h D D' ξ Q a (θFixed ξ Q D)
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
          T58Data P h D D' ξ Q cMinus cPlus pbar)
    (hR53 : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ (cMinus cPlus : ℝ≥0∞),
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        cMinus < cPlus →
        (∀ᵐ ω ∂P, ∀ z w : ℂ,
          (D' (h ω)) (z, w) ≤ cPlus * (D (h ω)) (z, w)) →
        ∀ (pbar : Set.Ioo (0 : ℝ) 1)
          (objs : ObjectsExist P h D D' ξ Q cMinus cPlus pbar)
          (a : Set.Ioo (3 / 4 : ℝ) 1)
          (κ : Set.Ioi (0 : ℝ)) (p : Set.Ioo (0 : ℝ) 1),
            ∃ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
              ∀ j : ℕ,
                ENNReal.ofReal (κ : ℝ) ≤
                  P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω))
                    (dyadicRadius j) κ
                      ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
                P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
                  ⟨Ctop, Ctop.property.1⟩ (θFixed ξ Q D) (h ω)} <
                    ENNReal.ofReal ((p : ℝ) / 2)) :
    ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞,
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        cMinus = cPlus := by
  intro ξ Q hQ D D' hD hD' Ω _ P _ h hGFF cMinus cPlus hMinus hPlus
  obtain ⟨m, M, hmPos, hmFin, hMPos, hMFin, hm, hM⟩ :=
    OptimalConstants.Determinism.hDET_proved ξ Q hQ D D' hD hD' P h hGFF
  obtain ⟨a, p, hUpper⟩ :=
    hS36upper ξ Q hQ D D' hD hD' P h hGFF M hMPos hMFin hM
  have hLower := hS36lower ξ Q hQ D D' hD hD' P h hGFF m hmPos hmFin hm
  have hObjects : ∀ pbar : Set.Ioo (0 : ℝ) 1, m < M →
      T58Data P h D D' ξ Q m M pbar := by
    intro pbar hstrict
    exact hT58 ξ Q hQ D D' hD hD' P h hGFF m M hm hM hstrict pbar
  have hCompare : m < M →
      (∀ᵐ ω ∂P, ∀ z w : ℂ,
        (D' (h ω)) (z, w) ≤ M * (D (h ω)) (z, w)) →
      ∀ (pbar : Set.Ioo (0 : ℝ) 1)
        (objs : ObjectsExist P h D D' ξ Q m M pbar)
        (a : Set.Ioo (3 / 4 : ℝ) 1)
        (κ : Set.Ioi (0 : ℝ)) (p : Set.Ioo (0 : ℝ) 1),
          ∃ Ctop : Set.Ioo (0 : ℝ) M.toReal,
            ∀ j : ℕ,
              ENNReal.ofReal (κ : ℝ) ≤
                P {ω | OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω))
                  (dyadicRadius j) κ
                    ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩} →
              P {ω | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
                ⟨Ctop, Ctop.property.1⟩ (θFixed ξ Q D) (h ω)} <
                  ENNReal.ofReal ((p : ℝ) / 2) := by
    intro hstrict hGlobal pbar objs a κ p
    exact hR53 ξ Q hQ D D' hD hD' P h hGFF m M hm hM hstrict
      hGlobal pbar objs a κ p
  have hmEqM := hMAIN_fixed_of_repaired_sections P h ξ Q D D' hD hD'
    hGFF m M hMPos hm hM (θFixed ξ Q D) ⟨a, p, hUpper⟩ hLower
    hObjects hCompare
  have hcMinus : cMinus = m := by
    obtain ⟨ω, hω, hω'⟩ := (hMinus.and hm).exists
    exact hω.symm.trans hω'
  have hcPlus : cPlus = M := by
    obtain ⟨ω, hω, hω'⟩ := (hPlus.and hM).exists
    exact hω.symm.trans hω'
  exact hcMinus.trans (hmEqM.trans hcPlus.symm)


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.RepairedInterfaces
