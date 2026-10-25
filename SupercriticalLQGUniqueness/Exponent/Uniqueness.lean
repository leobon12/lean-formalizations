import NV1Evidence
import LQGMetric.Papers.DFGPS.L2_8GffSq




 





set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent

open LQGMetric (DistC)

private theorem no_exponent_lt_of_common_bounds
    (ξ : Set.Ioi (0 : ℝ)) (Q Q' : ℝ) (m : ℝ → ℝ≥0∞)
    (hQ : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q + δ)) ≤ m ε ∧
        m ε ≤ ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q - δ)))
    (hQ' : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q' + δ)) ≤ m ε ∧
        m ε ≤ ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q' - δ))) :
    ¬ Q < Q' := by
  intro hlt
  let δ : ℝ := (ξ : ℝ) * (Q' - Q) / 3
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (mul_pos ξ.property (sub_pos.mpr hlt)) (by norm_num)
  have hpow : 1 - (ξ : ℝ) * Q' + δ < 1 - (ξ : ℝ) * Q - δ := by
    have hmul : 0 < (ξ : ℝ) * (Q' - Q) := mul_pos ξ.property (sub_pos.mpr hlt)
    dsimp [δ]
    nlinarith only [hmul]
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q' + δ)) ≤ m ε ∧
      m ε ≤ ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q - δ)) ∧
      0 < ε ∧ ε < 1 := by
    filter_upwards [hQ δ hδ, hQ' δ hδ,
      self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0),
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with ε h₁ h₂ hε hε1
    exact ⟨h₂.1, h₁.2, hε, hε1⟩
  obtain ⟨ε, hlow, hup, hε, hε1⟩ := hevent.exists
  have hstrict : ε ^ (1 - (ξ : ℝ) * Q - δ) < ε ^ (1 - (ξ : ℝ) * Q' + δ) :=
    Real.rpow_lt_rpow_of_exponent_gt hε hε1 hpow
  have hstrict' : ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q - δ)) <
      ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q' + δ)) :=
    (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hε _)).2 hstrict
  exact (not_le_of_gt hstrict') (hlow.trans hup)

 
theorem lfppCrossingLength_pos_and_lt_top (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    0 < lfppCrossingLength ξ φ ∧ lfppCrossingLength ξ φ < ∞ := by
  let E : ℂ → ℝ := fun z => Real.exp (ξ * φ z)
  have hE : Continuous E := Real.continuous_exp.comp (continuous_const.mul φ.continuous)
  have hcompact : IsCompact unitSquare := by
    change IsCompact LQGMetric.Blueprint.closedUnitSquare
    exact LQGMetric.DFGPS.isCompact_closedUnitSquare
  obtain ⟨z₀, -, hz₀⟩ := hcompact.exists_isMinOn
    (show unitSquare.Nonempty from ⟨0, by simp [unitSquare]⟩) hE.continuousOn
  let m := E z₀
  have hm : 0 < m := Real.exp_pos _
  have hmE : ∀ z ∈ unitSquare, m ≤ Real.exp (ξ * φ z) :=
    fun z hz => hz₀ hz
  have hbound : ENNReal.ofReal m ≤ lfppCrossingLength ξ φ := by
    unfold lfppCrossingLength
    refine le_iInf fun P => le_iInf fun hP => ?_
    have hleft : (P 0).re = 0 := hP.2.1.1
    have hright : (P 1).re = 1 := hP.2.2.1.1
    have hnorm : 1 ≤ ‖P 1 - P 0‖ := by
      have hre : (P 1 - P 0).re = 1 := by simp [Complex.sub_re, hleft, hright]
      calc (1 : ℝ) = (P 1 - P 0).re := hre.symm
        _ ≤ ‖P 1 - P 0‖ := Complex.re_le_norm _
    have hpath := hP.1.ofReal_mul_norm_sub_le (ξ := ξ) (φ := (φ : ℂ → ℝ))
      hm.le le_rfl zero_le_one le_rfl (fun t ht => hmE _ (hP.2.2.2 t ht))
    rw [hP.1.source, hP.1.target, ← LQGMetric.LFPP.lfppLen_eq] at hpath
    exact (ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left hnorm hm.le])).trans hpath
  exact ⟨(ENNReal.ofReal_pos.mpr hm).trans_le hbound, lfppCrossingLength_lt_top ξ φ⟩


 
theorem isLFPPExponent_unique :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q Q' : ℝ,
      IsLFPPExponent ξ Q → IsLFPPExponent ξ Q' → Q = Q' := by
  intro ξ Q Q' hQ hQ'
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := exists_normalizedGFF
  let : MeasurableSpace Ω := mΩ
  have : IsProbabilityMeasure P := hP
  obtain ⟨X, m, hXm⟩ := exists_exponent_witness_family P h hh ξ
  have h₁ := hQ P h hh X m hXm
  have h₂ := hQ' P h hh X m hXm
  exact le_antisymm
    (le_of_not_gt (no_exponent_lt_of_common_bounds ξ Q' Q m h₂ h₁))
    (le_of_not_gt (no_exponent_lt_of_common_bounds ξ Q Q' m h₁ h₂))

 

theorem isLFPPExponent_iff_exists_family_of_existsUnique
    (hEU : ∀ ξ : Set.Ioi (0 : ℝ), ∃! Q : ℝ, IsLFPPExponent ξ Q)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) :
    IsLFPPExponent ξ Q ↔
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (_ : IsProbabilityMeasure P) (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P ∧
        ∃ (X : ℝ → Ω → C(ℂ, ℝ)) (m : ℝ → ℝ≥0∞),
          (∀ ε : ℝ, ∀ hε : 0 < ε,
            (∀ z : ℂ, ∀ᵐ ω ∂P,
              Tendsto (fun n : ℕ => h ω
                (positiveHeatTrunc ⟨ε ^ 2 / 2,
                  Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n)) atTop
                (𝓝 (X ε ω z))) ∧
            IsMedian P (fun ω => lfppCrossingLength (ξ : ℝ) (X ε ω)) (m ε)) ∧
          (∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
            ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q + δ)) ≤ m ε ∧
              m ε ≤ ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q - δ))) := by
  constructor
  · intro hQ
    obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := exists_normalizedGFF
    let : MeasurableSpace Ω := mΩ
    have : IsProbabilityMeasure P := hP
    obtain ⟨X, m, hXm⟩ := exists_exponent_witness_family P h hh ξ
    exact ⟨Ω, mΩ, P, hP, h, hh, X, m, hXm, hQ P h hh X m hXm⟩
  · rintro ⟨Ω, mΩ, P, hP, h, hh, X, m, hXm, hBound⟩
    let : MeasurableSpace Ω := mΩ
    have : IsProbabilityMeasure P := hP
    obtain ⟨Q₀, hQ₀, _⟩ := hEU ξ
    have hBound₀ := hQ₀ P h hh X m hXm
    have hle : Q ≤ Q₀ :=
      le_of_not_gt (no_exponent_lt_of_common_bounds ξ Q₀ Q m hBound₀ hBound)
    have hge : Q₀ ≤ Q :=
      le_of_not_gt (no_exponent_lt_of_common_bounds ξ Q Q₀ m hBound hBound₀)
    have heq : Q = Q₀ := le_antisymm hle hge
    subst Q
    exact (hQ₀ : IsLFPPExponent ξ Q₀)



end SupercriticalLQGUniqueness.Exponent
