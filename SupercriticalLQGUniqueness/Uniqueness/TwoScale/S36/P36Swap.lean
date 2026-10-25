import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.S36B




 






















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 

theorem HEvent_swap_iff (D D' : DistC → LSCMetric) (ξ Q : ℝ) (r : Ioi (0 : ℝ))
    (a : Ioo (3 / 4 : ℝ) 1) (θ C : Ioi (0 : ℝ)) (g : DistC) :
    OptimalConstants.Ratios.HEvent D' D ξ Q r a ⟨(C : ℝ)⁻¹, mem_Ioi.mpr (inv_pos.mpr C.2)⟩ θ g ↔
      OptimalConstants.Ratios.HtildeEvent D D' ξ Q r a C θ g := by
  have hC : 0 < (C : ℝ) := C.2
  have hmul : ENNReal.ofReal (C : ℝ)⁻¹ * ENNReal.ofReal (C : ℝ) = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hC.le), inv_mul_cancel₀ hC.ne', ENNReal.ofReal_one]
  have key : ∀ x y : ℝ≥0∞, ENNReal.ofReal (C : ℝ)⁻¹ * x ≤ y ↔ x ≤ ENNReal.ofReal C * y := by
    intro x y
    constructor
    · intro hxy
      calc x = (ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (C : ℝ)⁻¹) * x := by
            rw [mul_comm (ENNReal.ofReal (C : ℝ)), hmul, one_mul]
        _ = ENNReal.ofReal (C : ℝ) * (ENNReal.ofReal (C : ℝ)⁻¹ * x) := mul_assoc _ _ _
        _ ≤ ENNReal.ofReal (C : ℝ) * y := mul_le_mul' le_rfl hxy
    · intro hxy
      calc ENNReal.ofReal (C : ℝ)⁻¹ * x ≤ ENNReal.ofReal (C : ℝ)⁻¹ * (ENNReal.ofReal C * y) :=
            mul_le_mul' le_rfl hxy
        _ = y := by rw [← mul_assoc, hmul, one_mul]
  unfold OptimalConstants.Ratios.HEvent OptimalConstants.Ratios.HtildeEvent OptimalConstants.Ratios.H OptimalConstants.Ratios.Htilde
  constructor
  · rintro ⟨hc, hcirc, u, v, hu, hv, hsu, hsv, hle, rest⟩
    exact ⟨hc, hcirc, u, v, hu, hv, hsu, hsv, (key _ _).mp hle, rest⟩
  · rintro ⟨hc, hcirc, u, v, hu, hv, hsu, hsv, hle, rest⟩
    exact ⟨hc, hcirc, u, v, hu, hv, hsu, hsv, (key _ _).mpr hle, rest⟩

 

def relGoodTilde {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ Q : ℝ) (a : Ioo (3 / 4 : ℝ) 1) (θ C : Ioi (0 : ℝ)) (p : ℝ)
    (b : Ioi (0 : ℝ)) (ε : ℝ) : Finset ℕ :=
  (gridIdx ε).filter fun k =>
    ENNReal.ofReal p ≤ P {ω | OptimalConstants.Ratios.HtildeEvent D D' ξ Q (relRad b k) a C θ (h ω)}

 

theorem attained_good_swap_rel (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (cMinus : ℝ≥0∞) (hm0 : 0 < cMinus) (hmt : cMinus < ⊤)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) :
    ∃ θ : Ioi (0 : ℝ), ∃ a : Ioo (3 / 4 : ℝ) 1, ∃ p : Ioo (0 : ℝ) 1,
      ∀ Cmid : {x : ℝ // cMinus.toReal < x}, ∃ cMid' : Ioi (0 : ℝ),
        cMinus.toReal < cMid' ∧ (cMid' : ℝ) < Cmid ∧
        ∀ κ : Ioi (0 : ℝ), ∃ ε₀ : Ioo (0 : ℝ) 1,
          ∀ (b : Ioi (0 : ℝ)) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
            ENNReal.ofReal (κ : ℝ) ≤ P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D' b κ cMid') →
            (3 / 4 : ℝ) * gridLen ε ≤
              ((relGoodTilde P h D D' (ξ : ℝ) Q a θ
                ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ p b ε).card : ℝ) := by
  set cS : ℝ≥0∞ := cMinus⁻¹ with hcSdef
  have hswap : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D' (h ω)) (D (h ω)) = cS := by
    filter_upwards [ae_lower_eq_inv_upper_swap ξ Q D D' hD hD' P h hh, hMinus] with ω h1 h2
    rw [hcSdef, ← h2, h1, inv_inv]
  have hcS0 : 0 < cS := ENNReal.inv_pos.mpr hmt.ne
  have hcSt : cS < ⊤ := ENNReal.inv_lt_top.mpr hm0
  have hCm0 : 0 < cMinus.toReal := ENNReal.toReal_pos hm0.ne' hmt.ne
  have hcSr : cS.toReal = (cMinus.toReal)⁻¹ := ENNReal.toReal_inv cMinus
  obtain ⟨θ, a, p, hup⟩ := attained_good_rel ξ Q hQ D' D hD' hD P h hh cS hcS0 hcSt hswap
  refine ⟨θ, a, p, fun Cmid => ?_⟩
  have hCmid0 : 0 < (Cmid : ℝ) := hCm0.trans Cmid.property
  have hCvlt : (Cmid : ℝ)⁻¹ < cS.toReal := by
    rw [hcSr]
    exact (inv_lt_inv₀ hCmid0 hCm0).mpr Cmid.property
  obtain ⟨C', hCC', hC'cS, hmain⟩ := hup ⟨(Cmid : ℝ)⁻¹, inv_pos.mpr hCmid0, hCvlt⟩
  have hC'0 : 0 < (C' : ℝ) := C'.2
  have hCC'' : (Cmid : ℝ)⁻¹ < C' := hCC'
  have hC'cS' : (C' : ℝ) < (cMinus.toReal)⁻¹ := by rw [← hcSr]; exact hC'cS
  refine ⟨⟨(C' : ℝ)⁻¹, mem_Ioi.mpr (inv_pos.mpr hC'0)⟩, (lt_inv_comm₀ hCm0 hC'0).mpr hC'cS',
    (inv_lt_comm₀ hC'0 hCmid0).mpr hCC'', fun κ => ?_⟩
  obtain ⟨ε₀, hε₀⟩ := hmain κ
  refine ⟨ε₀, fun b ε hε0 hεε₀ hGκ => ?_⟩
  have hCeq : (⟨((C' : ℝ)⁻¹)⁻¹, mem_Ioi.mpr (inv_pos.mpr (inv_pos.mpr hC'0))⟩ :
      Ioi (0 : ℝ)) = C' :=
    Subtype.ext (inv_inv _)
  have hG : ENNReal.ofReal (κ : ℝ) ≤ P {ω | OptimalConstants.Ratios.G (D' (h ω)) (D (h ω)) b κ C'} := by
    refine hGκ.trans (measure_mono fun ω hω => ?_)
    have hω' : OptimalConstants.Ratios.Gtilde (D (h ω)) (D' (h ω)) b κ
        ⟨(C' : ℝ)⁻¹, mem_Ioi.mpr (inv_pos.mpr hC'0)⟩ := hω
    have hsw := (OptimalConstants.Ratios.Gtilde_iff_swap (D (h ω)) (D' (h ω)) b κ
      ⟨(C' : ℝ)⁻¹, mem_Ioi.mpr (inv_pos.mpr hC'0)⟩).mp hω'
    change OptimalConstants.Ratios.G (D' (h ω)) (D (h ω)) b κ C'
    rw [← hCeq]
    exact hsw
  have hcount := hε₀ b ε hε0 hεε₀ hG
  have hset : relGood P h D' D (ξ : ℝ) Q a θ
      ⟨(Cmid : ℝ)⁻¹, mem_Ioi.mpr (inv_pos.mpr hCmid0)⟩ p b ε =
      relGoodTilde P h D D' (ξ : ℝ) Q a θ
        ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ p b ε := by
    unfold relGood relGoodTilde
    refine Finset.filter_congr fun k _ => ?_
    have hev : {ω | OptimalConstants.Ratios.HEvent D' D (ξ : ℝ) Q (relRad b k) a
        ⟨(Cmid : ℝ)⁻¹, mem_Ioi.mpr (inv_pos.mpr hCmid0)⟩ θ (h ω)} =
        {ω | OptimalConstants.Ratios.HtildeEvent D D' (ξ : ℝ) Q (relRad b k) a
          ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ θ (h ω)} := by
      ext ω
      exact HEvent_swap_iff D D' (ξ : ℝ) Q (relRad b k) a θ
        ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ (h ω)
    rw [hev]
  have hcard : ((relGood P h D' D (ξ : ℝ) Q a θ
      ⟨(Cmid : ℝ)⁻¹, mem_Ioi.mpr (inv_pos.mpr hCmid0)⟩ p b ε).card : ℝ) =
      ((relGoodTilde P h D D' (ξ : ℝ) Q a θ
        ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ p b ε).card : ℝ) := by
    rw [hset]
  exact hcount.trans_eq hcard

 

 
def tildeGoodRadii {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ Q : ℝ) (a : Ioo (3 / 4 : ℝ) 1) (θ C : Ioi (0 : ℝ)) (p : ℝ) :
    EndSaving.Interfaces.AdmissibleRadii where
  radii := {r | ∃ m : ℕ, 1 ≤ m ∧ r = (EndSaving.Interfaces.dyadicRadius m : ℝ) ∧
    ENNReal.ofReal p ≤ P {ω | OptimalConstants.Ratios.HtildeEvent D D' ξ Q (EndSaving.Interfaces.dyadicRadius m) a C θ (h ω)}}
  subset_unit := by
    rintro r ⟨m, hm, rfl, -⟩
    exact ⟨(EndSaving.Interfaces.dyadicRadius m).2, zpow_lt_one_of_neg₀ (by norm_num) (by omega)⟩
  separated := by
    rintro r s ⟨m, -, rfl, -⟩ ⟨m', -, rfl, -⟩ hrs
    change (8 : ℝ) ^ (-(m : ℤ)) < (8 : ℝ) ^ (-(m' : ℤ)) at hrs
    change 8 * (8 : ℝ) ^ (-(m : ℤ)) ≤ (8 : ℝ) ^ (-(m' : ℤ))
    have hmm : m' < m := by
      by_contra hle
      have : (8 : ℝ) ^ (-(m' : ℤ)) ≤ (8 : ℝ) ^ (-(m : ℤ)) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      linarith
    have h8 : 8 * (8 : ℝ) ^ (-(m : ℤ)) = (8 : ℝ) ^ (1 + -(m : ℤ)) := by
      rw [zpow_add₀ (by norm_num : (8 : ℝ) ≠ 0), zpow_one]
    rw [h8]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)

 
theorem relRad_dyadic (j k : ℕ) : relRad (EndSaving.Interfaces.dyadicRadius j) k = EndSaving.Interfaces.dyadicRadius (k + j) := by
  apply Subtype.ext
  change (8 : ℝ) ^ (-(k : ℤ)) * (8 : ℝ) ^ (-(j : ℤ)) = (8 : ℝ) ^ (-((k + j : ℕ) : ℤ))
  rw [← zpow_add₀ (by norm_num : (8 : ℝ) ≠ 0)]
  congr 1
  push_cast
  ring

theorem relRad_injective (b : Ioi (0 : ℝ)) : Function.Injective fun k => (relRad b k : ℝ) := by
  intro k₁ k₂ hk
  have hb : 0 < (b : ℝ) := b.2
  simp only [relRad_val] at hk
  have h8 : (8 : ℝ) ^ (-(k₁ : ℤ)) = (8 : ℝ) ^ (-(k₂ : ℤ)) := mul_right_cancel₀ hb.ne' hk
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : (8 : ℝ) ^ (-(k₂ : ℤ)) < (8 : ℝ) ^ (-(k₁ : ℤ)) :=
      zpow_lt_zpow_right₀ (by norm_num) (by omega)
    linarith
  · have : (8 : ℝ) ^ (-(k₁ : ℤ)) < (8 : ℝ) ^ (-(k₂ : ℤ)) :=
      zpow_lt_zpow_right₀ (by norm_num) (by omega)
    linarith

 

theorem tildeGoodRadii_density (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (cMinus : ℝ≥0∞) (hm0 : 0 < cMinus) (hmt : cMinus < ⊤)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) :
    ∃ θ : Ioi (0 : ℝ), ∃ a : Ioo (3 / 4 : ℝ) 1, ∃ p : Ioo (0 : ℝ) 1,
      ∀ Cmid : {x : ℝ // cMinus.toReal < x}, ∃ cMid' : ℝ, ∃ hlow : cMinus.toReal < cMid',
        cMid' < Cmid ∧
        ∀ κ : Ioi (0 : ℝ), ∃ ε₀ : Ioo (0 : ℝ) 1,
          ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ j : ℕ,
            let b : Ioi (0 : ℝ) := EndSaving.Interfaces.dyadicRadius j
            ENNReal.ofReal (κ : ℝ) ≤
              P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D' b κ
                ⟨cMid', lt_of_le_of_lt ENNReal.toReal_nonneg hlow⟩) →
            ∃ F : Finset ℝ,
              (F : Set ℝ) = (tildeGoodRadii P h D D' (ξ : ℝ) Q a θ
                ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ p).radii ∩
                  Icc (ε ^ 2 * (b : ℝ)) (ε * (b : ℝ)) ∧
              (5 / 8 : ℝ) * (Real.log ε⁻¹ / Real.log 8) ≤ F.card := by
  obtain ⟨θ, a, p, hmain⟩ := attained_good_swap_rel ξ Q hQ D D' hD hD' P h hh cMinus hm0 hmt
    hMinus
  refine ⟨θ, a, p, fun Cmid => ?_⟩
  obtain ⟨cMid', hlow, hup, hκ⟩ := hmain Cmid
  refine ⟨cMid', hlow, hup, fun κ => ?_⟩
  obtain ⟨ε₀, hε₀⟩ := hκ κ
  refine ⟨ε₀, fun ε hε0 hεε₀ j => ?_⟩
  intro b hG
  have hε1 : ε < 1 := hεε₀.trans_lt ε₀.2.2
  have hb : 0 < (b : ℝ) := b.2
  have hcount := hε₀ b ε hε0 hεε₀ hG
  set Cm : Ioi (0 : ℝ) := ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ with hCmdef
  set G := relGoodTilde P h D D' (ξ : ℝ) Q a θ Cm p b ε with hGdef
  refine ⟨G.image fun k => (relRad b k : ℝ), ?_, ?_⟩
  · ext r
    simp only [Finset.coe_image, mem_image, Finset.mem_coe, mem_inter_iff, mem_Icc]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' := Finset.mem_filter.mp hk
      have hkI := (mem_gridIdx_iff hε0 hε1.le k).mp hk'.1
      have hk1 := one_le_of_mem_gridIdx hε0 hε1 hk'.1
      have hrel : relRad b k = EndSaving.Interfaces.dyadicRadius (k + j) := relRad_dyadic j k
      refine ⟨⟨k + j, by omega, by rw [hrel], ?_⟩, ?_, ?_⟩
      · rw [← hrel]
        exact hk'.2
      · rw [relRad_val]
        exact mul_le_mul_of_nonneg_right hkI.1 hb.le
      · rw [relRad_val]
        exact mul_le_mul_of_nonneg_right hkI.2 hb.le
    · rintro ⟨⟨m, -, rfl, hprob⟩, hlo, hhi⟩
      have hbj : (b : ℝ) = (8 : ℝ) ^ (-(j : ℤ)) := rfl
      have hm : (EndSaving.Interfaces.dyadicRadius m : ℝ) = (8 : ℝ) ^ (-(m : ℤ)) := rfl
      have hjm : j < m := by
        by_contra hle
        have h1 : (8 : ℝ) ^ (-(j : ℤ)) ≤ (8 : ℝ) ^ (-(m : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        have h2 : ε * (b : ℝ) < b := by nlinarith
        rw [hm] at hhi
        rw [hbj] at hhi h2
        linarith
      obtain ⟨k, rfl⟩ : ∃ k, m = k + j := ⟨m - j, by omega⟩
      have hrel : relRad b k = EndSaving.Interfaces.dyadicRadius (k + j) := relRad_dyadic j k
      have hval : (relRad b k : ℝ) = (EndSaving.Interfaces.dyadicRadius (k + j) : ℝ) := by rw [hrel]
      have hkI : k ∈ gridIdx ε := by
        rw [mem_gridIdx_iff hε0 hε1.le]
        rw [← hval, relRad_val] at hlo hhi
        exact ⟨le_of_mul_le_mul_right hlo hb, le_of_mul_le_mul_right hhi hb⟩
      refine ⟨k, Finset.mem_filter.mpr ⟨hkI, ?_⟩, hval⟩
      rw [hrel]
      exact hprob
  · rw [Finset.card_image_of_injective _ (relRad_injective b)]
    have hL : 0 ≤ gridLen ε := gridLen_nonneg hε0 hε1.le
    have h58 : (5 / 8 : ℝ) * gridLen ε ≤ (3 / 4 : ℝ) * gridLen ε := by nlinarith
    exact h58.trans hcount

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
