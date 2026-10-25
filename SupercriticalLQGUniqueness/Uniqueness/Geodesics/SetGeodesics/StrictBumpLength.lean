import SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics.BadEventCode
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylBridge
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.WeylTransferV2




 




set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics

 

theorem length_lt_of_positive_bump_subarc
    (D E : LSCMetric) (ξ : ℝ) (hξ : 0 < ξ)
    (g : C(ℂ, ℝ)) (M δ : ℝ)
    (hforget : Continuous (Measurability.SetGeodesicCodes.euclidForget D))
    (hWeyl : ∀ q : ℂ × ℂ, E q = weylScale ξ g D q)
    (hg : ∀ z : ℂ, 0 ≤ g z ∧ g z ≤ M)
    (hδ : 0 < δ)
    (P : ℝ → ℂ) (T a b : ℝ)
    (hP : E.IsCurve P 0 T)
    (hfin : E.len P 0 T < ⊤)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hpos : ∀ t ∈ Icc a b, δ ≤ g (P t))
    (hne : P a ≠ P b) :
    D.len P 0 T < E.len P 0 T := by
  have hPD : D.IsCurve P 0 T :=
    Toolkit.WeylShift.curve_back_all_continuous D E ξ hξ.le g hforget hWeyl hP
  have hDsub : D.IsCurve P a b :=
    ⟨hab.le, hPD.2.mono (Icc_subset_Icc ha hb)⟩
  have hEsub : E.IsCurve P a b :=
    ⟨hab.le, hP.2.mono (Icc_subset_Icc ha hb)⟩
  have hDpos : 0 < D.len P a b := by
    have hd : 0 < D (P a, P b) := by
      apply pos_iff_ne_zero.mpr
      intro hzero
      exact hne (D.isExtMetric.2.1 _ _ hzero)
    exact hd.trans_le (LSCMetric.apply_le_len D P hab.le)
  have hEsubfin : E.len P a b < ⊤ :=
    (eVariationOn.mono _ (Icc_subset_Icc ha hb)).trans_lt hfin
  have hglobal : D.len P a b ≤ E.len P a b := by
    have hbound := (Toolkit.WeylShift.length_bounds D E ξ hξ.le g 0 M
      hforget hWeyl hg hDsub).1
    simpa only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] using hbound
  have hDfin : D.len P a b < ⊤ := hglobal.trans_lt hEsubfin
  have haT : a ≤ T := hab.le.trans hb
  have hfactor : (1 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (ξ * δ)) := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)]
    exact Real.one_lt_exp_iff.mpr (mul_pos hξ hδ)
  have hlocal : ENNReal.ofReal (Real.exp (ξ * δ)) * D.len P a b ≤
      E.len P a b := by
    have hbound := (Toolkit.WeylLength.weylCurveLength_factor_bounds
      D ξ hξ.le g hforget hDsub δ M hpos
      (fun t ht => (hg (P t)).2)).1
    change ENNReal.ofReal (Real.exp (ξ * δ)) * D.len P a b ≤
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ g D
          (BiLipschitz.Barrier.forget D x, BiLipschitz.Barrier.forget D y)) (D.pt ∘ P) a b at hbound
    rwa [← EndSaving.Choices.weyl_len_eq_weightedLength D E ξ g hWeyl P a b] at hbound
  have hstrict : D.len P a b < E.len P a b := by
    calc
      D.len P a b = 1 * D.len P a b := (one_mul _).symm
      _ < ENNReal.ofReal (Real.exp (ξ * δ)) * D.len P a b :=
        by simpa only [mul_comm] using
          ENNReal.mul_lt_mul_right hDpos.ne' hDfin.ne hfactor
      _ ≤ E.len P a b := hlocal
  have hDpre : D.IsCurve P 0 a :=
    ⟨ha, hPD.2.mono (Icc_subset_Icc le_rfl haT)⟩
  have hDsuf : D.IsCurve P b T :=
    ⟨hb, hPD.2.mono (Icc_subset_Icc (ha.trans hab.le) le_rfl)⟩
  have hpre : D.len P 0 a ≤ E.len P 0 a := by
    have hbound := (Toolkit.WeylShift.length_bounds D E ξ hξ.le g 0 M
      hforget hWeyl hg hDpre).1
    simpa only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] using hbound
  have hsuf : D.len P b T ≤ E.len P b T := by
    have hbound := (Toolkit.WeylShift.length_bounds D E ξ hξ.le g 0 M
      hforget hWeyl hg hDsuf).1
    simpa only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] using hbound
  have hEpreFin : E.len P 0 a < ⊤ :=
    (eVariationOn.mono _ (Icc_subset_Icc le_rfl haT)).trans_lt hfin
  have hEsufFin : E.len P b T < ⊤ :=
    (eVariationOn.mono _ (Icc_subset_Icc (ha.trans hab.le) le_rfl)).trans_lt hfin
  have hDpreFin : D.len P 0 a < ⊤ := hpre.trans_lt hEpreFin
  have hDsufFin : D.len P b T < ⊤ := hsuf.trans_lt hEsufFin
  have hDadd₁ : D.len P 0 a + D.len P a T = D.len P 0 T := by
    simpa only [LSCMetric.len, Set.univ_inter] using
      (eVariationOn.Icc_add_Icc (D.pt ∘ P)
      (s := Set.univ) ha haT (Set.mem_univ a))
  have hDadd₂ : D.len P a b + D.len P b T = D.len P a T := by
    simpa only [LSCMetric.len, Set.univ_inter] using
      (eVariationOn.Icc_add_Icc (D.pt ∘ P)
        (s := Set.univ) hab.le hb (Set.mem_univ b))
  have hEadd₁ : E.len P 0 a + E.len P a T = E.len P 0 T := by
    simpa only [LSCMetric.len, Set.univ_inter] using
      (eVariationOn.Icc_add_Icc (E.pt ∘ P)
      (s := Set.univ) ha haT (Set.mem_univ a))
  have hEadd₂ : E.len P a b + E.len P b T = E.len P a T := by
    simpa only [LSCMetric.len, Set.univ_inter] using
      (eVariationOn.Icc_add_Icc (E.pt ∘ P)
        (s := Set.univ) hab.le hb (Set.mem_univ b))
  calc
    D.len P 0 T = (D.len P 0 a + D.len P a b) + D.len P b T := by
      rw [← hDadd₁, ← hDadd₂, add_assoc]
    _ < (E.len P 0 a + E.len P a b) + E.len P b T :=
      ENNReal.add_lt_add_of_lt_of_le hDsufFin.ne
        (ENNReal.add_lt_add_of_le_of_lt hDpreFin.ne hpre hstrict) hsuf
    _ = E.len P 0 T := by rw [← hEadd₁, ← hEadd₂, add_assoc]

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics
