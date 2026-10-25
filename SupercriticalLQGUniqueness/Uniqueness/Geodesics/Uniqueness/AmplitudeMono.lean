import SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics.StrictBumpLength




 





set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

 

theorem weylScale_smul_mono (D : LSCMetric) (ξ a b : ℝ)
    (hξ : 0 ≤ ξ) (hab : a ≤ b) (f : C(ℂ, ℝ))
    (hf : ∀ z : ℂ, 0 ≤ f z)
    (hforget : Continuous (BiLipschitz.Barrier.forget D)) (x y : ℂ) :
    weylScale ξ (a • f) D (x, y) ≤
      weylScale ξ (b • f) D (x, y) := by
  rw [Toolkit.WeylLength.weylScale_eq_weylDistOn D ξ (a • f) hforget,
    Toolkit.WeylLength.weylScale_eq_weylDistOn D ξ (b • f) hforget]
  apply HigherDimLQGMetric.weylDistOn_mono_weight
  intro z hz
  change Real.exp (ξ * ((a • f) z)) ≤ Real.exp (ξ * ((b • f) z))
  apply Real.exp_le_exp.mpr
  have hmul : a * f z ≤ b * f z := mul_le_mul_of_nonneg_right hab (hf z)
  change ξ * (a * f z) ≤ ξ * (b * f z)
  exact mul_le_mul_of_nonneg_left hmul hξ

 
theorem setDist_smul_mono (D E₁ E₂ : LSCMetric) (ξ a b : ℝ)
    (hξ : 0 ≤ ξ) (hab : a ≤ b) (f : C(ℂ, ℝ))
    (hf : ∀ z : ℂ, 0 ≤ f z)
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (h₁ : ∀ p : ℂ × ℂ, E₁ p = weylScale ξ (a • f) D p)
    (h₂ : ∀ p : ℂ × ℂ, E₂ p = weylScale ξ (b • f) D p)
    (K₁ K₂ : Set ℂ) :
    OptimalConstants.Ratios.setDist E₁ K₁ K₂ ≤ OptimalConstants.Ratios.setDist E₂ K₁ K₂ := by
  unfold OptimalConstants.Ratios.setDist
  refine iInf_mono fun x => iInf_mono fun hx => iInf_mono fun y => iInf_mono fun hy => ?_
  rw [h₁ (x, y), h₂ (x, y)]
  exact weylScale_smul_mono D ξ a b hξ hab f hf hforget x y

 

theorem len_smul_mono (D E₁ E₂ : LSCMetric) (ξ a b : ℝ)
    (hξ : 0 ≤ ξ) (hab : a ≤ b) (f : C(ℂ, ℝ))
    (hf : ∀ z : ℂ, 0 ≤ f z)
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (h₁ : ∀ p : ℂ × ℂ, E₁ p = weylScale ξ (a • f) D p)
    (h₂ : ∀ p : ℂ × ℂ, E₂ p = weylScale ξ (b • f) D p)
    (P : ℝ → ℂ) (s t : ℝ) (hP : D.IsCurve P s t) :
    E₁.len P s t ≤ E₂.len P s t := by
  have hlen₁ := Toolkit.WeylLength.weylCurveLength_eq_weightedLength
    D ξ (a • f) hforget hP
  have hlen₂ := Toolkit.WeylLength.weylCurveLength_eq_weightedLength
    D ξ (b • f) hforget hP
  change HigherDimLQGMetric.curveLengthWith
      (fun x y : D.Space => weylScale ξ (a • f) D
        (BiLipschitz.Barrier.forget D x, BiLipschitz.Barrier.forget D y)) (D.pt ∘ P) s t = _ at hlen₁
  change HigherDimLQGMetric.curveLengthWith
      (fun x y : D.Space => weylScale ξ (b • f) D
        (BiLipschitz.Barrier.forget D x, BiLipschitz.Barrier.forget D y)) (D.pt ∘ P) s t = _ at hlen₂
  rw [← EndSaving.Choices.weyl_len_eq_weightedLength D E₁ ξ (a • f) h₁ P s t] at hlen₁
  rw [← EndSaving.Choices.weyl_len_eq_weightedLength D E₂ ξ (b • f) h₂ P s t] at hlen₂
  change E₁.len P s t = HigherDimLQGMetric.weightedLength
      (fun z : D.Space => Real.exp (ξ * (a * f z))) (D.pt ∘ P) s t at hlen₁
  change E₂.len P s t = HigherDimLQGMetric.weightedLength
      (fun z : D.Space => Real.exp (ξ * (b * f z))) (D.pt ∘ P) s t at hlen₂
  rw [hlen₁, hlen₂]
  apply HigherDimLQGMetric.weightedLength_mono_weight
  intro u hu
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hab (hf (P u))) hξ

 


theorem len_smul_strict_of_plateau (D E₁ E₂ : LSCMetric) (ξ a b : ℝ)
    (hξ : 0 < ξ) (ha₀ : 0 ≤ a) (hab : a < b) (f : C(ℂ, ℝ))
    (hf : ∀ z : ℂ, 0 ≤ f z ∧ f z ≤ 1)
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (h₁ : ∀ p : ℂ × ℂ, E₁ p = weylScale ξ (a • f) D p)
    (h₂ : ∀ p : ℂ × ℂ, E₂ p = weylScale ξ (b • f) D p)
    (P : ℝ → ℂ) (T s t : ℝ) (hP : D.IsCurve P 0 T)
    (hfin : E₂.len P 0 T < ⊤)
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (hplateau : ∀ u ∈ Icc s t, f (P u) = 1)
    (hne : P s ≠ P t) :
    E₁.len P 0 T < E₂.len P 0 T := by
  have hb₀ : 0 ≤ b := ha₀.trans hab.le
  have hDsub : D.IsCurve P s t :=
    ⟨hst.le, hP.2.mono (Icc_subset_Icc hs ht)⟩
  have hDpos : 0 < D.len P s t := by
    have hd : 0 < D (P s, P t) := by
      apply pos_iff_ne_zero.mpr
      intro hzero
      exact hne (D.isExtMetric.2.1 _ _ hzero)
    exact hd.trans_le (LSCMetric.apply_le_len D P hst.le)
  have hEsubfin : E₂.len P s t < ⊤ :=
    (eVariationOn.mono _ (Icc_subset_Icc hs ht)).trans_lt hfin
  have hbound₂ := (Toolkit.WeylShift.length_bounds D E₂ ξ hξ.le (b • f) 0 b
    hforget h₂ (fun z => by
      constructor
      · change 0 ≤ b * f z
        exact mul_nonneg hb₀ (hf z).1
      · change b * f z ≤ b
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf z).2 hb₀)
    hDsub).1
  have hDle : D.len P s t ≤ E₂.len P s t := by
    simpa only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] using hbound₂
  have hDfin : D.len P s t < ⊤ := hDle.trans_lt hEsubfin
  have hlow : ENNReal.ofReal (Real.exp (ξ * b)) * D.len P s t ≤
      E₂.len P s t := by
    have hbound := (Toolkit.WeylLength.weylCurveLength_factor_bounds D ξ hξ.le
      (b • f) hforget hDsub b b
      (fun u hu => by change b ≤ b * f (P u); rw [hplateau u hu]; simp)
      (fun u hu => by change b * f (P u) ≤ b; rw [hplateau u hu]; simp)).1
    change ENNReal.ofReal (Real.exp (ξ * b)) * D.len P s t ≤
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ (b • f) D
          (BiLipschitz.Barrier.forget D x, BiLipschitz.Barrier.forget D y)) (D.pt ∘ P) s t at hbound
    rwa [← EndSaving.Choices.weyl_len_eq_weightedLength D E₂ ξ (b • f) h₂ P s t] at hbound
  have hupp : E₁.len P s t ≤
      ENNReal.ofReal (Real.exp (ξ * a)) * D.len P s t := by
    have hbound := (Toolkit.WeylLength.weylCurveLength_factor_bounds D ξ hξ.le
      (a • f) hforget hDsub a a
      (fun u hu => by change a ≤ a * f (P u); rw [hplateau u hu]; simp)
      (fun u hu => by change a * f (P u) ≤ a; rw [hplateau u hu]; simp)).2
    change HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ (a • f) D
          (BiLipschitz.Barrier.forget D x, BiLipschitz.Barrier.forget D y)) (D.pt ∘ P) s t ≤
      ENNReal.ofReal (Real.exp (ξ * a)) * D.len P s t at hbound
    rwa [← EndSaving.Choices.weyl_len_eq_weightedLength D E₁ ξ (a • f) h₁ P s t] at hbound
  have hfactor : ENNReal.ofReal (Real.exp (ξ * a)) <
      ENNReal.ofReal (Real.exp (ξ * b)) := by
    exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mpr
      (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hab hξ))
  have hlocal : E₁.len P s t < E₂.len P s t := by
    calc
      E₁.len P s t ≤ ENNReal.ofReal (Real.exp (ξ * a)) * D.len P s t := hupp
      _ < ENNReal.ofReal (Real.exp (ξ * b)) * D.len P s t :=
        by simpa only [mul_comm] using
          ENNReal.mul_lt_mul_right hDpos.ne' hDfin.ne hfactor
      _ ≤ E₂.len P s t := hlow
  have hsT : s ≤ T := hst.le.trans ht
  have hDpre : D.IsCurve P 0 s :=
    ⟨hs, hP.2.mono (Icc_subset_Icc le_rfl hsT)⟩
  have hDsuf : D.IsCurve P t T :=
    ⟨ht, hP.2.mono (Icc_subset_Icc (hs.trans hst.le) le_rfl)⟩
  have hpre := len_smul_mono D E₁ E₂ ξ a b hξ.le hab.le f
    (fun z => (hf z).1) hforget h₁ h₂ P 0 s hDpre
  have hsuf := len_smul_mono D E₁ E₂ ξ a b hξ.le hab.le f
    (fun z => (hf z).1) hforget h₁ h₂ P t T hDsuf
  have hE₁preFin : E₁.len P 0 s < ⊤ :=
    hpre.trans_lt ((eVariationOn.mono _ (Icc_subset_Icc le_rfl hsT)).trans_lt hfin)
  have hE₁sufFin : E₁.len P t T < ⊤ :=
    hsuf.trans_lt ((eVariationOn.mono _
      (Icc_subset_Icc (hs.trans hst.le) le_rfl)).trans_lt hfin)
  have hsum₁ (E : LSCMetric) : E.len P 0 T =
      (E.len P 0 s + E.len P s t) + E.len P t T := by
    have hA : E.len P 0 s + E.len P s T = E.len P 0 T := by
      simpa only [LSCMetric.len, Set.univ_inter] using
        (eVariationOn.Icc_add_Icc (E.pt ∘ P) (s := Set.univ) hs hsT (Set.mem_univ s))
    have hB : E.len P s t + E.len P t T = E.len P s T := by
      simpa only [LSCMetric.len, Set.univ_inter] using
        (eVariationOn.Icc_add_Icc (E.pt ∘ P) (s := Set.univ) hst.le ht (Set.mem_univ t))
    rw [← hA, ← hB, add_assoc]
  calc
    E₁.len P 0 T = (E₁.len P 0 s + E₁.len P s t) + E₁.len P t T := hsum₁ E₁
    _ < (E₂.len P 0 s + E₂.len P s t) + E₂.len P t T :=
      ENNReal.add_lt_add_of_lt_of_le hE₁sufFin.ne
        (ENNReal.add_lt_add_of_le_of_lt hE₁preFin.ne hpre hlocal) hsuf
    _ = E₂.len P 0 T := (hsum₁ E₂).symm

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
