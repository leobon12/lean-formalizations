import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.AmplitudeMono




 






set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

 

theorem exists_nonconstant_plateau_subarc
    (E : LSCMetric) (K₁ K₂ V : Set ℂ) (f : C(ℂ, ℝ))
    (hforget : Continuous (BiLipschitz.Barrier.forget E)) (hV : IsOpen V)
    (hfV : ∀ z ∈ V, f z = 1)
    (Q : ℝ → ℂ) (S : ℝ) (hQ : EndSaving.FiniteEvents.SetGeodesic E K₁ K₂ Q S)
    (hstart : Q 0 ∉ V) (hend : Q S ∉ V)
    (hhit : ∃ u ∈ Icc 0 S, Q u ∈ V) :
    ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ S ∧
      (∀ u ∈ Icc s t, f (Q u) = 1) ∧ Q s ≠ Q t := by
  have hgeo := EndSaving.FiniteEvents.SetGeodesic.isGeodesic E K₁ K₂ Q S hQ
  have hunit := hQ.1.2.1
  have hcont : ContinuousOn Q (Icc 0 S) := by
    have hc := hforget.comp_continuousOn hQ.1.1.2
    change ContinuousOn Q (Icc 0 S) at hc
    exact hc
  obtain ⟨u, hu, huV⟩ := hhit
  have hu0 : 0 < u := by
    have hne : u ≠ 0 := by intro heq; exact hstart (heq ▸ huV)
    exact lt_of_le_of_ne hu.1 (Ne.symm hne)
  have huS : u < S := by
    have hne : u ≠ S := by intro heq; exact hend (heq ▸ huV)
    exact lt_of_le_of_ne hu.2 hne
  have huIoo : u ∈ Ioo 0 S := ⟨hu0, huS⟩
  have hnhds : Icc 0 S ∈ nhds u :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds huIoo) Ioo_subset_Icc_self
  have hcontAt : ContinuousAt Q u := hcont.continuousAt hnhds
  have hpre : Q ⁻¹' V ∈ nhds u := hcontAt.preimage_mem_nhds (hV.mem_nhds huV)
  obtain ⟨l, r, ⟨hlu, hur⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hpre
  obtain ⟨t, hut, htmin⟩ := exists_between (lt_min hur huS)
  have htR : t < r := htmin.trans_le (min_le_left _ _)
  have htS : t ≤ S := (htmin.trans_le (min_le_right _ _)).le
  have hinside : ∀ v ∈ Icc u t, Q v ∈ V := by
    intro v hv
    exact hsub ⟨hlu.trans_le hv.1, hv.2.trans_lt htR⟩
  have hneq : Q u ≠ Q t := by
    intro heq
    have hed := LQGMetric.MetricGeometry.IsGeodesicCurve.edist_eq_of_hasUnitSpeedOn
      (s := u) (t := t) hgeo hunit hu ⟨hu.1.trans hut.le, htS⟩ hut.le
    have hzero : (0 : ENNReal) = ENNReal.ofReal (t - u) := by
      simpa only [Function.comp_apply, heq, edist_self] using hed
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hut)).ne' hzero.symm
  exact ⟨u, t, hu.1, hut, htS, (fun v hv => hfV _ (hinside v hv)), hneq⟩

 


theorem no_later_set_geodesic_of_plateau
    (D E₁ E₂ : LSCMetric) (ξ a b : ℝ)
    (hξ : 0 < ξ) (ha₀ : 0 ≤ a) (hab : a < b)
    (f : C(ℂ, ℝ)) (hf : ∀ z : ℂ, 0 ≤ f z ∧ f z ≤ 1)
    (hforget : Continuous (BiLipschitz.Barrier.forget D)) (hLength : D.IsLengthSpace)
    (h₁ : ∀ p : ℂ × ℂ, E₁ p = weylScale ξ (a • f) D p)
    (h₂ : ∀ p : ℂ × ℂ, E₂ p = weylScale ξ (b • f) D p)
    (K₁ K₂ : Set ℂ)
    (P : ℝ → ℂ) (T : ℝ)
    (hP : EndSaving.FiniteEvents.SetGeodesic E₁ K₁ K₂ P T)
    (hzero : ∀ u ∈ Icc 0 T, f (P u) = 0)
    (Q : ℝ → ℂ) (S s t : ℝ)
    (hQ : EndSaving.FiniteEvents.SetGeodesic E₂ K₁ K₂ Q S)
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ S)
    (hplateau : ∀ u ∈ Icc s t, f (Q u) = 1)
    (hne : Q s ≠ Q t) : False := by
  rcases hP with ⟨⟨hPcurve, hPunit, hPlen, hPfin⟩, hP0, hPT, hPset⟩
  rcases hQ with ⟨⟨hQcurve, hQunit, hQlen, hQfin⟩, hQ0, hQS, hQset⟩
  have hPbase : D.IsCurve P 0 T :=
    Toolkit.WeylShift.curve_back_all_continuous D E₁ ξ hξ.le (a • f)
      hforget h₁ hPcurve
  have hQbase : D.IsCurve Q 0 S :=
    Toolkit.WeylShift.curve_back_all_continuous D E₂ ξ hξ.le (b • f)
      hforget h₂ hQcurve
  have hb₀ : 0 ≤ b := ha₀.trans hab.le
  have hE₂curve : E₂.IsCurve P 0 T :=
    Toolkit.WeylShift.curve_forward D E₂ ξ hξ.le (b • f) 0 b hforget h₂
      (fun z => by
        constructor
        · change 0 ≤ b * f z
          exact mul_nonneg hb₀ (hf z).1
        · change b * f z ≤ b
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf z).2 hb₀)
      hLength hPbase
  have hzero₁ : ∀ u ∈ Icc 0 T, (a • f) (P u) = 0 := by
    intro u hu
    change a * f (P u) = 0
    rw [hzero u hu, mul_zero]
  have hzero₂ : ∀ u ∈ Icc 0 T, (b • f) (P u) = 0 := by
    intro u hu
    change b * f (P u) = 0
    rw [hzero u hu, mul_zero]
  have hE₁zero := Toolkit.WeylShift.length_eq_of_zero_trace_all D E₁ ξ hξ.le
    (a • f) hforget h₁ hPcurve hzero₁
  have hE₂zero := Toolkit.WeylShift.length_eq_of_zero_trace_all D E₂ ξ hξ.le
    (b • f) hforget h₂ hE₂curve hzero₂
  have hPtime : E₁.len P 0 T = ENNReal.ofReal T := by
    rw [E₁.len_eq_curveLength]
    simpa only [sub_zero] using
      (LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hPunit
        (left_mem_Icc.mpr hPcurve.1) (right_mem_Icc.mpr hPcurve.1))
  have hQtime : E₂.len Q 0 S = ENNReal.ofReal S := by
    rw [E₂.len_eq_curveLength]
    simpa only [sub_zero] using
      (LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hQunit
        (left_mem_Icc.mpr hQcurve.1) (right_mem_Icc.mpr hQcurve.1))
  have hE₁min : E₁.len P 0 T = OptimalConstants.Ratios.setDist E₁ K₁ K₂ :=
    hPtime.trans hPset
  have hE₂min : E₂.len Q 0 S = OptimalConstants.Ratios.setDist E₂ K₁ K₂ :=
    hQtime.trans hQset
  have hsetmono := setDist_smul_mono D E₁ E₂ ξ a b hξ.le hab.le f
    (fun z => (hf z).1) hforget h₁ h₂ K₁ K₂
  have hsetupper : OptimalConstants.Ratios.setDist E₂ K₁ K₂ ≤ E₂.len P 0 T :=
    (iInf₂_le_of_le (P 0) hP0 (iInf₂_le (P T) hPT)).trans
      (LSCMetric.apply_le_len E₂ P hE₂curve.1)
  have hseteq : OptimalConstants.Ratios.setDist E₁ K₁ K₂ = OptimalConstants.Ratios.setDist E₂ K₁ K₂ := by
    apply le_antisymm hsetmono
    calc
      OptimalConstants.Ratios.setDist E₂ K₁ K₂ ≤ E₂.len P 0 T := hsetupper
      _ = E₁.len P 0 T := hE₂zero.trans hE₁zero.symm
      _ = OptimalConstants.Ratios.setDist E₁ K₁ K₂ := hE₁min
  have hstrict := len_smul_strict_of_plateau D E₁ E₂ ξ a b hξ ha₀ hab
    f hf hforget h₁ h₂ Q S s t hQbase (hQlen.symm ▸ hQfin) hs hst ht hplateau hne
  have hE₁lower : OptimalConstants.Ratios.setDist E₁ K₁ K₂ ≤ E₁.len Q 0 S :=
    (iInf₂_le_of_le (Q 0) hQ0 (iInf₂_le (Q S) hQS)).trans
      (LSCMetric.apply_le_len E₁ Q hQcurve.1)
  have hbad : OptimalConstants.Ratios.setDist E₂ K₁ K₂ < OptimalConstants.Ratios.setDist E₂ K₁ K₂ := by
    calc
      OptimalConstants.Ratios.setDist E₂ K₁ K₂ = OptimalConstants.Ratios.setDist E₁ K₁ K₂ := hseteq.symm
      _ ≤ E₁.len Q 0 S := hE₁lower
      _ < E₂.len Q 0 S := hstrict
      _ = OptimalConstants.Ratios.setDist E₂ K₁ K₂ := hE₂min
  exact lt_irrefl _ hbad

 


theorem badSetGeodesic_no_later_amplitude
    (D E₁ E₂ : LSCMetric) (ξ a b : ℝ)
    (hξ : 0 < ξ) (ha₀ : 0 ≤ a) (hab : a < b)
    (f : C(ℂ, ℝ)) (hf : ∀ z : ℂ, 0 ≤ f z ∧ f z ≤ 1)
    (hforget : Continuous (BiLipschitz.Barrier.forget D)) (hLength : D.IsLengthSpace)
    (h₁ : ∀ p : ℂ × ℂ, E₁ p = weylScale ξ (a • f) D p)
    (h₂ : ∀ p : ℂ × ℂ, E₂ p = weylScale ξ (b • f) D p)
    (K₁ K₂ U V : Set ℂ) (hV : IsOpen V)
    (hV₁ : Disjoint V K₁) (hV₂ : Disjoint V K₂)
    (hfU : ∀ z ∉ U, f z = 0) (hfV : ∀ z ∈ V, f z = 1) :
    Geodesics.SetGeodesics.BadSetGeodesic E₁ K₁ K₂ U V →
      ¬ Geodesics.SetGeodesics.BadSetGeodesic E₂ K₁ K₂ U V := by
  rintro ⟨P, T, hP, hAvoid, _, _, _, _⟩
    ⟨_, _, _, _, Q, S, hQ, hHit⟩
  have hzero : ∀ u ∈ Icc 0 T, f (P u) = 0 := by
    intro u hu
    exact hfU _ (hAvoid u hu)
  have hforget₂ : Continuous (BiLipschitz.Barrier.forget E₂) :=
    Toolkit.WeylShift.continuous_forget_of_weyl D E₂ ξ hξ.le (b • f) hforget h₂
  have hQ0 : Q 0 ∉ V := by
    intro hv
    exact (Set.disjoint_left.mp hV₁ hv) hQ.2.1
  have hQS : Q S ∉ V := by
    intro hv
    exact (Set.disjoint_left.mp hV₂ hv) hQ.2.2.1
  obtain ⟨s, t, hs, hst, ht, hplateau, hne⟩ :=
    exists_nonconstant_plateau_subarc E₂ K₁ K₂ V f hforget₂ hV hfV
      Q S hQ hQ0 hQS hHit
  exact no_later_set_geodesic_of_plateau D E₁ E₂ ξ a b hξ ha₀ hab
    f hf hforget hLength h₁ h₂ K₁ K₂ P T hP hzero Q S s t hQ
    hs hst ht hplateau hne

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
