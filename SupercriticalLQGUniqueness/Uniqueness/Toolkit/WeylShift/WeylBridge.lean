import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylLength.WeylLength
import SupercriticalLQGUniqueness.Frozen.IsLFPPExponent




 





set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

 

theorem length_bounds (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ)) (m M : ℝ)
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ p : ℂ × ℂ, E p = weylScale ξ g D p)
    (hg : ∀ x : ℂ, m ≤ g x ∧ g x ≤ M)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) :
    ENNReal.ofReal (Real.exp (ξ * m)) * D.len P a b ≤ E.len P a b ∧
      E.len P a b ≤ ENNReal.ofReal (Real.exp (ξ * M)) * D.len P a b := by
  have hδ : (fun x y : D.Space => weylScale ξ g D (x, y)) =
      (fun x y : D.Space => E (x, y)) := by
    funext x y
    exact (hWeyl (x, y)).symm
  have hE : E.len P a b =
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => E (x, y)) (D.pt ∘ P) a b := by
    rw [E.len_eq_curveLength]
    exact (HigherDimLQGMetric.curveLengthWith_edist (E.pt ∘ P) a b).symm
  have h := Toolkit.WeylLength.weylCurveLength_factor_bounds D ξ hξ g hforget hP m M
    (fun t ht => (hg (P t)).1) (fun t ht => (hg (P t)).2)
  change ENNReal.ofReal (Real.exp (ξ * m)) * D.len P a b ≤
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ g D (x, y)) (D.pt ∘ P) a b ∧
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ g D (x, y)) (D.pt ∘ P) a b ≤
      ENNReal.ofReal (Real.exp (ξ * M)) * D.len P a b at h
  rw [hδ, ← hE] at h
  exact h

 

theorem distance_lower (D E : LSCMetric) (ξ : ℝ) (g : C(ℂ, ℝ)) (m : ℝ)
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ p : ℂ × ℂ, E p = weylScale ξ g D p)
    (hm : ∀ x : ℂ, m ≤ g x) (hξ : 0 ≤ ξ) (x y : ℂ) :
    ENNReal.ofReal (Real.exp (ξ * m)) * D (x, y) ≤ E (x, y) := by
  rw [hWeyl, Toolkit.WeylLength.weylScale_eq_weylDistOn D ξ g hforget]
  let w : D.Space → ℝ := fun z => Real.exp (ξ * g z)
  have hw : ∀ z ∈ (Set.univ : Set D.Space), edist (D.pt x) z ≤ (⊤ : ENNReal) →
      Real.exp (ξ * m) ≤ w z := by
    intro z hz hdist
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hm z) hξ)
  have h := HigherDimLQGMetric.weylDistOn_ge_min
    (U := Set.univ) (w := w) (x := D.pt x) (R := ⊤) hw (D.pt y)
  change ENNReal.ofReal (Real.exp (ξ * m)) * edist (D.pt x) (D.pt y) ≤
      HigherDimLQGMetric.weylDistOn w Set.univ (D.pt x) (D.pt y)
  simpa only [min_top_right] using h

 
theorem distance_upper (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ)) (m M : ℝ)
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ p : ℂ × ℂ, E p = weylScale ξ g D p)
    (hg : ∀ x : ℂ, m ≤ g x ∧ g x ≤ M) (hLength : D.IsLengthSpace) (x y : ℂ) :
    E (x, y) ≤ ENNReal.ofReal (Real.exp (ξ * M)) * D (x, y) := by
  rw [(LSCMetric.isLengthSpace_iff_eq_iInf D).mp hLength x y]
  have hc0 : ENNReal.ofReal (Real.exp (ξ * M)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hct : ENNReal.ofReal (Real.exp (ξ * M)) ≠ ⊤ := ENNReal.ofReal_ne_top
  simp only [ENNReal.mul_iInf_of_ne hc0 hct]
  apply le_iInf
  intro P
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply le_iInf
  intro hP
  apply le_iInf
  intro hPa
  apply le_iInf
  intro hPb
  rw [hWeyl, ← hPa, ← hPb, Toolkit.WeylLength.weylScale_eq_weylDistOn D ξ g hforget]
  let w : D.Space → ℝ := fun z => Real.exp (ξ * g z)
  have hw : HigherDimLQGMetric.weylDistOn w Set.univ (D.pt (P a)) (D.pt (P b)) ≤
      HigherDimLQGMetric.weightedLength w (D.pt ∘ P) a b :=
    HigherDimLQGMetric.weylDistOn_le_of_curve hP.1 hP.2
      (fun _ _ => Set.mem_univ _)
  have hwl := Toolkit.WeylLength.weylCurveLength_eq_weightedLength D ξ g hforget hP
  have hδ : (fun u v : D.Space => weylScale ξ g D (u, v)) =
      (fun u v : D.Space => E (u, v)) := by
    funext u v
    exact (hWeyl (u, v)).symm
  have hE : E.len P a b =
      HigherDimLQGMetric.curveLengthWith
        (fun u v : D.Space => E (u, v)) (D.pt ∘ P) a b := by
    rw [E.len_eq_curveLength]
    exact (HigherDimLQGMetric.curveLengthWith_edist (E.pt ∘ P) a b).symm
  have hbound := (length_bounds D E ξ hξ g m M hforget hWeyl hg hP).2
  change HigherDimLQGMetric.weylDistOn w Set.univ (D.pt (P a)) (D.pt (P b)) ≤
    ENNReal.ofReal (Real.exp (ξ * M)) * D.len P a b
  calc
    _ ≤ HigherDimLQGMetric.weightedLength w (D.pt ∘ P) a b := hw
    _ = E.len P a b := by
      change HigherDimLQGMetric.curveLengthWith
        (fun u v : D.Space => weylScale ξ g D (u, v))
        (D.pt ∘ P) a b = HigherDimLQGMetric.weightedLength w (D.pt ∘ P) a b at hwl
      rw [hδ, ← hE] at hwl
      exact hwl.symm
    _ ≤ ENNReal.ofReal (Real.exp (ξ * M)) * D.len P a b := hbound

 
theorem curve_forward (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ)) (m M : ℝ)
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ p : ℂ × ℂ, E p = weylScale ξ g D p)
    (hg : ∀ x : ℂ, m ≤ g x ∧ g x ≤ M) (hLength : D.IsLengthSpace)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) : E.IsCurve P a b := by
  let K : NNReal := ⟨Real.exp (ξ * M), (Real.exp_pos _).le⟩
  let F : D.Space → E.Space := id
  have hLip : LipschitzWith K F := by
    intro x y
    have h := distance_upper D E ξ hξ g m M hforget hWeyl hg hLength x y
    change E (x, y) ≤ (K : ENNReal) * D (x, y)
    have hK : (K : ENNReal) = ENNReal.ofReal (Real.exp (ξ * M)) := by
      have hKr : (K : ℝ) = Real.exp (ξ * M) := rfl
      rw [← hKr, ENNReal.ofReal_coe_nnreal]
    rw [hK]
    exact h
  refine ⟨hP.1, ?_⟩
  change ContinuousOn (F ∘ (D.pt ∘ P)) (Icc a b)
  exact hLip.continuous.comp_continuousOn hP.2

 

theorem curve_back (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ)) (m : ℝ)
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ p : ℂ × ℂ, E p = weylScale ξ g D p)
    (hm : ∀ x : ℂ, m ≤ g x)
    {P : ℝ → ℂ} {a b : ℝ} (hP : E.IsCurve P a b) : D.IsCurve P a b := by
  let K : NNReal := ⟨Real.exp (-(ξ * m)), (Real.exp_pos _).le⟩
  have hKc : (K : ENNReal) * ENNReal.ofReal (Real.exp (ξ * m)) = 1 := by
    have hK : (K : ENNReal) = ENNReal.ofReal (Real.exp (-(ξ * m))) := by
      have hKr : (K : ℝ) = Real.exp (-(ξ * m)) := rfl
      rw [← hKr, ENNReal.ofReal_coe_nnreal]
    rw [hK, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero _), ENNReal.ofReal_one]
  have hcomp (x y : ℂ) : D (x, y) ≤ (K : ENNReal) * E (x, y) := by
    have hlower := distance_lower D E ξ g m hforget hWeyl hm hξ x y
    calc
      D (x, y) = 1 * D (x, y) := (one_mul _).symm
      _ = ((K : ENNReal) * ENNReal.ofReal (Real.exp (ξ * m))) * D (x, y) := by rw [hKc]
      _ = (K : ENNReal) *
          (ENNReal.ofReal (Real.exp (ξ * m)) * D (x, y)) := mul_assoc _ _ _
      _ ≤ (K : ENNReal) * E (x, y) := by gcongr
  let F : E.Space → D.Space := id
  have hLip : LipschitzWith K F := by
    intro x y
    exact hcomp x y
  refine ⟨hP.1, ?_⟩
  change ContinuousOn (F ∘ (E.pt ∘ P)) (Icc a b)
  exact hLip.continuous.comp_continuousOn hP.2

 

theorem length_eq_of_zero_trace (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ)) (m : ℝ)
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ p : ℂ × ℂ, E p = weylScale ξ g D p)
    (hm : ∀ x : ℂ, m ≤ g x)
    {P : ℝ → ℂ} {a b : ℝ} (hP : E.IsCurve P a b)
    (hzero : ∀ t ∈ Icc a b, g (P t) = 0) :
    E.len P a b = D.len P a b := by
  have hPD := curve_back D E ξ hξ g m hforget hWeyl hm hP
  have hLS47 := Toolkit.WeylLength.weylCurveLength_eq_of_zero_on_trace
    D ξ g hforget hPD hzero
  have hE : E.len P a b =
      HigherDimLQGMetric.curveLengthWith
        (fun x y : ℂ => E (x, y)) P a b := by
    rw [E.len_eq_curveLength, ← HigherDimLQGMetric.curveLengthWith_edist]
    rfl
  rw [hE]
  have heq : (fun x y : ℂ => E (x, y)) =
      (fun x y : ℂ => weylScale ξ g D (x, y)) := by
    funext x y
    exact hWeyl (x, y)
  rw [heq]
  exact hLS47

 

theorem curve_back_euclidean (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ)) (m : ℝ)
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ p : ℂ × ℂ, E p = weylScale ξ g D p)
    (hm : ∀ x : ℂ, m ≤ g x)
    {P : ℝ → ℂ} {a b : ℝ} (hP : E.IsCurve P a b) :
    ContinuousOn P (Icc a b) := by
  have hPD := curve_back D E ξ hξ g m hforget hWeyl hm hP
  exact hforget.comp_continuousOn hPD.2

 


theorem off_bump_subinterval_time (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (B : ℝ)
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ p : ℂ × ℂ, E p = weylScale ξ (-f) D p)
    (hB : ∀ x : ℂ, f x ≤ B)
    {P : ℝ → ℂ} {T a b : ℝ} (hP : E.IsCurve P 0 T)
    (hu : HasUnitSpeedOn (E.pt ∘ P) (Icc 0 T))
    (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b)
    (hzero : ∀ t ∈ Icc a b, f (P t) = 0) :
    D.IsCurve P a b ∧ D.len P a b = ENNReal.ofReal (b - a) := by
  have hPE : E.IsCurve P a b :=
    ⟨hab, hP.2.mono (Icc_subset_Icc ha.1 hb.2)⟩
  have hm : ∀ x : ℂ, -B ≤ (-f) x := by
    intro x
    simpa using neg_le_neg (hB x)
  have hPD := curve_back D E ξ hξ (-f) (-B) hforget hWeyl hm hPE
  have heq := length_eq_of_zero_trace D E ξ hξ (-f) (-B)
    hforget hWeyl hm hPE (by intro t ht; simpa using congrArg Neg.neg (hzero t ht))
  have htime : E.len P a b = ENNReal.ofReal (b - a) := by
    rw [E.len_eq_curveLength]
    exact LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hu ha hb
  exact ⟨hPD, heq.symm.trans htime⟩

 
theorem off_bump_support_subinterval_time (D E : LSCMetric) (ξ : ℝ)
    (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) (B : ℝ)
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ p : ℂ × ℂ, E p = weylScale ξ (-f) D p)
    (hB : ∀ x : ℂ, f x ≤ B)
    {P : ℝ → ℂ} {T a b : ℝ} (hP : E.IsCurve P 0 T)
    (hu : HasUnitSpeedOn (E.pt ∘ P) (Icc 0 T))
    (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b)
    (havoid : ∀ t ∈ Icc a b, P t ∉ tsupport (f : ℂ → ℝ)) :
    D.IsCurve P a b ∧ D.len P a b = ENNReal.ofReal (b - a) :=
  off_bump_subinterval_time D E ξ hξ f B hforget hWeyl hB
    hP hu ha hb hab
    (fun t ht => image_eq_zero_of_notMem_tsupport (havoid t ht))

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift
