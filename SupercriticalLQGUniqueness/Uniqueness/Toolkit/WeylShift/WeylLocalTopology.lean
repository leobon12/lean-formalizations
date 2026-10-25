import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylBridge




 
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

theorem continuous_forget_of_weyl (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ q : ℂ × ℂ, E q = weylScale ξ g D q) :
    Continuous (euclidForget E) := by
  rw [continuous_iff_continuousAt]
  intro x
  let x0 : ℂ := euclidForget E x
  have hG : Continuous (fun z : D.Space => g (euclidForget D z)) :=
    g.continuous.comp hforget
  have hNhds : {z : D.Space | g (euclidForget D z) > g x0 - 1} ∈ 𝓝 (D.pt x0) := by
    apply (isOpen_Ioi.preimage hG).mem_nhds
    change g x0 - 1 < g x0
    linarith
  obtain ⟨R, hR0, hRsub⟩ := Metric.nhds_basis_eball.mem_iff.mp hNhds
  obtain ⟨r, hr0, hrR⟩ := exists_between hR0
  have hWeight : ∀ z : D.Space, edist (D.pt x0) z ≤ r →
      Real.exp (ξ * (g x0 - 1)) ≤ Real.exp (ξ * g (euclidForget D z)) := by
    intro z hz
    have hzR : z ∈ Metric.eball (D.pt x0) R :=
      Metric.mem_eball.mpr (by rw [edist_comm]; exact lt_of_le_of_lt hz hrR)
    have hzlow : g x0 - 1 < g (euclidForget D z) := hRsub hzR
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzlow.le hξ)
  have hLocal (y : ℂ) :
      ENNReal.ofReal (Real.exp (ξ * (g x0 - 1))) *
        min (D (x0, y)) r ≤ E (x0, y) := by
    rw [hWeyl (x0,y), Toolkit.WeylLength.weylScale_eq_weylDistOn D ξ g hforget]
    have h := HigherDimLQGMetric.weylDistOn_ge_min
      (U := Set.univ) (w := fun z : D.Space => Real.exp (ξ * g (euclidForget D z)))
      (x := D.pt x0) (R := r)
      (fun z _ hz => hWeight z hz) (D.pt y)
    convert h using 1 <;> rfl
  have hAt : ContinuousAt (euclidForget D) (D.pt x0) := hforget.continuousAt
  rw [ContinuousAt, (Metric.nhds_basis_eball).tendsto_iff Metric.nhds_basis_ball] at hAt
  rw [ContinuousAt, (Metric.nhds_basis_eball).tendsto_iff Metric.nhds_basis_ball]
  intro ε hε
  obtain ⟨δ, hδ, hδmap⟩ := hAt ε hε
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * (g x0 - 1)))
  let ρ : ℝ≥0∞ := min r δ
  have hc0 : 0 < c := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hρ0 : 0 < ρ := lt_min hr0 hδ
  refine ⟨c * ρ, ENNReal.mul_pos hc0.ne' hρ0.ne', ?_⟩
  intro y hy
  have hEy : E (x0, (y : ℂ)) < c * ρ := by
    rw [Metric.mem_eball] at hy
    change edist x y < c * ρ
    simpa only [edist_comm] using hy
  have hmin : min (D (x0, (y : ℂ))) r < ρ := by
    have hle : c * min (D (x0, (y : ℂ))) r ≤ E (x0, (y : ℂ)) :=
      hLocal (y : ℂ)
    by_contra hnot
    have hρle : ρ ≤ min (D (x0, (y : ℂ))) r := le_of_not_gt hnot
    have hmul : c * ρ ≤ c * min (D (x0, (y : ℂ))) r := by gcongr
    exact (not_lt_of_ge (hmul.trans hle)) hEy
  have hDy : D (x0, (y : ℂ)) < δ := by
    by_cases hDr : D (x0, (y : ℂ)) < r
    · rw [min_eq_left hDr.le] at hmin
      exact hmin.trans_le (min_le_right _ _)
    · have hrD : r ≤ D (x0, (y : ℂ)) := le_of_not_gt hDr
      rw [min_eq_right hrD] at hmin
      have : r < r := hmin.trans_le (min_le_left _ _)
      exact False.elim (lt_irrefl r this)
  have hyD : D.pt (y : ℂ) ∈ Metric.eball (D.pt x0) δ := by
    rw [Metric.mem_eball]
    have hDy' : edist (D.pt x0) (D.pt (y : ℂ)) < δ := hDy
    simpa only [edist_comm] using hDy'
  exact hδmap (D.pt (y : ℂ)) hyD

 

theorem continuous_weyl_back (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ q : ℂ × ℂ, E q = weylScale ξ g D q) :
    Continuous (fun z : E.Space => D.pt (euclidForget E z)) := by
  rw [continuous_iff_continuousAt]
  intro x
  let x0 : ℂ := euclidForget E x
  have hG : Continuous (fun z : D.Space => g (euclidForget D z)) :=
    g.continuous.comp hforget
  have hNhds : {z : D.Space | g (euclidForget D z) > g x0 - 1} ∈ 𝓝 (D.pt x0) := by
    apply (isOpen_Ioi.preimage hG).mem_nhds
    change g x0 - 1 < g x0
    linarith
  obtain ⟨R, hR0, hRsub⟩ := Metric.nhds_basis_eball.mem_iff.mp hNhds
  obtain ⟨r, hr0, hrR⟩ := exists_between hR0
  have hWeight : ∀ z : D.Space, edist (D.pt x0) z ≤ r →
      Real.exp (ξ * (g x0 - 1)) ≤ Real.exp (ξ * g (euclidForget D z)) := by
    intro z hz
    have hzR : z ∈ Metric.eball (D.pt x0) R :=
      Metric.mem_eball.mpr (by rw [edist_comm]; exact lt_of_le_of_lt hz hrR)
    have hzlow : g x0 - 1 < g (euclidForget D z) := hRsub hzR
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzlow.le hξ)
  have hLocal (y : ℂ) :
      ENNReal.ofReal (Real.exp (ξ * (g x0 - 1))) *
        min (D (x0, y)) r ≤ E (x0, y) := by
    rw [hWeyl (x0,y), Toolkit.WeylLength.weylScale_eq_weylDistOn D ξ g hforget]
    have h := HigherDimLQGMetric.weylDistOn_ge_min
      (U := Set.univ) (w := fun z : D.Space => Real.exp (ξ * g (euclidForget D z)))
      (x := D.pt x0) (R := r)
      (fun z _ hz => hWeight z hz) (D.pt y)
    convert h using 1 <;> rfl
  rw [ContinuousAt, (Metric.nhds_basis_eball).tendsto_iff Metric.nhds_basis_eball]
  intro δ hδ
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * (g x0 - 1)))
  let ρ : ℝ≥0∞ := min r δ
  have hc0 : 0 < c := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hρ0 : 0 < ρ := lt_min hr0 hδ
  refine ⟨c * ρ, ENNReal.mul_pos hc0.ne' hρ0.ne', ?_⟩
  intro y hy
  have hEy : E (x0, (y : ℂ)) < c * ρ := by
    rw [Metric.mem_eball] at hy
    change edist x y < c * ρ
    simpa only [edist_comm] using hy
  have hmin : min (D (x0, (y : ℂ))) r < ρ := by
    have hle : c * min (D (x0, (y : ℂ))) r ≤ E (x0, (y : ℂ)) :=
      hLocal (y : ℂ)
    by_contra hnot
    have hρle : ρ ≤ min (D (x0, (y : ℂ))) r := le_of_not_gt hnot
    have hmul : c * ρ ≤ c * min (D (x0, (y : ℂ))) r := by gcongr
    exact (not_lt_of_ge (hmul.trans hle)) hEy
  have hDy : D (x0, (y : ℂ)) < δ := by
    by_cases hDr : D (x0, (y : ℂ)) < r
    · rw [min_eq_left hDr.le] at hmin
      exact hmin.trans_le (min_le_right _ _)
    · have hrD : r ≤ D (x0, (y : ℂ)) := le_of_not_gt hDr
      rw [min_eq_right hrD] at hmin
      have : r < r := hmin.trans_le (min_le_left _ _)
      exact False.elim (lt_irrefl r this)
  rw [Metric.mem_eball]
  have hDy' : edist (D.pt x0) (D.pt (y : ℂ)) < δ := hDy
  calc
    edist (D.pt (y : ℂ)) (D.pt x0) =
        edist (D.pt x0) (D.pt (y : ℂ)) := edist_comm _ _
    _ < δ := hDy'

 

theorem curve_back_all_continuous (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ q : ℂ × ℂ, E q = weylScale ξ g D q)
    {P : ℝ → ℂ} {a b : ℝ} (hP : E.IsCurve P a b) :
    D.IsCurve P a b := by
  refine ⟨hP.1, ?_⟩
  exact (continuous_weyl_back D E ξ hξ g hforget hWeyl).comp_continuousOn hP.2

 

theorem length_eq_of_zero_trace_all (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ q : ℂ × ℂ, E q = weylScale ξ g D q)
    {P : ℝ → ℂ} {a b : ℝ} (hP : E.IsCurve P a b)
    (hzero : ∀ t ∈ Icc a b, g (P t) = 0) :
    E.len P a b = D.len P a b := by
  have hPD := curve_back_all_continuous D E ξ hξ g hforget hWeyl hP
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

 

theorem off_bump_subinterval_time_all (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ q : ℂ × ℂ, E q = weylScale ξ (-f) D q)
    {P : ℝ → ℂ} {T a b : ℝ} (hP : E.IsCurve P 0 T)
    (hu : HasUnitSpeedOn (E.pt ∘ P) (Icc 0 T))
    (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b)
    (hzero : ∀ t ∈ Icc a b, f (P t) = 0) :
    D.IsCurve P a b ∧ D.len P a b = ENNReal.ofReal (b - a) := by
  have hPE : E.IsCurve P a b :=
    ⟨hab, hP.2.mono (Icc_subset_Icc ha.1 hb.2)⟩
  have hPD := curve_back_all_continuous D E ξ hξ (-f) hforget hWeyl hPE
  have heq := length_eq_of_zero_trace_all D E ξ hξ (-f)
    hforget hWeyl hPE (by intro t ht; simpa using congrArg Neg.neg (hzero t ht))
  have htime : E.len P a b = ENNReal.ofReal (b - a) := by
    rw [E.len_eq_curveLength]
    exact LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hu ha hb
  exact ⟨hPD, heq.symm.trans htime⟩

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift
