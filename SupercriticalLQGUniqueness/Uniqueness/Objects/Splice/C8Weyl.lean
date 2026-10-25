import SupercriticalLQGUniqueness.Uniqueness.Objects.Splice.C8Measure
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylLength.WeylLength



 
set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Splice

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

 

theorem bumped_length_bounds
    (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) :
    ENNReal.ofReal (Real.exp (-C.ξ*C.A_max)) * D.len P a b ≤
      Db.len P a b ∧ Db.len P a b ≤ D.len P a b := by
  have hδ : (fun x y : D.Space => weylScale C.ξ (-f) D (x, y)) =
      (fun x y : D.Space => Db (x, y)) := by
    funext x y
    exact (hWeyl x y).symm
  have hDb : Db.len P a b =
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => Db (x, y)) (D.pt ∘ P) a b := by
    rw [Db.len_eq_curveLength]
    exact (HigherDimLQGMetric.curveLengthWith_edist (Db.pt ∘ P) a b).symm
  have hlo : ∀ t ∈ Icc a b, -C.A_max ≤ (-f) (P t) := by
    intro t ht
    simpa using neg_le_neg (hf (P t)).2
  have hhi : ∀ t ∈ Icc a b, (-f) (P t) ≤ 0 := by
    intro t ht
    simpa using neg_nonpos.mpr (hf (P t)).1
  have h := Toolkit.WeylLength.weylCurveLength_factor_bounds D C.ξ C.ξPos.le
    (-f) hforget hP (-C.A_max) 0 hlo hhi
  change ENNReal.ofReal (Real.exp (C.ξ * -C.A_max)) * D.len P a b ≤
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale C.ξ (-f) D (x, y))
        (D.pt ∘ P) a b ∧
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale C.ξ (-f) D (x, y))
        (D.pt ∘ P) a b ≤
      ENNReal.ofReal (Real.exp (C.ξ * 0)) * D.len P a b at h
  rw [hδ, ← hDb] at h
  have hexp : C.ξ * -C.A_max = -C.ξ * C.A_max := by ring
  simpa only [hexp, mul_zero, Real.exp_zero, ENNReal.ofReal_one,
    one_mul] using h

 

theorem bumped_distance_le
    (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    (hLength : D.IsLengthSpace) (x y : ℂ) : Db (x, y) ≤ D (x, y) := by
  rw [(LSCMetric.isLengthSpace_iff_eq_iInf D).mp hLength x y]
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
  rw [hWeyl, ← hPa, ← hPb, Toolkit.WeylLength.weylScale_eq_weylDistOn D C.ξ (-f) hforget]
  let w : D.Space → ℝ := fun z => Real.exp (C.ξ * (-f z))
  have hw : HigherDimLQGMetric.weylDistOn w Set.univ (D.pt (P a)) (D.pt (P b)) ≤
      HigherDimLQGMetric.weightedLength w (D.pt ∘ P) a b := by
    exact HigherDimLQGMetric.weylDistOn_le_of_curve hP.1 hP.2
      (fun _ _ => Set.mem_univ _)
  have hwl := Toolkit.WeylLength.weylCurveLength_eq_weightedLength D C.ξ (-f) hforget hP
  have hδ : (fun u v : D.Space => weylScale C.ξ (-f) D (u, v)) =
      (fun u v : D.Space => Db (u, v)) := by
    funext u v
    exact (hWeyl u v).symm
  have hDb : Db.len P a b =
      HigherDimLQGMetric.curveLengthWith
        (fun u v : D.Space => Db (u, v)) (D.pt ∘ P) a b := by
    rw [Db.len_eq_curveLength]
    exact (HigherDimLQGMetric.curveLengthWith_edist (Db.pt ∘ P) a b).symm
  have hbound := (bumped_length_bounds C D Db f hforget hWeyl hf hP).2
  change HigherDimLQGMetric.weylDistOn w Set.univ (D.pt (P a)) (D.pt (P b)) ≤ D.len P a b
  calc
    _ ≤ HigherDimLQGMetric.weightedLength w (D.pt ∘ P) a b := hw
    _ = Db.len P a b := by
      change HigherDimLQGMetric.curveLengthWith
        (fun u v : D.Space => weylScale C.ξ (-f) D (u, v))
        (D.pt ∘ P) a b =
        HigherDimLQGMetric.weightedLength w (D.pt ∘ P) a b at hwl
      rw [hδ, ← hDb] at hwl
      exact hwl.symm
    _ ≤ D.len P a b := hbound

 

theorem bumped_distance_lower
    (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    (x y : ℂ) :
    ENNReal.ofReal (Real.exp (-C.ξ*C.A_max)) * D (x, y) ≤ Db (x, y) := by
  rw [hWeyl, Toolkit.WeylLength.weylScale_eq_weylDistOn D C.ξ (-f) hforget]
  let w : D.Space → ℝ := fun z => Real.exp (C.ξ * (-f z))
  have hm : ∀ z ∈ (Set.univ : Set D.Space),
      edist (D.pt x) z ≤ (⊤ : ENNReal) →
      Real.exp (-C.ξ*C.A_max) ≤ w z := by
    intro z hz hzdist
    apply Real.exp_le_exp.mpr
    have hneg : -C.A_max ≤ -f z := neg_le_neg (hf z).2
    nlinarith [mul_nonneg C.ξPos.le (sub_nonneg.mpr hneg)]
  have h := HigherDimLQGMetric.weylDistOn_ge_min
    (U := Set.univ) (w := w) (x := D.pt x) (R := ⊤) hm (D.pt y)
  change ENNReal.ofReal (Real.exp (-C.ξ*C.A_max)) *
      edist (D.pt x) (D.pt y) ≤
      HigherDimLQGMetric.weylDistOn w Set.univ (D.pt x) (D.pt y)
  simpa only [min_top_right] using h

 

theorem curve_transfer_of_distance_le (D Db : LSCMetric)
    (hcomp : ∀ x y : ℂ, Db (x, y) ≤ D (x, y))
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) : Db.IsCurve P a b := by
  let F : D.Space → Db.Space := id
  have hLip : LipschitzWith 1 F := LipschitzWith.of_edist_le (by
    intro x y
    exact hcomp x y)
  refine ⟨hP.1, ?_⟩
  change ContinuousOn (F ∘ (D.pt ∘ P)) (Icc a b)
  exact hLip.continuous.comp_continuousOn hP.2

 

theorem bumped_curve_transfer
    (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    (hLength : D.IsLengthSpace)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) : Db.IsCurve P a b :=
  curve_transfer_of_distance_le D Db
    (bumped_distance_le C D Db f hforget hWeyl hf hLength) hP

 

theorem bumped_curve_transfer_back
    (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {P : ℝ → ℂ} {a b : ℝ} (hP : Db.IsCurve P a b) : D.IsCurve P a b := by
  let K : NNReal := ⟨Real.exp (C.ξ*C.A_max), (Real.exp_pos _).le⟩
  have hKc : (K : ENNReal) * ENNReal.ofReal (Real.exp (-C.ξ*C.A_max)) = 1 := by
    have hK : (K : ENNReal) = ENNReal.ofReal (Real.exp (C.ξ*C.A_max)) := by
      have hKr : (K : ℝ) = Real.exp (C.ξ*C.A_max) := rfl
      rw [← hKr, ENNReal.ofReal_coe_nnreal]
    rw [hK]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    have he : Real.exp (C.ξ*C.A_max) * Real.exp (-C.ξ*C.A_max) = 1 := by
      rw [show -C.ξ*C.A_max = -(C.ξ*C.A_max) by ring,
        Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero _)]
    rw [he, ENNReal.ofReal_one]
  have hcomp (x y : ℂ) : D (x, y) ≤ (K : ENNReal) * Db (x, y) := by
    have hlower := bumped_distance_lower C D Db f hforget hWeyl hf x y
    calc
      D (x, y) = 1 * D (x, y) := (one_mul _).symm
      _ = ((K : ENNReal) * ENNReal.ofReal (Real.exp (-C.ξ*C.A_max))) *
          D (x, y) := by rw [hKc]
      _ = (K : ENNReal) *
          (ENNReal.ofReal (Real.exp (-C.ξ*C.A_max)) * D (x, y)) := mul_assoc _ _ _
      _ ≤ (K : ENNReal) * Db (x, y) := by gcongr
  let F : Db.Space → D.Space := id
  have hLip : LipschitzWith K F := by
    intro x y
    exact hcomp x y
  refine ⟨hP.1, ?_⟩
  change ContinuousOn (F ∘ (Db.pt ∘ P)) (Icc a b)
  exact hLip.continuous.comp_continuousOn hP.2

end SupercriticalLQGUniqueness.Uniqueness.Objects.Splice
