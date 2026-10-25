import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.EA8




 














set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 
theorem weyl_len_eq_gen (ξ : ℝ) (g : C(ℂ, ℝ)) (D Db : LSCMetric)
    (hW : ∀ x y : ℂ, Db (x, y) = weylScale ξ g D (x, y)) (Q : ℝ → ℂ) (a b : ℝ) :
    HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ g D (BiLipschitz.Barrier.forget D x, BiLipschitz.Barrier.forget D y))
        (D.pt ∘ Q) a b = Db.len Q a b := by
  have hδ : (fun x y : D.Space => weylScale ξ g D (BiLipschitz.Barrier.forget D x, BiLipschitz.Barrier.forget D y)) =
      (fun x y : D.Space => Db (x, y)) := by
    funext x y
    exact (hW x y).symm
  rw [hδ, Db.len_eq_curveLength]
  exact HigherDimLQGMetric.curveLengthWith_edist (Db.pt ∘ Q) a b

 

theorem bumped_len_le_of_le (ξ : ℝ) (g : C(ℂ, ℝ)) (D Dt Db Dtb : LSCMetric)
    (hfD : Continuous (BiLipschitz.Barrier.forget D)) (hfDt : Continuous (BiLipschitz.Barrier.forget Dt))
    (hWD : ∀ x y : ℂ, Db (x, y) = weylScale ξ g D (x, y))
    (hWDt : ∀ x y : ℂ, Dtb (x, y) = weylScale ξ g Dt (x, y))
    {K : ℝ≥0∞} (hK : K ≠ ⊤) (hle : ∀ x y : ℂ, Dt (x, y) ≤ K * D (x, y))
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) :
    Dtb.len P a b ≤ K * Db.len P a b := by
  have hPt : Dt.IsCurve P a b := Objects.ProducerBlocks.isCurve_of_le D Dt hK hle hP
  rw [← weyl_len_eq_gen ξ g D Db hWD, ← weyl_len_eq_gen ξ g Dt Dtb hWDt]
  rw [show HigherDimLQGMetric.curveLengthWith
      (fun x y : D.Space => weylScale ξ g D (BiLipschitz.Barrier.forget D x, BiLipschitz.Barrier.forget D y)) (D.pt ∘ P) a b = _
      from Toolkit.WeylLength.weylCurveLength_eq_weightedLength D ξ g hfD hP,
    show HigherDimLQGMetric.curveLengthWith
      (fun x y : Dt.Space => weylScale ξ g Dt (BiLipschitz.Barrier.forget Dt x, BiLipschitz.Barrier.forget Dt y)) (Dt.pt ∘ P) a b = _
      from Toolkit.WeylLength.weylCurveLength_eq_weightedLength Dt ξ g hfDt hPt]
  rw [← HigherDimLQGMetric.weightedLengthWith_edist]
  exact (HigherDimLQGMetric.weightedLengthWith_compare (X := D.Space) (U := univ)
    (E := fun x y : D.Space => Dt (BiLipschitz.Barrier.forget D x, BiLipschitz.Barrier.forget D y)) (m := 0) (M := K)
    (fun _ _ _ _ => by simp) (fun x _ y _ => hle x y) (fun _ _ => mem_univ _)).2

 


theorem blb (C : Objects.CorrectedEvent.Constants) (D Dt Db Dtb : LSCMetric) (f : C(ℂ, ℝ))
    (hLDt : Dt.IsLengthSpace) (hfD : Continuous (BiLipschitz.Barrier.forget D)) (hfDt : Continuous (BiLipschitz.Barrier.forget Dt))
    (hWD : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hWDt : ∀ x y : ℂ, Dtb (x, y) = weylScale C.ξ (-f) Dt (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {K : ℝ≥0∞} (hK0 : K ≠ 0) (hK : K ≠ ⊤) (hle : ∀ x y : ℂ, Dt (x, y) ≤ K * D (x, y))
    (W : Set ℂ) (p : W × W) : Dtb.internal W p ≤ K * Db.internal W p := by
  refine Objects.ProducerBlocks.internal_le_of_curves Db Dtb hK0 hK W (fun P a b hP => ?_) (fun P a b hP => ?_) p
  · have hPD : D.IsCurve P a b := Objects.Splice.bumped_curve_transfer_back C D Db f hfD hWD hf hP
    have hPDt : Dt.IsCurve P a b := Objects.ProducerBlocks.isCurve_of_le D Dt hK hle hPD
    exact Objects.Splice.bumped_curve_transfer C Dt Dtb f hfDt hWDt hf hLDt hPDt
  · have hPD : D.IsCurve P a b := Objects.Splice.bumped_curve_transfer_back C D Db f hfD hWD hf hP
    exact bumped_len_le_of_le C.ξ (-f) D Dt Db Dtb hfD hfDt hWD hWDt hK hle hPD

 
theorem internal_anti (D : LSCMetric) {Y Z : Set ℂ} (hYZ : Y ⊆ Z) {x y : ℂ} (hx : x ∈ Y)
    (hy : y ∈ Y) :
    D.internal Z (⟨x, hYZ hx⟩, ⟨y, hYZ hy⟩) ≤ D.internal Y (⟨x, hx⟩, ⟨y, hy⟩) := by
  rw [LSCMetric.internal_eq_internalEDist, LSCMetric.internal_eq_internalEDist]
  exact LQGMetric.MetricGeometry.internalEDist_anti (image_mono hYZ) _ _

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
