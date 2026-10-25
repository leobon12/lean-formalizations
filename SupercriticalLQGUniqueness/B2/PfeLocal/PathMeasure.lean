import SupercriticalLQGUniqueness.B2.PfeLocal.CirclePath
import SupercriticalLQGUniqueness.B2.PfeLocal.NonDawdleGeom
import LQGMetric.Papers.LM.T1_7G2

 





set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 

def pathLengthIn (D : LSCMetric) (P : ℝ → ℂ) (a b : ℝ) (S : Set ℂ) : ℝ≥0∞ :=
  LQGMetric.LM.t17LenMeas (D.pt ∘ P) a b (P ⁻¹' S ∩ Icc a b)

 

theorem pathLengthIn_le_len (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ}
    (hP : D.IsCurve P a b) (hfin : D.len P a b ≠ ∞) (S : Set ℂ) :
    pathLengthIn D P a b S ≤ D.len P a b := by
  have hcurve : LQGMetric.LM.T17Curve (D.pt ∘ P) a b := ⟨hP.1, hP.2, hfin⟩
  exact LQGMetric.LM.t17LenMeas_le_of_subset hcurve le_rfl hP.1 le_rfl
    (by intro t ht; exact ht.2)

 

theorem pathLengthIn_mono (D : LSCMetric) (P : ℝ → ℂ) (a b : ℝ)
    {S T : Set ℂ} (hST : S ⊆ T) :
    pathLengthIn D P a b S ≤ pathLengthIn D P a b T := by
  unfold pathLengthIn
  apply MeasureTheory.measure_mono
  intro t ht
  exact ⟨hST ht.1, ht.2⟩

 


theorem pathLengthIn_le_prefix (D : LSCMetric) (P : ℝ → ℂ) {a s b : ℝ}
    (hP : D.IsCurve P a b) (hfin : D.len P a b ≠ ∞)
    (has : a ≤ s) (hsb : s ≤ b) (S : Set ℂ)
    (hvisit : ∀ t ∈ Icc a b, P t ∈ S → t ≤ s) :
    pathLengthIn D P a b S ≤ D.len P a s := by
  have hcurve : LQGMetric.LM.T17Curve (D.pt ∘ P) a b := ⟨hP.1, hP.2, hfin⟩
  exact LQGMetric.LM.t17LenMeas_le_of_subset hcurve le_rfl has hsb
    (by
      intro t ht
      exact ⟨ht.2.1, hvisit t ht.2 ht.1⟩)

 

theorem pathLengthIn_le_suffix (D : LSCMetric) (P : ℝ → ℂ) {a s b : ℝ}
    (hP : D.IsCurve P a b) (hfin : D.len P a b ≠ ∞)
    (has : a ≤ s) (hsb : s ≤ b) (S : Set ℂ)
    (hvisit : ∀ t ∈ Icc a b, P t ∈ S → s ≤ t) :
    pathLengthIn D P a b S ≤ D.len P s b := by
  have hcurve : LQGMetric.LM.T17Curve (D.pt ∘ P) a b := ⟨hP.1, hP.2, hfin⟩
  exact LQGMetric.LM.t17LenMeas_le_of_subset hcurve has hsb le_rfl
    (by
      intro t ht
      exact ⟨hvisit t ht.2 ht.1, ht.2.2⟩)

 


theorem near_endpoint_pathLengthIn_le_prefix (D : LSCMetric) (P : ℝ → ℂ)
    {a s b ε : ℝ} {y z : ℂ}
    (hP : D.IsCurve P a b) (hfin : D.len P a b ≠ ∞)
    (has : a ≤ s) (hsb : s ≤ b) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hz : z ∈ Metric.ball y (3 * ε))
    (hafter : ∀ t ∈ Icc a b, s < t → P t ∉ Metric.ball z (4 * ε)) :
    pathLengthIn D P a b (Metric.ball y (ε ^ 2 / 2)) ≤ D.len P a s := by
  apply pathLengthIn_le_prefix D P hP hfin has hsb
  intro t ht hsmall
  have hbig := near_endpoint_ball_subset hε hε1 hz hsmall
  exact le_of_not_gt fun hst => hafter t ht hst hbig

 

theorem near_endpoint_pathLengthIn_le_suffix (D : LSCMetric) (P : ℝ → ℂ)
    {a s b ε : ℝ} {y w : ℂ}
    (hP : D.IsCurve P a b) (hfin : D.len P a b ≠ ∞)
    (has : a ≤ s) (hsb : s ≤ b) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hw : w ∈ Metric.ball y (3 * ε))
    (hbefore : ∀ t ∈ Icc a b, t < s → P t ∉ Metric.ball w (4 * ε)) :
    pathLengthIn D P a b (Metric.ball y (ε ^ 2 / 2)) ≤ D.len P s b := by
  apply pathLengthIn_le_suffix D P hP hfin has hsb
  intro t ht hsmall
  have hbig := near_endpoint_ball_subset hε hε1 hw hsmall
  exact le_of_not_gt fun hts => hbefore t ht hts hbig

end SupercriticalLQGUniqueness.B2.PfeLocal
