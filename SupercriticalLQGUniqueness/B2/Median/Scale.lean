import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.AroundTranslate

 






set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

open Uniqueness.Toolkit.CompactPathInfimum

theorem compactPathInf_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y))
    (K A B : Set ℂ) :
    compactPathInf E K A B = c * compactPathInf D K A B := by
  unfold compactPathInf
  simp only [Uniqueness.Positivity.Witnesses.isCurve_iff_of_dist_scale
      D E c hc0 hcTop hscale,
    Uniqueness.Positivity.Witnesses.len_eq_mul_of_dist_scale D E c hscale]
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]

private theorem len_translate (D E : LSCMetric) (z : ℂ)
    (hDE : ∀ x y : ℂ, E (x, y) = D (x + z, y + z))
    (P : ℝ → ℂ) (a b : ℝ) :
    E.len P a b = D.len (fun t => P t + z) a b := by
  unfold LSCMetric.len
  have h := LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
    (F := E.pt ∘ P) (G := D.pt ∘ fun t => P t + z) (c := (1 : ℝ≥0∞))
    (fun s t => by
      change E (P s, P t) = 1 * D (P s + z, P t + z)
      simp only [one_mul, hDE]) (Icc a b)
  simpa only [one_mul] using h

private theorem isCurve_translate (D E : LSCMetric) (z : ℂ)
    (hDE : ∀ x y : ℂ, E (x, y) = D (x + z, y + z))
    (P : ℝ → ℂ) (a b : ℝ) :
    E.IsCurve P a b ↔ D.IsCurve (fun t => P t + z) a b := by
  constructor
  · rintro ⟨hab, hP⟩
    refine ⟨hab, ?_⟩
    intro t ht
    have hlim := tendsto_iff_edist_tendsto_0.mp (hP t ht)
    apply tendsto_iff_edist_tendsto_0.mpr
    change Filter.Tendsto (fun s => D (P s + z, P t + z))
      (𝓝[Icc a b] t) (𝓝 0)
    change Filter.Tendsto (fun s => E (P s, P t))
      (𝓝[Icc a b] t) (𝓝 0) at hlim
    simpa only [hDE] using hlim
  · rintro ⟨hab, hP⟩
    refine ⟨hab, ?_⟩
    intro t ht
    have hlim := tendsto_iff_edist_tendsto_0.mp (hP t ht)
    apply tendsto_iff_edist_tendsto_0.mpr
    change Filter.Tendsto (fun s => E (P s, P t))
      (𝓝[Icc a b] t) (𝓝 0)
    change Filter.Tendsto (fun s => D (P s + z, P t + z))
      (𝓝[Icc a b] t) (𝓝 0) at hlim
    simpa only [hDE] using hlim

theorem compactPathInf_le_of_curve (d : LSCMetric) (K A B : Set ℂ)
    (P : ℝ → ℂ) (a b : ℝ) (hP : d.IsCurve P a b)
    (hK : ∀ t ∈ Icc a b, P t ∈ K) (hA : P a ∈ A) (hB : P b ∈ B) :
    compactPathInf d K A B ≤ d.len P a b := by
  unfold compactPathInf
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hP <| iInf_le_of_le hK <|
    iInf_le_of_le hA <| iInf_le_of_le hB le_rfl

private def shiftSet (z : ℂ) (K : Set ℂ) : Set ℂ := (fun x => x + z) '' K

 



theorem compactPathInf_translate (D E : LSCMetric) (z : ℂ)
    (hDE : ∀ x y : ℂ, E (x, y) = D (x + z, y + z))
    (K A B : Set ℂ) :
    compactPathInf E K A B =
      compactPathInf D (shiftSet z K) (shiftSet z A) (shiftSet z B) := by
  apply le_antisymm
  · refine le_iInf fun Q => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hQ => le_iInf fun hK => le_iInf fun hA =>
      le_iInf fun hB => ?_
    let P : ℝ → ℂ := fun t => Q t - z
    have hP : E.IsCurve P a b := by
      apply (isCurve_translate D E z hDE P a b).mpr
      simpa only [P, sub_add_cancel] using hQ
    have hPK : ∀ t ∈ Icc a b, P t ∈ K := by
      intro t ht
      obtain ⟨x, hx, hxt⟩ := hK t ht
      change Q t - z ∈ K
      have : x = Q t - z := by
        apply add_right_cancel (b := z)
        simpa only [sub_add_cancel] using hxt
      simpa only [← this] using hx
    have hPA : P a ∈ A := by
      obtain ⟨x, hx, hxa⟩ := hA
      have : x = Q a - z := by
        apply add_right_cancel (b := z)
        simpa only [sub_add_cancel] using hxa
      simpa only [P, ← this] using hx
    have hPB : P b ∈ B := by
      obtain ⟨x, hx, hxb⟩ := hB
      have : x = Q b - z := by
        apply add_right_cancel (b := z)
        simpa only [sub_add_cancel] using hxb
      simpa only [P, ← this] using hx
    calc
      compactPathInf E K A B ≤ E.len P a b :=
        compactPathInf_le_of_curve E K A B P a b hP hPK hPA hPB
      _ = D.len Q a b := by
        rw [len_translate D E z hDE P a b]
        simp only [P, sub_add_cancel]
  · refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hK => le_iInf fun hA =>
      le_iInf fun hB => ?_
    let Q : ℝ → ℂ := fun t => P t + z
    have hQ : D.IsCurve Q a b := (isCurve_translate D E z hDE P a b).mp hP
    have hQK : ∀ t ∈ Icc a b, Q t ∈ shiftSet z K := by
      intro t ht
      exact ⟨P t, hK t ht, rfl⟩
    have hQA : Q a ∈ shiftSet z A := ⟨P a, hA, rfl⟩
    have hQB : Q b ∈ shiftSet z B := ⟨P b, hB, rfl⟩
    calc
      compactPathInf D (shiftSet z K) (shiftSet z A) (shiftSet z B)
          ≤ D.len Q a b := compactPathInf_le_of_curve D _ _ _ Q a b hQ hQK hQA hQB
      _ = E.len P a b := (len_translate D E z hDE P a b).symm

end SupercriticalLQGUniqueness.B2.Median
