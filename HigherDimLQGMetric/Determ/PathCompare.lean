import HigherDimLQGMetric.Determ.PathGrid

/-!
# Path lengths from internal metrics on an open set

The curve-length comparison is dimension independent; this file adapts the
2D `T1_7V1` argument to the `Rd d` metric type.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {d : ℕ}

theorem determ_len_eq_of_internal_eq {D₁ D₂ : ContMetric d} {S : Set (Rd d)}
    (hS : ∀ u ∈ S, ∀ v ∈ S, D₁.internal S u v = D₂.internal S u v)
    {P : ℝ → Rd d} {x y : ℝ} (hP : ContinuousOn P (Icc x y))
    (hPS : MapsTo P (Icc x y) S) :
    D₁.len P x y = D₂.len P x y := by
  have h1 := curveLength_eq_iSup_internalEDist (X := D₁.Space) (Y := D₁.pt '' S)
    (P := D₁.pt ∘ P) (D₁.continuous_pt.comp_continuousOn hP)
    (fun t ht => ⟨P t, hPS ht, rfl⟩)
  have h2 := curveLength_eq_iSup_internalEDist (X := D₂.Space) (Y := D₂.pt '' S)
    (P := D₂.pt ∘ P) (D₂.continuous_pt.comp_continuousOn hP)
    (fun t ht => ⟨P t, hPS ht, rfl⟩)
  unfold ContMetric.len
  rw [h1, h2]
  exact iSup_congr fun p => Finset.sum_congr rfl fun i _ =>
    hS _ (hPS (p.2.2.2 _)) _ (hPS (p.2.2.2 _))

/-- Equal internal metrics on an open cell give equal length measures of the
part of any finite-length curve inside that cell. -/
theorem determ_lenMeas_eq_of_internal_eq {D₁ D₂ : ContMetric d}
    {S : Set (Rd d)} (hSo : IsOpen S)
    (hS : ∀ u ∈ S, ∀ v ∈ S, D₁.internal S u v = D₂.internal S u v)
    {P : ℝ → Rd d} {a b : ℝ} (hP : ContinuousOn P (Icc a b))
    (h₁ : LQGMetric.LM.T17Curve (D₁.pt ∘ P) a b)
    (h₂ : LQGMetric.LM.T17Curve (D₂.pt ∘ P) a b) :
    LQGMetric.LM.t17LenMeas (D₁.pt ∘ P) a b (Icc a b ∩ P ⁻¹' S) =
      LQGMetric.LM.t17LenMeas (D₂.pt ∘ P) a b (Icc a b ∩ P ⁻¹' S) := by
  let O := Ioo a b ∩ P ⁻¹' S
  have hO : IsOpen O :=
    (hP.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo hSo
  have heq := LQGMetric.LM.t17LenMeas_eq_on_open h₁ h₂ hO inter_subset_left
    (fun x y _ hsub => determ_len_eq_of_internal_eq hS
      (hP.mono (hsub.trans (inter_subset_left.trans Ioo_subset_Icc_self)))
      (fun t ht => (hsub ht).2))
  have key : ∀ μ : Measure ℝ, μ {a} = 0 → μ {b} = 0 →
      μ (Icc a b ∩ P ⁻¹' S) = μ O := by
    intro μ ha hb
    refine le_antisymm ?_ (measure_mono (inter_subset_inter_left _ Ioo_subset_Icc_self))
    have hsub : Icc a b ∩ P ⁻¹' S ⊆ O ∪ ({a} ∪ {b}) := by
      rintro t ⟨⟨h1, h2⟩, h3⟩
      rcases h1.lt_or_eq with h1 | h1
      · rcases h2.lt_or_eq with h2 | h2
        · exact Or.inl ⟨⟨h1, h2⟩, h3⟩
        · exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl h1.symm)
    calc μ (Icc a b ∩ P ⁻¹' S) ≤ μ (O ∪ ({a} ∪ {b})) := measure_mono hsub
      _ ≤ μ O + μ ({a} ∪ {b}) := measure_union_le _ _
      _ ≤ μ O + (μ {a} + μ {b}) := add_le_add le_rfl (measure_union_le _ _)
      _ = μ O := by rw [ha, hb, add_zero, add_zero]
  rw [key _ (LQGMetric.LM.t17v_lenMeas_singleton _ _ _ _)
      (LQGMetric.LM.t17v_lenMeas_singleton _ _ _ _),
    key _ (LQGMetric.LM.t17v_lenMeas_singleton _ _ _ _)
      (LQGMetric.LM.t17v_lenMeas_singleton _ _ _ _), heq]

end HigherDimLQGMetric
