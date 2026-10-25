import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.ShieldCost
import SupercriticalLQGUniqueness.Uniqueness.Objects.Blocks.Shield




 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

theorem internal_le_len_curve (D : LSCMetric) (W : Set ℂ)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b)
    (htrace : ∀ s ∈ Icc a b, P s ∈ W) :
    D.internal W (⟨P a, htrace a ⟨le_rfl, hP.1⟩⟩,
      ⟨P b, htrace b ⟨hP.1, le_rfl⟩⟩) ≤ D.len P a b := by
  unfold LSCMetric.internal
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hP <| iInf_le_of_le htrace <|
    iInf_le_of_le rfl <| iInf_le_of_le rfl le_rfl

theorem isCurve_subinterval (D : LSCMetric) (P : ℝ → ℂ)
    {a b s t : ℝ} (hP : D.IsCurve P a b)
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    D.IsCurve P s t :=
  ⟨hst, hP.2.mono (Icc_subset_Icc has htb)⟩

theorem len_subinterval_le (D : LSCMetric) (P : ℝ → ℂ)
    {a b s t : ℝ} (has : a ≤ s) (_hst : s ≤ t) (htb : t ≤ b) :
    D.len P s t ≤ D.len P a b := by
  exact LQGMetric.MetricGeometry.curveLength_mono (D.pt ∘ P) has htb

 

theorem internal_le_loop_length (D : LSCMetric) (W : Set ℂ)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b)
    (htrace : ∀ s ∈ Icc a b, P s ∈ W)
    {σ τ : ℝ} (hσ : σ ∈ Icc a b) (hτ : τ ∈ Icc a b) :
    D.internal W (⟨P σ, htrace σ hσ⟩, ⟨P τ, htrace τ hτ⟩) ≤
      D.len P a b := by
  rcases le_total σ τ with hστ | hτσ
  · have hsub := isCurve_subinterval D P hP hσ.1 hστ hτ.2
    have htr : ∀ s ∈ Icc σ τ, P s ∈ W :=
      fun s hs => htrace s ⟨hσ.1.trans hs.1, hs.2.trans hτ.2⟩
    exact (internal_le_len_curve D W P σ τ hsub htr).trans
      (len_subinterval_le D P hσ.1 hστ hτ.2)
  · have hsub := isCurve_subinterval D P hP hτ.1 hτσ hσ.2
    have htr : ∀ s ∈ Icc τ σ, P s ∈ W :=
      fun s hs => htrace s ⟨hτ.1.trans hs.1, hs.2.trans hσ.2⟩
    have hsym := (D.isExtMetric_internal W).2.2.1
      (⟨P σ, htrace σ hσ⟩ : W) (⟨P τ, htrace τ hτ⟩ : W)
    rw [hsym]
    exact (internal_le_len_curve D W P τ σ hsub htr).trans
      (len_subinterval_le D P hτ.1 hτσ hσ.2)

theorem three_costs {X : Type*} (d : X × X → ENNReal)
    (hd : IsExtMetric d) (x a b y : X) (A B C : ENNReal)
    (hA : d (x, a) ≤ A) (hB : d (a, b) ≤ B) (hC : d (b, y) ≤ C) :
    d (x, y) ≤ A + B + C := by
  have ht₁ := hd.2.2.2 x a y
  have ht₂ := hd.2.2.2 a b y
  calc
    d (x, y) ≤ d (x, a) + d (a, y) := ht₁
    _ ≤ d (x, a) + (d (a, b) + d (b, y)) :=
      add_le_add le_rfl ht₂
    _ ≤ A + (B + C) := add_le_add hA (add_le_add hB hC)
    _ = A + B + C := (add_assoc _ _ _).symm

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
