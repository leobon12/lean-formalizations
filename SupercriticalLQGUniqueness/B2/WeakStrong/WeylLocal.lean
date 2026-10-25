import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylBridge
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Cor

 

















set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.WeakStrong

local notation "forgetD" => Uniqueness.BiLipschitz.Barrier.forget

 
theorem weyl_len_le (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (g : C(ℂ, ℝ))
    (hforget : Continuous (forgetD D)) (hW : ∀ p : ℂ × ℂ, E p = weylScale ξ g D p)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) (m M : ℝ)
    (hlo : ∀ s ∈ Icc a b, m ≤ g (P s)) (hhi : ∀ s ∈ Icc a b, g (P s) ≤ M) :
    E.len P a b ≤ ENNReal.ofReal (Real.exp (ξ * M)) * D.len P a b := by
  have hδ : (fun x y : D.Space => weylScale ξ g D (x, y)) =
      (fun x y : D.Space => E (x, y)) := by
    funext x y
    exact (hW (x, y)).symm
  have hE : E.len P a b =
      HigherDimLQGMetric.curveLengthWith (fun x y : D.Space => E (x, y)) (D.pt ∘ P) a b := by
    rw [E.len_eq_curveLength]
    exact (HigherDimLQGMetric.curveLengthWith_edist (E.pt ∘ P) a b).symm
  have h := (Uniqueness.Toolkit.WeylLength.weylCurveLength_factor_bounds D ξ hξ g hforget hP
    m M hlo hhi).2
  change HigherDimLQGMetric.curveLengthWith
      (fun x y : D.Space => weylScale ξ g D (x, y)) (D.pt ∘ P) a b ≤ _ at h
  rw [hδ, ← hE] at h
  exact h

 

theorem isCurve_of_weyl (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (g : C(ℂ, ℝ))
    (hforget : Continuous (forgetD D)) (hW : ∀ p : ℂ × ℂ, E p = weylScale ξ g D p)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) (hfin : D.len P a b ≠ ⊤) (m M : ℝ)
    (hlo : ∀ s ∈ Icc a b, m ≤ g (P s)) (hhi : ∀ s ∈ Icc a b, g (P s) ≤ M) :
    E.IsCurve P a b := by
  refine ⟨hP.1, fun x hx => ?_⟩
  have hbv : BoundedVariationOn (D.pt ∘ P) (Icc a b) := hfin
  have hcx : ContinuousWithinAt (D.pt ∘ P) (Icc a b) x := hP.2 x hx
  have hR := hbv.tendsto_eVariationOn_Icc_zero_right (hcx.mono inter_subset_left)
  have hL := hbv.tendsto_eVariationOn_Icc_zero_left (hcx.mono inter_subset_left)
  obtain ⟨C, hC⟩ : ∃ C, C = ENNReal.ofReal (Real.exp (ξ * M)) := ⟨_, rfl⟩
  have hsum : Tendsto (fun y => C * (eVariationOn (D.pt ∘ P) (Icc a b ∩ Icc x y) +
      eVariationOn (D.pt ∘ P) (Icc a b ∩ Icc y x))) (𝓝[Icc a b] x) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (hR.add hL) (Or.inr (by rw [hC]; exact ENNReal.ofReal_ne_top))
      (a := C)
    simpa using this
  have hsub : ∀ {s t : ℝ}, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      E (P s, P t) ≤ C * eVariationOn (D.pt ∘ P) (Icc a b ∩ Icc s t) := by
    intro s t hs ht hst
    have hsubset : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hPst : D.IsCurve P s t := ⟨hst, hP.2.mono hsubset⟩
    calc E (P s, P t) ≤ E.len P s t := LSCMetric.apply_le_len E P hst
      _ ≤ C * D.len P s t := hC ▸ weyl_len_le D E ξ hξ g hforget hW hPst m M
          (fun u hu => hlo u (hsubset hu)) (fun u hu => hhi u (hsubset hu))
      _ = C * eVariationOn (D.pt ∘ P) (Icc a b ∩ Icc s t) := by
          rw [inter_eq_right.2 hsubset]; rfl
  refine (tendsto_iff_edist_tendsto_0).2 (tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum (Eventually.of_forall fun _ => zero_le) ?_)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rcases le_total x y with hxy | hyx
  · calc edist ((E.pt ∘ P) y) ((E.pt ∘ P) x) = E (P x, P y) := edist_comm _ _
      _ ≤ C * eVariationOn (D.pt ∘ P) (Icc a b ∩ Icc x y) := hsub hx hy hxy
      _ ≤ _ := mul_le_mul_right le_self_add C
  · calc edist ((E.pt ∘ P) y) ((E.pt ∘ P) x) = E (P y, P x) := rfl
      _ ≤ C * eVariationOn (D.pt ∘ P) (Icc a b ∩ Icc y x) := hsub hy hx hyx
      _ ≤ _ := mul_le_mul_right le_add_self C

 
theorem weyl_curve_finite (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (g : C(ℂ, ℝ))
    (hforget : Continuous (forgetD D)) (hW : ∀ p : ℂ × ℂ, E p = weylScale ξ g D p)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) (hfin : D.len P a b < ⊤) :
    E.IsCurve P a b ∧ E.len P a b < ⊤ := by
  have hPc : ContinuousOn P (Icc a b) := hforget.comp_continuousOn hP.2
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (g.continuous.comp_continuousOn hPc)
  have hlo : ∀ s ∈ Icc a b, -B ≤ g (P s) := fun s hs => by
    have := hB s hs; rw [Real.norm_eq_abs] at this; exact (abs_le.1 this).1
  have hhi : ∀ s ∈ Icc a b, g (P s) ≤ B := fun s hs => by
    have := hB s hs; rw [Real.norm_eq_abs] at this; exact (abs_le.1 this).2
  refine ⟨isCurve_of_weyl D E ξ hξ g hforget hW hP hfin.ne _ _ hlo hhi, ?_⟩
  exact (weyl_len_le D E ξ hξ g hforget hW hP _ _ hlo hhi).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

end SupercriticalLQGUniqueness.B2.WeakStrong
