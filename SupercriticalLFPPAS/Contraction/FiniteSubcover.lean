import SupercriticalLFPPAS.Contraction.IntervalCover

/-! The open interval cover along a compact geodesic-time segment has a finite subcover. -/

set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLFPPAS.Contraction

/-- A pointwise family of open time intervals covering `[a,b]` admits a finite subfamily.
The returned finset is of interval values, so duplicate intervals are harmless; each of its
members is the interval of some time of `[a, b]`. -/
theorem d4_finite_interval_subcover {a b : ℝ} (I : ℝ → D4Interval)
    (hgood : ∀ t ∈ Icc a b,
      (I t).1 < (I t).2 ∧ t ∈ Ioo (I t).1 (I t).2) :
    ∃ F : Finset D4Interval,
      (∀ J ∈ F, J.1 < J.2) ∧
      (∀ J ∈ F, (Ioo J.1 J.2 ∩ Icc a b).Nonempty) ∧
      Icc a b ⊆ ⋃ J ∈ F, Ioo J.1 J.2 ∧
      (∀ J ∈ F, ∃ t ∈ Icc a b, J = I t) := by
  classical
  let T := {t : ℝ // t ∈ Icc a b}
  let U : T → Set ℝ := fun t => Ioo (I t.1).1 (I t.1).2
  have hopen : ∀ t : T, IsOpen (U t) := fun t => isOpen_Ioo
  have hcover : (Icc a b : Set ℝ) ⊆ ⋃ t, U t := by
    intro x hx
    have hx' : x ∈ U ⟨x, hx⟩ := (hgood x hx).2
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hx'⟩
  obtain ⟨T₀, hT₀⟩ := isCompact_Icc.elim_finite_subcover U hopen hcover
  let F := T₀.image fun t : T => I t.1
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro J hJ
    obtain ⟨t, ht, hEq⟩ := Finset.mem_image.mp hJ
    subst J
    exact (hgood t.1 t.2).1
  · intro J hJ
    obtain ⟨t, ht, hEq⟩ := Finset.mem_image.mp hJ
    subst J
    exact ⟨t.1, (hgood t.1 t.2).2, t.2⟩
  · intro x hx
    obtain ⟨t, ht, hxU⟩ := Set.mem_iUnion₂.mp (hT₀ hx)
    apply Set.mem_iUnion₂.mpr
    refine ⟨I t.1, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
    exact hxU
  · intro J hJ
    obtain ⟨t, _, hEq⟩ := Finset.mem_image.mp hJ
    exact ⟨t.1, t.2, hEq.symm⟩

end SupercriticalLFPPAS.Contraction
