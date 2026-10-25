import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableBuffers

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem internal_eq_iInf_inner_buffers
    (D : LSCMetric)
    (hforget : Continuous (PfeWeyl.euclidForget D))
    {U : Set ℂ} (H : CompactExhaustion U) (x y : U)
    (W : ℕ → Set ℂ)
    (hHW : ∀ n, (H n).image Subtype.val ⊆ W n)
    (hWU : ∀ n, W n ⊆ U)
    (hxW : ∀ n, (x : ℂ) ∈ W n)
    (hyW : ∀ n, (y : ℂ) ∈ W n) :
    D.internal U (x, y) =
      ⨅ n : ℕ, D.internal (W n)
        (⟨(x : ℂ), hxW n⟩, ⟨(y : ℂ), hyW n⟩) := by
  have hcompact :=
    B2.PfeLocal.internal_eq_iInf_compactPathInf_of_forget D hforget H x y
  apply le_antisymm
  · refine le_iInf fun n => ?_
    rw [LSCMetric.internal_eq_internalEDist,
      LSCMetric.internal_eq_internalEDist]
    exact LQGMetric.MetricGeometry.internalEDist_anti
      (image_mono (hWU n)) _ _
  · calc
      (⨅ n : ℕ, D.internal (W n)
          (⟨(x : ℂ), hxW n⟩, ⟨(y : ℂ), hyW n⟩)) ≤
          ⨅ n : ℕ, Uniqueness.Toolkit.CompactPathInfimum.compactPathInf D
            ((H n).image Subtype.val) {(x : ℂ)} {(y : ℂ)} := by
        apply iInf_mono
        intro n
        unfold Uniqueness.Toolkit.CompactPathInfimum.compactPathInf
        refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
          le_iInf fun hP => le_iInf fun hK => le_iInf fun hE =>
          le_iInf fun hF => ?_
        have hW : ∀ t ∈ Icc a b, P t ∈ W n :=
          fun t ht => hHW n (hK t ht)
        have hx : P a = (x : ℂ) := Set.mem_singleton_iff.mp hE
        have hy : P b = (y : ℂ) := Set.mem_singleton_iff.mp hF
        unfold LSCMetric.internal
        exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
          iInf_le_of_le hP <| iInf_le_of_le hW <|
          iInf_le_of_le hx <| iInf_le_of_le hy le_rfl
      _ = D.internal U (x, y) := hcompact.symm

end SupercriticalLQGUniqueness.B2.PfeAxioms
