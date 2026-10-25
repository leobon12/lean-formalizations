import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableCofinal

 







set_option autoImplicit false
noncomputable section

open Set Topology

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_countable_inner_internal_identity
    (D : LSCMetric)
    (hforget : Continuous (PfeWeyl.euclidForget D))
    {U : Set ℂ} (hU : IsOpen U) (x y : U) :
    ∃ W : ℕ → Set ℂ,
      ∃ hxW : ∀ n, (x : ℂ) ∈ W n,
        ∃ hyW : ∀ n, (y : ℂ) ∈ W n,
          (∀ n, IsOpen (W n) ∧ IsCompact (closure (W n)) ∧
            closure (W n) ⊆ U) ∧
          D.internal U (x, y) =
            ⨅ n : ℕ, D.internal (W n)
              (⟨(x : ℂ), hxW n⟩, ⟨(y : ℂ), hyW n⟩) := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  let H : CompactExhaustion U := CompactExhaustion.choice U
  obtain ⟨W, hW⟩ := exists_countable_open_buffers hU H x y
  have hxW : ∀ n, (x : ℂ) ∈ W n := fun n => (hW n).2.2.2.2.1
  have hyW : ∀ n, (y : ℂ) ∈ W n := fun n => (hW n).2.2.2.2.2
  refine ⟨W, hxW, hyW, ?_, ?_⟩
  · exact fun n => ⟨(hW n).1, (hW n).2.1, (hW n).2.2.1⟩
  · exact internal_eq_iInf_inner_buffers D hforget H x y W
      (fun n => (hW n).2.2.2.1)
      (fun n => subset_closure.trans (hW n).2.2.1)
      hxW hyW

end SupercriticalLQGUniqueness.B2.PfeAxioms
