import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableCountableBuffers

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem internal_eq_iInf_lowerNeighborhoodObservable_of_smallAnnulusCosts
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, FinitePathsEuclideanContinuous (G n))
    (hforget : ∀ n, Continuous (PfeWeyl.euclidForget (G n)))
    (hDforget : Continuous (PfeWeyl.euclidForget D))
    {U : Set ℂ} (H : CompactExhaustion U) (x y : U)
    (W V : ℕ → Set ℂ)
    (hgeo : ∀ n,
      IsOpen (W n) ∧ IsCompact (closure (W n)) ∧
      closure (W n) ⊆ U ∧
      (H n).image Subtype.val ⊆ W n ∧
      (x : ℂ) ∈ W n ∧ (y : ℂ) ∈ W n ∧
      IsOpen (V n) ∧ IsCompact (closure (V n)) ∧
      closure (V n) ⊆ U ∧ closure (W n) ⊆ V n ∧
      IsCompact (frontier (V n)) ∧
      (frontier (V n)).Nonempty ∧
      Disjoint (closure (W n)) (frontier (V n)))
    (hsmall : ∀ n, PfeWeyl.SmallAnnulusCosts G D (closure (W n)) (V n)) :
    D.internal U (x, y) =
      ⨅ n : ℕ, lowerNeighborhoodObservable G (V n)
        ⟨(x : ℂ),
          (hgeo n).2.2.2.2.2.2.2.2.2.1
            (subset_closure (hgeo n).2.2.2.2.1)⟩
        ⟨(y : ℂ),
          (hgeo n).2.2.2.2.2.2.2.2.2.1
            (subset_closure (hgeo n).2.2.2.2.2.1)⟩ := by
  have hxW : ∀ n, (x : ℂ) ∈ W n := fun n => (hgeo n).2.2.2.2.1
  have hyW : ∀ n, (y : ℂ) ∈ W n := fun n => (hgeo n).2.2.2.2.2.1
  have hWV : ∀ n, W n ⊆ V n :=
    fun n => subset_closure.trans (hgeo n).2.2.2.2.2.2.2.2.2.1
  have hcof := internal_eq_iInf_inner_buffers D hDforget H x y W
    (fun n => (hgeo n).2.2.2.1)
    (fun n => subset_closure.trans (hgeo n).2.2.1)
    hxW hyW
  have hsand : ∀ n,
      D.internal U (x, y) ≤
        lowerNeighborhoodObservable G (V n)
          ⟨(x : ℂ), hWV n (hxW n)⟩
          ⟨(y : ℂ), hWV n (hyW n)⟩ ∧
      lowerNeighborhoodObservable G (V n)
          ⟨(x : ℂ), hWV n (hxW n)⟩
          ⟨(y : ℂ), hWV n (hyW n)⟩ ≤
        D.internal (W n)
          (⟨(x : ℂ), hxW n⟩, ⟨(y : ℂ), hyW n⟩) := by
    intro n
    rcases hgeo n with
      ⟨hWopen, hK, hKU, hHW, hx, hy, hVopen, hKout,
        hKoutU, hKV, hfront, hneFront, hdisj⟩
    have hWK : W n ⊆ interior (closure (W n)) :=
      interior_maximal subset_closure hWopen
    simpa only using buffered_neighborhood_observable_sandwich
      hG hLen hPath hforget (hWV n) hWK
      subset_closure hKout hKoutU hVopen hK
      hfront hneFront hdisj
      (hsmall n)
      ⟨(x : ℂ), hxW n⟩ ⟨(y : ℂ), hyW n⟩
  apply le_antisymm
  · exact le_iInf fun n => (hsand n).1
  · calc
      (⨅ n : ℕ, lowerNeighborhoodObservable G (V n)
          ⟨(x : ℂ), hWV n (hxW n)⟩
          ⟨(y : ℂ), hWV n (hyW n)⟩) ≤
          ⨅ n : ℕ, D.internal (W n)
            (⟨(x : ℂ), hxW n⟩, ⟨(y : ℂ), hyW n⟩) :=
        iInf_mono fun n => (hsand n).2
      _ = D.internal U (x, y) := hcof.symm

end SupercriticalLQGUniqueness.B2.PfeAxioms
