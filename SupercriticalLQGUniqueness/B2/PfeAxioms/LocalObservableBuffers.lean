import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableNeighborhood
import SupercriticalLQGUniqueness.B2.PfeLocal.OpenInternalBridge

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_open_compact_closure_buffer
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧
      IsCompact (closure W) ∧ closure W ⊆ U := by
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  have hO : IsOpen (U ∩ ball (0 : ℂ) R) := hU.inter isOpen_ball
  have hKO : K ⊆ U ∩ ball (0 : ℂ) R :=
    fun z hz => ⟨hKU hz, hKR hz⟩
  obtain ⟨W, hWopen, hKW, hcl⟩ :=
    hK.exists_isOpen_closure_subset (hO.mem_nhdsSet.mpr hKO)
  have hclB : closure W ⊆ closedBall (0 : ℂ) R :=
    (hcl.trans inter_subset_right).trans ball_subset_closedBall
  refine ⟨W, hWopen, hKW,
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) R)
      isClosed_closure hclB, hcl.trans inter_subset_left⟩

theorem exists_countable_open_buffers
    {U : Set ℂ} (hU : IsOpen U) (H : CompactExhaustion U)
    (x y : U) :
    ∃ W : ℕ → Set ℂ, ∀ n,
      IsOpen (W n) ∧ IsCompact (closure (W n)) ∧
      closure (W n) ⊆ U ∧
      (H n).image Subtype.val ⊆ W n ∧
      (x : ℂ) ∈ W n ∧ (y : ℂ) ∈ W n := by
  classical
  have hp : ∀ n : ℕ, ∃ W : Set ℂ,
      IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧
      (H n).image Subtype.val ⊆ W ∧
      (x : ℂ) ∈ W ∧ (y : ℂ) ∈ W := by
    intro n
    let K : Set ℂ := (H n).image Subtype.val ∪ {(x : ℂ), (y : ℂ)}
    have hxycompact : IsCompact ({(x : ℂ), (y : ℂ)} : Set ℂ) := by
      have h : IsCompact (({(x : ℂ)} : Set ℂ) ∪ {(y : ℂ)}) :=
        (isCompact_singleton : IsCompact ({(x : ℂ)} : Set ℂ)).union
          (isCompact_singleton : IsCompact ({(y : ℂ)} : Set ℂ))
      simpa only [insert_eq] using h
    have hK : IsCompact K :=
      ((H.isCompact n).image continuous_subtype_val).union hxycompact
    have hKU : K ⊆ U := by
      intro z hz
      rcases hz with hz | hz
      · obtain ⟨u, -, rfl⟩ := hz
        exact u.property
      · simp only [mem_insert_iff, mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact x.property
        · exact y.property
    obtain ⟨W, hW, hKW, hWcl, hWclU⟩ :=
      exists_open_compact_closure_buffer hK hU hKU
    refine ⟨W, hW, hWcl, hWclU, ?_, ?_, ?_⟩
    · exact (subset_union_left).trans hKW
    · exact hKW (Or.inr (by simp))
    · exact hKW (Or.inr (by simp))
  choose W hWopen hWcl hWclU hHW hxW hyW using hp
  exact ⟨W, fun n => ⟨hWopen n, hWcl n, hWclU n,
    hHW n, hxW n, hyW n⟩⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
