import SupercriticalLQGUniqueness.B2.LscTop.Metrizable

 
















set_option autoImplicit false

noncomputable section

open Set Filter Topology TopologicalSpace
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase

namespace SupercriticalLQGUniqueness.B2.LscTop

 
def supOfBasis {B : Set (Set (ℂ × ℂ))} (hB : IsTopologicalBasis B) (a : B → EReal) : LSCFun :=
  ⟨fun q => ⨆ (U : B) (_ : q ∈ (U : Set (ℂ × ℂ))), a U, by
    intro q t ht
    simp only [lt_iSup_iff] at ht
    obtain ⟨U, hqU, htU⟩ := ht
    filter_upwards [(hB.isOpen U.2).mem_nhds hqU] with x hx
    exact htU.trans_le (le_iSup₂_of_le U hx le_rfl)⟩

 

theorem exists_subseq_tendsto (F : ℕ → LSCFun) :
    ∃ f : LSCFun, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (F ∘ φ) atTop (𝓝 f) := by
  obtain ⟨B, S, hBc, -, hB, hSk, -, heq⟩ := exists_tests_eq_generateFrom
  have : Countable B := hBc.to_subtype
  let A : ℕ → B → EReal := fun n U => ⨅ x ∈ (U : Set (ℂ × ℂ)), (F n).1 x
  obtain ⟨a, -, φ, hφ, hA⟩ := isCompact_univ.tendsto_subseq (x := A) fun n => mem_univ (A n)
  have hAU : ∀ U : B, Tendsto (fun n => A (φ n) U) atTop (𝓝 (a U)) :=
    fun U => tendsto_pi_nhds.1 hA U
  refine ⟨supOfBasis hB a, φ, hφ, ?_⟩
  rw [heq, tendsto_nhds_generateFrom_iff]
  rintro t (⟨⟨⟨U, hU⟩, r⟩, rfl⟩ | ⟨⟨⟨K, hK⟩, r⟩, rfl⟩) hft
  · 
    obtain ⟨q, hqU, hq⟩ := hft
    have haU : a ⟨U, hU⟩ < ((r : ℝ) : EReal) :=
      (le_iSup₂_of_le (f := fun (V : B) (_ : q ∈ (V : Set (ℂ × ℂ))) => a V)
        ⟨U, hU⟩ hqU le_rfl).trans_lt hq
    filter_upwards [hAU ⟨U, hU⟩ (gt_mem_nhds haU)] with n hn
    simp only [A, Set.mem_preimage, Set.mem_ofPred_eq, iInf_lt_iff] at hn
    obtain ⟨x, hxU, hx⟩ := hn
    exact ⟨x, hxU, hx⟩
  · 
    have hcover : K ⊆ ⋃ V : {V : B // ((r : ℝ) : EReal) < a V}, (V.1 : Set (ℂ × ℂ)) := by
      intro x hx
      have := hft x hx
      simp only [supOfBasis, lt_iSup_iff] at this
      obtain ⟨V, hxV, hV⟩ := this
      exact mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩
    obtain ⟨T, hT⟩ := (hSk K hK).elim_finite_subcover
      (fun V : {V : B // ((r : ℝ) : EReal) < a V} => (V.1 : Set (ℂ × ℂ)))
      (fun V => hB.isOpen V.1.2) hcover
    have hev : ∀ᶠ n in atTop, ∀ V ∈ T, ((r : ℝ) : EReal) < A (φ n) V.1 :=
      T.eventually_all.2 fun V _ => hAU V.1 (lt_mem_nhds V.2)
    filter_upwards [hev] with n hn x hx
    obtain ⟨V, hVT, hxV⟩ := mem_iUnion₂.1 (hT hx)
    exact (hn V hVT).trans_le (iInf₂_le x hxV)

instance instSeqCompactSpace : SeqCompactSpace LSCFun :=
  ⟨fun F _ => by
    obtain ⟨f, φ, hφ, h⟩ := exists_subseq_tendsto F
    exact ⟨f, mem_univ f, φ, hφ, h⟩⟩

 

instance instCompactSpace : CompactSpace LSCFun :=
  compactSpace_iff_seqCompactSpace.2 inferInstance

 
instance instIsCompletelyMetrizableSpace : IsCompletelyMetrizableSpace LSCFun := by
  let _ := metrizableSpaceMetric LSCFun
  have : CompleteSpace LSCFun := complete_of_compact
  infer_instance

 
instance instPolishSpace : PolishSpace LSCFun := inferInstance

end SupercriticalLQGUniqueness.B2.LscTop
