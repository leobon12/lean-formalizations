import Mathlib




 











set_option autoImplicit false

open Set Bornology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEventContact

 
theorem frontier_component_subset {T : Set ℂ} (hT : IsClosed T) (x : ℂ) :
    frontier (connectedComponentIn Tᶜ x) ⊆ T := by
  intro p hp
  by_contra hpT
  have hopen : IsOpen (connectedComponentIn Tᶜ p) := hT.isOpen_compl.connectedComponentIn
  have hpmem : p ∈ connectedComponentIn Tᶜ p := mem_connectedComponentIn hpT
  have hcl : p ∈ closure (connectedComponentIn Tᶜ x) := frontier_subset_closure hp
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hcl _ hopen hpmem
  have h1 : connectedComponentIn Tᶜ p = connectedComponentIn Tᶜ y := connectedComponentIn_eq hy1
  have h2 : connectedComponentIn Tᶜ x = connectedComponentIn Tᶜ y := connectedComponentIn_eq hy2
  have hpx : p ∈ connectedComponentIn Tᶜ x := by rw [h2, ← h1]; exact hpmem
  have hxopen : IsOpen (connectedComponentIn Tᶜ x) := hT.isOpen_compl.connectedComponentIn
  rw [hxopen.frontier_eq] at hp
  exact hp.2 hpx

 
theorem component_eq_of_mem {F : Set ℂ} {x y w : ℂ} (hx : w ∈ connectedComponentIn F x)
    (hy : w ∈ connectedComponentIn F y) : connectedComponentIn F x = connectedComponentIn F y :=
  (connectedComponentIn_eq hx).trans (connectedComponentIn_eq hy).symm

 

theorem isPreconnected_compl_component {T : Set ℂ} (hT : IsClosed T) (hTc : IsPreconnected T)
    (hTne : T.Nonempty) (x : ℂ) : IsPreconnected (connectedComponentIn Tᶜ x)ᶜ := by
  obtain ⟨t₀, ht₀⟩ := hTne
  have hTV : T ⊆ (connectedComponentIn Tᶜ x)ᶜ := fun y hy hyV =>
    (connectedComponentIn_subset Tᶜ x hyV) hy
  refine isPreconnected_of_forall t₀ fun y hy => ?_
  by_cases hyT : y ∈ T
  · exact ⟨T, hTV, ht₀, hyT, hTc⟩
  · have hyC : y ∈ connectedComponentIn Tᶜ y := mem_connectedComponentIn hyT
    
    have hCV : connectedComponentIn Tᶜ y ⊆ (connectedComponentIn Tᶜ x)ᶜ := by
      intro w hwC hwV
      have e : connectedComponentIn Tᶜ x = connectedComponentIn Tᶜ y := component_eq_of_mem hwV hwC
      exact hy (e ▸ hyC)
    
    have hclT : (closure (connectedComponentIn Tᶜ y) ∩ T).Nonempty := by
      by_contra hcon
      have hsub : closure (connectedComponentIn Tᶜ y) ⊆ Tᶜ := by
        intro w hw hwT
        exact hcon ⟨w, hw, hwT⟩
      have hclC : closure (connectedComponentIn Tᶜ y) ⊆ connectedComponentIn Tᶜ y :=
        (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
          (subset_closure hyC) hsub
      have hCclosed : IsClosed (connectedComponentIn Tᶜ y) := closure_subset_iff_isClosed.1 hclC
      have hCopen : IsOpen (connectedComponentIn Tᶜ y) := hT.isOpen_compl.connectedComponentIn
      have huniv : connectedComponentIn Tᶜ y = univ :=
        (isClopen_iff.1 ⟨hCclosed, hCopen⟩).resolve_left (nonempty_iff_ne_empty.1 ⟨y, hyC⟩)
      exact (connectedComponentIn_subset Tᶜ y (huniv ▸ mem_univ t₀)) ht₀
    obtain ⟨b, hbC, hbT⟩ := hclT
    have hpre1 : IsPreconnected (insert b (connectedComponentIn Tᶜ y)) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
        (insert_subset hbC subset_closure)
    refine ⟨insert b (connectedComponentIn Tᶜ y) ∪ T, ?_, ?_, ?_, ?_⟩
    · intro w hw
      rcases hw with hw | hwT
      · rcases (mem_insert_iff.1 hw) with rfl | hwC
        · exact hTV hbT
        · exact hCV hwC
      · exact hTV hwT
    · exact Or.inr ht₀
    · exact Or.inl (mem_insert_of_mem _ hyC)
    · exact IsPreconnected.union b (mem_insert _ _) hbT hpre1 hTc

 

theorem nested_of_disjoint {T₁ T₂ : Set ℂ} (h₁ : IsClosed T₁) (h₂ : IsClosed T₂)
    (hc₁ : IsPreconnected T₁) (hc₂ : IsPreconnected T₂) (hn₂ : T₂.Nonempty)
    (hdisj : Disjoint T₁ T₂) (x₁ x₂ : ℂ)
    (hb₁ : IsBounded (connectedComponentIn T₁ᶜ x₁)) (hb₂ : IsBounded (connectedComponentIn T₂ᶜ x₂))
    (hmeet : (connectedComponentIn T₁ᶜ x₁ ∩ connectedComponentIn T₂ᶜ x₂).Nonempty) :
    connectedComponentIn T₁ᶜ x₁ ⊆ connectedComponentIn T₂ᶜ x₂ ∨
      connectedComponentIn T₂ᶜ x₂ ⊆ connectedComponentIn T₁ᶜ x₁ := by
  set V₁ := connectedComponentIn T₁ᶜ x₁ with hV₁
  set V₂ := connectedComponentIn T₂ᶜ x₂ with hV₂
  obtain ⟨z, hz₁, hz₂⟩ := hmeet
  by_contra hcon
  push Not at hcon
  obtain ⟨hn12, hn21⟩ := hcon
  
  have hT₁V₂ : T₁ ⊆ V₂ := by
    have hmeetT : (V₂ ∩ T₁).Nonempty := by
      by_contra hem
      have hsub : V₂ ⊆ T₁ᶜ := fun w hw hwT => hem ⟨w, hw, hwT⟩
      have : V₂ ⊆ connectedComponentIn T₁ᶜ z :=
        isPreconnected_connectedComponentIn.subset_connectedComponentIn hz₂ hsub
      rw [← connectedComponentIn_eq hz₁] at this
      exact hn21 this
    obtain ⟨p, hpV₂, hpT₁⟩ := hmeetT
    have hT₁sub : T₁ ⊆ T₂ᶜ := fun w hw hw2 => hdisj.ne_of_mem hw hw2 rfl
    have := hc₁.subset_connectedComponentIn hpT₁ hT₁sub
    rwa [← connectedComponentIn_eq hpV₂] at this
  
  have hT₂V₁ : T₂ ⊆ V₁ := by
    have hmeetT : (V₁ ∩ T₂).Nonempty := by
      by_contra hem
      have hsub : V₁ ⊆ T₂ᶜ := fun w hw hwT => hem ⟨w, hw, hwT⟩
      have : V₁ ⊆ connectedComponentIn T₂ᶜ z :=
        isPreconnected_connectedComponentIn.subset_connectedComponentIn hz₁ hsub
      rw [← connectedComponentIn_eq hz₂] at this
      exact hn12 this
    obtain ⟨p, hpV₁, hpT₂⟩ := hmeetT
    have hT₂sub : T₂ ⊆ T₁ᶜ := fun w hw hw1 => hdisj.ne_of_mem hw1 hw rfl
    have := hc₂.subset_connectedComponentIn hpT₂ hT₂sub
    rwa [← connectedComponentIn_eq hpV₁] at this
  
  have hF : IsPreconnected V₂ᶜ := isPreconnected_compl_component h₂ hc₂ hn₂ x₂
  have hV₁open : IsOpen V₁ := h₁.isOpen_compl.connectedComponentIn
  have hcover : V₂ᶜ ⊆ V₁ ∪ (closure V₁)ᶜ := by
    intro w hw
    by_cases hwV₁ : w ∈ V₁
    · exact Or.inl hwV₁
    · refine Or.inr fun hwcl => ?_
      have hfr : w ∈ frontier V₁ := by rw [hV₁open.frontier_eq]; exact ⟨hwcl, hwV₁⟩
      exact hw (hT₁V₂ (frontier_component_subset h₁ x₁ hfr))
  have hdj : Disjoint V₁ (closure V₁)ᶜ :=
    Set.disjoint_left.2 fun w hw hwc => hwc (subset_closure hw)
  rcases hF.subset_or_subset hV₁open isClosed_closure.isOpen_compl hdj hcover with hsub | hsub
  · 
    have hbd : IsBounded (univ : Set ℂ) := by
      have : (univ : Set ℂ) ⊆ V₂ ∪ V₁ := fun w _ => by
        by_cases hw : w ∈ V₂
        · exact Or.inl hw
        · exact Or.inr (hsub hw)
      exact (hb₂.union hb₁).subset this
    exact (NormedSpace.unbounded_univ ℝ ℂ) hbd
  · 
    obtain ⟨t, ht⟩ := hn₂
    have htF : t ∈ V₂ᶜ := fun htV₂ => (connectedComponentIn_subset T₂ᶜ x₂ htV₂) ht
    exact hsub htF (subset_closure (hT₂V₁ ht))

 


theorem isPreconnected_biUnion_of_minimal_cover {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (T : ι → Set ℂ) (x : ι → ℂ) (hTc : ∀ i, IsClosed (T i)) (hTp : ∀ i, IsPreconnected (T i))
    (hTn : ∀ i, (T i).Nonempty) (hb : ∀ i, IsBounded (connectedComponentIn (T i)ᶜ (x i)))
    {S : Set ℂ} (hS : IsPreconnected S)
    (hcov : S ⊆ ⋃ i ∈ I, connectedComponentIn (T i)ᶜ (x i))
    (hmin : ∀ i ∈ I, ¬ S ⊆ ⋃ j ∈ I.erase i, connectedComponentIn (T j)ᶜ (x j)) :
    IsPreconnected (⋃ i ∈ (I : Set ι), T i) := by
  set V : ι → Set ℂ := fun i => connectedComponentIn (T i)ᶜ (x i) with hV
  have hVopen : ∀ i, IsOpen (V i) := fun i => (hTc i).isOpen_compl.connectedComponentIn
  
  have hVS : ∀ i ∈ I, (V i ∩ S).Nonempty := by
    intro i hi
    by_contra hem
    apply hmin i hi
    intro s hs
    obtain ⟨k, hk, hsk⟩ := mem_iUnion₂.1 (hcov hs)
    by_cases hki : k = i
    · subst hki; exact absurd ⟨s, hsk, hs⟩ hem
    · exact mem_iUnion₂.2 ⟨k, Finset.mem_erase.2 ⟨hki, hk⟩, hsk⟩
  
  have hmeetT : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (V i ∩ V j).Nonempty → (T i ∩ T j).Nonempty := by
    intro i hi j hj hij hVij
    by_contra hem
    have hdisj : Disjoint (T i) (T j) := Set.disjoint_iff_inter_eq_empty.2
      (not_nonempty_iff_eq_empty.1 hem)
    rcases nested_of_disjoint (hTc i) (hTc j) (hTp i) (hTp j) (hTn j) hdisj (x i) (x j) (hb i)
        (hb j) hVij with hsub | hsub
    · apply hmin i hi
      intro s hs
      obtain ⟨k, hk, hsk⟩ := mem_iUnion₂.1 (hcov hs)
      by_cases hki : k = i
      · subst hki; exact mem_iUnion₂.2 ⟨j, Finset.mem_erase.2 ⟨hij.symm, hj⟩, hsub hsk⟩
      · exact mem_iUnion₂.2 ⟨k, Finset.mem_erase.2 ⟨hki, hk⟩, hsk⟩
    · apply hmin j hj
      intro s hs
      obtain ⟨k, hk, hsk⟩ := mem_iUnion₂.1 (hcov hs)
      by_cases hkj : k = j
      · subst hkj; exact mem_iUnion₂.2 ⟨i, Finset.mem_erase.2 ⟨hij, hi⟩, hsub hsk⟩
      · exact mem_iUnion₂.2 ⟨k, Finset.mem_erase.2 ⟨hkj, hk⟩, hsk⟩
  
  set R : ι → ι → Prop := fun i j => (T i ∩ T j).Nonempty ∧ i ∈ I ∧ j ∈ I with hR
  have hRsymm : ∀ {i j : ι}, R i j → R j i := fun h =>
    ⟨by rw [Set.inter_comm]; exact h.1, h.2.2, h.2.1⟩
  have hRTsymm : ∀ {a b : ι}, Relation.ReflTransGen R a b → Relation.ReflTransGen R b a := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hRsymm hbc) ih
  
  have hlink : ∀ i₀ ∈ I, ∀ j ∈ I, Relation.ReflTransGen R i₀ j := by
    intro i₀ hi₀
    by_contra hall
    push Not at hall
    obtain ⟨b, hbI, hbA⟩ := hall
    set A : Set ι := {j | j ∈ I ∧ Relation.ReflTransGen R i₀ j} with hA
    set UA : Set ℂ := ⋃ j ∈ A, V j with hUA
    set UB : Set ℂ := ⋃ j ∈ {j | j ∈ I ∧ j ∉ A}, V j with hUB
    have hUAo : IsOpen UA := isOpen_biUnion fun j _ => hVopen j
    have hUBo : IsOpen UB := isOpen_biUnion fun j _ => hVopen j
    have hSsub : S ⊆ UA ∪ UB := by
      intro s hs
      obtain ⟨k, hk, hsk⟩ := mem_iUnion₂.1 (hcov hs)
      by_cases hkA : k ∈ A
      · exact Or.inl (mem_iUnion₂.2 ⟨k, hkA, hsk⟩)
      · exact Or.inr (mem_iUnion₂.2 ⟨k, ⟨hk, hkA⟩, hsk⟩)
    have hi₀A : i₀ ∈ A := ⟨hi₀, Relation.ReflTransGen.refl⟩
    have hbB : b ∈ {j | j ∈ I ∧ j ∉ A} := ⟨hbI, fun hb' => hbA hb'.2⟩
    obtain ⟨s₁, hs₁V, hs₁S⟩ := hVS i₀ hi₀
    obtain ⟨s₂, hs₂V, hs₂S⟩ := hVS b hbI
    obtain ⟨w, hwS, hwA, hwB⟩ := hS UA UB hUAo hUBo hSsub
      ⟨s₁, hs₁S, mem_iUnion₂.2 ⟨i₀, hi₀A, hs₁V⟩⟩ ⟨s₂, hs₂S, mem_iUnion₂.2 ⟨b, hbB, hs₂V⟩⟩
    obtain ⟨a, haA, hwa⟩ := mem_iUnion₂.1 hwA
    obtain ⟨c, hcB, hwc⟩ := mem_iUnion₂.1 hwB
    have hac : a ≠ c := fun h => hcB.2 (h ▸ haA)
    have hTac := hmeetT a haA.1 c hcB.1 hac ⟨w, hwa, hwc⟩
    exact hcB.2 ⟨hcB.1, haA.2.tail ⟨hTac, haA.1, hcB.1⟩⟩
  
  refine IsPreconnected.biUnion_of_reflTransGen (fun i _ => hTp i) fun i hi j hj => ?_
  have hij : Relation.ReflTransGen R i j := hlink i hi j hj
  clear hlink
  induction hij with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (ih (Finset.mem_coe.2 hbc.2.1)).tail ⟨hbc.1, Finset.mem_coe.2 hbc.2.1⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEventContact

