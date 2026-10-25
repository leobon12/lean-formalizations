import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.ChargeV2




 











set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset LQGMetric.MetricGeometry Filter
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

 
def excSet (P : ℝ → ℂ) (T : ℝ) (O : Set ℂ) (V : TopologicalSpace.Opens ℂ) :
    Set (ℝ × ℝ × ℝ × ℝ) :=
  {e | EndSaving.Interfaces.Excursion P T O V e.1 e.2.1 e.2.2.1 e.2.2.2}

 
def ovSet (P : ℝ → ℂ) (T : ℝ) (O : Set ℂ) (V : TopologicalSpace.Opens ℂ) :
    Set (ℝ × ℝ × ℝ × ℝ) :=
  {e | e ∈ excSet P T O V ∧ ∃ t ∈ Ioo e.1 e.2.2.2, P t ∈ (V : Set ℂ)}

theorem ovSet_subset (P : ℝ → ℂ) (T : ℝ) (O : Set ℂ) (V : TopologicalSpace.Opens ℂ) :
    ovSet P T O V ⊆ excSet P T O V := fun _ he => he.1

 
theorem exc_basic {P : ℝ → ℂ} {T : ℝ} {O : Set ℂ} {V : TopologicalSpace.Opens ℂ}
    (hO : IsOpen O) (hVO : closure (V : Set ℂ) ⊆ O)
    {e : ℝ × ℝ × ℝ × ℝ} (he : e ∈ excSet P T O V) :
    e.1 < e.2.1 ∧ e.2.2.1 < e.2.2.2 ∧ P e.1 ∉ O ∧ P e.2.2.2 ∉ O := by
  obtain ⟨_, h12, _, h34, _, hf1, hf4, _, hτ, hσ, _, _⟩ := he
  have hnot1 : P e.1 ∉ O := by
    rw [hO.frontier_eq] at hf1
    exact hf1.2
  have hnot4 : P e.2.2.2 ∉ O := by
    rw [hO.frontier_eq] at hf4
    exact hf4.2
  refine ⟨lt_of_le_of_ne h12 ?_, lt_of_le_of_ne h34 ?_, hnot1, hnot4⟩
  · intro heq
    exact hnot1 (heq ▸ hVO hτ)
  · intro heq
    exact hnot4 (heq.symm ▸ hVO hσ)

 
theorem exc_eq_or_ordered {P : ℝ → ℂ} {T : ℝ} {O : Set ℂ} {V : TopologicalSpace.Opens ℂ}
    (hO : IsOpen O) (hVO : closure (V : Set ℂ) ⊆ O)
    {e f : ℝ × ℝ × ℝ × ℝ} (he : e ∈ excSet P T O V) (hf : f ∈ excSet P T O V) :
    e = f ∨ e.2.2.2 ≤ f.1 ∨ f.2.2.2 ≤ e.1 := by
  obtain ⟨he12, he34, he1, he4⟩ := exc_basic hO hVO he
  obtain ⟨hf12, hf34, hf1, hf4⟩ := exc_basic hO hVO hf
  have heO := he.2.2.2.2.2.2.2.1
  have hfO := hf.2.2.2.2.2.2.2.1
  have heab : e.1 < e.2.2.2 := he12.trans_le (he.2.2.1.trans he34.le)
  have hfab : f.1 < f.2.2.2 := hf12.trans_le (hf.2.2.1.trans hf34.le)
  have nf1 : f.1 ∉ Ioo e.1 e.2.2.2 := fun h => hf1 (heO _ h)
  have ne1 : e.1 ∉ Ioo f.1 f.2.2.2 := fun h => he1 (hfO _ h)
  have nf4 : f.2.2.2 ∉ Ioo e.1 e.2.2.2 := fun h => hf4 (heO _ h)
  have ne4 : e.2.2.2 ∉ Ioo f.1 f.2.2.2 := fun h => he4 (hfO _ h)
  rcases lt_trichotomy e.1 f.1 with hlt | heq | hgt
  · right; left
    by_contra hcon
    exact nf1 ⟨hlt, lt_of_not_ge hcon⟩
  · left
    have h4 : e.2.2.2 = f.2.2.2 := by
      rcases lt_trichotomy e.2.2.2 f.2.2.2 with h | h | h
      · exact absurd ⟨heq ▸ heab, h⟩ ne4
      · exact h
      · exact absurd ⟨heq.symm ▸ hfab, h⟩ nf4
    have h2 : e.2.1 = f.2.1 := by
      rcases lt_trichotomy e.2.1 f.2.1 with h | h | h
      · exact absurd he.2.2.2.2.2.2.2.2.1 (hf.2.2.2.2.2.2.2.2.2.2.1 _ ⟨heq ▸ he12, h⟩)
      · exact h
      · exact absurd hf.2.2.2.2.2.2.2.2.1 (he.2.2.2.2.2.2.2.2.2.2.1 _ ⟨heq.symm ▸ hf12, h⟩)
    have h3 : e.2.2.1 = f.2.2.1 := by
      rcases lt_trichotomy e.2.2.1 f.2.2.1 with h | h | h
      · exact absurd hf.2.2.2.2.2.2.2.2.2.1
          (he.2.2.2.2.2.2.2.2.2.2.2 _ ⟨h, h4 ▸ hf34⟩)
      · exact h
      · exact absurd he.2.2.2.2.2.2.2.2.2.1
          (hf.2.2.2.2.2.2.2.2.2.2.2 _ ⟨h, h4.symm ▸ he34⟩)
    obtain ⟨e1, e2, e3, e4⟩ := e
    obtain ⟨f1, f2, f3, f4⟩ := f
    simp only at heq h2 h3 h4
    rw [heq, h2, h3, h4]
  · right; right
    by_contra hcon
    exact ne1 ⟨hgt, lt_of_not_ge hcon⟩

 
theorem exc_ordered_of_disjoint {P : ℝ → ℂ} {T : ℝ} {O₁ O₂ : Set ℂ}
    {V₁ V₂ : TopologicalSpace.Opens ℂ}
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (hV₁ : closure (V₁ : Set ℂ) ⊆ O₁) (hV₂ : closure (V₂ : Set ℂ) ⊆ O₂)
    (hdisj : Disjoint O₁ O₂)
    {e f : ℝ × ℝ × ℝ × ℝ} (he : e ∈ excSet P T O₁ V₁) (hf : f ∈ excSet P T O₂ V₂) :
    e.2.2.2 ≤ f.1 ∨ f.2.2.2 ≤ e.1 := by
  obtain ⟨he12, he34, _, _⟩ := exc_basic hO₁ hV₁ he
  obtain ⟨hf12, hf34, _, _⟩ := exc_basic hO₂ hV₂ hf
  have heab : e.1 < e.2.2.2 := he12.trans_le (he.2.2.1.trans he34.le)
  have hfab : f.1 < f.2.2.2 := hf12.trans_le (hf.2.2.1.trans hf34.le)
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  set m := max e.1 f.1
  set M := min e.2.2.2 f.2.2.2
  have hmM : m < M := max_lt (lt_min heab h2) (lt_min h1 hfab)
  set t := (m + M) / 2
  have hmt : m < t := by simp only [t]; linarith
  have htM : t < M := by simp only [t]; linarith
  have hte : t ∈ Ioo e.1 e.2.2.2 :=
    ⟨(le_max_left e.1 f.1).trans_lt hmt, htM.trans_le (min_le_left e.2.2.2 f.2.2.2)⟩
  have htf : t ∈ Ioo f.1 f.2.2.2 :=
    ⟨(le_max_right e.1 f.1).trans_lt hmt, htM.trans_le (min_le_right e.2.2.2 f.2.2.2)⟩
  exact Set.disjoint_left.mp hdisj (he.2.2.2.2.2.2.2.1 t hte) (hf.2.2.2.2.2.2.2.1 t htf)

 

theorem openVisit_mem_window {P : ℝ → ℂ} {T : ℝ} {O : Set ℂ} {V : TopologicalSpace.Opens ℂ}
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) (hO : IsOpen O)
    (hVO : closure (V : Set ℂ) ⊆ O) (h0 : P 0 ∉ O) (hTO : P T ∉ O)
    {t : ℝ} (ht : t ∈ Icc 0 T) (htV : P t ∈ (V : Set ℂ)) :
    ∃ e ∈ ovSet P T O V, e.2.1 ≤ t ∧ t ≤ e.2.2.1 := by
  have htO : P t ∈ O := hVO (subset_closure htV)
  have hq : t ∈ Ioo 0 T := by
    refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
    · intro h; exact h0 (h ▸ htO)
    · intro h; exact hTO (h.symm ▸ htO)
  have hcomp := Toolkit.PlanarSeparation.excursionComponentCode hT hP hO h0 hTO hq htO
  dsimp only at hcomp
  obtain ⟨ha0, hat, htb, hbT, haOut, hbOut, hinside⟩ := hcomp
  set a := sSup {u ∈ Icc 0 t | P u ∉ O} with ha
  set b := sInf {u ∈ Icc t T | P u ∉ O} with hb
  have hcontact : ({u ∈ Icc a b | P u ∈ closure (V : Set ℂ)}).Nonempty :=
    ⟨t, ⟨hat.le, htb.le⟩, subset_closure htV⟩
  have hcc := Toolkit.PlanarSeparation.excursionContactCode hT hP hO h0 hTO hq htO hVO hcontact
  dsimp only at hcc
  obtain ⟨haτ, hτσ, hσb, hτV, hσV, hbetween⟩ := hcc
  set C := {u ∈ Icc a b | P u ∈ closure (V : Set ℂ)} with hC
  set τ := sInf C with hτ
  set σ := sSup C with hσ
  have hCbelow : BddBelow C := ⟨a, fun u hu => hu.1.1⟩
  have hCabove : BddAbove C := ⟨b, fun u hu => hu.1.2⟩
  have hab : a < b := hat.trans htb
  have hPab : ContinuousOn P (Icc a b) := hP.mono (Icc_subset_Icc ha0 hbT)
  have hfrontier : ∀ c ∈ ({a, b} : Set ℝ), P c ∉ O → P c ∈ frontier O := by
    intro c hc hcO
    rw [hO.frontier_eq]
    refine ⟨?_, hcO⟩
    have hcI : c ∈ Icc a b := by
      rcases hc with rfl | rfl
      · exact ⟨le_rfl, hab.le⟩
      · exact ⟨hab.le, le_rfl⟩
    have hcl : c ∈ closure (Ioo a b) := by
      rw [closure_Ioo hab.ne]
      exact hcI
    have hcont : ContinuousWithinAt P (Ioo a b) c :=
      (hPab c hcI).mono Ioo_subset_Icc_self
    exact hcont.mem_closure hcl (fun u hu => hinside u hu)
  refine ⟨(a, τ, σ, b), ⟨⟨ha0, haτ.le, hτσ, hσb.le, hbT,
    hfrontier a (Or.inl rfl) haOut, hfrontier b (Or.inr rfl) hbOut, hinside, hτV, hσV, ?_, ?_⟩,
    t, ⟨hat, htb⟩, htV⟩, (hbetween t ⟨hat.le, htb.le⟩ htV)⟩
  · intro u hu huV
    have huC : u ∈ C := ⟨⟨hu.1.le, hu.2.le.trans (hτσ.trans hσb.le)⟩, huV⟩
    exact (not_le_of_gt hu.2) (csInf_le hCbelow huC)
  · intro u hu huV
    have huC : u ∈ C := ⟨⟨(haτ.le.trans hτσ).trans hu.1.le, hu.2.le⟩, huV⟩
    exact (not_le_of_gt hu.1) (le_csSup hCabove huC)

 

theorem exc_window_endpoints_not_open {P : ℝ → ℂ} {T : ℝ} {O : Set ℂ}
    {V : TopologicalSpace.Opens ℂ} (hP : ContinuousOn P (Icc 0 T))
    (hO : IsOpen O) (hVO : closure (V : Set ℂ) ⊆ O)
    {e : ℝ × ℝ × ℝ × ℝ} (he : e ∈ excSet P T O V) :
    P e.2.1 ∉ (V : Set ℂ) ∧ P e.2.2.1 ∉ (V : Set ℂ) := by
  obtain ⟨he12, he34, _, _⟩ := exc_basic hO hVO he
  obtain ⟨h0, _, h23, _, h4T, _, _, _, _, _, hbefore, hafter⟩ := he
  constructor
  · intro hV
    have hτI : e.2.1 ∈ Icc 0 T := ⟨h0.trans he12.le, h23.trans (he34.le.trans h4T)⟩
    have hcont : ContinuousWithinAt P (Icc 0 T) e.2.1 := hP _ hτI
    have hnhds : P ⁻¹' (V : Set ℂ) ∈ 𝓝[Icc 0 T] e.2.1 :=
      hcont.preimage_mem_nhdsWithin (V.isOpen.mem_nhds hV)
    have hleft : Icc 0 T ∩ Ioo e.1 e.2.1 ∈ 𝓝[<] e.2.1 := by
      have h1 : Ioo e.1 e.2.1 ∈ 𝓝[<] e.2.1 := Ioo_mem_nhdsLT he12
      have h2 : Icc 0 T ∈ 𝓝[<] e.2.1 := by
        apply mem_nhdsWithin_of_mem_nhds
        apply Icc_mem_nhds
        · exact h0.trans_lt he12
        · exact lt_of_lt_of_le (lt_of_le_of_lt h23 he34) h4T
      exact Filter.inter_mem h2 h1
    have hcombined : P ⁻¹' (V : Set ℂ) ∩ (Icc 0 T ∩ Ioo e.1 e.2.1) ∈ 𝓝[<] e.2.1 := by
      have hnhds' : P ⁻¹' (V : Set ℂ) ∈ 𝓝[<] e.2.1 := by
        have hne : e.2.1 ∈ Ioo 0 T := ⟨h0.trans_lt he12, lt_of_lt_of_le
          (lt_of_le_of_lt h23 he34) h4T⟩
        have hle : 𝓝[<] e.2.1 ≤ 𝓝[Icc 0 T] e.2.1 := by
          rw [nhdsWithin_le_iff]
          exact Filter.mem_of_superset hleft Set.inter_subset_left
        exact hle hnhds
      exact Filter.inter_mem hnhds' hleft
    obtain ⟨u, huV, _, hu⟩ := Filter.nonempty_of_mem hcombined
    exact hbefore u hu (subset_closure huV)
  · intro hV
    have hσI : e.2.2.1 ∈ Icc 0 T := ⟨(h0.trans he12.le).trans h23, he34.le.trans h4T⟩
    have hcont : ContinuousWithinAt P (Icc 0 T) e.2.2.1 := hP _ hσI
    have hnhds : P ⁻¹' (V : Set ℂ) ∈ 𝓝[Icc 0 T] e.2.2.1 :=
      hcont.preimage_mem_nhdsWithin (V.isOpen.mem_nhds hV)
    have hright : Icc 0 T ∩ Ioo e.2.2.1 e.2.2.2 ∈ 𝓝[>] e.2.2.1 := by
      have h1 : Ioo e.2.2.1 e.2.2.2 ∈ 𝓝[>] e.2.2.1 := Ioo_mem_nhdsGT he34
      have h2 : Icc 0 T ∈ 𝓝[>] e.2.2.1 := by
        apply mem_nhdsWithin_of_mem_nhds
        apply Icc_mem_nhds
        · exact lt_of_lt_of_le (h0.trans_lt he12) h23
        · exact he34.trans_le h4T
      exact Filter.inter_mem h2 h1
    have hcombined : P ⁻¹' (V : Set ℂ) ∩ (Icc 0 T ∩ Ioo e.2.2.1 e.2.2.2) ∈ 𝓝[>] e.2.2.1 := by
      have hnhds' : P ⁻¹' (V : Set ℂ) ∈ 𝓝[>] e.2.2.1 := by
        have hle : 𝓝[>] e.2.2.1 ≤ 𝓝[Icc 0 T] e.2.2.1 := by
          rw [nhdsWithin_le_iff]
          exact Filter.mem_of_superset hright Set.inter_subset_left
        exact hle hnhds
      exact Filter.inter_mem hnhds' hright
    obtain ⟨u, huV, _, hu⟩ := Filter.nonempty_of_mem hcombined
    exact hafter u hu (subset_closure huV)


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
