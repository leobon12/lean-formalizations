import Mathlib




 









set_option autoImplicit false


open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeLoops

theorem gap_lemma {P : ℝ → ℂ} {t₁ t₂ δ : ℝ} {V X Y : Set ℂ}
    (h12 : t₁ ≤ t₂) (hδ : 0 < δ) (hP : ContinuousOn P (Icc t₁ t₂)) (hV : IsOpen V)
    (hjump : ∀ a b, t₁ ≤ a → b ≤ t₂ → (∀ t ∈ Icc a b, P t ∉ V) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (P s) (P t) < δ)
    (hX : IsClosed X) (hY : IsClosed Y) (hXY : ∀ x ∈ X, ∀ y ∈ Y, 2 * δ ≤ dist x y)
    (h1 : P t₁ ∈ X) (hcov : ∀ t ∈ Icc t₁ t₂, P t ∈ V → P t ∈ X ∪ Y) :
    ∀ t ∈ Icc t₁ t₂, P t ∉ Y ∧ ∃ x ∈ X, dist (P t) x < δ := by
  have hnear : ∀ t ∈ Icc t₁ t₂, ∃ w ∈ X ∪ Y, dist (P t) w < δ := by
    intro t ht
    by_cases hPt : P t ∈ V
    · exact ⟨P t, hcov t ht hPt, by simpa using hδ⟩
    set S : Set ℝ := {t' ∈ Icc t₁ t | P t' ∈ V} with hS
    have hSsub : S ⊆ Icc t₁ t := fun _ h => h.1
    by_cases hSne : S.Nonempty
    · have hbdd : BddAbove S := ⟨t, fun _ h => h.1.2⟩
      set e := sSup S with he
      have heS : e ∈ closure S := csSup_mem_closure hSne hbdd
      have heI : e ∈ Icc t₁ t := by
        have := closure_mono hSsub heS
        rwa [closure_Icc] at this
      have heI' : e ∈ Icc t₁ t₂ := ⟨heI.1, heI.2.trans ht.2⟩
      have hPe : P e ∈ X ∪ Y := by
        have hcl : P e ∈ closure (P '' S) := by
          have hcont : ContinuousWithinAt P (Icc t₁ t₂) e := hP e heI'
          have hsub : S ⊆ Icc t₁ t₂ := fun x hx => ⟨hx.1.1, hx.1.2.trans ht.2⟩
          exact (hcont.mono hsub).mem_closure_image heS
        have hsub2 : P '' S ⊆ X ∪ Y := by
          rintro _ ⟨x, hx, rfl⟩
          exact hcov x ⟨hx.1.1, hx.1.2.trans ht.2⟩ hx.2
        exact (closure_minimal hsub2 (hX.union hY)) hcl
      have hoff : ∀ s ∈ Icc e t, P s ∉ V := by
        intro s hs hsV
        rcases eq_or_lt_of_le hs.1 with hse | hse
        · rw [← hse] at hsV hs
          clear hse
          rcases eq_or_lt_of_le hs.2 with het | het
          · exact hPt (het ▸ hsV)
          · have hcont : ContinuousWithinAt P (Icc t₁ t₂) e := hP e heI'
            have hmem : P ⁻¹' V ∈ nhdsWithin e (Icc t₁ t₂) :=
              hcont.preimage_mem_nhdsWithin (hV.mem_nhds hsV)
            rw [mem_nhdsWithin] at hmem
            obtain ⟨O, hO, heO, hOsub⟩ := hmem
            obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO e heO
            set s' := min (e + ε / 2) t with hs'
            have hs's : e < s' := lt_min (by linarith) het
            have hs'O : s' ∈ O := hball (by
              rw [Metric.mem_ball, Real.dist_eq, abs_lt]
              constructor
              · linarith
              · have : s' ≤ e + ε / 2 := min_le_left _ _
                linarith)
            have hs'I : s' ∈ Icc t₁ t₂ :=
              ⟨heI'.1.trans hs's.le, (min_le_right _ _).trans ht.2⟩
            have hs'S : s' ∈ S := ⟨⟨heI.1.trans hs's.le, min_le_right _ _⟩,
              hOsub ⟨hs'O, hs'I⟩⟩
            have := le_csSup hbdd hs'S
            linarith
        · have hsS : s ∈ S := ⟨⟨heI.1.trans hse.le, hs.2⟩, hsV⟩
          have := le_csSup hbdd hsS
          linarith
      have hd := hjump e t heI'.1 ht.2 hoff t ⟨heI.2, le_rfl⟩ e ⟨le_rfl, heI.2⟩
      exact ⟨P e, hPe, hd⟩
    · have hoff : ∀ s ∈ Icc t₁ t, P s ∉ V := fun s hs hsV => hSne ⟨s, hs, hsV⟩
      have hd := hjump t₁ t le_rfl ht.2 hoff t ⟨ht.1, le_rfl⟩ t₁ ⟨le_rfl, ht.1⟩
      exact ⟨P t₁, Or.inl h1, hd⟩
  set Q : ℝ → ℂ := fun t => P (projIcc t₁ t₂ h12 t) with hQ
  have hQc : Continuous Q :=
    hP.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun t => (projIcc t₁ t₂ h12 t).2)
  have hQeq : ∀ t ∈ Icc t₁ t₂, Q t = P t := fun t ht => by
    simp [hQ, projIcc_of_mem h12 ht]
  set u : Set ℝ := {t | ∃ x ∈ X, dist (Q t) x < δ} with hu
  set v : Set ℝ := {t | ∃ y ∈ Y, dist (Q t) y < δ} with hv
  have huo : IsOpen u := by
    have : u = ⋃ x ∈ X, Q ⁻¹' ball x δ := by
      ext t; simp [hu, Metric.mem_ball]
    rw [this]
    exact isOpen_biUnion fun x _ => isOpen_ball.preimage hQc
  have hvo : IsOpen v := by
    have : v = ⋃ y ∈ Y, Q ⁻¹' ball y δ := by
      ext t; simp [hv, Metric.mem_ball]
    rw [this]
    exact isOpen_biUnion fun y _ => isOpen_ball.preimage hQc
  have huv : Disjoint u v := by
    rw [Set.disjoint_left]
    rintro t ⟨x, hx, hdx⟩ ⟨y, hy, hdy⟩
    have h2 := hXY x hx y hy
    have := dist_triangle_left x y (Q t)
    linarith
  have hcover : Icc t₁ t₂ ⊆ u ∪ v := by
    intro t ht
    obtain ⟨w, hw, hdw⟩ := hnear t ht
    rw [← hQeq t ht] at hdw
    rcases hw with hw | hw
    · exact Or.inl ⟨w, hw, hdw⟩
    · exact Or.inr ⟨w, hw, hdw⟩
  have hne : (Icc t₁ t₂ ∩ u).Nonempty :=
    ⟨t₁, ⟨le_rfl, h12⟩, ⟨P t₁, h1, by rw [hQeq t₁ ⟨le_rfl, h12⟩]; simpa using hδ⟩⟩
  have hsub : Icc t₁ t₂ ⊆ u :=
    isPreconnected_Icc.subset_left_of_subset_union huo hvo huv hcover hne
  intro t ht
  obtain ⟨x, hx, hdx⟩ := hsub ht
  rw [hQeq t ht] at hdx
  refine ⟨fun hPY => ?_, x, hx, hdx⟩
  have h2 := hXY x hx (P t) hPY
  rw [dist_comm] at hdx
  linarith

 
theorem gap_closure {s t : Set ℂ} {c : ℝ} (h : ∀ x ∈ s, ∀ y ∈ t, c ≤ dist x y) :
    ∀ x ∈ closure s, ∀ y ∈ closure t, c ≤ dist x y := by
  have hcl : IsClosed {p : ℂ × ℂ | c ≤ dist p.1 p.2} :=
    isClosed_le continuous_const (continuous_fst.dist continuous_snd)
  have hsub : s ×ˢ t ⊆ {p : ℂ × ℂ | c ≤ dist p.1 p.2} := fun p hp => h p.1 hp.1 p.2 hp.2
  intro x hx y hy
  have : (x, y) ∈ closure (s ×ˢ t) := by
    rw [closure_prod_eq]; exact ⟨hx, hy⟩
  exact (hcl.closure_subset_iff.2 hsub) this

 
def adj8 (i j : Fin 8) : Prop := j = i + 1 ∨ i = j + 1

instance : DecidableRel adj8 := fun i j => by unfold adj8; infer_instance

 
def U8 (S : Fin 8 → Set ℂ) (I : Finset (Fin 8)) : Set ℂ := ⋃ i ∈ I, S i

theorem closure_U8 (S : Fin 8 → Set ℂ) (I : Finset (Fin 8)) :
    closure (U8 S I) = ⋃ i ∈ I, closure (S i) := by
  unfold U8
  exact (I.finite_toSet).closure_biUnion _

theorem subset_closure_U8 (S : Fin 8 → Set ℂ) {I : Finset (Fin 8)} {i : Fin 8} (hi : i ∈ I) :
    closure (S i) ⊆ closure (U8 S I) := by
  rw [closure_U8]
  exact subset_biUnion_of_mem (u := fun i => closure (S i)) hi

 
structure Cyc8 (P : ℝ → ℂ) (V : Set ℂ) (S : Fin 8 → Set ℂ) (τ σ δ : ℝ) : Prop where
  hτσ : τ ≤ σ
  hδ : 0 < δ
  hP : ContinuousOn P (Icc τ σ)
  hV : IsOpen V
  hVS : V = ⋃ i, S i
  hgap : ∀ i j, i ≠ j → ¬ adj8 i j → ∀ x ∈ S i, ∀ y ∈ S j, 2 * δ ≤ dist x y
  hjump : ∀ a b, τ ≤ a → b ≤ σ → (∀ t ∈ Icc a b, P t ∉ V) →
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (P s) (P t) < δ

namespace Cyc8

variable {P : ℝ → ℂ} {V : Set ℂ} {S : Fin 8 → Set ℂ} {τ σ δ : ℝ}

 
theorem mem_piece_of_closure (C : Cyc8 P V S τ σ δ) {z : ℂ} (hzV : z ∈ V) {o : Fin 8}
    (hz : z ∈ closure (S o)) : ∃ i, z ∈ S i ∧ (i = o ∨ adj8 i o) := by
  rw [C.hVS, mem_iUnion] at hzV
  obtain ⟨i, hi⟩ := hzV
  refine ⟨i, hi, ?_⟩
  by_contra hno
  push Not at hno
  have h := gap_closure (C.hgap i o hno.1 hno.2) z (subset_closure hi) z hz
  rw [dist_self] at h
  linarith [C.hδ]

 
theorem gl (C : Cyc8 P V S τ σ δ) {t₁ t₂ : ℝ} (ht₁ : τ ≤ t₁) (h12 : t₁ ≤ t₂) (ht₂ : t₂ ≤ σ)
    (A B : Finset (Fin 8)) (hAB : ∀ i ∈ A, ∀ j ∈ B, i ≠ j ∧ ¬ adj8 i j)
    (hstart : P t₁ ∈ closure (U8 S A))
    (hcov : ∀ t ∈ Icc t₁ t₂, P t ∈ V → P t ∈ U8 S A ∪ U8 S B) :
    ∀ t ∈ Icc t₁ t₂, P t ∉ closure (U8 S B) := by
  have hP' : ContinuousOn P (Icc t₁ t₂) := C.hP.mono (Icc_subset_Icc ht₁ ht₂)
  have hjump' : ∀ a b, t₁ ≤ a → b ≤ t₂ → (∀ t ∈ Icc a b, P t ∉ V) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (P s) (P t) < δ :=
    fun a b ha hb => C.hjump a b (ht₁.trans ha) (hb.trans ht₂)
  have hXY : ∀ x ∈ closure (U8 S A), ∀ y ∈ closure (U8 S B), 2 * δ ≤ dist x y := by
    intro x hx y hy
    rw [closure_U8, mem_iUnion₂] at hx hy
    obtain ⟨i, hi, hx⟩ := hx
    obtain ⟨j, hj, hy⟩ := hy
    exact gap_closure (C.hgap i j (hAB i hi j hj).1 (hAB i hi j hj).2) x hx y hy
  have hcov' : ∀ t ∈ Icc t₁ t₂, P t ∈ V → P t ∈ closure (U8 S A) ∪ closure (U8 S B) := by
    intro t ht hPt
    rcases hcov t ht hPt with h | h
    · exact Or.inl (subset_closure h)
    · exact Or.inr (subset_closure h)
  intro t ht
  exact (gap_lemma h12 C.hδ hP' C.hV hjump' isClosed_closure isClosed_closure hXY hstart
    hcov' t ht).1

theorem mem_U8 {S : Fin 8 → Set ℂ} {I : Finset (Fin 8)} {i : Fin 8} {z : ℂ} (hi : i ∈ I)
    (hz : z ∈ S i) : z ∈ U8 S I := mem_biUnion hi hz

 
theorem reverse (C : Cyc8 P V S τ σ δ) {a b : ℝ} (ha : τ ≤ a) (hab : a ≤ b) (hb : b ≤ σ) :
    Cyc8 (fun u => P (a + b - u)) V S a b δ where
  hτσ := hab
  hδ := C.hδ
  hP := by
    apply C.hP.comp (by fun_prop)
    intro u hu
    exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  hV := C.hV
  hVS := C.hVS
  hgap := C.hgap
  hjump := by
    intro a' b' ha' hb' hoff s hs t ht
    have := C.hjump (a + b - b') (a + b - a') (by linarith) (by linarith)
      (fun u hu => by
        have := hoff (a + b - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
        simpa [show a + b - (a + b - u) = u by ring] using this)
      (a + b - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      (a + b - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa using this

 
theorem restrict (C : Cyc8 P V S τ σ δ) {a b : ℝ} (ha : τ ≤ a) (hab : a ≤ b) (hb : b ≤ σ) :
    Cyc8 P V S a b δ where
  hτσ := hab
  hδ := C.hδ
  hP := C.hP.mono (Icc_subset_Icc ha hb)
  hV := C.hV
  hVS := C.hVS
  hgap := C.hgap
  hjump := fun a' b' ha' hb' => C.hjump a' b' (ha.trans ha') (hb'.trans hb)

end Cyc8

 

def WindowAt (P : ℝ → ℂ) (V : Set ℂ) (S : Fin 8 → Set ℂ) (τ σ : ℝ) (b A B : Fin 8) : Prop :=
  ∃ t₁ t₂, τ ≤ t₁ ∧ t₁ ≤ t₂ ∧ t₂ ≤ σ ∧ P t₁ ∈ closure (S A) ∧ P t₂ ∈ closure (S B) ∧
    ∀ t ∈ Ioo t₁ t₂, P t ∈ V → P t ∈ S b

 

theorem case_plus {P : ℝ → ℂ} {V : Set ℂ} {S : Fin 8 → Set ℂ} {τ σ δ : ℝ}
    (C : Cyc8 P V S τ σ δ) (hτ : P τ ∈ closure (S 0))
    {d₀ c₀ : ℝ} (hd₀ : d₀ ∈ Icc τ σ) (hPd₀ : P d₀ ∈ closure (S 4))
    (hbefore : ∀ t ∈ Ico τ d₀, P t ∉ closure (S 4))
    (hc₀ : c₀ ∈ Icc τ d₀) (hPc₀ : P c₀ ∈ closure (S 2))
    (hafter : ∀ t ∈ Ioc c₀ d₀, P t ∉ closure (S 2) ∧ P t ∉ closure (S 6)) :
    WindowAt P V S τ σ 1 0 2 ∧ WindowAt P V S τ σ 3 2 4 := by
  have hcd : c₀ < d₀ := by
    rcases eq_or_lt_of_le hc₀.2 with h | h
    · exfalso
      have := gap_closure (C.hgap 2 4 (by decide) (by decide)) (P c₀) hPc₀ (P d₀) hPd₀
      rw [h, dist_self] at this
      linarith [C.hδ]
    · exact h
  
  have hno5 : ∀ t ∈ Ico c₀ d₀, P t ∉ closure (S 5) := by
    intro t ht
    have Ct := C.restrict (hc₀.1) ht.1 (ht.2.le.trans hd₀.2)
    have key := Ct.gl le_rfl ht.1 le_rfl {0, 1, 2, 3, 7} {5} (by decide)
      (subset_closure_U8 S (i := 2) (by decide) hPc₀)
      (by
        intro t' ht' hV'
        rcases eq_or_lt_of_le ht'.1 with h | h
        · subst h
          obtain ⟨i, hi, hio⟩ := C.mem_piece_of_closure hV' hPc₀
          left
          exact Cyc8.mem_U8 ((by decide : ∀ i : Fin 8, (i = 2 ∨ adj8 i 2) →
            i ∈ ({0, 1, 2, 3, 7} : Finset (Fin 8))) i hio) hi
        · obtain ⟨i, hi⟩ := mem_iUnion.1 (C.hVS ▸ hV')
          have h2 := (hafter t' ⟨h, ht'.2.trans ht.2.le⟩).1
          have h6 := (hafter t' ⟨h, ht'.2.trans ht.2.le⟩).2
          have h4 := hbefore t' ⟨hc₀.1.trans ht'.1, lt_of_le_of_lt ht'.2 ht.2⟩
          have hi2 : i ≠ 2 := fun e => h2 (e ▸ subset_closure hi)
          have hi6 : i ≠ 6 := fun e => h6 (e ▸ subset_closure hi)
          have hi4 : i ≠ 4 := fun e => h4 (e ▸ subset_closure hi)
          rcases ((by decide : ∀ i : Fin 8, i ≠ 2 → i ≠ 6 → i ≠ 4 →
              i ∈ ({0, 1, 3, 7} : Finset (Fin 8)) ∨ i = 5) i hi2 hi6 hi4) with hiA | hiB
          · left
            exact Cyc8.mem_U8 ((by decide : ∀ i : Fin 8, i ∈ ({0, 1, 3, 7} : Finset (Fin 8)) →
              i ∈ ({0, 1, 2, 3, 7} : Finset (Fin 8))) i hiA) hi
          · right; exact Cyc8.mem_U8 (by simp [hiB]) hi)
      t ⟨ht.1, le_rfl⟩
    intro h5
    exact key (subset_closure_U8 S (by decide) h5)
  
  have hclass : ∀ t ∈ Ioo c₀ d₀, P t ∈ V → ∀ i, P t ∈ S i →
      i ∈ ({0, 1, 3, 7} : Finset (Fin 8)) := by
    intro t ht hV' i hi
    have h2 := (hafter t ⟨ht.1, ht.2.le⟩).1
    have h6 := (hafter t ⟨ht.1, ht.2.le⟩).2
    have h4 := hbefore t ⟨hc₀.1.trans ht.1.le, ht.2⟩
    have h5 := hno5 t ⟨ht.1.le, ht.2⟩
    have hi2 : i ≠ 2 := fun e => h2 (e ▸ subset_closure hi)
    have hi6 : i ≠ 6 := fun e => h6 (e ▸ subset_closure hi)
    have hi4 : i ≠ 4 := fun e => h4 (e ▸ subset_closure hi)
    have hi5 : i ≠ 5 := fun e => h5 (e ▸ subset_closure hi)
    exact (by decide : ∀ i : Fin 8, i ≠ 2 → i ≠ 6 → i ≠ 4 → i ≠ 5 →
      i ∈ ({0, 1, 3, 7} : Finset (Fin 8))) i hi2 hi6 hi4 hi5
  
  have hwin3 : ∀ t ∈ Ioo c₀ d₀, P t ∈ V → P t ∈ S 3 := by
    intro t ht hV'
    obtain ⟨i, hi⟩ := mem_iUnion.1 (C.hVS ▸ hV')
    have hiA := hclass t ht hV' i hi
    by_contra h3
    have hi3 : i ≠ 3 := fun e => h3 (e ▸ hi)
    have hi017 : i ∈ ({0, 1, 7} : Finset (Fin 8)) :=
      (by decide : ∀ i : Fin 8, i ∈ ({0, 1, 3, 7} : Finset (Fin 8)) → i ≠ 3 →
        i ∈ ({0, 1, 7} : Finset (Fin 8))) i hiA hi3
    have Ct := C.restrict (hc₀.1.trans ht.1.le) ht.2.le hd₀.2
    have key := Ct.gl le_rfl ht.2.le le_rfl {0, 1, 7} {3, 4, 5} (by decide)
      (subset_closure (Cyc8.mem_U8 hi017 hi))
      (by
        intro t' ht' hV''
        rcases eq_or_lt_of_le ht'.2 with h | h
        · subst h
          obtain ⟨j, hj, hjo⟩ := C.mem_piece_of_closure hV'' hPd₀
          right
          exact Cyc8.mem_U8 ((by decide : ∀ j : Fin 8, (j = 4 ∨ adj8 j 4) →
            j ∈ ({3, 4, 5} : Finset (Fin 8))) j hjo) hj
        · obtain ⟨j, hj⟩ := mem_iUnion.1 (C.hVS ▸ hV'')
          have hjA := hclass t' ⟨lt_of_lt_of_le ht.1 ht'.1, h⟩ hV'' j hj
          rcases ((by decide : ∀ j : Fin 8, j ∈ ({0, 1, 3, 7} : Finset (Fin 8)) →
              j ∈ ({0, 1, 7} : Finset (Fin 8)) ∨ j = 3) j hjA) with hjA' | hjB
          · left; exact Cyc8.mem_U8 hjA' hj
          · right; exact Cyc8.mem_U8 (by simp [hjB]) hj)
      d₀ ⟨ht.2.le, le_rfl⟩
    exact key (subset_closure_U8 S (by decide) hPd₀)
  refine ⟨?_, ⟨c₀, d₀, hc₀.1, hcd.le, hd₀.2, hPc₀, hPd₀, hwin3⟩⟩
  
  have hP' : ContinuousOn P (Icc τ c₀) := C.hP.mono (Icc_subset_Icc le_rfl (hc₀.2.trans hd₀.2))
  set T2 : Set ℝ := Icc τ c₀ ∩ P ⁻¹' closure (S 2) with hT2
  have hT2c : IsClosed T2 := hP'.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closure
  have hT2ne : T2.Nonempty := ⟨c₀, ⟨hc₀.1, le_rfl⟩, hPc₀⟩
  have hT2b : BddBelow T2 := ⟨τ, fun _ h => h.1.1⟩
  set b₀ := sInf T2 with hb₀
  have hb₀T : b₀ ∈ T2 := hT2c.csInf_mem hT2ne hT2b
  have hb₀first : ∀ t ∈ Ico τ b₀, P t ∉ closure (S 2) := by
    intro t ht h
    have : b₀ ≤ t := csInf_le hT2b ⟨⟨ht.1, ht.2.le.trans hb₀T.1.2⟩, h⟩
    linarith [ht.2]
  have hP'' : ContinuousOn P (Icc τ b₀) :=
    C.hP.mono (Icc_subset_Icc le_rfl (hb₀T.1.2.trans (hc₀.2.trans hd₀.2)))
  set T0 : Set ℝ := Icc τ b₀ ∩ P ⁻¹' closure (S 0) with hT0
  have hT0c : IsClosed T0 := hP''.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closure
  have hT0ne : T0.Nonempty := ⟨τ, ⟨le_rfl, hb₀T.1.1⟩, hτ⟩
  have hT0b : BddAbove T0 := ⟨b₀, fun _ h => h.1.2⟩
  set a₀ := sSup T0 with ha₀
  have ha₀T : a₀ ∈ T0 := hT0c.csSup_mem hT0ne hT0b
  have ha₀last : ∀ t ∈ Ioc a₀ b₀, P t ∉ closure (S 0) := by
    intro t ht h
    have : t ≤ a₀ := le_csSup hT0b ⟨⟨ha₀T.1.1.trans ht.1.le, ht.2⟩, h⟩
    linarith [ht.1]
  have hb₀σ : b₀ ≤ σ := hb₀T.1.2.trans (hc₀.2.trans hd₀.2)
  have hb₀d : b₀ < d₀ := lt_of_le_of_lt hb₀T.1.2 hcd
  
  have hbase : ∀ t ∈ Ioo a₀ b₀, ∀ i, P t ∈ S i → i ≠ 0 ∧ i ≠ 2 ∧ i ≠ 4 := by
    intro t ht i hi
    have h0 := ha₀last t ⟨ht.1, ht.2.le⟩
    have h2 := hb₀first t ⟨ha₀T.1.1.trans ht.1.le, ht.2⟩
    have h4 := hbefore t ⟨ha₀T.1.1.trans ht.1.le, lt_trans ht.2 hb₀d⟩
    exact ⟨fun e => h0 (e ▸ subset_closure hi), fun e => h2 (e ▸ subset_closure hi),
      fun e => h4 (e ▸ subset_closure hi)⟩
  
  have hno3 : ∀ t ∈ Ioo a₀ b₀, P t ∉ S 3 := by
    intro t ht h3
    have Cr := C.reverse ha₀T.1.1 ht.1.le (ht.2.le.trans hb₀σ)
    have key := Cr.gl le_rfl ht.1.le le_rfl {3} {0, 1, 5, 6, 7} (by decide)
      (by
        simp only [show a₀ + t - a₀ = t by ring]
        exact subset_closure (Cyc8.mem_U8 (by simp) h3))
      (by
        intro u hu hV'
        set t' := a₀ + t - u with ht'
        have ht'I : t' ∈ Icc a₀ t := ⟨by linarith [hu.2], by linarith [hu.1]⟩
        rcases eq_or_lt_of_le ht'I.1 with h | h
        · rw [← h] at hV'
          obtain ⟨j, hj, hjo⟩ := C.mem_piece_of_closure hV' ha₀T.2
          right
          rw [← h]
          exact Cyc8.mem_U8 ((by decide : ∀ j : Fin 8, (j = 0 ∨ adj8 j 0) →
            j ∈ ({0, 1, 5, 6, 7} : Finset (Fin 8))) j hjo) hj
        · obtain ⟨j, hj⟩ := mem_iUnion.1 (C.hVS ▸ hV')
          have hb := hbase t' ⟨h, lt_of_le_of_lt ht'I.2 ht.2⟩ j hj
          rcases ((by decide : ∀ j : Fin 8, (j ≠ 0 ∧ j ≠ 2 ∧ j ≠ 4) →
              j = 3 ∨ j ∈ ({0, 1, 5, 6, 7} : Finset (Fin 8))) j hb) with hjA | hjB
          · left; exact Cyc8.mem_U8 (by simp [hjA]) hj
          · right; exact Cyc8.mem_U8 hjB hj)
      t ⟨ht.1.le, le_rfl⟩
    apply key
    simp only [show a₀ + t - t = a₀ by ring]
    exact subset_closure_U8 S (by decide) ha₀T.2
  
  refine ⟨a₀, b₀, ha₀T.1.1, ha₀T.1.2, hb₀σ, ha₀T.2, hb₀T.2, ?_⟩
  intro t ht hV'
  obtain ⟨i, hi⟩ := mem_iUnion.1 (C.hVS ▸ hV')
  have hb := hbase t ht i hi
  have hi3 : i ≠ 3 := fun e => hno3 t ht (e ▸ hi)
  by_contra h1
  have hi1 : i ≠ 1 := fun e => h1 (e ▸ hi)
  have hi567 : i ∈ ({5, 6, 7} : Finset (Fin 8)) :=
    (by decide : ∀ i : Fin 8, (i ≠ 0 ∧ i ≠ 2 ∧ i ≠ 4) → i ≠ 3 → i ≠ 1 →
      i ∈ ({5, 6, 7} : Finset (Fin 8))) i hb hi3 hi1
  have Ct := C.restrict (ha₀T.1.1.trans ht.1.le) ht.2.le hb₀σ
  have key := Ct.gl le_rfl ht.2.le le_rfl {5, 6, 7} {1, 2, 3} (by decide)
    (subset_closure (Cyc8.mem_U8 hi567 hi))
    (by
      intro t' ht' hV''
      rcases eq_or_lt_of_le ht'.2 with h | h
      · subst h
        obtain ⟨j, hj, hjo⟩ := C.mem_piece_of_closure hV'' hb₀T.2
        right
        exact Cyc8.mem_U8 ((by decide : ∀ j : Fin 8, (j = 2 ∨ adj8 j 2) →
          j ∈ ({1, 2, 3} : Finset (Fin 8))) j hjo) hj
      · obtain ⟨j, hj⟩ := mem_iUnion.1 (C.hVS ▸ hV'')
        have ht'I : t' ∈ Ioo a₀ b₀ := ⟨lt_of_lt_of_le ht.1 ht'.1, h⟩
        have hb' := hbase t' ht'I j hj
        have hj3 : j ≠ 3 := fun e => hno3 t' ht'I (e ▸ hj)
        rcases ((by decide : ∀ j : Fin 8, (j ≠ 0 ∧ j ≠ 2 ∧ j ≠ 4) → j ≠ 3 →
            j ∈ ({5, 6, 7} : Finset (Fin 8)) ∨ j = 1) j hb' hj3) with hjA | hjB
        · left; exact Cyc8.mem_U8 hjA hj
        · right; exact Cyc8.mem_U8 (by simp [hjB]) hj)
    b₀ ⟨ht.2.le, le_rfl⟩
  exact key (subset_closure_U8 S (by decide) hb₀T.2)

 
theorem adj8_neg (i j : Fin 8) : adj8 (-i) (-j) ↔ adj8 i j := by
  revert i j; decide

 
theorem passage8 {P : ℝ → ℂ} {V : Set ℂ} {S : Fin 8 → Set ℂ} {τ σ δ : ℝ}
    (C : Cyc8 P V S τ σ δ) (hτ : P τ ∈ closure (S 0)) (hσ : P σ ∈ closure (S 4)) :
    (WindowAt P V S τ σ 1 0 2 ∧ WindowAt P V S τ σ 3 2 4) ∨
      (WindowAt P V S τ σ 7 0 6 ∧ WindowAt P V S τ σ 5 6 4) := by
  
  set T4 : Set ℝ := Icc τ σ ∩ P ⁻¹' closure (S 4) with hT4
  have hT4c : IsClosed T4 := C.hP.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closure
  have hT4ne : T4.Nonempty := ⟨σ, ⟨C.hτσ, le_rfl⟩, hσ⟩
  have hT4b : BddBelow T4 := ⟨τ, fun _ h => h.1.1⟩
  set d₀ := sInf T4 with hd₀def
  have hd₀T : d₀ ∈ T4 := hT4c.csInf_mem hT4ne hT4b
  have hbefore : ∀ t ∈ Ico τ d₀, P t ∉ closure (S 4) := by
    intro t ht h
    have : d₀ ≤ t := csInf_le hT4b ⟨⟨ht.1, ht.2.le.trans hd₀T.1.2⟩, h⟩
    linarith [ht.2]
  
  have hA : ∃ t ∈ Icc τ d₀, P t ∈ closure (S 2) ∪ closure (S 6) := by
    by_contra hno
    push Not at hno
    have Cd := C.restrict le_rfl hd₀T.1.1 hd₀T.1.2
    have key := Cd.gl le_rfl hd₀T.1.1 le_rfl {0, 1, 7} {3, 4, 5} (by decide)
      (subset_closure_U8 S (by decide) hτ)
      (by
        intro t ht hV'
        obtain ⟨i, hi⟩ := mem_iUnion.1 (C.hVS ▸ hV')
        have hn := hno t ht
        have hi2 : i ≠ 2 := fun e => hn (Or.inl (e ▸ subset_closure hi))
        have hi6 : i ≠ 6 := fun e => hn (Or.inr (e ▸ subset_closure hi))
        rcases ((by decide : ∀ i : Fin 8, i ≠ 2 → i ≠ 6 →
            i ∈ ({0, 1, 7} : Finset (Fin 8)) ∨ i ∈ ({3, 4, 5} : Finset (Fin 8))) i hi2 hi6)
          with hiA | hiB
        · left; exact Cyc8.mem_U8 hiA hi
        · right; exact Cyc8.mem_U8 hiB hi)
      d₀ ⟨hd₀T.1.1, le_rfl⟩
    exact key (subset_closure_U8 S (by decide) hd₀T.2)
  
  have hPd : ContinuousOn P (Icc τ d₀) := C.hP.mono (Icc_subset_Icc le_rfl hd₀T.1.2)
  set T26 : Set ℝ := Icc τ d₀ ∩ P ⁻¹' (closure (S 2) ∪ closure (S 6)) with hT26
  have hT26c : IsClosed T26 :=
    hPd.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_closure.union isClosed_closure)
  obtain ⟨t₀, ht₀, hPt₀⟩ := hA
  have hT26ne : T26.Nonempty := ⟨t₀, ht₀, hPt₀⟩
  have hT26b : BddAbove T26 := ⟨d₀, fun _ h => h.1.2⟩
  set c₀ := sSup T26 with hc₀def
  have hc₀T : c₀ ∈ T26 := hT26c.csSup_mem hT26ne hT26b
  have hafter : ∀ t ∈ Ioc c₀ d₀, P t ∉ closure (S 2) ∧ P t ∉ closure (S 6) := by
    intro t ht
    have hnot : P t ∉ closure (S 2) ∪ closure (S 6) := by
      intro h
      have : t ≤ c₀ := le_csSup hT26b ⟨⟨hc₀T.1.1.trans ht.1.le, ht.2⟩, h⟩
      linarith [ht.1]
    exact ⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩
  rcases hc₀T.2 with h2 | h6
  · left
    exact case_plus C hτ hd₀T.1 hd₀T.2 hbefore hc₀T.1 h2 hafter
  · right
    
    set S' : Fin 8 → Set ℂ := fun i => S (-i) with hS'
    have C' : Cyc8 P V S' τ σ δ :=
      { hτσ := C.hτσ, hδ := C.hδ, hP := C.hP, hV := C.hV
        hVS := by
          rw [C.hVS]; ext z; simp only [mem_iUnion, hS']
          exact ⟨fun ⟨i, hi⟩ => ⟨-i, by simpa using hi⟩, fun ⟨i, hi⟩ => ⟨-i, hi⟩⟩
        hgap := by
          intro i j hij hadj x hx y hy
          exact C.hgap (-i) (-j) (fun e => hij (neg_injective e))
            (fun h => hadj ((adj8_neg i j).1 h)) x hx y hy
        hjump := C.hjump }
    have e0 : S' 0 = S 0 := by simp [hS']
    have e4 : S' 4 = S 4 := by
      simp only [hS']; congr 1
    have e2 : S' 2 = S 6 := by
      simp only [hS']; congr 1
    have e6 : S' 6 = S 2 := by
      simp only [hS']; congr 1
    have e1 : S' 1 = S 7 := by
      simp only [hS']; congr 1
    have e3 : S' 3 = S 5 := by
      simp only [hS']; congr 1
    have := case_plus C' (by rw [e0]; exact hτ) hd₀T.1 (by rw [e4]; exact hd₀T.2)
      (by rw [e4]; exact hbefore) hc₀T.1 (by rw [e2]; exact h6)
      (by rw [e2, e6]; exact fun t ht => ⟨(hafter t ht).2, (hafter t ht).1⟩)
    obtain ⟨⟨a, b, h1, h2, h3, h4, h5, h6'⟩, ⟨a', b', h1', h2', h3', h4', h5', h6''⟩⟩ := this
    refine ⟨⟨a, b, h1, h2, h3, by rw [← e0]; exact h4, by rw [← e2]; exact h5,
      fun t ht hV => by rw [← e1]; exact h6' t ht hV⟩,
      ⟨a', b', h1', h2', h3', by rw [← e2]; exact h4', by rw [← e4]; exact h5',
      fun t ht hV => by rw [← e3]; exact h6'' t ht hV⟩⟩

 
theorem jump_open {P : ℝ → ℂ} {t₁ t₂ δ : ℝ} {V : Set ℂ}
    (hP : ContinuousOn P (Icc t₁ t₂))
    (hjump : ∀ a b, t₁ ≤ a → b ≤ t₂ → (∀ t ∈ Icc a b, P t ∉ V) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (P s) (P t) < δ)
    {a b : ℝ} (ha : t₁ ≤ a) (hab : a < b) (hb : b ≤ t₂) (hoff : ∀ t ∈ Ioo a b, P t ∉ V) :
    dist (P a) (P b) ≤ δ := by
  by_contra hlt
  push Not at hlt
  set ε := (dist (P a) (P b) - δ) / 3 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have haI : a ∈ Icc t₁ t₂ := ⟨ha, hab.le.trans hb⟩
  have hbI : b ∈ Icc t₁ t₂ := ⟨ha.trans hab.le, hb⟩
  obtain ⟨η₁, hη₁, h₁⟩ := Metric.continuousWithinAt_iff.1 (hP a haI) ε hεpos
  obtain ⟨η₂, hη₂, h₂⟩ := Metric.continuousWithinAt_iff.1 (hP b hbI) ε hεpos
  set η := min (min η₁ η₂) ((b - a) / 3) with hη
  have hηpos : 0 < η := lt_min (lt_min hη₁ hη₂) (by linarith)
  have hη1 : η ≤ η₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : η ≤ η₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : η ≤ (b - a) / 3 := min_le_right _ _
  set a' := a + η / 2
  set b' := b - η / 2
  have ha'b' : a' ≤ b' := by simp only [a', b']; linarith
  have hoff' : ∀ t ∈ Icc a' b', P t ∉ V := fun t ht =>
    hoff t ⟨by simp only [a'] at ht; linarith [ht.1], by simp only [b'] at ht; linarith [ht.2]⟩
  have hd := hjump a' b' (by simp only [a']; linarith) (by simp only [b']; linarith) hoff'
    a' ⟨le_rfl, ha'b'⟩ b' ⟨ha'b', le_rfl⟩
  have hda : dist (P a') (P a) < ε := h₁ ⟨by simp only [a']; linarith,
    by simp only [a']; linarith⟩ (by rw [Real.dist_eq]; simp only [a']; rw [abs_lt]; constructor <;> linarith)
  have hdb : dist (P b') (P b) < ε := h₂ ⟨by simp only [b']; linarith,
    by simp only [b']; linarith⟩ (by rw [Real.dist_eq]; simp only [b']; rw [abs_lt]; constructor <;> linarith)
  have := dist_triangle4 (P a) (P a') (P b') (P b)
  rw [dist_comm (P a) (P a')] at this
  linarith

theorem window_extract {P : ℝ → ℂ} {t₁ t₂ δ g ρ : ℝ} {V A B : Set ℂ} {c : ℂ}
    (h12 : t₁ ≤ t₂) (hδ : 0 < δ) (hP : ContinuousOn P (Icc t₁ t₂))
    (hjump : ∀ a b, t₁ ≤ a → b ≤ t₂ → (∀ t ∈ Icc a b, P t ∉ V) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (P s) (P t) < δ)
    (hA : P t₁ ∈ closure A) (hB : P t₂ ∈ closure B)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, g ≤ dist x y) (hg : 2 * δ < g)
    (hAo : A ⊆ (ball c ρ)ᶜ) (hBo : B ⊆ (ball c ρ)ᶜ)
    (hwin : ∀ t ∈ Ioo t₁ t₂, P t ∈ V → P t ∈ ball c ρ) :
    ∃ a b, t₁ ≤ a ∧ a < b ∧ b ≤ t₂ ∧ dist (P a) c = ρ ∧ dist (P b) c = ρ ∧
      g - 2 * δ ≤ dist (P a) (P b) ∧ (∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c ρ) ∧
      ∀ t ∈ Icc a b, dist (P t) c ≤ ρ + δ := by
  have hdg : g ≤ dist (P t₁) (P t₂) := gap_closure hAB _ hA _ hB
  have hA' : P t₁ ∉ ball c ρ := fun h =>
    (closure_minimal hAo isOpen_ball.isClosed_compl hA) h
  have hB' : P t₂ ∉ ball c ρ := fun h =>
    (closure_minimal hBo isOpen_ball.isClosed_compl hB) h
  set T : Set ℝ := Icc t₁ t₂ ∩ P ⁻¹' closedBall c ρ with hT
  have hTc : IsClosed T := hP.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closedBall
  have h12' : t₁ < t₂ := by
    rcases eq_or_lt_of_le h12 with h | h
    · rw [h, dist_self] at hdg; linarith
    · exact h
  have hTne : T.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hoff : ∀ t ∈ Ioo t₁ t₂, P t ∉ V := by
      intro t ht hV
      have : t ∈ T := ⟨⟨ht.1.le, ht.2.le⟩, ball_subset_closedBall (hwin t ht hV)⟩
      rw [hemp] at this; exact this
    have := jump_open hP hjump le_rfl h12' le_rfl hoff
    linarith
  have hTbb : BddBelow T := ⟨t₁, fun _ h => h.1.1⟩
  have hTba : BddAbove T := ⟨t₂, fun _ h => h.1.2⟩
  set a := sInf T with ha
  set b := sSup T with hb
  have haT : a ∈ T := hTc.csInf_mem hTne hTbb
  have hbT : b ∈ T := hTc.csSup_mem hTne hTba
  have hab : a ≤ b := csInf_le_csSup hTne hTbb hTba
  
  have hbefore : ∀ t ∈ Ico t₁ a, P t ∉ closedBall c ρ := by
    intro t ht h
    have : a ≤ t := csInf_le hTbb ⟨⟨ht.1, ht.2.le.trans haT.1.2⟩, h⟩
    linarith [ht.2]
  have hafter : ∀ t ∈ Ioc b t₂, P t ∉ closedBall c ρ := by
    intro t ht h
    have : t ≤ b := le_csSup hTba ⟨⟨hbT.1.1.trans ht.1.le, ht.2⟩, h⟩
    linarith [ht.1]
  
  have hsph : ∀ t ∈ T, (t = t₁ ∨ ∀ t' ∈ Ico t₁ t, P t' ∉ closedBall c ρ) →
      dist (P t) c = ρ := by
    intro t ht hcase
    have hle : dist (P t) c ≤ ρ := ht.2
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    rcases hcase with h | h
    · rw [h] at hlt; exact hA' (mem_ball.2 hlt)
    · rcases eq_or_lt_of_le ht.1.1 with he | he
      · rw [← he] at hlt; exact hA' (mem_ball.2 hlt)
      · have hcont := hP t ht.1
        obtain ⟨η, hη, hηb⟩ := Metric.continuousWithinAt_iff.1 hcont (ρ - dist (P t) c)
          (by linarith)
        set t' := max t₁ (t - η / 2)
        have ht'I : t' ∈ Ico t₁ t := ⟨le_max_left _ _, max_lt he (by linarith)⟩
        apply h t' ht'I
        have := hηb (x := t') ⟨ht'I.1, ht'I.2.le.trans ht.1.2⟩ (by
          rw [Real.dist_eq, abs_lt]
          constructor
          · have : t - η / 2 ≤ t' := le_max_right _ _
            linarith
          · linarith [ht'I.2])
        rw [mem_closedBall]
        have := dist_triangle (P t') (P t) c
        linarith
  have hsph' : ∀ t ∈ T, (t = t₂ ∨ ∀ t' ∈ Ioc t t₂, P t' ∉ closedBall c ρ) →
      dist (P t) c = ρ := by
    intro t ht hcase
    have hle : dist (P t) c ≤ ρ := ht.2
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    rcases hcase with h | h
    · rw [h] at hlt; exact hB' (mem_ball.2 hlt)
    · rcases eq_or_lt_of_le ht.1.2 with he | he
      · rw [he] at hlt; exact hB' (mem_ball.2 hlt)
      · have hcont := hP t ht.1
        obtain ⟨η, hη, hηb⟩ := Metric.continuousWithinAt_iff.1 hcont (ρ - dist (P t) c)
          (by linarith)
        set t' := min t₂ (t + η / 2)
        have ht'I : t' ∈ Ioc t t₂ := ⟨lt_min he (by linarith), min_le_left _ _⟩
        apply h t' ht'I
        have := hηb (x := t') ⟨ht.1.1.trans ht'I.1.le, ht'I.2⟩ (by
          rw [Real.dist_eq, abs_lt]
          constructor
          · linarith [ht'I.1]
          · have : t' ≤ t + η / 2 := min_le_right _ _
            linarith)
        rw [mem_closedBall]
        have := dist_triangle (P t') (P t) c
        linarith
  have hPa : dist (P a) c = ρ := by
    rcases eq_or_lt_of_le haT.1.1 with h | h
    · exact hsph a haT (Or.inl h.symm)
    · exact hsph a haT (Or.inr hbefore)
  have hPb : dist (P b) c = ρ := by
    rcases eq_or_lt_of_le hbT.1.2 with h | h
    · exact hsph' b hbT (Or.inl h)
    · exact hsph' b hbT (Or.inr hafter)
  
  have hda : dist (P t₁) (P a) ≤ δ := by
    rcases eq_or_lt_of_le haT.1.1 with h | h
    · rw [← h, dist_self]; exact hδ.le
    · apply jump_open hP hjump le_rfl h (haT.1.2)
      intro t ht hV
      exact hbefore t ⟨ht.1.le, ht.2⟩ (ball_subset_closedBall
        (hwin t ⟨ht.1, ht.2.trans_le haT.1.2⟩ hV))
  have hdb : dist (P b) (P t₂) ≤ δ := by
    rcases eq_or_lt_of_le hbT.1.2 with h | h
    · rw [h, dist_self]; exact hδ.le
    · apply jump_open hP hjump hbT.1.1 h le_rfl
      intro t ht hV
      exact hafter t ⟨ht.1, ht.2.le⟩ (ball_subset_closedBall
        (hwin t ⟨lt_of_le_of_lt hbT.1.1 ht.1, ht.2⟩ hV))
  have hdab : g - 2 * δ ≤ dist (P a) (P b) := by
    have := dist_triangle4 (P t₁) (P a) (P b) (P t₂)
    linarith
  have hab' : a < b := by
    rcases eq_or_lt_of_le hab with h | h
    · rw [h, dist_self] at hdab; linarith
    · exact h
  refine ⟨a, b, haT.1.1, hab', hbT.1.2, hPa, hPb, hdab, ?_, ?_⟩
  · intro t ht hV
    exact hwin t ⟨lt_of_le_of_lt haT.1.1 ht.1, lt_of_lt_of_le ht.2 hbT.1.2⟩ hV
  · 
    intro t ht
    by_cases hin : P t ∈ closedBall c ρ
    · have := mem_closedBall.1 hin; linarith
    · set S' : Set ℝ := Icc a t ∩ P ⁻¹' closedBall c ρ with hS'
      have hPat : ContinuousOn P (Icc a t) := hP.mono (Icc_subset_Icc haT.1.1 (ht.2.trans hbT.1.2))
      have hS'c : IsClosed S' := hPat.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closedBall
      have hS'ne : S'.Nonempty := ⟨a, ⟨le_rfl, ht.1⟩, haT.2⟩
      have hS'b : BddAbove S' := ⟨t, fun _ h => h.1.2⟩
      set e := sSup S' with he
      have heS : e ∈ S' := hS'c.csSup_mem hS'ne hS'b
      have het : e < t := by
        rcases eq_or_lt_of_le heS.1.2 with h | h
        · exact absurd (h ▸ heS.2) hin
        · exact h
      have hoff : ∀ t' ∈ Ioo e t, P t' ∉ V := by
        intro t' ht' hV
        have hball := hwin t' ⟨lt_of_le_of_lt (haT.1.1.trans heS.1.1) ht'.1,
          lt_of_lt_of_le ht'.2 (ht.2.trans hbT.1.2)⟩ hV
        have : t' ≤ e := le_csSup hS'b ⟨⟨heS.1.1.trans ht'.1.le, ht'.2.le⟩,
          ball_subset_closedBall hball⟩
        linarith [ht'.1]
      have hd := jump_open hP hjump (haT.1.1.trans heS.1.1) het (ht.2.trans hbT.1.2) hoff
      have := dist_triangle (P t) (P e) c
      rw [dist_comm] at hd
      have hPe := mem_closedBall.1 heS.2
      linarith

end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeLoops

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeChecks

open Set Metric SupercriticalLQGUniqueness.Uniqueness.Objects.TubeLoops

 


def Hit (P : ℝ → ℂ) (V : Set ℂ) (τ σ δ g ρ : ℝ) (c : ℂ) : Prop :=
  ∃ a b, τ ≤ a ∧ a < b ∧ b ≤ σ ∧ dist (P a) c = ρ ∧ dist (P b) c = ρ ∧
    g - 2 * δ ≤ dist (P a) (P b) ∧ (∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c ρ) ∧
    ∀ t ∈ Icc a b, dist (P t) c ≤ ρ + δ

 
theorem hit_of_window {P : ℝ → ℂ} {V : Set ℂ} {S : Fin 8 → Set ℂ} {τ σ δ g ρ : ℝ} {c : ℂ}
    (C : Cyc8 P V S τ σ δ) (hg : 2 * δ < g) {b A B : Fin 8}
    (hb : S b = ball c ρ) (hAB : ∀ x ∈ S A, ∀ y ∈ S B, g ≤ dist x y)
    (hAo : S A ⊆ (ball c ρ)ᶜ) (hBo : S B ⊆ (ball c ρ)ᶜ)
    (hW : WindowAt P V S τ σ b A B) : Hit P V τ σ δ g ρ c := by
  obtain ⟨t₁, t₂, hτ₁, h12, h₂σ, hA, hB, hwin⟩ := hW
  have hP : ContinuousOn P (Icc t₁ t₂) := C.hP.mono (Icc_subset_Icc hτ₁ h₂σ)
  have hjump : ∀ a b, t₁ ≤ a → b ≤ t₂ → (∀ t ∈ Icc a b, P t ∉ V) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (P s) (P t) < δ :=
    fun a b ha hb' => C.hjump a b (hτ₁.trans ha) (hb'.trans h₂σ)
  have hwin' : ∀ t ∈ Ioo t₁ t₂, P t ∈ V → P t ∈ ball c ρ := fun t ht hV => hb ▸ hwin t ht hV
  obtain ⟨a, b', ha, hab, hb', hPa, hPb, hd, hint, hcl⟩ :=
    window_extract h12 C.hδ hP hjump hA hB hAB hg hAo hBo hwin'
  exact ⟨a, b', hτ₁.trans ha, hab, hb'.trans h₂σ, hPa, hPb, hd, hint, hcl⟩

 



theorem L5_compose {P : ℝ → ℂ} {V : Set ℂ} {S : Fin 8 → Set ℂ} {τ σ δ g ρ : ℝ}
    {c₁ c₃ c₅ c₇ : ℂ}
    (C : Cyc8 P V S τ σ δ) (hτ : P τ ∈ closure (S 0)) (hσ : P σ ∈ closure (S 4))
    (hg : 2 * δ < g)
    (hgap : ∀ i j, i ≠ j → ¬ adj8 i j → ∀ x ∈ S i, ∀ y ∈ S j, g ≤ dist x y)
    (h1 : S 1 = ball c₁ ρ) (h3 : S 3 = ball c₃ ρ) (h5 : S 5 = ball c₅ ρ) (h7 : S 7 = ball c₇ ρ)
    (h01 : S 0 ⊆ (ball c₁ ρ)ᶜ) (h21 : S 2 ⊆ (ball c₁ ρ)ᶜ)
    (h23 : S 2 ⊆ (ball c₃ ρ)ᶜ) (h43 : S 4 ⊆ (ball c₃ ρ)ᶜ)
    (h07 : S 0 ⊆ (ball c₇ ρ)ᶜ) (h67 : S 6 ⊆ (ball c₇ ρ)ᶜ)
    (h65 : S 6 ⊆ (ball c₅ ρ)ᶜ) (h45 : S 4 ⊆ (ball c₅ ρ)ᶜ) :
    (Hit P V τ σ δ g ρ c₁ ∧ Hit P V τ σ δ g ρ c₃) ∨
      (Hit P V τ σ δ g ρ c₇ ∧ Hit P V τ σ δ g ρ c₅) := by
  rcases passage8 C hτ hσ with ⟨w1, w3⟩ | ⟨w7, w5⟩
  · exact Or.inl ⟨hit_of_window C hg h1 (hgap 0 2 (by decide) (by decide)) h01 h21 w1,
      hit_of_window C hg h3 (hgap 2 4 (by decide) (by decide)) h23 h43 w3⟩
  · exact Or.inr ⟨hit_of_window C hg h7 (hgap 0 6 (by decide) (by decide)) h07 h67 w7,
      hit_of_window C hg h5 (hgap 6 4 (by decide) (by decide)) h65 h45 w5⟩

 
theorem cyc8_of_gap {P : ℝ → ℂ} {V : Set ℂ} {S : Fin 8 → Set ℂ} {τ σ δ g : ℝ}
    (hτσ : τ ≤ σ) (hδ : 0 < δ) (hP : ContinuousOn P (Icc τ σ)) (hV : IsOpen V)
    (hVS : V = ⋃ i, S i) (hg : 2 * δ < g)
    (hgap : ∀ i j, i ≠ j → ¬ adj8 i j → ∀ x ∈ S i, ∀ y ∈ S j, g ≤ dist x y)
    (hjump : ∀ a b, τ ≤ a → b ≤ σ → (∀ t ∈ Icc a b, P t ∉ V) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (P s) (P t) < δ) :
    Cyc8 P V S τ σ δ where
  hτσ := hτσ
  hδ := hδ
  hP := hP
  hV := hV
  hVS := hVS
  hgap := fun i j hij hadj x hx y hy => (hg.le).trans (hgap i j hij hadj x hx y hy)
  hjump := hjump

 


theorem excursion_endpoints_off {P : ℝ → ℂ} {V : Set ℂ} {c : ℂ} {R a b α β : ℝ}
    (hV : IsOpen V) (hP : ContinuousOn P (Icc a b)) (haα : a ≤ α) (hαβ : α < β) (hβb : β ≤ b)
    (hext : ∀ t ∈ Ioo α β, R < dist (P t) c)
    (hwin : ∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c R) :
    ∀ t ∈ Icc α β, P t ∉ V := by
  
  have hin : ∀ t ∈ Ioo α β, P t ∉ V := by
    intro t ht hPt
    have h1 := hwin t ⟨lt_of_le_of_lt haα ht.1, lt_of_lt_of_le ht.2 hβb⟩ hPt
    rw [mem_ball] at h1
    linarith [hext t ht]
  
  have hnear : ∀ e ∈ Icc α β, P e ∈ V → ∃ ε > 0, ∀ t ∈ Icc a b, dist t e < ε → P t ∈ V := by
    intro e he hPe
    have heI : e ∈ Icc a b := ⟨haα.trans he.1, he.2.trans hβb⟩
    have hmem : P ⁻¹' V ∈ nhdsWithin e (Icc a b) :=
      (hP e heI).preimage_mem_nhdsWithin (hV.mem_nhds hPe)
    rw [Metric.mem_nhdsWithin_iff] at hmem
    obtain ⟨ε, hε, hsub⟩ := hmem
    exact ⟨ε, hε, fun t ht hd => hsub ⟨Metric.mem_ball.2 hd, ht⟩⟩
  intro t ht hPt
  rcases eq_or_lt_of_le ht.1 with h | h
  · 
    obtain ⟨ε, hε, hV'⟩ := hnear t ht hPt
    set t' := min (t + ε / 2) ((α + β) / 2) with ht'
    have h1 : α < t' := lt_min (by linarith) (by linarith)
    have h2 : t' < β := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have h3 : dist t' t < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith
      · have : t' ≤ t + ε / 2 := min_le_left _ _
        linarith
    exact hin t' ⟨h1, h2⟩ (hV' t' ⟨haα.trans h1.le, h2.le.trans hβb⟩ h3)
  · rcases eq_or_lt_of_le ht.2 with h' | h'
    · 
      obtain ⟨ε, hε, hV'⟩ := hnear t ht hPt
      set t' := max (t - ε / 2) ((α + β) / 2) with ht'
      have h1 : α < t' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have h2 : t' < β := max_lt (by linarith) (by linarith)
      have h3 : dist t' t < ε := by
        rw [Real.dist_eq, abs_lt]
        constructor
        · have : t - ε / 2 ≤ t' := le_max_left _ _
          linarith
        · linarith
      exact hin t' ⟨h1, h2⟩ (hV' t' ⟨haα.trans h1.le, h2.le.trans hβb⟩ h3)
    · exact hin t ⟨h, h'⟩ hPt

end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeChecks

