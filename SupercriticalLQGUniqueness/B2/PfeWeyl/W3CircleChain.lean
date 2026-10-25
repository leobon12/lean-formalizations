import SupercriticalLQGUniqueness.B2.PfeWeyl.W3CircleSegment

 















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
theorem exists_pos_le_finset (s : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ j ∈ s, 0 < a j) :
    ∃ g : ℝ, 0 < g ∧ ∀ j ∈ s, g ≤ a j := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun j hj => absurd hj (Finset.notMem_empty j)⟩
  | insert i s hi ih =>
    obtain ⟨g, hg, hgs⟩ := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    refine ⟨min g (a i), lt_min hg (ha i (Finset.mem_insert_self i s)), fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hgs j hj)

 
theorem exists_circle_curve (D : LSCMetric) (hDforget : Continuous (euclidForget D))
    (ξ : ℝ) (f : C(ℂ, ℝ)) {O O' : Set ℂ} (hOc : IsClosed O) (hO'c : IsClosed O')
    (hdisj : Disjoint O O') {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O')
    (hfin : weylScale ξ f D (x, y) ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : ℝ → ℂ) (L t₀ t₁ : ℝ), D.IsCurve P 0 L ∧
      HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L) ∧ 0 ≤ t₀ ∧ t₀ < t₁ ∧ t₁ ≤ L ∧
      P t₀ ∈ O ∧ P t₁ ∈ O' ∧ (∀ s ∈ Ioo t₀ t₁, P s ∉ O ∧ P s ∉ O') ∧
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) <
        weylScale ξ f D (x, y) + ENNReal.ofReal ε := by
  obtain ⟨P, L, hP, hu, hP0, hPL, hcost⟩ := exists_near_min_weyl_curve D ξ f x y hfin hε
  have hPc := continuousOn_of_isCurve_of_forget D hDforget hP
  have hL : 0 ≤ L := hP.1
  
  set T' : Set ℝ := Icc 0 L ∩ P ⁻¹' O' with hT'def
  have hT'c : IsClosed T' := hPc.preimage_isClosed_of_isClosed isClosed_Icc hO'c
  have hT'ne : T'.Nonempty := ⟨L, ⟨hL, le_rfl⟩, by simp only [mem_preimage, hPL]; exact hy⟩
  have hT'b : BddBelow T' := ⟨0, fun t ht => ht.1.1⟩
  set t₁ := sInf T' with ht₁def
  have ht₁ : t₁ ∈ T' := hT'c.csInf_mem hT'ne hT'b
  
  set T : Set ℝ := Icc 0 t₁ ∩ P ⁻¹' O with hTdef
  have hT₁L : Icc 0 t₁ ⊆ Icc 0 L := Icc_subset_Icc le_rfl ht₁.1.2
  have hTc : IsClosed T := (hPc.mono hT₁L).preimage_isClosed_of_isClosed isClosed_Icc hOc
  have hTne : T.Nonempty := ⟨0, ⟨le_rfl, ht₁.1.1⟩, by simp only [mem_preimage, hP0]; exact hx⟩
  have hTb : BddAbove T := ⟨t₁, fun t ht => ht.1.2⟩
  set t₀ := sSup T with ht₀def
  have ht₀ : t₀ ∈ T := hTc.csSup_mem hTne hTb
  have ht₀t₁ : t₀ < t₁ := by
    rcases ht₀.1.2.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 : P t₀ ∈ O := ht₀.2
      have h2 : P t₁ ∈ O' := ht₁.2
      rw [h] at h1
      exact Set.disjoint_left.1 hdisj h1 h2
  refine ⟨P, L, t₀, t₁, hP, hu, ht₀.1.1, ht₀t₁, ht₁.1.2, ht₀.2, ht₁.2, ?_, hcost⟩
  intro s hs
  constructor
  · intro hsO
    have hsT : s ∈ T := ⟨⟨(ht₀.1.1.trans hs.1.le), hs.2.le⟩, hsO⟩
    exact absurd (le_csSup hTb hsT) (not_le.2 hs.1)
  · intro hsO'
    have hsT' : s ∈ T' := ⟨⟨(ht₀.1.1.trans hs.1.le), hs.2.le.trans ht₁.1.2⟩, hsO'⟩
    exact absurd (csInf_le hT'b hsT') (not_le.2 hs.2)

 

theorem exists_circle_chain_of_curve (D : LSCMetric) (hDforget : Continuous (euclidForget D))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) {O O' : Set ℂ} (hdisj : Disjoint O O')
    {P : ℝ → ℂ} {L t₀ t₁ : ℝ} (hP : D.IsCurve P 0 L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) (ht₀ : 0 ≤ t₀) (ht₀₁ : t₀ < t₁)
    (ht₁ : t₁ ≤ L) (hP₀ : P t₀ ∈ O) (hP₁ : P t₁ ∈ O')
    (hint : ∀ s ∈ Ioo t₀ t₁, P s ∉ O ∧ P s ∉ O')
    {θ δ : ℝ} (hδ : 0 < δ)
    (hosc : ∀ u ∈ P '' Icc 0 L, ∀ u' ∈ P '' Icc 0 L,
      D (u, u') ≤ ENNReal.ofReal δ → |f u - f u'| < θ) :
    ∃ (N : ℕ) (v : ℕ → ℂ), 2 ≤ N ∧ v 0 ∈ O ∧ v N ∈ O' ∧
      (∀ j, 0 < j → j < N → v j ∉ O ∧ v j ∉ O') ∧
      (∀ j < N, v j ≠ v (j + 1)) ∧
      (∀ j ≤ N, v j ∈ P '' Icc 0 L) ∧
      (∀ j < N, D (v j, v (j + 1)) ≤ ENNReal.ofReal δ) ∧
      (∑ j ∈ Finset.range N, chainWeightMinus ξ f θ (v j) * D (v j, v (j + 1))) ≤
        ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
  
  set N₀ : ℕ := ⌈(t₁ - t₀) / δ⌉₊ + 2 with hN₀def
  have hN₀ : 2 ≤ N₀ := Nat.le_add_left 2 _
  have hN₀pos : (0 : ℝ) < N₀ := by exact_mod_cast (lt_of_lt_of_le two_pos hN₀)
  set step : ℝ := (t₁ - t₀) / N₀ with hstepdef
  have hstep0 : 0 < step := div_pos (by linarith) hN₀pos
  have hstepδ : step ≤ δ := by
    rw [hstepdef, div_le_iff₀ hN₀pos]
    have h1 : (t₁ - t₀) / δ ≤ (⌈(t₁ - t₀) / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(t₁ - t₀) / δ⌉₊ : ℝ) ≤ N₀ := by
      simp only [hN₀def, Nat.cast_add, Nat.cast_ofNat]
      linarith
    have h3 := h1.trans h2
    rw [div_le_iff₀ hδ] at h3
    linarith
  set t : ℕ → ℝ := fun i => t₀ + i * step with htdef
  have htmono : Monotone t := fun i j hij => by
    simp only [htdef]
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    nlinarith
  have ht0 : t 0 = t₀ := by simp [htdef]
  have htN : t N₀ = t₁ := by
    simp only [htdef, hstepdef]
    field_simp
    ring
  have htmem : ∀ i ≤ N₀, t i ∈ Icc 0 L := by
    intro i hi
    have hi' : (i : ℝ) ≤ N₀ := by exact_mod_cast hi
    have h1 : t i ≤ t N₀ := htmono hi
    rw [htN] at h1
    have h0 : t₀ ≤ t i := by
      show t₀ ≤ t₀ + i * step
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hstep0.le)
    exact ⟨ht₀.trans h0, h1.trans ht₁⟩
  have htint : ∀ i, 0 < i → i < N₀ → t i ∈ Ioo t₀ t₁ := by
    intro i hi0 hiN
    have hi0' : (0 : ℝ) < i := by exact_mod_cast hi0
    have hiN' : (i : ℝ) < N₀ := by exact_mod_cast hiN
    refine ⟨by simp only [htdef]; nlinarith, ?_⟩
    have : t i < t N₀ := by simp only [htdef]; nlinarith
    rwa [htN] at this
  have hstepeq : ∀ i, t (i + 1) - t i = step := by
    intro i
    simp only [htdef]
    push_cast
    ring
  have hlenstep : ∀ i < N₀, D.len P (t i) (t (i + 1)) ≤ ENNReal.ofReal δ := by
    intro i hi
    have h := (hasUnitSpeedOn_iff D P L).1 hu (t i) (htmem i hi.le) (t (i + 1))
      (htmem (i + 1) hi) (htmono (Nat.le_succ i))
    rw [h, hstepeq]
    exact ENNReal.ofReal_le_ofReal hstepδ
  set v : ℕ → ℂ := fun i => P (t i) with hvdef
  have hfield : ∀ j < N₀, ∀ s ∈ Icc (t j) (t (j + 1)), f (P (t j)) - θ ≤ f (P s) := by
    intro j hj s hs
    have hsmem : s ∈ Icc 0 L :=
      ⟨(htmem j hj.le).1.trans hs.1, hs.2.trans (htmem (j + 1) hj).2⟩
    have hD : D (P (t j), P s) ≤ ENNReal.ofReal δ :=
      (LSCMetric.apply_le_len D P hs.1).trans
        ((len_mono_Icc D P le_rfl hs.2).trans (hlenstep j hj))
    have := hosc _ (mem_image_of_mem P (htmem j hj.le)) _ (mem_image_of_mem P hsmem) hD
    linarith [(abs_sub_lt_iff.1 this).1]
  have hchain := weighted_chain_le_weyl_cost_sub D ξ hξ f hDforget hP hu t htmono N₀
    (by rw [ht0]; exact ht₀) (by rw [htN]; exact ht₁) θ hfield
  have hvint : ∀ i, 0 < i → i < N₀ → v i ∉ O ∧ v i ∉ O' := fun i h0 hN =>
    hint _ (htint i h0 hN)
  have hv0 : v 0 ∈ O := by simp only [hvdef]; rw [ht0]; exact hP₀
  have hvN : v N₀ ∈ O' := by simp only [hvdef]; rw [htN]; exact hP₁
  
  obtain ⟨N, w, hNN₀, hw0, hwN, hdist, hpair, hidx, hsum⟩ := exists_dedup_chain_idx v N₀
  have hw0O : w 0 ∈ O := hw0 ▸ hv0
  have hwNO' : w N ∈ O' := hwN ▸ hvN
  have hN2 : 2 ≤ N := by
    by_contra hlt
    push Not at hlt
    interval_cases N
    · exact Set.disjoint_left.1 hdisj hw0O hwNO'
    · obtain ⟨i, hi, h1, h2⟩ := hpair 0 one_pos
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0
        have h1N : 1 < N₀ := hN₀
        exact (hvint 1 one_pos h1N).2 (h2 ▸ hwNO')
      · exact (hvint i hi0 hi).1 (h1 ▸ hw0O)
  refine ⟨N, w, hN2, hw0O, hwNO', ?_, hdist, ?_, ?_, ?_⟩
  · intro j hj0 hjN
    obtain ⟨i, hi, h1, h2, h3⟩ := hidx j hjN.le
    rw [h1]
    exact hvint i (h2 hj0) (h3 hjN)
  · intro j hj
    obtain ⟨i, hi, h1, -⟩ := hidx j hj
    rw [h1]
    exact mem_image_of_mem P (htmem i hi)
  · intro j hj
    obtain ⟨i, hi, h1, h2⟩ := hpair j hj
    rw [h1, h2]
    exact (LSCMetric.apply_le_len D P (htmono (Nat.le_succ i))).trans (hlenstep i hi)
  · exact (hsum fun a b => chainWeightMinus ξ f θ a * D (a, b)).trans hchain

end SupercriticalLQGUniqueness.B2.PfeWeyl
