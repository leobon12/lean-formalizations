import LQGMetric.Metric.Geodesic
import SLUMetricAPI2




 






















set_option autoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

open LQGMetric.MetricGeometry (curveLength curveLength_add curveLength_congr curveLength_concat
  continuousOn_concat curveLength_comp_of_monotoneOn curveLength_reverse)

section Generic

variable {X : Type*} [PseudoEMetricSpace X]

 
structure ICurve (X : Type*) [PseudoEMetricSpace X] where
   
  γ : ℝ → X
   
  a : ℝ
   
  b : ℝ
  le : a ≤ b
  cont : ContinuousOn γ (Icc a b)

namespace ICurve

 
def trace (c : ICurve X) : Set X := c.γ '' Icc c.a c.b

 
def len (c : ICurve X) : ℝ≥0∞ := curveLength c.γ c.a c.b

 
def src (c : ICurve X) : X := c.γ c.a

 
def tgt (c : ICurve X) : X := c.γ c.b

 
def restr (c : ICurve X) (s t : ℝ) (hs : c.a ≤ s) (hst : s ≤ t) (ht : t ≤ c.b) : ICurve X where
  γ := c.γ
  a := s
  b := t
  le := hst
  cont := c.cont.mono (Icc_subset_Icc hs ht)

 
def rev (c : ICurve X) : ICurve X where
  γ := fun t => c.γ (c.a + c.b - t)
  a := c.a
  b := c.b
  le := c.le
  cont := by
    refine c.cont.comp (by fun_prop : Continuous fun t : ℝ => c.a + c.b - t).continuousOn ?_
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

 
theorem image_shift_Icc (b₁ a₂ b₂ : ℝ) :
    (fun t : ℝ => t - b₁ + a₂) '' Icc b₁ (b₁ + (b₂ - a₂)) = Icc a₂ b₂ := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro hy
    exact ⟨y - a₂ + b₁, ⟨by linarith [hy.1], by linarith [hy.2]⟩, by ring⟩

 
def append (c₁ c₂ : ICurve X) (h : c₁.tgt = c₂.src) : ICurve X where
  γ := fun t => if t ≤ c₁.b then c₁.γ t else c₂.γ (t - c₁.b + c₂.a)
  a := c₁.a
  b := c₁.b + (c₂.b - c₂.a)
  le := by linarith [c₁.le, c₂.le]
  cont := by
    have hsh : ContinuousOn (fun t => c₂.γ (t - c₁.b + c₂.a))
        (Icc c₁.b (c₁.b + (c₂.b - c₂.a))) := by
      refine c₂.cont.comp (by fun_prop : Continuous fun t : ℝ => t - c₁.b + c₂.a).continuousOn ?_
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hj : c₁.γ c₁.b = c₂.γ (c₁.b - c₁.b + c₂.a) := by
      rw [sub_self, zero_add]
      exact h
    exact continuousOn_concat c₁.le (by linarith [c₂.le]) hj c₁.cont hsh

theorem trace_restr (c : ICurve X) {s t : ℝ} (hs : c.a ≤ s) (hst : s ≤ t) (ht : t ≤ c.b) :
    (c.restr s t hs hst ht).trace ⊆ c.trace :=
  image_mono (Icc_subset_Icc hs ht)

theorem trace_restr_union (c : ICurve X) {s : ℝ} (hs : c.a ≤ s) (ht : s ≤ c.b) :
    (c.restr c.a s le_rfl hs ht).trace ∪ (c.restr s c.b hs ht le_rfl).trace = c.trace := by
  simp only [trace, restr]
  rw [← image_union, Icc_union_Icc_eq_Icc hs ht]

theorem len_restr_add (c : ICurve X) {s : ℝ} (hs : c.a ≤ s) (ht : s ≤ c.b) :
    (c.restr c.a s le_rfl hs ht).len + (c.restr s c.b hs ht le_rfl).len = c.len := by
  simp only [len, restr]
  exact curveLength_add c.γ hs ht

@[simp] theorem src_restr (c : ICurve X) {s t : ℝ} (hs : c.a ≤ s) (hst : s ≤ t) (ht : t ≤ c.b) :
    (c.restr s t hs hst ht).src = c.γ s := rfl

@[simp] theorem tgt_restr (c : ICurve X) {s t : ℝ} (hs : c.a ≤ s) (hst : s ≤ t) (ht : t ≤ c.b) :
    (c.restr s t hs hst ht).tgt = c.γ t := rfl

theorem trace_rev (c : ICurve X) : c.rev.trace = c.trace := by
  simp only [trace, rev]
  have himg : (fun t : ℝ => c.a + c.b - t) '' Icc c.a c.b = Icc c.a c.b := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · intro hy
      exact ⟨c.a + c.b - y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by ring⟩
  rw [show (fun t => c.γ (c.a + c.b - t)) = c.γ ∘ (fun t : ℝ => c.a + c.b - t) from rfl,
    image_comp, himg]

theorem len_rev (c : ICurve X) : c.rev.len = c.len := by
  simp only [len, rev]
  exact curveLength_reverse c.γ c.le

@[simp] theorem src_rev (c : ICurve X) : c.rev.src = c.tgt := by
  simp only [src, tgt, rev]
  congr 1
  ring

@[simp] theorem tgt_rev (c : ICurve X) : c.rev.tgt = c.src := by
  simp only [src, tgt, rev]
  congr 1
  ring

theorem trace_append (c₁ c₂ : ICurve X) (h : c₁.tgt = c₂.src) :
    (c₁.append c₂ h).trace = c₁.trace ∪ c₂.trace := by
  have hb : c₁.b ≤ c₁.b + (c₂.b - c₂.a) := by linarith [c₂.le]
  simp only [trace, append]
  rw [← Icc_union_Icc_eq_Icc c₁.le hb, image_union]
  congr 1
  · refine image_congr fun t ht => ?_
    simp only [ht.2, ite_true]
  · rw [← image_shift_Icc c₁.b c₂.a c₂.b, ← image_comp]
    refine image_congr fun t ht => ?_
    rcases eq_or_lt_of_le ht.1 with heq | hlt
    · subst heq
      simp only [le_refl, ite_true, Function.comp_apply, sub_self, zero_add]
      exact h
    · simp only [not_le.2 hlt, ite_false, Function.comp_apply]

theorem len_append (c₁ c₂ : ICurve X) (h : c₁.tgt = c₂.src) :
    (c₁.append c₂ h).len = c₁.len + c₂.len := by
  have hb : c₁.b ≤ c₁.b + (c₂.b - c₂.a) := by linarith [c₂.le]
  have hj : c₁.γ c₁.b = c₂.γ (c₁.b - c₁.b + c₂.a) := by
    rw [sub_self, zero_add]
    exact h
  simp only [len, append]
  rw [curveLength_concat (Q := fun t => c₂.γ (t - c₁.b + c₂.a)) c₁.le hb hj]
  congr 1
  have hmono : MonotoneOn (fun t : ℝ => t - c₁.b + c₂.a) (Icc c₁.b (c₁.b + (c₂.b - c₂.a))) :=
    fun x _ y _ hxy => by simp only; linarith
  exact curveLength_comp_of_monotoneOn c₂.γ hmono (image_shift_Icc c₁.b c₂.a c₂.b)

@[simp] theorem src_append (c₁ c₂ : ICurve X) (h : c₁.tgt = c₂.src) :
    (c₁.append c₂ h).src = c₁.src := by
  simp only [src, append, c₁.le, ite_true]

@[simp] theorem tgt_append (c₁ c₂ : ICurve X) (h : c₁.tgt = c₂.src) :
    (c₁.append c₂ h).tgt = c₂.tgt := by
  simp only [tgt, append]
  by_cases hle : c₁.b + (c₂.b - c₂.a) ≤ c₁.b
  · have hab : c₂.b = c₂.a := le_antisymm (by linarith) c₂.le
    rw [ite_eq_left hle]
    have ht : c₁.b + (c₂.b - c₂.a) = c₁.b := by rw [hab, sub_self, add_zero]
    rw [ht, hab]
    exact h
  · rw [ite_eq_right hle]
    congr 1
    ring

 

def excursion (c : ICurve X) (s₀ : ℝ) (hs : c.a ≤ s₀) (ht : s₀ ≤ c.b) : ICurve X :=
  let c₁ := c.restr c.a s₀ le_rfl hs ht
  let c₂ := c.restr s₀ c.b hs ht le_rfl
  (c₁.rev.append c₁ (by rw [tgt_rev])).append (c₂.append c₂.rev (by rw [src_rev]))
    (by simp only [tgt_append, src_append, c₁, c₂, tgt_restr, src_restr])

theorem src_excursion (c : ICurve X) (s₀ : ℝ) (hs : c.a ≤ s₀) (ht : s₀ ≤ c.b) :
    (c.excursion s₀ hs ht).src = c.γ s₀ := by
  simp only [excursion, src_append, src_rev, tgt_restr]

theorem tgt_excursion (c : ICurve X) (s₀ : ℝ) (hs : c.a ≤ s₀) (ht : s₀ ≤ c.b) :
    (c.excursion s₀ hs ht).tgt = c.γ s₀ := by
  simp only [excursion, tgt_append, tgt_rev, src_restr]

theorem trace_excursion (c : ICurve X) (s₀ : ℝ) (hs : c.a ≤ s₀) (ht : s₀ ≤ c.b) :
    (c.excursion s₀ hs ht).trace = c.trace := by
  simp only [excursion, trace_append, trace_rev, union_self]
  exact trace_restr_union c hs ht

theorem len_excursion (c : ICurve X) (s₀ : ℝ) (hs : c.a ≤ s₀) (ht : s₀ ≤ c.b) :
    (c.excursion s₀ hs ht).len = 2 * c.len := by
  simp only [excursion, len_append, len_rev]
  rw [← len_restr_add c hs ht, two_mul]
  ring

 

theorem exists_insert (Tr c : ICurve X) {x : X} (hxTr : x ∈ Tr.trace) (hxc : x ∈ c.trace) :
    ∃ Tr' : ICurve X, Tr'.trace = Tr.trace ∪ c.trace ∧ Tr'.len ≤ Tr.len + 2 * c.len := by
  obtain ⟨t₀, ht₀, rfl⟩ := hxTr
  obtain ⟨s₀, hs₀, hcs⟩ := hxc
  let e := c.excursion s₀ hs₀.1 hs₀.2
  let Tr₁ := Tr.restr Tr.a t₀ le_rfl ht₀.1 ht₀.2
  let Tr₂ := Tr.restr t₀ Tr.b ht₀.1 ht₀.2 le_rfl
  have h₁ : Tr₁.tgt = e.src := by
    simp only [Tr₁, e, tgt_restr, src_excursion]
    exact hcs.symm
  have h₂ : (Tr₁.append e h₁).tgt = Tr₂.src := by
    simp only [tgt_append, e, tgt_excursion, Tr₂, src_restr]
    exact hcs
  refine ⟨(Tr₁.append e h₁).append Tr₂ h₂, ?_, ?_⟩
  · rw [trace_append, trace_append, trace_excursion, ← trace_restr_union Tr ht₀.1 ht₀.2]
    simp only [Tr₁, Tr₂]
    rw [union_right_comm]
  · rw [len_append, len_append, len_excursion, ← len_restr_add Tr ht₀.1 ht₀.2]
    simp only [Tr₁, Tr₂]
    rw [add_right_comm]

end ICurve

open ICurve

 

theorem exists_crossing_step {ι : Type*} {R : ι → ι → Prop} {J : Set ι} {i₀ k : ι}
    (h : Relation.ReflTransGen R i₀ k) (hi₀ : i₀ ∈ J) (hk : k ∉ J) :
    ∃ j k', j ∈ J ∧ k' ∉ J ∧ R j k' := by
  induction h with
  | refl => exact absurd hi₀ hk
  | @tail b c' _ hbc ih =>
    by_cases hb : b ∈ J
    · exact ⟨b, c', hb, hk, hbc⟩
    · exact ih hb

 


theorem exists_tour {ι : Type*} [DecidableEq ι] (I : Finset ι) (c : ι → ICurve X) {i₀ : ι}
    (hi₀ : i₀ ∈ I)
    (hconn : ∀ i ∈ I, Relation.ReflTransGen
      (fun i j => i ∈ I ∧ j ∈ I ∧ ((c i).trace ∩ (c j).trace).Nonempty) i₀ i) :
    ∃ Tr : ICurve X, Tr.trace = ⋃ i ∈ I, (c i).trace ∧ Tr.len ≤ 2 * ∑ i ∈ I, (c i).len := by
  suffices H : ∀ n : ℕ, ∀ J : Finset ι, J ⊆ I → i₀ ∈ J → (I \ J).card = n →
      (∃ Tr : ICurve X, Tr.trace = ⋃ i ∈ J, (c i).trace ∧ Tr.len ≤ 2 * ∑ i ∈ J, (c i).len) →
      ∃ Tr : ICurve X, Tr.trace = ⋃ i ∈ I, (c i).trace ∧ Tr.len ≤ 2 * ∑ i ∈ I, (c i).len by
    refine H _ {i₀} (Finset.singleton_subset_iff.2 hi₀) (Finset.mem_singleton_self i₀) rfl
      ⟨c i₀, ?_, ?_⟩
    · simp only [Finset.mem_singleton, iUnion_iUnion_eq_left]
    · rw [Finset.sum_singleton]
      calc (c i₀).len = 1 * (c i₀).len := (one_mul _).symm
        _ ≤ 2 * (c i₀).len := by gcongr; norm_num
  intro n
  induction n with
  | zero =>
    intro J hJI _ hcard hTr
    have hIJ : I ⊆ J := Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hcard)
    have hJ : J = I := Finset.Subset.antisymm hJI hIJ
    rw [← hJ]
    exact hTr
  | succ n ih =>
    intro J hJI hi₀J hcard ⟨Tr, hTrt, hTrl⟩
    have hne : (I \ J).Nonempty := by
      rw [← Finset.card_pos, hcard]
      exact Nat.succ_pos n
    obtain ⟨k, hk⟩ := hne
    rw [Finset.mem_sdiff] at hk
    obtain ⟨j, k', hjJ, hk'J, hjk'⟩ :=
      exists_crossing_step (J := (J : Set ι)) (hconn k hk.1) (Finset.mem_coe.2 hi₀J) hk.2
    obtain ⟨-, hk'I, x, hxj, hxk'⟩ := hjk'
    have hxTr : x ∈ Tr.trace := by
      rw [hTrt]
      exact mem_biUnion (Finset.mem_coe.1 hjJ) hxj
    obtain ⟨Tr', hTr't, hTr'l⟩ := exists_insert Tr (c k') hxTr hxk'
    have hk'J' : k' ∉ J := hk'J
    refine ih (insert k' J) (Finset.insert_subset hk'I hJI) (Finset.mem_insert_of_mem hi₀J) ?_
      ⟨Tr', ?_, ?_⟩
    · have hmem : k' ∈ I \ J := Finset.mem_sdiff.2 ⟨hk'I, hk'J'⟩
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem hmem, hcard]
      rfl
    · rw [hTr't, hTrt, Finset.set_biUnion_insert, union_comm]
    · rw [Finset.sum_insert hk'J', mul_add]
      calc Tr'.len ≤ Tr.len + 2 * (c k').len := hTr'l
        _ ≤ 2 * ∑ i ∈ J, (c i).len + 2 * (c k').len := by gcongr
        _ = 2 * (c k').len + 2 * ∑ i ∈ J, (c i).len := add_comm _ _

end Generic

 

theorem reflTransGen_of_isPreconnected {Y : Type*} [TopologicalSpace Y] {ι : Type*}
    (I : Finset ι) (T : ι → Set Y) (hT : ∀ i ∈ I, IsClosed (T i))
    (hne : ∀ i ∈ I, (T i).Nonempty) (hpre : IsPreconnected (⋃ i ∈ I, T i)) {i₀ : ι}
    (hi₀ : i₀ ∈ I) :
    ∀ i ∈ I, Relation.ReflTransGen (fun i j => i ∈ I ∧ j ∈ I ∧ (T i ∩ T j).Nonempty) i₀ i := by
  classical
  set R : ι → ι → Prop := fun i j => i ∈ I ∧ j ∈ I ∧ (T i ∩ T j).Nonempty with hR
  set JA : Finset ι := I.filter fun j => Relation.ReflTransGen R i₀ j with hJA
  set JB : Finset ι := I.filter fun j => ¬ Relation.ReflTransGen R i₀ j with hJB
  set A : Set Y := ⋃ i ∈ JA, T i with hA
  set B : Set Y := ⋃ i ∈ JB, T i with hB
  have hAc : IsClosed A :=
    isClosed_biUnion_finset fun i hi => hT i (Finset.mem_filter.1 hi).1
  have hBc : IsClosed B :=
    isClosed_biUnion_finset fun i hi => hT i (Finset.mem_filter.1 hi).1
  have hsub : (⋃ i ∈ I, T i) ⊆ A ∪ B := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx
    by_cases hr : Relation.ReflTransGen R i₀ i
    · exact Or.inl (mem_iUnion₂.2 ⟨i, Finset.mem_filter.2 ⟨hi, hr⟩, hxi⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨i, Finset.mem_filter.2 ⟨hi, hr⟩, hxi⟩)
  have hdisj : (⋃ i ∈ I, T i) ∩ (A ∩ B) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro _ hxA hxB
    obtain ⟨a, haA, hxa⟩ := mem_iUnion₂.1 hxA
    obtain ⟨b, hbB, hxb⟩ := mem_iUnion₂.1 hxB
    obtain ⟨haI, hra⟩ := Finset.mem_filter.1 haA
    obtain ⟨hbI, hrb⟩ := Finset.mem_filter.1 hbB
    exact hrb (hra.tail ⟨haI, hbI, x, hxa, hxb⟩)
  have hi₀A : T i₀ ⊆ A := fun x hx =>
    mem_iUnion₂.2 ⟨i₀, Finset.mem_filter.2 ⟨hi₀, Relation.ReflTransGen.refl⟩, hx⟩
  have hI : ∀ i ∈ I, T i ⊆ ⋃ j ∈ I, T j := fun i hi x hx => mem_iUnion₂.2 ⟨i, hi, hx⟩
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hpre A B hAc hBc hsub hdisj with hA' | hB'
  · intro i hi
    by_contra hni
    obtain ⟨x, hx⟩ := hne i hi
    have hxB : x ∈ B := mem_iUnion₂.2 ⟨i, Finset.mem_filter.2 ⟨hi, hni⟩, hx⟩
    have hxA : x ∈ A := hA' (hI i hi hx)
    have : x ∈ (⋃ i ∈ I, T i) ∩ (A ∩ B) := ⟨hI i hi hx, hxA, hxB⟩
    rw [hdisj] at this
    exact this
  · intro i _
    exfalso
    obtain ⟨x, hx⟩ := hne i₀ hi₀
    have : x ∈ (⋃ i ∈ I, T i) ∩ (A ∩ B) := ⟨hI i₀ hi₀ hx, hi₀A hx, hB' (hI i₀ hi₀ hx)⟩
    rw [hdisj] at this
    exact this

section LSC

 
theorem reflTransGen_mono' {α : Type*} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b)
    {a b : α} (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

 
def ofCurve (D : LSCMetric) (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b) : ICurve D.Space where
  γ := D.pt ∘ P
  a := a
  b := b
  le := hP.1
  cont := hP.2

 


theorem exists_curve_tour (D : LSCMetric) {ι : Type*} [DecidableEq ι] (I : Finset ι) {i₀ : ι}
    (hi₀ : i₀ ∈ I) (P : ι → ℝ → ℂ) (a b : ι → ℝ) (hP : ∀ i ∈ I, D.IsCurve (P i) (a i) (b i))
    (hconn : ∀ i ∈ I, Relation.ReflTransGen (fun i j => i ∈ I ∧ j ∈ I ∧
      (P i '' Icc (a i) (b i) ∩ P j '' Icc (a j) (b j)).Nonempty) i₀ i) :
    ∃ (Tr : ℝ → ℂ) (s t : ℝ), D.IsCurve Tr s t ∧
      Tr '' Icc s t = ⋃ i ∈ I, P i '' Icc (a i) (b i) ∧
      D.len Tr s t ≤ 2 * ∑ i ∈ I, D.len (P i) (a i) (b i) := by
  classical
  let c : ι → ICurve D.Space := fun i =>
    if h : i ∈ I then ofCurve D (P i) (a i) (b i) (hP i h)
    else ⟨fun _ => D.pt 0, 0, 0, le_rfl, continuousOn_const⟩
  have hc : ∀ i (hi : i ∈ I), c i = ofCurve D (P i) (a i) (b i) (hP i hi) := by
    intro i hi
    simp only [c]
    exact dite_eq_left hi
  have htr : ∀ i ∈ I, (c i).trace = P i '' Icc (a i) (b i) := by
    intro i hi
    rw [hc i hi]
    rfl
  have hlen : ∀ i ∈ I, (c i).len = D.len (P i) (a i) (b i) := by
    intro i hi
    rw [hc i hi]
    rfl
  have hconn' : ∀ i ∈ I, Relation.ReflTransGen
      (fun i j => i ∈ I ∧ j ∈ I ∧ ((c i).trace ∩ (c j).trace).Nonempty) i₀ i := by
    intro i hi
    refine reflTransGen_mono' ?_ (hconn i hi)
    rintro u v ⟨hu, hv, hne⟩
    refine ⟨hu, hv, ?_⟩
    rw [htr u hu, htr v hv]
    exact hne
  obtain ⟨Tr, hTrt, hTrl⟩ := exists_tour I c hi₀ hconn'
  refine ⟨fun t => (Tr.γ t : ℂ), Tr.a, Tr.b, ⟨Tr.le, Tr.cont⟩, ?_, ?_⟩
  · change Tr.trace = _
    rw [hTrt]
    refine iUnion₂_congr fun i hi => ?_
    rw [htr i hi]
  · change Tr.len ≤ _
    rw [← Finset.sum_congr rfl hlen]
    exact hTrl

end LSC

end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
