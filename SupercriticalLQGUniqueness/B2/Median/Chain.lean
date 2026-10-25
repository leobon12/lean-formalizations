import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Tour

 










set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

open Uniqueness.Objects.AnnulusTails
open Uniqueness.Objects.AnnulusTails.ICurve

section Generic

variable {X : Type*} [PseudoEMetricSpace X]

 
theorem icurve_exists_subarc (c : ICurve X) {x y : X} (hx : x ∈ c.trace)
    (hy : y ∈ c.trace) :
    ∃ e : ICurve X, e.src = x ∧ e.tgt = y ∧ e.trace ⊆ c.trace ∧ e.len ≤ c.len := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  rcases le_total s t with hst | hts
  · refine ⟨c.restr s t hs.1 hst ht.2, rfl, rfl, trace_restr c hs.1 hst ht.2, ?_⟩
    exact LQGMetric.MetricGeometry.curveLength_mono c.γ hs.1 ht.2
  · refine ⟨(c.restr t s ht.1 hts hs.2).rev, by simp, by simp, ?_, ?_⟩
    · rw [trace_rev]
      exact trace_restr c ht.1 hts hs.2
    · rw [len_rev]
      exact LQGMetric.MetricGeometry.curveLength_mono c.γ ht.1 hs.2

 

theorem icurve_exists_append_subarc (Γ c : ICurve X) {z : X}
    (h₁ : Γ.tgt ∈ c.trace) (hz : z ∈ c.trace) :
    ∃ Γ' : ICurve X, Γ'.src = Γ.src ∧ Γ'.tgt = z ∧
      Γ'.trace ⊆ Γ.trace ∪ c.trace ∧ Γ'.len ≤ Γ.len + c.len := by
  obtain ⟨e, he1, he2, he3, he4⟩ := icurve_exists_subarc c h₁ hz
  refine ⟨Γ.append e he1.symm, by simp, by simp [he2], ?_, ?_⟩
  · rw [trace_append]
    exact union_subset_union le_rfl he3
  · rw [len_append]
    exact add_le_add le_rfl he4

 
def icurveConst (x : X) : ICurve X := ⟨fun _ => x, 0, 0, le_rfl, continuousOn_const⟩

@[simp] theorem icurveConst_src (x : X) : (icurveConst x).src = x := rfl
@[simp] theorem icurveConst_tgt (x : X) : (icurveConst x).tgt = x := rfl

theorem icurveConst_trace (x : X) : (icurveConst x).trace = {x} := by
  simp [icurveConst, ICurve.trace]

theorem icurveConst_len (x : X) : (icurveConst x).len = 0 := by
  simp [icurveConst, ICurve.len, LQGMetric.MetricGeometry.curveLength,
    eVariationOn.subsingleton _ Set.subsingleton_singleton]

 




theorem icurve_exists_glued (m : ℕ) (ℓ q : ℕ → ICurve X) (deg : ℕ → Prop)
    (hdeg : ∀ j < m, deg j → ℓ (j + 1) = ℓ j)
    (hmeet : ∀ j < m, ¬ deg j →
      ((ℓ j).trace ∩ (q j).trace).Nonempty ∧ ((q j).trace ∩ (ℓ (j + 1)).trace).Nonempty)
    (R : Set X) (hℓR : ∀ j ≤ m, (ℓ j).trace ⊆ R) (hqR : ∀ j < m, (q j).trace ⊆ R)
    {x y : X} (hx : x ∈ (ℓ 0).trace) (hy : y ∈ (ℓ m).trace) :
    ∃ Γ : ICurve X, Γ.src = x ∧ Γ.tgt = y ∧ Γ.trace ⊆ R ∧
      Γ.len ≤ ∑ j ∈ Finset.range m, (q j).len + ∑ j ∈ Finset.range (m + 1), (ℓ j).len := by
  classical
  have hxR : x ∈ R := hℓR 0 (Nat.zero_le _) hx
  have key : ∀ k ≤ m, ∃ Γ : ICurve X, Γ.src = x ∧ Γ.tgt ∈ (ℓ k).trace ∧ Γ.trace ⊆ R ∧
      Γ.len ≤ ∑ j ∈ Finset.range k, (q j).len + ∑ j ∈ Finset.range k, (ℓ j).len := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨icurveConst x, rfl, hx, ?_, ?_⟩
      · rw [icurveConst_trace]; exact Set.singleton_subset_iff.mpr hxR
      · rw [icurveConst_len]; exact bot_le
    | succ k ih =>
      obtain ⟨Γ, h1, h2, h3, h4⟩ := ih (by omega)
      have hkm : k < m := by omega
      by_cases hd : deg k
      · refine ⟨Γ, h1, by rw [hdeg k hkm hd]; exact h2, h3, ?_⟩
        refine h4.trans ?_
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        exact add_le_add (le_self_add) (le_self_add)
      · obtain ⟨⟨y₁, hy₁ℓ, hy₁q⟩, ⟨y₂, hy₂q, hy₂ℓ⟩⟩ := hmeet k hkm hd
        obtain ⟨Γ₁, k1, k2, k3, k4⟩ := icurve_exists_append_subarc Γ (ℓ k) h2 hy₁ℓ
        obtain ⟨Γ₂, l1, l2, l3, l4⟩ := icurve_exists_append_subarc Γ₁ (q k)
          (by rw [k2]; exact hy₁q) hy₂q
        refine ⟨Γ₂, by rw [l1, k1, h1], by rw [l2]; exact hy₂ℓ, ?_, ?_⟩
        · refine l3.trans (union_subset (k3.trans (union_subset h3 (hℓR k hkm.le)))
            (hqR k hkm))
        · calc Γ₂.len ≤ Γ₁.len + (q k).len := l4
            _ ≤ (Γ.len + (ℓ k).len) + (q k).len := add_le_add k4 le_rfl
            _ ≤ ((∑ j ∈ Finset.range k, (q j).len + ∑ j ∈ Finset.range k, (ℓ j).len) +
                (ℓ k).len) + (q k).len := add_le_add (add_le_add h4 le_rfl) le_rfl
            _ = _ := by rw [Finset.sum_range_succ, Finset.sum_range_succ]; ring
  obtain ⟨Γ, h1, h2, h3, h4⟩ := key m le_rfl
  obtain ⟨Γ', k1, k2, k3, k4⟩ := icurve_exists_append_subarc Γ (ℓ m) h2 hy
  refine ⟨Γ', by rw [k1, h1], k2, k3.trans (union_subset h3 (hℓR m le_rfl)), ?_⟩
  calc Γ'.len ≤ Γ.len + (ℓ m).len := k4
    _ ≤ (∑ j ∈ Finset.range m, (q j).len + ∑ j ∈ Finset.range m, (ℓ j).len) + (ℓ m).len :=
        add_le_add h4 le_rfl
    _ = _ := by rw [Finset.sum_range_succ (fun j => (ℓ j).len)]; ring

end Generic

 
def toICurve (d : LSCMetric) (P : ℝ → ℂ) (a b : ℝ) (hP : d.IsCurve P a b) :
    ICurve d.Space :=
  ofCurve d P a b hP

@[simp] theorem toICurve_trace (d : LSCMetric) (P : ℝ → ℂ) (a b : ℝ)
    (hP : d.IsCurve P a b) : (toICurve d P a b hP).trace = P '' Icc a b := rfl

@[simp] theorem toICurve_len (d : LSCMetric) (P : ℝ → ℂ) (a b : ℝ)
    (hP : d.IsCurve P a b) : (toICurve d P a b hP).len = d.len P a b := rfl

@[simp] theorem toICurve_src (d : LSCMetric) (P : ℝ → ℂ) (a b : ℝ)
    (hP : d.IsCurve P a b) : (toICurve d P a b hP).src = P a := rfl

@[simp] theorem toICurve_tgt (d : LSCMetric) (P : ℝ → ℂ) (a b : ℝ)
    (hP : d.IsCurve P a b) : (toICurve d P a b hP).tgt = P b := rfl

 
theorem icurve_isCurve (d : LSCMetric) (e : ICurve d.Space) :
    d.IsCurve (fun t => (e.γ t : ℂ)) e.a e.b :=
  ⟨e.le, e.cont⟩

theorem icurve_len_eq (d : LSCMetric) (e : ICurve d.Space) :
    d.len (fun t => (e.γ t : ℂ)) e.a e.b = e.len := rfl

theorem icurve_trace_eq (d : LSCMetric) (e : ICurve d.Space) :
    (fun t => (e.γ t : ℂ)) '' Icc e.a e.b = e.trace := rfl

end SupercriticalLQGUniqueness.B2.Median
