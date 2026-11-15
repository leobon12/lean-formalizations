/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualA15CofinalEncl
import InteractingSLE.Spec.ZhanGT4.DualA15CofinalExit
import InteractingSLE.Spec.ZhanGT4.DualA15Coupling
import InteractingSLE.Spec.ZhanGT4.DualA15CofinalRec

/-!
# Zhan's A.1.5: the countable cofinal family of enclosures, its exit times, and the limit coupling

Packet PROVE-ZHAN-GT4-A15F. Source: Astra, *Follow-up proofs*, §A.1.3 (L300–L305) and §A.1.5
(`source/external/AstraIG1/ig1_followup_proofs.txt` L409–L425, R38): "Enumerate a countable cofinal family of separated
polygonal enclosure pairs. For its first `n` pairs use (D11) … Any pair of disjoint compact prefixes is contained in a
member of the countable enclosure family".

* `goodIdx x₂ p`: the good indices (`GoodEncl`) of the countable index type `CofIdx`; nonempty when the marks avoid
  the sources (`goodIdx_nonempty`); `goodSeq x₂ p : ℕ → CofIdx` enumerates them (`range_goodSeq`).
* The family: enclosures `cofH₁`, `cofH₂`, rational data `cofδ`, `cofq`, `cofd`, and exit times
  `cofS₁ = hullExit (√κ B₁) (cofH₁ k) N_k`, `cofS₂ = hullExit (√(16/κ) B₂ + x₂) (cofH₂ k) N_k` (first exit, capped);
  bounds `cofTm m = Σ_{j ≤ m} N_j + 1`.
* **`dualHyp_cof`**: every initial block of the family satisfies A16's `DualHyp` in the usual augmentations of the
  two filtrations (right-continuous, so the exit times are stopping times; the Brownian motions stay Brownian, R34).
* **`exists_cof_le`** (cofinality): whenever the prefixes `closure K₁(s) ∪ {0}` and `closure K₂(t) ∪ {x₂}` are disjoint
  and contain no mark, some member `k` of the family has `s ≤ S₁ k` and `t ≤ S₂ k`.
* **`exists_dualCoupling_cof`**: A18's `exists_dualCoupling_lim` on this family — one probability measure on
  `RecPair` under which every member's pair of recorded stopped paths has the stopped-rectangle law and every block of
  each curve's records has its law under the first-`(k + 1)` coupling; `exists_dualCoupling_cof_consistent` adds that
  almost surely the records of each curve are consistent across members (`RecAgree`, `RecStop`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H fwdHull drive)

/-! ### The enumeration of the good indices -/

section Enum

variable {nm : ℕ} {x₂ : ℝ} {p : Fin nm → ℝ}

/-- The good indices of the enclosure family. -/
def goodIdx (x₂ : ℝ) (p : Fin nm → ℝ) : Set CofIdx := {i | GoodEncl x₂ p i}

/-- **The family is nonempty** when the marks avoid the two sources. -/
theorem goodIdx_nonempty (hx₂ : 0 < x₂) (hp0 : ∀ m, p m ≠ 0) (hpx : ∀ m, p m ≠ x₂) :
    (goodIdx x₂ p).Nonempty := by
  obtain ⟨i, hi, -⟩ := exists_goodEncl_prefix (p := p) hx₂ isHPHull_empty isHPHull_empty
    (by
      rw [closure_empty, empty_union, empty_union, disjoint_singleton]
      intro h
      have := congrArg Complex.re h
      simp only [Complex.zero_re, Complex.ofReal_re] at this
      linarith)
    (fun m h => by
      simp only [closure_empty, empty_union, mem_union, mem_singleton_iff] at h
      rcases h with h | h
      · exact hp0 m (by exact_mod_cast h)
      · exact hpx m (by exact_mod_cast h)) 1 one_pos
  exact ⟨i, hi⟩

open Classical in
/-- An enumeration of the good indices (a constant default if there are none). -/
def goodSeq (x₂ : ℝ) (p : Fin nm → ℝ) : ℕ → CofIdx :=
  if h : (goodIdx x₂ p).Nonempty then Classical.choose ((Set.to_countable (goodIdx x₂ p)).exists_eq_range h)
  else fun _ => default

theorem range_goodSeq (h : (goodIdx x₂ p).Nonempty) : range (goodSeq x₂ p) = goodIdx x₂ p := by
  unfold goodSeq
  simp only [h, ↓reduceDIte]
  exact (Classical.choose_spec ((Set.to_countable (goodIdx x₂ p)).exists_eq_range h)).symm

theorem goodSeq_good (h : (goodIdx x₂ p).Nonempty) (k : ℕ) : GoodEncl x₂ p (goodSeq x₂ p k) := by
  have : goodSeq x₂ p k ∈ goodIdx x₂ p := by rw [← range_goodSeq h]; exact ⟨k, rfl⟩
  exact this

end Enum

/-! ### The family and its exit times -/

section Family

variable {nm : ℕ} {x₂ : ℝ} {p : Fin nm → ℝ}

/-- The enclosure of curve `1` of member `k`. -/
def cofH₁ (x₂ : ℝ) (p : Fin nm → ℝ) (k : ℕ) : Set ℂ := (goodSeq x₂ p k).encl₁

/-- The enclosure of curve `2` of member `k`. -/
def cofH₂ (x₂ : ℝ) (p : Fin nm → ℝ) (k : ℕ) : Set ℂ := (goodSeq x₂ p k).encl₂ x₂

/-- The separation of member `k`. -/
def cofδ (x₂ : ℝ) (p : Fin nm → ℝ) (k : ℕ) : ℝ := (goodSeq x₂ p k).sep

/-- The protected point of member `k`. -/
def cofq (x₂ : ℝ) (p : Fin nm → ℝ) (k : ℕ) : ℝ := (goodSeq x₂ p k).prot

/-- The protection radius of member `k`. -/
def cofd (x₂ : ℝ) (p : Fin nm → ℝ) (k : ℕ) : ℝ := (goodSeq x₂ p k).rad

/-- The bound of the first `m + 1` exit times. -/
def cofTm (x₂ : ℝ) (p : Fin nm → ℝ) (m : ℕ) : ℝ := ∑ j ∈ Finset.range (m + 1), ((goodSeq x₂ p j).cap : ℝ) + 1

/-- The exit time of curve `1` (`√κ B₁`) from the enclosure of member `k`, capped. -/
def cofS₁ {Ω₁ : Type*} (κ : ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (x₂ : ℝ) (p : Fin nm → ℝ) (k : ℕ) (ω : Ω₁) : ℝ≥0 :=
  hullExit (drive κ B₁ ω) (cofH₁ x₂ p k) (goodSeq x₂ p k).cap

/-- The exit time of curve `2` (`√(16/κ) B₂ + x₂`) from the enclosure of member `k`, capped. -/
def cofS₂ {Ω₂ : Type*} (κ : ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (p : Fin nm → ℝ) (k : ℕ) (ω : Ω₂) : ℝ≥0 :=
  hullExit (fun u => drive (16 / κ) B₂ ω u + x₂) (cofH₂ x₂ p k) (goodSeq x₂ p k).cap

theorem cap_le_cofTm {k m : ℕ} (hkm : k ≤ m) : ((goodSeq x₂ p k).cap : ℝ) ≤ cofTm x₂ p m := by
  unfold cofTm
  have h := Finset.single_le_sum (f := fun j => ((goodSeq x₂ p j).cap : ℝ)) (fun j _ => NNReal.coe_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hkm))
  linarith

theorem cofTm_pos (m : ℕ) : 0 < cofTm x₂ p m := by
  unfold cofTm
  have := Finset.sum_nonneg (s := Finset.range (m + 1)) fun j _ => NNReal.coe_nonneg (goodSeq x₂ p j).cap
  linarith

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {κ : ℝ} {P₁ : Measure Ω₁}
  {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ} {P₂ : Measure Ω₂} {𝓕₂ : Filtration ℝ≥0 mΩ₂}
  {B₂ : ℝ≥0 → Ω₂ → ℝ}

/-- **Every initial block of the cofinal family is a protected family of stopped rectangles** (A16's `DualHyp`), in
the usual augmentations of the two filtrations. -/
theorem dualHyp_cof (hκ : 0 < κ) (hB₁ : IsFilteredBrownianReal 𝓕₁ B₁ P₁) (hc₁ : ∀ ω, Continuous (B₁ · ω))
    (h0₁ : ∀ ω, B₁ 0 ω = 0) (hB₂ : IsFilteredBrownianReal 𝓕₂ B₂ P₂) (hc₂ : ∀ ω, Continuous (B₂ · ω))
    (h0₂ : ∀ ω, B₂ 0 ω = 0) (hx₂ : 0 < x₂) (hpinj : Function.Injective p) (hp0 : ∀ m, p m ≠ 0)
    (hpx : ∀ m, p m ≠ x₂) (m : ℕ) :
    DualHyp κ P₁ (usualAugmentation 𝓕₁ P₁) B₁ P₂ (usualAugmentation 𝓕₂ P₂) B₂ x₂
      (fun k : Fin (m + 1) => cofH₁ x₂ p k) (fun k : Fin (m + 1) => cofH₂ x₂ p k)
      (fun k : Fin (m + 1) => cofδ x₂ p k) (fun k : Fin (m + 1) => cofq x₂ p k)
      (fun k : Fin (m + 1) => cofd x₂ p k) p (cofTm x₂ p m)
      (fun k : Fin (m + 1) => cofS₁ κ B₁ x₂ p k) (fun k : Fin (m + 1) => cofS₂ κ B₂ x₂ p k) := by
  have hne := goodIdx_nonempty hx₂ hp0 hpx
  have hg : ∀ k, GoodEncl x₂ p (goodSeq x₂ p k) := goodSeq_good hne
  have hB₁' := Ito.isFilteredBrownianReal_usualAugmentation hB₁
  have hB₂' := Ito.isFilteredBrownianReal_usualAugmentation hB₂
  have hW₁ : ∀ ω, Continuous (drive κ B₁ ω) := fun ω => QuantumZipper.drive_continuous (hc₁ ω)
  have hW₂ : ∀ ω, Continuous (drive (16 / κ) B₂ ω) := fun ω => QuantumZipper.drive_continuous (hc₂ ω)
  have hW₁0 : ∀ ω, drive κ B₁ ω 0 = 0 := fun ω => QuantumZipper.drive_zero (h0₁ ω)
  have hW₂0 : ∀ ω, drive (16 / κ) B₂ ω 0 = 0 := fun ω => QuantumZipper.drive_zero (h0₂ ω)
  exact {
    κpos := hκ
    bm₁ := hB₁'
    cont₁ := hc₁
    zero₁ := h0₁
    bm₂ := hB₂'
    cont₂ := hc₂
    zero₂ := h0₂
    hull₁ := fun k => (hg k).isHPHull₁
    hull₂ := fun k => (hg k).isHPHull₂
    δpos := fun k => (hg k).sep_pos
    sep := fun k => (hg k).sep
    dpos := fun k => (hg k).rad_pos
    qpos := fun k => (hg k).prot_pos
    qH := fun k => (hg k).protH
    pH := fun k j => (hg k).markH j
    pinj := hpinj
    x₂H := fun k => (hg k).mem_closure_encl₂
    qx := fun k => (hg k).prot_lt
    Tmpos := cofTm_pos m
    stop₁ := fun k => isStoppingTime_hullExit hc₁ hB₁'.2.1 (IsHPHull.isOpen_H_diff (hg k).isHPHull₁) _
    pos₁ := fun k ω => by
      obtain ⟨ε, hε, hsub⟩ := (hg k).nbhd₁
      exact hullExit_pos (hW₁ ω) (hW₁0 ω) (hg k).cap_pos hε hsub
    le₁ := fun k ω => (NNReal.coe_le_coe.2 hullExit_le).trans (cap_le_cofTm (Nat.lt_succ_iff.1 k.2))
    K₁ := fun k ω => fwdHull_hullExit_subset (hW₁ ω) (hW₁0 ω) (hg k).isHPHull₁
    stop₂ := fun k => isStoppingTime_hullExit_add hc₂ hB₂'.2.1 (IsHPHull.isOpen_H_diff (hg k).isHPHull₂) x₂ _
    pos₂ := fun k ω => by
      obtain ⟨ε, hε, hsub⟩ := (hg k).nbhd₂
      exact hullExit_pos_add (hW₂ ω) (hW₂0 ω) x₂ (hg k).cap_pos hε hsub
    le₂ := fun k ω => (NNReal.coe_le_coe.2 hullExit_le).trans (cap_le_cofTm (Nat.lt_succ_iff.1 k.2))
    K₂ := fun k ω => fwdHull_hullExit_subset_add (hW₂ ω) (hW₂0 ω) x₂ (hg k).isHPHull₂ }

/-- **Cofinality of the family**: if the prefixes `closure K₁(s) ∪ {0}` and `closure K₂(t) ∪ {x₂}` of the two curves are
disjoint and contain no mark, some member of the family has `s ≤ S₁ k` and `t ≤ S₂ k`. -/
theorem exists_cof_le (hc₁ : ∀ ω, Continuous (B₁ · ω)) (hc₂ : ∀ ω, Continuous (B₂ · ω)) (hx₂ : 0 < x₂)
    (hp0 : ∀ m, p m ≠ 0) (hpx : ∀ m, p m ≠ x₂) {ω₁ : Ω₁} {ω₂ : Ω₂} {s t : ℝ≥0}
    (hdisj : Disjoint (closure (fwdHull (drive κ B₁ ω₁) s) ∪ {0})
      (closure (fwdHull (fun u => drive (16 / κ) B₂ ω₂ u + x₂) t) ∪ {(x₂ : ℂ)}))
    (hp : ∀ m, (p m : ℂ) ∉ (closure (fwdHull (drive κ B₁ ω₁) s) ∪ {0}) ∪
      (closure (fwdHull (fun u => drive (16 / κ) B₂ ω₂ u + x₂) t) ∪ {(x₂ : ℂ)})) :
    ∃ k, s ≤ cofS₁ κ B₁ x₂ p k ω₁ ∧ t ≤ cofS₂ κ B₂ x₂ p k ω₂ := by
  have hW₁ : Continuous (drive κ B₁ ω₁) := QuantumZipper.drive_continuous (hc₁ ω₁)
  have hW₂ : Continuous fun u => drive (16 / κ) B₂ ω₂ u + x₂ :=
    (QuantumZipper.drive_continuous (hc₂ ω₂)).add continuous_const
  set N : ℕ := ⌈max s t⌉₊ + 1 with hN
  have hmN : max s t ≤ (N : ℝ≥0) :=
    (Nat.le_ceil (max s t)).trans (by rw [hN]; exact_mod_cast Nat.le_succ _)
  have hsN : s ≤ (N : ℝ≥0) := (le_max_left s t).trans hmN
  have htN : t ≤ (N : ℝ≥0) := (le_max_right s t).trans hmN
  obtain ⟨i, hi, hcap, h₁, h₂⟩ := exists_goodEncl_prefix hx₂ (isHPHull_fwdHull hW₁ s.coe_nonneg)
    (isHPHull_fwdHull hW₂ t.coe_nonneg) hdisj hp N (Nat.succ_pos _)
  obtain ⟨k, hk⟩ : i ∈ range (goodSeq x₂ p) := by
    rw [range_goodSeq (goodIdx_nonempty hx₂ hp0 hpx)]; exact hi
  refine ⟨k, ?_, ?_⟩
  · unfold cofS₁ cofH₁
    rw [hk, hcap]
    exact le_hullExit hsN fun r hr =>
      (QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 hr.le)).trans h₁
  · unfold cofS₂ cofH₂
    rw [hk, hcap]
    exact le_hullExit htN fun r hr =>
      (QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 hr.le)).trans h₂

/-- **Exhaustion**: the prefixes `closure K₁(s) ∪ {0}` and `closure K₂(t) ∪ {x₂}` are disjoint and contain no mark iff
some member of the family has `s ≤ S₁ k` and `t ≤ S₂ k`. So the members exhaust the region before first contact. -/
theorem disjoint_prefix_iff_exists_cof (hc₁ : ∀ ω, Continuous (B₁ · ω)) (h0₁ : ∀ ω, B₁ 0 ω = 0)
    (hc₂ : ∀ ω, Continuous (B₂ · ω)) (h0₂ : ∀ ω, B₂ 0 ω = 0) (hx₂ : 0 < x₂) (hp0 : ∀ m, p m ≠ 0)
    (hpx : ∀ m, p m ≠ x₂) {ω₁ : Ω₁} {ω₂ : Ω₂} {s t : ℝ≥0} :
    (Disjoint (closure (fwdHull (drive κ B₁ ω₁) s) ∪ {0})
        (closure (fwdHull (fun u => drive (16 / κ) B₂ ω₂ u + x₂) t) ∪ {(x₂ : ℂ)}) ∧
      ∀ m, (p m : ℂ) ∉ (closure (fwdHull (drive κ B₁ ω₁) s) ∪ {0}) ∪
        (closure (fwdHull (fun u => drive (16 / κ) B₂ ω₂ u + x₂) t) ∪ {(x₂ : ℂ)})) ↔
      ∃ k, s ≤ cofS₁ κ B₁ x₂ p k ω₁ ∧ t ≤ cofS₂ κ B₂ x₂ p k ω₂ := by
  refine ⟨fun h => exists_cof_le hc₁ hc₂ hx₂ hp0 hpx h.1 h.2, ?_⟩
  rintro ⟨k, hsk, htk⟩
  have hg := goodSeq_good (goodIdx_nonempty hx₂ hp0 hpx) k
  have hW₁ := QuantumZipper.drive_continuous (κ := κ) (hc₁ ω₁)
  have hW₂ := QuantumZipper.drive_continuous (κ := 16 / κ) (hc₂ ω₂)
  have hK₁ : fwdHull (drive κ B₁ ω₁) s ⊆ cofH₁ x₂ p k :=
    (QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 hsk)).trans
      (fwdHull_hullExit_subset hW₁ (QuantumZipper.drive_zero (h0₁ ω₁)) hg.isHPHull₁)
  have hK₂ : fwdHull (fun u => drive (16 / κ) B₂ ω₂ u + x₂) t ⊆ cofH₂ x₂ p k :=
    (QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 htk)).trans
      (fwdHull_hullExit_subset_add hW₂ (QuantumZipper.drive_zero (h0₂ ω₂)) x₂ hg.isHPHull₂)
  have hP₁ : closure (fwdHull (drive κ B₁ ω₁) s) ∪ {0} ⊆ closure (cofH₁ x₂ p k) :=
    union_subset (closure_mono hK₁) (singleton_subset_iff.2 hg.zero_mem_closure_encl₁)
  have hP₂ : closure (fwdHull (fun u => drive (16 / κ) B₂ ω₂ u + x₂) t) ∪ {(x₂ : ℂ)} ⊆ closure (cofH₂ x₂ p k) :=
    union_subset (closure_mono hK₂) (singleton_subset_iff.2 hg.mem_closure_encl₂)
  exact ⟨hg.disjoint_closure.mono hP₁ hP₂, fun m hm => hg.mark_notMem_closure m
    (union_subset_union hP₁ hP₂ hm)⟩

/-- **A.1.5 on the cofinal family**: one probability measure on `RecPair` under which the pair of recorded stopped
paths of every member has the stopped-rectangle law, and every block of the first `k + 1` records of each curve has its
law under the first-`(k + 1)` stopped dual coupling (A18's `exists_dualCoupling_lim` applied to `dualHyp_cof`). -/
theorem exists_dualCoupling_cof (hκ : 0 < κ) (hB₁ : IsFilteredBrownianReal 𝓕₁ B₁ P₁)
    (hc₁ : ∀ ω, Continuous (B₁ · ω)) (h0₁ : ∀ ω, B₁ 0 ω = 0) (hB₂ : IsFilteredBrownianReal 𝓕₂ B₂ P₂)
    (hc₂ : ∀ ω, Continuous (B₂ · ω)) (h0₂ : ∀ ω, B₂ 0 ω = 0) (hx₂ : 0 < x₂) (hpinj : Function.Injective p)
    (hp0 : ∀ m, p m ≠ 0) (hpx : ∀ m, p m ≠ x₂) (rr : Fin nm → ℝ) :
    ∃ μ : Measure RecPair, IsProbabilityMeasure μ ∧
      (∀ k, μ.map (fun z => (z.1 k, z.2 k)) =
        (dualCouplingOne κ rr p P₁ B₁ P₂ B₂ x₂ (cofS₁ κ B₁ x₂ p) (cofS₂ κ B₂ x₂ p) (cofTm x₂ p) k).map
          (fun ω => (recPath B₁ (cofS₁ κ B₁ x₂ p k) ω.1, recPath B₂ (cofS₂ κ B₂ x₂ p k) ω.2))) ∧
      (∀ k, μ.map (fun z => truncRec k z.1) =
        (dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ (cofS₁ κ B₁ x₂ p) (cofS₂ κ B₂ x₂ p) (cofTm x₂ p) k).map
          (fun ω => truncRec k (recAll B₁ (cofS₁ κ B₁ x₂ p) ω.1))) ∧
      ∀ k, μ.map (fun z => truncRec k z.2) =
        (dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ (cofS₁ κ B₁ x₂ p) (cofS₂ κ B₂ x₂ p) (cofTm x₂ p) k).map
          (fun ω => truncRec k (recAll B₂ (cofS₂ κ B₂ x₂ p) ω.2)) :=
  exists_dualCoupling_lim (fun m => dualHyp_cof hκ hB₁ hc₁ h0₁ hB₂ hc₂ h0₂ hx₂ hpinj hp0 hpx m) rr

/-- **A.1.5 on the cofinal family, with consistent records**: the limit coupling of `exists_dualCoupling_cof`, under
which moreover almost surely the records of each curve agree across members below both stopping times and are constant
after their stopping times. -/
theorem exists_dualCoupling_cof_consistent (hκ : 0 < κ) (hB₁ : IsFilteredBrownianReal 𝓕₁ B₁ P₁)
    (hc₁ : ∀ ω, Continuous (B₁ · ω)) (h0₁ : ∀ ω, B₁ 0 ω = 0) (hB₂ : IsFilteredBrownianReal 𝓕₂ B₂ P₂)
    (hc₂ : ∀ ω, Continuous (B₂ · ω)) (h0₂ : ∀ ω, B₂ 0 ω = 0) (hx₂ : 0 < x₂) (hpinj : Function.Injective p)
    (hp0 : ∀ m, p m ≠ 0) (hpx : ∀ m, p m ≠ x₂) (rr : Fin nm → ℝ) :
    ∃ μ : Measure RecPair, IsProbabilityMeasure μ ∧
      (∀ k, μ.map (fun z => (z.1 k, z.2 k)) =
        (dualCouplingOne κ rr p P₁ B₁ P₂ B₂ x₂ (cofS₁ κ B₁ x₂ p) (cofS₂ κ B₂ x₂ p) (cofTm x₂ p) k).map
          (fun ω => (recPath B₁ (cofS₁ κ B₁ x₂ p k) ω.1, recPath B₂ (cofS₂ κ B₂ x₂ p k) ω.2))) ∧
      (∀ k, μ.map (fun z => truncRec k z.1) =
        (dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ (cofS₁ κ B₁ x₂ p) (cofS₂ κ B₂ x₂ p) (cofTm x₂ p) k).map
          (fun ω => truncRec k (recAll B₁ (cofS₁ κ B₁ x₂ p) ω.1))) ∧
      (∀ k, μ.map (fun z => truncRec k z.2) =
        (dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ (cofS₁ κ B₁ x₂ p) (cofS₂ κ B₂ x₂ p) (cofTm x₂ p) k).map
          (fun ω => truncRec k (recAll B₂ (cofS₂ κ B₂ x₂ p) ω.2))) ∧
      ∀ᵐ z ∂μ, ((∀ k k' j, z.1 ∈ RecAgree k k' j) ∧ ∀ k j j', z.1 ∈ RecStop k j j') ∧
        ((∀ k k' j, z.2 ∈ RecAgree k k' j) ∧ ∀ k j j', z.2 ∈ RecStop k j j') := by
  obtain ⟨μ, hμ, hrect, hb₁, hb₂⟩ := exists_dualCoupling_cof (𝓕₁ := 𝓕₁) (𝓕₂ := 𝓕₂) hκ hB₁ hc₁ h0₁ hB₂ hc₂ h0₂
    hx₂ hpinj hp0 hpx rr
  have hfam := fun m => dualHyp_cof (κ := κ) (P₁ := P₁) (𝓕₁ := 𝓕₁) (P₂ := P₂) (𝓕₂ := 𝓕₂) hκ hB₁ hc₁ h0₁ hB₂ hc₂
    h0₂ hx₂ hpinj hp0 hpx m
  have hm₁ : Measurable (recAll B₁ (cofS₁ κ B₁ x₂ p)) := measurable_pi_iff.2 fun k =>
    (measurable_recPath (hfam k).bm₁.2.1 (hfam k).cont₁ ((hfam k).stop₁ ⟨k, Nat.lt_succ_self k⟩)).mono
      ((hfam k).stop₁ ⟨k, Nat.lt_succ_self k⟩).measurableSpace_le le_rfl
  have hm₂ : Measurable (recAll B₂ (cofS₂ κ B₂ x₂ p)) := measurable_pi_iff.2 fun k =>
    (measurable_recPath (hfam k).bm₂.2.1 (hfam k).cont₂ ((hfam k).stop₂ ⟨k, Nat.lt_succ_self k⟩)).mono
      ((hfam k).stop₂ ⟨k, Nat.lt_succ_self k⟩).measurableSpace_le le_rfl
  refine ⟨μ, hμ, hrect, hb₁, hb₂, ?_⟩
  exact (ae_recAgree_of_block measurable_fst (π := Prod.fst) (hm₁.comp measurable_fst) hb₁).and
    (ae_recAgree_of_block measurable_snd (π := Prod.snd) (hm₂.comp measurable_snd) hb₂)

end Family

end InteractingSLE.ZhanGT4
