import QuantumZipper.Proofs.LQG.LocalRule
import Mathlib.Topology.PartitionOfUnity

/-!
# Gluing local vague limits on an open subset of `ℝ` (for E1-FIX)

`handoff/E1-PLAN.md`, sub-node **E1-FIX** ("needs gluing of local vague limits: existence on
`liveNeg` from the windows"). If a sequence `νs` of locally finite measures has a vague limit on
every window `(p,q)` with `[p,q] ⊆ U`, it has a vague limit on the open set `U`
(`exists_isVagueLimitOnR_of_windows`).

Construction: enumerate the rational windows `W_n = (p_n,q_n)`, `[p_n,q_n] ⊆ U`, which cover `U`;
disjointify `D_n = W_n \ ⋃_{m<n} W_m`; put `μ = Σ_n ν_n|_{D_n}`. By uniqueness of local limits
(`LocalRule.isVagueLimitOnR_unique`) the `ν_n` agree on overlaps, so `μ|_{W_n} = ν_n`
(`restrict_glue`); `μ` is finite on compacts of `U`; and a finite partition of unity subordinate
to the windows (`exists_continuous_sum_one_of_isOpen_isCompact`) reduces a test function supported
in `U` to test functions supported in single windows. This is the standard sheaf property of
Radon measures (e.g. Bourbaki, *Integration*, Ch. III §2 No. 1, Prop. 1); our own formalization.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace E1

variable {νs : ℕ → Measure ℝ}

/-- A local vague limit restricts to smaller open sets. -/
theorem isVagueLimitOnR_restrict_open {W V : Set ℝ} {ν : Measure ℝ}
    (h : IsVagueLimitOnR W νs ν) (hV : IsOpen V) (hVW : V ⊆ W) :
    IsVagueLimitOnR V νs (ν.restrict V) := by
  obtain ⟨-, hK, ht⟩ := h
  refine ⟨by rw [Measure.restrict_apply hV.measurableSet.compl]; simp,
    fun K hKc hKV => (Measure.restrict_apply_le _ _).trans_lt (hK K hKc (hKV.trans hVW)),
    fun f hf hfc hfV => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => image_eq_zero_of_notMem_tsupport fun h => ht (hfV h))]
  exact ht f hf hfc (hfV.trans hVW)

/-! ## Rational windows -/

/-- The `n`-th rational pair. -/
def winPQ (n : ℕ) : ℚ × ℚ := (Encodable.decode n).getD (0, 0)

open Classical in
/-- The `n`-th window of `U`: `(p_n,q_n)` if `[p_n,q_n] ⊆ U`, else `∅`. -/
def winW (U : Set ℝ) (n : ℕ) : Set ℝ :=
  if Icc ((winPQ n).1 : ℝ) (winPQ n).2 ⊆ U then Ioo ((winPQ n).1 : ℝ) (winPQ n).2 else ∅

theorem isOpen_winW (U : Set ℝ) (n : ℕ) : IsOpen (winW U n) := by
  unfold winW; split_ifs
  · exact isOpen_Ioo
  · exact isOpen_empty

theorem winW_subset (U : Set ℝ) (n : ℕ) : winW U n ⊆ U := by
  unfold winW; split_ifs with h
  · exact Ioo_subset_Icc_self.trans h
  · exact empty_subset _

theorem iUnion_winW {U : Set ℝ} (hU : IsOpen U) : ⋃ n, winW U n = U := by
  refine subset_antisymm (iUnion_subset (winW_subset U)) fun x hx => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show x - ε / 2 < x by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < x + ε / 2 by linarith)
  have hsub : Icc (p : ℝ) q ⊆ U := fun y hy => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2])
  refine mem_iUnion.2 ⟨Encodable.encode (p, q), ?_⟩
  have e : winPQ (Encodable.encode (p, q)) = (p, q) := by simp [winPQ, Encodable.encodek]
  unfold winW
  rw [e, if_pos hsub]
  exact ⟨hp2, hq1⟩

/-- Points of a window have a closed neighbourhood inside the window. -/
theorem exists_Icc_subset_winW {U : Set ℝ} {n : ℕ} {x : ℝ} (hx : x ∈ winW U n) :
    ∃ ε > 0, Icc (x - ε) (x + ε) ⊆ winW U n := by
  unfold winW at hx ⊢
  split_ifs at hx ⊢ with h
  · refine ⟨min (x - (winPQ n).1) ((winPQ n).2 - x) / 2,
      by have := hx.1; have := hx.2; positivity, fun y hy => ⟨?_, ?_⟩⟩
    · have := min_le_left (x - (winPQ n).1) ((winPQ n).2 - x)
      have := hx.1; linarith [hy.1]
    · have := min_le_right (x - (winPQ n).1) ((winPQ n).2 - x)
      have := hx.2; linarith [hy.2]
  · exact absurd hx (notMem_empty x)

/-! ## The glued measure -/

/-- Disjointified windows. -/
def winD (U : Set ℝ) (n : ℕ) : Set ℝ := winW U n \ ⋃ m < n, winW U m

theorem measurableSet_winD (U : Set ℝ) (n : ℕ) : MeasurableSet (winD U n) :=
  (isOpen_winW U n).measurableSet.diff
    (MeasurableSet.biUnion (to_countable _) fun m _ => (isOpen_winW U m).measurableSet)

theorem winD_subset (U : Set ℝ) (n : ℕ) : winD U n ⊆ winW U n := diff_subset

theorem pairwise_disjoint_winD (U : Set ℝ) : Pairwise (Function.onFun Disjoint (winD U)) := by
  intro n m hnm
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨hxn, hxn'⟩ ⟨hxm, hxm'⟩
  rcases lt_or_gt_of_ne hnm with h | h
  · exact hxm' (mem_biUnion h hxn)
  · exact hxn' (mem_biUnion h hxm)

theorem iUnion_winD (U : Set ℝ) : ⋃ n, winD U n = ⋃ n, winW U n := by
  refine subset_antisymm (iUnion_mono (winD_subset U)) fun x hx => ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 hx
  classical
  let m := Nat.find (⟨n, hn⟩ : ∃ n, x ∈ winW U n)
  refine mem_iUnion.2 ⟨m, Nat.find_spec (⟨n, hn⟩ : ∃ n, x ∈ winW U n), ?_⟩
  simp only [mem_iUnion, not_exists]
  intro k hk hxk
  exact Nat.find_min (⟨n, hn⟩ : ∃ n, x ∈ winW U n) hk hxk

/-- The glued measure `Σ_n ν_n|_{D_n}`. -/
def glue (U : Set ℝ) (ν : ℕ → Measure ℝ) : Measure ℝ :=
  Measure.sum fun n => (ν n).restrict (winD U n)

/-- **Consistency gives `μ|_{W_m} = ν_m`.** -/
theorem restrict_glue {U : Set ℝ} (hU : IsOpen U) {ν : ℕ → Measure ℝ}
    (hν : ∀ n, IsVagueLimitOnR (winW U n) νs (ν n)) (m : ℕ) :
    (glue U ν).restrict (winW U m) = ν m := by
  have hcons : ∀ n, (ν n).restrict (winW U n ∩ winW U m) = (ν m).restrict (winW U n ∩ winW U m) :=
    fun n => LocalRule.isVagueLimitOnR_unique ((isOpen_winW U n).inter (isOpen_winW U m))
      (isVagueLimitOnR_restrict_open (hν n) ((isOpen_winW U n).inter (isOpen_winW U m))
        inter_subset_left)
      (isVagueLimitOnR_restrict_open (hν m) ((isOpen_winW U n).inter (isOpen_winW U m))
        inter_subset_right)
  ext A hA
  have hWm := (isOpen_winW U m).measurableSet
  rw [Measure.restrict_apply hA, glue, Measure.sum_apply _ (hA.inter hWm)]
  have hterm : ∀ n, (ν n).restrict (winD U n) (A ∩ winW U m) =
      ν m (A ∩ winW U m ∩ winD U n) := fun n => by
    rw [Measure.restrict_apply (hA.inter hWm)]
    have hsub : A ∩ winW U m ∩ winD U n ⊆ winW U n ∩ winW U m := fun x hx =>
      ⟨winD_subset U n hx.2, hx.1.2⟩
    have hm := (hA.inter hWm).inter (measurableSet_winD U n)
    rw [← Measure.restrict_eq_self (ν n) hsub, hcons n, Measure.restrict_eq_self (ν m) hsub]
  simp_rw [hterm]
  rw [← measure_iUnion (fun i j hij => (pairwise_disjoint_winD U hij).mono inter_subset_right
    inter_subset_right) (fun n => (hA.inter hWm).inter (measurableSet_winD U n)),
    ← inter_iUnion, iUnion_winD, iUnion_winW hU,
    inter_eq_left.2 (inter_subset_right.trans (winW_subset U m))]
  have h0 : ν m (winW U m)ᶜ = 0 := (hν m).1
  have hae : ∀ᵐ x ∂ν m, x ∈ winW U m :=
    (measure_eq_zero_iff_ae_notMem.1 h0).mono fun x hx => by simpa using hx
  rw [← Measure.restrict_apply hA, Measure.restrict_eq_self_of_ae_mem hae]

/-- Vague limits on the windows `W_n` from vague limits on the rational windows `(p,q)` with
`[p,q] ⊆ U` (the empty windows are trivial). -/
theorem exists_isVagueLimitOnR_winW {U : Set ℝ} (n : ℕ)
    (hloc : Icc ((winPQ n).1 : ℝ) (winPQ n).2 ⊆ U →
      ∃ ν, IsVagueLimitOnR (Ioo ((winPQ n).1 : ℝ) (winPQ n).2) νs ν) :
    ∃ ν, IsVagueLimitOnR (winW U n) νs ν := by
  classical
  by_cases h : Icc ((winPQ n).1 : ℝ) (winPQ n).2 ⊆ U
  · obtain ⟨ν, hν⟩ := hloc h
    refine ⟨ν, ?_⟩
    unfold winW; rw [if_pos h]; exact hν
  · refine ⟨0, ?_⟩
    unfold winW; rw [if_neg h]
    exact ⟨by simp, fun _ _ _ => by simp, fun f _ _ hfU => by
      have : f = 0 := funext fun t => image_eq_zero_of_notMem_tsupport fun ht => hfU ht
      subst this; simp⟩

/-- **Gluing** (window form): vague limits on all windows `W_n` give a vague limit on `U`. -/
theorem exists_isVagueLimitOnR_of_winW {U : Set ℝ} (hU : IsOpen U)
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (νs k))
    (hW : ∀ n, ∃ ν, IsVagueLimitOnR (winW U n) νs ν) :
    ∃ ν, IsVagueLimitOnR U νs ν := by
  classical
  choose ν hν using hW
  set μ := glue U ν with hμ
  have hres := restrict_glue hU hν
  -- (i) no mass off `U`
  have h0 : μ Uᶜ = 0 := by
    rw [hμ, glue, Measure.sum_apply _ hU.measurableSet.compl]
    refine ENNReal.tsum_eq_zero.2 fun n => ?_
    rw [Measure.restrict_apply hU.measurableSet.compl]
    convert measure_empty (μ := ν n)
    exact eq_empty_of_forall_notMem fun x hx =>
      hx.1 (winW_subset U n (winD_subset U n hx.2))
  -- (ii) finite on compacts of `U`
  have hK : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤ := fun K hKc hKU => by
    refine hKc.measure_lt_top_of_nhdsWithin fun x hx => ?_
    rw [← iUnion_winW hU] at hKU
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hKU hx)
    obtain ⟨ε, hε, hsub⟩ := exists_Icc_subset_winW hn
    refine ⟨Ioo (x - ε) (x + ε), mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith)
      (by linarith)), ?_⟩
    calc μ (Ioo (x - ε) (x + ε)) ≤ μ (Icc (x - ε) (x + ε)) := measure_mono Ioo_subset_Icc_self
      _ = (μ.restrict (winW U n)) (Icc (x - ε) (x + ε)) := by
          rw [Measure.restrict_apply measurableSet_Icc, inter_eq_left.2 hsub]
      _ < ⊤ := by rw [hres]; exact (hν n).2.1 _ isCompact_Icc hsub
  refine ⟨μ, h0, hK, fun f hf hfc hfU => ?_⟩
  -- (iii) test functions: a partition of unity subordinate to finitely many windows
  set K := tsupport f with hKdef
  have hKc : IsCompact K := hfc
  obtain ⟨s, hs⟩ := hKc.elim_finite_subcover (winW U) (isOpen_winW U)
    (by rw [iUnion_winW hU]; exact hfU)
  set e := s.equivFin
  set S : Fin s.card → Set ℝ := fun i => winW U (e.symm i) with hS
  obtain ⟨g, hgS, hg1, -, hgc⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (fun i => isOpen_winW U (e.symm i)) hKc (t := K) (s := S) (by
      intro x hx
      obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.1 (hs hx)
      exact mem_iUnion.2 ⟨e ⟨n, hn⟩, by simp only [hS, Equiv.symm_apply_apply]; exact hxn⟩)
  have hsplit : ∀ t, f t = ∑ i, f t * g i t := fun t => by
    rw [← Finset.mul_sum]
    by_cases ht : t ∈ K
    · have := hg1 ht
      simp only [Finset.sum_apply, Pi.one_apply] at this
      rw [this, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  have hfg : ∀ i, Continuous fun t => f t * g i t := fun i => hf.mul (g i).continuous
  have hfgc : ∀ i, HasCompactSupport fun t => f t * g i t := fun i => hfc.mul_right
  have hfgS : ∀ i, tsupport (fun t => f t * g i t) ⊆ S i := fun i =>
    (tsupport_mul_subset_right).trans (hgS i)
  have hint : ∀ k, ∫ t, f t ∂νs k = ∑ i, ∫ t, f t * g i t ∂νs k := fun k => by
    have := hfin k
    simp_rw [← integral_finset_sum _ fun i _ => (hfg i).integrable_of_hasCompactSupport (hfgc i)]
    exact integral_congr_ae (ae_of_all _ fun t => hsplit t)
  have hμK : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.2 (hK K hKc hfU).ne
  have hlim : ∫ t, f t ∂μ = ∑ i, ∫ t, f t * g i t ∂μ := by
    have hsK : ∀ φ : ℝ → ℝ, (∀ t, t ∉ K → φ t = 0) → ∫ t, φ t ∂μ = ∫ t, φ t ∂μ.restrict K :=
      fun φ hφ => (setIntegral_eq_integral_of_forall_compl_eq_zero hφ).symm
    have hzero : ∀ i t, t ∉ K → f t * g i t = 0 := fun i t ht => by
      rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
    rw [hsK f fun t ht => image_eq_zero_of_notMem_tsupport ht]
    simp_rw [fun i => hsK _ (hzero i)]
    rw [← integral_finset_sum _ fun i _ => (hfg i).integrable_of_hasCompactSupport (hfgc i)]
    exact integral_congr_ae (ae_of_all _ fun t => hsplit t)
  rw [hlim]
  simp_rw [hint]
  refine tendsto_finset_sum _ fun i _ => ?_
  have hi := (hν (e.symm i)).2.2 _ (hfg i) (hfgc i) (hfgS i)
  have e1 : ∫ t, f t * g i t ∂μ = ∫ t, f t * g i t ∂ν (e.symm i) := by
    rw [← hres (e.symm i), setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => image_eq_zero_of_notMem_tsupport fun h => ht (hfgS i h))]
  rw [e1]; exact hi

/-- **Gluing.** Vague limits on all windows `(p,q)` with `[p,q] ⊆ U` give a vague limit on `U`. -/
theorem exists_isVagueLimitOnR_of_windows {U : Set ℝ} (hU : IsOpen U)
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (νs k))
    (hloc : ∀ p q : ℝ, Icc p q ⊆ U → ∃ ν, IsVagueLimitOnR (Ioo p q) νs ν) :
    ∃ ν, IsVagueLimitOnR U νs ν :=
  exists_isVagueLimitOnR_of_winW hU hfin fun n =>
    exists_isVagueLimitOnR_winW n fun h => hloc _ _ h

end E1
end QuantumZipper
