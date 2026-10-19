import GaussianLQG.Core.Defs
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# A Hilbert basis of nice white-noise vectors (blueprint Appendix B, "The frame")

`exists_nice_hilbertBasis`: there is a Hilbert basis `(b_j)_{j ∈ ℕ}` of `L²(ℝ × ℂ)` all of whose
vectors are nice (`IsNiceWN`: essentially bounded, vanishing outside a bounded set at positive
distance from time `0`).

Proof.
1. Nice vectors form a submodule `niceSubmodule`, which is dense: by `Lp.induction` it suffices
   to approximate indicators `1_s` of finite-measure sets, and `1_{s ∩ S_n} → 1_s` with
   `S_n = {1/(n+1) ≤ |t| ≤ n + 1, |y| ≤ n + 1}` (continuity of the measure; `{t = 0}` is null).
2. `L²` is separable, so `niceSubmodule` contains a countable dense set `D`.
3. The indicators `o_n` of the disjoint boxes `(n + 1, n + 2] × B̄₁(0)` are nice, nonzero and
   orthogonal, hence linearly independent. Extend them to a linearly independent `B ⊆ range o ∪ D`
   spanning `D`; `B` is countable and infinite, so it can be enumerated by `ℕ`.
4. Gram–Schmidt on the enumeration gives an orthonormal family with the same span (dense), whose
   vectors lie in the span of `B ⊆ niceSubmodule`.

The closure lemmas `isNiceWN_zero`, `IsNiceWN.add`, `IsNiceWN.smul` and the theorem
`exists_nice_hilbertBasis` are in `GaussianLQG`; the construction is in `GaussianLQG.WNFrame`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace symmDiff

namespace GaussianLQG

/-! ## Nice vectors form a dense submodule -/

lemma isNiceWN_zero : IsNiceWN 0 := by
  refine ⟨1, 1, 0, 0, one_pos, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure (ℝ × ℂ))] with q hq
    rw [hq]; simp
  · filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure (ℝ × ℂ))] with q hq h
    exact absurd hq h

lemma IsNiceWN.add {g h : WNSpace} (hg : IsNiceWN g) (hh : IsNiceWN h) : IsNiceWN (g + h) := by
  obtain ⟨a, b, M, R, ha, hM, hS⟩ := hg
  obtain ⟨a', b', M', R', ha', hM', hS'⟩ := hh
  refine ⟨min a a', max b b', M + M', max R R', lt_min ha ha', ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add g h, hM, hM'] with q hq h1 h2
    rw [hq, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  · filter_upwards [Lp.coeFn_add g h, hS, hS'] with q hq h1 h2 hne
    rw [hq, Pi.add_apply] at hne
    by_cases hg0 : (g : ℝ × ℂ → ℝ) q = 0
    · have hh0 : (h : ℝ × ℂ → ℝ) q ≠ 0 := by rw [hg0, zero_add] at hne; exact hne
      obtain ⟨x1, x2, x3⟩ := h2 hh0
      exact ⟨(min_le_right _ _).trans x1, x2.trans (le_max_right _ _),
        x3.trans (le_max_right _ _)⟩
    · obtain ⟨x1, x2, x3⟩ := h1 hg0
      exact ⟨(min_le_left _ _).trans x1, x2.trans (le_max_left _ _),
        x3.trans (le_max_left _ _)⟩

lemma IsNiceWN.smul {g : WNSpace} (hg : IsNiceWN g) (c : ℝ) : IsNiceWN (c • g) := by
  obtain ⟨a, b, M, R, ha, hM, hS⟩ := hg
  refine ⟨a, b, |c| * M, R, ha, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul c g, hM] with q hq h1
    rw [hq, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  · filter_upwards [Lp.coeFn_smul c g, hS] with q hq h1 hne
    rw [hq, Pi.smul_apply, smul_eq_mul] at hne
    exact h1 (right_ne_zero_of_mul hne)

namespace WNFrame

/-- The submodule of nice white-noise vectors. -/
def niceSubmodule : Submodule ℝ WNSpace where
  carrier := {g | IsNiceWN g}
  zero_mem' := isNiceWN_zero
  add_mem' := fun hg hh => IsNiceWN.add hg hh
  smul_mem' := fun c _ hg => IsNiceWN.smul hg c

/-- The truncation boxes `S_n = {1/(n+1) ≤ |t| ≤ n + 1, ‖y‖ ≤ n + 1}`. -/
def truncBox (n : ℕ) : Set (ℝ × ℂ) :=
  {q | 1 / ((n : ℝ) + 1) ≤ |q.1| ∧ |q.1| ≤ (n : ℝ) + 1 ∧ ‖q.2‖ ≤ (n : ℝ) + 1}

lemma measurableSet_truncBox (n : ℕ) : MeasurableSet (truncBox n) := by
  have h1 : MeasurableSet {q : ℝ × ℂ | 1 / ((n : ℝ) + 1) ≤ |q.1|} :=
    measurableSet_le measurable_const (by fun_prop)
  have h2 : MeasurableSet {q : ℝ × ℂ | |q.1| ≤ (n : ℝ) + 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have h3 : MeasurableSet {q : ℝ × ℂ | ‖q.2‖ ≤ (n : ℝ) + 1} :=
    measurableSet_le (by fun_prop) measurable_const
  exact h1.inter (h2.inter h3)

lemma monotone_truncBox : Monotone truncBox := by
  intro m n hmn q hq
  obtain ⟨h1, h2, h3⟩ := hq
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  refine ⟨le_trans ?_ h1, h2.trans (by linarith), h3.trans (by linarith)⟩
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

lemma iUnion_truncBox : (⋃ n, truncBox n) = {q : ℝ × ℂ | q.1 ≠ 0} := by
  ext q
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨n, h1, -, -⟩ h0
    rw [h0, abs_zero] at h1
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro h0
    have hpos : 0 < |q.1| := abs_pos.mpr h0
    obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt hpos
    obtain ⟨n2, hn2⟩ := exists_nat_ge (max |q.1| ‖q.2‖)
    refine ⟨n1 + n2, ?_, ?_, ?_⟩
    · refine le_trans (one_div_le_one_div_of_le (by positivity) ?_) hn1.le
      push_cast; linarith [(Nat.cast_nonneg n2 : (0 : ℝ) ≤ n2)]
    · push_cast
      linarith [le_max_left |q.1| ‖q.2‖, (Nat.cast_nonneg n1 : (0 : ℝ) ≤ n1)]
    · push_cast
      linarith [le_max_right |q.1| ‖q.2‖, (Nat.cast_nonneg n1 : (0 : ℝ) ≤ n1)]

lemma volume_time_zero : (volume : Measure (ℝ × ℂ)) {q : ℝ × ℂ | q.1 = 0} = 0 := by
  have e : {q : ℝ × ℂ | q.1 = 0} = ({0} : Set ℝ) ×ˢ (univ : Set ℂ) := by
    ext q; simp
  rw [e, show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, Measure.prod_prod,
    Real.volume_singleton, zero_mul]

lemma isNiceWN_indicatorConstLp_truncBox {s : Set (ℝ × ℂ)} (hs : MeasurableSet s) (n : ℕ)
    (hμ : volume (s ∩ truncBox n) ≠ ∞) (c : ℝ) :
    IsNiceWN (indicatorConstLp 2 (hs.inter (measurableSet_truncBox n)) hμ c) := by
  refine ⟨1 / ((n : ℝ) + 1), (n : ℝ) + 1, |c|, (n : ℝ) + 1, by positivity, ?_, ?_⟩
  · filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs.inter (measurableSet_truncBox n))
      (hμs := hμ) (c := c)] with q hq
    rw [hq]
    by_cases h : q ∈ s ∩ truncBox n
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h, abs_zero]; exact abs_nonneg _
  · filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs.inter (measurableSet_truncBox n))
      (hμs := hμ) (c := c)] with q hq hne
    rw [hq] at hne
    by_cases h : q ∈ s ∩ truncBox n
    · exact h.2
    · rw [indicator_of_notMem h] at hne; exact absurd rfl hne

/-- Indicators of finite-measure sets are limits of nice vectors. -/
lemma indicatorConstLp_mem_closure {s : Set (ℝ × ℂ)} (hs : MeasurableSet s)
    (hμs : volume s ≠ ∞) (c : ℝ) :
    indicatorConstLp 2 hs hμs c ∈ niceSubmodule.topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  have hfin : ∀ n, volume (s ∩ truncBox n) ≠ ∞ := fun n =>
    measure_ne_top_of_subset inter_subset_left hμs
  have hdiff : ∀ n, (s ∩ truncBox n) ∆ s = s \ truncBox n := fun n => by
    ext q
    simp only [mem_symmDiff, mem_inter_iff, Set.mem_sdiff]
    tauto
  have hlim : Tendsto (fun n => volume ((s ∩ truncBox n) ∆ s)) atTop (𝓝 0) := by
    simp_rw [hdiff]
    have hanti : Antitone fun n => s \ truncBox n := fun m n hmn =>
      sdiff_subset_sdiff_right (monotone_truncBox hmn)
    have h := tendsto_measure_iInter_atTop (μ := volume)
      (fun n => (hs.diff (measurableSet_truncBox n)).nullMeasurableSet) hanti
      ⟨0, measure_ne_top_of_subset sdiff_subset hμs⟩
    have hI : (⋂ n, s \ truncBox n) ⊆ {q : ℝ × ℂ | q.1 = 0} := by
      intro q hq
      simp only [mem_iInter, Set.mem_sdiff] at hq
      by_contra h0
      have : q ∈ ⋃ n, truncBox n := by rw [iUnion_truncBox]; exact h0
      obtain ⟨n, hn⟩ := mem_iUnion.mp this
      exact (hq n).2 hn
    rwa [measure_mono_null hI volume_time_zero] at h
  refine mem_closure_of_tendsto (tendsto_indicatorConstLp_set (hs := hs) (hμs := hμs)
    (ht := fun n => hs.inter (measurableSet_truncBox n)) (hμt := hfin) (c := c)
    (by norm_num) hlim) (Eventually.of_forall fun n => ?_)
  exact isNiceWN_indicatorConstLp_truncBox hs n (hfin n) c

/-- **Density** of the nice vectors in `L²(ℝ × ℂ)`. -/
theorem niceSubmodule_topologicalClosure : niceSubmodule.topologicalClosure = ⊤ := by
  refine eq_top_iff.mpr fun f _ => ?_
  refine Lp.induction (p := 2) (by norm_num)
    (motive := fun f => f ∈ niceSubmodule.topologicalClosure) ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact indicatorConstLp_mem_closure hs hμs.ne c
  · intro f g hf hg _ hf' hg'
    exact Submodule.add_mem _ hf' hg'
  · exact niceSubmodule.isClosed_topologicalClosure

/-! ## An infinite linearly independent family of nice vectors -/

/-- The disjoint boxes `(n + 1, n + 2] × B̄₁(0)`. -/
def unitBox (n : ℕ) : Set (ℝ × ℂ) :=
  Ioc ((n : ℝ) + 1) ((n : ℝ) + 2) ×ˢ Metric.closedBall (0 : ℂ) 1

lemma measurableSet_unitBox (n : ℕ) : MeasurableSet (unitBox n) :=
  measurableSet_Ioc.prod measurableSet_closedBall

lemma volume_unitBox (n : ℕ) : volume (unitBox n) = volume (Metric.closedBall (0 : ℂ) 1) := by
  rw [unitBox, show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, Measure.prod_prod,
    Real.volume_Ioc, show (n : ℝ) + 2 - (n + 1) = 1 by ring, ENNReal.ofReal_one, one_mul]

lemma volume_unitBox_ne_top (n : ℕ) : volume (unitBox n) ≠ ∞ := by
  rw [volume_unitBox]; exact measure_closedBall_lt_top.ne

lemma volume_unitBox_pos (n : ℕ) : 0 < volume (unitBox n) := by
  rw [volume_unitBox]; exact Metric.measure_closedBall_pos _ _ one_pos

/-- The (unnormalized) indicator vectors `1_{unitBox n}` of the boxes. -/
def boxVec (n : ℕ) : WNSpace :=
  indicatorConstLp 2 (measurableSet_unitBox n) (volume_unitBox_ne_top n) (1 : ℝ)

lemma isNiceWN_boxVec (n : ℕ) : IsNiceWN (boxVec n) := by
  refine ⟨(n : ℝ) + 1, (n : ℝ) + 2, 1, 1, by positivity, ?_, ?_⟩
  · filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := measurableSet_unitBox n)
      (hμs := volume_unitBox_ne_top n) (c := (1 : ℝ))] with q hq
    rw [boxVec, hq]
    by_cases h : q ∈ unitBox n
    · rw [indicator_of_mem h, abs_one]
    · rw [indicator_of_notMem h, abs_zero]; exact zero_le_one
  · filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := measurableSet_unitBox n)
      (hμs := volume_unitBox_ne_top n) (c := (1 : ℝ))] with q hq hne
    rw [boxVec, hq] at hne
    by_cases h : q ∈ unitBox n
    · obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have h0 : 0 < q.1 := lt_trans (by positivity) h1
      rw [abs_of_pos h0]
      exact ⟨h1.le, h2, by simpa using h3⟩
    · rw [indicator_of_notMem h] at hne; exact absurd rfl hne

lemma disjoint_unitBox {m n : ℕ} (hmn : m ≠ n) : Disjoint (unitBox m) (unitBox n) := by
  rw [Set.disjoint_left]
  rintro q ⟨⟨h1, h2⟩, -⟩ ⟨⟨h3, h4⟩, -⟩
  rcases lt_or_gt_of_ne hmn with h | h
  · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith
  · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    linarith

lemma linearIndependent_boxVec : LinearIndependent ℝ boxVec := by
  refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun n => ?_) fun m n hmn => ?_
  · intro h0
    have h := congrArg (‖·‖) h0
    simp only [norm_zero, boxVec] at h
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul] at h
    have hpos : 0 < volume.real (unitBox n) :=
      ENNReal.toReal_pos (volume_unitBox_pos n).ne' (volume_unitBox_ne_top n)
    have : 0 < volume.real (unitBox n) ^ (1 / (2 : ℝ≥0∞).toReal) := Real.rpow_pos_of_pos hpos _
    linarith
  · show ⟪boxVec m, boxVec n⟫ = 0
    unfold boxVec
    rw [L2.inner_indicatorConstLp_one_indicatorConstLp_one (measurableSet_unitBox m)
      (measurableSet_unitBox n) (volume_unitBox_ne_top m) (volume_unitBox_ne_top n),
      (disjoint_unitBox hmn).inter_eq, measureReal_empty]
    rfl

end WNFrame

open WNFrame

/-! ## The Hilbert basis -/

/-- **A Hilbert basis of nice vectors** (blueprint Appendix B, "The frame"). -/
theorem exists_nice_hilbertBasis : ∃ b : HilbertBasis ℕ ℝ WNSpace, ∀ j, IsNiceWN (b j) := by
  -- a countable dense subset of the nice vectors
  have : Nonempty niceSubmodule := ⟨0⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq niceSubmodule
  set D : Set WNSpace := range fun n => (u n : WNSpace) with hD
  have hDN : D ⊆ niceSubmodule := by
    rintro _ ⟨n, rfl⟩; exact (u n).2
  have hND : (niceSubmodule : Set WNSpace) ⊆ closure D := by
    have h := Subtype.dense_iff.mp hu
    rwa [← range_comp] at h
  -- a linearly independent extension of the boxes inside `range boxVec ∪ D`
  set O : Set WNSpace := range boxVec with hO
  have hO_li : LinearIndepOn ℝ id O :=
    (linearIndepOn_id_range_iff linearIndependent_boxVec.injective).mpr linearIndependent_boxVec
  obtain ⟨B, hBt, hOB, htB, hBli⟩ := exists_linearIndepOn_id_extension hO_li
    (subset_union_left : O ⊆ O ∪ D)
  have hBN : B ⊆ niceSubmodule := by
    intro x hx
    rcases hBt hx with ⟨n, rfl⟩ | hxD
    · exact isNiceWN_boxVec n
    · exact hDN hxD
  have hBc : B.Countable :=
    ((countable_range boxVec).union (countable_range _)).mono hBt
  have hBi : B.Infinite :=
    (infinite_range_of_injective linearIndependent_boxVec.injective).mono hOB
  have : Countable B := hBc.to_subtype
  have : Infinite B := hBi.to_subtype
  obtain ⟨e⟩ : Nonempty (ℕ ≃ B) := nonempty_equiv_of_countable
  set f : ℕ → WNSpace := fun n => (e n : WNSpace) with hf
  have hfli : LinearIndependent ℝ f := by
    have h : LinearIndependent ℝ (fun x : B => (x : WNSpace)) := hBli
    exact h.comp e e.injective
  have hfr : range f = B := by
    rw [hf, show (fun n => (e n : WNSpace)) = ((↑) : B → WNSpace) ∘ e from rfl,
      e.surjective.range_comp, Subtype.range_coe]
  set v := InnerProductSpace.gramSchmidtNormed ℝ f with hv
  have hon : Orthonormal ℝ v := InnerProductSpace.gramSchmidtNormed_orthonormal hfli
  have hspan : Submodule.span ℝ (range v) = Submodule.span ℝ B := by
    rw [hv, InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt, hfr]
  have hsp : ⊤ ≤ (Submodule.span ℝ (range v)).topologicalClosure := by
    rw [hspan, ← niceSubmodule_topologicalClosure]
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
    intro x hx
    have h1 : x ∈ closure D := hND hx
    have h2 : closure D ⊆ closure (Submodule.span ℝ B : Set WNSpace) :=
      closure_mono (fun y hy => htB (subset_union_right hy))
    rw [← Submodule.topologicalClosure_coe] at h2
    exact h2 h1
  refine ⟨HilbertBasis.mk hon hsp, fun j => ?_⟩
  rw [HilbertBasis.coe_mk]
  have hmem : v j ∈ Submodule.span ℝ B := by
    rw [← hspan]; exact Submodule.subset_span (mem_range_self j)
  exact (Submodule.span_le.mpr hBN) hmem

end GaussianLQG
