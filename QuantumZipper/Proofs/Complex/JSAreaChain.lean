import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Order.Compact

/-!
# EXT-JS node A5: the one-dimensional chain lemma

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 step C0.4 and §3 (node A5).

Let `E : ℝ → F` satisfy `E v - E u = ∫_u^v γ` on every subinterval `[u,v] ⊆ [a,b]` whose
interior misses a closed set `S ⊆ [a,b]`, and let finitely many closed sets `C i` cover `S`, with
the oscillation of `E` on `C i ∩ [a,b]` at most `ω i`. Then
`‖E b - E a - ∫_a^b γ‖ ≤ Σ ω i + ∫_{(a,b] ∩ ⋃ hull (C i ∩ [a,b])} ‖γ‖`.

Proof: induction on the number of sets. With `s₀ = min S`, pick `i` with `s₀ ∈ C i`, and let
`M = max (C i ∩ [a,b])`. Then `E s₀ - E a = ∫_a^{s₀} γ`, `‖E M - E s₀‖ ≤ ω i`,
`‖∫_{s₀}^M γ‖ ≤ ∫_{(s₀,M]} ‖γ‖` with `(s₀, M] ⊆ hull (C i ∩ [a,b])`, and the induction hypothesis
applies on `[M,b]` to `closure (S ∩ (M,b])` (covered by the `C j`, `j ≠ i`) and the other sets.
This is the one-dimensional cutting step in Jones–Smirnov, *Removability theorems for Sobolev
functions and quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2, proof of Proposition 1:
the cutting of `[x_j, y_j]` into intervals `[u_i, u_{i+1}]` that either miss `K` or lie in one
shadow, leading to estimate (10) (`literature/JonesSmirnov_Removability_ArkMat2000.pdf`).

Compared with the blueprint shape: the hypothesis "`E` continuous" is not needed and is omitted,
the hypothesis `0 ≤ ω i` is added (otherwise an unused `C i` with `ω i < 0` breaks the bound),
and the integral is over `(a,b] ∩ ⋃ …` (a subset of the blueprint's `[a,b] ∩ ⋃ …`, so the bound
is stronger).
-/

noncomputable section

open MeasureTheory Set

namespace QuantumZipper.JS

/-- **A5 (1D chain lemma).** -/
theorem chain1D {ι : Type*} [DecidableEq ι] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (s : Finset ι) (C : ι → Set ℝ) (hC : ∀ i ∈ s, IsClosed (C i)) (ω : ι → ℝ)
    (hω0 : ∀ i ∈ s, 0 ≤ ω i) {E γ : ℝ → F} {a b : ℝ} (hab : a ≤ b)
    (hγ : IntegrableOn γ (Icc a b)) {S : Set ℝ} (hS : IsClosed S) (hSab : S ⊆ Icc a b)
    (hloc : ∀ u v, a ≤ u → u ≤ v → v ≤ b → Ioo u v ∩ S = ∅ → E v - E u = ∫ t in u..v, γ t)
    (hcov : S ⊆ ⋃ i ∈ s, C i)
    (hω : ∀ i ∈ s, ∀ p ∈ C i ∩ Icc a b, ∀ q ∈ C i ∩ Icc a b, ‖E p - E q‖ ≤ ω i) :
    ‖E b - E a - ∫ t in a..b, γ t‖ ≤
      ∑ i ∈ s, ω i + ∫ t in Ioc a b ∩ ⋃ i ∈ s, convexHull ℝ (C i ∩ Icc a b), ‖γ t‖ := by
  induction s using Finset.strongInduction generalizing a S with
  | H s ih =>
  have hRHS0 : 0 ≤ ∑ i ∈ s, ω i + ∫ t in Ioc a b ∩ ⋃ i ∈ s, convexHull ℝ (C i ∩ Icc a b),
      ‖γ t‖ :=
    add_nonneg (Finset.sum_nonneg hω0) (integral_nonneg fun _ => norm_nonneg _)
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hloc a b le_rfl hab le_rfl (by rw [hSe, inter_empty]), sub_self, norm_zero]
    exact hRHS0
  -- the first point of `S`
  have hSbdd : BddBelow S := ⟨a, fun x hx => (hSab hx).1⟩
  set s₀ := sInf S with hs₀
  have hs₀S : s₀ ∈ S := hS.csInf_mem hSne hSbdd
  have hs₀le : ∀ x ∈ S, s₀ ≤ x := fun x hx => csInf_le hSbdd hx
  obtain ⟨ha₀, h₀b⟩ := hSab hs₀S
  obtain ⟨i, hi, hs₀i⟩ : ∃ i ∈ s, s₀ ∈ C i := by
    simpa only [mem_iUnion, exists_prop] using hcov hs₀S
  -- the last point of `C i ∩ [a,b]`
  set X := C i ∩ Icc a b with hX
  have hXc : IsCompact X := isCompact_Icc.inter_left (hC i hi)
  have hs₀X : s₀ ∈ X := ⟨hs₀i, ha₀, h₀b⟩
  set M := sSup X with hM
  have hMX : M ∈ X := hXc.sSup_mem ⟨s₀, hs₀X⟩
  have hXle : ∀ x ∈ X, x ≤ M := fun x hx => le_csSup hXc.bddAbove hx
  have hs₀M : s₀ ≤ M := hXle s₀ hs₀X
  obtain ⟨-, hMb⟩ := hMX.2
  have haM : a ≤ M := ha₀.trans hs₀M
  -- step 1: no point of `S` before `s₀`
  have hstep1 : E s₀ - E a = ∫ t in a..s₀, γ t :=
    hloc a s₀ le_rfl ha₀ h₀b
      (subset_empty_iff.1 fun x hx => absurd (hs₀le x hx.2) (not_le.2 hx.1.2))
  have hII : ∀ u v, a ≤ u → u ≤ v → v ≤ b → IntervalIntegrable γ volume u v :=
    fun u v hu huv hv => (intervalIntegrable_iff_integrableOn_Icc_of_le huv).2
      (hγ.mono_set (Icc_subset_Icc hu hv))
  -- induction hypothesis on `[M, b]`
  set S' := closure (S ∩ Ioc M b) with hS'
  have hS'sub : S' ⊆ Icc M b :=
    isClosed_Icc.closure_subset_iff.2 fun x hx => ⟨hx.2.1.le, hx.2.2⟩
  have hloc' : ∀ u v, M ≤ u → u ≤ v → v ≤ b → Ioo u v ∩ S' = ∅ →
      E v - E u = ∫ t in u..v, γ t := by
    intro u v hu huv hv hempty
    refine hloc u v (haM.trans hu) huv hv (subset_empty_iff.1 ?_)
    rintro x ⟨hx, hxS⟩
    have hxS' : x ∈ S' := subset_closure ⟨hxS, hu.trans_lt hx.1, hx.2.le.trans hv⟩
    exact hempty.subset ⟨hx, hxS'⟩
  have hcov' : S' ⊆ ⋃ j ∈ s.erase i, C j := by
    refine closure_minimal ?_ (isClosed_biUnion_finset fun j hj =>
      hC j (Finset.mem_of_mem_erase hj))
    rintro x ⟨hxS, hMx, hxb⟩
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 (hcov hxS)
    have hji : j ≠ i := by
      rintro rfl
      exact absurd (hXle x ⟨hxj, hSab hxS⟩) (not_le.2 hMx)
    exact mem_iUnion₂.2 ⟨j, Finset.mem_erase.2 ⟨hji, hj⟩, hxj⟩
  have hIH := ih (s.erase i) (Finset.erase_ssubset hi)
    (hC := fun j hj => hC j (Finset.mem_of_mem_erase hj))
    (hω0 := fun j hj => hω0 j (Finset.mem_of_mem_erase hj))
    (hab := hMb) (hγ := hγ.mono_set (Icc_subset_Icc haM le_rfl)) (hS := isClosed_closure)
    (hSab := hS'sub) (hloc := hloc') (hcov := hcov')
    (hω := fun j hj p hp q hq => hω j (Finset.mem_of_mem_erase hj) p
      ⟨hp.1, haM.trans hp.2.1, hp.2.2⟩ q ⟨hq.1, haM.trans hq.2.1, hq.2.2⟩)
  -- the splitting
  have hsplit : E b - E a - ∫ t in a..b, γ t =
      (E M - E s₀ - ∫ t in s₀..M, γ t) + (E b - E M - ∫ t in M..b, γ t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hII a s₀ le_rfl ha₀ h₀b)
      (hII s₀ b ha₀ h₀b le_rfl), ← intervalIntegral.integral_add_adjacent_intervals
      (hII s₀ M ha₀ hs₀M hMb) (hII M b haM hMb le_rfl)]
    have : E s₀ = E a + ∫ t in a..s₀, γ t := by rw [← hstep1]; abel
    rw [this]; abel
  have hosc : ‖E M - E s₀‖ ≤ ω i := hω i hi M hMX s₀ hs₀X
  have hint1 : ‖∫ t in s₀..M, γ t‖ ≤ ∫ t in Ioc s₀ M, ‖γ t‖ :=
    (intervalIntegral.norm_integral_le_integral_norm hs₀M).trans_eq
      (intervalIntegral.integral_of_le hs₀M)
  set U := ⋃ j ∈ s, convexHull ℝ (C j ∩ Icc a b) with hU
  set U' := ⋃ j ∈ s.erase i, convexHull ℝ (C j ∩ Icc M b) with hU'
  have hsub1 : Ioc s₀ M ⊆ Ioc a b ∩ U := fun x hx =>
    ⟨⟨ha₀.trans_lt hx.1, hx.2.trans hMb⟩, mem_iUnion₂.2 ⟨i, hi,
      segment_subset_convexHull hs₀X hMX (by rw [segment_eq_Icc hs₀M]; exact Ioc_subset_Icc_self hx)⟩⟩
  have hsub2 : Ioc M b ∩ U' ⊆ Ioc a b ∩ U := by
    rintro x ⟨hx, hxU⟩
    refine ⟨⟨haM.trans_lt hx.1, hx.2⟩, ?_⟩
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hxU
    exact mem_iUnion₂.2 ⟨j, Finset.mem_of_mem_erase hj,
      convexHull_mono (inter_subset_inter_right _ (Icc_subset_Icc haM le_rfl)) hxj⟩
  have hdisj : Disjoint (Ioc M b ∩ U') (Ioc s₀ M) :=
    disjoint_left.2 fun x hx hx' => absurd hx.1.1 (not_lt.2 hx'.2)
  have hint : IntegrableOn (fun t => ‖γ t‖) (Ioc a b ∩ U) :=
    (show IntegrableOn (fun t => ‖γ t‖) (Icc a b) volume from hγ.norm).mono_set
      (inter_subset_left.trans Ioc_subset_Icc_self)
  have hcomb : (∫ t in Ioc s₀ M, ‖γ t‖) + (∫ t in Ioc M b ∩ U', ‖γ t‖) ≤
      ∫ t in Ioc a b ∩ U, ‖γ t‖ := by
    rw [_root_.add_comm, ← setIntegral_union hdisj measurableSet_Ioc (hint.mono_set hsub2)
      (hint.mono_set hsub1)]
    exact setIntegral_mono_set hint (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (union_subset hsub2 hsub1).eventuallyLE
  calc ‖E b - E a - ∫ t in a..b, γ t‖
      = ‖(E M - E s₀ - ∫ t in s₀..M, γ t) + (E b - E M - ∫ t in M..b, γ t)‖ := by rw [hsplit]
    _ ≤ ‖E M - E s₀‖ + ‖∫ t in s₀..M, γ t‖ + ‖E b - E M - ∫ t in M..b, γ t‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ ω i + (∫ t in Ioc s₀ M, ‖γ t‖) + (∑ j ∈ s.erase i, ω j + ∫ t in Ioc M b ∩ U', ‖γ t‖) := by
        gcongr
    _ = (ω i + ∑ j ∈ s.erase i, ω j) + ((∫ t in Ioc s₀ M, ‖γ t‖) + ∫ t in Ioc M b ∩ U', ‖γ t‖) := by
        ring
    _ ≤ ∑ j ∈ s, ω j + ∫ t in Ioc a b ∩ U, ‖γ t‖ := by
        rw [Finset.add_sum_erase s ω hi]; gcongr

end QuantumZipper.JS
