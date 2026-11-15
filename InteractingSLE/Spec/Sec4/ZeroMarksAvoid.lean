/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.ZeroMarks
import InteractingSLE.Spec.Sec4.Prob41Lemmas

/-!
# Boundary avoidance when zero-weight marks collide (§4.1, `κ′ > 4` with the basic lower constants)

Packet PROVE-SEC4-A4, item (1). PROVE-SEC4-A3 proved boundary avoidance for words whose every side partial sum is at
least `c = k/2 − 2` (Remark 4.1). The frozen flow-line word keeps its seed marks with weight `0`; for `k > 4` and the
basic lower constants `−Λ`, `Λ` (Figures 4.1–4.4, "In the basic figure the lower lists are empty") these seeds collide
with the driver and that hypothesis fails. Deleting the zero-weight marks (`IsIntegratedSLEEvolution.dropZero`,
`ZeroMarks.lean`) gives an evolution of the word the source uses, with the same driver and lifetime.

* `HasAdmissibleNonzeroPartialSums`: every side partial sum that contains a mark of nonzero weight is at least `c`
  (no condition on a prefix of zero-weight marks: "One must not insert a zero seed force and demand `0 ≥ k/2 − 2` when
  `k > 4`", `PartialSums.lean`);
* `IsIntegratedSLEEvolution.ae_trace_ne_of_hasAdmissibleNonzeroPartialSums`: under it, almost surely `ζ = ∞` and
  every generating trace avoids the real points at or beyond every mark of nonzero weight (Aux. lemma 6 for the
  nonzero sub-word, `aux6Statement`, and SEC4-A3's avoidance);
* `IsIntegratedSLEEvolution.ae_tendsto_of_aux7_of_nonzero`: the limit at the target from Aux. lemma 7 (named input);
* `IsFlowLine.ae_trace_ne_of_nonzero` / `IsFlowLine.ae_tendsto_of_aux7_of_nonzero`: the flow line of data `b` that is
  at most `−Λ + πX` at every point `x < 0` beyond which (towards the seed) the data is not identically `−Λ`, and
  symmetrically on the right. Both Remark 4.1's data and the basic constants qualify. The trace avoids every real
  point `x < 0` such that the data differs from `−Λ` somewhere on `[x, 0)`, and symmetrically.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Real NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE

namespace Sec4

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-! ### Admissible partial sums over the nonzero marks -/

/-- The noncollision hypothesis of Aux. lemmas 6–7 for the marks of nonzero weight: every side prefix sum whose
prefix contains a mark of nonzero weight is at least `c = k/2 − 2` (a left prefix: the marks strictly right of some
`x < 0`; a right prefix: the marks at or left of some `x ≥ 0`). Prefixes of zero-weight marks are unconstrained. -/
def HasAdmissibleNonzeroPartialSums (k : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : Prop :=
  (∀ x : ℝ, x < 0 → (∃ i, ρL i ≠ 0 ∧ x < xL i) →
      k / 2 - 2 ≤ ∑ i ∈ Finset.univ.filter (fun i => x < xL i), ρL i) ∧
    ∀ x : ℝ, 0 ≤ x → (∃ i, ρR i ≠ 0 ∧ xR i ≤ x) →
      k / 2 - 2 ≤ ∑ i ∈ Finset.univ.filter (fun i => xR i ≤ x), ρR i

/-- Admissible partial sums are admissible over the nonzero marks. -/
theorem HasAdmissiblePartialSums.nonzero (h : HasAdmissiblePartialSums k ρL ρR xL xR) :
    HasAdmissibleNonzeroPartialSums k ρL ρR xL xR :=
  ⟨fun x hx ⟨i, _, hi⟩ => h.1 x hx ⟨i, hi⟩, fun x hx ⟨i, _, hi⟩ => h.2 x hx ⟨i, hi⟩⟩

/-- **The nonzero sub-word is admissible**: its partial sums are those of the full word (zero weights add nothing). -/
theorem HasAdmissibleNonzeroPartialSums.nonzeroWord (h : HasAdmissibleNonzeroPartialSums k ρL ρR xL xR) :
    HasAdmissiblePartialSums k (fun j => ρL (nonzeroEmb ρL j)) (fun j => ρR (nonzeroEmb ρR j))
      (fun j => xL (nonzeroEmb ρL j)) (fun j => xR (nonzeroEmb ρR j)) := by
  refine ⟨fun x hx ⟨j, hj⟩ => ?_, fun x hx ⟨j, hj⟩ => ?_⟩
  · rw [sum_filter_comp_embedding _ (nonzeroEmb ρL).injective ρL
      (fun _ hi => eq_zero_of_notMem_range_nonzeroEmb hi) (fun i => x < xL i)]
    exact h.1 x hx ⟨_, nonzero_nonzeroEmb ρL j, hj⟩
  · rw [sum_filter_comp_embedding _ (nonzeroEmb ρR).injective ρR
      (fun _ hi => eq_zero_of_notMem_range_nonzeroEmb hi) (fun i => xR i ≤ x)]
    exact h.2 x hx ⟨_, nonzero_nonzeroEmb ρR j, hj⟩

/-- The condition need only be checked off a finite set, through the boundary data of the word. -/
theorem hasAdmissibleNonzeroPartialSums_of_forall_not_mem (hk : 0 < k) (E : Finset ℝ)
    (hL : ∀ x : ℝ, x < 0 → x ∉ E → (∃ i, ρL i ≠ 0 ∧ x < xL i) →
      forceBoundaryData k ρL ρR xL xR x ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 ≤ x → x ∉ E → (∃ i, ρR i ≠ 0 ∧ xR i ≤ x) →
      sleLambda k - π * chiC k ≤ forceBoundaryData k ρL ρR xL xR x) :
    HasAdmissibleNonzeroPartialSums k ρL ρR xL xR := by
  refine ⟨fun x hx ⟨i, hρ, hi⟩ => ?_, fun x hx ⟨i, hρ, hi⟩ => ?_⟩
  · obtain ⟨x', h1, h2, hE, hS⟩ := exists_left_prefix_eq xL E hx
    have hi' : x' < xL i := by
      have : i ∈ Finset.univ.filter (fun i => x' < xL i) := by
        rw [hS]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
      exact (Finset.mem_filter.1 this).2
    have := (le_cumWeightLeft_iff hk).2 (hL x' h2 hE ⟨i, hρ, hi'⟩)
    rwa [cumWeightLeft_forceBoundaryData hk ρL ρR xL xR h2, hS] at this
  · obtain ⟨x', h1, hE, hS⟩ := exists_right_prefix_eq xR E x
    have hx' : 0 ≤ x' := hx.trans h1.le
    have hi' : xR i ≤ x' := hi.trans h1.le
    have := (le_cumWeightRight_iff hk).2 (hR x' hx' hE ⟨i, hρ, hi'⟩)
    rwa [cumWeightRight_forceBoundaryData hk ρL ρR xL xR hx', hS] at this

/-! ### Avoidance and limits for evolutions -/

/-- **Boundary avoidance beyond the nonzero marks.** For an ordered force word whose partial sums over its nonzero
marks are at least `k/2 − 2`, almost surely the lifetime is infinite and every generating trace avoids every real
point `x < 0` at or beyond a left mark of nonzero weight and every real point `x > 0` at or beyond a right mark of
nonzero weight. (Aux. lemma 6 for the nonzero sub-word, which is an evolution with the same driver and lifetime.) -/
theorem IsIntegratedSLEEvolution.ae_trace_ne_of_hasAdmissibleNonzeroPartialSums (hk : 0 < k)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hword : IsOrderedForceWord xL xR) (hadm : HasAdmissibleNonzeroPartialSums k ρL ρR xL xR)
    (h : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0,
      (∀ i, ρL i ≠ 0 → ∀ x : ℝ, x < 0 → x ≤ xL i → η ω t ≠ x) ∧
        ∀ i, ρR i ≠ 0 → ∀ x : ℝ, 0 < x → xR i ≤ x → η ω t ≠ x := by
  filter_upwards [IsIntegratedSLEEvolution.ae_trace_ne_of_hasAdmissiblePartialSums hk
    (hword.compEmb (nonzeroEmb ρL) (nonzeroEmb ρR)) hadm.nonzeroWord h.dropZero hη] with ω hω
  refine ⟨hω.1, fun t => ⟨fun i hi x hx hxi => ?_, fun i hi x hx hxi => ?_⟩⟩
  · obtain ⟨j, rfl⟩ := exists_nonzeroEmb_eq hi
    exact (hω.2 t).1 j x hx hxi
  · obtain ⟨j, rfl⟩ := exists_nonzeroEmb_eq hi
    exact (hω.2 t).2 j x hx hxi

/-- **The limit at the target over the nonzero marks** (from Aux. lemma 7, applied to the nonzero sub-word). -/
theorem IsIntegratedSLEEvolution.ae_tendsto_of_aux7_of_nonzero (h7 : Aux7Statement.{u} k)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hword : IsOrderedForceWord xL xR) (hadm : HasAdmissibleNonzeroPartialSums k ρL ρR xL xR)
    (h : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
        Tendsto (fun t => ‖η t‖) atTop atTop :=
  h7 _ _ _ _ P 𝓕 W _ _ B ζ (hword.compEmb (nonzeroEmb ρL) (nonzeroEmb ρR)) hadm.nonzeroWord
    h.dropZero

/-! ### One-sided limits of piecewise-constant data -/

/-- Off a finite set of candidates, `t` is eventually not a candidate as `t → z⁻`. -/
theorem eventually_notMem_nhdsLT (J : Finset ℝ) (z : ℝ) : ∀ᶠ t in 𝓝[<] z, t ∉ J := by
  have h1 : ((↑J : Set ℝ) \ {z})ᶜ ∈ 𝓝 z :=
    (J.finite_toSet.sdiff).isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with t ht htz htJ
  exact ht ⟨htJ, ne_of_lt htz⟩

/-- Off a finite set of candidates, `t` is eventually not a candidate as `t → z⁺`. -/
theorem eventually_notMem_nhdsGT (J : Finset ℝ) (z : ℝ) : ∀ᶠ t in 𝓝[>] z, t ∉ J := by
  have h1 : ((↑J : Set ℝ) \ {z})ᶜ ∈ 𝓝 z :=
    (J.finite_toSet.sdiff).isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with t ht htz htJ
  exact ht ⟨htJ, ne_of_gt htz⟩

/-- The left limit at `z` of data equal to `c` on `(a, z)` off a finite set. -/
theorem leftLim_eq_of_forall_notMem {b : ℝ → ℝ} (J : Finset ℝ) {a z c : ℝ} (haz : a < z)
    (h : ∀ t ∈ Ioo a z, t ∉ J → b t = c) : leftLim b z = c := by
  unfold PiecewiseConstantBoundaryData.leftLim
  refine Filter.Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [Ioo_mem_nhdsLT haz, eventually_notMem_nhdsLT J z] with t ht htJ
  exact (h t ht htJ).symm

/-- The right limit at `z` of data equal to `c` on `(z, a)` off a finite set. -/
theorem rightLim_eq_of_forall_notMem {b : ℝ → ℝ} (J : Finset ℝ) {z a c : ℝ} (hza : z < a)
    (h : ∀ t ∈ Ioo z a, t ∉ J → b t = c) : rightLim b z = c := by
  unfold PiecewiseConstantBoundaryData.rightLim
  refine Filter.Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT hza, eventually_notMem_nhdsGT J z] with t ht htJ
  exact (h t ht htJ).symm

/-! ### A boundary value off the basic constant forces a nonzero mark -/

/-- If the boundary data of a word at `y < 0` is not `−Λ`, some left mark of nonzero weight lies right of `y`. -/
theorem exists_nonzero_left_of_forceBoundaryData_ne {x y : ℝ} (hxy : x ≤ y) (hy : y < 0)
    (hne : forceBoundaryData k ρL ρR xL xR y ≠ -sleLambda k) : ∃ i, ρL i ≠ 0 ∧ x ≤ xL i := by
  rw [forceBoundaryData_of_neg ρL ρR xL xR hy] at hne
  have hS : ∑ i ∈ Finset.univ.filter (fun i => y < xL i), ρL i ≠ 0 := by
    intro h0; apply hne; rw [h0]; ring
  obtain ⟨i, hi, hρ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  exact ⟨i, hρ, hxy.trans (Finset.mem_filter.1 hi).2.le⟩

/-- If the boundary data of a word at `y > 0` is not `Λ`, some right mark of nonzero weight lies left of `y`. -/
theorem exists_nonzero_right_of_forceBoundaryData_ne {x y : ℝ} (hyx : y ≤ x) (hy : 0 < y)
    (hne : forceBoundaryData k ρL ρR xL xR y ≠ sleLambda k) : ∃ i, ρR i ≠ 0 ∧ xR i ≤ x := by
  rw [forceBoundaryData_of_nonneg ρL ρR xL xR hy.le] at hne
  have hS : ∑ i ∈ Finset.univ.filter (fun i => xR i ≤ y), ρR i ≠ 0 := by
    intro h0; apply hne; rw [h0]; ring
  obtain ⟨i, hi, hρ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  exact ⟨i, hρ, (Finset.mem_filter.1 hi).2.trans hyx⟩

/-! ### Flow lines -/

variable {b : ℝ → ℝ} {J : Finset ℝ}

/-- **The flow-line word is admissible over its nonzero marks** when the boundary data is at most `−Λ + πX` at
every point `x < 0` such that the data differs from `−Λ` somewhere on `[x, 0)`, and at least `Λ − πX` at every point
`x > 0` such that the data differs from `Λ` somewhere on `(0, x]` (off the jump candidates). If the data is
identically `−Λ` on `[x, 0)`, every mark in `(x, 0]` (the seed and the jumps there) has weight `0`. -/
theorem hasAdmissibleNonzeroPartialSums_flowLine (hk : 0 < k)
    (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ J ∧ b y ≠ -sleLambda k) →
      b x ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ J ∧ b y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ b x) :
    HasAdmissibleNonzeroPartialSums k (flowLineRhoL k b J 0 0) (flowLineRhoR k b J 0 0)
      (flowLineXL b J 0) (flowLineXR b J 0) := by
  have hΛ : sleLambda k ≠ 0 := sleLambda_ne_zero hk
  refine hasAdmissibleNonzeroPartialSums_of_forall_not_mem hk (insert 0 J)
    (fun x hx hxE hi => ?_) (fun x hx hxE hi => ?_)
  · have hxJ : x ∉ J := fun h => hxE (Finset.mem_insert_of_mem h)
    rw [forceBoundaryData_flowLine hk hb hx.ne hxJ]
    refine hL x hx hxJ ?_
    by_contra hcon
    have hc : ∀ y, x ≤ y → y < 0 → y ∉ J → b y = -sleLambda k := fun y h1 h2 h3 => by
      by_contra hne; exact hcon ⟨y, h1, h2, h3, hne⟩
    obtain ⟨i, hρ, hi⟩ := hi
    revert hρ hi
    unfold flowLineRhoL flowLineXL flowLineNL
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hρ _
      apply hρ
      have hlim : leftLim b 0 = -sleLambda k :=
        leftLim_eq_of_forall_notMem J hx fun t ht htJ => hc t ht.1.le ht.2 htJ
      rw [Fin.cons_zero, hlim]
      field_simp
      ring
    · intro hρ hi
      rw [Fin.cons_succ] at hρ hi
      simp only at hρ
      rw [sub_zero] at hi
      have hmem := ((jumpSet b J).filter (· < 0)).orderEmbOfFin_mem rfl (Fin.rev j)
      generalize ((jumpSet b J).filter (· < 0)).orderEmbOfFin rfl (Fin.rev j) = y at hρ hi hmem
      have hy0 : y < 0 := (Finset.mem_filter.1 hmem).2
      apply hρ
      have h1 : leftLim b y = -sleLambda k :=
        leftLim_eq_of_forall_notMem J hi fun t ht htJ => hc t ht.1.le (ht.2.trans hy0) htJ
      have h2 : rightLim b y = -sleLambda k :=
        rightLim_eq_of_forall_notMem J hy0 fun t ht htJ => hc t (hi.le.trans ht.1.le) ht.2 htJ
      rw [h1, h2, sub_self, zero_div]
  · have hx0 : x ≠ 0 := fun h => hxE (h ▸ Finset.mem_insert_self 0 J)
    have hxJ : x ∉ J := fun h => hxE (Finset.mem_insert_of_mem h)
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [forceBoundaryData_flowLine hk hb hx0 hxJ]
    refine hR x hxpos hxJ ?_
    by_contra hcon
    have hc : ∀ y, 0 < y → y ≤ x → y ∉ J → b y = sleLambda k := fun y h1 h2 h3 => by
      by_contra hne; exact hcon ⟨y, h1, h2, h3, hne⟩
    obtain ⟨i, hρ, hi⟩ := hi
    revert hρ hi
    unfold flowLineRhoR flowLineXR flowLineNR
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hρ _
      apply hρ
      have hlim : rightLim b 0 = sleLambda k :=
        rightLim_eq_of_forall_notMem J hxpos fun t ht htJ => hc t ht.1 ht.2.le htJ
      rw [Fin.cons_zero, hlim]
      field_simp
      ring
    · intro hρ hi
      rw [Fin.cons_succ] at hρ hi
      simp only at hρ
      rw [sub_zero] at hi
      have hmem := ((jumpSet b J).filter (0 < ·)).orderEmbOfFin_mem rfl j
      generalize ((jumpSet b J).filter (0 < ·)).orderEmbOfFin rfl j = y at hρ hi hmem
      have hy0 : 0 < y := (Finset.mem_filter.1 hmem).2
      have hyJ : y ∈ J := (Finset.mem_filter.1 (Finset.mem_filter.1 hmem).1).1
      have hyx' : y < x := lt_of_le_of_ne hi fun h => hxJ (h ▸ hyJ)
      apply hρ
      have h1 : leftLim b y = sleLambda k :=
        leftLim_eq_of_forall_notMem J hy0 fun t ht htJ => hc t ht.1 (ht.2.le.trans hi) htJ
      have h2 : rightLim b y = sleLambda k :=
        rightLim_eq_of_forall_notMem J hyx' fun t ht htJ => hc t (hy0.trans ht.1) ht.2.le htJ
      rw [h1, h2, sub_self, zero_div]

/-- **Boundary avoidance for flow lines whose seed marks may have weight zero** (`κ′ > 4` with the basic lower
constants; the passive-mark step of Lemmas 4.3, 4.5 and Aux. lemma 22 for the source's words, whose lower lists are
empty in the basic figure). If the boundary data is at most `−Λ + πX` at every `x < 0` such that it differs from
`−Λ` somewhere on `[x, 0)`, and at least `Λ − πX` at every `x > 0` such that it differs from `Λ` somewhere on
`(0, x]` (off the candidates), then almost surely the flow line from `0` has infinite lifetime and never visits a real
point `x < 0` such that the data differs from `−Λ` somewhere on `[x, 0)`, nor a real point `x > 0` such that the data
differs from `Λ` somewhere on `(0, x]`. -/
theorem IsFlowLine.ae_trace_ne_of_nonzero (hk : 0 < k) (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ J ∧ b y ≠ -sleLambda k) →
      b x ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ J ∧ b y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ b x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine k b J 0 0 P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0,
      (∀ x : ℝ, x < 0 → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ J ∧ b y ≠ -sleLambda k) → η ω t ≠ x) ∧
        ∀ x : ℝ, 0 < x → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ J ∧ b y ≠ sleLambda k) → η ω t ≠ x := by
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := IsFlowLine.exists_evolution hfl
  have hword := Theorem15.isOrderedForceWord_flowLine b J 0
  have hadm := hasAdmissibleNonzeroPartialSums_flowLine hk hb hL hR
  filter_upwards [IsIntegratedSLEEvolution.ae_trace_ne_of_hasAdmissibleNonzeroPartialSums hk hword
    hadm hev htr] with ω hω
  refine ⟨hω.1, fun t => ⟨fun x hx ⟨y, hxy, hy, hyJ, hby⟩ => ?_,
    fun x hx ⟨y, hy, hyx, hyJ, hby⟩ => ?_⟩⟩
  · rw [← forceBoundaryData_flowLine hk hb hy.ne hyJ] at hby
    obtain ⟨i, hρ, hi⟩ := exists_nonzero_left_of_forceBoundaryData_ne hxy hy hby
    exact (hω.2 t).1 i hρ x hx hi
  · rw [← forceBoundaryData_flowLine hk hb hy.ne' hyJ] at hby
    obtain ⟨i, hρ, hi⟩ := exists_nonzero_right_of_forceBoundaryData_ne hyx hy hby
    exact (hω.2 t).2 i hρ x hx hi

/-- **Boundary avoidance and the limit at the target for flow lines whose seed marks may have weight zero**
(from Aux. lemma 7 applied to the nonzero sub-word). -/
theorem IsFlowLine.ae_tendsto_of_aux7_of_nonzero (h7 : Aux7Statement.{u} k) (hk : 0 < k)
    (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ J ∧ b y ≠ -sleLambda k) →
      b x ≤ -sleLambda k + π * chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ J ∧ b y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ b x)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine k b J 0 0 P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0,
      (∀ x : ℝ, x < 0 → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ J ∧ b y ≠ -sleLambda k) → η ω t ≠ x) ∧
        ∀ x : ℝ, 0 < x → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ J ∧ b y ≠ sleLambda k) → η ω t ≠ x) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop := by
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := IsFlowLine.exists_evolution hfl
  have hword := Theorem15.isOrderedForceWord_flowLine b J 0
  have hadm := hasAdmissibleNonzeroPartialSums_flowLine hk hb hL hR
  filter_upwards [IsFlowLine.ae_trace_ne_of_nonzero hk hb hL hR hfl,
    IsIntegratedSLEEvolution.ae_tendsto_of_aux7_of_nonzero h7 hword hadm hev, htr] with ω h1 h2 h3
  rw [h1.1] at h3
  exact ⟨h1.1, h1.2, h2.2.2 _ h3⟩

/-! ### For `k ≤ 4` the condition is Remark 4.1's -/

/-- `πX ≥ 0` for `0 < k ≤ 4`. -/
theorem pi_mul_chiC_nonneg (hk : 0 < k) (hk4 : k ≤ 4) : 0 ≤ π * chiC k := by
  rw [pi_mul_chiC hk]
  exact mul_nonneg (by linarith) (sleLambda_pos hk).le

/-- `πX < 0` for `k > 4`. -/
theorem pi_mul_chiC_neg (hk4 : 4 < k) : π * chiC k < 0 := by
  have hk : 0 < k := by linarith
  rw [pi_mul_chiC hk]
  exact mul_neg_of_neg_of_pos (by linarith) (sleLambda_pos hk)

/-- For `k ≤ 4` the left condition above is Remark 4.1's (`−Λ ≤ −Λ + πX`). -/
theorem le_of_forall_exists_ne_left_of_le_four (hk : 0 < k) (hk4 : k ≤ 4)
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → (∃ y, x ≤ y ∧ y < 0 ∧ y ∉ J ∧ b y ≠ -sleLambda k) →
      b x ≤ -sleLambda k + π * chiC k) {x : ℝ} (hx : x < 0) (hxJ : x ∉ J) :
    b x ≤ -sleLambda k + π * chiC k := by
  by_cases hbx : b x = -sleLambda k
  · rw [hbx]; linarith [pi_mul_chiC_nonneg hk hk4]
  · exact hL x hx hxJ ⟨x, le_rfl, hx, hxJ, hbx⟩

/-- For `k ≤ 4` the right condition above is Remark 4.1's (`Λ − πX ≤ Λ`). -/
theorem le_of_forall_exists_ne_right_of_le_four (hk : 0 < k) (hk4 : k ≤ 4)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → (∃ y, 0 < y ∧ y ≤ x ∧ y ∉ J ∧ b y ≠ sleLambda k) →
      sleLambda k - π * chiC k ≤ b x) {x : ℝ} (hx : 0 < x) (hxJ : x ∉ J) :
    sleLambda k - π * chiC k ≤ b x := by
  by_cases hbx : b x = sleLambda k
  · rw [hbx]; linarith [pi_mul_chiC_nonneg hk hk4]
  · exact hR x hx hxJ ⟨x, hx, le_rfl, hxJ, hbx⟩

end Sec4

end InteractingSLE
