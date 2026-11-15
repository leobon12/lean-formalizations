/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCBBuffer
import InteractingSLE.Spec.Supplement.G7RetainedReduce

/-!
# The canonical seed germs of the retained chart datum

Packet PROVE-RLC-B, step (ii) of `planning/handoffs/PROVE-RLC-A.md` ("the seed heights at the first tip"). Source:
"Verification of hypotheses for retained original histories" after Lemma G3 (supplement p. 493: "If both tips
satisfy the first condition, the physical separation from the other retained prefix supplies protected collars
around their own tip sides. Nested boundary comparison gives the single-flow canonical germs there"), W0a's proof
(p. 528: "positive initial lifetime requires both seed groups to exceed `−2`").

The retained word `c` of the restart (`Supp7.IsRetainedWord`, the outer word of Aux. 85–86) gives the exact heights
`−λ − θ₂χ`, `λ − θ₂χ` at chart points whose inverse-chart image is an interior point of the second prefix, and only
`∓λ − θ₁χ` (no side) on the first prefix. Here:

* **the fibers of the retained chart over the two tips are single points** (`eq_zero_of_inv_eq_tip₂`,
  `eq_of_inv_eq_tip₁`: both tips are regular points of the chart, `isChartRegularPoint_tip₂`, `…_tip₁`), so near `0`
  and near the first tip's chart position `W` every real chart point maps to an interior non-tip point of the
  corresponding prefix, and the word has no jump there and the stated heights (`exists_wordGerm_of_retChart`);
* **the side at `W` is forced by positive lifetime**: if the height just left (right) of `W` were `λ − θ₁χ`
  (`−λ − θ₁χ`), the left (right) seed weight of the angle-`θ₁` flow from `W` would be `−2`, so its lifetime is `0`
  almost surely (`ae_eq_zero_of_mem_badSeed`, from `Supp9.ae_seedWeights_of_isFlowLine`); `BadSeed` is a measurable
  set of data (`measurableSet_badSeed`);
* `mem_hasSeedGerms_of_wordGerm`: the word facts at `0` and `W` and `(c, W) ∉ BadSeed` give `HasSeedGerms`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

open Supp7 Restart

/-! ### The tips are regular points of the retained chart -/

section Regular

variable {α β : ℝ≥0 → ℂ} {a b : ℝ≥0}

/-- **The second tip is a regular point** (it is off the first prefix and not visited earlier by the second path). -/
theorem isChartRegularPoint_tip₂ (hc₁ : ContinuousOn α (Icc 0 a)) (hc₂ : ContinuousOn β (Icc 0 b))
    (h0₁ : (α 0).im = 0) (h0₂ : (β 0).im = 0) (hp : β b ∉ α '' Icc 0 a) (hne : ∀ t < b, β t ≠ β b) :
    IsChartRegularPoint α a β b (β b) := by
  refine Or.inr (isUnboundedLinked_of_forall fun z hz hzq => ?_)
  rcases hz with hz | ⟨t, ht, rfl⟩
  · exact ⟨α '' Icc 0 a, subset_union_left, isPreconnected_Icc.image _ hc₁, hz, hp, α 0,
      ⟨0, left_mem_Icc.2 zero_le, rfl⟩, h0₁⟩
  · have htb : t < b := lt_of_le_of_ne ht.2 fun h => hzq (by rw [h])
    refine ⟨β '' Icc 0 t, fun x hx => Or.inr (image_mono (Icc_subset_Icc_right htb.le) hx),
      isPreconnected_Icc.image _ (hc₂.mono (Icc_subset_Icc_right htb.le)), ⟨t, right_mem_Icc.2 zero_le, rfl⟩,
      ?_, β 0, ⟨0, left_mem_Icc.2 zero_le, rfl⟩, h0₂⟩
    rintro ⟨t', ht', he⟩
    exact hne t' (lt_of_le_of_lt ht'.2 htb) he

/-- **The first tip is a regular point** (it is off the second prefix and the first prefix is simple). -/
theorem isChartRegularPoint_tip₁ (hc₁ : ContinuousOn α (Icc 0 a)) (hc₂ : ContinuousOn β (Icc 0 b))
    (h0₁ : (α 0).im = 0) (h0₂ : (β 0).im = 0) (hq : α a ∉ β '' Icc 0 b) (hi : InjOn α (Icc 0 a)) :
    IsChartRegularPoint α a β b (α a) := by
  refine Or.inr (isUnboundedLinked_of_forall fun z hz hzq => ?_)
  rcases hz with ⟨s, hs, rfl⟩ | hz
  · have hsa : s < a := lt_of_le_of_ne hs.2 fun h => hzq (by rw [h])
    refine ⟨α '' Icc 0 s, fun x hx => Or.inl (image_mono (Icc_subset_Icc_right hsa.le) hx),
      isPreconnected_Icc.image _ (hc₁.mono (Icc_subset_Icc_right hsa.le)), ⟨s, right_mem_Icc.2 zero_le, rfl⟩,
      ?_, α 0, ⟨0, left_mem_Icc.2 zero_le, rfl⟩, h0₁⟩
    rintro ⟨s', hs', he⟩
    have := hi ⟨hs'.1, hs'.2.trans hsa.le⟩ ⟨zero_le, le_rfl⟩ he
    exact absurd (this ▸ hs'.2) (not_le.2 hsa)
  · exact ⟨β '' Icc 0 b, subset_union_right, isPreconnected_Icc.image _ hc₂, hz, hq, β 0,
      ⟨0, left_mem_Icc.2 zero_le, rfl⟩, h0₂⟩

variable {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

/-- **The fiber of the retained chart over a regular point with a known preimage is that preimage.** -/
theorem eq_of_inv_eq_of_regular (hC : IsRetChart α a β b φ ψ lift) (h0₂ : (β 0).im = 0) {z w₀ w : ℂ}
    (hreg : IsChartRegularPoint α a β b z) (hw₀ : w₀ ∈ Hbar) (hz : ψ w₀ = z) (hw : w ∈ Hbar) (he : ψ w = z) :
    w = w₀ := by
  obtain ⟨v, -, -, -, hu⟩ := hC.exists_tendsto_of_regular h0₂ (hz ▸ inv_mem_closure hC h0₂ hw₀) hreg
  exact (hu w hw he).trans (hu w₀ hw₀ hz).symm

end Regular

/-! ### The word near the two chart seeds -/

/-- **The retained word near the chart seeds** (the protected collars of p. 493): near `0` it has no jump other
than `0` and the canonical heights `−λ − θ₂χ`, `λ − θ₂χ`; near the first tip's chart position `W` it has no jump
other than `W` and heights in `{−λ − θ₁χ, λ − θ₁χ}`. -/
theorem exists_wordGerm_of_retChart {κ θ₁ θ₂ : ℝ} {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}
    (hC : IsRetChart α a β b φ ψ lift) (hc₁ : ContinuousOn α (Icc 0 a)) (hc₂ : ContinuousOn β (Icc 0 b))
    (h0₁ : (α 0).im = 0) (h0₂ : (β 0).im = 0) (hpH : β b ∈ H) (hp : β b ∉ α '' Icc 0 a)
    (hne : ∀ t < b, β t ≠ β b) (hqH : α a ∈ H) (hq : α a ∉ β '' Icc 0 b) (hi : InjOn α (Icc 0 a)) {W : ℝ}
    (hW : ψ W = α a) {c : BoundaryWord} (hw : IsRetainedWord κ θ₁ θ₂ α a β b ψ c) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ y : ℝ, y ≠ 0 → |y| < δ → y ∉ c.jumps ∧
        (y < 0 → c.fn y = -sleLambda κ - θ₂ * QuantumZipper.chiC κ) ∧
        (0 < y → c.fn y = sleLambda κ - θ₂ * QuantumZipper.chiC κ)) ∧
      (∀ y : ℝ, y ≠ W → |y - W| < δ → y ∉ c.jumps ∧
        (c.fn y = -sleLambda κ - θ₁ * QuantumZipper.chiC κ ∨
          c.fn y = sleLambda κ - θ₁ * QuantumZipper.chiC κ)) := by
  set K₁ := α '' Icc 0 a with hK₁
  set K₂ := β '' Icc 0 b with hK₂
  have hK₁c : IsClosed K₁ := (isCompact_Icc.image_of_continuousOn hc₁).isClosed
  have hK₂c : IsClosed K₂ := (isCompact_Icc.image_of_continuousOn hc₂).isClosed
  have hK₁ne : K₁.Nonempty := ⟨α 0, 0, left_mem_Icc.2 zero_le, rfl⟩
  have hK₂ne : K₂.Nonempty := ⟨β 0, 0, left_mem_Icc.2 zero_le, rfl⟩
  have hreg₂ := isChartRegularPoint_tip₂ hc₁ hc₂ h0₁ h0₂ hp hne
  have hreg₁ := isChartRegularPoint_tip₁ hc₁ hc₂ h0₁ h0₂ hq hi
  have h0H : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
  have hWH : (W : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (W : ℂ).im by simp
  have hrealH : ∀ y : ℝ, (y : ℂ) ∈ Hbar := fun y => show (0 : ℝ) ≤ (y : ℂ).im by simp
  have hψ0 : ψ 0 = β b := hC.inv_zero h0₂
  -- the radii around the two tips
  set ρ₂ := min (β b).im (infDist (β b) K₁) with hρ₂
  set ρ₁ := min (α a).im (infDist (α a) K₂) with hρ₁
  have hρ₂pos : 0 < ρ₂ := lt_min hpH ((hK₁c.notMem_iff_infDist_pos hK₁ne).1 hp)
  have hρ₁pos : 0 < ρ₁ := lt_min hqH ((hK₂c.notMem_iff_infDist_pos hK₂ne).1 hq)
  obtain ⟨δ₂, hδ₂, hc0⟩ := Metric.continuousWithinAt_iff.1 (hC.continuousOn_inv 0 h0H) ρ₂ hρ₂pos
  obtain ⟨δ₁, hδ₁, hcW⟩ := Metric.continuousWithinAt_iff.1 (hC.continuousOn_inv (W : ℂ) hWH) ρ₁ hρ₁pos
  -- a point within `ρ` of an interior tip off a closed set is interior and off that set
  have hnear : ∀ {p z : ℂ} {K : Set ℂ}, dist z p < min p.im (infDist p K) → z ∈ H ∧ z ∉ K := by
    intro p z K hd
    refine ⟨?_, fun hzK => ?_⟩
    · have h1 : |z.im - p.im| ≤ dist z p := by
        rw [Complex.dist_eq]; exact (abs_im_le_norm (z - p)).trans_eq' (by simp)
      have h2 := lt_of_le_of_lt h1 (lt_of_lt_of_le hd (min_le_left _ _))
      show 0 < z.im
      rw [abs_lt] at h2; linarith
    · have h1 : infDist p K ≤ dist p z := infDist_le_dist_of_mem hzK
      rw [dist_comm] at h1
      exact absurd (lt_of_lt_of_le hd (min_le_right _ _)) (not_lt.2 h1)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy0 hy => ?_, fun y hyW hy => ?_⟩
  · have hd : dist (ψ y) (β b) < ρ₂ := by
      rw [← hψ0]
      refine hc0 (hrealH y) ?_
      rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact lt_of_lt_of_le hy (min_le_right _ _)
    obtain ⟨hyH, hyK₁⟩ := hnear hd
    have hyK : ψ y ∈ prefixSet α a β b := inv_mem_prefixSet_of_real hC h0₂ hc₁ hc₂ hyH
    have hyK₂ : ψ y ∈ K₂ := hyK.resolve_left hyK₁
    have hyp : ψ y ≠ β b := fun he => hy0 (by
      have := eq_of_inv_eq_of_regular hC h0₂ hreg₂ h0H hψ0 (hrealH y) he
      exact_mod_cast this)
    have hyq : ψ y ≠ α a := fun he => hyK₁ (he ▸ ⟨a, right_mem_Icc.2 zero_le, rfl⟩)
    obtain ⟨-, hyJ, hβ, -⟩ := hw y hyH hyp hyq fun h => hyK₁ h.1
    exact ⟨hyJ, (hβ hyK₂).1, (hβ hyK₂).2⟩
  · have hd : dist (ψ y) (α a) < ρ₁ := by
      rw [← hW]
      refine hcW (hrealH y) ?_
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact lt_of_lt_of_le hy (min_le_left _ _)
    obtain ⟨hyH, hyK₂⟩ := hnear hd
    have hyK : ψ y ∈ prefixSet α a β b := inv_mem_prefixSet_of_real hC h0₂ hc₁ hc₂ hyH
    have hyK₁ : ψ y ∈ K₁ := hyK.resolve_right hyK₂
    have hyq : ψ y ≠ α a := fun he => hyW (by
      have := eq_of_inv_eq_of_regular hC h0₂ hreg₁ hWH hW (hrealH y) he
      exact_mod_cast this)
    have hyp : ψ y ≠ β b := fun he => hyK₂ (he ▸ ⟨b, right_mem_Icc.2 zero_le, rfl⟩)
    obtain ⟨-, hyJ, -, hα⟩ := hw y hyH hyp hyq fun h => hyK₂ h.2
    exact ⟨hyJ, (hα hyK₁).2⟩

/-! ### The wrong side at the first tip has zero lifetime -/

/-- **Data whose first-seed germ has the wrong side** at a rational certificate: the height just left of `w` is
`λ − θ₁χ` (on `[q, w)`, no jump position there), or the height just right of `w` is `−λ − θ₁χ` (on `(w, q]`). -/
def BadSeed (κ θ₁ : ℝ) : Set (BoundaryWord × ℝ) :=
  ⋃ q : ℚ, ({c | (q : ℝ) < c.2 ∧ (∀ i < c.1.1, c.1.2.1 i < q ∨ c.2 ≤ c.1.2.1 i) ∧
      c.1.fn q = sleLambda κ - θ₁ * QuantumZipper.chiC κ} ∪
    {c | c.2 < q ∧ (∀ i < c.1.1, c.1.2.1 i ≤ c.2 ∨ (q : ℝ) < c.1.2.1 i) ∧
      c.1.fn q = -sleLambda κ - θ₁ * QuantumZipper.chiC κ})

/-- A finite-index condition on the jump positions of a word is measurable. -/
theorem measurableSet_forall_pos {P : ℝ → ℝ → Prop} (hP : MeasurableSet {x : ℝ × ℝ | P x.1 x.2}) :
    MeasurableSet {c : BoundaryWord × ℝ | ∀ i < c.1.1, P (c.1.2.1 i) c.2} := by
  have hp : ∀ i : ℕ, Measurable fun c : BoundaryWord × ℝ => c.1.2.1 i :=
    fun i => (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have hn : Measurable fun c : BoundaryWord × ℝ => c.1.1 := measurable_fst.comp measurable_fst
  have : {c : BoundaryWord × ℝ | ∀ i < c.1.1, P (c.1.2.1 i) c.2} =
      ⋂ i : ℕ, ({c : BoundaryWord × ℝ | c.1.1 ≤ i} ∪ (fun c : BoundaryWord × ℝ => (c.1.2.1 i, c.2)) ⁻¹'
        {x : ℝ × ℝ | P x.1 x.2}) := by
    ext c
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_preimage]
    refine ⟨fun h i => ?_, fun h i hi => ?_⟩
    · by_cases hi : i < c.1.1
      · exact Or.inr (h i hi)
      · exact Or.inl (not_lt.1 hi)
    · rcases h i with h' | h'
      · exact absurd hi (not_lt.2 h')
      · exact h'
  rw [this]
  exact MeasurableSet.iInter fun i => (hn (measurableSet_Iic (a := i))).union
    (((hp i).prodMk measurable_snd) hP)

theorem measurableSet_badSeed (κ θ₁ : ℝ) : MeasurableSet (BadSeed κ θ₁) := by
  have hfn : ∀ y : ℝ, Measurable fun c : BoundaryWord × ℝ => c.1.fn y :=
    fun y => (Supp7.measurable_boundaryWord_fn y).comp measurable_fst
  refine MeasurableSet.iUnion fun q => MeasurableSet.union ?_ ?_
  · have e : {c : BoundaryWord × ℝ | (q : ℝ) < c.2 ∧ (∀ i < c.1.1, c.1.2.1 i < q ∨ c.2 ≤ c.1.2.1 i) ∧
        c.1.fn q = sleLambda κ - θ₁ * QuantumZipper.chiC κ} =
        {c : BoundaryWord × ℝ | (q : ℝ) < c.2} ∩ ({c : BoundaryWord × ℝ | ∀ i < c.1.1, c.1.2.1 i < q ∨
          c.2 ≤ c.1.2.1 i} ∩ {c | c.1.fn q = sleLambda κ - θ₁ * QuantumZipper.chiC κ}) := rfl
    rw [e]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      ((measurableSet_forall_pos (P := fun x y => x < (q : ℝ) ∨ y ≤ x)
        ((measurableSet_lt measurable_fst measurable_const).union
        (measurableSet_le measurable_snd measurable_fst))).inter (measurableSet_eq_fun (hfn _) measurable_const))
  · have e : {c : BoundaryWord × ℝ | c.2 < q ∧ (∀ i < c.1.1, c.1.2.1 i ≤ c.2 ∨ (q : ℝ) < c.1.2.1 i) ∧
        c.1.fn q = -sleLambda κ - θ₁ * QuantumZipper.chiC κ} =
        {c : BoundaryWord × ℝ | c.2 < q} ∩ ({c : BoundaryWord × ℝ | ∀ i < c.1.1, c.1.2.1 i ≤ c.2 ∨
          (q : ℝ) < c.1.2.1 i} ∩ {c | c.1.fn q = -sleLambda κ - θ₁ * QuantumZipper.chiC κ}) := rfl
    rw [e]
    exact (measurableSet_lt measurable_snd measurable_const).inter
      ((measurableSet_forall_pos (P := fun x y => x ≤ y ∨ (q : ℝ) < x)
        ((measurableSet_le measurable_fst measurable_snd).union
        (measurableSet_lt measurable_const measurable_fst))).inter (measurableSet_eq_fun (hfn _) measurable_const))

/-- **A flow line from a wrong-sided first seed has zero lifetime** (W0a: "positive initial lifetime requires both
seed groups to exceed `−2`"; the wrong side gives seed weight exactly `−2`). -/
theorem ae_eq_zero_of_mem_badSeed {κ θ₁ : ℝ} (hκ : 0 < κ) {c : BoundaryWord × ℝ} (hc : c ∈ BadSeed κ θ₁)
    {S : Type*} [MeasurableSpace S] {Q : Measure S} {H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens}
    {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞} (h : IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ Q H₀ Γ U) :
    ∀ᵐ x ∂Q, U x = 0 := by
  have hlam := Sec4.sleLambda_pos hκ
  filter_upwards [Supp9.ae_seedWeights_of_isFlowLine h] with x hx
  by_contra hne
  obtain ⟨hL, hR⟩ := hx (pos_iff_ne_zero.2 hne)
  obtain ⟨q, ⟨hqw, hpos, hfn⟩ | ⟨hwq, hpos, hfn⟩⟩ := mem_iUnion.1 hc
  · have hlim : PiecewiseConstantBoundaryData.leftLim c.1.fn c.2 = sleLambda κ - θ₁ * QuantumZipper.chiC κ := by
      refine Sec4.leftLim_eq_of_forall hqw fun t ht => ?_
      rw [← hfn]
      refine (fn_eq_of_noPos ht.1.le fun i hi => ?_).symm
      rcases hpos i hi with h' | h'
      · exact Or.inl h'
      · exact Or.inr (ht.2.le.trans h')
    rw [hlim] at hL
    unfold Sec4.cumWeightLeft at hL
    have : -(sleLambda κ - θ₁ * QuantumZipper.chiC κ + θ₁ * QuantumZipper.chiC κ) / sleLambda κ - 1 = -2 := by
      field_simp; ring
    linarith
  · have hlim : PiecewiseConstantBoundaryData.rightLim c.1.fn c.2 =
        -sleLambda κ - θ₁ * QuantumZipper.chiC κ := by
      refine Sec4.rightLim_eq_of_forall hwq fun t ht => ?_
      rw [← hfn]
      refine fn_eq_of_noPos ht.2.le fun i hi => ?_
      rcases hpos i hi with h' | h'
      · exact Or.inl (lt_of_le_of_lt h' ht.1)
      · exact Or.inr h'.le
    rw [hlim] at hR
    unfold Sec4.cumWeightRight at hR
    have : (-sleLambda κ - θ₁ * QuantumZipper.chiC κ + θ₁ * QuantumZipper.chiC κ) / sleLambda κ - 1 = -2 := by
      field_simp; ring
    linarith

/-! ### The seed germs of the datum -/

/-- **The canonical seed germs from the word near the seeds and the right sides at the first tip.** -/
theorem mem_hasSeedGerms_of_wordGerm {κ θ₁ θ₂ : ℝ} {c : BoundaryWord} {W δ : ℝ} (hW : 0 < W) (hδ : 0 < δ)
    (h0 : ∀ y : ℝ, y ≠ 0 → |y| < δ → y ∉ c.jumps ∧
      (y < 0 → c.fn y = -sleLambda κ - θ₂ * QuantumZipper.chiC κ) ∧
      (0 < y → c.fn y = sleLambda κ - θ₂ * QuantumZipper.chiC κ))
    (hWg : ∀ y : ℝ, y ≠ W → |y - W| < δ → y ∉ c.jumps ∧
      (c.fn y = -sleLambda κ - θ₁ * QuantumZipper.chiC κ ∨ c.fn y = sleLambda κ - θ₁ * QuantumZipper.chiC κ))
    (hbad : (c, W) ∉ BadSeed κ θ₁) : (c, W) ∈ HasSeedGerms κ θ₁ θ₂ := by
  set δ' := min δ (W / 2) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ (by linarith)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'W : δ' ≤ W / 2 := min_le_right _ _
  obtain ⟨q, hq0, hqδ⟩ := exists_rat_btwn hδ'pos
  obtain ⟨q₁, hq₁l, hq₁r⟩ := exists_rat_btwn (show W - δ' < W by linarith)
  obtain ⟨q₂, hq₂l, hq₂r⟩ := exists_rat_btwn (show W < W + δ' by linarith)
  have hnotJ : ∀ i < c.1, c.2.1 i ∈ c.jumps := fun i hi => BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩
  have hpos : ∀ i < c.1, c.2.1 i < -(q : ℝ) ∨ c.2.1 i = 0 ∨ ((q : ℝ) < c.2.1 i ∧ c.2.1 i < q₁) ∨
      c.2.1 i = W ∨ (q₂ : ℝ) < c.2.1 i := by
    intro i hi
    set x := c.2.1 i with hx
    have hxJ := hnotJ i hi
    by_cases h1 : x < -(q : ℝ)
    · exact Or.inl h1
    by_cases h2 : x = 0
    · exact Or.inr (Or.inl h2)
    by_cases h3 : x ≤ q
    · exfalso
      exact (h0 x h2 (by rw [abs_lt]; constructor <;> linarith)).1 hxJ
    by_cases h4 : x < q₁
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith, h4⟩))
    by_cases h5 : x = W
    · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))
    by_cases h6 : x ≤ q₂
    · exfalso
      exact (hWg x h5 (by rw [abs_lt]; constructor <;> linarith)).1 hxJ
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))
  have e1 := (h0 (-(q : ℝ)) (by linarith) (by rw [abs_lt]; constructor <;> linarith)).2.1 (by linarith)
  have e2 := (h0 (q : ℝ) (by linarith) (by rw [abs_lt]; constructor <;> linarith)).2.2 (by linarith)
  have e3 : c.fn q₁ = -sleLambda κ - θ₁ * QuantumZipper.chiC κ := by
    rcases (hWg (q₁ : ℝ) (by linarith) (by rw [abs_lt]; constructor <;> linarith)).2 with h | h
    · exact h
    · refine absurd (mem_iUnion.2 ⟨q₁, Or.inl ⟨hq₁r, fun i hi => ?_, h⟩⟩) hbad
      rcases hpos i hi with h' | h' | h' | h' | h'
      · exact Or.inl (by linarith)
      · exact Or.inl (by rw [h']; linarith)
      · exact Or.inl h'.2
      · exact Or.inr h'.ge
      · exact Or.inr (by linarith)
  have e4 : c.fn q₂ = sleLambda κ - θ₁ * QuantumZipper.chiC κ := by
    rcases (hWg (q₂ : ℝ) (by linarith) (by rw [abs_lt]; constructor <;> linarith)).2 with h | h
    · refine absurd (mem_iUnion.2 ⟨q₂, Or.inr ⟨hq₂l, fun i hi => ?_, h⟩⟩) hbad
      rcases hpos i hi with h' | h' | h' | h' | h'
      · exact Or.inl (by linarith)
      · exact Or.inl (by rw [h']; linarith)
      · exact Or.inl (by linarith [h'.2])
      · exact Or.inl h'.le
      · exact Or.inr h'
    · exact h
  refine ⟨q, q₁, q₂, ?_, by linarith, hq₁r, hq₂l, hpos, ?_, ?_, e3, e4⟩
  · exact_mod_cast hq0
  · simpa using e1
  · exact e2

end RLC

end InteractingSLE
