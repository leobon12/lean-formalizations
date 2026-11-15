/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinConfig
import InteractingSLE.Spec.Supplement.SBTail2Induction

/-!
# SB2(2)'s later relative stages by the bridge (ruling R120): the retained path through `0` with head time `0`

Packet PROVE-GW2-GEOM2 (SB2(2), D5 F1 / D11 (G2); ruling R120). At a later relative stage, in B's stage-`ℓ`
coordinates (reflected so that the retained set lies to the right), the explored piece `β'` starts at the chart's `0`,
off the retained set. R120: take the retained path

  `p` = the real segment from `0` to `x₁ = q 0`, followed by the lifted upper prefix `q`

(**`bridgePath x₁ q`**). Adjoining a real segment changes no filling (**`fillH_image_bridgePath`**), so every object of
SB2(1)'s constructor that reads the retained set through `fillH` is unchanged; the piece now starts on the retained
path, and since `β'` is injective its head time is `0` (**`headTime_eq_zero`**).

* `bridgePath`, `continuousOn_bridgePath`, `bridgePath_zero`, `im_bridgePath_nonneg`, **`image_bridgePath`** (the
  image is `q([0, 1]) ∪ [0, x₁]`), **`realMin_image_bridgePath`** (`= 0` when `q`'s real points are `≥ 0`),
  **`image_bridgePath_subset_closedRightSide`** (S1 for the bridge from S1 for `q`);
* `isLeftEntryChart_congr_fillH`, `isSB2RelChain_congr_fillH` (only the filling enters);
* `interior_union_real_eq_empty` (no open time interval on `K ∪ T`, `T ⊆ ℝ`, from none on `K` and none on `ℝ`);
* **`exists_isSB2RelChain_bridgePath`**: FIN's chain builder `FinRel.exists_relConfig` for the bridged set at head
  time `0`, for a given lift `γ` (`g ∘ γ = β'`), transported to any retained set `R` with the same filling;
* **`exists_lift_isSB2RelChain_bridgePath`**: FIN's `exists_relConfig_of_path` for the bridge path — the S2 lift
  `γ` of `β'` from time `0` and its relative chain.

No hypothesis of SB2(1)'s path constructor fails for the bridge path: `hp`, `hp0`, `hpH` hold by construction,
`htL` with `tL = 0` holds because `realMin = 0`, the left entry chart and the chain read the set only through
`fillH`, and S1 for the segment holds for every proper curve from `0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)
open InteractingSLE.Supp9B (IsProperCurve closedRightSide)

namespace InteractingSLE.Theorem14.SB.Bq

open Sec7.Lemma71C FinRel

/-! ### The bridge path -/

/-- **R120's retained path**: the real segment from `0` to `x₁` on `[0, 1/2]`, then `q` on `[1/2, 1]` (for
`q 0 = x₁`). -/
def bridgePath (x₁ : ℝ) (q : ℝ → ℂ) (s : ℝ) : ℂ :=
  ((min (2 * s) 1 * x₁ : ℝ) : ℂ) + (q (max (2 * s - 1) 0) - x₁)

variable {x₁ : ℝ} {q : ℝ → ℂ}

theorem bridgePath_of_le (hq0 : q 0 = x₁) {s : ℝ} (hs : s ≤ 1 / 2) :
    bridgePath x₁ q s = ((2 * s * x₁ : ℝ) : ℂ) := by
  have h1 : min (2 * s) 1 = 2 * s := min_eq_left (by linarith)
  have h2 : max (2 * s - 1) 0 = 0 := max_eq_right (by linarith)
  simp only [bridgePath, h1, h2, hq0, sub_self, add_zero]

theorem bridgePath_of_ge {s : ℝ} (hs : 1 / 2 ≤ s) : bridgePath x₁ q s = q (2 * s - 1) := by
  have h1 : min (2 * s) 1 = 1 := min_eq_right (by linarith)
  have h2 : max (2 * s - 1) 0 = 2 * s - 1 := max_eq_left (by linarith)
  simp only [bridgePath, h1, h2, one_mul]
  ring

theorem bridgePath_zero (hq0 : q 0 = x₁) : bridgePath x₁ q 0 = 0 := by
  rw [bridgePath_of_le hq0 (by norm_num)]
  simp

theorem continuousOn_bridgePath (hq : ContinuousOn q (Icc 0 1)) : ContinuousOn (bridgePath x₁ q) (Icc 0 1) := by
  have hm : ContinuousOn (fun s : ℝ => max (2 * s - 1) 0) (Icc 0 1) :=
    (((continuous_const.mul continuous_id).sub continuous_const).max continuous_const).continuousOn
  have hmaps : MapsTo (fun s : ℝ => max (2 * s - 1) 0) (Icc 0 1) (Icc 0 1) := fun s hs =>
    ⟨le_max_right _ _, max_le (by linarith [hs.2]) zero_le_one⟩
  have hqm := hq.comp hm hmaps
  have hseg : Continuous fun s : ℝ => ((min (2 * s) 1 * x₁ : ℝ) : ℂ) :=
    continuous_ofReal.comp (((continuous_const.mul continuous_id).min continuous_const).mul continuous_const)
  exact hseg.continuousOn.add (hqm.sub continuousOn_const)

theorem im_bridgePath_nonneg (hq0 : q 0 = x₁) (hqH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (q s).im) :
    ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (bridgePath x₁ q s).im := by
  intro s hs
  rcases le_total s (1 / 2) with h | h
  · rw [bridgePath_of_le hq0 h]; simp
  · rw [bridgePath_of_ge h]; exact hqH _ ⟨by linarith, by linarith [hs.2]⟩

/-- **The image of the bridge path**: the lifted prefix and the real segment `[0, x₁]`. -/
theorem image_bridgePath (hx₁ : 0 ≤ x₁) (hq0 : q 0 = x₁) :
    bridgePath x₁ q '' Icc 0 1 = q '' Icc 0 1 ∪ (fun x : ℝ => (x : ℂ)) '' Icc 0 x₁ := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    rcases le_total s (1 / 2) with h | h
    · right
      refine ⟨2 * s * x₁, ⟨mul_nonneg (mul_nonneg zero_le_two hs.1) hx₁, ?_⟩, (bridgePath_of_le hq0 h).symm⟩
      nlinarith
    · left
      exact ⟨2 * s - 1, ⟨by linarith, by linarith [hs.2]⟩, (bridgePath_of_ge h).symm⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨x, hx, rfl⟩)
    · refine ⟨(t + 1) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      rw [bridgePath_of_ge (by linarith [ht.1])]
      congr 1
      ring
    · rcases eq_or_lt_of_le hx₁ with h0 | hpos
      · have hx0 : x = 0 := le_antisymm (h0 ▸ hx.2) hx.1
        refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
        rw [bridgePath_zero hq0, hx0]
        simp
      · have h2 : (0 : ℝ) < 2 * x₁ := by linarith
        have hle : x / (2 * x₁) ≤ 1 / 2 := by
          rw [div_le_iff₀ h2]
          linarith [hx.2]
        refine ⟨x / (2 * x₁), ⟨div_nonneg hx.1 h2.le, hle.trans (by norm_num)⟩, ?_⟩
        rw [bridgePath_of_le hq0 hle]
        congr 1
        field_simp

/-- **The bridge changes no filling.** -/
theorem fillH_image_bridgePath (hx₁ : 0 ≤ x₁) (hq0 : q 0 = x₁) :
    fillH (bridgePath x₁ q '' Icc 0 1) = fillH (q '' Icc 0 1) := by
  rw [image_bridgePath hx₁ hq0]
  exact fillH_union_of_im_eq_zero fun _ ⟨_, _, hx⟩ => hx ▸ ofReal_im _

/-- The real points of a bounded set are bounded below and above. -/
theorem bdd_real_of_isBounded {A : Set ℂ} (hA : IsBounded A) :
    BddBelow {x : ℝ | (x : ℂ) ∈ A} ∧ BddAbove {x : ℝ | (x : ℂ) ∈ A} := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hA
  refine ⟨⟨-C, fun x hx => ?_⟩, ⟨C, fun x hx => ?_⟩⟩
  · have := hC _ hx
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith [neg_abs_le x]
  · have := hC _ hx
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith [le_abs_self x]

/-- **The leftmost real point of the bridge is `0`** when the lifted prefix has no negative real points. -/
theorem realMin_image_bridgePath (hx₁ : 0 ≤ x₁) (hq0 : q 0 = x₁)
    (hqR : ∀ y : ℝ, (y : ℂ) ∈ q '' Icc 0 1 → 0 ≤ y) : realMin (bridgePath x₁ q '' Icc 0 1) = 0 := by
  have h0 : (0 : ℝ) ∈ {x : ℝ | (x : ℂ) ∈ bridgePath x₁ q '' Icc 0 1} :=
    ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [bridgePath_zero hq0]; simp⟩
  have hlow : ∀ y ∈ {x : ℝ | (x : ℂ) ∈ bridgePath x₁ q '' Icc 0 1}, 0 ≤ y := by
    intro y hy
    change (y : ℂ) ∈ bridgePath x₁ q '' Icc 0 1 at hy
    rw [image_bridgePath hx₁ hq0] at hy
    rcases hy with hy | ⟨x, hx, hxy⟩
    · exact hqR y hy
    · rw [← ofReal_injective hxy]
      exact hx.1
  exact le_antisymm (csInf_le ⟨0, hlow⟩ h0) (le_csInf ⟨0, h0⟩ hlow)

/-- **S1 for the bridge** from S1 for the lifted prefix: the segment `[0, x₁]` lies on the closed right side of every
proper curve from `0`. -/
theorem image_bridgePath_subset_closedRightSide (hx₁ : 0 ≤ x₁) (hq0 : q 0 = x₁) {β' : ℝ≥0 → ℂ}
    (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : q '' Icc 0 1 ⊆ closedRightSide β') :
    bridgePath x₁ q '' Icc 0 1 ⊆ closedRightSide β' := by
  rw [image_bridgePath hx₁ hq0]
  rintro z (hz | ⟨x, hx, rfl⟩)
  · exact hA hz
  · exact ofReal_mem_closedRightSide_of_seed_le hβ' (by rw [hβ'0]; simp) (by rw [hβ'0]; simpa using hx.1)

/-- **The head time is `0`**: an injective explored curve from `0` visits `0` only at time `0`. -/
theorem headTime_eq_zero {β' : ℝ≥0 → ℂ} (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) {tL : ℝ≥0}
    (htL : β' tL = 0) : tL = 0 :=
  hβ'.2.1 (htL.trans hβ'0.symm)

/-! ### Only the filling enters -/

theorem isLeftEntryChart_congr_fillH {A A' : Set ℂ} (h : fillH A = fillH A') {L : ℝ} {c : Chart} :
    IsLeftEntryChart A L c ↔ IsLeftEntryChart A' L c := by
  unfold IsLeftEntryChart
  rw [h]

theorem isSB2RelChain_congr_fillH {A A' : Set ℂ} (h : fillH A = fillH A') {c : Chart} {β' γ : ℝ≥0 → ℂ}
    {tL : ℝ≥0} {S₀ : ℝ} {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} :
    IsSB2RelChain A c β' γ tL S₀ Wr ηr ↔ IsSB2RelChain A' c β' γ tL S₀ Wr ηr := by
  unfold IsSB2RelChain
  rw [h]

/-! ### No open time interval on the bridge -/

/-- **No open time interval on `K ∪ T` (`T ⊆ ℝ`)** from none on `K` and none on `ℝ`, for a continuous curve. -/
theorem interior_union_real_eq_empty {f : ℝ → ℂ} (hf : Continuous f) {S : ℝ} {K T : Set ℂ}
    (hK : interior {r ∈ Ioo (0 : ℝ) S | f r ∈ K} = ∅)
    (hR : interior {r ∈ Ioo (0 : ℝ) S | f r ∈ {z : ℂ | z.im = 0}} = ∅) (hT : ∀ z ∈ T, z.im = 0) :
    interior {r ∈ Ioo (0 : ℝ) S | f r ∈ K ∪ T} = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro r hr
  have hU : IsOpen (interior {r ∈ Ioo (0 : ℝ) S | f r ∈ K ∪ T}) := isOpen_interior
  by_cases hex : ∃ x ∈ interior {r ∈ Ioo (0 : ℝ) S | f r ∈ K ∪ T}, (f x).im ≠ 0
  · obtain ⟨x, hxU, hx⟩ := hex
    have hV : IsOpen (interior {r ∈ Ioo (0 : ℝ) S | f r ∈ K ∪ T} ∩ {r | (f r).im ≠ 0}) :=
      hU.inter (isOpen_ne_fun (continuous_im.comp hf) continuous_const)
    have hsub : interior {r ∈ Ioo (0 : ℝ) S | f r ∈ K ∪ T} ∩ {r | (f r).im ≠ 0} ⊆
        {r ∈ Ioo (0 : ℝ) S | f r ∈ K} := by
      rintro y ⟨hyU, hy⟩
      obtain ⟨hy1, hy2⟩ := interior_subset hyU
      exact ⟨hy1, hy2.resolve_right fun hT' => hy (hT _ hT')⟩
    have hmem := hV.subset_interior_iff.2 hsub ⟨hxU, hx⟩
    rw [hK] at hmem
    exact hmem
  · simp only [not_exists, not_and, not_not] at hex
    have hsub : interior {r ∈ Ioo (0 : ℝ) S | f r ∈ K ∪ T} ⊆ {r ∈ Ioo (0 : ℝ) S | f r ∈ {z : ℂ | z.im = 0}} :=
      fun y hy => ⟨(interior_subset hy).1, hex y hy⟩
    have hmem := hU.subset_interior_iff.2 hsub hr
    rw [hR] at hmem
    exact hmem

/-- The no-common-arc input for the bridged set at head time `0`, from that for the lifted prefix and the no-real-arc
input. -/
theorem interior_bridge_eq_empty (hx₁ : 0 ≤ x₁) (hq0 : q 0 = x₁) (hq : ContinuousOn q (Icc 0 1)) {β' : ℝ≥0 → ℂ}
    (hβc : Continuous β') {S : ℝ}
    (hnA : interior {r ∈ Ioo (0 : ℝ) S | β' r.toNNReal ∈ q '' Icc 0 1} = ∅)
    (hnR : interior {r ∈ Ioo (0 : ℝ) S | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} = ∅) :
    interior {r ∈ Ioo (0 : ℝ) S | β' (0 + r.toNNReal) ∈ closure (bridgePath x₁ q '' Icc 0 1)} = ∅ := by
  have hpc : IsCompact (bridgePath x₁ q '' Icc 0 1) :=
    isCompact_Icc.image_of_continuousOn (continuousOn_bridgePath hq)
  simp only [zero_add]
  rw [hpc.isClosed.closure_eq, image_bridgePath hx₁ hq0]
  exact interior_union_real_eq_empty (hβc.comp continuous_real_toNNReal) hnA hnR
    fun _ ⟨_, _, hx⟩ => hx ▸ ofReal_im _

/-! ### FIN's chain builder for the bridge, head time `0` -/

variable {R : Set ℂ} {L : ℝ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ}

/-- **The relative chain at a later stage by the bridge, for a given lift** (`FinRel.exists_relConfig` for the
bridged set at head time `0`): a left entry chart of `ℍ ∖ fill R` (where `fill R = fill q([0, 1])`, `q` a continuous
path from the real point `x₁ ≥ 0`) with a continuous boundary extension `g` of its inverse, a proper explored curve
`β'` from `0`, a proper lift `γ` from `0` with `g ∘ γ = β'`, and no open time interval of `β'` on `q([0, 1])` or on
`ℝ` on `(0, S)`. -/
theorem exists_isSB2RelChain_bridgePath (hq : ContinuousOn q (Icc 0 1)) (hq0 : q 0 = x₁) (hx₁ : 0 ≤ x₁)
    (hR : fillH R = fillH (q '' Icc 0 1)) (hc : IsLeftEntryChart R L c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hlift : ∀ s, g (γ s) = β' s) {S S₀ : ℝ} (hS₀ : 0 ≤ S₀) (hS₀S : S₀ < S)
    (hnA : interior {r ∈ Ioo (0 : ℝ) S | β' r.toNNReal ∈ q '' Icc 0 1} = ∅)
    (hnR : interior {r ∈ Ioo (0 : ℝ) S | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} = ∅) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), IsSB2RelChain R c β' γ 0 S₀ Wr ηr := by
  have hpc : IsCompact (bridgePath x₁ q '' Icc 0 1) :=
    isCompact_Icc.image_of_continuousOn (continuousOn_bridgePath hq)
  have hfill : fillH (bridgePath x₁ q '' Icc 0 1) = fillH R := (fillH_image_bridgePath hx₁ hq0).trans hR.symm
  have h0 : (0 : ℂ) ∈ bridgePath x₁ q '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, bridgePath_zero hq0⟩
  have hAc : IsPreconnected (bridgePath x₁ q '' Icc 0 1 ∪ {z : ℂ | z.im ≤ 0}) :=
    (isPreconnected_Icc.image _ (continuousOn_bridgePath hq)).union 0 h0 (show (0 : ℂ).im ≤ 0 by simp)
      isPreconnected_lowerHalf
  have hpre : β' '' Icc 0 0 ⊆ hullK (bridgePath x₁ q '' Icc 0 1) := by
    rintro _ ⟨r, hr, rfl⟩
    have hr0 : r = 0 := le_antisymm hr.2 hr.1
    rw [hr0, hβ'0]
    right
    obtain ⟨hlo, hhi⟩ := bdd_real_of_isBounded hpc.isBounded
    have h0' : (0 : ℝ) ∈ {x : ℝ | (x : ℂ) ∈ bridgePath x₁ q '' Icc 0 1} := by simpa using h0
    exact ⟨0, ⟨csInf_le hlo h0', le_csSup hhi h0'⟩, by simp⟩
  have hc' : IsLeftEntryChart (bridgePath x₁ q '' Icc 0 1) L c := (isLeftEntryChart_congr_fillH hfill).2 hc
  obtain ⟨Wr, ηr, hch⟩ := exists_relConfig hpc.isBounded hAc hc' hgc hgi hβ' hpre hγ hγ0
    (fun s => by rw [zero_add]; exact hlift s) hS₀ hS₀S
    (interior_bridge_eq_empty hx₁ hq0 hq hβ'.1 hnA hnR) (by simpa only [zero_add] using hnR)
  exact ⟨Wr, ηr, (isSB2RelChain_congr_fillH hfill).1 hch⟩

/-- **The S2 lift from time `0` and its relative chain at a later stage, by the bridge** (`FinRel.
exists_relConfig_of_path` for `bridgePath x₁ q`): for the lifted prefix `q` (continuous on `[0, 1]`, in `ℍ̄`, from
the real point `x₁ ≥ 0`, with no negative real points) on the closed right side of the proper explored curve `β'`
from `0` (S1), a left entry chart of `ℍ ∖ fill R` at `0` (`fill R = fill q([0, 1])`) whose inverse has a continuous
finite-fibre extension `g`, and no open time interval of `β'` on `q([0, 1])` or on `ℝ` on `(0, S)`: the proper lift
`γ` of `β'` from time `0` exists, and for every `S₀ < S` its relative chain. -/
theorem exists_lift_isSB2RelChain_bridgePath (hq : ContinuousOn q (Icc 0 1)) (hq0 : q 0 = x₁) (hx₁ : 0 ≤ x₁)
    (hqH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (q s).im) (hqR : ∀ y : ℝ, (y : ℂ) ∈ q '' Icc 0 1 → 0 ≤ y)
    (hR : fillH R = fillH (q '' Icc 0 1)) (hc : IsLeftEntryChart R 0 c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite)
    (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : q '' Icc 0 1 ⊆ closedRightSide β')
    {S S₀ : ℝ} (hS₀ : 0 ≤ S₀) (hS₀S : S₀ < S)
    (hnA : interior {r ∈ Ioo (0 : ℝ) S | β' r.toNNReal ∈ q '' Icc 0 1} = ∅)
    (hnR : interior {r ∈ Ioo (0 : ℝ) S | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} = ∅) :
    ∃ γ : ℝ≥0 → ℂ, IsProperCurve γ ∧ γ 0 = 0 ∧ (∀ s, g (γ s) = β' s) ∧
      ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), IsSB2RelChain R c β' γ 0 S₀ Wr ηr := by
  have hfill : fillH (bridgePath x₁ q '' Icc 0 1) = fillH R := (fillH_image_bridgePath hx₁ hq0).trans hR.symm
  have hmin := realMin_image_bridgePath hx₁ hq0 hqR
  have hc' : IsLeftEntryChart (bridgePath x₁ q '' Icc 0 1) (realMin (bridgePath x₁ q '' Icc 0 1)) c := by
    rw [hmin]; exact (isLeftEntryChart_congr_fillH hfill).2 hc
  have hnA' : ∀ t : ℝ≥0, β' t = realMin (bridgePath x₁ q '' Icc 0 1) →
      interior {r ∈ Ioo (0 : ℝ) S | β' (t + r.toNNReal) ∈ closure (bridgePath x₁ q '' Icc 0 1)} = ∅ := by
    intro t ht
    rw [hmin] at ht
    rw [headTime_eq_zero hβ' hβ'0 ht]
    exact interior_bridge_eq_empty hx₁ hq0 hq hβ'.1 hnA hnR
  have hnR' : ∀ t : ℝ≥0, β' t = realMin (bridgePath x₁ q '' Icc 0 1) →
      interior {r ∈ Ioo (0 : ℝ) S | β' (t + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅ := by
    intro t ht
    rw [hmin] at ht
    rw [headTime_eq_zero hβ' hβ'0 ht]
    simpa only [zero_add] using hnR
  obtain ⟨tL, γ, htL, -, hγ, hγ0, hlift, Wr, ηr, hch⟩ := exists_relConfig_of_path (continuousOn_bridgePath hq)
    (bridgePath_zero hq0) (im_bridgePath_nonneg hq0 hqH) hβ' hβ'0
    (image_bridgePath_subset_closedRightSide hx₁ hq0 hβ' hβ'0 hA) hc' hgc hgi hgf hS₀ hS₀S hnA' hnR'
  rw [hmin] at htL
  have htL0 := headTime_eq_zero hβ' hβ'0 htL
  subst htL0
  exact ⟨γ, hγ, hγ0, fun s => by rw [hlift, zero_add], Wr, ηr, (isSB2RelChain_congr_fillH hfill).1 hch⟩

end InteractingSLE.Theorem14.SB.Bq
