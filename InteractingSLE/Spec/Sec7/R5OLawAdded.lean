/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutEnlarged
import InteractingSLE.Spec.Sec7.R5EnlAdded

/-!
# The added set of a component reference chart is hitting-measurable

Packet PROVE-R5-OUTERLAW (ruling R88). `R5Enl.measurable_globalOldChartAddedSet_oldOn` (`hAdded`) reads the reference
chart's domain off the reference set `B` (`dom = ℍ ∖ B`). For an outer pocket the reference chart uniformizes only the
component of `ℍ ∖ B` incident to the pocket target. Here `dom ⊆ ℍ ∖ B`, the rest `(ℍ ∖ B) ∖ dom` is open, and the
domain events of the chart are events of the reference record (`hdom`); a ball inside `ℍ ∖ B` whose centre is in the
domain lies in the domain (connectedness of the ball), which replaces the identity `dom = ℍ ∖ B` in the countable
description of the hitting events.

* **`measurable_globalOldChartAddedSet_oldOn_comp`** — `hAdded` for a component reference chart;
* **`hasOldChartIncrementLawOn_of_enlarged_component_fwd`** — PROVE-R5-OUTER's
  `R5Out.hasOldChartIncrementLawOn_of_enlarged_component_marked` with `hAdded` discharged.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.R5OLaw

open LocalSets WholeField PocketStopSide R5Enl

section Added

variable {Ω : Type*} {ℋ₀ ℋ₁ : MeasurableSpace Ω}

/-- **`hAdded` for a component reference chart**: the increment of the extended charts is hitting-measurable for
`ℋ₁`, from the reference chart's domain events and forward map (`ℋ₀ ≤ ℋ₁`), the hitting measurability of the
reference set `B` (`ℋ₀`) and of `K'` (`ℋ₁`), with `dom ⊆ ℍ ∖ B` and `(ℍ ∖ B) ∖ dom` open on `G`. -/
theorem measurable_globalOldChartAddedSet_oldOn_comp (hInfo : ℋ₀ ≤ ℋ₁) {G : Set Ω} (hG : MeasurableSet[ℋ₀] G)
    {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    {B K' : Ω → Set ℂ} (hB : Measurable[ℋ₀, hittingSigma] B)
    (hOldSub : ∀ ω ∈ G, ((old ω).dom : Set ℂ) ⊆ H \ B ω) (hCut : ∀ ω ∈ G, IsOpen ((H \ B ω) \ (old ω).dom))
    (hK' : Measurable[ℋ₁, hittingSigma] K') (hK'o : ∀ ω ∈ G, IsOpen (H \ K' ω)) :
    Measurable[ℋ₁, hittingSigma] (globalOldChartAddedSet (oldOn G old) (curOn G fun ω => H \ K' ω)) := by
  refine @measurable_generateFrom Ω (Set ℂ) ℋ₁ _ _ ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  set x : ℕ → ℂ := TopologicalSpace.denseSeq ℂ with hxdef
  have hxd : DenseRange x := TopologicalSpace.denseRange_denseSeq ℂ
  set F : ℂ → Ω → ℂ := fun z => (G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z with hFdef
  have hUc : (Uᶜ).Nonempty := ⟨-Complex.I, fun h => neg_I_notMem_H (hUH h)⟩
  -- the countable description
  let E : ℕ × ℚ × ℚ → Set Ω := fun p =>
    ({ω | Disjoint (B ω) (ball (x p.1) p.2.1)} ∩ (G ∩ {ω | x p.1 ∈ (old ω).dom})) ∩
      (⋂ j, ⋂ (_ : x j ∈ ball (x p.1) (p.2.1 : ℝ)), {ω | ((p.2.2 : ℚ) : ℝ) ≤ infDist (F (x j) ω) Uᶜ}) ∩
      {ω | (K' ω ∩ ball (x p.1) p.2.1).Nonempty}
  have e : globalOldChartAddedSet (oldOn G old) (curOn G fun ω => H \ K' ω) ⁻¹'
      {S : Set ℂ | (S ∩ U).Nonempty} =
      G ∩ ⋃ p : ℕ × ℚ × ℚ, ⋃ (_ : (0 : ℝ) < p.2.2 ∧ ball (x p.1) (p.2.1 : ℝ) ⊆ H), E p := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff, mem_iUnion, exists_prop]
    constructor
    · intro hne
      by_cases hω : ω ∈ G
      · refine ⟨hω, ?_⟩
        have hc := hOld ω hω
        rw [globalOldChartAddedSet_oldOn_of_mem hω hc (hK'o ω hω)] at hne
        obtain ⟨w, ⟨hw, hwK⟩, hwU⟩ := hne
        set y := (old ω).2.1 w with hy
        have hydom : y ∈ (old ω).dom := hc.inv_mem_dom hw
        have hfy : (old ω).1 y = w := hc.2.2 w hw
        obtain ⟨e₀, he₀, hballU⟩ := Metric.isOpen_iff.1 hUo w hwU
        have hcont : ContinuousAt (old ω).1 y :=
          ((hc.differentiableOn_fwd y hydom).differentiableAt
            ((old ω).dom.isOpen.mem_nhds hydom)).continuousAt
        obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcont (e₀ / 2) (by positivity)
        obtain ⟨δ', hδ', hδ'd⟩ := Metric.isOpen_iff.1 (old ω).dom.isOpen y hydom
        set δ₁ := min δ δ' with hδ₁
        have hδ₁p : 0 < δ₁ := lt_min hδ hδ'
        obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 hxd y (δ₁ / 4) (by positivity)
        obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show dist (x k) y < δ₁ / 2 by
          rw [dist_comm]; linarith)
        obtain ⟨ε, hε1, hε2⟩ := exists_rat_btwn (show (0 : ℝ) < e₀ / 2 by positivity)
        have hball : ball (x k) (r : ℝ) ⊆ ball y δ₁ := by
          intro z hz
          rw [mem_ball] at hz ⊢
          have := dist_triangle z (x k) y
          linarith
        have hballdom : ball (x k) (r : ℝ) ⊆ (old ω).dom := fun z hz =>
          hδ'd (ball_subset_ball (min_le_right δ δ') (hball hz))
        have hballH : ball (x k) (r : ℝ) ⊆ H := hballdom.trans hc.dom_subset
        have hr0 : (0 : ℝ) < r := lt_of_le_of_lt dist_nonneg hr1
        refine ⟨(k, r, ε), ⟨hε1, hballH⟩, ⟨⟨⟨?_, hω, hballdom (mem_ball_self hr0)⟩, ?_⟩, ?_⟩⟩
        · show Disjoint (B ω) (ball (x k) (r : ℝ))
          exact Set.disjoint_left.2 fun z hzB hz => (hOldSub ω hω (hballdom hz)).2 hzB
        · simp only [mem_iInter, mem_ofPred_eq]
          intro j hj
          have hjdom : x j ∈ (old ω).dom := hballdom hj
          have hFj : F (x j) ω = (old ω).1 (x j) := by
            simp only [hFdef]
            exact indicator_of_mem (show ω ∈ G ∩ {ω | x j ∈ (old ω).dom} from ⟨hω, hjdom⟩) _
          rw [hFj]
          have hdj : dist ((old ω).1 (x j)) w < e₀ / 2 := by
            rw [← hfy]
            exact hδc (lt_of_lt_of_le (mem_ball.1 (hball hj)) (min_le_left δ δ'))
          refine (Metric.le_infDist hUc).2 fun u hu => ?_
          have hu' : e₀ ≤ dist u w := by
            by_contra hlt
            exact hu (hballU (mem_ball.2 (not_le.1 hlt)))
          have h1 := dist_triangle u ((old ω).1 (x j)) w
          have h2 : dist u ((old ω).1 (x j)) = dist ((old ω).1 (x j)) u := dist_comm _ _
          linarith
        · exact ⟨y, hwK, by rw [mem_ball, dist_comm]; exact hr1⟩
      · rw [globalOldChartAddedSet_oldOn_of_notMem hω] at hne
        simp only [empty_inter, Set.not_nonempty_empty] at hne
    · rintro ⟨hω, p, ⟨hε, hballH⟩, ⟨⟨hdisj, -, hcen⟩, hgood⟩, hK⟩
      have hc := hOld ω hω
      rw [globalOldChartAddedSet_oldOn_of_mem hω hc (hK'o ω hω)]
      have hballdom : ball (x p.1) (p.2.1 : ℝ) ⊆ (old ω).dom := by
        have hsub : ball (x p.1) (p.2.1 : ℝ) ⊆ ((old ω).dom : Set ℂ) ∪ ((H \ B ω) \ (old ω).dom) := by
          intro z hz
          by_cases hzd : z ∈ (old ω).dom
          · exact Or.inl hzd
          · exact Or.inr ⟨⟨hballH hz, fun hzB => Set.disjoint_left.1 hdisj hzB hz⟩, hzd⟩
        have hr0 : (0 : ℝ) < p.2.1 := pos_of_mem_ball hK.some_mem.2
        exact (isPreconnected_ball (x := x p.1) (r := (p.2.1 : ℝ))).subset_left_of_subset_union
          (old ω).dom.isOpen (hCut ω hω) disjoint_sdiff_right hsub ⟨x p.1, mem_ball_self hr0, hcen⟩
      obtain ⟨y, hyK, hyb⟩ := hK
      have hydom : y ∈ (old ω).dom := hballdom hyb
      have hcont : ContinuousAt (fun z => infDist ((old ω).1 z) Uᶜ) y :=
        (continuous_infDist_pt _).continuousAt.comp
          ((hc.differentiableOn_fwd y hydom).differentiableAt
            ((old ω).dom.isOpen.mem_nhds hydom)).continuousAt
      have hcl : y ∈ closure (ball (x p.1) (p.2.1 : ℝ) ∩ range x) :=
        hxd.open_subset_closure_inter isOpen_ball hyb
      obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
      have hge : ((p.2.2 : ℚ) : ℝ) ≤ infDist ((old ω).1 y) Uᶜ := by
        refine ge_of_tendsto' (hcont.tendsto.comp hlim) fun n => ?_
        obtain ⟨hub, j, hj⟩ := hu n
        have h1 : ((p.2.2 : ℚ) : ℝ) ≤ infDist (F (x j) ω) Uᶜ := by
          simp only [mem_iInter, mem_ofPred_eq] at hgood
          exact hgood j (by rw [hj]; exact hub)
        have hFj : F (x j) ω = (old ω).1 (x j) := by
          simp only [hFdef]
          exact indicator_of_mem (show ω ∈ G ∩ {ω | x j ∈ (old ω).dom} from
            ⟨hω, hballdom (by rw [hj]; exact hub)⟩) _
        rw [hFj, hj] at h1
        exact h1
      refine ⟨(old ω).1 y, ⟨hc.fwd_mem hydom, by rw [hc.inv_fwd hydom]; exact hyK⟩, ?_⟩
      by_contra hnot
      have h0 : infDist ((old ω).1 y) Uᶜ = 0 := infDist_zero_of_mem hnot
      have : (0 : ℝ) < ((p.2.2 : ℚ) : ℝ) := hε
      linarith
  rw [e]
  refine (hInfo _ hG).inter (MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun hp => ?_)
  refine (((hInfo _ (hB (measurableSet_avoid isOpen_ball hp.2))).inter (hInfo _ (hdom (x p.1)))).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_)).inter
    (hK' (measurableSet_hitting isOpen_ball hp.2))
  exact hInfo _ (measurableSet_le measurable_const ((continuous_infDist_pt _).measurable.comp (hfwd _)))

end Added

section Final

variable {Ω : Type*} {ℋ₀ ℋ' ℋc : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The enlarged-stop increment law in a component reference chart, from the marked laws**: PROVE-R5-OUTER's
`R5Out.hasOldChartIncrementLawOn_of_enlarged_component_marked` with `hAdded` discharged
(`measurable_globalOldChartAddedSet_oldOn_comp`). The chart inputs are its domain events `hdom` and forward map
`hfwd` for the reference record `ℋ₀`, `dom ⊆ ℍ ∖ B` with an open complementary piece, and the nesting of the
enlarged complement in the chart's domain on `G`. -/
theorem hasOldChartIncrementLawOn_of_enlarged_component_fwd [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {B K K' : Ω → Set ℂ} {g₀ : Ω → DistOn upperHalfPlaneOpens}
    (hB₀ : germSigma B h ≤ ℋ₀) (hg₀ : Measurable[germSigma B h] g₀)
    (hHarm₀ : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₀ ω) (H \ B ω))
    (hK₀ : IsCondZeroBoundaryGFF P ℋ₀ (fun ω => H \ B ω) fun ω => h ω - g₀ ω)
    (hℋ' : ℋ' ≤ mΩ) (hℋc : ℋc ≤ mΩ)
    (hK'm : Measurable[mΩ, hittingSigma] K') (hK'reg : ∀ᵐ ω ∂P, K' ω ⊆ H ∧ IsOpen (H \ K' ω))
    (hK'loc : IsHistoryAvoidanceLocal ℋ' K' h P)
    (hKm : Measurable[mΩ, hittingSigma] K) (hKreg : ∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω))
    (hKloc : IsHistoryAvoidanceLocal ℋc K h P)
    (hInfo : ℋ₀ ≤ germSigma K' h ⊔ ℋ')
    {E : Set Ω} (hE : MeasurableSet[germSigma K h ⊔ ℋc] E) (hE' : MeasurableSet[germSigma K' h ⊔ ℋ'] E)
    (hKE : ∀ ω ∈ E, K ω = K' ω)
    (hmarks : MeasurableSpace.comap ((↑) : E → Ω) ℋc = MeasurableSpace.comap ((↑) : E → Ω) ℋ')
    {G : Set Ω} (hG : MeasurableSet[ℋ₀] G) {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldSub : ∀ ω ∈ G, ((old ω).dom : Set ℂ) ⊆ H \ B ω) (hBo : ∀ ω ∈ G, IsOpen (H \ B ω))
    (hCut : ∀ ω ∈ G, IsOpen ((H \ B ω) \ (old ω).dom))
    (hK'o : ∀ ω ∈ G, IsOpen (H \ K' ω)) (hNest : ∀ ω ∈ G, H \ K' ω ⊆ (old ω).dom)
    {M : Set Ω} (hMG : M ⊆ G) (hME : M ⊆ E) {current : Ω → Chart}
    (hcur : ∀ ω ∈ M, ((current ω).dom : Set ℂ) = H \ K ω) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean B h P gOld →
      ∀ gNow : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h P gNow →
        HasOldChartIncrementLawOn P M old current gOld gNow := by
  have hBm : Measurable[ℋ₀, hittingSigma] B :=
    (measurable_iff_comap_le.2 (comap_le_germSigma B h)).mono hB₀ le_rfl
  have hK'm' : Measurable[germSigma K' h ⊔ ℋ', hittingSigma] K' :=
    (measurable_iff_comap_le.2 (comap_le_germSigma K' h)).mono le_sup_left le_rfl
  exact R5Out.hasOldChartIncrementLawOn_of_enlarged_component_marked hh hB₀ hg₀ hHarm₀ hK₀ hℋ' hℋc hK'm hK'reg
    hK'loc hKm hKreg hKloc hInfo hE hE' hKE hmarks hG hOld hdom hfwd hOldSub hBo hCut hK'o hNest
    (measurable_globalOldChartAddedSet_oldOn_comp hInfo hG hOld hdom hfwd hBm hOldSub hCut hK'm' hK'o) hMG hME hcur

end Final

end InteractingSLE.Sec7.R5OLaw
