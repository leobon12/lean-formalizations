/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlLocal

/-!
# The record-transport input `hAdded`: the pulled increment is measurable for the enlarged record

Packet PROVE-R5-ENLARGED (continued). After `R5EnlLocal` the only record-transport input of the enlarged-stop law is
`hAdded`: the increment `{w ∈ ℍ : old⁻¹(w) ∈ K'}` (in the reference chart, on the reference event `G`; empty off `G`)
is hitting-measurable for the enlarged record `ℋ₁`. It follows from the measurability of the reference chart's forward
map and of the reference set `B` for the reference record `ℋ₀ ≤ ℋ₁`, and of the enlarged set `K'` for `ℋ₁`:
for an open `U ⊆ ℍ`, on `G`,

`increment ∩ U ≠ ∅  ⟺  ∃ x (dense), r, ε ∈ ℚ₊ : B(x, r) ⊆ ℍ ∖ B, ε ≤ dist(old(z), Uᶜ) for the dense z ∈ B(x, r),
  K' ∩ B(x, r) ≠ ∅`

(`⟸`: a point `y ∈ K' ∩ B(x, r)` has `old(y) ∈ U` by continuity of the chart and density; `⟹`: around
`y = old⁻¹(w)` the chart is continuous and the domain open). Each condition is a countable combination of events of
`ℋ₀` and hitting events of `K'`.

* `globalOldChartAddedSet_oldOn_of_mem`, `globalOldChartAddedSet_oldOn_of_notMem` — the increment of the extended
  charts;
* **`measurable_globalOldChartAddedSet_oldOn`** — `hAdded`;
* `measurableSet_inter_mem_dom_of_hitting` — the reference chart's domain events (`hdom`) from the hitting measurability
  of `B` (so only the forward map `hfwd` is a chart input).

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.R5Enl

open LocalSets PocketStopSide

section Added

variable {Ω : Type*}

/-- On the reference event, the increment of the extended charts is the reference-chart preimage of `K'`. -/
theorem globalOldChartAddedSet_oldOn_of_mem {G : Set Ω} {old : Ω → Chart} {K' : Ω → Set ℂ} {ω : Ω}
    (hω : ω ∈ G) (hc : (old ω).IsConformal) (hK'o : IsOpen (H \ K' ω)) :
    globalOldChartAddedSet (oldOn G old) (curOn G fun ω => H \ K' ω) ω =
      {w | w ∈ H ∧ (old ω).2.1 w ∈ K' ω} := by
  rw [globalOldChartAddedSet, dom_curOn_of_mem hω hK'o sdiff_subset, oldOn_of_mem hω]
  ext w
  constructor
  · rintro ⟨hw, hn⟩
    refine ⟨hw, ?_⟩
    by_contra hk
    exact hn ⟨hw, hc.2.1 hw, hk⟩
  · rintro ⟨hw, hk⟩
    exact ⟨hw, fun h => h.2.2 hk⟩

/-- Off the reference event the increment of the extended charts is empty. -/
theorem globalOldChartAddedSet_oldOn_of_notMem {G : Set Ω} {old : Ω → Chart} {K' : Ω → Set ℂ} {ω : Ω}
    (hω : ω ∉ G) : globalOldChartAddedSet (oldOn G old) (curOn G fun ω => H \ K' ω) ω = ∅ := by
  rw [globalOldChartAddedSet, dom_curOn_of_notMem hω, oldOn_of_notMem hω]
  ext w
  constructor
  · rintro ⟨hw, hn⟩
    exact absurd ⟨hw, hw⟩ hn
  · intro h
    exact absurd h (notMem_empty w)

theorem neg_I_notMem_H : -Complex.I ∉ H := by
  change ¬ 0 < (-Complex.I).im
  rw [Complex.neg_im, Complex.I_im]
  norm_num

variable {ℋ₀ ℋ₁ : MeasurableSpace Ω}

/-- **`hAdded`**: the increment of the extended charts is hitting-measurable for `ℋ₁`, from the measurability of the
reference chart's forward map and of the reference set `B` for `ℋ₀ ≤ ℋ₁`, and of `K'` for `ℋ₁`. -/
theorem measurable_globalOldChartAddedSet_oldOn (hInfo : ℋ₀ ≤ ℋ₁) {G : Set Ω} (hG : MeasurableSet[ℋ₀] G)
    {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    {B K' : Ω → Set ℂ} (hB : Measurable[ℋ₀, hittingSigma] B)
    (hOldDom : ∀ ω ∈ G, ((old ω).dom : Set ℂ) = H \ B ω)
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
    {ω | Disjoint (B ω) (ball (x p.1) p.2.1)} ∩
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
        refine ⟨(k, r, ε), ⟨hε1, hballH⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
        · rw [hOldDom ω hω] at hballdom
          show Disjoint (B ω) (ball (x k) (r : ℝ))
          exact Set.disjoint_left.2 fun z hzB hz => (hballdom hz).2 hzB
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
    · rintro ⟨hω, p, ⟨hε, hballH⟩, ⟨hdisj, hgood⟩, hK⟩
      have hc := hOld ω hω
      rw [globalOldChartAddedSet_oldOn_of_mem hω hc (hK'o ω hω)]
      have hballdom : ball (x p.1) (p.2.1 : ℝ) ⊆ (old ω).dom := by
        intro z hz
        rw [hOldDom ω hω]
        exact ⟨hballH hz, fun hzB => Set.disjoint_left.1 hdisj hzB hz⟩
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
  refine ((hInfo _ (hB (measurableSet_avoid isOpen_ball hp.2))).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_)).inter
    (hK' (measurableSet_hitting isOpen_ball hp.2))
  exact hInfo _ (measurableSet_le measurable_const ((continuous_infDist_pt _).measurable.comp (hfwd _)))

/-- **The reference chart's domain events from the reference set**: if the chart's domain is `ℍ ∖ B` on `G` and `B`
is hitting-measurable, the domain events on `G` are measurable (`hdom` of the increment law). -/
theorem measurableSet_inter_mem_dom_of_hitting {G : Set Ω} (hG : MeasurableSet[ℋ₀] G) {old : Ω → Chart}
    {B : Ω → Set ℂ} (hB : Measurable[ℋ₀, hittingSigma] B) (hOldDom : ∀ ω ∈ G, ((old ω).dom : Set ℂ) = H \ B ω)
    (hBc : ∀ ω ∈ G, IsOpen (H \ B ω)) (z : ℂ) :
    MeasurableSet[ℋ₀] (G ∩ {ω | z ∈ (old ω).dom}) := by
  by_cases hz : z ∈ H
  · have hzo : IsOpen H := QuantumZipper.isOpen_H
    obtain ⟨ρ, hρ, hρH⟩ := Metric.isOpen_iff.1 hzo z hz
    -- `z ∉ B` iff some small ball around `z` avoids `B` (on `G`, `ℍ ∖ B` is open)
    have e : G ∩ {ω | z ∈ (old ω).dom} =
        G ∩ ⋃ n : ℕ, {ω | Disjoint (B ω) (ball z (ρ / ((n : ℝ) + 1)))} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hω, hzd⟩
        refine ⟨hω, ?_⟩
        rw [← SetLike.mem_coe, hOldDom ω hω] at hzd
        obtain ⟨e, he, heB⟩ := Metric.isOpen_iff.1 (hBc ω hω) z hzd
        obtain ⟨n, hn⟩ := exists_nat_gt (ρ / e)
        refine ⟨n, Set.disjoint_left.2 fun w hwB hw => (heB (ball_subset_ball ?_ hw)).2 hwB⟩
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ he] at hn
        nlinarith
      · rintro ⟨hω, n, hn⟩
        refine ⟨hω, ?_⟩
        rw [← SetLike.mem_coe, hOldDom ω hω]
        exact ⟨hz, fun hzB => Set.disjoint_left.1 hn hzB (mem_ball_self (by positivity))⟩
    rw [e]
    refine hG.inter (MeasurableSet.iUnion fun n => hB (measurableSet_avoid isOpen_ball ?_))
    exact (ball_subset_ball (div_le_self hρ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))).trans hρH
  · have e : G ∩ {ω | z ∈ (old ω).dom} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hω hzd
      rw [← SetLike.mem_coe, hOldDom ω hω] at hzd
      exact hz hzd.1
    rw [e]
    exact MeasurableSet.empty

end Added

section Final

open WholeField

variable {Ω : Type*} {ℋ₀ ℋ' ℋc : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **R.5's enlarged-stop increment law from the marked laws, with every record-transport input discharged**: no
`hGerm` (`R5EnlLocal`), `hAdded` and the chart's domain events from the hitting measurability of the reference and
enlarged sets. The only chart input is the measurability `hfwd` of the reference chart's forward map for the reference
record `ℋ₀` on the reference event `G`. -/
theorem hasOldChartIncrementLawOn_of_enlarged_marked_fwd [IsProbabilityMeasure P]
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
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldDom : ∀ ω ∈ G, ((old ω).dom : Set ℂ) = H \ B ω) (hBo : ∀ ω ∈ G, IsOpen (H \ B ω))
    (hK'o : ∀ ω ∈ G, IsOpen (H \ K' ω)) (hNest : ∀ ω ∈ G, H \ K' ω ⊆ H \ B ω)
    {M : Set Ω} (hMG : M ⊆ G) (hME : M ⊆ E) {current : Ω → Chart}
    (hcur : ∀ ω ∈ M, ((current ω).dom : Set ℂ) = H \ K ω) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean B h P gOld →
      ∀ gNow : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h P gNow →
        HasOldChartIncrementLawOn P M old current gOld gNow := by
  have hBm : Measurable[ℋ₀, hittingSigma] B :=
    (measurable_iff_comap_le.2 (comap_le_germSigma B h)).mono hB₀ le_rfl
  have hK'm' : Measurable[germSigma K' h ⊔ ℋ', hittingSigma] K' :=
    (measurable_iff_comap_le.2 (comap_le_germSigma K' h)).mono le_sup_left le_rfl
  exact hasOldChartIncrementLawOn_of_enlarged_marked_noGerm hh hB₀ hg₀ hHarm₀ hK₀ hℋ' hℋc hK'm hK'reg hK'loc
    hKm hKreg hKloc hInfo hE hE' hKE hmarks hG hOld (measurableSet_inter_mem_dom_of_hitting hG hBm hOldDom hBo)
    hfwd hOldDom hK'o hNest (measurable_globalOldChartAddedSet_oldOn hInfo hG hOld hfwd hBm hOldDom hK'm' hK'o)
    hMG hME hcur

end Final

end InteractingSLE.Sec7.R5Enl
