/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS4Theta
import InteractingSLE.Spec.Sec5.CrossCondStagedMeanCat
import InteractingSLE.Spec.Sec7.Lemma71MMeas
import InteractingSLE.Spec.Sec5.Prop59PiecesArc

/-!
# Measurable random charts: Loewner charts at random times, compositions, restarted charts

Packet PROVE-STAGED-S5 (the chart data of the restarted word, (M3) of `planning/handoffs/PROVE-STAGED-S3.md` §5.2).
A random conformal chart has **measurable data** (`IsMeasChart`) when its closed-disc domain events and its masked
forward maps and lifts at every point are measurable — exactly what `Sec7.Lemma71M.measurable_chartAvoid` consumes.

* **`measurableSet_closedBall_subset_dom_loewnerChartAtTime`**: the closed-disc events of the centred Loewner chart
  at a random time `τ` (a compact disc outside the hull at `τ` is outside the hull at some rational `q > τ`, by
  compactness and the openness of `ℍ ∖ K_q`);
* **`IsMeasChart.trans`**: compositions of charts with measurable data have measurable data (the domain of the
  composition is `dom c ∩ c⁻¹(dom d)`; a compact image `c(B)` lies in the open `dom d` iff it lies in a finite union of
  rational closed discs inside `dom d`; forward maps and lifts through the jointly measurable masked maps of `d`);
* **`isMeasChart_rChart`**: the restarted chart of a measurable family of killed arcs at a measurable start before the
  terminal capacity, in a chart with measurable data.

Conditional helpers with distinct names; R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Sec5.CrossCond.StagedS5

open WangWu WangWu.ImgWord Coupling StagedS3

/-! ### Loewner charts at a random time -/

section RandomTime

variable {X : Type*} [MeasurableSpace X] {W : ℝ≥0 → X → ℝ} {τ : X → ℝ≥0}

/-- **Closed-disc events of the centred Loewner chart at a random time.** -/
theorem measurableSet_closedBall_subset_dom_loewnerChartAtTime (hWc : ∀ x, Continuous fun t => W t x)
    (hW0 : ∀ x, W 0 x = 0) (hτ : Measurable τ) (hWm : ∀ t, Measurable (W t)) (z : ℂ) (ε : ℝ) :
    MeasurableSet {x | closedBall z ε ⊆ (Chart.loewnerChartAtTime W τ x).dom} := by
  set S : ℝ≥0 → Set X := fun q => {x | closedBall z ε ⊆ (Chart.id.loewner (Ito.rpath (W · x)) q).dom} with hS
  have hSm : ∀ q, MeasurableSet (S q) := fun q =>
    Staged.measurableSet_closedBall_subset_dom_loewner hWc hW0 hWm q z ε
  have hv : ∀ x, Continuous (Ito.rpath (W · x)) := fun x => Staged.continuous_rpath_of (hWc x)
  have hv0 : ∀ x, Ito.rpath (W · x) 0 = 0 := fun x => Staged.rpath_zero_of_zero (hW0 x)
  have hdom : ∀ x {t : ℝ} (ht : 0 ≤ t) (w : ℂ),
      w ∈ (Chart.id.loewner (Ito.rpath (W · x)) t).dom ↔ w ∈ H \ fwdHull (Ito.rpath (W · x)) t :=
    fun x t ht w => Staged.mem_dom_loewner_iff_mem_diff_hull (hv x) (hv0 x) ht
  have e : {x | closedBall z ε ⊆ (Chart.loewnerChartAtTime W τ x).dom} =
      ⋃ q : ℚ, ({x | ((τ x : ℝ≥0) : ℝ) < q} ∩ S (q : ℝ).toNNReal) := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, hS]
    constructor
    · intro hB
      -- a cover of the disc by the complements of the hulls at rational times after `τ`
      set ι := {q : ℚ // ((τ x : ℝ≥0) : ℝ) < q}
      set U : ι → Set ℂ := fun q => H \ fwdHull (Ito.rpath (W · x)) (q.1 : ℝ) with hU
      have hne : Nonempty ι := by
        obtain ⟨q, hq⟩ := exists_rat_gt ((τ x : ℝ≥0) : ℝ)
        exact ⟨⟨q, hq⟩⟩
      have hq0 : ∀ q : ι, (0 : ℝ) ≤ q.1 := fun q => (NNReal.coe_nonneg _).trans q.2.le
      have hUo : ∀ q, IsOpen (U q) := fun q => QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hv x) (hq0 q)
      have hcov : closedBall z ε ⊆ ⋃ q, U q := by
        intro w hw
        have hwd := (hdom x (NNReal.coe_nonneg _) w).1 (hB hw)
        have hlt : ENNReal.ofReal ((τ x : ℝ≥0) : ℝ) < QuantumZipper.swallowTime (Ito.rpath (W · x)) w := by
          by_contra hc
          exact hwd.2 ⟨hwd.1, not_lt.1 hc⟩
        obtain ⟨q, hq0', h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
        have h1' : ENNReal.ofReal ((τ x : ℝ≥0) : ℝ) < ENNReal.ofReal q := h1
        have hτq : ((τ x : ℝ≥0) : ℝ) < q := ((ENNReal.ofReal_lt_ofReal_iff'.1 h1').1)
        refine mem_iUnion.2 ⟨⟨q, hτq⟩, hwd.1, fun hK => ?_⟩
        have h2' : ENNReal.ofReal q < QuantumZipper.swallowTime (Ito.rpath (W · x)) w := h2
        exact absurd hK.2 (not_le.2 h2')
      have hdir : Directed (fun A B => A ⊆ B) U := by
        intro q₁ q₂
        refine ⟨⟨min q₁.1 q₂.1, lt_min_iff.2 ⟨q₁.2, q₂.2⟩ |>.trans_le (by push_cast; exact le_rfl)⟩, ?_, ?_⟩
        · exact fun w hw => ⟨hw.1, fun hK => hw.2 (QuantumZipper.CoreArc.fwdHull_mono_coreArc
            (by push_cast; exact min_le_left _ _) hK)⟩
        · exact fun w hw => ⟨hw.1, fun hK => hw.2 (QuantumZipper.CoreArc.fwdHull_mono_coreArc
            (by push_cast; exact min_le_right _ _) hK)⟩
      obtain ⟨q, hq⟩ := (isCompact_closedBall z ε).elim_directed_cover U hUo hcov hdir
      have hqq : (((q.1 : ℝ).toNNReal : ℝ≥0) : ℝ) = q.1 := Real.coe_toNNReal _ (hq0 q)
      refine ⟨q.1, q.2, fun w hw => ?_⟩
      change w ∈ (Chart.id.loewner (Ito.rpath (W · x)) (((q.1 : ℝ).toNNReal : ℝ≥0) : ℝ)).dom
      rw [hdom x (NNReal.coe_nonneg _) w, hqq]
      exact hq hw
    · rintro ⟨q, hτq, hB⟩ w hw
      have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg _).trans hτq.le
      have hqq : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
      have hw' := (hdom x (NNReal.coe_nonneg _) w).1 (hB hw)
      rw [hqq] at hw'
      change w ∈ (Chart.id.loewner (Ito.rpath (W · x)) ((τ x : ℝ≥0) : ℝ)).dom
      rw [hdom x (NNReal.coe_nonneg _) w]
      exact ⟨hw'.1, fun hK => hw'.2 (QuantumZipper.CoreArc.fwdHull_mono_coreArc hτq.le hK)⟩
  rw [e]
  exact MeasurableSet.iUnion fun q =>
    (measurableSet_lt (measurable_coe_nnreal_real.comp hτ) measurable_const).inter (hSm _)

end RandomTime

/-! ### Random charts with measurable data -/

section MeasChart

variable {X : Type*}

/-- **A random conformal chart with measurable data** for the σ-algebra `m`: conformal with a continuous lift, and
its closed-disc domain events, masked forward maps and masked lifts are `m`-measurable. -/
structure IsMeasChart (m : MeasurableSpace X) (c : X → Chart) : Prop where
  conf : ∀ x, (c x).IsConformal
  lift : ∀ x, ContinuousOn (c x).2.2 (c x).dom
  ball : ∀ (z : ℂ) (ε : ℝ), MeasurableSet[m] {x | closedBall z ε ⊆ (c x).dom}
  fwd : ∀ z, Measurable[m] ({x | z ∈ (c x).dom}.indicator fun x => (c x).1 z)
  lft : ∀ z, Measurable[m] ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z)

/-- The domain of a composition of conformal charts. -/
theorem mem_dom_trans_iff {c d : Chart} (hc : c.IsConformal) (hd : d.IsConformal) {z : ℂ} :
    z ∈ (c.trans d).dom ↔ z ∈ c.dom ∧ c.1 z ∈ d.dom := by
  constructor
  · intro hz
    rw [(hc.trans hd).mem_dom_iff] at hz
    obtain ⟨h1, h2⟩ := hz
    have hw : d.2.1 (d.1 (c.1 z)) ∈ H := hd.2.1 h1
    have hz' : z ∈ c.dom := by
      rw [← h2]
      exact hc.inv_mem_dom hw
    refine ⟨hz', ?_⟩
    rw [hd.mem_dom_iff]
    refine ⟨h1, ?_⟩
    have := congrArg c.1 h2
    simp only [Chart.trans_fst, Chart.trans_inv] at this
    rw [hc.2.2 _ hw] at this
    exact this
  · rintro ⟨h1, h2⟩
    rw [(hc.trans hd).mem_dom_iff]
    refine ⟨hd.fwd_mem h2, ?_⟩
    simp only [Chart.trans_fst, Chart.trans_inv]
    rw [hd.inv_fwd h2, hc.inv_fwd h1]

variable [mX : MeasurableSpace X] {c d : X → Chart}

theorem IsMeasChart.measurableSet_mem (hc : IsMeasChart mX c) (z : ℂ) : MeasurableSet {x | z ∈ (c x).dom} :=
  Sec7.Lemma71E.measurableSet_mem_of_closedBall (C := fun x => ((c x).dom : Set ℂ)) (fun x => (c x).dom.isOpen)
    hc.ball z

theorem IsMeasChart.measurableSet_setOf_mem (hc : IsMeasChart mX c) :
    MeasurableSet {p : X × ℂ | p.2 ∈ ((c p.1).dom : Set ℂ)} :=
  Sec7.Lemma71I.measurableSet_setOf_mem (C := fun x => ((c x).dom : Set ℂ)) (fun x => (c x).dom.isOpen) hc.ball

/-- The masked forward maps of a chart with measurable data are jointly measurable. -/
theorem IsMeasChart.measurable_uncurry_fwd (hc : IsMeasChart mX c) :
    Measurable ({p : X × ℂ | p.2 ∈ ((c p.1).dom : Set ℂ)}.indicator fun p => (c p.1).1 p.2) :=
  Sec7.Lemma71I.measurable_indicator_uncurry (C := fun x => ((c x).dom : Set ℂ)) (fun x => (c x).dom.isOpen)
    hc.ball (F := fun x w => (c x).1 w) (fun x => (hc.conf x).differentiableOn_fwd.continuousOn) hc.fwd

/-- The masked lifts of a chart with measurable data are jointly measurable. -/
theorem IsMeasChart.measurable_uncurry_lift (hc : IsMeasChart mX c) :
    Measurable ({p : X × ℂ | p.2 ∈ ((c p.1).dom : Set ℂ)}.indicator fun p => (((c p.1).2.2 p.2 : ℝ) : ℂ)) := by
  refine Sec7.Lemma71I.measurable_indicator_uncurry (C := fun x => ((c x).dom : Set ℂ))
    (fun x => (c x).dom.isOpen) hc.ball (F := fun x w => (((c x).2.2 w : ℝ) : ℂ))
    (fun x => Complex.continuous_ofReal.comp_continuousOn (hc.lift x)) fun z => ?_
  have e : ({x | z ∈ ((c x).dom : Set ℂ)}.indicator fun x => (((c x).2.2 z : ℝ) : ℂ)) =
      (fun r : ℝ => (r : ℂ)) ∘ ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z) := by
    funext x
    by_cases hx : z ∈ (c x).dom
    · simp only [Function.comp_apply, indicator_of_mem (show x ∈ {x | z ∈ (c x).dom} from hx),
        indicator_of_mem (show x ∈ {x | z ∈ ((c x).dom : Set ℂ)} from hx)]
    · simp only [Function.comp_apply, indicator_of_notMem (show x ∉ {x | z ∈ (c x).dom} from hx),
        indicator_of_notMem (show x ∉ {x | z ∈ ((c x).dom : Set ℂ)} from hx), Complex.ofReal_zero]
  rw [e]
  exact Complex.measurable_ofReal.comp (hc.lft z)

/-- **Compositions of charts with measurable data have measurable data.** -/
theorem IsMeasChart.trans (hc : IsMeasChart mX c) (hd : IsMeasChart mX d) :
    IsMeasChart mX fun x => (c x).trans (d x) := by
  have hmem : ∀ x z, z ∈ ((c x).trans (d x)).dom ↔ z ∈ (c x).dom ∧ (c x).1 z ∈ (d x).dom := fun x z =>
    mem_dom_trans_iff (hc.conf x) (hd.conf x)
  -- the masked forward maps of `c` at a point
  set Fc : ℂ → X → ℂ := fun z => {x | z ∈ (c x).dom}.indicator fun x => (c x).1 z with hFc
  have hFcx : ∀ z x, z ∈ (c x).dom → Fc z x = (c x).1 z := fun z x hz =>
    indicator_of_mem (show x ∈ {x | z ∈ (c x).dom} from hz) _
  have hMd := hd.measurableSet_setOf_mem
  -- the domain events at a point
  have hdomm : ∀ z, MeasurableSet {x | z ∈ ((c x).trans (d x)).dom} := fun z => by
    have e : {x | z ∈ ((c x).trans (d x)).dom} =
        {x | z ∈ (c x).dom} ∩ (fun x => (x, Fc z x)) ⁻¹' {p : X × ℂ | p.2 ∈ ((d p.1).dom : Set ℂ)} := by
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, hmem]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [hFcx z x h1]; exact h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have h2' : Fc z x ∈ ((d x).dom : Set ℂ) := h2
        rwa [hFcx z x h1] at h2'
    rw [e]
    exact (hc.measurableSet_mem z).inter ((measurable_id.prodMk (hc.fwd z)) hMd)
  refine ⟨fun x => (hc.conf x).trans (hd.conf x),
    fun x => StagedS4.continuousOn_lift_trans (hc.conf x) (hd.conf x) (hc.lift x) (hd.lift x), ?_, ?_, ?_⟩
  · -- closed-disc events: finite unions of rational closed discs inside `dom d`
    intro z ε
    obtain ⟨D, hDB, hDc, hBD⟩ := (isCompact_closedBall z ε).isSeparable.exists_countable_dense_subset
    have hDcl : closure D = closedBall z ε :=
      Subset.antisymm (closure_minimal hDB isClosed_closedBall) hBD
    have e : {x | closedBall z ε ⊆ ((c x).trans (d x)).dom} =
        {x | closedBall z ε ⊆ ((c x).dom : Set ℂ)} ∩ ⋃ F : Finset (ℚ × ℚ × ℚ),
          ((⋂ y ∈ D, {x | Fc y x ∈ ballsK F}) ∩ {x | ballsK F ⊆ ((d x).dom : Set ℂ)}) := by
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter]
      constructor
      · intro hB
        have hBc : closedBall z ε ⊆ ((c x).dom : Set ℂ) := fun w hw => ((hmem x w).1 (hB hw)).1
        have hQ : IsCompact ((c x).1 '' closedBall z ε) :=
          (isCompact_closedBall z ε).image_of_continuousOn
            ((hc.conf x).differentiableOn_fwd.continuousOn.mono hBc)
        have hQd : (c x).1 '' closedBall z ε ⊆ ((d x).dom : Set ℂ) := by
          rintro _ ⟨w, hw, rfl⟩
          exact ((hmem x w).1 (hB hw)).2
        obtain ⟨F, hQF, hFd⟩ := exists_rationalBalls hQ (d x).dom.isOpen hQd
        refine ⟨hBc, F, fun y hy => ?_, hFd⟩
        rw [hFcx y x (hBc (hDB hy))]
        exact ballsU_subset_ballsK F (hQF (mem_image_of_mem _ (hDB hy)))
      · rintro ⟨hBc, F, hDF, hFd⟩ w hw
        have hcl : (c x).1 '' D ⊆ ballsK F := by
          rintro _ ⟨y, hy, rfl⟩
          rw [← hFcx y x (hBc (hDB hy))]
          exact hDF y hy
        have hca : ContinuousAt (c x).1 w :=
          (hc.conf x).differentiableOn_fwd.continuousOn.continuousAt ((c x).dom.isOpen.mem_nhds (hBc hw))
        have hwF : (c x).1 w ∈ ballsK F :=
          closure_minimal hcl (isCompact_ballsK F).isClosed
            (hca.continuousWithinAt.mem_closure_image (hDcl ▸ hw))
        exact (hmem x w).2 ⟨hBc hw, hFd hwF⟩
    rw [e]
    refine (Sec7.Lemma72B.measurableSet_subset_of_closedBall (C := fun x => ((c x).dom : Set ℂ))
      (fun x => (c x).dom.isOpen) hc.ball (isCompact_closedBall z ε)).inter
      (MeasurableSet.iUnion fun F => MeasurableSet.inter ?_ ?_)
    · exact MeasurableSet.biInter hDc fun y _ => (hc.fwd y) (isCompact_ballsK F).isClosed.measurableSet
    · exact Sec7.Lemma72B.measurableSet_subset_of_closedBall (C := fun x => ((d x).dom : Set ℂ))
        (fun x => (d x).dom.isOpen) hd.ball (isCompact_ballsK F)
  · -- forward maps
    intro z
    have hG := hd.measurable_uncurry_fwd
    have e : ({x | z ∈ ((c x).trans (d x)).dom}.indicator fun x => ((c x).trans (d x)).1 z) =
        {x | z ∈ ((c x).trans (d x)).dom}.indicator fun x =>
          ({p : X × ℂ | p.2 ∈ ((d p.1).dom : Set ℂ)}.indicator fun p => (d p.1).1 p.2) (x, Fc z x) := by
      funext x
      by_cases hx : z ∈ ((c x).trans (d x)).dom
      · obtain ⟨h1, h2⟩ := (hmem x z).1 hx
        rw [indicator_of_mem (show x ∈ {x | z ∈ ((c x).trans (d x)).dom} from hx),
          indicator_of_mem (show x ∈ {x | z ∈ ((c x).trans (d x)).dom} from hx), hFcx z x h1,
          indicator_of_mem (show (x, (c x).1 z) ∈ {p : X × ℂ | p.2 ∈ ((d p.1).dom : Set ℂ)} from h2)]
        rfl
      · rw [indicator_of_notMem (show x ∉ {x | z ∈ ((c x).trans (d x)).dom} from hx),
          indicator_of_notMem (show x ∉ {x | z ∈ ((c x).trans (d x)).dom} from hx)]
    rw [e]
    exact (hG.comp (measurable_id.prodMk (hc.fwd z))).indicator (hdomm z)
  · -- lifts
    intro z
    have hG := hd.measurable_uncurry_lift
    have e : ({x | z ∈ ((c x).trans (d x)).dom}.indicator fun x => ((c x).trans (d x)).2.2 z) =
        {x | z ∈ ((c x).trans (d x)).dom}.indicator fun x =>
          (({p : X × ℂ | p.2 ∈ ((d p.1).dom : Set ℂ)}.indicator
            fun p => (((d p.1).2.2 p.2 : ℝ) : ℂ)) (x, Fc z x)).re +
          ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z) x := by
      funext x
      by_cases hx : z ∈ ((c x).trans (d x)).dom
      · obtain ⟨h1, h2⟩ := (hmem x z).1 hx
        rw [indicator_of_mem (show x ∈ {x | z ∈ ((c x).trans (d x)).dom} from hx),
          indicator_of_mem (show x ∈ {x | z ∈ ((c x).trans (d x)).dom} from hx), hFcx z x h1,
          indicator_of_mem (show (x, (c x).1 z) ∈ {p : X × ℂ | p.2 ∈ ((d p.1).dom : Set ℂ)} from h2),
          indicator_of_mem (show x ∈ {x | z ∈ (c x).dom} from h1), Complex.ofReal_re]
        rfl
      · rw [indicator_of_notMem (show x ∉ {x | z ∈ ((c x).trans (d x)).dom} from hx),
          indicator_of_notMem (show x ∉ {x | z ∈ ((c x).trans (d x)).dom} from hx)]
    rw [e]
    exact ((Complex.measurable_re.comp (hG.comp (measurable_id.prodMk (hc.fwd z)))).add (hc.lft z)).indicator
      (hdomm z)

end MeasChart

/-! ### The restarted chart of a measurable family of killed arcs -/

section Restart

variable {X : Type*} [MeasurableSpace X] {γ : X → ℝ → ℂ} {P : X → Set ℝ} {S₀ : X → ℝ≥0}

/-- The killed driver frozen at the start `S₀`. -/
def frozKW (γ : X → ℝ → ℂ) (P : X → Set ℝ) (S₀ : X → ℝ≥0) : ℝ≥0 → X → ℝ :=
  fun t x => kW (γ x) (P x) (min t (S₀ x))

omit [MeasurableSpace X] in
theorem rpath_frozKW (x : X) : Ito.rpath (frozKW γ P S₀ · x) = Ito.clampDrv (kPath (γ x) (P x)) (S₀ x) := by
  funext r
  simp only [Ito.rpath, frozKW, Ito.clampDrv, kPath]
  congr 1
  rcases le_total r 0 with hr | hr
  · rw [max_eq_right hr, Real.toNNReal_of_nonpos hr, min_eq_left (NNReal.coe_nonneg _), Real.toNNReal_zero,
      min_eq_left (by exact zero_le)]
  · rw [max_eq_left hr]
    rcases le_total r (S₀ x) with hrS | hrS
    · rw [min_eq_left hrS, min_eq_left ((Real.toNNReal_le_iff_le_coe).2 hrS)]
    · rw [min_eq_right hrS, Real.toNNReal_coe, min_eq_right ((Real.le_toNNReal_iff_coe_le hr).2 hrS)]

variable (hF : Prop59Pieces.IsKilledFamily γ P) (hS₀ : Measurable S₀)
  (hlt : ∀ x, (S₀ x : WithTop ℝ≥0) < kLife (γ x) (P x))
include hF hlt

theorem continuous_frozKW (x : X) : Continuous fun t => frozKW γ P S₀ t x := by
  have h := (continuous_clampDrv_kPath (hF.arc x) (hlt x)).comp NNReal.continuous_coe
  refine h.congr fun t => ?_
  have := congrFun (rpath_frozKW (γ := γ) (P := P) (S₀ := S₀) x) (t : ℝ)
  simp only [Ito.rpath, Real.toNNReal_coe] at this
  exact this.symm

omit hlt in
theorem frozKW_zero (x : X) : frozKW γ P S₀ 0 x = 0 := by
  simp only [frozKW, zero_min]
  exact (hF.arc x).kW_zero

include hS₀ in
omit hlt in
theorem measurable_frozKW (t : ℝ≥0) : Measurable (frozKW γ P S₀ t) :=
  hF.measurable_uncurry_kW.comp ((measurable_const.min hS₀).prodMk measurable_id)

omit [MeasurableSpace X] hF hlt in
/-- The restarted chart is the composition with the Loewner chart of the frozen driver at the start. -/
theorem rChart_eq_trans (c : X → Chart) (x : X) :
    rChart (c x) (γ x) (P x) (S₀ x) = (c x).trans (Chart.loewnerChartAtTime (frozKW γ P S₀) S₀ x) := by
  rw [rChart, Chart.loewner_eq_trans, Chart.loewnerChartAtTime, rpath_frozKW]

include hS₀ in
/-- **The Loewner chart of the frozen driver at the start has measurable data.** -/
theorem isMeasChart_loewnerChartAtTime_frozKW :
    IsMeasChart ‹MeasurableSpace X› (Chart.loewnerChartAtTime (frozKW γ P S₀) S₀) := by
  have hWc := continuous_frozKW hF hlt
  have hW0 := frozKW_zero (S₀ := S₀) hF
  have hWm := measurable_frozKW hF hS₀
  have hWs : ∀ t, Measurable (Chart.stoppedDrv (frozKW γ P S₀) S₀ t) := fun t => by
    have e : Chart.stoppedDrv (frozKW γ P S₀) S₀ t = fun x => frozKW γ P S₀ (min t (S₀ x)) x := rfl
    rw [e]
    exact hF.measurable_uncurry_kW.comp
      (((measurable_const.min hS₀).min hS₀).prodMk measurable_id)
  refine ⟨Chart.isConformal_loewnerChartAtTime hWc hW0, fun x => ?_,
    measurableSet_closedBall_subset_dom_loewnerChartAtTime hWc hW0 hS₀ hWm,
    Chart.measurable_indicator_fwd_loewnerChartAtTime le_rfl hWc hW0 hS₀ hWs,
    Chart.measurable_indicator_lift_loewnerChartAtTime le_rfl hWc hW0 hS₀ hWs⟩
  exact Chart.continuousOn_lift_loewner (Staged.continuous_rpath_of (hWc x)) (Staged.rpath_zero_of_zero (hW0 x))
    (S₀ x).coe_nonneg

include hS₀ in
/-- **The restarted chart of a measurable family of killed arcs has measurable data.** -/
theorem isMeasChart_rChart {c : X → Chart} (hc : IsMeasChart ‹MeasurableSpace X› c) :
    IsMeasChart ‹MeasurableSpace X› fun x => rChart (c x) (γ x) (P x) (S₀ x) := by
  have h := hc.trans (isMeasChart_loewnerChartAtTime_frozKW hF hS₀ hlt)
  have e : (fun x => rChart (c x) (γ x) (P x) (S₀ x)) =
      fun x => (c x).trans (Chart.loewnerChartAtTime (frozKW γ P S₀) S₀ x) :=
    funext fun x => rChart_eq_trans c x
  rw [e]
  exact h

end Restart

end InteractingSLE.Sec5.CrossCond.StagedS5
