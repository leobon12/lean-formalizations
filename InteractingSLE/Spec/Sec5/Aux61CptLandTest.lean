/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptAccess
import InteractingSLE.Spec.Sec5.Aux61GWindow18Geometry
import InteractingSLE.Spec.Exist.StagedLaw2Flow

/-!
# The Borel landing test of the per-outcome family

Packet PROVE-AUX61-CAPTURE (rulings R103, R103a). On the certified retained records of a good time (GLUEINST's
`Aux61GWindow17.certifiedRecords`, with the canonical chart `recordChart`), a rational landing parameter
`L = (v₀, ε₀, M, d)` defines the **landing test** (`landTest`): at every rational point of the chart half-disc
`ℍ ∩ B(v₀, ε₀)` the counterflow-chart image of the inverse chart is bounded by `M`, and at every rational real point of
the closed interval `[v₀ − ε₀, v₀ + ε₀]` the bounded inverse stays at distance `≥ d` from `1` (the image of `∞`) and its
physical point has imaginary part `≥ d` and distance `≥ d` from the own prefix. The records passing it form a Borel set
(`measurableSet_landRecords`). Everything is read from the record: the chart, the counterflow driver frozen at `s`
(`recDrv`), the own prefix (`recPrefix`).

R48/R77 respected; nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.CA (cayley cayleyInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu Aux61SlitW Aux61R1C Aux61GInst Aux61GWindow17 LawUnique
universe u

variable (S : SourceSetting.{u}) (t : GoodTime S)

/-- The counterflow driver read from a record, frozen at the counterflow time. -/
def recDrv (y : SourceRecord S.nL S.nR) : ℝ → ℝ := Ito.rpath (frozenDrv (rationalTime S.s) y.1)

/-- The physical point of a chart point, through the bounded inverse of the canonical chart. -/
def recPhys (y : SourceRecord S.nL S.nR) (a : ℂ) : ℂ := cayleyInv (boundedInverse (recordChart S t y) a)

/-- The own prefix read from a record. -/
def recPrefix (y : SourceRecord S.nL S.nR) : Set ℂ := (fun r : ℝ => recTrace y.2 r) '' Icc 0 (t.1 : ℝ)

/-- Rational landing parameters `(v₀, ε₀, M, d)` with `ε₀, d > 0`. -/
abbrev LandParam := {L : ℚ × ℚ × ℚ × ℚ // 0 < L.2.1 ∧ 0 < L.2.2.2}

/-- **The landing test** of a record. -/
def landTest (L : LandParam) (y : SourceRecord S.nL S.nR) : Prop :=
  (∀ a b : ℚ, 0 < b → ratPt a b ∈ ball ((L.1.1 : ℝ) : ℂ) (L.1.2.1 : ℝ) →
    ‖revChart (recDrv S y) (rationalTime S.s) (recPhys S t y (ratPt a b))‖ ≤ (L.1.2.2.1 : ℝ) ∧
    (L.1.2.2.2 : ℝ) ≤ (revChart (recDrv S y) (rationalTime S.s) (recPhys S t y (ratPt a b))).re) ∧
  (∀ a : ℚ, |(a : ℝ) - L.1.1| ≤ L.1.2.1 →
    (L.1.2.2.2 : ℝ) ≤ ‖boundedInverse (recordChart S t y) ((a : ℝ) : ℂ) - 1‖ ∧
    (L.1.2.2.2 : ℝ) ≤ (recPhys S t y ((a : ℝ) : ℂ)).im ∧
    (L.1.2.2.2 : ℝ) ≤ infDist (recPhys S t y ((a : ℝ) : ℂ)) (recPrefix S t y))

/-- **The landing records**: certified records passing the landing test. -/
def landRecords (L : LandParam) : Set (SourceRecord S.nL S.nR) :=
  certifiedRecords S t ∩ {y | landTest S t L y}

/-! ### Measurability on the certified records -/

theorem measurable_cayleyInv : Measurable cayleyInv :=
  (measurable_const.mul (measurable_const.add measurable_id)).div (measurable_const.sub measurable_id)

theorem measurable_negInv : Measurable negInv := measurable_inv.neg

/-- The bounded inverse at a closed-half-plane point is measurable on the certified records. -/
theorem measurable_boundedInverse_cert {z : ℂ} (hz : z ∈ Hbar) :
    Measurable (fun y : certifiedRecords S t => boundedInverse (recordChart S t y.1) z) := by
  have h := (Aux61SlitWAA.measurable_boundedInverse_Hbar (measurableSet_certifiedRecords S t)
    (recordChart_spec S t).measurable (fun y _ => (recordChart_spec S t).conformal y)
    (fun _ hy => recordChart_extension S t hy) hz).comp
    (measurable_subtype_coe : Measurable (Subtype.val : certifiedRecords S t → SourceRecord S.nL S.nR))
  have heq : (fun y : certifiedRecords S t => (certifiedRecords S t).indicator
      (fun y => boundedInverse (recordChart S t y) z) y.1) =
      (fun y : certifiedRecords S t => boundedInverse (recordChart S t y.1) z) :=
    funext fun y => indicator_of_mem y.2 _
  change Measurable (fun y : certifiedRecords S t => (certifiedRecords S t).indicator
    (fun y => boundedInverse (recordChart S t y) z) y.1) at h
  rwa [heq] at h

theorem measurable_recPhys_cert {z : ℂ} (hz : z ∈ Hbar) :
    Measurable (fun y : certifiedRecords S t => recPhys S t y.1 z) :=
  measurable_cayleyInv.comp (measurable_boundedInverse_cert S t hz)

/-- The record driver is continuous and starts at `0` on certified records. -/
theorem recDrv_facts {y : SourceRecord S.nL S.nR} (hy : y ∈ certifiedRecords S t) :
    Continuous (recDrv S y) ∧ recDrv S y 0 = 0 :=
  ⟨hy.2.1.continuous_rpath, hy.2.1.rpath_zero⟩

/-- **The counterflow chart at a measurable point is measurable** on the certified records. -/
theorem measurable_revChart_cert {u : certifiedRecords S t → ℂ} (hu : Measurable u) :
    Measurable (fun y : certifiedRecords S t => revChart (recDrv S y.1) (rationalTime S.s) (u y)) := by
  have h := (Exist.StagedLaw.measurable_fwdMap_param (W := fun y : certifiedRecords S t => recDrv S y.1)
    (fun y => (recDrv_facts S t y.2).1)
    (fun r => (measurable_frozenDrv (rationalTime S.s) r.toNNReal).comp
      (measurable_fst.comp measurable_subtype_coe))
    (fun y => (recDrv_facts S t y.2).2) (τ := fun _ => ((rationalTime S.s : ℝ≥0) : ℝ)) measurable_const
    (fun _ => NNReal.coe_nonneg _) (measurable_negInv.comp hu)).1
  exact measurable_negInv.comp h

/-- The good time is positive. -/
theorem goodTime_pos : (0 : ℝ) < (t.1 : ℝ) := by
  obtain ⟨y, hy⟩ := t.2
  exact hy.1.facts.1

/-- On certified records the own record trace is continuous on the retained interval. -/
theorem continuousOn_recTrace_cert {y : SourceRecord S.nL S.nR} (hy : y ∈ certifiedRecords S t) :
    ContinuousOn (fun r : ℝ => recTrace y.2 r) (Icc 0 (t.1 : ℝ)) := by
  have hg : y ∈ goodSet (rationalTime S.s) t.1 := hy.1.2
  have hc := hg.1.facts.2.2.2.2.2.2.1
  have hq0 : (0 : ℚ) ≤ t.1 := by exact_mod_cast (goodTime_pos S t).le
  have hq := coe_rationalTime hq0
  refine hc.congr fun r hr => ?_
  have hr' : r ≤ ((rationalTime t.1 : ℝ≥0) : ℝ) := by rw [hq]; exact hr.2
  exact (fullTrace_of_le hr').symm

/-- **Distance to the own prefix is measurable** at a measurable point, on the certified records. -/
theorem measurable_infDist_recPrefix {u : certifiedRecords S t → ℂ} (hu : Measurable u) :
    Measurable (fun y : certifiedRecords S t => infDist (u y) (recPrefix S t y.1)) := by
  let J := Icc (0 : ℝ) (t.1 : ℝ)
  have : CompactSpace J := isCompact_iff_compactSpace.1 isCompact_Icc
  have : Nonempty J := ⟨⟨0, le_rfl, (goodTime_pos S t).le⟩⟩
  let f : certifiedRecords S t → J → ℂ := fun y j => recTrace y.1.2 j
  have hfc : ∀ y, Continuous (f y) := fun y =>
    (continuousOn_recTrace_cert S t y.2).comp_continuous continuous_subtype_val (fun j => j.2)
  have hfm : ∀ j, Measurable (fun y => f y j) := fun j =>
    (measurable_recTrace (j : ℝ)).comp (measurable_snd.comp measurable_subtype_coe)
  have hr : ∀ y : certifiedRecords S t, range (f y) = recPrefix S t y.1 := by
    intro y
    ext w
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.1, j.2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  have h2 : ∀ z, Measurable (fun y : certifiedRecords S t => infDist z (recPrefix S t y.1)) := by
    intro z
    simpa only [hr] using Aux61GInst.measurable_infDist_compact_range hfc hfm z
  exact measurable_comp_of_continuous_of_measurable
    (u := fun z (y : certifiedRecords S t) => infDist z (recPrefix S t y.1))
    (fun _ => continuous_infDist_pt _) h2 hu

theorem ratPt_mem_Hbar {a b : ℚ} (hb : 0 < b) : ratPt a b ∈ Hbar := by
  change (0 : ℝ) ≤ (ratPt a b).im
  simp only [ratPt]
  exact_mod_cast hb.le

theorem ofReal_mem_Hbar (a : ℝ) : ((a : ℝ) : ℂ) ∈ Hbar := by
  change (0 : ℝ) ≤ ((a : ℝ) : ℂ).im
  simp

/-- An implication with a constant premise is measurable when its conclusion is. -/
theorem measurableSet_imp {X : Type*} [MeasurableSpace X] {P : Prop} {Q : X → Prop}
    (hQ : P → MeasurableSet {x | Q x}) : MeasurableSet {x | P → Q x} := by
  by_cases hP : P
  · simpa only [hP, true_implies] using hQ hP
  · have h : {x : X | P → Q x} = univ := by
      ext x
      simp only [hP, false_implies, mem_ofPred_eq, mem_univ]
    rw [h]
    exact MeasurableSet.univ

/-- **The landing records are Borel.** -/
theorem measurableSet_landRecords (L : LandParam) : MeasurableSet (landRecords S t L) := by
  have hset : MeasurableSet {y : certifiedRecords S t | landTest S t L y.1} := by
    simp only [landTest, ofPred_and, ofPred_forall]
    refine (MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => MeasurableSet.iInter fun hb =>
      MeasurableSet.iInter fun _ => ?_).inter
      (MeasurableSet.iInter fun a => MeasurableSet.iInter fun _ => ?_)
    · have hm := measurable_revChart_cert S t (measurable_recPhys_cert S t (ratPt_mem_Hbar (a := a) hb))
      exact (measurableSet_le hm.norm measurable_const).inter
        (measurableSet_le measurable_const (Complex.measurable_re.comp hm))
    · have hz := ofReal_mem_Hbar (a : ℝ)
      exact (measurableSet_le measurable_const
        ((measurable_boundedInverse_cert S t hz).sub_const 1).norm).inter
        ((measurableSet_le measurable_const (Complex.measurable_im.comp
          (measurable_recPhys_cert S t hz))).inter
          (measurableSet_le measurable_const (measurable_infDist_recPrefix S t
            (measurable_recPhys_cert S t hz))))
  have himg : landRecords S t L = Subtype.val '' {y : certifiedRecords S t | landTest S t L y.1} := by
    ext y
    constructor
    · rintro ⟨hy, hT⟩
      exact ⟨⟨y, hy⟩, hT, rfl⟩
    · rintro ⟨y', hT, rfl⟩
      exact ⟨y'.2, hT⟩
  rw [himg]
  exact (measurableSet_certifiedRecords S t).subtype_image hset

/-! ### Consequences of the test -/

/-- A continuous lower bound at the rational points of an open real set holds on the whole set. -/
theorem le_of_forall_rat {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hf : ContinuousOn f U) {d : ℝ}
    (h : ∀ a : ℚ, (a : ℝ) ∈ U → d ≤ f a) : ∀ r ∈ U, d ≤ f r := by
  intro r hr
  by_contra hlt
  have hlt' : f r < d := lt_of_not_ge hlt
  have hev : ∀ᶠ x in 𝓝 r, f x < d ∧ x ∈ U :=
    ((hf.continuousAt (hU.mem_nhds hr)).eventually (gt_mem_nhds hlt')).and (hU.mem_nhds hr)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hev
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show r - δ < r by linarith)
  have hab : (a : ℝ) ∈ ball r δ := by
    rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  obtain ⟨hfa, haU⟩ := hball hab
  exact absurd (h a haU) (not_le.2 hfa)

/-- A continuous upper bound at the rational points of an open subset of `ℍ` holds on the whole set. -/
theorem le_of_forall_ratPt {g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H)
    (hg : ContinuousOn g U) {M : ℝ}
    (h : ∀ a b : ℚ, 0 < b → ratPt a b ∈ U → g (ratPt a b) ≤ M) : ∀ ζ ∈ U, g ζ ≤ M := by
  intro ζ hζ
  by_contra hlt
  have hlt' : M < g ζ := lt_of_not_ge hlt
  have hev : ∀ᶠ x in 𝓝 ζ, M < g x ∧ x ∈ U :=
    ((hg.continuousAt (hU.mem_nhds hζ)).eventually (lt_mem_nhds hlt')).and (hU.mem_nhds hζ)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hev
  obtain ⟨a, b, hab⟩ := exists_ratPt_dist_lt ζ hδ
  obtain ⟨hga, haU⟩ := hball hab
  have hb : (0 : ℝ) < (ratPt a b).im := hUH haU
  have hb' : 0 < b := by simpa [ratPt] using hb
  exact absurd (h a b hb' haU) (not_le.2 hga)

/-- On a certified record the canonical chart's domain misses the reflected counterflow hull of the record driver. -/
theorem recordChart_dom_subset {y : SourceRecord S.nL S.nR} (hy : y ∈ certifiedRecords S t) :
    ((recordChart S t y).dom : Set ℂ) ⊆ H \ negInv '' fwdHull (recDrv S y) (rationalTime S.s) := by
  have hg : y ∈ goodSet (rationalTime S.s) t.1 := hy.1.2
  have hd := (recordChart_spec S t).domain y
  change ((recordChart S t y).dom : Set ℂ) = Aux61Restart.restartComponent
    (Aux61Restart.historyHull (rationalTime S.s) (finY (rationalTime S.s) t.1) y)
    (finη (rationalTime S.s) t.1 y) t.1 _ at hd
  rw [Aux61Restart.historyHull, finY_of_mem hg, finη_of_mem hg,
    Aux61SlitWAB.cfDrv0_eq_frozenDrv hy.2.1] at hd
  intro z hz
  rw [hd] at hz
  have hz' := connectedComponentIn_subset _ _ hz
  exact ⟨hz'.1, fun hK => hz'.2 (Or.inl hK)⟩

/-- The physical point of an upper chart point is the inverse chart. -/
theorem recPhys_eq_of_mem_H {y : SourceRecord S.nL S.nR} (hy : y ∈ certifiedRecords S t) {ζ : ℂ}
    (hζ : ζ ∈ H) : recPhys S t y ζ = (recordChart S t y).2.1 ζ := by
  have hc := (recordChart_spec S t).conformal y
  rw [recPhys, (recordChart_extension S t hy).1 hζ, Function.comp_apply,
    QuantumZipper.CA.cayleyInv_cayley
      (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt (hc.2.1 hζ)))]

/-- **The bound of the test on the whole chart half-disc.** -/
theorem landTest_bound (L : LandParam) {y : SourceRecord S.nL S.nR} (hy : y ∈ landRecords S t L) :
    ∀ ζ ∈ H ∩ ball ((L.1.1 : ℝ) : ℂ) (L.1.2.1 : ℝ),
      ‖revChart (recDrv S y) (rationalTime S.s) ((recordChart S t y).2.1 ζ)‖ ≤ (L.1.2.2.1 : ℝ) := by
  have hc := (recordChart_spec S t).conformal y
  have hsub := recordChart_dom_subset S t hy.1
  obtain ⟨hw, -⟩ := recDrv_facts S t hy.1
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hU : IsOpen (H ∩ ball ((L.1.1 : ℝ) : ℂ) (L.1.2.1 : ℝ)) := QuantumZipper.isOpen_H.inter isOpen_ball
  refine le_of_forall_ratPt hU inter_subset_left ?_ ?_
  · intro ζ hζ
    have hm := hsub (hc.inv_mem_dom hζ.1)
    have h1 : ContinuousWithinAt (revChart (recDrv S y) (rationalTime S.s) ∘ (recordChart S t y).2.1)
        (H ∩ ball ((L.1.1 : ℝ) : ℂ) (L.1.2.1 : ℝ)) ζ :=
      (GlueImg.differentiableAt_revChart hw hs hm).continuousAt.comp_continuousWithinAt
        ((hc.1.continuousOn ζ hζ.1).mono inter_subset_left)
    exact h1.norm
  · intro a b hb hab
    have h := (hy.2.1 a b hb hab.2).1
    rwa [recPhys_eq_of_mem_H S t hy.1 hab.1] at h

/-- **The eastern certificate of the test on the whole chart half-disc**: the counterflow-chart image has real part
at least `d`. -/
theorem landTest_re (L : LandParam) {y : SourceRecord S.nL S.nR} (hy : y ∈ landRecords S t L) :
    ∀ ζ ∈ H ∩ ball ((L.1.1 : ℝ) : ℂ) (L.1.2.1 : ℝ),
      (L.1.2.2.2 : ℝ) ≤ (revChart (recDrv S y) (rationalTime S.s) ((recordChart S t y).2.1 ζ)).re := by
  have hc := (recordChart_spec S t).conformal y
  have hsub := recordChart_dom_subset S t hy.1
  obtain ⟨hw, -⟩ := recDrv_facts S t hy.1
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hU : IsOpen (H ∩ ball ((L.1.1 : ℝ) : ℂ) (L.1.2.1 : ℝ)) := QuantumZipper.isOpen_H.inter isOpen_ball
  have h := le_of_forall_ratPt (g := fun ζ =>
      -(revChart (recDrv S y) (rationalTime S.s) ((recordChart S t y).2.1 ζ)).re)
    (M := -(L.1.2.2.2 : ℝ)) hU inter_subset_left ?_ ?_
  · intro ζ hζ
    have := h ζ hζ
    linarith
  · intro ζ hζ
    have hm := hsub (hc.inv_mem_dom hζ.1)
    have h1 : ContinuousWithinAt (revChart (recDrv S y) (rationalTime S.s) ∘ (recordChart S t y).2.1)
        (H ∩ ball ((L.1.1 : ℝ) : ℂ) (L.1.2.1 : ℝ)) ζ :=
      (GlueImg.differentiableAt_revChart hw hs hm).continuousAt.comp_continuousWithinAt
        ((hc.1.continuousOn ζ hζ.1).mono inter_subset_left)
    exact (Complex.continuous_re.continuousAt.comp_continuousWithinAt h1).neg
  · intro a b hb hab
    have h := (hy.2.1 a b hb hab.2).2
    rw [recPhys_eq_of_mem_H S t hy.1 hab.1] at h
    linarith

/-- **The physical limits of the test on the open chart interval**: the inverse chart has a boundary limit at every
real point, with imaginary part `≥ d` and distance `≥ d` from the own prefix. -/
theorem landTest_phys (L : LandParam) {y : SourceRecord S.nL S.nR} (hy : y ∈ landRecords S t L)
    {r : ℝ} (hr : |r - L.1.1| < L.1.2.1) :
    Tendsto (recordChart S t y).2.1 (𝓝[H] (r : ℂ)) (𝓝 (recPhys S t y r)) ∧
      (L.1.2.2.2 : ℝ) ≤ (recPhys S t y r).im ∧
      ∀ u ∈ recPrefix S t y, (L.1.2.2.2 : ℝ) ≤ dist (recPhys S t y r) u := by
  set U : Set ℝ := {r : ℝ | |r - L.1.1| < L.1.2.1} with hUdef
  have hUo : IsOpen U := isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
  obtain ⟨hFeq, hFc⟩ := recordChart_extension S t hy.1
  have hφc : Continuous fun r : ℝ => boundedInverse (recordChart S t y) (r : ℂ) :=
    hFc.comp_continuous Complex.continuous_ofReal ofReal_mem_Hbar
  have hd : (0 : ℝ) < L.1.2.2.2 := by exact_mod_cast L.2.2
  -- the bounded inverse stays away from `1`
  have hA : ∀ r ∈ U, (L.1.2.2.2 : ℝ) ≤ ‖boundedInverse (recordChart S t y) (r : ℂ) - 1‖ :=
    le_of_forall_rat hUo ((hφc.sub continuous_const).norm.continuousOn) fun a ha => (hy.2.2 a ha.le).1
  have hne : ∀ r ∈ U, boundedInverse (recordChart S t y) (r : ℂ) ≠ 1 := fun r hr h1 => by
    have := hA r hr
    rw [h1, sub_self, norm_zero] at this
    linarith
  have hψc : ContinuousOn (fun r : ℝ => recPhys S t y r) U := fun r hr => by
    have hca : ContinuousAt cayleyInv (boundedInverse (recordChart S t y) (r : ℂ)) :=
      QuantumZipper.CA.continuousOn_cayleyInv.continuousAt (isOpen_ne.mem_nhds (hne r hr))
    exact (ContinuousAt.comp (f := fun r : ℝ => boundedInverse (recordChart S t y) (r : ℂ)) (x := r)
      hca hφc.continuousAt).continuousWithinAt
  have hB : ∀ r ∈ U, (L.1.2.2.2 : ℝ) ≤ (recPhys S t y r).im :=
    le_of_forall_rat hUo (Complex.continuous_im.comp_continuousOn hψc) fun a ha => (hy.2.2 a ha.le).2.1
  have hC : ∀ r ∈ U, (L.1.2.2.2 : ℝ) ≤ infDist (recPhys S t y r) (recPrefix S t y) :=
    le_of_forall_rat hUo ((continuous_infDist_pt _).comp_continuousOn hψc) fun a ha =>
      (hy.2.2 a ha.le).2.2
  refine ⟨?_, hB r hr, fun u hu => (hC r hr).trans (infDist_le_dist_of_mem hu)⟩
  have h1 : Tendsto (boundedInverse (recordChart S t y)) (𝓝[H] (r : ℂ))
      (𝓝 (boundedInverse (recordChart S t y) (r : ℂ))) :=
    (hFc (r : ℂ) (ofReal_mem_Hbar r)).tendsto.mono_left (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)
  have h2 := (QuantumZipper.CA.continuousOn_cayleyInv.continuousAt
    (isOpen_ne.mem_nhds (hne r hr))).tendsto.comp h1
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  simp only [Function.comp_apply]
  rw [← recPhys, recPhys_eq_of_mem_H S t hy.1 hζ]

end InteractingSLE.Sec5.Aux61Cpt
