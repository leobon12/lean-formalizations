/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketTraversalMeasRand

/-!
# The pocket word evolution from a change pocket opening at the flow seed (`rightLo = 0`)

Packet PROVE-STRIPSYS23, item 6. Specification §7.4.1, proof of Aux. lemma 130 (`source/spec/p385-432.md` L482–L489,
pp. 412–413): "If `x₀ = x` or `y₀ = y`, the same Jordan argument applies in the compactified domain. […] In the first
case the terminal visit may be at infinite ambient capacity. The complete-traversal and announcing arguments in Aux.
lemma 125 already allow that case."

PROVE-STRIPSYS20 assembled hPW (`Lemma725Ref.PocketWordEvolution`) from a random change pocket on an event
`G ⊆ {0 < rightLo}` (the bounded case, `x₀ ≠ x`). Since the selection event of Aux. lemma 130 may put all its
probability on `{rightLo = 0}` (the pocket opening at the flow seed `x₀ = x`, which the counterflow chart
`m(z) = −1/z` sends to `∞`), this file adds that case and the assembly over both cases:

* `IsCfPocketConfigInf`: the pathwise hypotheses of one realization opening at the flow seed (the change
  configuration with `rightLo = 0`, its orientation, the counterflow trace, its transience, the reverse visit order and
  visits of both walls, Aux. lemma 37's attachment constancy at infinity); the erased traversal `cfTraversalInf` in a
  Jordan coordinate at infinity is then a driven curve with points of large modulus (STRIPSYS18's
  `isDrivenCurve_cfTraversalInf`);
* `exists_measurable_pocketMarksInf_pts`: one Jordan coordinate at infinity, measurable at measurable points, with
  the same marks as in the bounded case (`marksR`, `marksL2`, `marksL1`; the inversion keeps the sides,
  `PocketMarks.cfCoord_sides`);
* `measurable_travSubInf`: the traversal at infinity is measurable at each fixed own time (the terminal clock value
  `ℓ(∞) = sup ℓ` is a countable supremum; the fibres below it are bounded);
* `PocketCouplingInputInf`: the coupling clause along the traversal at infinity (the named input of item 1 for this
  case, as `PocketCouplingInput` for the bounded case);
* **`pocketWordEvolution_of_cfPocketConfigInf`**: hPW from a random change pocket opening at the flow seed;
* **`pocketWordEvolution_of_changeConfig`**, `pocketWordEvolution_of_changeConfig'`: hPW from a random change
  pocket of either kind on a positive-probability event (the event of the two splits with positive probability is
  selected), with the counterflow measurable at fixed times — no restriction to `0 < rightLo`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function
open QuantumZipper (H Hbar)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketSeedOpen

open WangWu Lemma71I Lemma71C PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt PocketMeas
  PocketWordAssembly PocketTraversalMeasRand PhaseSel

/-! ### The pathwise hypotheses of one realization -/

/-- **The pathwise hypotheses of a change pocket opening at the flow seed traversed by the counterflow** (one
realization): the change configuration with `rightLo = 0`, its flow-chart orientation, the counterflow driver `W` and
trace `η` in the chart `m(z) = −1/z`, transient, the reverse first-visit order of both walls with all their points
visited (Lemma 5.7), and Aux. lemma 37's attachment constancy at infinity after the first visit of `m(y₀)`. -/
structure IsCfPocketConfigInf (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (W : ℝ → ℝ) (η : ℝ → ℂ) : Prop where
  conf : IsChangeConfigInc R L r
  seed : rightLo R L r = 0
  oriented : IsFlowChartOriented R L r
  trace : IsLoewnerTrace W η
  continuous_W : Continuous W
  W_zero : W 0 = 0
  transient : Tendsto (fun t => ‖η t‖) atTop atTop
  revR : IsWallReverseVisit R η
  revL : IsWallReverseVisit L η
  visR : IsWallVisited R η
  visL : IsWallVisited L η
  attach : Sec6.AttachmentConstancyInf η (cfPocket R L r) (cfArcRInf R L r) (cfArcLInf R L r)
    (firstHit η (cfArcRInf R L r 0))

/-- The Jordan coordinates at infinity of the change pocket opening at the flow seed (`m(y₀) ↦ 0`, `∞ ↦ ∞`). -/
abbrev IsCfJordanInf (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (ψ : ℂ → ℂ) : Prop :=
  Sec6.IsJordanCoordInf (cfPocket R L r) (cfPt (closePt R L r)) ψ

theorem IsCfPocketConfigInf.isReversePocketInf {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hc : IsCfPocketConfigInf R L r W η) :
    Sec6.IsReversePocketInf W η (cfPocket R L r) (cfArcRInf R L r) (cfArcLInf R L r)
      (firstHit η (cfArcRInf R L r 0)) :=
  hc.conf.isReversePocketInf_of_counterflow hc.seed hc.trace hc.continuous_W hc.W_zero hc.revR hc.revL hc.visR
    hc.visL

/-- **The erased traversal of a pocket opening at the flow seed is a driven curve with points of large modulus**
(PROVE-STRIPSYS18's `isDrivenCurve_cfTraversalInf`). -/
theorem IsCfPocketConfigInf.isDrivenCurve {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hc : IsCfPocketConfigInf R L r W η) {ψ : ℂ → ℂ} (hψ : IsCfJordanInf R L r ψ) :
    IsDrivenCurve (cfTraversalInf R L r η ψ) ∧
      ∀ M : ℝ, ∃ u, 0 ≤ u ∧ cfTraversalInf R L r η ψ u ∈ H ∧ M < ‖cfTraversalInf R L r η ψ u‖ :=
  hc.conf.isDrivenCurve_cfTraversalInf hc.seed hc.trace hc.continuous_W hc.W_zero hc.transient hc.revR hc.revL
    hc.visR hc.visL hc.attach hψ

/-! ### The clock at infinity -/

section Deterministic

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} {τ : ℝ}

/-- The terminal clock value is the supremum over integer times. -/
theorem clockEnd_eq_iSup_nat (hP : Sec6.IsReversePocketInf W η C α₁ α₂ τ) :
    Sec6.clockEnd η C τ = ⨆ n : ℕ, Sec6.pocketClockInf η C τ n := by
  have hb := hP.bddAbove_clock
  have hbn : BddAbove (range fun n : ℕ => Sec6.pocketClockInf η C τ n) :=
    hb.mono (range_subset_iff.2 fun n => mem_range_self _)
  refine le_antisymm (ciSup_le fun t => ?_) (ciSup_le fun n => le_ciSup hb _)
  exact (hP.monotone_clock (Nat.le_ceil t)).trans (le_ciSup hbn ⌈t⌉₊)

/-- **The right end of a fibre below the terminal clock value exceeds `a`** iff `a < τ` or some rational `q ≥ τ`,
`q > a`, has clock at most `v ∨ ℓ τ`. -/
theorem lt_pocketFibreInf_iff (hP : Sec6.IsReversePocketInf W η C α₁ α₂ τ) {v a : ℝ}
    (hv : v ∈ Ico 0 (Sec6.clockEnd η C τ)) :
    a < Sec6.pocketFibreInf η C τ v ↔
      a < τ ∨ ∃ q : ℚ, a < q ∧ τ ≤ q ∧ Sec6.pocketClockInf η C τ q ≤ max v (Sec6.pocketClockInf η C τ τ) := by
  obtain ⟨T, hτT, hvT⟩ := hP.exists_clock_gt hv.2
  rw [hP.fibre_eq_fibreRight_of_lt hv.1 hvT, lt_fibreRight_iff hP.continuous_clock hP.monotone_clock hτT]
  refine or_congr_right ⟨fun ⟨q, h1, h2, _, h4⟩ => ⟨q, h1, h2, h4⟩, fun ⟨q, h1, h2, h4⟩ => ⟨q, h1, h2, ?_, h4⟩⟩
  by_contra hqT
  push Not at hqT
  have h5 := (hP.monotone_clock hqT.le).trans h4
  rw [Sec6.IsReversePocketInf.clock_τ, max_eq_left hv.1] at h5
  exact absurd hvT (not_lt.2 h5)

end Deterministic

section Generic

variable {α : Type*} [MeasurableSpace α] {η : α → ℝ → ℂ}

/-- **The pocket clock at infinity is measurable at measurable times.** -/
theorem measurable_pocketClockInf (hη : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {C : α → Set ℂ}
    (hC : MeasurableSet {x : α × ℂ | x.2 ∈ C x.1}) {τ T : α → ℝ} (hτ : Measurable τ) (hτ0 : ∀ ω, 0 ≤ τ ω)
    (hT : Measurable T) : Measurable fun ω => Sec6.pocketClockInf (η ω) (C ω) (τ ω) (T ω) := by
  have h3 : MeasurableSet {x : α × ℝ | η x.1 (max x.2 0) ∈ C x.1} :=
    (measurable_fst.prodMk (measurable_uncurry_max hη hηm)) hC
  have hS : MeasurableSet {x : α × ℝ | x.2 ∈ Sec6.visitSetInf (η x.1) (C x.1) (τ x.1)} := by
    have heq : {x : α × ℝ | x.2 ∈ Sec6.visitSetInf (η x.1) (C x.1) (τ x.1)} =
        {x : α × ℝ | τ x.1 < x.2} ∩ {x : α × ℝ | η x.1 (max x.2 0) ∈ C x.1} := by
      ext x
      simp only [Sec6.visitSetInf, mem_ofPred_eq, mem_Ioi, mem_inter_iff]
      constructor
      · rintro ⟨h1, h3⟩
        exact ⟨h1, by rwa [max_eq_left ((hτ0 x.1).trans h1.le)]⟩
      · rintro ⟨h1, h3⟩
        exact ⟨h1, by rwa [max_eq_left ((hτ0 x.1).trans h1.le)] at h3⟩
    rw [heq]
    exact (measurableSet_lt (hτ.comp measurable_fst) measurable_snd).inter h3
  exact measurable_erasureClock hS hτ hT

end Generic

/-! ### The traversal at infinity on an event -/

section Defs

variable {Ω : Type*}

/-- The measurability of a random Jordan coordinate at infinity at measurable random points of the closed pocket, on
measurable subsets of `G`. -/
def IsPointMeasurableInf [MeasurableSpace Ω] (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (G : Set Ω) (ψ : Ω → ℂ → ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet A → A ⊆ G → ∀ p : Ω → ℂ, Measurable p →
    (∀ ω ∈ A, p ω ∈ closure (cfPocket (R ω) (L ω) r)) → Measurable (A.indicator fun ω => ψ ω (p ω))

/-- The erased traversal at infinity on `A`, in the coordinate `ψ`. -/
def travSubInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (A : Set Ω) : A → ℝ → ℂ :=
  fun ω => cfTraversalInf (R ω) (L ω) r (η ω) (ψ ω)

end Defs

section Pocket

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {G : Set Ω}

/-- **The erased traversal at infinity of a random change pocket opening at the flow seed is measurable at each fixed
own time**, for every Jordan coordinate family at infinity measurable for `𝓦` at its `𝓦`-measurable points. -/
theorem measurable_travSubInf (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hAG : A ⊆ G) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) {u : ℝ}
    (hu : 0 ≤ u) : Measurable fun ω : A => travSubInf R L r η ψ A ω u := by
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hP : ∀ ω : A, Sec6.IsReversePocketInf (W ω) (η ω) (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r)
      (cfArcLInf (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) := fun ω =>
    (hcfg ω (hAG ω.2)).isReversePocketInf
  have hηc : ∀ ω : A, ContinuousOn (η ω) (Ici 0) := fun ω => (hcfg ω (hAG ω.2)).trace.2.1
  have hηmA : ∀ u, 0 ≤ u → Measurable fun ω : A => η ω u := fun u hu =>
    (hηm u hu).comp measurable_subtype_coe
  have hy : Measurable fun ω : A => cfArcRInf (R ω) (L ω) r 0 := by
    have h := measurable_cfArcR_sub h𝓦 hRm hLm hGm hG hAG (s := 1) ⟨zero_le_one, le_rfl⟩
    convert h using 1
    funext ω
    rw [IsChangeConfigInc.cfArcRInf_zero, IsChangeConfigInc.cfArcR_one]
  have hτ : Measurable fun ω : A => firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) := measurable_firstHit hηc hηmA hy
  have hℓ : ∀ {T : A → ℝ}, Measurable T → Measurable fun ω : A =>
      Sec6.pocketClockInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (T ω) :=
    fun hT => measurable_pocketClockInf hηc hηmA (measurable_cfPocket_sub h𝓦 hRm hLm hGm hG hAG) hτ
      (fun ω => firstHit_nonneg _ _) hT
  have hend : Measurable fun ω : A =>
      Sec6.clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) := by
    have h : Measurable fun ω : A => ⨆ n : ℕ,
        Sec6.pocketClockInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) n :=
      Measurable.iSup fun n => hℓ measurable_const
    convert h using 1
    funext ω
    exact clockEnd_eq_iSup_nat (hP ω)
  have hv : Measurable fun ω : A => clockOf (Sec6.clockEnd (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) u := hend.mul measurable_const
  have hvI : ∀ ω : A, clockOf (Sec6.clockEnd (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) u ∈
        Ico 0 (Sec6.clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) :=
    fun ω => clockOf_mem_Ico ((hP ω).clockEnd_pos (hcfg ω (hAG ω.2)).attach) hu
  have hfR : Measurable fun ω : A => Sec6.pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (clockOf (Sec6.clockEnd (η ω) (cfPocket (R ω) (L ω) r)
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) u) := by
    refine measurable_of_Ioi fun a => ?_
    rw [show (fun ω : A => Sec6.pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r)
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (clockOf (Sec6.clockEnd (η ω) (cfPocket (R ω) (L ω) r)
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) u)) ⁻¹' Ioi a =
        {ω : A | a < firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)} ∪ ⋃ q : ℚ, {ω : A | a < q ∧
          firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ q ∧
          Sec6.pocketClockInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) q ≤
            max (clockOf (Sec6.clockEnd (η ω) (cfPocket (R ω) (L ω) r)
              (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) u)
              (Sec6.pocketClockInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
                (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))} from by
      ext ω
      simp only [mem_preimage, mem_Ioi, mem_union, mem_iUnion, mem_ofPred_eq]
      exact lt_pocketFibreInf_iff (hP ω) (hvI ω)]
    refine (measurableSet_lt measurable_const hτ).union (MeasurableSet.iUnion fun q => ?_)
    exact measurableSet_setOfPred.2 (measurable_const.and
      ((measurableSet_setOfPred.1 (measurableSet_le hτ measurable_const)).and
        (measurableSet_setOfPred.1 (measurableSet_le (hℓ measurable_const) (hv.max (hℓ hτ))))))
  have hp := measurable_comp_time hηc hηmA hfR fun ω => (hP ω).fibre_nonneg (hvI ω)
  refine measurable_comp_of_fixedPts h𝓦 hRm hLm hGm hG hAG (fun z => ?_) hp
    (fun ω => (hP ω).erasedPath_mem (hvI ω))
    fun ω => ((hψ ω ω.2).1 _ ((hP ω).erasedPath_mem (hvI ω))).mono subset_closure
  exact hψm _ (measurableSet_mem_cfPocket hRm hLm hGm hG z) (fun ω hω => hω.1) (fun _ => z) measurable_const
    fun ω hω => subset_closure hω.2

end Pocket

/-! ### One measurable Jordan coordinate at infinity for the marks and the traversal -/

/-- A point `c ∈ (0, u]` is `u/(1 + v)` for some `v ≥ 0`. -/
theorem exists_div_one_add_eq {u c : ℝ} (hc : 0 < c) (hcu : c ≤ u) : ∃ v : ℝ, 0 ≤ v ∧ u / (1 + v) = c := by
  have hu : 0 < u := hc.trans_le hcu
  refine ⟨u / c - 1, ?_, ?_⟩
  · rw [sub_nonneg, le_div_iff₀ hc, one_mul]
    exact hcu
  · rw [add_sub_cancel]
    field_simp

section Random

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {G : Set Ω}

/-- **The marks (Aux. 119–121) and the traversal at infinity from one measurable Jordan coordinate at infinity**: the
analogue of `PocketWordAssembly.exists_measurable_pocketMarks_pts` for the pocket opening at the flow seed. -/
theorem exists_measurable_pocketMarksInf_pts (hRm : ∀ t, Measurable fun ω => R ω t)
    (hLm : ∀ t, Measurable fun ω => L ω t) (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hG0 : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0)
    (hor : ∀ ω ∈ G, IsFlowChartOriented (R ω) (L ω) r) (c₁ : ℝ) :
    ∃ ψ : Ω → ℂ → ℂ, (∀ ω ∈ G, IsCfJordanInf (R ω) (L ω) r (ψ ω)) ∧ IsPointMeasurableInf R L r G ψ ∧
      Measurable (G.indicator fun ω => (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re) ∧
      (∀ ω ∈ G, 0 < (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re) ∧
      Measurable ({ω | ω ∈ G ∧ c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)}.indicator
        fun ω => (ψ ω (cfPt (toDisc (realPath (R ω)) c₁))).re) ∧
      ∀ ω ∈ G, c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r) →
        (ψ ω (cfPt (toDisc (realPath (R ω)) c₁))).re < 0 := by
  classical
  obtain ⟨a, Ψ, haΨ, hmeas0⟩ := exists_measurable_cfCoord hRm hLm hGm hG
  have hJ : ∀ ω ∈ G, IsCfJordanInf (R ω) (L ω) r (cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r)) := fun ω hω =>
    (hG ω hω).isJordanCoordInf_cfCoord ((hG ω hω).openPt_eq_neg_one_iff.2 (hG0 ω hω)) (haΨ ω hω).2 (haΨ ω hω).1
  set ψ : Ω → ℂ → ℂ := fun ω => if ω ∈ G then cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r) else 0 with hψdef
  have hψG : ∀ ω ∈ G, ψ ω = cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r) := fun ω hω => by
    simp only [hψdef, hω, ↓reduceIte]
  have hpts : IsPointMeasurableInf R L r G ψ := by
    intro A hA hAG p hp hpA
    have h := hmeas0 A hA hAG p hp fun ω hω =>
      ⟨hpA ω hω, ((hJ ω (hAG hω)).1 _ (hpA ω hω)).mono subset_closure⟩
    convert h using 1
    funext ω
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, hψG ω (hAG hω)]
    · simp only [indicator_of_notMem hω]
  have hre : ∀ A : Set Ω, MeasurableSet A → A ⊆ G → ∀ p : Ω → ℂ, Measurable p →
      (∀ ω ∈ A, p ω ∈ closure (cfPocket (R ω) (L ω) r)) →
      Measurable (A.indicator fun ω => (ψ ω (p ω)).re) := fun A hA hAG p hp hpA => by
    have h := Complex.measurable_re.comp (hpts A hA hAG p hp hpA)
    convert h using 1
    funext ω
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, Function.comp_apply]
    · simp only [indicator_of_notMem hω, Function.comp_apply, Complex.zero_re]
  have hE := (measurableSet_rightLo_pos_and hRm hLm hGm hG).2 c₁
  have hmemL : ∀ ω ∈ G, cfPt (toDisc (realPath (L ω)) (discTime r)) ∈ closure (cfPocket (R ω) (L ω) r) :=
    fun ω hω => by
      have hP := (hG ω hω).isCfPocketInf (hG0 ω hω)
      have hd := (hG ω hω).changeCorners.2.2.2.2.1
      rw [(hG ω hω).leftLo_eq_zero_of_rightLo_eq_zero (hG0 ω hω)] at hd
      obtain ⟨v, hv, he⟩ := exists_div_one_add_eq hd.1 hd.2.le
      have hm : cfPt (toDisc (realPath (L ω)) (discTime r)) ∈ frontier (cfPocket (R ω) (L ω) r) := by
        rw [hP.frontier_eq]
        exact Or.inr ⟨v, hv, by simp only [cfArcLInf, he]⟩
      exact frontier_subset_closure hm
  have hmemR : ∀ ω ∈ G, c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r) →
      cfPt (toDisc (realPath (R ω)) c₁) ∈ closure (cfPocket (R ω) (L ω) r) := fun ω hω hc => by
    have hP := (hG ω hω).isCfPocketInf (hG0 ω hω)
    rw [hG0 ω hω] at hc
    obtain ⟨v, hv, he⟩ := exists_div_one_add_eq hc.1 hc.2.le
    have hm : cfPt (toDisc (realPath (R ω)) c₁) ∈ frontier (cfPocket (R ω) (L ω) r) := by
      rw [hP.frontier_eq]
      exact Or.inl ⟨v, hv, by simp only [cfArcRInf, he]⟩
    exact frontier_subset_closure hm
  have hpL : Measurable fun ω => cfPt (toDisc (realPath (L ω)) (discTime r)) :=
    measurable_cfPt.comp (measurable_toDisc_apply hLm _)
  have hpR : Measurable fun ω => cfPt (toDisc (realPath (R ω)) c₁) :=
    measurable_cfPt.comp (measurable_toDisc_apply hRm _)
  refine ⟨ψ, fun ω hω => hψG ω hω ▸ hJ ω hω, hpts, hre G hGm subset_rfl _ hpL hmemL, fun ω hω => ?_,
    hre _ hE (fun ω hω => hω.1) _ hpR (fun ω hω => hmemR ω hω.1 hω.2), fun ω hω hc => ?_⟩
  · rw [hψG ω hω]
    exact (cfCoord_sides (hG ω hω) (hor ω hω) (haΨ ω hω).2 (haΨ ω hω).1).2 _
      (hG ω hω).changeCorners.2.2.2.2.1
  · rw [hψG ω hω]
    exact (cfCoord_sides (hG ω hω) (hor ω hω) (haΨ ω hω).2 (haΨ ω hω).1).1 _ hc

end Random

/-! ### hPW from a random change pocket opening at the flow seed -/

/-- **hPW from the coupling clause on one word-shape event, pocket opening at the flow seed** (the analogue of
`PocketWordAssembly.pocketWordEvolution_of_word`, with the traversal at infinity, measurable at fixed own times by
`measurable_travSubInf`). -/
theorem pocketWordEvolution_of_wordInf.{v} {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : rL ∈ Ioo (-2) (counterflowA κ - 2)) (hR : rR ∈ Ioo (-2) (counterflowA κ - 2))
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ G, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ)
    (hxRm : Measurable[𝓦] (G.indicator fun ω => (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re))
    (hxRp : ∀ ω ∈ G, 0 < (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re)
    {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G) (hPA : 0 < P A)
    {nL : ℕ} {ρL : Fin (nL + 1) → ℝ} (hρL : ρL 0 = rL)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    {xL : A → Fin (nL + 1) → ℝ} (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] xL) (hseedL : ∀ ω, xL ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxLi : ∀ ω, Antitone (xL ω))
    (hcpl : PocketCouplingClause (16 / κ) ρL (wordR2 κ (rs136Theta2 κ rR)) (MeasurableSpace.comap Subtype.val 𝓦)
      (condSub P A) (travSubInf R L r η ψ A) xL (marksR L r ψ A)) :
    Lemma725Ref.PocketWordEvolution.{v} (16 / κ) rL rR := by
  have hAm : MeasurableSet A := h𝓦 _ hA
  have : StandardBorelSpace A := hAm.standardBorel
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hAm hPA.ne'
  obtain ⟨-, -, hρR, -, -, hsR, -, -⟩ := lemma725_word hκ hκ4 hL hR
  have hAe : counterflowA κ = 16 / κ / 2 - 2 := rfl
  have hκ' : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
  have hLd : rL < 16 / κ / 2 - 4 := by have := hL.2; rw [hAe] at this; linarith
  have hRd : rR < 16 / κ / 2 - 4 := by have := hR.2; rw [hAe] at this; linarith
  have hxRm' : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (marksR L r ψ A) :=
    @measurable_vec_two A (MeasurableSpace.comap Subtype.val 𝓦) _ (measurable_sub_of_indicator hAG hxRm)
  have hdrive : ∀ ω : A, IsDrivenCurve (travSubInf R L r η ψ A ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧
      travSubInf R L r η ψ A ω u ∈ H ∧ M < ‖travSubInf R L r η ψ A ω u‖ := fun ω =>
    (hcfg ω (hAG ω.2)).isDrivenCurve (hψ ω (hAG ω.2))
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travSubInf R L r η ψ A ω u := fun u hu =>
    measurable_travSubInf h𝓦 hRm hLm hGm hcfg hηm hAG (fun ω hω => hψ ω (hAG hω)) hψm hu
  have h𝓔 : MeasurableSpace.comap Subtype.val 𝓦 ≤ (inferInstance : MeasurableSpace A) :=
    MeasurableSpace.comap_mono h𝓦
  obtain ⟨h, hint, hcf⟩ := hcpl h𝓔 fun r n k => measurableSet_prefixEvent (fun ω => (hdrive ω).1) hγm r n k
  refine pocketWordEvolution_of_charFun_measurable hκ' hLd hRd hρL hρR hsL hsR h𝓔 (fun ω => (hdrive ω).1) hγm
    (fun ω => (hdrive ω).2) hxLm hxRm' hseedL
    (fun ω => by simp [marksR]) hxLd (fun ω j => ?_) hxLi (fun ω => monotone_vec_two (hxRp ω (hAG ω.2)).le) hint hcf
  have hj : j.succ = (1 : Fin 2) := by fin_cases j; rfl
  rw [hj]
  simpa [marksR] using hxRp ω (hAG ω.2)

/-- **The coupling inputs on every word-shape event, pocket opening at the flow seed** (packet item 1 in this case;
the analogue of `PocketWordAssembly.PocketCouplingInput` with the Jordan coordinates at infinity and the traversal at
infinity). -/
def PocketCouplingInputInf (κ rL rR : ℝ) {Ω : Type*} (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketCouplingClause (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR))
        (MeasurableSpace.comap Subtype.val 𝓦) (condSub P A) (travSubInf R L r η ψ A)
        (marksL2 R ψ A) (marksR L r ψ A)) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketCouplingClause (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR))
        (MeasurableSpace.comap Subtype.val 𝓦) (condSub P A) (travSubInf R L r η ψ A)
        (marksL1 A) (marksR L r ψ A))

/-- **hPW from a random change pocket opening at the flow seed** (Lemma 7.25's proof with Aux. 119–122 and Aux. 130's
case `x₀ = x`): as `PocketTraversalMeasRand.pocketWordEvolution_of_cfPocketConfig_meas`, with every realization in
`G` a change pocket opening at the flow seed (`IsCfPocketConfigInf`) and the coupling input at infinity. -/
theorem pocketWordEvolution_of_cfPocketConfigInf.{v} {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : rL ∈ Ioo (-2) (counterflowA κ - 2)) (hR : rR ∈ Ioo (-2) (counterflowA κ - 2))
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (hcpl : PocketCouplingInputInf κ rL rR 𝓦 P R L r η G) :
    Lemma725Ref.PocketWordEvolution.{v} (16 / κ) rL rR := by
  have hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  obtain ⟨ψ, hψ, hψm, hxRm, hxRp, hxL2m, hxL2n⟩ := exists_measurable_pocketMarksInf_pts (mΩ := 𝓦) hRm hLm hGm hconf
    (fun ω hω => (hcfg ω hω).seed) (fun ω hω => (hcfg ω hω).oriented) (discTime 1)
  obtain ⟨hρL2, hρL1, -, hsL2, hsL1, -, -, -⟩ := lemma725_word hκ hκ4 hL hR
  set E := {ω | ω ∈ G ∧ discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)} with hEdef
  have hEm : MeasurableSet[𝓦] E := (measurableSet_rightLo_pos_and (mΩ := 𝓦) hRm hLm hGm hconf).2 _
  by_cases hE : 0 < P E
  · have hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (marksL2 R ψ E) :=
      @measurable_vec_two E (MeasurableSpace.comap Subtype.val 𝓦) _ (measurable_sub_of_indicator subset_rfl hxL2m)
    refine pocketWordEvolution_of_wordInf hκ hκ4 hL hR h𝓦 hRm hLm hGm hcfg hηm hψ hψm hxRm hxRp hEm
      (fun ω hω => hω.1) hE hρL2 hsL2 hxLm (fun ω => by simp [marksL2]) (fun ω i => ?_)
      (fun ω => antitone_vec_two ?_)
      ((hcpl E hEm (fun ω hω => hω.1) hE ψ (fun ω hω => hψ ω hω.1) hψm).1 fun ω hω => hω.2)
    · have hi : i.succ = (1 : Fin 2) := by fin_cases i; rfl
      rw [hi]
      simpa [marksL2] using hxL2n ω ω.2.1 ω.2.2
    · exact (hxL2n ω ω.2.1 ω.2.2).le
  · have hPE : P E = 0 := le_antisymm (not_lt.1 hE) zero_le
    have hPA : 0 < P (G \ E) := by
      have h1 : P G ≤ P (G ∩ E) + P (G \ E) := measure_le_inter_add_sdiff P G E
      have h2 : P (G ∩ E) = 0 := measure_mono_null inter_subset_right hPE
      rw [h2, zero_add] at h1
      exact lt_of_lt_of_le hPG h1
    exact pocketWordEvolution_of_wordInf hκ hκ4 hL hR h𝓦 hRm hLm hGm hcfg hηm hψ hψm hxRm hxRp (hGm.diff hEm)
      sdiff_subset hPA hρL1 hsL1 measurable_const (fun ω => rfl) (fun ω i => i.elim0) (fun ω => antitone_vec_one)
      ((hcpl (G \ E) (hGm.diff hEm) sdiff_subset hPA ψ (fun ω hω => hψ ω hω.1) hψm).2
        fun ω hω hc => hω.2 ⟨hω.1, hc⟩)

/-! ### hPW from a random change pocket of either kind -/

/-- **hPW from a random change pocket of either kind** (Lemma 7.25's proof with Aux. lemma 130, both cases
`x₀ ≠ x` and `x₀ = x`): on a standard Borel probability space, let the walls be measurable for `𝓦 ≤ mΩ` at every
time, and let `G ∈ 𝓦` have positive probability, with every realization in `G` a change configuration that is a
bounded change pocket traversed by the counterflow when `0 < rightLo` (`IsCfPocketConfig`) and a pocket opening at the
flow seed traversed by the counterflow when `rightLo = 0` (`IsCfPocketConfigInf`). Given the fixed-time measurability
of the counterflow and the coupling inputs of both cases, the pocket word evolution exists at `κ′ = 16/κ`. -/
theorem pocketWordEvolution_of_changeConfig.{v} {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : rL ∈ Ioo (-2) (counterflowA κ - 2)) (hR : rR ∈ Ioo (-2) (counterflowA κ - 2))
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r → IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 → IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (hcpl : PocketCouplingInput κ rL rR 𝓦 P R L r η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r})
    (hcplI : PocketCouplingInputInf κ rL rR 𝓦 P R L r η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r}) :
    Lemma725Ref.PocketWordEvolution.{v} (16 / κ) rL rR := by
  set Gp := {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} with hGpdef
  have hGpm : MeasurableSet[𝓦] Gp := (measurableSet_rightLo_pos_and (mΩ := 𝓦) hRm hLm hGm hconf).1
  have hG0 : {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} = G \ Gp := by
    ext ω
    simp only [hGpdef, mem_ofPred_eq, Set.mem_sdiff, not_and]
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
  have hseed : ∀ ω ∈ G \ Gp, rightLo (R ω) (L ω) r = 0 := fun ω hω =>
    le_antisymm (not_lt.1 fun h => hω.2 ⟨hω.1, h⟩) ((hconf ω hω.1).changeCorner_props.1.1)
  by_cases hp : 0 < P Gp
  · exact pocketWordEvolution_of_cfPocketConfig_meas hκ hκ4 hL hR h𝓦 hRm hLm hGpm hp
      (fun ω hω => hcfg ω hω.1 hω.2) hηm hcpl
  · have hPA : 0 < P (G \ Gp) := by
      have h1 : P G ≤ P (G ∩ Gp) + P (G \ Gp) := measure_le_inter_add_sdiff P G Gp
      have h2 : P (G ∩ Gp) = 0 := measure_mono_null inter_subset_right (le_antisymm (not_lt.1 hp) zero_le)
      rw [h2, zero_add] at h1
      exact lt_of_lt_of_le hPG h1
    rw [hG0] at hcplI
    exact pocketWordEvolution_of_cfPocketConfigInf hκ hκ4 hL hR h𝓦 hRm hLm (hGm.diff hGpm) hPA
      (fun ω hω => hcfgI ω hω.1 (hseed ω hω)) hηm hcplI

/-- **hPW from a random change pocket of either kind, in the form the Theorem 1.3 wiring consumes** (`κ′ > 4`,
both-low seed weights). -/
theorem pocketWordEvolution_of_changeConfig'.{v} {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hR : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r → IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 → IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (hcpl : PocketCouplingInput (16 / κ') rL rR 𝓦 P R L r η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r})
    (hcplI : PocketCouplingInputInf (16 / κ') rL rR 𝓦 P R L r η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r}) :
    Lemma725Ref.PocketWordEvolution.{v} κ' rL rR := by
  have hκ0 : 0 < κ' := by linarith
  have hκ : 0 < 16 / κ' := by positivity
  have hκ4 : 16 / κ' < 4 := by rw [div_lt_iff₀ hκ0]; linarith
  have hinv : 16 / (16 / κ') = κ' := by field_simp
  have hA : counterflowA (16 / κ') - 2 = κ' / 2 - 4 := by
    show 16 / (16 / κ') / 2 - 2 - 2 = κ' / 2 - 4
    rw [hinv]; ring
  have h := pocketWordEvolution_of_changeConfig hκ hκ4 ⟨hL, by rw [hA]; exact hLd⟩ ⟨hR, by rw [hA]; exact hRd⟩
    h𝓦 hRm hLm hGm hPG hconf hcfg hcfgI hηm hcpl hcplI
  rwa [hinv] at h

end InteractingSLE.Sec7.PocketSeedOpen
