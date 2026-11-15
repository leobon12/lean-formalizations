/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7StopInWire
import InteractingSLE.Spec.Sec7.R7Aux131Word

/-!
# Theorem R.7's outer pockets: one realization, the traversal's measurability and the measurable erasure

Packet PROVE-HOUTER. Supplement §5.4 (`source/spec/p433-480.md` L974–L997, pp. 473–474) and the proof of Theorem R.7
(L1058–L1068): for a mixed or outer pocket `C` (an outer incoming arm, never reverse-visited off its certified
frontier), the landed Aux. lemmas 39–41 (`Sec6.IsReversePocket`) do not apply; PROVE-R7-STOPIN isolated the erasure
facts (`R7StopIn.IsErasurePocket`, `R7StopIn.IsErasurePocketInf`) and the relative Loewner conclusion
(`R7StopIn.RelLoewner`), from which the erased relative traversal `cfTraversal` is a driven curve.

This file packages one realization of such a pocket (`IsOuterCfg`, `IsOuterCfgInf`: the change configuration, its
flow-chart orientation, the counterflow's Loewner trace, the erasure facts and the relative Loewner conclusion for
every Jordan coordinate) and proves the measurability facts the stop-level statement needs, for the erasure in place
of the reverse pocket:

* `IsOuterCfg.props`, `IsOuterCfgInf.props`: the traversal is driven, has points of `ℍ` of large modulus, tends to
  `∞`, and satisfies `GoodR7` with infinite capacity lifetime (STOPIN's `cfTraversal(Inf)_props_of_erasure`);
* **`measurable_travAll_outer`**, **`measurable_travAllInf_outer`**: the traversal is measurable at each fixed own
  time on every measurable subset of the configuration event (PROVE-STRIPSYS23's proof
  `PocketTraversalMeasRand.traversalMeasStatement_of_measurable` / `PocketSeedOpen.measurable_travSubInf`, whose only
  pocket inputs are clock facts that the erasure pocket also has);
* **`pocketErasure_outer`**, **`pocketErasure_outerInf`**: the measurable pocket erasure (`PocketErasure`, Aux. lemma
  125's proof) through `Lemma725RefChart.pocketErasure_of_driven`.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function
open QuantumZipper (H Hbar)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.HOuter

open WangWu Lemma71I Lemma71C PocketCoord PocketJordan PocketMarks PocketTraversal PocketWordAssembly PocketSeedOpen
  PocketCoupling R7StopIn PocketTraversalMeasRand Lemma725RefChart R7Aux131

/-! ### One realization of a mixed or outer pocket -/

/-- **One realization of a bounded mixed or outer change pocket traversed by the counterflow** (supplement §5.4): the
change configuration with `0 < rightLo`, its flow-chart orientation (Aux. 119), the counterflow driver `W` and trace
`η` in the chart `m(z) = −1/z`, the erasure facts of the pocket between the first visits of `m(y₀)` and `m(x₀)`
(Consequence R.4, no terminal gap, equal gap endpoints) and the relative Loewner conclusion in every Jordan
coordinate (§5.4: "The same Loewner criterion used in Aux. 41 now gives a continuous relative driver"). -/
structure IsOuterCfg (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (W : ℝ → ℝ) (η : ℝ → ℂ) : Prop where
  conf : IsChangeConfigInc R L r
  bounded : 0 < rightLo R L r
  oriented : IsFlowChartOriented R L r
  trace : IsLoewnerTrace W η
  continuous_W : Continuous W
  W_zero : W 0 = 0
  erase : IsErasurePocket η (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) (firstHit η (cfArcR R L r 1))
    (firstHit η (cfArcR R L r 0))
  loewner : ∀ ψ : ℂ → ℂ, IsCfJordan R L r ψ →
    RelLoewner (fun v => ψ (Sec6.erasedPath η (cfPocket R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) v))
      (Sec6.pocketClock η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))
        (firstHit η (cfArcR R L r 0)))

/-- **One realization of a mixed or outer change pocket opening at the flow seed traversed by the counterflow**: as
`IsOuterCfg` with `rightLo = 0`, a transient counterflow, and the erasure at infinity after the first visit of
`m(y₀)`. -/
structure IsOuterCfgInf (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (W : ℝ → ℝ) (η : ℝ → ℂ) : Prop where
  conf : IsChangeConfigInc R L r
  seed : rightLo R L r = 0
  oriented : IsFlowChartOriented R L r
  trace : IsLoewnerTrace W η
  continuous_W : Continuous W
  W_zero : W 0 = 0
  transient : Tendsto (fun t => ‖η t‖) atTop atTop
  erase : IsErasurePocketInf η (cfPocket R L r) (cfArcRInf R L r 0) (firstHit η (cfArcRInf R L r 0))
  loewner : ∀ ψ : ℂ → ℂ, IsCfJordanInf R L r ψ →
    RelLoewner (fun v => ψ (Sec6.erasedPathInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)) v))
      (Sec6.clockEnd η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)))

/-- **The relative traversal of one realization** (bounded): driven, with points of `ℍ` of arbitrarily large modulus,
tending to `∞`, and `GoodR7` with infinite capacity lifetime. -/
theorem IsOuterCfg.props {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ} (hc : IsOuterCfg R L r W η)
    {ψ : ℂ → ℂ} (hψ : IsCfJordan R L r ψ) :
    IsDrivenCurve (cfTraversal R L r η ψ) ∧
      (∀ M : ℝ, ∃ u, 0 ≤ u ∧ cfTraversal R L r η ψ u ∈ H ∧ M < ‖cfTraversal R L r η ψ u‖) ∧
      Tendsto (fun u => ‖cfTraversal R L r η ψ u‖) atTop atTop ∧
      (capLife (cfTraversal R L r η ψ) = ⊤ → GoodR7 (fun t => segDriver (cfTraversal R L r η ψ) t) ⊤) :=
  cfTraversal_props_of_erasure hc.erase hψ (hc.loewner ψ hψ)

/-- **The relative traversal of one realization** (opening at the flow seed). -/
theorem IsOuterCfgInf.props {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ} (hc : IsOuterCfgInf R L r W η)
    {ψ : ℂ → ℂ} (hψ : IsCfJordanInf R L r ψ) :
    IsDrivenCurve (cfTraversalInf R L r η ψ) ∧
      (∀ M : ℝ, ∃ u, 0 ≤ u ∧ cfTraversalInf R L r η ψ u ∈ H ∧ M < ‖cfTraversalInf R L r η ψ u‖) ∧
      Tendsto (fun u => ‖cfTraversalInf R L r η ψ u‖) atTop atTop ∧
      (capLife (cfTraversalInf R L r η ψ) = ⊤ → GoodR7 (fun t => segDriver (cfTraversalInf R L r η ψ) t) ⊤) :=
  cfTraversalInf_props_of_erasure hc.erase hψ hc.transient (hc.loewner ψ hψ)

/-! ### The clock at infinity of an erasure pocket -/

section ClockInf

variable {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ}

/-- The terminal clock value at infinity is the supremum over integer times (erasure form of
`PocketSeedOpen.clockEnd_eq_iSup_nat`). -/
theorem clockEnd_eq_iSup_nat' (hP : IsErasurePocketInf η C y₀ τ) :
    Sec6.clockEnd η C τ = ⨆ n : ℕ, Sec6.pocketClockInf η C τ n := by
  have hb := hP.bddAbove_clock
  have hbn : BddAbove (range fun n : ℕ => Sec6.pocketClockInf η C τ n) :=
    hb.mono (range_subset_iff.2 fun n => mem_range_self _)
  refine le_antisymm (ciSup_le fun t => ?_) (ciSup_le fun n => le_ciSup hb _)
  exact (hP.monotone_clock (Nat.le_ceil t)).trans (le_ciSup hbn ⌈t⌉₊)

/-- **The right end of a fibre below the terminal clock value exceeds `a`** iff `a < τ` or some rational `q ≥ τ`,
`q > a`, has clock at most `v ∨ ℓ τ` (erasure form of `PocketSeedOpen.lt_pocketFibreInf_iff`). -/
theorem lt_pocketFibreInf_iff' (hP : IsErasurePocketInf η C y₀ τ) {v a : ℝ}
    (hv : v ∈ Ico 0 (Sec6.clockEnd η C τ)) :
    a < Sec6.pocketFibreInf η C τ v ↔
      a < τ ∨ ∃ q : ℚ, a < q ∧ τ ≤ q ∧ Sec6.pocketClockInf η C τ q ≤ max v (Sec6.pocketClockInf η C τ τ) := by
  obtain ⟨T, hτT, hvT⟩ := hP.exists_clock_gt hv.2
  rw [hP.fibre_eq_fibreRight_of_lt hv.1 hvT, lt_fibreRight_iff hP.continuous_clock hP.monotone_clock hτT]
  refine or_congr_right ⟨fun ⟨q, h1, h2, _, h4⟩ => ⟨q, h1, h2, h4⟩, fun ⟨q, h1, h2, h4⟩ => ⟨q, h1, h2, ?_, h4⟩⟩
  by_contra hqT
  push Not at hqT
  have h5 := (hP.monotone_clock hqT.le).trans h4
  rw [IsErasurePocketInf.clock_τ, max_eq_left hv.1] at h5
  exact absurd hvT (not_lt.2 h5)

end ClockInf

/-! ### The traversal is measurable at each fixed own time -/

section Meas

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {G : Set Ω}

/-- **The erased traversal of a random bounded outer pocket is measurable at each fixed own time**
(`PocketTraversalMeasRand.traversalMeasStatement_of_measurable` with the erasure pocket in place of the reverse
pocket): for walls measurable for `𝓦 ≤ mΩ`, a `𝓦`-measurable configuration event `G`, a counterflow measurable at
fixed times and a Jordan coordinate family measurable for `𝓦` at its `𝓦`-measurable points. -/
theorem measurable_travAll_outer (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hAG : A ⊆ G) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) {u : ℝ}
    (hu : 0 ≤ u) : Measurable fun ω : A => travAll R L r η ψ ω u := by
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hP : ∀ ω : A, IsErasurePocket (η ω) (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0)
      (cfArcR (R ω) (L ω) r 1) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) := fun ω => (hcfg ω (hAG ω.2)).erase
  have hηc : ∀ ω : A, ContinuousOn (η ω) (Ici 0) := fun ω => (hP ω).cont
  have hηmA : ∀ u, 0 ≤ u → Measurable fun ω : A => η ω u := fun u hu =>
    (hηm u hu).comp measurable_subtype_coe
  -- the first visits of `m(y₀)` and `m(x₀)`
  have hτ : Measurable fun ω : A => firstHit (η ω) (cfArcR (R ω) (L ω) r 1) :=
    measurable_firstHit hηc hηmA (measurable_cfArcR_sub h𝓦 hRm hLm hGm hG hAG ⟨zero_le_one, le_rfl⟩)
  have hσ : Measurable fun ω : A => firstHit (η ω) (cfArcR (R ω) (L ω) r 0) :=
    measurable_firstHit hηc hηmA (measurable_cfArcR_sub h𝓦 hRm hLm hGm hG hAG ⟨le_rfl, zero_le_one⟩)
  -- the clock, the fibre and the erased point
  have hℓ : ∀ {T : A → ℝ}, Measurable T → Measurable fun ω : A =>
      Sec6.pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (T ω) := fun hT =>
    measurable_pocketClock hηc hηmA (measurable_cfPocket_sub h𝓦 hRm hLm hGm hG hAG) hτ hσ
      (fun ω => firstHit_nonneg _ _) hT
  have hv : Measurable fun ω : A => clockOf (Sec6.pocketClock (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))) u :=
    (hℓ hσ).mul measurable_const
  have hfR := measurable_fibreRight (fun ω => (hP ω).continuous_clock) (fun ω => (hP ω).monotone_clock)
    (fun q => hℓ measurable_const) hτ hσ hv (hℓ hτ) (fun ω => (hP ω).lt.le)
  have hp := measurable_comp_time hηc hηmA hfR fun ω => (hP ω).nonneg.trans ((hP ω).fibre_mem _).1
  refine measurable_comp_of_isPointMeasurable h𝓦 hRm hLm hGm hG hAG (fun ω hω => (hψ ω hω).1) hψm hp
    fun ω => ?_
  have hm := (hP ω).erasedPath_mem (clockOf_mem_Ico (hP ω).clock_σ_pos hu)
  exact ⟨hm.1, fun h => hm.2 (mem_singleton_iff.2
    ((mem_singleton_iff.1 h).trans IsChangeConfigInc.cfArcR_zero.symm))⟩

/-- **The erased traversal of a random outer pocket opening at the flow seed is measurable at each fixed own time**
(`PocketSeedOpen.measurable_travSubInf` with the erasure pocket at infinity in place of the reverse pocket). -/
theorem measurable_travAllInf_outer (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hAG : A ⊆ G) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) {u : ℝ}
    (hu : 0 ≤ u) : Measurable fun ω : A => travAllInf R L r η ψ ω u := by
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hP : ∀ ω : A, IsErasurePocketInf (η ω) (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) := fun ω => (hcfg ω (hAG ω.2)).erase
  have hηc : ∀ ω : A, ContinuousOn (η ω) (Ici 0) := fun ω => (hP ω).cont
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
    exact clockEnd_eq_iSup_nat' (hP ω)
  have hv : Measurable fun ω : A => clockOf (Sec6.clockEnd (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) u := hend.mul measurable_const
  have hvI : ∀ ω : A, clockOf (Sec6.clockEnd (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) u ∈
        Ico 0 (Sec6.clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) :=
    fun ω => clockOf_mem_Ico (hP ω).clockEnd_pos hu
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
      exact lt_pocketFibreInf_iff' (hP ω) (hvI ω)]
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

end Meas

/-! ### The measurable pocket erasure -/

section Erase

universe u

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The measurable pocket erasure for a bounded outer pocket** (`Lemma725RefChart.pocketErasure_of_driven` with
`measurable_travAll_outer` for the σ-algebra `𝓦 ∨ σ(η|_ℚ)`; the proof of `Lemma725RefChart.pocketErasure_cfPocket`). -/
theorem pocketErasure_outer [IsProbabilityMeasure P] {nL nR : ℕ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ}
    {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsOuterCfg (R ω) (L ω) r (W ω) (η ω)) (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xL ω))
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xR ω))
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    PocketErasure 𝓦 P A (travAll R L r η ψ) xL xR η := by
  have hηm' : ∀ u, 0 ≤ u → Measurable[wallsRatSigma 𝓦 η] fun ω => η ω u := fun u hu =>
    (measurable_apply_of_rat hηc (fun q => (measurable_pi_apply q).comp (comap_measurable _)) hu).mono
      le_sup_right le_rfl
  have hγm : ∀ u, 0 ≤ u → Measurable[MeasurableSpace.comap Subtype.val (wallsRatSigma 𝓦 η)]
      fun ω : A => travAll R L r η ψ ω u := fun u hu =>
    measurable_travAll_outer (mΩ := wallsRatSigma 𝓦 η) (le_sup_left : 𝓦 ≤ wallsRatSigma 𝓦 η) hRm hLm hGm hcfg
      hηm' hAG hψ hψm hu
  exact pocketErasure_of_driven h𝓦 hA hηm (fun ω hω => ((hcfg ω (hAG hω)).props (hψ ω hω)).1) hγm
    hxLm hxRm hE₀ hgen

/-- **The measurable pocket erasure for an outer pocket opening at the flow seed.** -/
theorem pocketErasure_outerInf [IsProbabilityMeasure P] {nL nR : ℕ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ}
    {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xL ω))
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xR ω))
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    PocketErasure 𝓦 P A (travAllInf R L r η ψ) xL xR η := by
  have hηm' : ∀ u, 0 ≤ u → Measurable[wallsRatSigma 𝓦 η] fun ω => η ω u := fun u hu =>
    (measurable_apply_of_rat hηc (fun q => (measurable_pi_apply q).comp (comap_measurable _)) hu).mono
      le_sup_right le_rfl
  have hγm : ∀ u, 0 ≤ u → Measurable[MeasurableSpace.comap Subtype.val (wallsRatSigma 𝓦 η)]
      fun ω : A => travAllInf R L r η ψ ω u := fun u hu =>
    measurable_travAllInf_outer (mΩ := wallsRatSigma 𝓦 η) (le_sup_left : 𝓦 ≤ wallsRatSigma 𝓦 η) hRm hLm hGm
      hcfg hηm' hAG hψ hψm hu
  exact pocketErasure_of_driven h𝓦 hA hηm (fun ω hω => ((hcfg ω (hAG hω)).props (hψ ω hω)).1) hγm
    hxLm hxRm hE₀ hgen

end Erase

end InteractingSLE.Sec7.HOuter
