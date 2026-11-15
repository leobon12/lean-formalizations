/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Iface
import InteractingSLE.Spec.Supplement.GW2SdePrefix
import InteractingSLE.Spec.Supplement.GW2RdRootLink
import InteractingSLE.Spec.Supplement.GW2BfSlow
import InteractingSLE.Spec.Supplement.GW2SdgRead

/-!
# J32's stage start is a functional of the retained history

Packet PROVE-GW2-BUF (ruling R110: the buffer property for `RootJ32.constructionFamily`). J32's sample read at
`q = 0` is the stage start `(−1)^{|l|} 2^{r.2} (D(F_T) − D(F_{v₀}))`, where
* `D` is J32's capacity driver reader of the future pair (the running-maximum clock);
* `F_t` is the joint-chart capacity at physical time `t`;
* `T = historyTime c r l` and `v₀` is the root's initial time.

At a live sample, J32's reader at capacities up to `F_T` is J31's exact-horizon reader at horizon `T`
(`RootJ32.capacityDriverRead_eq_of_clock` at `w = T`, with the strict clock of `Gm.ae_live_clock`). That reader
sees the future joined driver only on `[0, T]`, where it is the HISTORY's joined driver
(`GW2Sde.joinedRead_future_eq_history`). So the start equals a functional of the counterflow record and the history's
joined driver, which is `c.sigma r l`-measurable.

* `histJoined`, `histPair`, `histCap`, `histStart`: the history's joined driver, its pair recorded up to `T`, the
  capacity reader and the start functional;
* `recOf_top_congr`: a record with infinite lifetime at a deterministic horizon reads the driver only up to it;
* **`measurable_histStart`**: `Measurable[c.sigma r l] (histStart c r l)`;
* `j32Read`, `j32Start`: J32's reader of the future pair and its stage start;
* **`ae_j32Start_eq_histStart`**: for a time-ordered history (deterministic in `l`), almost surely at every live
  sample of every candidate, `j32Start = histStart`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bf

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### The history functional -/

/-- The history's joined driver. -/
def histJoined (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) :
    ℝ≥0 → ℝ :=
  RootJ31.joinedRead (RootJ31.historyProgram c r l)
    (RootJ31.programRecords c (rootPt r.1) (RootJ31.historyProgram c r l) ω)

/-- The history pair: the counterflow record and the history's joined driver recorded up to `T`. -/
def histPair (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) :
    RecData × RecData :=
  (cfRec c.s c.W c.ζ ω,
    recOf ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) (histJoined c r l ω, ⊤))

/-- The joint-chart capacity of the history pair at physical time `t`, as a level. -/
def histCap (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (t : ℝ≥0) (ω : Ω) :
    ℝ≥0 :=
  (RootH29.forwardCapacity (rootPt r.1) c.s t (histPair c r l ω)).toNNReal

/-- **The history start functional**: J31's exact-horizon reader at horizon `T` of the history pair. -/
def histStart (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) : ℝ :=
  (-1) ^ l.length * (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) *
    (RootJ31.capacityDriverRead (rootPt r.1) c.s (RootJ31.historyTime c r l)
        (histCap c r l (RootJ31.historyTime c r l) ω) (histPair c r l ω) -
      RootJ31.capacityDriverRead (rootPt r.1) c.s (RootJ31.historyTime c r l)
        (histCap c r l (rootEntry r.1).2 ω) (histPair c r l ω))

/-- A record with infinite lifetime at a deterministic horizon reads the driver only up to the horizon. -/
theorem recOf_top_congr {T : ℝ≥0} {W W' : ℝ≥0 → ℝ} (h : ∀ t ≤ T, W t = W' t) :
    recOf (T : ℝ≥0∞) (W, ⊤) = recOf (T : ℝ≥0∞) (W', ⊤) := by
  unfold recOf retOf
  congr 2
  funext q
  refine h _ ?_
  change (min (q : ℝ≥0∞) (min (T : ℝ≥0∞) ⊤)).toNNReal ≤ T
  rw [min_top_right, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
  exact min_le_right _ _

theorem continuous_histJoined (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (ω : Ω) : Continuous (histJoined c r l ω) ∧ histJoined c r l ω 0 = 0 :=
  RootJ31.continuous_joinedRead _ _

/-- **The history pair is a retained functional.** -/
theorem measurable_histPair (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    Measurable[c.sigma r l] (histPair c r l) := by
  have hJ : Measurable[c.sigma r l] fun ω => ((histJoined c r l ω, (⊤ : ℝ≥0∞)) : (ℝ≥0 → ℝ) × ℝ≥0∞) := by
    refine Measurable.prodMk ((@measurable_pi_iff Ω ℝ≥0 (fun _ => ℝ) (c.sigma r l) _ _).2 fun t => ?_)
      measurable_const
    exact GW2Sde.measurable_joinedRead_history_sigma c r l t
  refine (GW2Rd.measurable_cfRec_sigma c r l).prodMk ?_
  exact @measurable_recOf Ω (c.sigma r l) _ hJ
    (fun ω => Gm.isRegularDriver_top (continuous_histJoined c r l ω).1 (continuous_histJoined c r l ω).2) _

/-- **The history start functional is a retained functional.** -/
theorem measurable_histStart (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    Measurable[c.sigma r l] (histStart c r l) := by
  have hp := measurable_histPair c r l
  have hcap : ∀ t : ℝ≥0, Measurable[c.sigma r l] (histCap c r l t) := fun t =>
    (@RootH29.measurable_forwardCapacity_random Ω (c.sigma r l) (rootPt r.1) c.s _ hp _
      measurable_const).real_toNNReal
  have hD : ∀ t : ℝ≥0, Measurable[c.sigma r l] fun ω =>
      RootJ31.capacityDriverRead (rootPt r.1) c.s (RootJ31.historyTime c r l) (histCap c r l t ω)
        (histPair c r l ω) := fun t =>
    @RootJ31.measurable_capacityDriverRead_random Ω (c.sigma r l) _ hp _ (hcap t) _ _ _
  exact measurable_const.mul ((hD _).sub (hD _))

/-! ### J32's stage start -/

/-- J32's capacity driver reader of the future pair. -/
def j32Read (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (u : ℝ≥0)
    (ξ : Ω) : ℝ :=
  RootJ32.capacityDriverRead (rootPt r.1) c.s (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) u
    (RootJ31.futurePair c r l a ξ)

/-- **J32's stage start** `(−1)^{|l|} 2^{r.2} (D(F_T) − D(F_{v₀}))`. -/
def j32Start (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ξ : Ω) : ℝ :=
  (-1) ^ l.length * (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) *
    (j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ) ξ -
      j32Read c r l a (GW2Sdg.rootCapAt c r l a (rootEntry r.1).2 ξ).toNNReal ξ)

/-- The future joined driver is the history's on `[0, T]`. -/
theorem futureJoined_eq_histJoined (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (ω : Ω) {t : ℝ≥0} (ht : t ≤ RootJ31.historyTime c r l) :
    Gm.futureJoined c r l a ω t = histJoined c r l ω t := by
  rw [GW2Sde.historyTime_eq_lastTime] at ht
  exact GW2Sde.joinedRead_future_eq_history c r l a ω ht

/-- The future pair's capacity before `T` is the history pair's. -/
theorem forwardCapacity_future_eq_hist (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) {t : ℝ≥0} (ht : t ≤ RootJ31.historyTime c r l) :
    RootH29.forwardCapacity (rootPt r.1) c.s t (RootJ31.futurePair c r l a ω) =
      RootH29.forwardCapacity (rootPt r.1) c.s t (histPair c r l ω) := by
  obtain ⟨hJ, hJ0⟩ := Gm.continuous_futureJoined c r l a ω
  obtain ⟨hJh, hJh0⟩ := continuous_histJoined c r l ω
  rw [Gm.futurePair_eq_recOfDriver]
  refine Gm.forwardCapacity_congr _ _ t _ fun y hy => ?_
  have hy0 : 0 ≤ y := hy.1
  have hyt : y.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hy.2
  have hyT : y.toNNReal ≤ RootJ31.historyTime c r l := hyt.trans ht
  have hyL : y.toNNReal ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a := hyT.trans le_self_add
  have e1 := Gm.rdrv_recOfDriver hJ hJ0
    (q₀ := RootJ31.historyTime c r l + RootJ31.candidateCap c r a) y.toNNReal
  have e2 := Gm.rdrv_recOfDriver hJh hJh0 (q₀ := RootJ31.historyTime c r l) y.toNNReal
  rw [Real.coe_toNNReal _ hy0] at e1 e2
  change rdrv _ y = rdrv (recOf ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) (histJoined c r l ω, ⊤)) y
  rw [e1, ← Gm.recOfDriver_eq_recOf, e2, min_eq_left hyL, min_eq_left hyT]
  exact futureJoined_eq_histJoined c r l a ω hyT

/-- **J32's reader below the history's capacity is the history functional's reader**, at a live sample. -/
theorem j32Read_eq_hist_of_live (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (ξ : Ω) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace (Gm.futureJoined c r l a ξ) ⊤ γ)
    (hm : MonotoneOn (fun t => RootH29.forwardCapacity (rootPt r.1) c.s t (RootJ31.futurePair c r l a ξ))
      (Icc 0 (RootJ31.historyTime c r l)))
    (hc : ContinuousOn (fun t => RootH29.forwardCapacity (rootPt r.1) c.s t (RootJ31.futurePair c r l a ξ))
      (Icc 0 (RootJ31.historyTime c r l)))
    {c' : ℝ≥0} (hc' : (c' : ℝ) ≤ RootH29.forwardCapacity (rootPt r.1) c.s (RootJ31.historyTime c r l)
      (RootJ31.futurePair c r l a ξ)) :
    j32Read c r l a c' ξ =
      RootJ31.capacityDriverRead (rootPt r.1) c.s (RootJ31.historyTime c r l) c' (histPair c r l ξ) := by
  obtain ⟨hJ, hJ0⟩ := Gm.continuous_futureJoined c r l a ξ
  have hTv : RootJ31.historyTime c r l ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a := le_self_add
  have hpe := Gm.futurePair_eq_recOfDriver c r l a ξ
  rw [hpe] at hm hc hc'
  have he := RootJ32.capacityDriverRead_eq_of_clock hJ hJ0 hγ hTv hTv hm hc hc'
  unfold j32Read
  rw [hpe, he]
  unfold histPair
  rw [recOf_top_congr fun t ht => futureJoined_eq_histJoined c r l a ξ ht]

/-- **J32's stage start is the history functional** at every live sample of every candidate, almost surely, for a
history whose root time is not after its end (deterministic in `l`; true for time-ordered histories). -/
theorem ae_j32Start_eq_histStart [StandardBorelSpace Ω] (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (hv₀ : (rootEntry r.1).2 ≤ RootJ31.historyTime c r l) :
    ∀ᵐ ξ ∂c.P, ∀ a, 0 < (RootJ31.sourceSample c r l a ξ).1 → j32Start c r l a ξ = histStart c r l ξ := by
  filter_upwards [Gm.ae_live_clock h13 c r] with ξ hξ a hlive
  obtain ⟨γ, hγ, -, hm, hc, -, -⟩ := hξ l a hlive
  have hsub : Icc 0 (RootJ31.historyTime c r l) ⊆
      Icc 0 (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ) := Icc_subset_Icc le_rfl le_self_add
  have hm' : MonotoneOn (fun t => RootH29.forwardCapacity (rootPt r.1) c.s t (RootJ31.futurePair c r l a ξ))
      (Icc 0 (RootJ31.historyTime c r l)) := hm.monotoneOn.mono hsub
  have hc'' : ContinuousOn (fun t => RootH29.forwardCapacity (rootPt r.1) c.s t (RootJ31.futurePair c r l a ξ))
      (Icc 0 (RootJ31.historyTime c r l)) := hc.mono hsub
  have hT : ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ) ≤
      RootH29.forwardCapacity (rootPt r.1) c.s (RootJ31.historyTime c r l) (RootJ31.futurePair c r l a ξ) :=
    le_of_eq (Real.coe_toNNReal _ (RootJ32.forwardCapacity_nonneg _ _ _ _))
  have h0 : (((GW2Sdg.rootCapAt c r l a (rootEntry r.1).2 ξ).toNNReal : ℝ≥0) : ℝ) ≤
      RootH29.forwardCapacity (rootPt r.1) c.s (RootJ31.historyTime c r l) (RootJ31.futurePair c r l a ξ) := by
    unfold GW2Sdg.rootCapAt
    rw [Real.coe_toNNReal _ (RootJ32.forwardCapacity_nonneg _ _ _ _)]
    exact hm' ⟨zero_le, hv₀⟩ ⟨zero_le, le_rfl⟩ hv₀
  have eT : GW2Sdg.rootHistCap c r l a ξ = histCap c r l (RootJ31.historyTime c r l) ξ := by
    unfold GW2Sdg.rootHistCap GW2Sdg.rootCapAt histCap
    rw [forwardCapacity_future_eq_hist c r l a ξ le_rfl]
  have e0 : (GW2Sdg.rootCapAt c r l a (rootEntry r.1).2 ξ).toNNReal = histCap c r l (rootEntry r.1).2 ξ := by
    unfold GW2Sdg.rootCapAt histCap
    rw [forwardCapacity_future_eq_hist c r l a ξ hv₀]
  unfold j32Start histStart
  rw [j32Read_eq_hist_of_live c r l a ξ hγ hm' hc'' hT, j32Read_eq_hist_of_live c r l a ξ hγ hm' hc'' h0, eT, e0]

end InteractingSLE.Theorem14.GW2Bf
