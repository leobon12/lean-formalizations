/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BfDrv
import InteractingSLE.Spec.Supplement.GW2BfJ32Slow

/-!
# S1 for J32: the stage driver identification from the instance's re-centred hulls

Packet PROVE-GW2-BUF (S1; rulings R110, R113, R114). On a live sample, J32's capacity driver reader of the future
pair, below the capacity reached at the buffer `v = T + F`, is J31's exact-horizon reader of the joined trace
(`RootJ32.ae_capacityDriverRead_eq`). That reader is every driver of the re-centred forward hulls
(`GW2Bf.capacityDriverRead_eq_of_hull`). So J32's reads ARE the stage instance's relative driver once that driver has
the re-centred hull identity of ruling R113. This is the content of the instance's GB6 version in the re-centred
chart, for a cap at or beyond the buffer, which R114's first-contact cap gives.

* `exactPair`: the exact-horizon pair `(cfRec, recOf (T + F) (futureJoined, ⊤))` of a candidate;
* `forwardCapacity_future_eq_exact`: below `T + F` its capacities are the future pair's;
* **`ae_j32Read_eq_of_hull`**: almost surely, at every live sample, for EVERY continuous driver `R` from `0` with the
  re-centred hull identity on `[0, T + F]`, J32's read is `R` at every capacity below `A(T + F)`;
* **`j32DriverId_of_hull`**: `J32DriverId` from the instance's hull identity and the stage relation (the stage driver
  is the increment of the instance's relative driver after the history's capacity).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Bf

open Exist Staged StagedLaw Restart GW2Sde GW2TipSystem GW2TipSystem.RootC24 Supp8.GB6

section Pair

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The exact-horizon pair** of a candidate: the counterflow record and the joined future driver recorded at the
buffer time `T + F`. -/
def exactPair (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ξ : Ω) :
    RecData × RecData :=
  (cfRec c.s c.W c.ζ ξ,
    recOf ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ : ℝ≥0) : ℝ≥0∞)
      (Gm.futureJoined c r l a ξ, ⊤))

/-- Below `T + F` the exact-horizon pair has the future pair's capacities. -/
theorem forwardCapacity_future_eq_exact (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ξ : Ω) {t : ℝ≥0}
    (ht : t ≤ RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ) :
    RootH29.forwardCapacity (rootPt r.1) c.s t (RootJ31.futurePair c r l a ξ) =
      RootH29.forwardCapacity (rootPt r.1) c.s t (exactPair c r l a ξ) := by
  obtain ⟨hJ, hJ0⟩ := Gm.continuous_futureJoined c r l a ξ
  have hFL : RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ ≤
      RootJ31.historyTime c r l + RootJ31.candidateCap c r a :=
    add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a ξ)
  rw [Gm.futurePair_eq_recOfDriver]
  refine Gm.forwardCapacity_congr _ _ t _ fun y hy => ?_
  have hy0 : 0 ≤ y := hy.1
  have hyt : y.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hy.2
  have hyv := hyt.trans ht
  have e1 := Gm.rdrv_recOfDriver hJ hJ0
    (q₀ := RootJ31.historyTime c r l + RootJ31.candidateCap c r a) y.toNNReal
  have e2 := Gm.rdrv_recOfDriver hJ hJ0
    (q₀ := RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ) y.toNNReal
  rw [Real.coe_toNNReal _ hy0] at e1 e2
  change rdrv _ y = rdrv (recOf ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ : ℝ≥0) : ℝ≥0∞)
    (Gm.futureJoined c r l a ξ, ⊤)) y
  rw [e1, ← Gm.recOfDriver_eq_recOf, e2, min_eq_left (hyv.trans hFL), min_eq_left hyv]

end Pair

/-- **J32's reads are every driver of the re-centred forward hulls**: almost surely, at every live sample of every
candidate, for every continuous driver `R` from `0` whose Loewner hulls at the relative clock are the re-centred
forward hulls of the exact-horizon pair on `[0, T + F]`, J32's capacity driver read is `R` below `A(T + F)`. -/
theorem ae_j32Read_eq_of_hull {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ξ ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), 0 < (RootJ31.sourceSample c r l a ξ).1 →
      ∀ R : ℝ≥0 → ℝ, Continuous R → R 0 = 0 →
      (∀ t ∈ Icc 0 (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ),
        fwdHull (fun r : ℝ => R r.toNNReal)
            (RootH29.forwardCapacity (rootPt r.1) c.s t (exactPair c r l a ξ)) =
          (fun z : ℂ => z + ((-relBase (rootPt r.1) c.s (exactPair c r l a ξ) : ℝ) : ℂ)) ''
            RootH29.forwardHull (rootPt r.1) c.s t (exactPair c r l a ξ)) →
      ∀ c' : ℝ≥0, (c' : ℝ) < RootH29.forwardCapacity (rootPt r.1) c.s
          (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ) (exactPair c r l a ξ) →
        j32Read c r l a c' ξ = R c' := by
  filter_upwards [RootCv.ae_coverEvent_spec h13 c r, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ, Gm.ae_futureJoined_trace h13 c r,
    RootJ32.ae_capacityDriverRead_eq h13 c r]
    with ξ hcover hα hreg hζ hjoin hJ32 l a hlive R hRc hR0 hR c' hc'
  obtain ⟨hcov, hold, -, -⟩ := RootK32.sourceSample_live_geometry c r l a ξ hlive
  obtain ⟨hseed, hsH, -, -, -, harc⟩ := hcover hcov
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  have hs : 0 < c.s := by
    by_contra hn
    have hs0 : c.s = 0 := le_antisymm (not_lt.mp hn) zero_le
    exact ne_zero_of_mem_H hsH (by rw [hs0]; exact hα.1)
  obtain ⟨-, γ, hγ⟩ := hjoin l a hold
  obtain ⟨hJ, hJ0⟩ := Gm.continuous_futureJoined c r l a ξ
  have hvL : RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ ≤
      Sec5.Prop513Schedule.lastTime 0 (RootJ31.futureProgram c r l a) := by
    rw [Gm.lastTime_futureProgram]
    exact add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a ξ)
  have hv := RootK32.sourceSample_live_before_contact c r l a ξ hlive
  rw [← Gm.lastTime_futureProgram] at hv
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous (c.α ξ) := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hnc := (Gm.lt_translatedContact_iff c.W c.ζ ξ hα hW hW0 hζ (rootPt r.1) c.s hJ hJ0 hγ hvL).1 hv
  have hv' : ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ : ℝ≥0) : ℝ≥0∞) < min
      (firstContactTime (fun t => sphereInv ((((rootPt r.1 : ℝ) : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (c.α ξ u : OnePoint ℂ)) '' Icc 0 c.s)) (Gm.futureJoined c r l a ξ, (⊤ : ℝ≥0∞)).2 := by
    change _ < min _ ⊤
    rw [min_top_right]
    exact (Gm.lt_firstContactTime_iff_noncontact (continuous_const.add hγc) hαc _ c.s).2 hnc
  have he := Gm.isRegularDriver_top hJ hJ0
  have hx := RootH29.rootPt_nonneg_of_seedOK c hseed
  have hc'' : (c' : ℝ) ≤ RootH29.forwardCapacity (rootPt r.1) c.s
      (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ) (RootJ31.futurePair c r l a ξ) := by
    rw [forwardCapacity_future_eq_exact c r l a ξ le_rfl]
    exact hc'.le
  unfold j32Read
  rw [hJ32 l a hlive c' hc'']
  exact capacityDriverRead_eq_of_hull c.W c.ζ ξ hα hW hW0 hζ hs hx harc he hγ hv' hRc hR0 hR hc'

/-- **`J32DriverId` from the instance's re-centred hulls.** Let `R` be the stage instance's relative driver in the
re-centred chart (continuous, from `0`). On the retained gate, at live samples, suppose it has the re-centred hull
identity on `[0, T + F]` and the stage driver is its increment after the history's capacity. Then the J32 driver
identification holds. -/
theorem j32DriverId_of_hull {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (h13 : Theorem13Statement.{u}) (K : PkgFamily.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (R : ℝ≥0 → Ω → ℝ) (hRc : ∀ ξ, Continuous fun u => R u ξ) (hR0 : ∀ ξ, R 0 ξ = 0)
    (hhull : ∀ᵐ ξ ∂c.P, ξ ∈ GW2Sdg.rootGate c r l → 0 < (RootJ31.sourceSample c r l a ξ).1 →
      ∀ t ∈ Icc 0 (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ),
        fwdHull (fun r : ℝ => R r.toNNReal ξ)
            (RootH29.forwardCapacity (rootPt r.1) c.s t (exactPair c r l a ξ)) =
          (fun z : ℂ => z + ((-relBase (rootPt r.1) c.s (exactPair c r l a ξ) : ℝ) : ℂ)) ''
            RootH29.forwardHull (rootPt r.1) c.s t (exactPair c r l a ξ))
    (hstage : ∀ᵐ ξ ∂c.P, ξ ∈ GW2Sdg.rootGate c r l → ∀ u : ℝ≥0, u < GW2Sdg.rootGain c r l a ξ →
      ((K Ω c r).inst l a).drv c u ξ =
        R (GW2Sdg.rootHistCap c r l a ξ + u) ξ - R (GW2Sdg.rootHistCap c r l a ξ) ξ) :
    J32DriverId K Ω c r l a := by
  filter_upwards [ae_j32Read_eq_of_hull h13 c r, hhull, hstage] with ξ hread hh hst hG u hu
  set T := RootJ31.historyTime c r l
  set v := RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ
  have hgain : 0 < GW2Sdg.rootGain c r l a ξ := lt_of_le_of_lt zero_le hu
  have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 := by
    rw [GW2Sdg.sourceSample_fst]
    exact ENNReal.mul_pos (pow_ne_zero _ (by norm_num)) (ENNReal.coe_ne_zero.2 hgain.ne')
  -- the capacities at `T` and at `v`
  have hT0 : 0 ≤ RootH29.forwardCapacity (rootPt r.1) c.s T (RootJ31.futurePair c r l a ξ) :=
    RootJ32.forwardCapacity_nonneg _ _ _ _
  have hgain' : (0 : ℝ) < RootH29.forwardCapacity (rootPt r.1) c.s v (RootJ31.futurePair c r l a ξ) -
      RootH29.forwardCapacity (rootPt r.1) c.s T (RootJ31.futurePair c r l a ξ) := by
    have h := hgain
    unfold GW2Sdg.rootGain GW2Sdg.rootCapAt at h
    exact Real.toNNReal_pos.1 h
  have hlev : ∀ w : ℝ≥0, w ≤ u → ((GW2Sdg.rootHistCap c r l a ξ + w : ℝ≥0) : ℝ) <
      RootH29.forwardCapacity (rootPt r.1) c.s v (exactPair c r l a ξ) := by
    intro w hw
    rw [← forwardCapacity_future_eq_exact c r l a ξ le_rfl]
    have hu' : ((u : ℝ≥0) : ℝ) < RootH29.forwardCapacity (rootPt r.1) c.s v (RootJ31.futurePair c r l a ξ) -
        RootH29.forwardCapacity (rootPt r.1) c.s T (RootJ31.futurePair c r l a ξ) := by
      have h := NNReal.coe_lt_coe.2 hu
      unfold GW2Sdg.rootGain GW2Sdg.rootCapAt at h
      rwa [Real.coe_toNNReal _ hgain'.le] at h
    have hw' : (w : ℝ) ≤ u := NNReal.coe_le_coe.2 hw
    unfold GW2Sdg.rootHistCap GW2Sdg.rootCapAt
    push_cast
    rw [Real.coe_toNNReal _ hT0]
    linarith
  have hR := hh hG hlive
  rw [hread l a hlive (fun u => R u ξ) (hRc ξ) (hR0 ξ) hR _ (hlev u le_rfl),
    hread l a hlive (fun u => R u ξ) (hRc ξ) (hR0 ξ) hR _ (by simpa using hlev 0 zero_le), hst hG u hu]

end InteractingSLE.Theorem14.GW2Bf
