/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfRegQ
import InteractingSLE.Spec.Sec7.Aux50HitPath
import InteractingSLE.WangWu.ReverseContactUnion
import InteractingSLE.Spec.Coupling.Locality11Gauss
import InteractingSLE.Spec.Sec5.GlueCondTopo
import InteractingSLE.Spec.Sec7.SideHeightHull

/-!
# The cross-curve conditioning on the glued space, field side: the two stopped hulls are a local set

Packet PROVE-GLUECOND. Specification §4.2, proof of Lemma 4.7 (`source/spec/p097-144.md#lem-4.7-proof`, p. 118):

> "On the event that `t` occurs before the first time that `η′` accumulates in `∂_L𝒮 ∪ η([0, τ])`, Proposition 3.7
> and Proposition 3.8 together tell us that the boundary data for the conditional law of `h` given both `η|_{[0,τ]}`
> and `η′|_{[0,t]}` in the unbounded component of `𝒮 ∖ (η([0, τ]) ∪ η′([0, t]))` is that of a GFF whose boundary
> conditions along `∂_L𝒮 ∪ η([0, τ])` (resp. `∂_U𝒮 ∪ η′([0, t])`) agree with those of the conditional law of `h`
> given just `η|_{[0,τ]}` (resp. `η′|_{[0,t]}`) alone."

This is the field side of the cross-curve conditioning, on the glued space of `Prop411Q.CfGlueAE` (PROVE-SEC5-N): the
flow line `η` of `h` (an optional hull coupling on `Ω`) and the counterflow line `η′ = R ∘ β` of `h − π/2 χ`
(`R z = −1/z`, the centred counterflow coupling on `Ω₂`, read through a regular conditional law `k` of its history),
conditionally independent given `h`.

* **The counterflow hull read from a history** (`hullAt t y`, chart `R`; `cfHullQ t y = R(hullAt t y)`, chart `Q`):
  the Loewner hull at time `t` of the regularized driver of the history stopped at `t` (`Sec4.regHull`). Unlike the
  closure of the trace (`WangWu.histHull`), this is the filled hull also for the non-simple counterflow
  (`κ′ = 16/κ > 4`). It is hitting-measurable and relatively closed in `ℍ` for every history.
* **The counterflow hull is a local set on `Ω₂`** (`isLocalSet_cfHullQ`): from the frozen local-set clause of the
  counterflow's optional hull coupling in the chart `R`, through the chart transport of `IsCenteredCounterflowDriver`
  (`h₂ = returnField a k h₂′ = R_*(h₂′) + (a + k · lift)`), `IsLocalSet.reflect` and `IsLocalSet.add_dist`.
* **The two stopped hulls are a local set on the glued space** (`isLocalSet_union_glue`, Proposition 3.7 by the
  independent-union lemma `IsLocalSet.glue_union`): `A ∪ G` with `A` the flow hull at a positive time `q` (a
  hitting-measurable version) and `G = cfHullQ t p.2`, for the centred field `h − 𝔥₀`.
* **Proposition 3.8 for the two stopped hulls** (`ae_union_boundary_cfGlue`): every local-set mean of `A ∪ G` has,
  almost surely, a harmonic representative `w` on `ℍ ∖ (A ∪ G)` that is asymptotic to the local-set mean of `A` near
  `A ∪ ℝ` away from `G`, and to that of `G` near `G ∪ ℝ` away from `A` (WangWu's generic `ae_union_boundary_glue`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.GlueCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref
open LocalSets (IsLocalSetMean)

/-! ### The counterflow hull read from a history -/

section Hull

variable {nL nR : ℕ}

/-- **The hull at time `t` read from a history**: the Loewner hull at time `t` of the regularized driver of the
history stopped at `t`, closed in `ℍ` (the filled hull, also for non-simple traces). -/
def hullAt (t : ℝ≥0) (y : HistorySpace nL nR) : Set ℂ :=
  Sec4.regHull (Sec4.stopHistory (Aux50Hit.cstop t) y)

/-- **The counterflow hull at time `t` in the chart `Q`**: the image of `hullAt t y` under `R(z) = −1/z`. -/
def cfHullQ (t : ℝ≥0) (y : HistorySpace 0 0) : Set ℂ := negInv '' hullAt t y

theorem hullAt_relClosed (t : ℝ≥0) (y : HistorySpace nL nR) :
    hullAt t y ⊆ H ∧ IsOpen (H \ hullAt t y) := by
  refine ⟨inter_subset_right, ?_⟩
  have e : H \ hullAt t y =
      H \ closure (fwdHull (Ito.rpath (Sec4.regPath (Sec4.stopHistory (Aux50Hit.cstop t) y)))
        (Sec4.histStop (Sec4.stopHistory (Aux50Hit.cstop t) y))) := by
    ext z
    constructor
    · rintro ⟨hzH, hz⟩
      exact ⟨hzH, fun hc => hz ⟨hc, hzH⟩⟩
    · rintro ⟨hzH, hz⟩
      exact ⟨hzH, fun hc => hz hc.1⟩
  rw [e]
  exact QuantumZipper.isOpen_H.sdiff isClosed_closure

theorem cfHullQ_relClosed (t : ℝ≥0) (y : HistorySpace 0 0) :
    cfHullQ t y ⊆ H ∧ IsOpen (H \ cfHullQ t y) :=
  image_negInv_relClosed (hullAt_relClosed t y)

/-- **The counterflow hull read from a history is hitting-measurable.** -/
theorem measurable_hullAt (t : ℝ≥0) : Measurable[_, hittingSigma] (hullAt (nL := nL) (nR := nR) t) := by
  have hY : Measurable (Sec4.stopHistory (nL := nL) (nR := nR) (Aux50Hit.cstop t)) :=
    Sec4.measurable_stopHistory (Aux50Hit.measurable_cstop t)
  refine @measurable_generateFrom _ _ _ _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have hne : Uᶜ.Nonempty := ⟨0, fun h0 => by
    have : (0 : ℝ) < (0 : ℂ).im := hUH h0
    simp at this⟩
  have e : (hullAt (nL := nL) (nR := nR) t) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      ⋃ j : ℕ, (Sec4.stopHistory (nL := nL) (nR := nR) (Aux50Hit.cstop t) ⁻¹'
        {γ | Disjoint (WholeField.openExhaust U j) (Sec4.regHull γ)})ᶜ := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, mem_compl_iff]
    constructor
    · rintro ⟨z, hzK, hzU⟩
      rw [← WholeField.iUnion_openExhaust hU hne] at hzU
      obtain ⟨j, hj⟩ := mem_iUnion.1 hzU
      exact ⟨j, fun hd => Set.disjoint_left.1 hd hj hzK⟩
    · rintro ⟨j, hj⟩
      obtain ⟨z, hzC, hzK⟩ := Set.not_disjoint_iff.1 hj
      exact ⟨z, hzK, WholeField.openExhaust_subset j hzC⟩
  rw [e]
  exact MeasurableSet.iUnion fun j =>
    (hY (Sec4.measurableSet_disjoint_regHull (WholeField.isCompact_openExhaust U j))).compl

theorem measurable_cfHullQ (t : ℝ≥0) : Measurable[_, hittingSigma] (cfHullQ t) :=
  measurable_image_negInv.comp (measurable_hullAt t)

/-- **The hull read from any history is a compact `ℍ`-hull** (the regularized driver is continuous). -/
theorem isHPHull_hullAt (t : ℝ≥0) (y : HistorySpace nL nR) : IsHPHull (hullAt t y) := by
  have hc := Sec4.continuous_rpath_regPath (Sec4.stopHistory (Aux50Hit.cstop t) y)
  rw [hullAt, Sec4.regHull, Aux50Hit.closure_fwdHull_inter_H hc (NNReal.coe_nonneg _)]
  exact isHPHull_fwdHull hc (NNReal.coe_nonneg _)

end Hull

/-! ### The counterflow hull is a local set on the counterflow's space -/

section Omega2

variable {κ : ℝ} {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- On a path of infinite lifetime with a continuous driver from `0`, the hull read from the history is the driver's
Loewner hull. -/
theorem hullAt_cfHistory {ω : Ω₂} (hζ : ζ₂ ω = ⊤) (hw0 : W₂ 0 ω = 0) (hw : Continuous fun t => W₂ t ω)
    (t : ℝ≥0) : hullAt t (cfHistory W₂ ζ₂ ω) = fwdHull (fun s : ℝ => W₂ s.toNNReal ω) t := by
  have hg : Aux50Hit.IsGoodPath W₂ (Fin.elim0 : Fin 0 → ℝ≥0 → Ω₂ → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω₂ → ℝ) ζ₂ ω :=
    ⟨hζ, hw0, hw.continuousOn, fun i => i.elim0, fun i => i.elim0⟩
  exact Aux50Hit.regHull_stopHistory_cstop hg t

/-- The additive part of the return chart: `a + k · lift`, with `lift = Im(−2 log w)` the infinity-source lift. -/
def retShift (a k : ℝ) (w : ℂ) : ℝ := a + k * infinitySourceChart.2.2 w

theorem continuousOn_retShift (a k : ℝ) : ContinuousOn (retShift a k) H :=
  continuousOn_const.add (continuousOn_const.mul Sec7.StripSysField.continuousOn_infinitySourceChart_lift')

theorem harmonicOnNhd_retShift (a k : ℝ) : InnerProductSpace.HarmonicOnNhd (retShift a k) H := fun z hz =>
  (InnerProductSpace.harmonicAt_const a).add
    (by simpa only [Pi.smul_def, smul_eq_mul] using
      (Sec7.StripSysField.harmonicOnNhd_infinitySourceChart_lift z hz).const_smul (c := k))

/-- **The return chart is the reflection plus a harmonic shift**: `returnField a k f = R_* f + (a + k · lift)`. -/
theorem returnField_eq_reflectField_add (a k : ℝ) (f : DistOn upperHalfPlaneOpens) :
    Sec7.StripSysField.returnField a k f =
      reflectField f + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (retShift a k) := by
  ext φ
  rw [Sec7.StripSysField.returnField_apply, add_apply, reflectField_apply,
    Coupling.smoothDist_apply_eq (continuousOn_retShift a k)]
  have h0 : Integrable fun w => φ w := by
    simpa only [one_mul] using Coupling.MartMeans2.integrable_mul_test_of_continuousOn (f := fun _ => (1 : ℝ))
      continuousOn_const φ φ.tsupport_subset
  have h1 := Coupling.MartMeans2.integrable_mul_test_of_continuousOn
    Sec7.StripSysField.continuousOn_infinitySourceChart_lift' φ φ.tsupport_subset
  have e : (∫ z, retShift a k z * φ z) = a * (∫ w, φ w) + k * ∫ w, infinitySourceChart.2.2 w * φ w := by
    simp only [retShift, add_mul, mul_assoc]
    rw [integral_add (h0.const_mul a) (h1.const_mul k), integral_const_mul, integral_const_mul]
  rw [e]
  ring

/-- **The counterflow hull is a local set of the counterflow's field** (chart `Q`): for a centred counterflow coupling
whose lifetime is almost surely infinite and whose driver is almost surely continuous from `0`, the hull read from
the history at time `t`, reflected by `R`, is a local set of `h₂`. -/
theorem isLocalSet_cfHullQ (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω) (t : ℝ≥0) :
    IsLocalSet (fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω)) h₂ P₂ := by
  obtain ⟨b', J', h', -, htr, hfl⟩ := hcf
  obtain ⟨h'', 𝓕, VL, VR, B, htac, hC⟩ := hfl
  have e : h'' = h' := funext fun ω =>
    Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htac ω)
  subst e
  obtain ⟨-, -, -, hX, hker⟩ := hC
  have hτζ : ∀ᵐ ω ∂P₂, (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ₂ ω := by
    filter_upwards [hreg] with ω hω
    rw [hω.1]
    exact ENNReal.coe_lt_top
  have hK := (hker (fun _ => ((t : ℝ≥0) : WithTop ℝ≥0)) (isStoppingTime_const _ t) hτζ).1
  have hK' : IsLocalSet (fun ω => fwdHull (fun s : ℝ => W₂ s.toNNReal ω) (t : ℝ)) h'' P₂ := by
    simpa only [WithTop.untopD_coe] using hK
  set D := SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens
    (retShift (-(π * chiC κ)) (chiC (16 / κ))) with hD
  have hDh : IsHarmonicDistOn D H := WholeField.isHarmonicDistOn_smoothDist (harmonicOnNhd_retShift _ _)
  have hR := Coupling.IsLocalSet.add_dist (IsLocalSet.reflect hK') hDh
  have hh₂ : h₂ = fun ω => reflectField (h'' ω) + D := by
    funext ω
    rw [Theorem14.GW2Cone.eq_returnField_of_isChartTransport (htr ω), returnField_eq_reflectField_add]
  rw [hh₂]
  refine Coupling.IsLocalSet.congr_set hR ?_
  filter_upwards [hreg] with ω hω
  rw [cfHullQ, hullAt_cfHistory hω.1 hω.2.1 hω.2.2]

end Omega2

/-! ### The centred field on the glued space -/

section Centre

open SupercriticalConformalCovariance.GM24 (smoothDist)

theorem pushTest_shiftChart_zero (φ : TestOn upperHalfPlaneOpens) :
    Chart.pushTest (Exist.isConformal_shiftChart 0) φ = φ := by
  ext z
  rw [Exist.pushTest_shiftChart_apply, Complex.ofReal_zero, sub_zero]

theorem flowField_zero_flowField_zero (a b : ℝ) (f : DistOn upperHalfPlaneOpens) :
    Exist.flowField 0 a (Exist.flowField 0 b f) = Exist.flowField 0 (a + b) f := by
  ext φ
  simp only [Exist.flowField_apply, pushTest_shiftChart_zero]
  ring

theorem flowField_zero_zero (f : DistOn upperHalfPlaneOpens) : Exist.flowField 0 0 f = f := by
  ext φ
  simp only [Exist.flowField_apply, pushTest_shiftChart_zero, zero_mul, add_zero]

/-- The shift `flowField 0 a` adds the constant `a`. -/
theorem flowField_zero_eq_add (a : ℝ) (f : DistOn upperHalfPlaneOpens) :
    Exist.flowField 0 a f = f + smoothDist upperHalfPlaneOpens (fun _ => a) := by
  ext φ
  rw [Exist.flowField_apply, pushTest_shiftChart_zero, add_apply,
    Coupling.smoothDist_apply_eq continuousOn_const, integral_const_mul]

/-- **The centring of the counterflow field**: `cenT κ u₀ (h − π/2 χ) = h − 𝔥₀`, with `𝔥₀ = u₀` the bounded harmonic
extension of the flow line's data. -/
def cenT (κ : ℝ) (u₀ : ℂ → ℝ) (f : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  Exist.flowField 0 (π / 2 * chiC κ) f - smoothDist upperHalfPlaneOpens u₀

/-- The inverse of `cenT κ u₀`. -/
def cenT' (κ : ℝ) (u₀ : ℂ → ℝ) (g : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  cfField κ (g + smoothDist upperHalfPlaneOpens u₀)

theorem measurable_cenT (κ : ℝ) (u₀ : ℂ → ℝ) : Measurable (cenT κ u₀) :=
  (WholeField.measurable_sub_dist _).comp (Exist.measurable_flowField 0 _)

theorem measurable_cenT' (κ : ℝ) (u₀ : ℂ → ℝ) : Measurable (cenT' κ u₀) :=
  (measurable_cfField κ).comp (Coupling.measurable_add_distOnConst _)

theorem cenT_cfField (κ : ℝ) (u₀ : ℂ → ℝ) (f : DistOn upperHalfPlaneOpens) :
    cenT κ u₀ (cfField κ f) = f - smoothDist upperHalfPlaneOpens u₀ := by
  rw [cenT, cfField, flowField_zero_flowField_zero, add_neg_cancel, flowField_zero_zero]

theorem cenT'_cenT (κ : ℝ) (u₀ : ℂ → ℝ) (f : DistOn upperHalfPlaneOpens) : cenT' κ u₀ (cenT κ u₀ f) = f := by
  rw [cenT', cenT, sub_add_cancel, cfField, flowField_zero_flowField_zero, neg_add_cancel, flowField_zero_zero]

theorem cenT_eq_add_sub (κ : ℝ) (u₀ : ℂ → ℝ) (f : DistOn upperHalfPlaneOpens) :
    cenT κ u₀ f = f + smoothDist upperHalfPlaneOpens (fun _ => π / 2 * chiC κ) -
      smoothDist upperHalfPlaneOpens u₀ := by
  rw [cenT, flowField_zero_eq_add]

end Centre

/-! ### The two stopped hulls are a local set on the glued space (Proposition 3.7) -/

section Glue

open SupercriticalConformalCovariance.GM24 (smoothDist)

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}

omit [IsProbabilityMeasure P] in
/-- **The flow hull at a deterministic time is a local set of the centred flow field** (read from the flow line's
history, a hitting-measurable version of `K_q`). -/
theorem isLocalSet_hullAt_flow (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q : ℝ≥0) :
    IsLocalSet (fun ω => hullAt q (killedHistory W VL VR ζ ω)) (fun ω => cenT κ u₀ (cfField κ (h ω))) P := by
  obtain ⟨hX, hker⟩ := hC.2.2.2
  have hτζ : ∀ᵐ ω ∂P, (((fun _ : Ω => ((q : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hK := (hker (fun _ => ((q : ℝ≥0) : WithTop ℝ≥0)) (isStoppingTime_const _ q) hτζ).1
  have hK' : IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) (q : ℝ)) h P := by
    simpa only [WithTop.untopD_coe] using hK
  have hA := WholeField.IsLocalSet.sub_dist hK' (WholeField.isHarmonicDistOn_smoothDist hu₀.1)
  have e : (fun ω => cenT κ u₀ (cfField κ (h ω))) = fun ω => h ω - smoothDist upperHalfPlaneOpens u₀ :=
    funext fun ω => cenT_cfField κ u₀ (h ω)
  rw [e]
  refine Coupling.IsLocalSet.congr_set hA ?_
  filter_upwards [Aux50Hit.ae_isGoodPath hC.1 hζ] with ω hg
  exact Aux50Hit.regHull_stopHistory_cstop hg q

omit [IsProbabilityMeasure P₂] in
/-- **The counterflow hull is a local set of the centring of the counterflow's field.** -/
theorem isLocalSet_cfHullQ_cenT (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (t : ℝ≥0) :
    IsLocalSet (fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω)) (fun ω => cenT κ u₀ (h₂ ω)) P₂ := by
  have hc : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens (fun _ => π / 2 * chiC κ)) H :=
    WholeField.isHarmonicDistOn_smoothDist fun _ _ => InnerProductSpace.harmonicAt_const _
  have h1 := WholeField.IsLocalSet.sub_dist (Coupling.IsLocalSet.add_dist (isLocalSet_cfHullQ hcf hreg₂ t) hc)
    (WholeField.isHarmonicDistOn_smoothDist hu₀)
  have e : (fun ω => cenT κ u₀ (h₂ ω)) = fun ω => h₂ ω + smoothDist upperHalfPlaneOpens (fun _ => π / 2 * chiC κ) -
      smoothDist upperHalfPlaneOpens u₀ := funext fun ω => cenT_eq_add_sub κ u₀ (h₂ ω)
  rw [e]
  exact h1

/-- **Proposition 3.7 on the glued space: the flow hull at time `q` together with the counterflow hull at time `t` is
a local set of the centred field `h − 𝔥₀`.** On the glued space `P ⊗ k(h − π/2 χ)` of an optional hull coupling
`(h, W, …)` of infinite lifetime and a centred counterflow coupling `(h₂, W₂)` of `h − π/2 χ` (conditionally
independent given `h`), `A = K_q` (read from the flow line's history) and `G = R(K′_t)` (read from the counterflow's
history) are local sets of `h − 𝔥₀`, and so is `A ∪ G` (the independent-union lemma). -/
theorem isLocalSet_union_glue (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q t : ℝ≥0) :
    IsLocalSet (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1))
        (fun p => cenT κ u₀ (cfField κ (h p.1)))
        (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) ∧
      IsLocalSet (fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2) (fun p => cenT κ u₀ (cfField κ (h p.1)))
        (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) ∧
      IsLocalSet (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
        (fun p => cenT κ u₀ (cfField κ (h p.1)))
        (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) := by
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hAm : Measurable[mΩ, hittingSigma] fun ω => hullAt q (killedHistory W VL VR ζ ω) :=
    (measurable_hullAt q).comp (measurable_killedHistory hX)
  have hAg := IsLocalSet.glue_fst hXm k (T := cenT κ u₀) (isLocalSet_hullAt_flow hC hζ hu₀ q)
  have hGg := IsLocalSet.glue_snd hXm k (CfRegQ.measurable_of_isCenteredCounterflowDriver hcf)
    (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)) hlaw hk
    (measurable_cenT κ u₀) (measurable_cfHullQ t) MeasurableSet.univ (fun y _ => cfHullQ_relClosed t y)
    (Eventually.of_forall fun _ => mem_univ _) (isLocalSet_cfHullQ_cenT hcf hreg₂ hu₀.1 t)
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => cenT κ u₀ (cfField κ (h ω))) P := by
    have e : (fun ω => cenT κ u₀ (cfField κ (h ω))) = WholeField.centredField h u₀ :=
      funext fun ω => cenT_cfField κ u₀ (h ω)
    rw [e]
    exact WholeField.isZeroBoundaryGFF_centredField hC hu₀
  exact ⟨hAg, hGg, IsLocalSet.glue_union hXm k (measurable_cenT κ u₀) (measurable_cenT' κ u₀) (cenT'_cenT κ u₀)
    hF hAm (measurable_cfHullQ t) hAg hGg⟩

/-- **Proposition 3.8 for the two stopped hulls on the glued space.** In the setting of `isLocalSet_union_glue`, for
local-set means `g` of `A ∪ G`, `gA` of `A = K_q` and `gG` of `G = R(K′_t)` (centred field `h − 𝔥₀`): almost surely,
for all harmonic representatives `wA` of `gA` off `A` and `wG` of `gG` off `G`, the union mean has a harmonic
representative `w` off `A ∪ G` with `w − wA → 0` at every point of `A ∪ ℝ` near which `G ⊆ A`, and `w − wG → 0` at
every point of `G ∪ ℝ` near which `A ⊆ G`. -/
theorem ae_union_boundary_cfGlue (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q t : ℝ≥0)
    {g gA gG : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
      (fun p => cenT κ u₀ (cfField κ (h p.1)))
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) g)
    (hgA : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1))
      (fun p => cenT κ u₀ (cfField κ (h p.1)))
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) gA)
    (hgG : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2)
      (fun p => cenT κ u₀ (cfField κ (h p.1)))
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) gG) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)), ∀ wA wG : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd wA (H \ hullAt q (killedHistory W VL VR ζ p.1)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ hullAt q (killedHistory W VL VR ζ p.1) →
        gA p φ = ∫ z, wA z * φ z) →
      InnerProductSpace.HarmonicOnNhd wG (H \ cfHullQ t p.2) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cfHullQ t p.2 → gG p φ = ∫ z, wG z * φ z) →
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2) → g p φ = ∫ z, w z * φ z) ∧
        (∀ z₀ ∈ hullAt q (killedHistory W VL VR ζ p.1) ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, cfHullQ t p.2 ∩ ball z₀ r ⊆ hullAt q (killedHistory W VL VR ζ p.1)) →
          Tendsto (fun z => w z - wA z)
            (𝓝[H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)] z₀) (𝓝 0)) ∧
        (∀ z₀ ∈ cfHullQ t p.2 ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, hullAt q (killedHistory W VL VR ζ p.1) ∩ ball z₀ r ⊆ cfHullQ t p.2) →
          Tendsto (fun z => w z - wG z)
            (𝓝[H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)] z₀) (𝓝 0)) := by
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hAm : Measurable[mΩ, hittingSigma] fun ω => hullAt q (killedHistory W VL VR ζ ω) :=
    (measurable_hullAt q).comp (measurable_killedHistory hX)
  obtain ⟨hAg, hGg, -⟩ := isLocalSet_union_glue (k := k) hC hζ hcf hreg₂ hlaw hk hu₀ q t
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => cenT κ u₀ (cfField κ (h ω))) P := by
    have e : (fun ω => cenT κ u₀ (cfField κ (h ω))) = WholeField.centredField h u₀ :=
      funext fun ω => cenT_cfField κ u₀ (h ω)
    rw [e]
    exact WholeField.isZeroBoundaryGFF_centredField hC hu₀
  exact ae_union_boundary_glue hXm k (measurable_cenT κ u₀) (measurable_cenT' κ u₀) (cenT'_cenT κ u₀) hF hAm
    (measurable_cfHullQ t) hAg hGg
    (Eventually.of_forall fun p => not_isBounded_lowerUnion_of_isHPHull (isHPHull_hullAt _ _))
    (Eventually.of_forall fun p => not_isBounded_lowerUnion_image_negInv (isHPHull_hullAt _ _)) hg hgA hgG

/-- **The flow hull's mean on the glued space, explicit** (the boundary data along `∂ℍ ∪ η([0, q])` of the
conditional law given `η|_{[0,q]}` alone). For `κ > 0`, an optional hull coupling of infinite lifetime and bounded
harmonic extensions `u ω` of the force-word data at the centred positions at time `q`: there is a local-set mean `g`
of `A = K_q` (read from the flow line's history) for the centred field on the glued space, and almost surely, for
every test function supported off `A`, `g(φ) = ∫ (𝔥_q − 𝔥₀) φ` with `𝔥_q = couplingMean κ W q u` the frozen coupling
mean. -/
theorem exists_isLocalSetMean_flowHull_glue (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q : ℝ≥0)
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω))
      (forceJumpSet (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω)) (u ω)) :
    ∃ g : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1))
        (fun p => cenT κ u₀ (cfField κ (h p.1)))
        (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) g ∧
      ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
        ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ hullAt q (killedHistory W VL VR ζ p.1) →
          g p φ = ∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal p.1) q (u p.1) z - u₀ z) * φ z := by
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hAm : Measurable[mΩ, hittingSigma] fun ω => hullAt q (killedHistory W VL VR ζ ω) :=
    (measurable_hullAt q).comp (measurable_killedHistory hX)
  have hh0 := WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have e : (fun ω => cenT κ u₀ (cfField κ (h ω))) = WholeField.centredField h u₀ :=
    funext fun ω => cenT_cfField κ u₀ (h ω)
  have hloc : IsLocalSet (fun ω => hullAt q (killedHistory W VL VR ζ ω)) (WholeField.centredField h u₀) P :=
    e ▸ isLocalSet_hullAt_flow hC hζ hu₀ q
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh0 hAm hloc
  have hτζ : ∀ᵐ ω ∂P, (((fun _ : Ω => ((q : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hAK : ∀ᵐ ω ∂P, hullAt q (killedHistory W VL VR ζ ω) =
      (fun z : ℂ => z + ((0 : ℝ) : ℂ)) '' fwdHull (fun s : ℝ => W s.toNNReal ω)
        (((fun _ : Ω => ((q : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0 : ℝ≥0) := by
    filter_upwards [Aux50Hit.ae_isGoodPath hC.1 hζ] with ω hg
    rw [WithTop.untopD_coe, hullAt, Aux50Hit.regHull_stopHistory_cstop hg q]
    simp only [Complex.ofReal_zero, add_zero, image_id']
    rfl
  have hid := Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull (x := 0) (c := 0) hC hκ
    (fun ω => by simpa only [zero_mul] using Sec7.StripSysField.isTranslateAddConst_zero_self (h ω) 0) hh0 hu₀.1 hu₀
    (fun z _ => by simp only [Complex.ofReal_zero, add_zero]) hX (isStoppingTime_const _ q) hτζ hAm hAK hg
    (u := u) (by simpa only [WithTop.untopD_coe] using hu)
  refine ⟨fun p => g p.1, ?_, ?_⟩
  · have hgl := IsLocalSetMean.comp measurable_fst (glueMeasure_fst (μ := P) k hXm) hAm
      (WholeField.measurable_centredField hC.2.1 u₀) hg
    have e' : (fun p : Ω × HistorySpace 0 0 => cenT κ u₀ (cfField κ (h p.1))) =
        fun p => WholeField.centredField h u₀ p.1 := funext fun p => cenT_cfField κ u₀ (h p.1)
    rw [e']
    exact hgl
  · have hid' : ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ hullAt q (killedHistory W VL VR ζ ω) →
          g ω φ = ∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) q (u ω) z - u₀ z) * φ z := by
      filter_upwards [hid] with ω hω φ hφ
      rw [hω φ hφ]
      simp only [WithTop.untopD_coe, Complex.ofReal_zero, sub_zero]
    exact ae_glue_fst (μ := P) k hXm hid'

end Glue

end InteractingSLE.Sec5.GlueCond
