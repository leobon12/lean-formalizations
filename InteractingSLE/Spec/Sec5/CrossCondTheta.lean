/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondWord

/-!
# The cross-conditioning law at a general relative angle `θ`: the setting

Packet PROVE-CROSSCOND-THETA. PROVE-GLUECOND2–10 proved the cross-conditioning law for the flow line `η` of `h` (an
optional hull coupling) and the counterflow line of `h − π/2 χ` from `∞` (a centred counterflow coupling, glued
conditionally independently given `h`): relative angle `π/2`. This file sets up the same glued configuration at a
**general relative angle `θ`**: the counterflow is that of `h − θχ` (equivalently, `η` is the flow line of angle `θ`
of the counterflow's own field `h − θχ`). The `θ = π/2` case is the landed one (`cfFieldT_pi_div_two`,
`cenTT_pi_div_two`).

* `cfFieldT κ θ f = f − θχ`, its centring `cenTT κ θ u₀ f = f + θχ − u₀` (so `cenTT κ θ u₀ (cfFieldT κ θ h) = h − u₀`);
* `cLT θ`, `cRT θ`: the junction weights of the image word in the counterflow chart, derived from the exposed heights
  `−λ′ + πχ + θχ` (left) and `λ′ − πχ + θχ` (right) of the counterflow sides read in `h`
  (`junction_height_leftT`, `junction_height_rightT`): `cLT θ κ σ = (3/2 + θ/π)(κ/2 − 2) − σ`,
  `cRT θ κ σ = (3/2 − θ/π)(κ/2 − 2) − σ`; at `θ = π/2` these are R57's `cL6`, `cR6` (`cLT_pi_div_two`,
  `cRT_pi_div_two`);
* `CfThetaBounds κ θ …`: the data of `h − θχ` satisfy Remark 4.1's bounds (`≤ −λ + π/2 χ` on `ℝ₋`, `≥ λ − π/2 χ` on
  `ℝ₊`), the hypothesis under which the counterflow of `h − θχ` is an admissible `SLE_{16/κ}(ρ′)` flow line (Remark 4.8
  (b)); it follows from (4.4) at `θ = π/2` (`cfThetaBounds_of_cond44`);
* `CfGlueAET θ Φ`: the glued setting of `Prop411Q.CfGlueAE` at relative angle `θ`;
* the θ-versions of the setting lemmas of PROVE-GLUECOND2/3/5/7 (counterflow regularity, the union of the two
  stopped hulls is local, the marked history-avoidance criterion, the good-sample sets), each with the landed proof
  read with `h − θχ` in place of `h − π/2 χ`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CrossCond.Theta

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond MartChar.RealFlow Cond44Ref CfRegQ Prop411Q WholeField Word49
open LocalSets (IsLocalSetMean)
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-! ### The counterflow field at relative angle `θ` and its centring -/

section Field

/-- **The counterflow field at relative angle `θ`**: `h − θχ` (at `θ = π/2` the landed `cfField`). -/
def cfFieldT (κ θ : ℝ) (f : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  Exist.flowField 0 (-(θ * chiC κ)) f

theorem measurable_cfFieldT (κ θ : ℝ) : Measurable (cfFieldT κ θ) := Exist.measurable_flowField 0 _

theorem cfFieldT_pi_div_two (κ : ℝ) : cfFieldT κ (π / 2) = cfField κ := rfl

/-- **The centring at relative angle `θ`**: `cenTT κ θ u₀ (h − θχ) = h − u₀`. -/
def cenTT (κ θ : ℝ) (u₀ : ℂ → ℝ) (f : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  Exist.flowField 0 (θ * chiC κ) f - smoothDist upperHalfPlaneOpens u₀

/-- The inverse of `cenTT κ θ u₀`. -/
def cenTT' (κ θ : ℝ) (u₀ : ℂ → ℝ) (g : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  cfFieldT κ θ (g + smoothDist upperHalfPlaneOpens u₀)

theorem cenTT_pi_div_two (κ : ℝ) : cenTT κ (π / 2) = cenT κ := rfl

theorem measurable_cenTT (κ θ : ℝ) (u₀ : ℂ → ℝ) : Measurable (cenTT κ θ u₀) :=
  (WholeField.measurable_sub_dist _).comp (Exist.measurable_flowField 0 _)

theorem measurable_cenTT' (κ θ : ℝ) (u₀ : ℂ → ℝ) : Measurable (cenTT' κ θ u₀) :=
  (measurable_cfFieldT κ θ).comp (Coupling.measurable_add_distOnConst _)

theorem cenTT_cfFieldT (κ θ : ℝ) (u₀ : ℂ → ℝ) (f : DistOn upperHalfPlaneOpens) :
    cenTT κ θ u₀ (cfFieldT κ θ f) = f - smoothDist upperHalfPlaneOpens u₀ := by
  rw [cenTT, cfFieldT, flowField_zero_flowField_zero, add_neg_cancel, flowField_zero_zero]

theorem cenTT'_cenTT (κ θ : ℝ) (u₀ : ℂ → ℝ) (f : DistOn upperHalfPlaneOpens) :
    cenTT' κ θ u₀ (cenTT κ θ u₀ f) = f := by
  rw [cenTT', cenTT, sub_add_cancel, cfFieldT, flowField_zero_flowField_zero, neg_add_cancel, flowField_zero_zero]

theorem cenTT_eq_add_sub (κ θ : ℝ) (u₀ : ℂ → ℝ) (f : DistOn upperHalfPlaneOpens) :
    cenTT κ θ u₀ f = f + smoothDist upperHalfPlaneOpens (fun _ => θ * chiC κ) -
      smoothDist upperHalfPlaneOpens u₀ := by
  rw [cenTT, flowField_zero_eq_add]

/-- `cenTT κ θ u₀ f = f − (u₀ − θχ)`. -/
theorem cenTT_eq_sub (κ θ : ℝ) {u₀ : ℂ → ℝ} (hu₀ : ContinuousOn u₀ H) (f : DistOn upperHalfPlaneOpens) :
    cenTT κ θ u₀ f = f - smoothDist upperHalfPlaneOpens (fun z => u₀ z + -(θ * chiC κ)) := by
  rw [cenTT_eq_add_sub]
  ext φ
  have hc : ContinuousOn (fun z => u₀ z + -(θ * chiC κ)) H := hu₀.add continuousOn_const
  rw [sub_apply, add_apply, sub_apply, Coupling.smoothDist_apply_eq continuousOn_const,
    Coupling.smoothDist_apply_eq hu₀, Coupling.smoothDist_apply_eq hc]
  have h1 := Coupling.MartMeans2.integrable_mul_test_of_continuousOn hu₀ φ φ.tsupport_subset
  have h2 := Coupling.MartMeans2.integrable_mul_test_of_continuousOn (f := fun _ => θ * chiC κ)
    continuousOn_const φ φ.tsupport_subset
  have e : (∫ z, (u₀ z + -(θ * chiC κ)) * φ z) = (∫ z, u₀ z * φ z) - ∫ z, (θ * chiC κ) * φ z := by
    rw [← integral_sub h1 h2]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [e]
  ring

end Field

/-! ### The admissibility hypothesis and the glued setting at relative angle `θ` -/

section Setting

/-- **The counterflow of `h − θχ` is admissible**: the data of `h − θχ` satisfy Remark 4.1's bounds (`≤ −λ + π/2 χ`
left of `0`, `≥ λ − π/2 χ` right of `0`), so that its counterflow from `∞` is the flow line of an admissible word at
`16/κ` (Remark 4.8 (b), `counterflowData_bounds`). At `θ = π/2` this follows from (4.4) (`cfThetaBounds_of_cond44`). -/
def CfThetaBounds (κ θ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    Prop :=
  (∀ x : ℝ, x < 0 → forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ) ≤ -sleLambda κ + π / 2 * chiC κ) ∧
    ∀ x : ℝ, 0 < x → sleLambda κ - π / 2 * chiC κ ≤ forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)

/-- (4.4) gives the admissibility hypothesis at the landed relative angle `π/2`. -/
theorem cfThetaBounds_of_cond44 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (h44 : Sec4.Cond44 κ ρL ρR) : CfThetaBounds κ (π / 2) ρL ρR xL xR := by
  obtain ⟨hbL, hbR⟩ := Sec4.forceBoundaryData_bounds_of_cond44 hκ hκ4 hF h44
  exact ⟨fun x hx => by linarith [hbL x hx], fun x hx => by linarith [hbR x hx.le]⟩

/-- **The glued setting at relative angle `θ`** (`Prop411Q.CfGlueAE` with the counterflow of `h − θχ`): for
`0 < κ < 4`, an ordered (4.4) word whose shifted data satisfy `CfThetaBounds`, an optional hull coupling `(h, W, …)` on
`Ω`, a centred counterflow coupling on `Ω₂` whose field has the law of `h − θχ`, and a regular conditional law `k` of
    its
killed history given its field, the property `Φ` of the flow line and the counterflow history holds almost surely on the
glued space. -/
def CfGlueAET (θ : ℝ) (Φ : (ℝ → ℂ) → HistorySpace 0 0 → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → Sec4.Cond44 κ ρL ρR → CfThetaBounds κ θ ρL ρR xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
      P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂ →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
        P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
        ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
          Φ (seedLine ζ W p.1) p.2

/-- At `θ = π/2` the θ-setting gives the landed setting. -/
theorem cfGlueAE_of_cfGlueAET {Φ : (ℝ → ℂ) → HistorySpace 0 0 → Prop} (hΦ : CfGlueAET.{u} (π / 2) Φ) :
    CfGlueAE.{u} Φ := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44
  exact hΦ κ hκ hκ4 xL xR ρL ρR hF h44 (cfThetaBounds_of_cond44 hκ hκ4 hF h44)

/-- **(4.4) at relative angle `θ`** (a sufficient condition for `CfThetaBounds`): the left partial sums of the flow
word are at least `(1/2 + θ/π)(κ/2 − 2)` and the right ones at least `(θ/π − 1/2)(2 − κ/2)`. At `θ = π/2` these bounds
are `κ/2 − 2` and `0`, i.e. (4.4). -/
def Cond44T (κ θ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  (∀ j : ℕ, 1 ≤ j → j ≤ nL →
      (1 / 2 + θ / π) * (κ / 2 - 2) ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin nL => i.val < j), ρL i) ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ nR →
      (θ / π - 1 / 2) * (2 - κ / 2) ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin nR => i.val < j), ρR i

/-- A right prefix of an ordered word has partial sum at least `c ≤ 0` if every nonempty index prefix does. -/
theorem le_sum_filter_xR_le {nR : ℕ} {xR ρR : Fin nR → ℝ} (hxR : Monotone xR) {c : ℝ} (hc : c ≤ 0)
    (hS : ∀ j : ℕ, 1 ≤ j → j ≤ nR → c ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin nR => i.val < j), ρR i)
    (x : ℝ) : c ≤ ∑ i ∈ Finset.univ.filter (fun i => xR i ≤ x), ρR i := by
  have hdown : ∀ i i' : Fin nR, i' ≤ i → xR i ≤ x → xR i' ≤ x := fun i i' hii' hi =>
    (hxR hii').trans hi
  rw [Sec4.filter_eq_filter_val_lt_card hdown]
  rcases Nat.eq_zero_or_pos (Finset.univ.filter fun i => xR i ≤ x).card with h0 | hpos
  · rw [h0]
    simpa using hc
  · exact hS _ hpos ((Finset.card_filter_le _ _).trans (by simp))

/-- **(4.4) at relative angle `θ ∈ [−π/2, π/2]` gives the admissibility hypothesis `CfThetaBounds`.** -/
theorem cfThetaBounds_of_cond44T {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (h : Cond44T κ θ ρL ρR) : CfThetaBounds κ θ ρL ρR xL xR := by
  have hL := Sec4.sleLambda_pos hκ
  have hπχ := Sec4.pi_mul_chiC hκ
  have hπ := Real.pi_pos
  have hθπ₁ : 0 ≤ 1 / 2 + θ / π := by
    have : -(1 / 2 : ℝ) ≤ θ / π := by rw [le_div_iff₀ hπ]; linarith
    linarith
  have hθπ₂ : θ / π - 1 / 2 ≤ 0 := by
    have : θ / π ≤ 1 / 2 := by rw [div_le_iff₀ hπ]; linarith
    linarith
  have e1 : θ * chiC κ = θ / π * ((2 - κ / 2) * sleLambda κ) := by rw [← hπχ]; field_simp
  have e2 : π / 2 * chiC κ = 1 / 2 * ((2 - κ / 2) * sleLambda κ) := by rw [← hπχ]; ring
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [Sec4.forceBoundaryData_of_neg ρL ρR xL xR hx, e1, e2]
    have hS : (1 / 2 + θ / π) * (κ / 2 - 2) ≤ ∑ i ∈ Finset.univ.filter (fun i => x < xL i), ρL i := by
      by_cases hne : ∃ i, x < xL i
      · have h' := Sec4.sum_filter_lt_xL_ge_of_cond44 (κ := 2 * ((1 / 2 + θ / π) * (κ / 2 - 2)) + 4) (ρL := ρL) hF.1
          (fun j h1 h2 => by linarith [h.1 j h1 h2]) hne
        linarith
      · push Not at hne
        rw [Finset.filter_false_of_mem fun i _ => not_lt.2 (hne i), Finset.sum_empty]
        nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hS hL.le]
  · rw [Sec4.forceBoundaryData_of_nonneg ρL ρR xL xR hx.le, e1, e2]
    have hS := le_sum_filter_xR_le hF.2.2.1 (by nlinarith) h.2 x
    nlinarith [mul_le_mul_of_nonneg_left hS hL.le]

/-- **Non-vacuity of `CfThetaBounds`**: the word without force points satisfies it at every `θ ∈ [−π/2, π/2]`. -/
theorem cfThetaBounds_elim0 {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2) :
    CfThetaBounds κ θ (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → ℝ) :=
  cfThetaBounds_of_cond44T hκ hκ4 hθ₁ hθ₂ ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    ⟨fun j h1 h2 => absurd (h1.trans h2) (by omega), fun j h1 h2 => absurd (h1.trans h2) (by omega)⟩

end Setting

/-! ### The counterflow of `h − θχ` is an admissible flow line at `16/κ` (Remark 4.8 (b)) -/

section Counterflow

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- θ-version of `exists_admissible_of_isCenteredCounterflowDriver` (`Sec5.CfRegQ`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem exists_admissible_of_isCenteredCounterflowDriverT [IsProbabilityMeasure P₂] (hκ : 0 < κ) (hθb : CfThetaBounds
    κ θ ρL ρR xL xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂) :
    ∃ (mL mR : ℕ) (yL : Fin mL → ℝ) (yR : Fin mR → ℝ) (σL : Fin mL → ℝ) (σR : Fin mR → ℝ)
      (𝓕₂ : Filtration ℝ≥0 _mΩ₂) (VL₂ : Fin mL → ℝ≥0 → Ω₂ → ℝ) (VR₂ : Fin mR → ℝ≥0 → Ω₂ → ℝ)
      (B₂ : ℝ≥0 → Ω₂ → ℝ), IsOrderedForceWord yL yR ∧ Sec4.HasAdmissiblePartialSums (16 / κ) σL σR yL yR ∧
        IsIntegratedSLEEvolution (16 / κ) yL yR σL σR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ := by
  set c : ℝ := -(θ * chiC κ) with hc
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + c with hbdef
  have hb : IsPiecewiseConstantBoundaryData b (forceJumpFinset xL xR) := isPiecewiseConstant_forceData κ ρL ρR xL xR c
  have hh : IsGFFWithBoundaryData P h (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) := ⟨hC.2.1, hC.2.2.1⟩
  have hh' := isGFFWithBoundaryData_flowField_zero hh c
  rw [← coe_forceJumpFinset] at hh'
  have hh'' : IsGFFWithBoundaryData P (fun ω => cfFieldT κ θ (h ω)) b (forceJumpFinset xL xR) := hh'
  have hh₂ := isGFFWithBoundaryData_of_map_eq hh'' (measurable_of_isCenteredCounterflowDriver hcf) hlaw
  obtain ⟨h', -, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hh₂ hcf
  obtain ⟨h'', 𝓕₂, VL₂, VR₂, B₂, -, hC'⟩ := hfl
  have hk' : 0 < 16 / κ := by positivity
  obtain ⟨hbL, hbR⟩ := hθb
  have hbd := counterflowData_bounds hκ (g := b) (fun x hx => hbL x hx) (fun x hx => hbR x hx)
  have hadm := Sec4.hasAdmissiblePartialSums_flowLine hk' (Sec7.StripSysField.isPiecewiseConstant_counterflowData κ hb)
    (fun x hx _ => hbd.1 x hx) (fun x hx _ => hbd.2 x hx)
  exact ⟨_, _, _, _, _, _, 𝓕₂, VL₂, VR₂, B₂, Theorem15.isOrderedForceWord_flowLine _ _ 0, hadm, hC'.1⟩

/-- θ-version of `ae_cfHistory_mem_goodCfSet` (`Sec5.CfRegQ`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem ae_cfHistory_mem_goodCfSetT [IsProbabilityMeasure P₂] (hκ : 0 < κ) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂) :
    ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodCfSet := by
  obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
    exists_admissible_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw
  have hk' : 0 < 16 / κ := by positivity
  filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE,
    hE.2.2.2.2] with ω ⟨hζ, _, η, hη⟩ hp
  have hw : Continuous fun t => W₂ t ω := by
    have := hp.2.2.2.1
    rw [hζ] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  exact cfHistory_mem_goodCfSet hζ hw hp.1 hη

/-- θ-version of `exists_seed_admissible_of_isCenteredCounterflowDriver` (`Sec5.GlueCondHit`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem exists_seed_admissible_of_isCenteredCounterflowDriverT [IsProbabilityMeasure P₂] (hκ : 0 < κ)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂) :
    ∃ (mL mR : ℕ) (yL : Fin mL → ℝ) (yR : Fin mR → ℝ) (σL : Fin mL → ℝ) (σR : Fin mR → ℝ)
      (𝓕₂ : Filtration ℝ≥0 _mΩ₂) (VL₂ : Fin mL → ℝ≥0 → Ω₂ → ℝ) (VR₂ : Fin mR → ℝ≥0 → Ω₂ → ℝ)
      (B₂ : ℝ≥0 → Ω₂ → ℝ), IsOrderedForceWord yL yR ∧ Sec4.HasAdmissiblePartialSums (16 / κ) σL σR yL yR ∧
        IsIntegratedSLEEvolution (16 / κ) yL yR σL σR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
          (∃ i, yL i = 0) ∧ ∃ i, yR i = 0 := by
  set c : ℝ := -(θ * chiC κ) with hc
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + c with hbdef
  have hb : IsPiecewiseConstantBoundaryData b (forceJumpFinset xL xR) := isPiecewiseConstant_forceData κ ρL ρR xL xR c
  have hh : IsGFFWithBoundaryData P h (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) := ⟨hC.2.1, hC.2.2.1⟩
  have hh' := isGFFWithBoundaryData_flowField_zero hh c
  rw [← coe_forceJumpFinset] at hh'
  have hh'' : IsGFFWithBoundaryData P (fun ω => cfFieldT κ θ (h ω)) b (forceJumpFinset xL xR) := hh'
  have hh₂ := isGFFWithBoundaryData_of_map_eq hh'' (measurable_of_isCenteredCounterflowDriver hcf) hlaw
  obtain ⟨h', -, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hh₂ hcf
  obtain ⟨h'', 𝓕₂, VL₂, VR₂, B₂, -, hC'⟩ := hfl
  have hk' : 0 < 16 / κ := by positivity
  obtain ⟨hbL, hbR⟩ := hθb
  have hbd := counterflowData_bounds hκ (g := b) (fun x hx => hbL x hx) (fun x hx => hbR x hx)
  have hadm := Sec4.hasAdmissiblePartialSums_flowLine hk' (Sec7.StripSysField.isPiecewiseConstant_counterflowData κ hb)
    (fun x hx _ => hbd.1 x hx) (fun x hx _ => hbd.2 x hx)
  exact ⟨_, _, _, _, _, _, 𝓕₂, VL₂, VR₂, B₂, Theorem15.isOrderedForceWord_flowLine _ _ 0, hadm, hC'.1,
    ⟨_, Sec4.flowLineXL_zero _ _⟩, ⟨_, Sec4.flowLineXR_zero _ _⟩⟩

/-- θ-version of `ae_trace_ne_real_of_isCenteredCounterflowDriver` (`Sec5.GlueCondHit`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem ae_trace_ne_real_of_isCenteredCounterflowDriverT [IsProbabilityMeasure P₂] (hκ : 0 < κ) (hθb : CfThetaBounds κ
    θ ρL ρR xL xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂) :
    ∀ᵐ ω ∂P₂, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₂ t ω) ⊤ γ → ∀ t : ℝ≥0, ∀ x : ℝ, x ≠ 0 →
      γ t ≠ x := by
  obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE, ⟨iL, hiL⟩, ⟨iR, hiR⟩⟩ :=
    exists_seed_admissible_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw
  have hk' : 0 < 16 / κ := by positivity
  filter_upwards [CfAvoidLeftQ.ae_trace_ne_pos hk' hF' hadm hE, CfAvoidLeftQ.ae_trace_ne_neg hk' hF' hadm hE]
    with ω hR hL γ hγ t x hx
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · exact hL γ hγ t iL x hneg (by rw [hiL]; exact hneg.le)
  · exact hR γ hγ t iR x hpos (by rw [hiR]; exact hpos.le)

/-- θ-version of `ae_cfReg` (`Sec5.CrossCondMartFwd`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem ae_cfRegT [IsProbabilityMeasure P₂] (hκ : 0 < κ) (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hC :
    IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂) :
    ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω := by
  obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
    exists_admissible_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw
  have hk' : 0 < 16 / κ := by positivity
  filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE,
    hE.2.2.2.2] with ω ⟨hζ, _, η, hη⟩ hp
  have hw : Continuous fun t => W₂ t ω := by
    have := hp.2.2.2.1
    rw [hζ] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  exact ⟨hζ, hp.1, hw⟩

end Counterflow

/-! ### Almost-sure regularity on the glued space -/

section GlueAE

/-- θ-version of `cfGlueAE_mem_goodHitSet` (`Sec5.GlueCondHit`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem cfGlueAE_mem_goodHitSetT (θ : ℝ) : CfGlueAET.{u} θ fun _ y => y ∈ goodHitSet := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 hθb Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hΩ₂ : ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodHitSet := by
    obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
      exists_admissible_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw
    have hk' : 0 < 16 / κ := by positivity
    filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE,
      hE.2.2.2.2, ae_trace_ne_real_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw]
      with ω ⟨hζ, _, η, hη⟩ hp hne
    have hw : Continuous fun t => W₂ t ω := by
      have := hp.2.2.2.1
      rw [hζ] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    exact cfHistory_mem_goodHitSet hζ hw hp.1 hη fun t _ x hx => hne η hη t x hx
  exact ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf) (measurable_cfHistory hX₂) hlaw k hk
    measurableSet_goodHitSet hΩ₂

/-- θ-version of `cfGlueAE_exists_imageTrace` (`Sec5.GlueCondHit`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem cfGlueAE_exists_imageTraceT (θ : ℝ) : CfGlueAET.{u} θ fun η y => ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 < t →
    Disjoint (η '' Ioc 0 t) (negInv '' fwdHull (cfDrv y) s) →
    ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ T : ℝ, 0 < T ∧ ∃ η' : ℝ → ℂ, IsLoewnerTrace W' η' ∧
      IsProperArc η' ∧ fwdHull W' T = revChart (cfDrv y) s '' (η '' Ioc 0 t) ∧
        η' T = revChart (cfDrv y) s (η t) := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 hθb Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_glue_fst (μ := P) k hXm (ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1)
  filter_upwards [hline, cfGlueAE_mem_goodHitSetT θ κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂
    hcf hlaw k hk] with p ⟨_, ⟨η, hη, hseq⟩, hprop⟩ hy s hs t ht hdisj
  have hα : IsLoewnerTrace (fun r : ℝ => W r.toNNReal p.1) (seedLine ζ W p.1) := by
    rw [hseq]; exact isLoewnerTrace_of_isGeneratingTrace hη
  have hA := fwdHull_eq_image_Ioc hα hprop ht.le
  obtain ⟨-, hwc, hw0, -⟩ := reg_of_mem_goodCfSet hy.1
  obtain ⟨W', hW'c, hW'0, T, hT, η', h1, h2, h3, h4⟩ := exists_imageTrace hα hprop hwc hw0 hs
    (isClosed_negInv_fwdHull_of_mem_goodHitSet hy hs).1 ht (by rw [hA]; exact hdisj)
  exact ⟨W', hW'c, hW'0, T, hT, η', h1, h2, by rw [h3, hA], h4⟩

/-- θ-version of `cfGlueAE_isGood49` (`Sec5.CrossCondWord`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem cfGlueAE_isGood49T (θ : ℝ) (s : ℝ≥0) (hs : 0 < s) :
    CfGlueAET.{u} θ fun η y => IsProperArc η ∧ y ∈ goodSet49 s := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 hθb Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_glue_fst (μ := P) k hXm (ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1)
  have hΩ₂ : ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodSet49 s := by
    obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm', hE, ⟨iL, hiL⟩, ⟨iR, hiR⟩⟩ :=
      exists_seed_admissible_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw
    have hk' : 0 < 16 / κ := by positivity
    filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm' hE,
      hE.2.2.2.2, ae_trace_ne_real_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw]
      with ω ⟨hζ, hsep, η, hη⟩ hp hne
    have hw : Continuous fun t => W₂ t ω := by
      have := hp.2.2.2.1
      rw [hζ] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    exact cfHistory_mem_goodSet49 hp hζ hw hsep hiL hiR hη (fun t _ x hx => hne η hη t x hx) hs
  have h2 := ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf) (measurable_cfHistory hX₂) hlaw k hk
    (measurableSet_goodSet49 s) hΩ₂
  filter_upwards [hline, h2] with p hp1 hp2
  exact ⟨hp1.2.2, hp2⟩

end GlueAE

/-! ### The counterflow's own stopped record (on `Ω₂`) -/

section Omega2

variable {κ θ : ℝ} {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- θ-version of `cfShiftDist` (`Sec5.CrossCond`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
def cfShiftDistT (κ θ : ℝ) (u₀ : ℂ → ℝ) : DistOn upperHalfPlaneOpens :=
  smoothDist upperHalfPlaneOpens u₀ - smoothDist upperHalfPlaneOpens (retShift (-(π * chiC κ)) (chiC (16 / κ))) -
    smoothDist upperHalfPlaneOpens (fun _ => θ * chiC κ)

/-- θ-version of `isHarmonicDistOn_cfShiftDist` (`Sec5.CrossCond`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem isHarmonicDistOn_cfShiftDistT (κ θ : ℝ) {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) :
    IsHarmonicDistOn (cfShiftDistT κ θ u₀) H :=
  LocalSets.IsHarmonicDistOn.sub' QuantumZipper.isOpen_H
    (LocalSets.IsHarmonicDistOn.sub' QuantumZipper.isOpen_H (isHarmonicDistOn_smoothDist hu₀)
      (isHarmonicDistOn_smoothDist (harmonicOnNhd_retShift _ _)))
    (isHarmonicDistOn_smoothDist fun _ _ => InnerProductSpace.harmonicAt_const _)

/-- θ-version of `cenT_eq_reflectField_sub` (`Sec5.CrossCond`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem cenTT_eq_reflectField_sub (κ θ : ℝ) (u₀ : ℂ → ℝ) {f f' : DistOn upperHalfPlaneOpens}
    (htr : IsChartTransport infinitySourceChart (-1) (-(π * chiC κ)) (chiC (16 / κ)) f f') :
    cenTT κ θ u₀ f = reflectField f' - cfShiftDistT κ θ u₀ := by
  rw [cenTT_eq_add_sub, Theorem14.GW2Cone.eq_returnField_of_isChartTransport htr, returnField_eq_reflectField_add,
    cfShiftDistT]
  abel

/-- θ-version of `isHistoryAvoidanceLocal_cfHullQ` (`Sec5.CrossCond`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem isHistoryAvoidanceLocal_cfHullQT (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hκ : 0 < κ)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (t : ℝ≥0) :
    IsHistoryAvoidanceLocal (MeasurableSpace.comap (cfHistory W₂ ζ₂) (stopSigma t))
      (fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω)) (fun ω => cenTT κ θ u₀ (h₂ ω)) P₂ := by
  have hX₀ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  obtain ⟨b', J', h', -, htr, hfl⟩ := hcf
  obtain ⟨h'', 𝓕, VL, VR, B, htac, hC⟩ := hfl
  have e : h'' = h' := funext fun ω =>
    Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htac ω)
  subst e
  have hX := hC.2.2.2.1
  have hτ := isStoppingTime_const (drivingFiltration P₂ hX) t
  have hτζ : ∀ᵐ ω ∂P₂, (((fun _ : Ω₂ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ₂ ω := by
    filter_upwards [hreg₂] with ω hω
    rw [hω.1]
    exact ENNReal.coe_lt_top
  have hloc := isHistoryAvoidanceLocal_reflect_hull hC (by positivity) (isHarmonicDistOn_cfShiftDistT κ θ hu₀) hX hτ
    hτζ (A := fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω)) ((measurable_cfHullQ t).comp (measurable_cfHistory hX₀))
    (by
      filter_upwards [hreg₂] with ω hω
      rw [cfHullQ, hullAt_cfHistory hω.1 hω.2.1 hω.2.2, WithTop.untopD_coe])
  have hf : (fun ω => cenTT κ θ u₀ (h₂ ω)) = fun ω => reflectField (h'' ω) - cfShiftDistT κ θ u₀ :=
    funext fun ω => cenTT_eq_reflectField_sub κ θ u₀ (htr ω)
  rw [hf]
  exact IsHistoryAvoidanceLocal.mono_marks hloc ((comap_cfHistory_stopSigma_le P₂ hX t).trans
    (IsStoppingTime.measurableSpace_const _ _).symm.le)

end Omega2

/-! ### The flow line's own stopped record (on `Ω`) -/

section Omega

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}

/-- θ-version of `isHistoryAvoidanceLocal_hullAt_flow` (`Sec5.CrossCond`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem isHistoryAvoidanceLocal_hullAt_flowT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q : ℝ≥0) :
    IsHistoryAvoidanceLocal (MeasurableSpace.comap (killedHistory W VL VR ζ) (stopSigma q))
      (fun ω => hullAt q (killedHistory W VL VR ζ ω)) (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P := by
  have hX := hC.2.2.2.1
  have hτ := isStoppingTime_const (drivingFiltration P hX) q
  have hτζ : ∀ᵐ ω ∂P, (((fun _ : Ω => ((q : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hloc := isHistoryAvoidanceLocal_hull hC hκ hu₀ hX hτ hτζ
    (A := fun ω => hullAt q (killedHistory W VL VR ζ ω)) ((measurable_hullAt q).comp (measurable_killedHistory hX))
    (by
      filter_upwards [Aux50Hit.ae_isGoodPath hC.1 hζ] with ω hg
      rw [WithTop.untopD_coe]
      exact Aux50Hit.regHull_stopHistory_cstop hg q)
  have hf : centredField h u₀ = fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω)) :=
    funext fun ω => (cenTT_cfFieldT κ θ u₀ (h ω)).symm
  rw [hf] at hloc
  exact IsHistoryAvoidanceLocal.mono_marks hloc ((comap_stopSigma_le (P := P) hX q).trans
    (IsStoppingTime.measurableSpace_const _ _).symm.le)

end Omega

/-! ### The revealed union on the glued space -/

section Glue

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}

omit [IsProbabilityMeasure P] in
/-- θ-version of `comap_cenT_glue` (`Sec5.CrossCond`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem comap_cenTT_glue (κ θ : ℝ) (u₀ : ℂ → ℝ) (X : Ω → DistOn upperHalfPlaneOpens) :
    MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (X p.1)) inferInstance =
      MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => X p.1) inferInstance := by
  refine le_antisymm ?_ ?_
  · change MeasurableSpace.comap (cenTT κ θ u₀ ∘ fun p : Ω × HistorySpace 0 0 => X p.1) _ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_cenTT κ θ u₀).comap_le
  · calc MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => X p.1) inferInstance
        = MeasurableSpace.comap (cenTT' κ θ u₀ ∘ fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (X p.1))
            inferInstance := by
          congr 1
          funext p
          exact (cenTT'_cenTT κ θ u₀ (X p.1)).symm
      _ ≤ _ := by
          rw [← MeasurableSpace.comap_comp]
          exact MeasurableSpace.comap_mono (measurable_cenTT' κ θ u₀).comap_le

/-- θ-version of `isHistoryAvoidanceLocal_cfGlue` (`Sec5.CrossCond`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem isHistoryAvoidanceLocal_cfGlueT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q t : ℝ≥0) :
    IsHistoryAvoidanceLocal (cfGlueMarks W VL VR ζ q t)
      (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
      (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  have hX := hC.2.2.2.1
  have hX₀ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hh₂m := CfRegQ.measurable_of_isCenteredCounterflowDriver hcf
  have hXm₀ : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hXm : Measurable fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω)) := (measurable_cenTT κ θ u₀).comp hXm₀
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hY₂m : Measurable (cfHistory W₂ ζ₂) := measurable_cfHistory hX₀
  have hX₂m : Measurable fun ω => cenTT κ θ u₀ (h₂ ω) := (measurable_cenTT κ θ u₀).comp hh₂m
  -- the flow line's record, transported along `fst`
  have hlaw₁ : μ.map (fun p : Ω × HistorySpace 0 0 =>
      (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)), killedHistory W VL VR ζ p.1)) =
      P.map (fun ω => (cenTT κ θ u₀ (cfFieldT κ θ (h ω)), killedHistory W VL VR ζ ω)) := by
    rw [show (fun p : Ω × HistorySpace 0 0 => (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)), killedHistory W VL VR ζ p.1)) =
        (fun ω => (cenTT κ θ u₀ (cfFieldT κ θ (h ω)), killedHistory W VL VR ζ ω)) ∘ Prod.fst from rfl,
      ← Measure.map_map (hXm.prodMk hYm) measurable_fst, hμ, glueMeasure_fst k hXm₀]
  have hA₁ := isHistoryAvoidanceLocal_of_map_eq (𝔐 := stopSigma q) hXm hYm (hXm.comp measurable_fst)
    (hYm.comp measurable_fst) hlaw₁ (measurable_hullAt q) (stopSigma_le _)
    (isHistoryAvoidanceLocal_hullAt_flowT hC hκ hζ hu₀ q)
  -- the counterflow's record, transported along the law of `(h − π/2 χ, history)`
  have hlaw₂ : μ.map (fun p : Ω × HistorySpace 0 0 => (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)), p.2)) =
      P₂.map (fun ω => (cenTT κ θ u₀ (h₂ ω), cfHistory W₂ ζ₂ ω)) := by
    have hT : Measurable fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenTT κ θ u₀ r.1, r.2) :=
      ((measurable_cenTT κ θ u₀).comp measurable_fst).prodMk measurable_snd
    have hpair : Measurable fun p : Ω × HistorySpace 0 0 => (cfFieldT κ θ (h p.1), p.2) :=
      (hXm₀.comp measurable_fst).prodMk measurable_snd
    have hpair₂ : Measurable fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω) := hh₂m.prodMk hY₂m
    rw [show (fun p : Ω × HistorySpace 0 0 => (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)), p.2)) =
        (fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenTT κ θ u₀ r.1, r.2)) ∘
          fun p => (cfFieldT κ θ (h p.1), p.2) from rfl,
      show (fun ω => (cenTT κ θ u₀ (h₂ ω), cfHistory W₂ ζ₂ ω)) =
        (fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenTT κ θ u₀ r.1, r.2)) ∘
          fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω) from rfl,
      ← Measure.map_map hT hpair, ← Measure.map_map hT hpair₂, hμ, glueMeasure_map_pair hXm₀ k, hlaw, hk]
  have hA₂ := isHistoryAvoidanceLocal_of_map_eq (𝔐 := stopSigma t) hX₂m hY₂m (hXm.comp measurable_fst)
    measurable_snd hlaw₂ (measurable_cfHullQ t) (stopSigma_le _)
    (isHistoryAvoidanceLocal_cfHullQT hcf hκ hreg₂ hu₀.1 t)
  -- the union
  have hci := condIndepEv_glue_fst (μ := P) k hXm₀
  rw [← comap_cenTT_glue κ θ u₀ (fun ω => cfFieldT κ θ (h ω))] at hci
  have hℋ₁ : MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => killedHistory W VL VR ζ p.1)
      (stopSigma q) ≤ MeasurableSpace.comap Prod.fst mΩ := by
    rw [show (fun p : Ω × HistorySpace 0 0 => killedHistory W VL VR ζ p.1) =
      killedHistory W VL VR ζ ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ((MeasurableSpace.comap_mono (stopSigma_le _)).trans hYm.comap_le)
  have hℋ₂ : MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => p.2) (stopSigma t) ≤
      MeasurableSpace.comap Prod.snd inferInstance :=
    MeasurableSpace.comap_mono (stopSigma_le _)
  exact isHistoryAvoidanceLocal_union measurable_fst.comap_le measurable_snd.comap_le hℋ₁ hℋ₂
    (((measurable_hullAt q).comp hYm).comp (comap_measurable Prod.fst))
    ((measurable_cfHullQ t).comp (comap_measurable Prod.snd)) hci hA₁ hA₂

omit [IsProbabilityMeasure P] in
/-- θ-version of `isLocalSet_hullAt_flow` (`Sec5.GlueCond`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem isLocalSet_hullAt_flowT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q : ℝ≥0) :
    IsLocalSet (fun ω => hullAt q (killedHistory W VL VR ζ ω)) (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P := by
  obtain ⟨hX, hker⟩ := hC.2.2.2
  have hτζ : ∀ᵐ ω ∂P, (((fun _ : Ω => ((q : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hK := (hker (fun _ => ((q : ℝ≥0) : WithTop ℝ≥0)) (isStoppingTime_const _ q) hτζ).1
  have hK' : IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) (q : ℝ)) h P := by
    simpa only [WithTop.untopD_coe] using hK
  have hA := WholeField.IsLocalSet.sub_dist hK' (WholeField.isHarmonicDistOn_smoothDist hu₀.1)
  have e : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = fun ω => h ω - smoothDist upperHalfPlaneOpens u₀ :=
    funext fun ω => cenTT_cfFieldT κ θ u₀ (h ω)
  rw [e]
  refine Coupling.IsLocalSet.congr_set hA ?_
  filter_upwards [Aux50Hit.ae_isGoodPath hC.1 hζ] with ω hg
  exact Aux50Hit.regHull_stopHistory_cstop hg q

omit [IsProbabilityMeasure P₂] in
/-- θ-version of `isLocalSet_cfHullQ_cenT` (`Sec5.GlueCond`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem isLocalSet_cfHullQ_cenTT (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (t : ℝ≥0) :
    IsLocalSet (fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω)) (fun ω => cenTT κ θ u₀ (h₂ ω)) P₂ := by
  have hc : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens (fun _ => θ * chiC κ)) H :=
    WholeField.isHarmonicDistOn_smoothDist fun _ _ => InnerProductSpace.harmonicAt_const _
  have h1 := WholeField.IsLocalSet.sub_dist (Coupling.IsLocalSet.add_dist (isLocalSet_cfHullQ hcf hreg₂ t) hc)
    (WholeField.isHarmonicDistOn_smoothDist hu₀)
  have e : (fun ω => cenTT κ θ u₀ (h₂ ω)) = fun ω => h₂ ω + smoothDist upperHalfPlaneOpens (fun _ => θ * chiC κ) -
      smoothDist upperHalfPlaneOpens u₀ := funext fun ω => cenTT_eq_add_sub κ θ u₀ (h₂ ω)
  rw [e]
  exact h1

/-- θ-version of `isLocalSet_union_glue` (`Sec5.GlueCond`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem isLocalSet_union_glueT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q t : ℝ≥0) :
    IsLocalSet (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1))
        (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) ∧
      IsLocalSet (fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2) (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) ∧
      IsLocalSet (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
        (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) := by
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hAm : Measurable[mΩ, hittingSigma] fun ω => hullAt q (killedHistory W VL VR ζ ω) :=
    (measurable_hullAt q).comp (measurable_killedHistory hX)
  have hAg := IsLocalSet.glue_fst hXm k (T := cenTT κ θ u₀) (isLocalSet_hullAt_flowT hC hζ hu₀ q)
  have hGg := IsLocalSet.glue_snd hXm k (CfRegQ.measurable_of_isCenteredCounterflowDriver hcf)
    (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)) hlaw hk
    (measurable_cenTT κ θ u₀) (measurable_cfHullQ t) MeasurableSet.univ (fun y _ => cfHullQ_relClosed t y)
    (Eventually.of_forall fun _ => mem_univ _) (isLocalSet_cfHullQ_cenTT hcf hreg₂ hu₀.1 t)
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P := by
    have e : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = WholeField.centredField h u₀ :=
      funext fun ω => cenTT_cfFieldT κ θ u₀ (h ω)
    rw [e]
    exact WholeField.isZeroBoundaryGFF_centredField hC hu₀
  exact ⟨hAg, hGg, IsLocalSet.glue_union hXm k (measurable_cenTT κ θ u₀) (measurable_cenTT' κ θ u₀) (cenTT'_cenTT κ θ
      u₀)
    hF hAm (measurable_cfHullQ t) hAg hGg⟩

/-- θ-version of `isZeroBoundaryGFF_cenT_glue` (`Sec5.CrossCondLaw`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem isZeroBoundaryGFF_cenTT_glue (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h
        p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) := by
  have hXm₀ : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have e : (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) =
      fun p => centredField h u₀ p.1 := funext fun p => cenTT_cfFieldT κ θ u₀ (h p.1)
  rw [e]
  exact isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => centredField h u₀ ω) (f := Prod.fst) measurable_fst
    (glueMeasure_fst (μ := P) k hXm₀) (isZeroBoundaryGFF_centredField hC hu₀)

end Glue

end InteractingSLE.Sec5.CrossCond.Theta
