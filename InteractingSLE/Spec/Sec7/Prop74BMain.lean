/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Prop74BChart
import InteractingSLE.Spec.Sec7.Lemma71KData
import InteractingSLE.Spec.Sec7.Prop74OrderPocket
import InteractingSLE.Spec.Jordan.Transport
import InteractingSLE.Spec.Sobolev.GFFRegularity

/-!
# Proposition 7.4's last input: Lemma 7.1 for two middle curves in one pocket, from the fixed-chart Lemma 7.1

Packet PROVE-PROP74B. Specification p. 243 ("Applying the same component-pair construction simultaneously to finitely
many middle flow lines"), §7.1 setup, Lemma 7.1 and its proof (pp. 221–225), Figure 7.1.

`Prop74Pocket.Lemma71TwoMiddleStatement` (PROVE-PROP74's named input) asks, on every four-curve space, for **one**
pocket chart `ψ` between the outer curves `β = η_{α₂}`, `α = η_{α₁}` and one pulled-back field `h_ψ` such that the
mapped segments of **both** middle curves `γᵢ = η_{θᵢ}` are the angle-`θᵢ` flow lines of `h_ψ`. It is derived here from
Lemma 7.1 for **one** middle curve and a **given** chart (`Lemma71FixedChartStatement`, the named input), applied twice:

1. **The angle shift** (`Prop74BShift`): `(h + θᵢχ, β, α, γᵢ)` is a three-curve space.
2. **One chart** (PROVE-LEMMA71K): the canonical wall-pair chart `cw (β, α)` (`Lemma71K.exists_isWallPairChart`) gives
   a pocket construction on both three-curve spaces (`Lemma71K.isPocketConstruction_of_wallPairChart`) with the same
   pocket and chart, because they are read off the outer curves.
3. **The fixed-chart Lemma 7.1** on each: for a `σ(β, α)`-measurable branch shift `nᵢ` (the inherited branch), the
   mapped segment is the zero-angle flow line of the pulled-back field of `h + θᵢχ`, which is `h_ψ + θᵢχ`
   (`chartField_flowField`); so it is the angle-`θᵢ` flow line of `h_ψ` (`isFlowLine_shift_iff`). The pulled-back field
   is independent of the outer curves.
4. **The same branch** (`ae_eq_zero_of_isGFFWithBoundaryData_flowField`): the two pulled-back fields of `h` differ by
   `2π(n₂ − n₁)χ`, a `σ(β, α)`-measurable constant, and both are GFFs with the same data, one of them independent of
   `σ(β, α)`; comparing second moments, `n₁ = n₂` almost surely.
5. **The inverse chart on `ℍ̄`** (`Prop74BChart`) and the image relation `G (range η'ᵢ) = range γᵢ ∩ G(ℍ̄)` from the
   construction's `γ'ᵢ([0, ∞)) = Ψ(cayley(range γᵢ) ∩ E)`.

## Main results

* `chartField_flowField`, `chartField_shiftLift`: the pulled-back field under the shifts of the field and of the lift;
* `ae_eq_zero_of_isGFFWithBoundaryData_flowField`: a random constant shift independent of a GFF and keeping its law is
  almost surely `0`;
* `Lemma71FixedChartStatement` (**named input**: Lemma 7.1 for one middle curve and a given pocket construction);
* **`lemma71TwoMiddleStatement_of_fixedChart`**: `Prop74Pocket.Lemma71TwoMiddleStatement` from the named input, the
  orientation input `PocketChartOrientationStatement`, and the inputs `Lemma71H.Cond44ReferenceStatement`,
  `Lemma71H.Prop55HalfPlaneStatement` of the three-curve space;
* **`prop74OrderStatement_of_fixedChart`**: Proposition 7.4's order (`Prop74OrderStatement`) through
  `Prop74Pocket.prop74OrderStatement_of_twoMiddle`.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Function
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar chiC)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec7.Prop74B

open Lemma71E (shiftLift)

/-! ### The pulled-back field under shifts -/

/-- **The pulled-back field of `h + s` is the pulled-back field of `h`, plus `s`** (the change of variables
`∫ pushTest φ = ∫ φ`, `Chart.integral_pushTest`). -/
theorem chartField_flowField {c : Chart} (hc : c.IsConformal) (a k s : ℝ) (h : DistOn upperHalfPlaneOpens) :
    Lemma71K.chartField c a k (Exist.flowField 0 s h) = Exist.flowField 0 s (Lemma71K.chartField c a k h) := by
  ext φ
  simp only [Lemma71K.chartField, hc, ↓reduceDIte]
  rw [Chart.chartTransport_apply', flowField_zero_apply, flowField_zero_apply, Chart.chartTransport_apply',
    Chart.integral_pushTest hc]
  ring

/-- **Shifting the lift by `2πn` adds `2πnk` to the pulled-back field.** -/
theorem chartField_shiftLift {c : Chart} (hc : c.IsConformal) (hl : ContinuousOn c.2.2 c.dom) (a k : ℝ) (n : ℤ)
    (h : DistOn upperHalfPlaneOpens) :
    Lemma71K.chartField (shiftLift c n) a k h =
      Exist.flowField 0 (2 * π * n * k) (Lemma71K.chartField c a k h) := by
  have hc' : (shiftLift c n).IsConformal := Lemma71E.isConformal_shiftLift hc n
  have hl₀ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H := hc.continuousOn_lift_inv hl
  have hℓ := Chart.locallyIntegrableOn_of_continuousOn hl₀
  have hℓ' := Chart.locallyIntegrableOn_of_continuousOn
    (hc'.continuousOn_lift_inv (Lemma71E.continuousOn_shiftLift hl n))
  ext φ
  simp only [Lemma71K.chartField, hc, hc', ↓reduceDIte]
  rw [Chart.chartTransport_apply hc' hℓ', flowField_zero_apply, Chart.chartTransport_apply hc hℓ]
  have hpt : Chart.pushTest hc' φ = Chart.pushTest hc φ := rfl
  have hi : Integrable (fun w => c.2.2 (c.2.1 w) * φ w) :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn (S := H) hl₀ φ φ.tsupport_subset
  have hφi : Integrable (fun x => φ x) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have e : (fun w => (shiftLift c n).2.2 ((shiftLift c n).2.1 w) * φ w) =
      fun w => c.2.2 (c.2.1 w) * φ w + (2 * π * n) * φ w := by
    funext w
    simp only [shiftLift]
    ring
  rw [hpt, e, integral_add hi (hφi.const_mul _), integral_const_mul]
  ring

/-! ### A random constant shift that keeps the law of a GFF -/

/-- A test function on `ℍ` with nonzero integral. -/
theorem exists_testOn_integral_ne_zero : ∃ φ : TestOn upperHalfPlaneOpens, ∫ w, φ w ≠ 0 := by
  have hK : IsCompact (closedBall Complex.I (1 / 2)) := isCompact_closedBall _ _
  have hKH : closedBall Complex.I (1 / 2) ⊆ (upperHalfPlaneOpens : Set ℂ) := fun z hz => by
    have h1 : |z.im - 1| ≤ 1 / 2 := by
      have := Complex.abs_im_le_norm (z - Complex.I)
      rw [Complex.sub_im, Complex.I_im] at this
      exact this.trans (mem_closedBall_iff_norm.1 hz)
    show (0 : ℝ) < z.im
    linarith [(abs_le.1 h1).1]
  obtain ⟨φ, hφ01, hφ1⟩ := Sobolev.exists_cutoff_testOn hK hKH
  refine ⟨φ, (ne_of_lt ?_).symm⟩
  have hφi : Integrable (fun x => φ x) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  rw [integral_pos_iff_support_of_nonneg (fun x => (hφ01 x).1) hφi]
  refine lt_of_lt_of_le (measure_closedBall_pos volume Complex.I (by norm_num : (0 : ℝ) < 1 / 2))
    (measure_mono fun z hz => ?_)
  rw [mem_support, hφ1 hz]
  exact one_ne_zero

section Shift

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Two zero-boundary GFF processes on `ℍ` have the same second moments (both are the Dirichlet-energy covariance). -/
theorem integral_sq_eq_of_isZBGFFProcess {X Y : TestOn upperHalfPlaneOpens → Ω → ℝ}
    (hX : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens X P) (hY : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens Y P)
    (φ : TestOn upperHalfPlaneOpens) : ∫ ω, X φ ω ^ 2 ∂P = ∫ ω, Y φ ω ^ 2 ∂P := by
  have hm : AEMeasurable (X φ) P := (hX.measurable φ).aemeasurable
  have hm' : AEMeasurable (Y φ) P := (hY.measurable φ).aemeasurable
  rw [← variance_of_integral_eq_zero hm (hX.centered φ), ← covariance_self hm, hX.covariance_eq φ φ,
    ← variance_of_integral_eq_zero hm' (hY.centered φ), ← covariance_self hm', hY.covariance_eq φ φ]

/-- **A random constant shift that is independent of a GFF and keeps its law is almost surely zero.** If `X` and
`X + d` are GFFs with the same boundary data and `d` is independent of `X`, then for a test `φ` with `∫ φ ≠ 0` the
pairings `X φ − m` and `X φ − m + d ∫ φ` have the same second moment, and the cross term vanishes by independence, so
`E[(d ∫ φ)²] = 0`. -/
theorem ae_eq_zero_of_isGFFWithBoundaryData_flowField {X : Ω → DistOn upperHalfPlaneOpens} {d : Ω → ℝ}
    {g : ℝ → ℝ} {S : Set ℝ} {u : ℂ → ℝ} (hu : IsBoundedHarmonicExtension g S u)
    (hX : IsGFFWithBoundaryData P X g S) (hY : IsGFFWithBoundaryData P (fun ω => Exist.flowField 0 (d ω) (X ω)) g S)
    (hind : IndepFun X d P) : d =ᵐ[P] 0 := by
  obtain ⟨φ, hφ⟩ := exists_testOn_integral_ne_zero
  have hXp := hX.2 u hu
  have hYp := hY.2 u hu
  set I := ∫ w, φ w with hI
  set m := ∫ z, u z * φ z with hm
  set Xφ : Ω → ℝ := fun ω => X ω φ - m with hXφ
  set Dφ : Ω → ℝ := fun ω => d ω * I with hDφ
  have hYeq : (fun ω => Exist.flowField 0 (d ω) (X ω) φ - m) = fun ω => Xφ ω + Dφ ω := by
    funext ω
    simp only [hXφ, hDφ, flowField_zero_apply]
    ring
  have hX2 : MemLp Xφ 2 P := (hXp.gaussian.hasGaussianLaw_eval φ).memLp (by norm_num)
  have hY2 : MemLp (fun ω => Xφ ω + Dφ ω) 2 P := by
    rw [← hYeq]
    exact (hYp.gaussian.hasGaussianLaw_eval φ).memLp (by norm_num)
  have hD2 : MemLp Dφ 2 P := by
    have h1 := hY2.sub hX2
    have e : (fun ω => Xφ ω + Dφ ω) - Xφ = Dφ := by
      funext ω
      simp
    rwa [e] at h1
  have hsq : ∫ ω, (Xφ ω + Dφ ω) ^ 2 ∂P = ∫ ω, Xφ ω ^ 2 ∂P := by
    have h1 := integral_sq_eq_of_isZBGFFProcess hYp hXp φ
    have e : ∀ ω, Exist.flowField 0 (d ω) (X ω) φ - m = Xφ ω + Dφ ω := fun ω => congrFun hYeq ω
    rw [← hm] at h1
    simp only [e] at h1
    exact h1
  have hind' : IndepFun Xφ Dφ P :=
    hind.comp ((LQGMetric.measurable_distOn_apply φ).sub_const m) (measurable_id.mul_const I)
  have hcross : ∫ ω, Xφ ω * Dφ ω ∂P = 0 := by
    have h1 := hind'.integral_mul_eq_mul_integral hX2.aestronglyMeasurable hD2.aestronglyMeasurable
    have h0 : ∫ ω, Xφ ω ∂P = 0 := hXp.centered φ
    simp only [Pi.mul_apply] at h1
    rw [h1, h0, zero_mul]
  have hint1 := hX2.integrable_sq
  have hint3 := hD2.integrable_sq
  have hintY := hY2.integrable_sq
  have hint2 : Integrable (fun ω => Xφ ω * Dφ ω) P := by
    have e : (fun ω => Xφ ω * Dφ ω) = fun ω => ((Xφ ω + Dφ ω) ^ 2 - Xφ ω ^ 2 - Dφ ω ^ 2) / 2 := by
      funext ω
      ring
    rw [e]
    exact ((hintY.sub hint1).sub hint3).div_const 2
  have hexp : ∫ ω, (Xφ ω + Dφ ω) ^ 2 ∂P =
      ∫ ω, Xφ ω ^ 2 ∂P + 2 * (∫ ω, Xφ ω * Dφ ω ∂P) + ∫ ω, Dφ ω ^ 2 ∂P := by
    have e : (fun ω => (Xφ ω + Dφ ω) ^ 2) = fun ω => Xφ ω ^ 2 + 2 * (Xφ ω * Dφ ω) + Dφ ω ^ 2 := by
      funext ω
      ring
    rw [e, integral_add (f := fun ω => Xφ ω ^ 2 + 2 * (Xφ ω * Dφ ω)) (g := fun ω => Dφ ω ^ 2)
      (hint1.add (hint2.const_mul 2)) hint3,
      integral_add (f := fun ω => Xφ ω ^ 2) (g := fun ω => 2 * (Xφ ω * Dφ ω)) hint1 (hint2.const_mul 2),
      integral_const_mul]
  have hD0 : ∫ ω, Dφ ω ^ 2 ∂P = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (Dφ ω)) hint3).1 hD0
  filter_upwards [hae] with ω hω
  have h1 : Dφ ω = 0 := pow_eq_zero_iff two_ne_zero |>.1 hω
  exact (mul_eq_zero.1 h1).resolve_right hφ

end Shift

/-! ### Null modifications of the field -/

section Congr

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **A local set stays a local set under a null modification of the field** (the frozen `IsLocalSet` is a statement
about the joint law of the set and the field). -/
theorem IsLocalSet.congr_field {A : Ω → Set ℂ} {h h₁ : Ω → DistOn upperHalfPlaneOpens} (hloc : IsLocalSet A h P)
    (he : h₁ =ᵐ[P] h) : IsLocalSet A h₁ P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hm, hA, Ω', mΩ', P', hP', A', g₁, g₂, hA'm, hg₁, hg₂, hA', hharm, hcond, hlaw⟩ := hloc
  have hpair : (fun ω => (A ω, h₁ ω)) =ᵐ[P] fun ω => (A ω, h ω) := he.mono fun ω hω => by simp only [hω]
  refine ⟨hm.congr hpair.symm, hA, Ω', mΩ', P', hP', A', g₁, g₂, hA'm, hg₁, hg₂, hA', hharm, hcond, ?_⟩
  rw [hlaw]
  exact Measure.map_congr hpair.symm

/-- **The optional hull coupling under a null modification of the field**, given the measurability and the Gaussian
clause of the new field. -/
theorem IsOptionalHullCoupling.congr_field {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h h₁ : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hh₁ : Measurable h₁)
    (hgff : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h₁ ω φ - ∫ z, u₀ z * φ z) P)
    (he : h₁ =ᵐ[P] h) : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h₁ := by
  obtain ⟨hE, -, -, hX, hcl⟩ := hC
  refine ⟨hE, hh₁, hgff, hX, fun τ hτ hτζ => ?_⟩
  obtain ⟨hloc, hce⟩ := hcl τ hτ hτζ
  refine ⟨IsLocalSet.congr_field hloc he, fun u hu φ => ?_⟩
  have hc : (fun ω' => Complex.exp (Complex.I * (h₁ ω' φ : ℂ))) =ᵐ[P]
      fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) := he.mono fun ω hω => by simp only [hω]
  filter_upwards [hce u hu φ, condExp_congr_ae (m := hτ.measurableSpace) hc] with ω h1 h2 hd
  rw [h2]
  exact h1 hd

/-- **A flow line of a field is a flow line of every null modification of it that is a GFF with the same data.** -/
theorem IsFlowLine.congr_field {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {x θ : ℝ} {h h₁ : Ω → DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLine κ b J x θ P h η ζ)
    (hh₁ : IsGFFWithBoundaryData P h₁ b J) (he : h₁ =ᵐ[P] h) : IsFlowLine κ b J x θ P h₁ η ζ := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hc, htrace⟩ := hfl
  have hG := Exist.isGFFWithBoundaryData_flowField hκ hb x θ hh₁
  have he' : (fun ω => Exist.flowField x (θ * chiC κ) (h₁ ω)) =ᵐ[P] h' := he.mono fun ω hω => by
    show Exist.flowField x (θ * chiC κ) (h₁ ω) = h' ω
    rw [hω, Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)]
  exact ⟨fun ω => Exist.flowField x (θ * chiC κ) (h₁ ω), 𝓕, W, VL, VR, B,
    fun ω => Exist.isTranslateAddConst_flowField x _ (h₁ ω), IsOptionalHullCoupling.congr_field hc hG.1 hG.2 he',
    htrace⟩

end Congr

/-! ### One inverse chart for both mapped segments -/

section Two

open Lemma71K (IsMarkedPocket wallPt)

/-- The forward map of a conformal chart is a conformal bijection of its domain onto `ℍ`. -/
theorem isConformalBijection_fwd {c : Chart} (hc : c.IsConformal) :
    IsConformalBijection c.1 (c.dom : Set ℂ) H :=
  ⟨hc.differentiableOn_fwd, fun _ hz => hc.fwd_mem hz, fun z₁ hz₁ z₂ hz₂ h12 => by
    rw [← hc.inv_fwd hz₁, ← hc.inv_fwd hz₂, h12], fun w hw => ⟨c.2.1 w, hc.inv_mem_dom hw, hc.2.2 w hw⟩⟩

/-- The data of a marked pocket chart with its boundary map and the image of a middle curve (the almost-sure clause
of `Lemma71K.IsPocketConstruction` at one `ω`). -/
def IsMarkedChartImage (R M : ℝ≥0 → ℂ) (C : Set ℂ) (c : Chart) (S : Set ℂ) : Prop :=
  ∃ (a' b' : ℝ) (Ψ : ℂ → ℂ), IsMarkedPocket R C a' b' ∧
    ContinuousOn Ψ (closure (cayley '' C) \ {wallPt R b'}) ∧ InjOn Ψ (closure (cayley '' C) \ {wallPt R b'}) ∧
    MapsTo Ψ (closure (cayley '' C) \ {wallPt R b'}) Hbar ∧ Ψ (wallPt R a') = 0 ∧
    Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {wallPt R b'}] (wallPt R b')) atTop ∧
    (∀ x ∈ C, c.1 x = Ψ (cayley x)) ∧ S = Ψ '' (cayley '' range M ∩ (closure (cayley '' C) \ {wallPt R b'}))

/-- **One inverse chart on `ℍ̄` for two mapped segments of one pocket chart** (deterministic). Given the marked
pocket data of the chart `c` of a component `C` between `R` and `L` for two middle curves `M₁`, `M₂` (with images
`S₁`, `S₂`), and the orientation input, there is `G` continuous and injective on `ℍ̄`, mapping `ℍ` into `ℍ`, the
negative half-line into `L`, the positive half-line into `R`, with `G Sᵢ = range Mᵢ ∩ G(ℍ̄)`. The two boundary maps
agree on `E` (they agree on the dense subset `cayley C`), and the marked times are those of `C`. -/
theorem exists_pocketInv_two (hor : PocketChartOrientationStatement) {R L M₁ M₂ : ℝ≥0 → ℂ} {C : Set ℂ}
    {c : Chart} (hR : Lemma71I.IsSimpleProper R) (hL : Lemma71I.IsSimpleProper L) (hLR : range L ⊆ closedLeftSide R)
    (hM₁ : ∀ t, 0 ≤ (M₁ t).im) (hM₂ : ∀ t, 0 ≤ (M₂ t).im) (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C)
    (hC : C ∈ betweenComponents (range R) (range L)) {S₁ S₂ : Set ℂ} (h₁ : IsMarkedChartImage R M₁ C c S₁)
    (h₂ : IsMarkedChartImage R M₂ C c S₂) :
    ∃ G : ℂ → ℂ, ContinuousOn G Hbar ∧ InjOn G Hbar ∧ MapsTo G H H ∧ (∀ x : ℝ, x < 0 → G x ∈ range L) ∧
      (∀ x : ℝ, 0 < x → G x ∈ range R) ∧ G '' S₁ = range M₁ ∩ G '' Hbar ∧ G '' S₂ = range M₂ ∩ G '' Hbar := by
  obtain ⟨a', b', Ψ, hM, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨf, hS₁⟩ := h₁
  obtain ⟨a'', b'', Ψ', hM', hΨc', -, -, -, -, hΨf', hS₂⟩ := h₂
  have hf : IsConformalBijection c.1 C H := hdom ▸ isConformalBijection_fwd hc
  have hCo : IsOpen C := hdom ▸ c.dom.isOpen
  have hCH : C ⊆ H := fun z hz => (subset_of_mem_betweenComponents hC hz).1
  have hor' := hor R L hR hL hLR C hC a' b' hM c.1 Ψ hf hΨc hΨi hΨH hΨ0 hΨinf hΨf
  obtain ⟨hGc, hGi, hGinv, hGneg, hGpos, hGimg⟩ :=
    pocketInv_boundary hR hL hLR hCo hC hM hf hΨc hΨi hΨH hΨ0 hΨinf hΨf hor'
  -- the marked times are those of `C`
  have hab : a'' = a' ∧ b'' = b' := by
    have e : Icc a'' b'' = Icc a' b' := hM'.2.2.2.1.symm.trans hM.2.2.2.1
    exact (Icc_eq_Icc_iff hM'.2.1.le).1 e
  rw [hab.2] at hΨc' hS₂
  -- the two boundary maps agree on `E`
  have hqC : ∀ x ∈ C, cayley x ≠ wallPt R b' := fun x hx h =>
    (subset_of_mem_betweenComponents hC hx).2 (Or.inl (mem_range_of_cayley_eq_toDisc hR.isProperCurve.2.2.1
      (mem_Hbar_of_mem_H (hCH hx)) h))
  have hUE : cayley '' C ⊆ closure (cayley '' C) \ {wallPt R b'} := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨subset_closure ⟨x, hx, rfl⟩, hqC x hx⟩
  have hEq : EqOn Ψ' Ψ (closure (cayley '' C) \ {wallPt R b'}) := by
    refine Set.EqOn.of_subset_closure (s := cayley '' C) ?_ hΨc' hΨc hUE sdiff_subset
    rintro _ ⟨x, hx, rfl⟩
    rw [← hΨf x hx, ← hΨf' x hx]
  have hS₂' : S₂ = Ψ '' (cayley '' range M₂ ∩ (closure (cayley '' C) \ {wallPt R b'})) := by
    rw [hS₂]
    exact image_congr fun y hy => hEq hy.2
  refine ⟨_, hGc, hGi, fun w hw => ?_, hGneg, hGpos, ?_, ?_⟩
  · rw [hGinv w hw (c.2.1 w) (hdom ▸ hc.inv_mem_dom hw) (hc.2.2 w hw)]
    exact hCH (hdom ▸ hc.inv_mem_dom hw)
  · rw [hS₁]
    exact hGimg (range M₁) (range_subset_iff.2 hM₁)
  · rw [hS₂']
    exact hGimg (range M₂) (range_subset_iff.2 hM₂)

end Two

/-! ### Back from the shifted field -/

section Back

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Back from the shifted field.** If `η` is the zero-angle flow line of `X + θχ` with the shifted pocket data
`((α₂ − θ)χ − λ, −λ − (α₁ − θ)χ)`, then `η` is the angle-`θ` flow line of `X` with the data `(α₂χ − λ, −λ − α₁χ)`,
and `X` is a GFF with these data. -/
theorem isFlowLine_of_shift {κ α₁ α₂ θ : ℝ} (hκ : 0 < κ) {X : Ω → DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine κ (prop74Data ((α₂ - θ) * chiC κ - sleLambda κ) (-sleLambda κ - (α₁ - θ) * chiC κ)) {0} 0 0
      P (fun ω => Exist.flowField 0 (θ * chiC κ) (X ω)) η ζ) :
    IsFlowLine κ (prop74Data (α₂ * chiC κ - sleLambda κ) (-sleLambda κ - α₁ * chiC κ)) {0} 0 θ P X η ζ ∧
      IsGFFWithBoundaryData P X (prop74Data (α₂ * chiC κ - sleLambda κ) (-sleLambda κ - α₁ * chiC κ))
        ((({0} : Finset ℝ)) : Set ℝ) := by
  have e1 : α₂ * chiC κ - sleLambda κ - θ * chiC κ = (α₂ - θ) * chiC κ - sleLambda κ := by ring
  have e2 : -sleLambda κ - α₁ * chiC κ + θ * chiC κ = -sleLambda κ - (α₁ - θ) * chiC κ := by ring
  refine ⟨?_, ?_⟩
  · rw [isFlowLine_shift_iff (θ₀ := θ), sub_self, e1, e2]
    exact hfl
  · have hG := isGFFWithBoundaryData_shift (IsFlowLine.isGFFWithBoundaryData_zero hκ hfl) (-(θ * chiC κ))
    have e3 : (α₂ - θ) * chiC κ - sleLambda κ - -(θ * chiC κ) = α₂ * chiC κ - sleLambda κ := by ring
    have e4 : -sleLambda κ - (α₁ - θ) * chiC κ + -(θ * chiC κ) = -sleLambda κ - α₁ * chiC κ := by ring
    have e5 : (fun ω => Exist.flowField 0 (-(θ * chiC κ)) (Exist.flowField 0 (θ * chiC κ) (X ω))) = X := by
      funext ω
      rw [flowField_zero_flowField_zero, add_neg_cancel, flowField_zero_zero]
    rw [e3, e4, e5] at hG
    exact hG

end Back

/-! ### The named input and the derivation -/

/-- **Named input: Lemma 7.1 for one middle curve and a given pocket construction** (specification §7.1, pp. 221–225:
the setup "what we will argue holds for all such `C` simultaneously", "the scale factor can be determined by an
arbitrary rule", "The argument lift for `ψ⁻¹` is inherited from the outer-curve height convention"; Lemma 7.1: "The
conditional law of `η_ψ` is `SLE_κ(ρ^L; ρ^R)` with seed weights (CPF2) … It is a continuous simple path in `ℍ̄` and
tends to `∞` at the end of its capacity lifetime. The joint pair with `h_ψ` has the original coupling specification …
its full joint law is independent of the two outer curves"; Figure 7.1, right: `h_ψ` has the data `λ − θ₂χ` on `ℝ₋`
and `−λ − θ₁χ` on `ℝ₊`).

For `0 < κ < 4`, `θ₁ < 0 < θ₂` and `a, b` with (5.2), on every three-curve space (`Lemma72B.IsThreeCurveSpace`) and for
every pocket construction `(C, c, γ')` on it (PROVE-LEMMA71K's `Lemma71K.IsPocketConstruction`: a pocket between the
outer curves and its two-point chart, functions of the outer curves, and the mapped middle segment `γ'`), there is a
`σ(β, α)`-measurable branch shift `n` (the inherited branch: `Lemma71E.shiftLift`) such that the mapped segment,
reparametrized by capacity, is the zero-angle flow line `η` (complete: `ζ = ∞`; a proper curve) of the pulled-back
field `h_ψ = h ∘ ψ⁻¹ − χ arg (ψ⁻¹)′` (`Lemma71K.chartField` with `a = 0`, `k = χ`) for the data of Figure 7.1 (right),
and `h_ψ` is independent of the outer curves. The range of `η` is the range of `γ'`. -/
def Lemma71FixedChartStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ a b : ℝ, θ₁ < 0 → 0 < θ₂ →
    sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a → sleLambda κ - θ₁ * chiC κ ≤ b →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) (ζβ ζα ζγ : Ω → ℝ≥0∞),
      Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ →
    ∀ (C : Ω → Set ℂ) (c : Ω → Chart) (γ' : Ω → ℝ → ℂ), Lemma71K.IsPocketConstruction P β α γ C c γ' →
    ∃ n : Ω → ℤ, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n ∧
      ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
        IsFlowLine κ (prop74Data (θ₂ * chiC κ - sleLambda κ) (-sleLambda κ - θ₁ * chiC κ)) {0} 0 0 P
          (fun ω => Lemma71K.chartField (shiftLift (c ω) (n ω)) 0 (chiC κ) (h ω)) η ζ ∧
        IndepFun (fun ω => Lemma71K.chartField (shiftLift (c ω) (n ω)) 0 (chiC κ) (h ω))
          (fun ω => (β ω, α ω)) P ∧
        ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Supp9B.IsProperCurve (η ω) ∧ range (η ω) = γ' ω '' Ici 0

/-- **Lemma 7.1 for two middle curves in one pocket** (`Prop74Pocket.Lemma71TwoMiddleStatement`, PROVE-PROP74's named
input) **from the fixed-chart Lemma 7.1** (`Lemma71FixedChartStatement`), the orientation of the pocket chart
(`PocketChartOrientationStatement`), and the inputs `Lemma71H.Cond44ReferenceStatement`,
`Lemma71H.Prop55HalfPlaneStatement` of the three-curve space (used for Lemma 6.13's (MD1) exclusion). Conditional
helper. -/
theorem lemma71TwoMiddleStatement_of_fixedChart (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hfc : Lemma71FixedChartStatement.{u})
    (hor : PocketChartOrientationStatement) : Prop74Pocket.Lemma71TwoMiddleStatement.{u} := by
  intro κ hκ hκ4 α₁ θ₁ θ₂ α₂ A B h1 h12 h2 hA hB Ω mΩ P hP h u₀ β γ₂ γ₁ α ζβ ζ₂ ζ₁ ζα hS
  have hχ := Sec4.chiC_pos hκ hκ4
  -- (c) the two three-curve spaces
  have S₁ := isThreeCurveSpace_one href h55 hκ hκ4 h1 h12 h2 hA hB hS
  have S₂ := isThreeCurveSpace_two href h55 hκ hκ4 h1 h12 h2 hA hB hS
  obtain ⟨hA₁, hB₁⟩ := shift_bounds (κ := κ) θ₁ hA hB
  obtain ⟨hA₂, hB₂⟩ := shift_bounds (κ := κ) θ₂ hA hB
  -- (b) one pocket construction for both middle curves: the canonical wall-pair chart of `(β, α)`
  obtain ⟨e, Cw, Np, Nx, Ny, cw, hW⟩ := Lemma71K.exists_isWallPairChart
  obtain ⟨γ'₁, hpc₁⟩ := Lemma71K.isPocketConstruction_of_wallPairChart hW S₁
  obtain ⟨γ'₂, hpc₂⟩ := Lemma71K.isPocketConstruction_of_wallPairChart hW S₂
  set C : Ω → Set ℂ := fun ω => Cw (Lemma71K.toWallPair (β ω) (α ω)) with hCdef
  set c : Ω → Chart := fun ω => cw (Lemma71K.toWallPair (β ω) (α ω)) with hcdef
  -- (a) the fixed-chart Lemma 7.1, twice
  obtain ⟨n₁, hn₁, η₁, ζ'₁, hfl₁, hind₁, hae₁⟩ := hfc κ hκ hκ4 _ _ _ _ (by linarith) (by linarith) hA₁ hB₁ P _ _
    β α γ₁ ζβ ζα ζ₁ S₁ C c γ'₁ hpc₁
  obtain ⟨n₂, hn₂, η₂, ζ'₂, hfl₂, -, hae₂⟩ := hfc κ hκ hκ4 _ _ _ _ (by linarith) (by linarith) hA₂ hB₂ P _ _
    β α γ₂ ζβ ζα ζ₂ S₂ C c γ'₂ hpc₂
  obtain ⟨-, -, hconf, hdom, -, -, hlc, -, hbetw, -, -, -, haeC₁⟩ := hpc₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, haeC₂⟩ := hpc₂
  -- the pulled-back fields of `h`
  set hψ : Ω → DistOn upperHalfPlaneOpens :=
    fun ω => Lemma71K.chartField (shiftLift (c ω) (n₁ ω)) 0 (chiC κ) (h ω) with hψdef
  set hψ₂ : Ω → DistOn upperHalfPlaneOpens :=
    fun ω => Lemma71K.chartField (shiftLift (c ω) (n₂ ω)) 0 (chiC κ) (h ω) with hψ₂def
  have eshift : ∀ (n : Ω → ℤ) (θ : ℝ),
      (fun ω => Lemma71K.chartField (shiftLift (c ω) (n ω)) 0 (chiC κ) (Exist.flowField 0 (θ * chiC κ) (h ω))) =
        fun ω => Exist.flowField 0 (θ * chiC κ) (Lemma71K.chartField (shiftLift (c ω) (n ω)) 0 (chiC κ) (h ω)) :=
    fun n θ => funext fun ω => chartField_flowField (Lemma71E.isConformal_shiftLift (hconf ω) (n ω)) _ _ _ _
  have hfl₁' : IsFlowLine κ (prop74Data ((α₂ - θ₁) * chiC κ - sleLambda κ) (-sleLambda κ - (α₁ - θ₁) * chiC κ))
      {0} 0 0 P (fun ω => Lemma71K.chartField (shiftLift (c ω) (n₁ ω)) 0 (chiC κ)
        (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) η₁ ζ'₁ := hfl₁
  have hfl₂' : IsFlowLine κ (prop74Data ((α₂ - θ₂) * chiC κ - sleLambda κ) (-sleLambda κ - (α₁ - θ₂) * chiC κ))
      {0} 0 0 P (fun ω => Lemma71K.chartField (shiftLift (c ω) (n₂ ω)) 0 (chiC κ)
        (Exist.flowField 0 (θ₂ * chiC κ) (h ω))) η₂ ζ'₂ := hfl₂
  have hind₁' : IndepFun (fun ω => Lemma71K.chartField (shiftLift (c ω) (n₁ ω)) 0 (chiC κ)
      (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) (fun ω => (β ω, α ω)) P := hind₁
  rw [eshift] at hfl₁' hfl₂' hind₁'
  obtain ⟨hfl₁θ, hG₁⟩ := isFlowLine_of_shift hκ hfl₁'
  obtain ⟨hfl₂θ, hG₂⟩ := isFlowLine_of_shift hκ hfl₂'
  -- `h_ψ` is independent of the outer curves
  have hind : IndepFun hψ (fun ω => (β ω, α ω)) P := by
    have h2 := hind₁'.comp (Exist.measurable_flowField 0 (-(θ₁ * chiC κ))) measurable_id
    have e2 : (Exist.flowField 0 (-(θ₁ * chiC κ))) ∘
        (fun ω => Exist.flowField 0 (θ₁ * chiC κ) (Lemma71K.chartField (shiftLift (c ω) (n₁ ω)) 0 (chiC κ) (h ω)))
        = hψ := by
      funext ω
      simp only [Function.comp, flowField_zero_flowField_zero, add_neg_cancel, flowField_zero_zero, hψdef]
    rw [e2] at h2
    exact h2
  -- the same branch: `n₁ = n₂` almost surely
  obtain ⟨f₁, hf₁m, hf₁⟩ := hn₁.exists_eq_measurable_comp
  obtain ⟨f₂, hf₂m, hf₂⟩ := hn₂.exists_eq_measurable_comp
  set d : Ω → ℝ := fun ω => 2 * π * ((n₂ ω : ℝ) - (n₁ ω : ℝ)) * chiC κ with hddef
  have hgm : Measurable fun p : (ℝ≥0 → ℂ) × (ℝ≥0 → ℂ) => 2 * π * ((f₂ p : ℝ) - (f₁ p : ℝ)) * chiC κ :=
    (((Measurable.of_discrete (f := (Int.cast : ℤ → ℝ))).comp hf₂m).sub
      ((Measurable.of_discrete (f := (Int.cast : ℤ → ℝ))).comp hf₁m)).const_mul _ |>.mul_const _
  have hdg : d = (fun p : (ℝ≥0 → ℂ) × (ℝ≥0 → ℂ) => 2 * π * ((f₂ p : ℝ) - (f₁ p : ℝ)) * chiC κ) ∘
      (fun ω => (β ω, α ω)) := by
    funext ω
    simp only [hddef, Function.comp, hf₁, hf₂]
  have hindd : IndepFun hψ d P := by
    rw [hdg]
    exact hind.comp measurable_id hgm
  have hψ₂eq : (fun ω => Exist.flowField 0 (d ω) (hψ ω)) = hψ₂ := funext fun ω => by
    simp only [hψdef, hψ₂def, hddef]
    rw [chartField_shiftLift (hconf ω) (hlc ω), chartField_shiftLift (hconf ω) (hlc ω),
      flowField_zero_flowField_zero]
    congr 1
    ring
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension
    (isPiecewiseConstant_prop74Data (α₂ * chiC κ - sleLambda κ) (-sleLambda κ - α₁ * chiC κ))
  have hG₂' : IsGFFWithBoundaryData P (fun ω => Exist.flowField 0 (d ω) (hψ ω))
      (prop74Data (α₂ * chiC κ - sleLambda κ) (-sleLambda κ - α₁ * chiC κ)) ((({0} : Finset ℝ)) : Set ℝ) := by
    rw [hψ₂eq]
    exact hG₂
  have hd0 := ae_eq_zero_of_isGFFWithBoundaryData_flowField hu hG₁ hG₂' hindd
  have hψae : hψ =ᵐ[P] hψ₂ := hd0.mono fun ω hω => by
    rw [← hψ₂eq]
    show hψ ω = Exist.flowField 0 (d ω) (hψ ω)
    rw [show d ω = 0 from hω, flowField_zero_zero]
  have hfl₂ψ := IsFlowLine.congr_field hκ (isPiecewiseConstant_prop74Data _ _) hfl₂θ hG₁ hψae
  -- the inverse chart on `ℍ̄`, for every `ω` of the good event
  have hGex : ∀ ω, ∃ G : ℂ → ℂ, (Lemma71I.IsSimpleProper (α ω) ∧ Lemma71I.IsSimpleProper (β ω) ∧
      range (β ω) ⊆ closedLeftSide (α ω) ∧ (∀ t, 0 ≤ (γ₁ ω t).im) ∧ (∀ t, 0 ≤ (γ₂ ω t).im) ∧
      C ω ∈ betweenComponents (range (α ω)) (range (β ω)) ∧
      IsMarkedChartImage (α ω) (γ₁ ω) (C ω) (c ω) (γ'₁ ω '' Ici 0) ∧
      IsMarkedChartImage (α ω) (γ₂ ω) (C ω) (c ω) (γ'₂ ω '' Ici 0)) →
      ContinuousOn G Hbar ∧ InjOn G Hbar ∧ MapsTo G H H ∧ (∀ x : ℝ, x < 0 → G x ∈ range (β ω)) ∧
        (∀ x : ℝ, 0 < x → G x ∈ range (α ω)) ∧ G '' (γ'₁ ω '' Ici 0) = range (γ₁ ω) ∩ G '' Hbar ∧
        G '' (γ'₂ ω '' Ici 0) = range (γ₂ ω) ∩ G '' Hbar := fun ω => by
    by_cases hg : Lemma71I.IsSimpleProper (α ω) ∧ Lemma71I.IsSimpleProper (β ω) ∧
        range (β ω) ⊆ closedLeftSide (α ω) ∧ (∀ t, 0 ≤ (γ₁ ω t).im) ∧ (∀ t, 0 ≤ (γ₂ ω t).im) ∧
        C ω ∈ betweenComponents (range (α ω)) (range (β ω)) ∧
        IsMarkedChartImage (α ω) (γ₁ ω) (C ω) (c ω) (γ'₁ ω '' Ici 0) ∧
        IsMarkedChartImage (α ω) (γ₂ ω) (C ω) (c ω) (γ'₂ ω '' Ici 0)
    · obtain ⟨hα, hβ, hβα, hγ₁, hγ₂, hCω, hI₁, hI₂⟩ := hg
      obtain ⟨G, hG⟩ := exists_pocketInv_two hor hα hβ hβα hγ₁ hγ₂ (hconf ω) (hdom ω) hCω hI₁ hI₂
      exact ⟨G, fun _ => hG⟩
    · exact ⟨id, fun h' => absurd h' hg⟩
  choose G hG using hGex
  refine ⟨G, hψ, η₁, η₂, ζ'₁, ζ'₂, ?_, hfl₁θ, hfl₂ψ, ?_⟩
  · rwa [Finset.coe_singleton] at hG₁
  obtain ⟨-, -, -, -, -, -, -, -, -, hae3₁⟩ := S₁
  obtain ⟨-, -, -, -, -, -, -, -, -, hae3₂⟩ := S₂
  filter_upwards [hae₁, hae₂, hae3₁, hae3₂, hbetw, haeC₁, haeC₂] with ω hω₁ hω₂ h3₁ h3₂ hb hc₁ hc₂
  obtain ⟨hz₁, hp₁, hr₁⟩ := hω₁
  obtain ⟨hz₂, hp₂, hr₂⟩ := hω₂
  obtain ⟨-, -, -, -, -, -, hβα, pβ, pα, pγ₁, -, -, -⟩ := h3₁
  obtain ⟨-, -, -, -, -, -, -, -, -, pγ₂, -, -, -⟩ := h3₂
  obtain ⟨a₁, b₁, Ψ₁, hM₁, hc₁', hi₁, hm₁, h0₁, ht₁, hf₁', -, him₁⟩ := hc₁
  obtain ⟨a₂, b₂, Ψ₂, hM₂, hc₂', hi₂, hm₂, h0₂, ht₂, hf₂', -, him₂⟩ := hc₂
  obtain ⟨hGc, hGi, hGH, hGneg, hGpos, hGim₁, hGim₂⟩ := hG ω ⟨pα, pβ, hβα, pγ₁.isProperCurve.2.2.1,
    pγ₂.isProperCurve.2.2.1, hb, ⟨a₁, b₁, Ψ₁, hM₁, hc₁', hi₁, hm₁, h0₁, ht₁, hf₁', him₁⟩,
    ⟨a₂, b₂, Ψ₂, hM₂, hc₂', hi₂, hm₂, h0₂, ht₂, hf₂', him₂⟩⟩
  refine ⟨hz₁, hz₂, hp₁, hp₂, hGc, hGi, hGH, hGneg, hGpos, ?_, ?_⟩
  · rw [hr₁]
    exact hGim₁
  · rw [hr₂]
    exact hGim₂

/-- **Proposition 7.4's order** (`Prop74OrderStatement`) from Lemma 7.5's universal determining function, the §4.2
reference, Proposition 5.5 in `ℍ`, the fixed-chart Lemma 7.1 and the orientation of the pocket chart
(`Prop74Pocket.prop74OrderStatement_of_twoMiddle` with `lemma71TwoMiddleStatement_of_fixedChart`). Conditional
helper. -/
theorem prop74OrderStatement_of_fixedChart (h75 : Theorem15.Lemma75Statement.{u})
    (href : Lemma71H.Cond44ReferenceStatement.{u}) (h55 : Lemma71H.Prop55HalfPlaneStatement.{u})
    (hfc : Lemma71FixedChartStatement.{u}) (hor : PocketChartOrientationStatement) : Prop74OrderStatement.{u} :=
  Prop74Pocket.prop74OrderStatement_of_twoMiddle h75 href h55 (lemma71TwoMiddleStatement_of_fixedChart href h55 hfc hor)

end InteractingSLE.Sec7.Prop74B
