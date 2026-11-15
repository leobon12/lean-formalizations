/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.CanonicalKernel
import InteractingSLE.Spec.Coupling.Assembly11
import InteractingSLE.Spec.Coupling.Lemma311
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# The conditional law of the high pairing given the history code has no atoms

Packet PROVE-FLOWEXIST3 (AUD-3c N1). For the frozen coupling with an admissible seed and a history code `X₀` that is
almost surely the frozen code of the killed history (as `Exist.exists_fieldDetermination_frz` provides):

* the σ-algebra of `X₀` lies in the history announced at the lifetime (`Exist.comap_le_announce`), so the Gaussian bound
  of `Exist.exists_announce_norm_condExp_le` passes to the conditional expectation given `X₀`
  (`ae_norm_condExp_le_of_le`: conditional Jensen and the tower property);
* that conditional expectation is the characteristic function of the conditional law `condDistrib`
  (`ae_condExp_cexp_eq_charFun`);
* **`ae_noAtom_condDistrib`**: for almost every history code `x` with `cζ x ≤ n`, the conditional law of
  `(h, φₙ)` given `X₀ = x` has characteristic function bounded by `e^{−s² cₙ/2}`, hence no atoms
  (`Exist.measure_singleton_eq_zero_of_norm_charFun_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

open QuantumZipper (H zeroGFFTestCov)
open LQGMetric Sec2.Assembly

/-! ### The tower step -/

section Tower

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

/-- A bound on `‖E[f | m₂]‖` on an event of `m₁ ≤ m₂` passes to `‖E[f | m₁]‖`. -/
theorem ae_norm_condExp_le_of_le {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m₀)
    {f : Ω → ℂ} {E : Set Ω} (hE : MeasurableSet[m₁] E) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ᵐ ω ∂P, ω ∈ E → ‖P[f|m₂] ω‖ ≤ c) : ∀ᵐ ω ∂P, ω ∈ E → ‖P[f|m₁] ω‖ ≤ c := by
  set g := P[f|m₂] with hg
  have hgi : Integrable g P := integrable_condExp
  have h1 : P[g|m₁] =ᵐ[P] P[f|m₁] := condExp_condExp_of_le h₁₂ h₂
  have h2 : P[E.indicator g|m₁] =ᵐ[P] E.indicator (P[g|m₁]) := condExp_indicator hgi hE
  have h3 := norm_condExp_le (μ := P) (m := m₁) (E.indicator g)
  have h4 : P[fun ω => ‖E.indicator g ω‖|m₁] ≤ᵐ[P] fun _ => c := by
    have hle : (fun ω => ‖E.indicator g ω‖) ≤ᵐ[P] fun _ => c := by
      filter_upwards [hb] with ω hω
      by_cases hωE : ω ∈ E
      · rw [indicator_of_mem hωE]; exact hω hωE
      · rw [indicator_of_notMem hωE, norm_zero]; exact hc
    have := condExp_mono (m := m₁) (hgi.indicator (h₂ _ (h₁₂ _ hE))).norm (integrable_const c) hle
    rwa [condExp_const (h₁₂.trans h₂)] at this
  filter_upwards [h1, h2, h3, h4] with ω e1 e2 e3 e4 hωE
  rw [← e1]
  have : P[g|m₁] ω = P[E.indicator g|m₁] ω := by rw [e2, indicator_of_mem hωE]
  rw [this]
  exact e3.trans e4

/-- The conditional characteristic function given `X` is the characteristic function of `condDistrib`. -/
theorem ae_condExp_cexp_eq_charFun {β : Type*} [MeasurableSpace β] {X : Ω → β} (hX : Measurable X)
    {Y : Ω → ℝ} (hY : Measurable Y) (s : ℝ) :
    P[fun ω => cexp (s * Y ω * I) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun ω => charFun (condDistrib Y X P (X ω)) s := by
  have hf : StronglyMeasurable fun y : ℝ => cexp (s * y * I) := by
    exact (by fun_prop : Continuous fun y : ℝ => cexp (s * y * I)).stronglyMeasurable
  have hint : Integrable (fun ω => cexp (s * Y ω * I)) P := by
    refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun ω => ?_)
    · exact (hf.measurable.comp hY).aestronglyMeasurable
    · rw [show (s : ℂ) * (Y ω : ℂ) * I = ((s * Y ω : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
  have := condExp_ae_eq_integral_condDistrib hX hY.aemeasurable hf hint
  filter_upwards [this] with ω hω
  rw [hω, charFun_apply_real]

end Tower

/-! ### No atoms -/

section NoAtom

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

theorem measurable_eval_field (hh : Measurable h) (φ : TestOn upperHalfPlaneOpens) :
    Measurable fun ω => h ω φ :=
  ((measurable_pi_apply φ).comp (comap_measurable _)).comp hh

/-- A probability measure on `ℝ` whose characteristic function is bounded by `e^{−q² c/2}` at the rational points
(`c > 0`) has no atoms. -/
theorem measure_singleton_eq_zero_of_rat {ν : Measure ℝ} [IsProbabilityMeasure ν] {c : ℝ} (hc : 0 < c)
    (h : ∀ q : ℚ, ‖charFun ν q‖ ≤ Real.exp (-((q : ℝ) ^ 2 * c / 2))) (a : ℝ) : ν {a} = 0 := by
  have hall : ∀ s : ℝ, ‖charFun ν s‖ ≤ Real.exp (-(s ^ 2 * c / 2)) := by
    intro s
    refine Rat.denseRange_cast.induction_on s ?_ h
    exact isClosed_le (continuous_charFun.norm) (by fun_prop)
  refine measure_singleton_eq_zero_of_norm_charFun_le (C := 1) (c := c / 2) (by positivity) (fun s => ?_) a
  rw [one_mul]
  convert hall s using 2
  ring

/-- **No atoms given the history code.** For the frozen coupling with an admissible seed and a history code `X₀`
that is almost surely in `DetSet` and the frozen code of the killed history, for almost every code `x` with
`cζ x ≤ n` the conditional law of `(h, φₙ)` given `X₀ = x` has no atoms. -/
theorem ae_noAtom_condDistrib (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {B' : ℝ≥0 → Ω → ℝ} {X₀ : Ω → XCode nL nR}
    (hX₀m : Measurable X₀)
    (hX₀ : ∀ᵐ ω ∂P, X₀ ω ∈ DetSet κ xL xR ρL ρR ∧ X₀ ω = frz (codeOf xL xR B' W VL VR ζ ω)) (n : ℕ) :
    ∀ᵐ x ∂(P.map X₀), cζ x ≤ n → ∀ a, condDistrib (fun ω => h ω (highBump n)) X₀ P x {a} = 0 := by
  have hE := hC.1
  have hX : IsMeasurableKilledDriving W VL VR ζ :=
    Coupling.isMeasurableKilledDriving_of_adaptedBefore hE.2.1 hE.2.2.1 hE.2.2.2.1
  obtain ⟨σ, hσ, hann, hbd⟩ := exists_announce_norm_condExp_le hC hκ hX hseed
  have hℋ : (⨆ k, (hσ k).measurableSpace) ≤ mΩ := iSup_le fun k => (hσ k).measurableSpace_le
  have hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[⨆ k, (hσ k).measurableSpace] N := by
    intro N hN h0
    have h0' : MeasurableSet[drivingFiltration P hX 0] N := Ito.measurableSet_usualAugmentation_of_null hN h0 0
    have hle : drivingFiltration P hX 0 ≤ (hσ 0).measurableSpace := by
      rw [← IsStoppingTime.measurableSpace_const (drivingFiltration P hX) 0]
      exact (isStoppingTime_const (drivingFiltration P hX) 0).measurableSpace_mono (hσ 0) fun ω => zero_le
    exact le_iSup (fun k => (hσ k).measurableSpace) 0 _ (hle _ h0')
  have hW : AdaptedBefore (drivingFiltration P hX) ζ W :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hVL : ∀ i, AdaptedBefore (drivingFiltration P hX) ζ (VL i) := fun i =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i)
  have hVR : ∀ j, AdaptedBefore (drivingFiltration P hX) ζ (VR j) := fun j =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX j)
  have hcomap := comap_le_announce hκ hX₀m hX₀ hσ hnull hann.2.2.2 hW hVL hVR
  set Y : Ω → ℝ := fun ω => h ω (highBump n) with hY
  have hYm : Measurable Y := measurable_eval_field hC.2.1 _
  set ν := condDistrib Y X₀ P with hν
  -- the bound at every rational frequency
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂P, cζ (X₀ ω) ≤ n →
      ‖charFun (ν (X₀ ω)) q‖ ≤ Real.exp (-((q : ℝ) ^ 2 * highConst n / 2)) := by
    intro q
    have hEm : MeasurableSet[MeasurableSpace.comap X₀ inferInstance] {ω | cζ (X₀ ω) ≤ n} :=
      ⟨{x | cζ x ≤ n}, measurableSet_le measurable_cζ measurable_const, rfl⟩
    have hb : ∀ᵐ ω ∂P, ω ∈ {ω | cζ (X₀ ω) ≤ n} →
        ‖P[fun ω' => cexp ((q : ℝ) * Y ω' * I) | ⨆ k, (hσ k).measurableSpace] ω‖ ≤
          Real.exp (-((q : ℝ) ^ 2 * highConst n / 2)) := by
      filter_upwards [hbd n q, hX₀] with ω hω hx hle
      refine hω ?_
      have : cζ (X₀ ω) = ζ ω := by rw [hx.2]; rfl
      rw [← this]; exact hle
    have h1 := ae_norm_condExp_le_of_le hcomap hℋ hEm (Real.exp_pos _).le hb
    filter_upwards [h1, ae_condExp_cexp_eq_charFun hX₀m hYm (q : ℝ)] with ω hω e hle
    rw [← e]
    exact hω hle
  have hq' : ∀ᵐ ω ∂P, ∀ q : ℚ, cζ (X₀ ω) ≤ n →
      ‖charFun (ν (X₀ ω)) q‖ ≤ Real.exp (-((q : ℝ) ^ 2 * highConst n / 2)) := ae_all_iff.2 hq
  -- push to the codes
  have hmeas : MeasurableSet {x : XCode nL nR | ∀ q : ℚ, cζ x ≤ n →
      ‖charFun (ν x) q‖ ≤ Real.exp (-((q : ℝ) ^ 2 * highConst n / 2))} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun q => ?_
    have hf : StronglyMeasurable fun y : ℝ => cexp (y * (q : ℝ) * I) :=
      (by fun_prop : Continuous fun y : ℝ => cexp (y * (q : ℝ) * I)).stronglyMeasurable
    have hcf' := (hf.integral_kernel (κ := ν)).measurable
    have e : (fun x => charFun (ν x) q) = fun x => ∫ y, cexp (y * (q : ℝ) * I) ∂ν x := by
      funext x
      rw [charFun_apply_real]
      congr 1; funext y; ring_nf
    have hcf : Measurable fun x => charFun (ν x) q := by rw [e]; exact hcf'
    have hset : {x : XCode nL nR | cζ x ≤ n →
        ‖charFun (ν x) q‖ ≤ Real.exp (-((q : ℝ) ^ 2 * highConst n / 2))} =
        {x | cζ x ≤ n}ᶜ ∪ {x | ‖charFun (ν x) q‖ ≤ Real.exp (-((q : ℝ) ^ 2 * highConst n / 2))} := by
      ext x
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [hset]
    exact (measurableSet_le measurable_cζ measurable_const).compl.union
      (measurableSet_le hcf.norm measurable_const)
  have hx := (ae_map_iff hX₀m.aemeasurable hmeas).2 hq'
  filter_upwards [hx] with x hx hxn a
  exact measure_singleton_eq_zero_of_rat (highConst_pos n) (fun q => hx q hxn) a

end NoAtom

/-! ### An inadmissible seed: lifetime zero -/

section Zero

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The history code of lifetime zero. -/
def zeroCode (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : XCode nL nR :=
  (fun _ _ => 0, 0, fun _ _ => 0, fun i n k => if dyad n k = 0 then xL i else 0,
    fun j n k => if dyad n k = 0 then xR j else 0)

omit mΩ in
theorem frz_codeOf_of_eq_zero {B' : ℝ≥0 → Ω → ℝ} {ω : Ω} (hζ : ζ ω = 0) :
    frz (codeOf xL xR B' W VL VR ζ ω) = zeroCode xL xR := by
  have hnlt : ∀ t : ℝ≥0, ¬ (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζ]; exact not_lt.2 bot_le
  refine Prod.ext ?_ (Prod.ext hζ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · funext n k
    change frzPath (codeOf xL xR B' W VL VR ζ ω) (dyad n k) = 0
    unfold frzPath
    have : cζ (codeOf xL xR B' W VL VR ζ ω) = 0 := hζ
    simp only [this, ↓reduceIte]
  · funext n k
    change killedCode W 0 ζ ω n k = 0
    unfold killedCode
    simp only [hnlt, ↓reduceIte, ite_self]
  · funext i n k
    change killedCode (VL i) (xL i) ζ ω n k = if dyad n k = 0 then xL i else 0
    unfold killedCode
    simp only [hnlt, ↓reduceIte]
  · funext j n k
    change killedCode (VR j) (xR j) ζ ω n k = if dyad n k = 0 then xR j else 0
    unfold killedCode
    simp only [hnlt, ↓reduceIte]

omit [IsProbabilityMeasure P] in
/-- An inadmissible seed has lifetime zero almost surely. -/
theorem ae_lifetime_eq_zero (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR) : ∀ᵐ ω ∂P, ζ ω = 0 := by
  filter_upwards [hE.2.2.2.2] with ω hp
  by_contra hne
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hne
  obtain ⟨hw0, hL0, hR0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnt, -, -⟩ := hp
  have := hnt 0 h0
  rw [hw0, funext hL0, funext hR0] at this
  exact this hseed

/-- **No atoms for an inadmissible seed.** The history code is almost surely the constant `zeroCode`, so the
conditional law of `(h, φₙ)` given it is its law, a Gaussian of variance `G_ℍ(φₙ, φₙ) ≥ cₙ > 0`. -/
theorem ae_noAtom_condDistrib_zero (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR) {B' : ℝ≥0 → Ω → ℝ} {X₀ : Ω → XCode nL nR}
    (hX₀m : Measurable X₀) (hX₀ : ∀ᵐ ω ∂P, X₀ ω = frz (codeOf xL xR B' W VL VR ζ ω)) (n : ℕ) :
    ∀ᵐ x ∂(P.map X₀), ∀ a, condDistrib (fun ω => h ω (highBump n)) X₀ P x {a} = 0 := by
  set Y : Ω → ℝ := fun ω => h ω (highBump n) with hY
  have hYm : Measurable Y := measurable_eval_field hC.2.1 _
  have hXc : ∀ᵐ ω ∂P, X₀ ω = zeroCode xL xR := by
    filter_upwards [hX₀, ae_lifetime_eq_zero hC.1 hseed] with ω h1 h2
    rw [h1, frz_codeOf_of_eq_zero h2]
  have hmapX : P.map X₀ = Measure.dirac (zeroCode xL xR) := by
    rw [Measure.map_congr hXc, Measure.map_const, measure_univ, one_smul]
  have hmapXY : P.map (fun ω => (X₀ ω, Y ω)) = P.map X₀ ⊗ₘ Kernel.const _ (P.map Y) := by
    rw [Measure.compProd_const, hmapX, Measure.dirac_prod, Measure.map_map measurable_prodMk_left hYm]
    refine Measure.map_congr ?_
    filter_upwards [hXc] with ω hω
    simp only [Function.comp_apply, hω]
  have hcd := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hX₀m hYm hmapXY
  obtain ⟨u₀, hu₀⟩ := WholeField.exists_bhe κ ρL ρR xL xR
  have hlaw := Coupling.map_eval_eq_gaussianReal_of_isZBGFFProcess (hC.2.2.1 u₀ hu₀) (highBump n)
  have hv : highConst n ≤ ((zeroGFFTestCov upperHalfPlaneOpens (highBump n) (highBump n)).toNNReal : ℝ) := by
    have h1 := le_zeroGFFTestCov_highBump n 1 QuantumZipper.isOpen_H subset_rfl (highRegion_subset_H n)
    rw [one_smul, one_pow, one_mul] at h1
    exact h1.trans (Real.le_coe_toNNReal _)
  filter_upwards [hcd] with x hx a
  rw [hx, Kernel.const_apply]
  rw [hlaw]
  refine measure_singleton_eq_zero_of_norm_charFun_le (C := 1) (c := highConst n / 2)
    (by have := highConst_pos n; positivity) (fun s => ?_) a
  rw [charFun_gaussianReal, Complex.norm_exp, one_mul]
  set v : ℝ := ((zeroGFFTestCov upperHalfPlaneOpens (highBump n) (highBump n)).toNNReal : ℝ) with hvdef
  have hre : ((s : ℂ) * ((∫ z, u₀ z * highBump n z : ℝ) : ℂ) * I - ((v : ℝ) : ℂ) * (s : ℂ) ^ 2 / 2).re =
      -(v * s ^ 2 / 2) := by
    rw [show ((s : ℂ) * ((∫ z, u₀ z * highBump n z : ℝ) : ℂ) * I - ((v : ℝ) : ℂ) * (s : ℂ) ^ 2 / 2) =
        ((s * ∫ z, u₀ z * highBump n z : ℝ) : ℂ) * I - ((v * s ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.sub_re, Complex.mul_I_re, Complex.ofReal_im, Complex.ofReal_re, neg_zero, zero_sub]
  rw [hre]
  refine Real.exp_le_exp.2 ?_
  nlinarith [sq_nonneg s]

end Zero

end Exist

end InteractingSLE
