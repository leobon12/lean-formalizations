/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefRecoveryMap
import InteractingSLE.Spec.Sec7.Lemma725RefDetStrip
import InteractingSLE.Spec.Sec7.Lemma72CLocal
import InteractingSLE.Spec.Sec7.LocalExtOCov
import InteractingSLE.Spec.Sec7.LocalExtOPiece

/-!
# The ambient recovery for the pocket: `PocketAmbientRecovery` and `PocketRecoveryInput` from Aux. lemma 124's
# exterior decomposition

Packet PROVE-LEMMA725REF5. Specification §7.4, Aux. lemma 124 and Aux. lemma 125's proof
(`source/spec/p385-432.md` L171–L250, pp. 393–398); Astra's shortcut note, Proposition 2.1 steps 1 and 3
(`source/external/AstraIG1/ig1_shortcuts_audited.txt` L248–L285): "E includes the incoming labels and germ, the
chart and lift, and the full exterior Dirichlet projection `h_B` […] Aux. 124 gives `h = h_B + h_C`,
`Law(h_C | E) = GFF₀(C)`"; ruling R68.

* `PocketExteriorDecomp 𝓦 P G C h` (**named input**, Aux. lemma 124's decomposition on the configuration event `G`):
  a `𝓦`-measurable `g` (the exterior projection `h_B`) such that, conditionally on `𝓦`, `h − g` is a zero-boundary
  GFF on a random open set inside the pocket `C` on `G`;
* `isCondZeroBoundaryGFF_of_le`: the tower property of conditional zero-boundary laws;
* **`exists_pocketExteriorDecomp`** (the provider): for a history-marked local set `E` of the zero-boundary GFF `h₀`
  with marks `ℋ`, the germ version `h₁` of Lemma 3.6 (`Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal`) gives
  `PocketExteriorDecomp 𝓦 P G C (h₀ + u)` for every `𝓦` between `σ(E) ∨ σ(h₁)` and `𝒜_E ∨ ℋ` and every pocket
  `C ⊇ ℍ ∖ E` on `G` — this is ruling R68's `𝓦 = σ(walls) ∨ σ(h_B) ∨ 𝒩` with `h_B = h₁ + u`;
* **`pocketAmbientRecovery_of_condGFF`**, **`pocketAmbientRecovery_of_exteriorDecomp`**: REF4's named input
  `PocketAmbientRecovery` for the canonical pocket chart `pChart A C ψ` (`exists_recovery_of_condGFF`);
* **`pocketRecoveryInput_of_exteriorDecomp`**, **`pocketRecoveryInputInf_of_exteriorDecomp`**: REF4's named inputs
  `PocketRecoveryInput`/`…Inf` (all word-shape events and Jordan coordinates of a change pocket);
* **`pocketHistDet_of_exteriorDecomp`**: REF4's `PocketHistDet` (the determination input of
  `pocketChartFieldStatement_of_stop`) from the decomposition, Proposition 5.13 and the pocket erasure.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov chiC)
open LQGMetric (TestOn DistOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefRecovery

open Chart PocketStopField Lemma725RefChart LocalSets

universe u

/-! ### The named input: Aux. lemma 124's exterior decomposition -/

section Defs

variable {Ω : Type*}

/-- **Named input: Aux. lemma 124's exterior decomposition on `G`** (ruling R68). The σ-algebra `𝓦` records a version
`g` of the exterior Dirichlet projection `h_B` (`g` is `𝓦`-measurable), and conditionally on `𝓦` the remainder
`h − g` is a zero-boundary GFF on a random open set `U_ω ⊆ ℍ` lying inside the pocket `C ω` for `ω ∈ G`. -/
def PocketExteriorDecomp (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω) (G : Set Ω)
    (C : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (g : Ω → DistOn upperHalfPlaneOpens) (U : Ω → Set ℂ), Measurable[𝓦] g ∧ (∀ ω, IsOpen (U ω)) ∧
    (∀ ω, U ω ⊆ H) ∧ (∀ ω ∈ G, U ω ⊆ C ω) ∧ IsCondZeroBoundaryGFF P 𝓦 U fun ω => h ω - g ω

theorem PocketExteriorDecomp.mono {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {G G' : Set Ω}
    {C : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens} (hd : PocketExteriorDecomp 𝓦 P G C h) (hG' : G' ⊆ G) :
    PocketExteriorDecomp 𝓦 P G' C h := by
  obtain ⟨g, U, hg, hUo, hUH, hUC, hc⟩ := hd
  exact ⟨g, U, hg, hUo, hUH, fun ω hω => hUC ω (hG' hω), hc⟩

end Defs

/-! ### The tower property and the provider from a history-marked local set -/

section Provider

variable {Ω : Type*} {𝓦 𝒢 ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Tower property of conditional zero-boundary laws**: a conditional zero-boundary GFF given `𝒢` is one given every
smaller `𝓦` for which the conditional variances are `𝓦`-measurable. -/
theorem isCondZeroBoundaryGFF_of_le [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ)
    (h𝓦𝒢 : 𝓦 ≤ 𝒢) {U : Ω → Set ℂ} (hUo : ∀ ω, IsOpen (U ω)) (hUH : ∀ ω, U ω ⊆ H)
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : IsCondZeroBoundaryGFF P 𝒢 U X)
    (hm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable[𝓦] fun ω => zeroGFFTestCov (U ω) φ φ) :
    IsCondZeroBoundaryGFF P 𝓦 U X := by
  intro φ
  have hfm : Measurable[𝓦] fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (U ω) φ φ) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp ((hm φ).const_mul _))
  have hb : ∀ ω, ‖((Real.exp (-(1 / 2) * zeroGFFTestCov (U ω) φ φ) : ℝ) : ℂ)‖ ≤ 1 := fun ω => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith [LocalSets.zeroGFFTestCov_self_nonneg (hUo ω) (hUH ω) φ]
  have hfi : Integrable (fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (U ω) φ φ) : ℝ) : ℂ)) P :=
    Integrable.of_bound ((hfm.mono (h𝓦𝒢.trans h𝒢) le_rfl).aestronglyMeasurable) 1 (Eventually.of_forall hb)
  calc P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | 𝓦]
      =ᵐ[P] P[P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | 𝒢] | 𝓦] :=
        (condExp_condExp_of_le h𝓦𝒢 h𝒢).symm
    _ =ᵐ[P] P[fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (U ω) φ φ) : ℝ) : ℂ) | 𝓦] :=
        condExp_congr_ae (hX φ)
    _ = fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (U ω) φ φ) : ℝ) : ℂ) :=
        condExp_of_stronglyMeasurable (h𝓦𝒢.trans h𝒢) hfm.stronglyMeasurable hfi

theorem diff_relClosureH_subset (S : Set ℂ) : H \ relClosureH S ⊆ H \ S := fun _ hz =>
  ⟨hz.1, fun hzS => hz.2 ⟨hz.1, subset_closure ⟨hzS, hz.1⟩⟩⟩

/-- **The exterior decomposition from the germ law** (Aux. lemma 124 from Lemma 3.6 / Aux. lemma 18 with the history
retained): if `h₀ − h₁` is, conditionally on the germs and marks `𝒜_E ∨ ℋ`, a zero-boundary GFF on `ℍ ∖ E`, and `𝓦`
lies between `σ(E) ∨ σ(h₁)` and `𝒜_E ∨ ℋ`, then `PocketExteriorDecomp 𝓦 P G C (h₀ + u)` holds with `g = h₁ + u` for
every event `G` and every pocket `C ⊇ ℍ ∖ E` on `G`. -/
theorem pocketExteriorDecomp_of_germLaw [IsProbabilityMeasure P] {h₀ h₁ : Ω → DistOn upperHalfPlaneOpens}
    {E : Ω → Set ℂ} (hle : germSigma E h₀ ⊔ ℋ ≤ mΩ) (h𝓦 : 𝓦 ≤ germSigma E h₀ ⊔ ℋ)
    (hE𝓦 : Measurable[𝓦, hittingSigma] E) (hh₁𝓦 : Measurable[𝓦] h₁)
    (hAc : ∀ᵐ ω ∂P, E ω ⊆ H ∧ IsOpen (H \ E ω))
    (hcond : IsCondZeroBoundaryGFF P (germSigma E h₀ ⊔ ℋ) (fun ω => H \ E ω) (fun ω => h₀ ω - h₁ ω))
    (u : ℂ → ℝ) {G : Set Ω} {C : Ω → Set ℂ} (hGC : ∀ ω ∈ G, H \ E ω ⊆ C ω) :
    PocketExteriorDecomp 𝓦 P G C (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) := by
  have hUo : ∀ ω, IsOpen (H \ relClosureH (E ω)) := fun ω => isOpen_H_diff_relClosureH _
  have hUH : ∀ ω, H \ relClosureH (E ω) ⊆ H := fun ω => sdiff_subset
  have hcondU : IsCondZeroBoundaryGFF P (germSigma E h₀ ⊔ ℋ) (fun ω => H \ relClosureH (E ω))
      (fun ω => h₀ ω - h₁ ω) := by
    refine LocalExt.IsCondZeroBoundaryGFF.congr_ae hcond ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hAc] with ω hω
    rw [relClosureH_eq hω.1 hω.2]
  have hm : ∀ φ : TestOn upperHalfPlaneOpens,
      Measurable[𝓦] fun ω => zeroGFFTestCov (H \ relClosureH (E ω)) φ φ := fun φ =>
    @LocalExt.measurable_zeroGFFTestCov_random Ω 𝓦 (fun ω => H \ relClosureH (E ω))
      (fun ω => ⟨hUo ω, hUH ω⟩) (LocalExt.measurableSet_testFamily_subset_compl hE𝓦) (fun _ => φ) (fun _ => φ)
      (fun _ => measurable_const) (fun _ => measurable_const)
  have e : (fun ω => (h₀ ω + smoothDist upperHalfPlaneOpens u) - (h₁ ω + smoothDist upperHalfPlaneOpens u)) =
      fun ω => h₀ ω - h₁ ω := funext fun ω => add_sub_add_right_eq_sub _ _ _
  refine ⟨fun ω => h₁ ω + smoothDist upperHalfPlaneOpens u, fun ω => H \ relClosureH (E ω),
    (@LQGMetric.measurable_distOn_iff upperHalfPlaneOpens Ω 𝓦 _).2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).comp hh₁𝓦).add_const _,
    hUo, hUH, fun ω hω => (diff_relClosureH_subset _).trans (hGC ω hω), ?_⟩
  rw [e]
  exact isCondZeroBoundaryGFF_of_le hle h𝓦 hUo hUH hcondU hm

/-- **The exterior decomposition from a history-marked local set**: for a history-marked local set `E` of the
zero-boundary GFF `h₀` (marks `ℋ`), almost surely relatively closed in `ℍ`, its germ version `h₁`
(`Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal`) gives `PocketExteriorDecomp 𝓦 P G C (h₀ + u)` for every `𝓦`
between `σ(E) ∨ σ(h₁)` and `𝒜_E ∨ ℋ`, every event `G` and every pocket `C ⊇ ℍ ∖ E` on `G`. -/
theorem exists_pocketExteriorDecomp [IsProbabilityMeasure P] {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {E : Ω → Set ℂ} (hE : Measurable[mΩ, hittingSigma] E)
    (hℋ : ℋ ≤ mΩ) (hloc : WholeField.IsHistoryAvoidanceLocal ℋ E h₀ P)
    (hAc : ∀ᵐ ω ∂P, E ω ⊆ H ∧ IsOpen (H \ E ω)) (u : ℂ → ℝ) :
    ∃ h₁ : Ω → DistOn upperHalfPlaneOpens, Measurable[germSigma E h₀] h₁ ∧
      ∀ 𝓦' : MeasurableSpace Ω, 𝓦' ≤ germSigma E h₀ ⊔ ℋ → Measurable[𝓦', hittingSigma] E → Measurable[𝓦'] h₁ →
        ∀ (G : Set Ω) (C : Ω → Set ℂ), (∀ ω ∈ G, H \ E ω ⊆ C ω) →
          @PocketExteriorDecomp Ω 𝓦' mΩ P G C (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) := by
  obtain ⟨h₁, hh₁m, -, hcond⟩ := Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh₀ hE hℋ hloc hAc
  have hle : germSigma E h₀ ⊔ ℋ ≤ mΩ := sup_le (germSigma_le hE hh₀.measurable) hℋ
  exact ⟨h₁, hh₁m, fun 𝓦' h1 h2 h3 G C hGC =>
    pocketExteriorDecomp_of_germLaw (mΩ := mΩ) (P := P) (𝓦 := 𝓦') hle h1 h2 h3 hAc hcond u hGC⟩

end Provider

/-! ### The ambient recovery for the canonical pocket chart -/

section Pocket

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **REF4's `PocketAmbientRecovery` from a conditional zero-boundary law inside the pocket** (p. 398): if `h − g` is,
conditionally on `𝓦`, a zero-boundary GFF on a random open set inside the pocket on `A`, with `g` `𝓦`-measurable, and
`𝓦` is generated up to null sets by a standard Borel record, then on `A` the ambient field is a Borel function of the
record and the pocket field read in the canonical pocket chart `pChart A C ψ`. -/
theorem pocketAmbientRecovery_of_condGFF [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) (κ : ℝ) {A : Set Ω}
    (hA : MeasurableSet[𝓦] A) {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hCH : ∀ ω ∈ A, C ω ⊆ H) (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    {h g : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hg : Measurable[𝓦] g) {U : Ω → Set ℂ}
    (hUo : ∀ ω, IsOpen (U ω)) (hUH : ∀ ω, U ω ⊆ H) (hUA : ∀ ω ∈ A, U ω ⊆ C ω)
    (hcond : IsCondZeroBoundaryGFF P 𝓦 U fun ω => h ω - g ω)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    PocketAmbientRecovery κ 𝓦 P A C ψ h := by
  have hprops := pChart_props hCo hCH hψ
  have hc : ∀ ω, (pChart A C ψ ω).IsConformal := fun ω => (hprops ω).2.2.1
  have hdom : ∀ z, MeasurableSet[𝓦] {ω | z ∈ (pChart A C ψ ω).dom} := fun z =>
    measurableSet_mem_dom_pChart (mΩ := 𝓦) hCo hCH hψ hA hCm z
  have hfwd : ∀ z, Measurable[𝓦] ({ω | z ∈ (pChart A C ψ ω).dom}.indicator fun ω => (pChart A C ψ ω).1 z) :=
    fun z => measurable_fwd_pChart (mΩ := 𝓦) hCo hCH hψ hA hψm z
  have hn0 : Measurable[𝓦] fun _ : Ω => (0 : ℤ) := measurable_const
  have hliftm : ∀ z, Measurable[𝓦] ({ω | z ∈ (pChart A C ψ ω).dom}.indicator fun ω => (pChart A C ψ ω).2.2 z) := by
    intro z
    have h0 := measurable_lift_shiftChart hCo hCH hψ hA hCm hψm hn0 z
    have e : ({ω | z ∈ (shiftChart (pChart A C ψ ω) 0).dom}.indicator
        fun ω => (shiftChart (pChart A C ψ ω) 0).2.2 z) =
        ({ω | z ∈ (pChart A C ψ ω).dom}.indicator fun ω => (pChart A C ψ ω).2.2 z) := by
      funext ω
      simp only [shiftChart, Int.cast_zero, mul_zero, sub_zero]
    rwa [e] at h0
  have hliftc : ∀ ω, ContinuousOn (pChart A C ψ ω).2.2 (pChart A C ψ ω).dom := fun ω =>
    (continuousOn_lift_shiftChart hCo hCH hψ (fun _ => (0 : ℤ)) ω).congr fun z _ => by
      simp only [shiftChart, Int.cast_zero, mul_zero, sub_zero]
  have hUA' : ∀ ω ∈ A, U ω ⊆ (pChart A C ψ ω).dom := fun ω hω z hz =>
    (mem_dom_pChart_iff hCo hCH hψ ω z).2 (Or.inl ⟨hω, hUA ω hω hz⟩)
  obtain ⟨F, hF, hFe⟩ := exists_recovery_of_condGFF h𝓦 hA hc hdom hfwd hliftm hliftc hh hg hUo hUH hUA' hcond
    hE₀ hgen 0 (chiC κ)
  refine ⟨ε₀, inferInstance, inferInstance, E₀, F, hE₀, hF, ?_⟩
  filter_upwards [hFe] with ω hω hωA _
  exact hω hωA

/-- **REF4's `PocketAmbientRecovery` from Aux. lemma 124's exterior decomposition.** -/
theorem pocketAmbientRecovery_of_exteriorDecomp [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) (κ : ℝ) {A : Set Ω}
    (hA : MeasurableSet[𝓦] A) {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hCH : ∀ ω ∈ A, C ω ⊆ H) (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hdec : PocketExteriorDecomp 𝓦 P A C h)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    PocketAmbientRecovery κ 𝓦 P A C ψ h := by
  obtain ⟨g, U, hg, hUo, hUH, hUA, hcond⟩ := hdec
  exact pocketAmbientRecovery_of_condGFF h𝓦 κ hA hCo hCH hψ hCm hψm hh hg hUo hUH hUA hcond hE₀ hgen

/-- **REF4's determination input `PocketHistDet`** (the `hdet` of `pocketChartFieldStatement_of_stop`) from Aux.
lemma 124's exterior decomposition, Proposition 5.13 and the measurable pocket erasure
(`pocketAmbientRecovery_of_exteriorDecomp`, `pocketHistDet_of_recovery`). -/
theorem pocketHistDet_of_exteriorDecomp [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {κ : ℝ} {nL nR : ℕ} {A : Set Ω}
    (hA : MeasurableSet[𝓦] A) {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hdec : PocketExteriorDecomp 𝓦 P A C h)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) {η : Ω → ℝ → ℂ}
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    (hers : PocketErasure 𝓦 P A γ xL xR η) :
    PocketHistDet κ 𝓦 P A γ xL xR C ψ h :=
  pocketHistDet_of_recovery hCo hCH hψ
    (pocketAmbientRecovery_of_exteriorDecomp h𝓦 κ hA hCo hCH hψ hCm hψm hh hdec hE₀ hgen) h513 hers

end Pocket

/-! ### `PocketRecoveryInput` for the strip's change pockets -/

section Change

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketLeftFrontier
  PocketCoupling

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **REF4's named input `PocketRecoveryInput`** (bounded change pocket) from Aux. lemma 124's exterior decomposition
on the configuration event. -/
theorem pocketRecoveryInput_of_exteriorDecomp [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) (κ : ℝ)
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hdec : PocketExteriorDecomp 𝓦 P G (fun ω => cfPocket (R ω) (L ω) r) h)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    PocketRecoveryInput κ 𝓦 P R L r G h := by
  intro A hA hAG _ ψ hψ hψm
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    PocketUnionPt.measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  refine pocketAmbientRecovery_of_exteriorDecomp h𝓦 (16 / κ) hA (fun ω hω => ?_) (fun ω hω => ?_)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm (fun z => ?_) hh (hdec.mono hAG) hE₀ hgen
  · exact isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  · exact PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  · exact hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩

/-- **REF4's named input `PocketRecoveryInputInf`** (change pocket opening at the flow seed) from Aux. lemma 124's
exterior decomposition on the configuration event. -/
theorem pocketRecoveryInputInf_of_exteriorDecomp [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) (κ : ℝ)
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hdec : PocketExteriorDecomp 𝓦 P G (fun ω => cfPocket (R ω) (L ω) r) h)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    PocketRecoveryInputInf κ 𝓦 P R L r G h := by
  intro A hA hAG _ ψ hψ hψm
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    PocketUnionPt.measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  refine pocketAmbientRecovery_of_exteriorDecomp h𝓦 (16 / κ) hA (fun ω hω => ?_) (fun ω hω => ?_)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm (fun z => ?_) hh (hdec.mono hAG) hE₀ hgen
  · exact isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  · exact PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  · exact hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2

end Change

end InteractingSLE.Sec7.Lemma725RefRecovery
