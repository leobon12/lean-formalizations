import SmallGammaGeodesics.CC.ConfMetric
import SmallGammaGeodesics.CC.UniversalLocality
import SmallGammaGeodesics.CC.Coupling
import LQGMetric.Field.StandardBorelRange
import LQGMetric.Field.RandomDistVersion

/-!
# Locality of the transported metric `D^ϕ` (track CC, packet CC2, target T3)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D4** (used in [3] Lemma 3.8 and
Thm 3.4; Gwynne–Miller arXiv:1905.00384). Let `(h, h̄, f)` be a coupling for `IsConfNbhd ϕ W V`
(`IsConfCoupling`, `Core/Interfaces.lean`) and `A ⊆ V` open. By "internal of internal"
(`funInternal_confMetric`, `CC/ConfMetric.lean`), the internal metric of `D^ϕ` on `A` is
`confMetric D ϕ A h̄ f = D_{h̄+f}(ϕ ·, ϕ ·; ϕ(A))`.

**Coordinates.** Let `O` be the open set `ϕ(A)` and `(e_c)_{c ∈ CoordJ}` LQGMetric's countable family
`comb O c` (the coordinates `pairJ O`; `CoordJ = (ℕ × ℕ) →₀ ℤ` is countable). The **transported
coordinates** of `h` are `confCoord γ ϕ W O h c = h(τ e_c) − Q ∫ log|ϕ'| τ e_c`, with `τ e_c` the
conformal pullback (`confPull`), a test function supported in `A`. On the coupling event they are the
coordinates of `(h̄ + f)|_O` (`IsConfCoupling.confCoord_eq`).

Results:
* `confMetric_eq_of_locality` (deterministic core): for any locality functional `F` of `h̄ + f` on `O`,
  `D^ϕ(z, w; A) = F(pairJInv O (confCoord h))(ϕ z, ϕ w)` for `z, w ∈ A`. No continuity of `g ↦ τ g`
  is used.
* `exists_confMetric_eq_coord` (**T3, coordinate form**): a.s. `D^ϕ(·,·;A)` is a measurable function of
  the countably many transported pairings `confCoord γ ϕ W O h`;
  `exists_universal_confMetric_eq_coord`: one such function for countably many couplings on
  possibly different probability spaces (universal locality, `CC/UniversalLocality.lean`).
* `exists_confMetric_eq_restrict` (**T3**): a.s. `D^ϕ(·,·;A) = G(h|_A)` on `A × A` with `G` measurable
  on `𝒟'(A)`: the locality axiom for `D^ϕ` with respect to `h`; `exists_universal_confMetric_eq_restrict`
  and `exists_funInternal_eq_restrict` (the same with `funInternal (confMetric D ϕ V h̄ f) A`).
* **modulo constants**: `ae_isConfCoupling_addConst` (adding a random constant to `h` and `h̄` keeps a
  coupling), `ae_confMetric_addConst_random` (it multiplies `D^ϕ` by `e^{ξ c}`), and the combination
  `exists_confMetric_eq_restrict_addConst`: a.s. `e^{ξ c} D^ϕ(·,·;A) = G((h + c)|_A)`; the companion
  for `D_h(·,·;A)` is `exists_internal_eq_restrict_addConst`. Hence scale-invariant events built from
  `D^ϕ(·,·;A)` and `D_h(·,·;A)` are determined by `(h + c)|_A` (e.g. `c = −h_{4r}(z)`), as in GM's
  `gm_L3_7_of_loc`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-! ## 1. Test functions and coordinates -/

/-- A test function on `ℂ` supported in the open set `U`, as an element of `𝓓(U)`. -/
def testOnOfSupp (U : TopologicalSpace.Opens ℂ) (φ : TestC) (hφ : tsupport (φ : ℂ → ℝ) ⊆ U) :
    TestOn U where
  toFun := φ
  contDiff' := φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport
  tsupport_subset' := hφ

theorem restrictTo_testOnOfSupp (U : TopologicalSpace.Opens ℂ) (x : DistC) (φ : TestC)
    (hφ : tsupport (φ : ℂ → ℝ) ⊆ U) : restrictTo U x (testOnOfSupp U φ hφ) = x φ := by
  change x (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) _) = x φ
  congr 1
  ext y
  rw [coe_monoCLM_top]
  rfl

/-- The coordinate test function `e_c = comb O c` of `pairJ O`, as a test function on `ℂ`. -/
def combC (O : TopologicalSpace.Opens ℂ) (c : CoordJ) : TestC :=
  TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) (comb O c)

theorem coe_combC (O : TopologicalSpace.Opens ℂ) (c : CoordJ) :
    (combC O c : ℂ → ℝ) = comb O c :=
  coe_monoCLM_top O (comb O c)

theorem tsupport_combC_subset (O : TopologicalSpace.Opens ℂ) (c : CoordJ) :
    tsupport (combC O c : ℂ → ℝ) ⊆ O := by
  rw [coe_combC]
  exact (comb O c).tsupport_subset

/-- The `pairJ` coordinates of a restriction are pairings with the `combC` test functions. -/
theorem pairJ_restrictTo_apply (O : TopologicalSpace.Opens ℂ) (x : DistC) (c : CoordJ) :
    pairJ O (restrictTo O x) c = x (combC O c) := rfl

/-- The **transported coordinates** `c ↦ h(τ e_c) − Q γ ∫ log|ϕ'| τ e_c` (`τ = confPull ϕ W`): the
`pairJ O` coordinates of `(h ∘ ϕ⁻¹ + Q log|(ϕ⁻¹)'|)|_O`. -/
def confCoord (γ : ℝ) (ϕ : ℂ → ℂ) (W : Set ℂ) (O : TopologicalSpace.Opens ℂ) (x : DistC) :
    CoordJ → ℝ := fun c =>
  x (confPull ϕ W (combC O c)) - Q γ * ∫ y, Real.log ‖deriv ϕ y‖ * confPull ϕ W (combC O c) y

theorem measurable_confCoord (γ : ℝ) (ϕ : ℂ → ℂ) (W : Set ℂ) (O : TopologicalSpace.Opens ℂ) :
    Measurable (confCoord γ ϕ W O) :=
  measurable_pi_iff.2 fun _ => (measurable_distOn_apply _).sub_const _

variable {γ : ℝ} {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {W V A : Set ℂ}

/-- On the coupling event, the transported coordinates are the `pairJ` coordinates of
`(h̄ + f)|_O`, for any open `O ⊆ ϕ(V)`. -/
theorem IsConfCoupling.confCoord_eq {h hbar : DistC} {f : C(ℂ, ℝ)} (hϕ : IsConfNbhd ϕ W V)
    {O : TopologicalSpace.Opens ℂ} (hOV : (O : Set ℂ) ⊆ ϕ '' V)
    (hc : IsConfCoupling γ ϕ W V h hbar f) :
    confCoord γ ϕ W O h = pairJ O (restrictTo O (addFun hbar f)) := by
  funext c
  have hg : tsupport (combC O c : ℂ → ℝ) ⊆ ϕ '' V := (tsupport_combC_subset O c).trans hOV
  have key := hc (combC O c) (confPull ϕ W (combC O c)) hg (isConfPull_confPull hϕ hg)
  rw [pairJ_restrictTo_apply]
  show h (confPull ϕ W (combC O c)) - Q γ * ∫ y, Real.log ‖deriv ϕ y‖ * confPull ϕ W (combC O c) y =
    (hbar + ofCont f) (combC O c)
  rw [key]
  show _ = hbar (combC O c) + ofCont f (combC O c)
  rw [ofCont_apply]
  congr 2
  funext y
  ring

/-- The transported coordinates only depend on `h|_A`: they are a measurable function of the
restriction to an open `A ⊆ V` with `ϕ '' A = O`. -/
theorem exists_confCoord_eq_restrict (hϕ : IsConfNbhd ϕ W V) (A : TopologicalSpace.Opens ℂ)
    (hAV : (A : Set ℂ) ⊆ V) (O : TopologicalSpace.Opens ℂ) (hO : (O : Set ℂ) = ϕ '' A) :
    ∃ R : DistOn A → CoordJ → ℝ, Measurable R ∧
      ∀ x : DistC, R (restrictTo A x) = confCoord γ ϕ W O x := by
  have hϕA : IsConfNbhd ϕ W A := hϕ.mono A.isOpen hAV
  have hsupp : ∀ c, tsupport (confPull ϕ W (combC O c) : ℂ → ℝ) ⊆ A := fun c => by
    have hg : tsupport (combC O c : ℂ → ℝ) ⊆ ϕ '' A := hO ▸ tsupport_combC_subset O c
    exact IsConfPull.tsupport_subset_V hϕA hg (isConfPull_confPull hϕA hg)
  refine ⟨fun x c => x (testOnOfSupp A (confPull ϕ W (combC O c)) (hsupp c)) -
    Q γ * ∫ y, Real.log ‖deriv ϕ y‖ * confPull ϕ W (combC O c) y, ?_, fun x => ?_⟩
  · exact measurable_pi_iff.2 fun c => (measurable_distOn_apply _).sub_const _
  · funext c
    show restrictTo A x (testOnOfSupp A (confPull ϕ W (combC O c)) (hsupp c)) - _ = _
    rw [restrictTo_testOnOfSupp]
    rfl

/-! ## 2. The deterministic core -/

/-- **Locality of `D^ϕ`, deterministic core** (CC0 D4): if `F` is a locality functional of `h̄ + f` on
`O = ϕ(A)` (pathwise) and `(h, h̄, f)` is a coupling, then
`D^ϕ(z, w; A) = F(pairJInv O (confCoord h))(ϕ z, ϕ w)` for `z, w ∈ A`. -/
theorem confMetric_eq_of_locality {h hbar : DistC} {f : C(ℂ, ℝ)} (hϕ : IsConfNbhd ϕ W V)
    (hAV : A ⊆ V) {O : TopologicalSpace.Opens ℂ} (hO : (O : Set ℂ) = ϕ '' A)
    (hc : IsConfCoupling γ ϕ W V h hbar f) {F : DistOn O → ℂ → ℂ → ℝ≥0∞}
    (hF : ∀ y ∈ O, ∀ y' ∈ O,
      (D (addFun hbar f)).internal O y y' = F (restrictTo O (addFun hbar f)) y y')
    {z w : ℂ} (hz : z ∈ A) (hw : w ∈ A) :
    confMetric D ϕ A hbar f z w = F (pairJInv O (confCoord γ ϕ W O h)) (ϕ z) (ϕ w) := by
  have hOV : (O : Set ℂ) ⊆ ϕ '' V := hO ▸ image_mono hAV
  rw [hc.confCoord_eq hϕ hOV, pairJInv_pairJ, confMetric_def, ← hO]
  have hzO : ϕ z ∈ (O : Set ℂ) := hO ▸ mem_image_of_mem ϕ hz
  have hwO : ϕ w ∈ (O : Set ℂ) := hO ▸ mem_image_of_mem ϕ hw
  exact hF _ hzO _ hwO

/-! ## 3. Locality of `D^ϕ` almost surely -/

section AS

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)}

/-- The measurable functional `a ↦ F(pairJInv O a)(ϕ ·, ϕ ·)`. -/
theorem measurable_locFun {O : TopologicalSpace.Opens ℂ} {F : DistOn O → ℂ → ℂ → ℝ≥0∞}
    (hF : Measurable F) (ϕ : ℂ → ℂ) :
    Measurable fun (a : CoordJ → ℝ) (z w : ℂ) => F (pairJInv O a) (ϕ z) (ϕ w) :=
  measurable_pi_iff.2 fun z => measurable_pi_iff.2 fun w =>
    (measurable_pi_apply (ϕ w)).comp ((measurable_pi_apply (ϕ z)).comp
      (hF.comp (measurable_pairJInv O)))

/-- **T3, coordinate form** (CC0 D4): for `A ⊆ V` and `O = ϕ(A)` open, a.s. `D^ϕ(·,·;A)` is a
measurable function of the countably many transported pairings `h(τ e_c) − Q ∫ log|ϕ'| τ e_c`
(`c ∈ CoordJ`, the `pairJ` family of `ϕ(A)`). -/
theorem exists_confMetric_eq_coord (hD : IsStrongLQGMetric γ D) (hϕ : IsConfNbhd ϕ W V)
    (hAV : A ⊆ V) (O : TopologicalSpace.Opens ℂ) (hO : (O : Set ℂ) = ϕ '' A)
    (hhb : IsWholePlaneGFF hbar P) (hf : Measurable f)
    (hc : ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) :
    ∃ Ψ : (CoordJ → ℝ) → ℂ → ℂ → ℝ≥0∞, Measurable Ψ ∧
      ∀ᵐ ω ∂P, ∀ z ∈ A, ∀ w ∈ A,
        confMetric D ϕ A (hbar ω) (f ω) z w = Ψ (confCoord γ ϕ W O (h ω)) z w := by
  obtain ⟨F, hFm, hF⟩ := hD.locality P _ (isGFFPlusCont_addFun_of_wp hhb hf) O
  refine ⟨fun a z w => F (pairJInv O a) (ϕ z) (ϕ w), measurable_locFun hFm ϕ, ?_⟩
  filter_upwards [hc, hF] with ω hcω hFω z hz w hw
  exact confMetric_eq_of_locality hϕ hAV hO hcω hFω hz hw

/-- **T3** (CC0 D4): for `A ⊆ V` open, a.s. `D^ϕ(·,·;A)` is a measurable function of `h|_A`
(the locality axiom for `D^ϕ` with respect to `h`). -/
theorem exists_confMetric_eq_restrict (hD : IsStrongLQGMetric γ D) (hϕ : IsConfNbhd ϕ W V)
    (A : TopologicalSpace.Opens ℂ) (hAV : (A : Set ℂ) ⊆ V) (hhb : IsWholePlaneGFF hbar P)
    (hf : Measurable f) (hc : ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) :
    ∃ G : DistOn A → ℂ → ℂ → ℝ≥0∞, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ z ∈ A, ∀ w ∈ A,
        confMetric D ϕ A (hbar ω) (f ω) z w = G (restrictTo A (h ω)) z w := by
  let O : TopologicalSpace.Opens ℂ := ⟨ϕ '' A, (hϕ.mono A.isOpen hAV).isOpen_image⟩
  obtain ⟨Ψ, hΨ, hΨae⟩ := exists_confMetric_eq_coord hD hϕ hAV O rfl hhb hf hc
  obtain ⟨R, hR, hRe⟩ := exists_confCoord_eq_restrict (γ := γ) hϕ A hAV O rfl
  refine ⟨Ψ ∘ R, hΨ.comp hR, ?_⟩
  filter_upwards [hΨae] with ω hω z hz w hw
  rw [hω z hz w hw, Function.comp_apply, hRe]

/-- **T3, internal-metric form**: a.s. the internal metric of `D^ϕ` on `A`,
`funInternal (confMetric D ϕ V h̄ f) A`, is a measurable function of `h|_A` on `A × A`. -/
theorem exists_funInternal_eq_restrict (hD : IsStrongLQGMetric γ D) (hϕ : IsConfNbhd ϕ W V)
    (A : TopologicalSpace.Opens ℂ) (hAV : (A : Set ℂ) ⊆ V) (hhb : IsWholePlaneGFF hbar P)
    (hf : Measurable f) (hc : ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) :
    ∃ G : DistOn A → ℂ → ℂ → ℝ≥0∞, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ z ∈ A, ∀ w ∈ A,
        funInternal (confMetric D ϕ V (hbar ω) (f ω)) A z w = G (restrictTo A (h ω)) z w := by
  obtain ⟨G, hG, hGae⟩ := exists_confMetric_eq_restrict hD hϕ A hAV hhb hf hc
  refine ⟨G, hG, ?_⟩
  filter_upwards [hGae] with ω hω z hz w hw
  rw [funInternal_confMetric hϕ hAV (hϕ.subset (hAV hz)) (hϕ.subset (hAV hw))]
  exact hω z hz w hw

/-! ## 4. One functional for countably many couplings -/

/-- **T3, universal coordinate form**: one measurable `Ψ` for countably many couplings (same map,
possibly different probability spaces), by universal locality. -/
theorem exists_universal_confMetric_eq_coord (hD : IsStrongLQGMetric γ D)
    (hϕ : IsConfNbhd ϕ W V) (hAV : A ⊆ V) (O : TopologicalSpace.Opens ℂ)
    (hO : (O : Set ℂ) = ϕ '' A) {ι : Type} [Countable ι] {Ωi : ι → Type}
    [∀ i, MeasurableSpace (Ωi i)] (Pi : ∀ i, Measure (Ωi i)) [∀ i, IsProbabilityMeasure (Pi i)]
    (hi hbari : ∀ i, Ωi i → DistC) (fi : ∀ i, Ωi i → C(ℂ, ℝ))
    (hhb : ∀ i, IsWholePlaneGFF (hbari i) (Pi i)) (hf : ∀ i, Measurable (fi i))
    (hc : ∀ i, ∀ᵐ ω ∂(Pi i), IsConfCoupling γ ϕ W V (hi i ω) (hbari i ω) (fi i ω)) :
    ∃ Ψ : (CoordJ → ℝ) → ℂ → ℂ → ℝ≥0∞, Measurable Ψ ∧
      ∀ i, ∀ᵐ ω ∂(Pi i), ∀ z ∈ A, ∀ w ∈ A,
        confMetric D ϕ A (hbari i ω) (fi i ω) z w = Ψ (confCoord γ ϕ W O (hi i ω)) z w := by
  obtain ⟨F, hFm, hF⟩ := universalLocality hD O ι Ωi Pi (fun i ω => addFun (hbari i ω) (fi i ω))
    fun i => isGFFPlusCont_addFun_of_wp (hhb i) (hf i)
  refine ⟨fun a z w => F (pairJInv O a) (ϕ z) (ϕ w), measurable_locFun hFm ϕ, fun i => ?_⟩
  filter_upwards [hc i, hF i] with ω hcω hFω z hz w hw
  exact confMetric_eq_of_locality hϕ hAV hO hcω hFω hz hw

/-- **T3, universal restriction form**: one measurable `G` on `𝒟'(A)` for countably many
couplings. -/
theorem exists_universal_confMetric_eq_restrict (hD : IsStrongLQGMetric γ D)
    (hϕ : IsConfNbhd ϕ W V) (A : TopologicalSpace.Opens ℂ) (hAV : (A : Set ℂ) ⊆ V) {ι : Type}
    [Countable ι] {Ωi : ι → Type} [∀ i, MeasurableSpace (Ωi i)] (Pi : ∀ i, Measure (Ωi i))
    [∀ i, IsProbabilityMeasure (Pi i)] (hi hbari : ∀ i, Ωi i → DistC) (fi : ∀ i, Ωi i → C(ℂ, ℝ))
    (hhb : ∀ i, IsWholePlaneGFF (hbari i) (Pi i)) (hf : ∀ i, Measurable (fi i))
    (hc : ∀ i, ∀ᵐ ω ∂(Pi i), IsConfCoupling γ ϕ W V (hi i ω) (hbari i ω) (fi i ω)) :
    ∃ G : DistOn A → ℂ → ℂ → ℝ≥0∞, Measurable G ∧
      ∀ i, ∀ᵐ ω ∂(Pi i), ∀ z ∈ A, ∀ w ∈ A,
        confMetric D ϕ A (hbari i ω) (fi i ω) z w = G (restrictTo A (hi i ω)) z w := by
  let O : TopologicalSpace.Opens ℂ := ⟨ϕ '' A, (hϕ.mono A.isOpen hAV).isOpen_image⟩
  obtain ⟨Ψ, hΨ, hΨae⟩ :=
    exists_universal_confMetric_eq_coord hD hϕ hAV O rfl Pi hi hbari fi hhb hf hc
  obtain ⟨R, hR, hRe⟩ := exists_confCoord_eq_restrict (γ := γ) hϕ A hAV O rfl
  refine ⟨Ψ ∘ R, hΨ.comp hR, fun i => ?_⟩
  filter_upwards [hΨae i] with ω hω z hz w hw
  rw [hω z hz w hw, Function.comp_apply, hRe]

/-! ## 5. Modulo additive constants -/

omit [IsProbabilityMeasure P] in
/-- **D4, modulo constants**: adding the same (random) constant to `h` and `h̄` keeps a coupling
(CC1's `IsConfCoupling.addConst`, pathwise). -/
theorem ae_isConfCoupling_addConst (hϕ : IsConfNbhd ϕ W V)
    (hc : ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) (c : Ω → ℝ) :
    ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (addConst (h ω) (c ω)) (addConst (hbar ω) (c ω)) (f ω) :=
  hc.mono fun _ hω => hω.addConst hϕ _

/-- **D4, modulo constants**: a.s., adding a (random) constant `c` to `h̄` multiplies `D^ϕ` by
`e^{ξ c}`, for every conformal neighbourhood and every continuous function. -/
theorem ae_confMetric_addConst_random (hD : IsStrongLQGMetric γ D) (hhb : IsWholePlaneGFF hbar P)
    (c : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V → ∀ (g : C(ℂ, ℝ)) (z w : ℂ),
      confMetric D ϕ V (addConst (hbar ω) (c ω)) g z w =
        ENNReal.ofReal (Real.exp (xiGamma γ * c ω)) * confMetric D ϕ V (hbar ω) g z w :=
  (ae_confMetric_addConst hD (isGFFPlusCont_of_wp hhb)).mono fun ω hω ϕ W V hϕ g z w =>
    hω ϕ W V hϕ g (c ω) z w

/-- **T3, modulo constants** (CC0 D4): for a measurable random constant `c` (e.g. `c = −h_{4r}(z)`),
a.s. `e^{ξ c} D^ϕ(·,·;A)` is a measurable function of `(h + c)|_A`. -/
theorem exists_confMetric_eq_restrict_addConst (hD : IsStrongLQGMetric γ D)
    (hϕ : IsConfNbhd ϕ W V) (A : TopologicalSpace.Opens ℂ) (hAV : (A : Set ℂ) ⊆ V)
    (hhb : IsWholePlaneGFF hbar P) (hf : Measurable f)
    (hc : ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) {c : Ω → ℝ} (hcm : Measurable c) :
    ∃ G : DistOn A → ℂ → ℂ → ℝ≥0∞, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ z ∈ A, ∀ w ∈ A,
        ENNReal.ofReal (Real.exp (xiGamma γ * c ω)) * confMetric D ϕ A (hbar ω) (f ω) z w =
          G (restrictTo A (addConst (h ω) (c ω))) z w := by
  obtain ⟨G, hG, hGae⟩ := exists_confMetric_eq_restrict hD hϕ A hAV (hhb.addConst hcm) hf
    (ae_isConfCoupling_addConst hϕ hc c)
  refine ⟨G, hG, ?_⟩
  filter_upwards [hGae, ae_confMetric_addConst_random hD hhb c] with ω h1 h2 z hz w hw
  rw [← h2 ϕ W A (hϕ.mono A.isOpen hAV) (f ω) z w]
  exact h1 z hz w hw

/-- The companion for `D_h` (Axioms II and III): a.s. `e^{ξ c} D_h(·,·;A)` is a measurable function
of `(h + c)|_A`. -/
theorem exists_internal_eq_restrict_addConst (hD : IsStrongLQGMetric γ D)
    (A : TopologicalSpace.Opens ℂ) (hh : IsWholePlaneGFF h P) {c : Ω → ℝ} (hcm : Measurable c) :
    ∃ G : DistOn A → ℂ → ℂ → ℝ≥0∞, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ z ∈ A, ∀ w ∈ A,
        ENNReal.ofReal (Real.exp (xiGamma γ * c ω)) * (D (h ω)).internal A z w =
          G (restrictTo A (addConst (h ω) (c ω))) z w := by
  obtain ⟨G, hG, hGae⟩ := hD.locality P _ (isGFFPlusCont_of_wp (hh.addConst hcm)) A
  refine ⟨G, hG, ?_⟩
  filter_upwards [hGae, hD.ae_internal_addFun_of_eq_const (isGFFPlusCont_of_wp hh)] with
    ω h1 h2 z hz w hw
  rw [← h1 z hz w hw]
  exact (h2 (ContinuousMap.const ℂ (c ω)) A (xiGamma γ * c ω) A.isOpen (fun _ _ => rfl) z w).symm

end AS

end SmallGammaGeodesics.CC
