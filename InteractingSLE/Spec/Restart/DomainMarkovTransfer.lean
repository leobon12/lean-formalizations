/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovLaw
import InteractingSLE.Spec.Exist.StagedCongr
import InteractingSLE.Spec.Sec7.Aux122DisintMart

/-!
# The domain Markov step, part 5: transferring the protected-kernel law to the regular conditional law

Packet PROVE-DOMAINMARKOV2, item (S). Under the conditional law `ν = condExpKernel P 𝓓_T ω₀` only countably many
identities can be carried over from `P`. This file proves `IsDyadicSampled`-type identities under almost every `ν`:

* **`condExp_cexp_ae_eq_of_local_countable`**: a conditional characteristic functional with local Gaussian laws is
  determined by its values at the countably many test functions `ratTest p` (rational combinations of the generating
  family on finite unions of basis sets): the step from countably many to all test functions;
* safe-set tools for driving processes with only the pathwise properties that survive a null modification
  (`IsWeakPath`: `W₀ = 0`, continuity before `ζ`, marks on their sides);
* **`ae_setIntegral_cexp_eq_cfAt_restart`**: for `P`-almost every `ω₀` with `T ω₀ < ζ ω₀`, under `ν`, for every test
  function `ψ`, every dyadic time `q` and every event `A` that is `ν`-almost surely equal to an event of the restarted
  data σ-algebra at `q` and `ν`-almost surely inside the avoidance event, `∫_A e^{i(h', ψ)} dν = ∫_A cfAt q dν`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov fwdHull chiC IsForwardSol fwdMap)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace DomainMarkov

open Coupling Ito

/-! ### Countably many test functions determine a conditional law with local Gaussian laws -/

section Countable

/-- The countable index of the test functions `ratTest p`: a finite family of basis sets and a rational combination of
the generating family on their union. -/
abbrev RatIdx : Type := RandomTest.basisFamilies × (Σ s : Finset (ℕ × ℕ), (s → ℚ))

instance : Countable RandomTest.basisFamilies := RandomTest.countable_basisFamilies.to_subtype

/-- The test function `∑ qᵢ distGen_i` on the basis union `⋃ F`, included into `V`. -/
def ratTest (V : Opens ℂ) (p : RatIdx) : TestOn V :=
  GFF.testIncl (RandomTest.basisUnion p.1.1) V
    (∑ i : p.2.1, (p.2.2 i : ℝ) • LQGMetric.distGen (RandomTest.basisUnion p.1.1) i)

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Countably many test functions suffice** (the step from countably many to all test functions). Let `X` be a
random distribution on `V`, `U ω ⊆ V` random open sets and `Ψ ω` functionals such that almost surely, for every open
`R ⊆ U ω`, `Ψ ω` restricted to `𝒟(R)` is the characteristic functional of a probability law on `𝒟'(R)`. If
`E[exp(i X(φ)) | 𝒢] = Ψ(ω, φ)` almost surely on `{tsupport φ ⊆ U ω}` for the countably many `φ = ratTest V p`, then the
same holds for every test function `φ`. -/
theorem condExp_cexp_ae_eq_of_local_countable (h𝒢 : 𝒢 ≤ mΩ) {V : Opens ℂ} {X : Ω → DistOn V}
    (hX : Measurable X) {U : Ω → Set ℂ} (hUo : ∀ ω, IsOpen (U ω)) (hUV : ∀ ω, U ω ⊆ V)
    {Ψ : Ω → TestOn V → ℂ}
    (hΨ : ∀ᵐ ω ∂P, ∀ R : Opens ℂ, (R : Set ℂ) ⊆ U ω → ∃ μ : Measure (DistOn R), IsProbabilityMeasure μ ∧
      ∀ ψ : TestOn R, ∫ v, Complex.exp (Complex.I * (v ψ : ℂ)) ∂μ = Ψ ω (GFF.testIncl R V ψ))
    (hcond : ∀ p : RatIdx, ∀ᵐ ω ∂P, tsupport (ratTest V p) ⊆ U ω →
      P[fun ω => Complex.exp (Complex.I * (X ω (ratTest V p) : ℂ)) | 𝒢] ω = Ψ ω (ratTest V p))
    (φ : TestOn V) :
    ∀ᵐ ω ∂P, tsupport φ ⊆ U ω → P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | 𝒢] ω = Ψ ω φ := by
  classical
  have hid : Measurable[mΩ, 𝒢] (id : Ω → Ω) := measurable_id'' h𝒢
  set κ := @condDistrib Ω Ω (DistOn V) _ _ _ mΩ 𝒢 X id P _ with hκ
  have hcomap : MeasurableSpace.comap (id : Ω → Ω) 𝒢 = 𝒢 := MeasurableSpace.comap_id
  -- the kernel computes the conditional characteristic function at every fixed test function
  have hk : ∀ φ : TestOn V, ∀ᵐ ω ∂P, P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | 𝒢] ω =
      ∫ u, Complex.exp (Complex.I * (u φ : ℂ)) ∂(κ ω) := by
    intro φ
    have hf : StronglyMeasurable fun u : DistOn V => Complex.exp (Complex.I * (u φ : ℂ)) :=
      (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply φ)).stronglyMeasurable
    have h1 := @condExp_ae_eq_integral_condDistrib Ω Ω (DistOn V) ℂ _ _ _ _ mΩ P _ id X 𝒢 _ _ hid
      hX.aemeasurable _ hf (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hX))
    rw [hcomap] at h1
    exact h1
  have hmap : ∀ (R : Opens ℂ) (ν : Measure (DistOn V)) (ψ : TestOn R),
      ∫ v, Complex.exp (Complex.I * (v ψ : ℂ)) ∂(ν.map (GFF.restrictDist R)) =
        ∫ u, Complex.exp (Complex.I * (u (GFF.testIncl R V ψ) : ℂ)) ∂ν := fun R ν ψ => by
    rw [integral_map (GFF.measurable_restrictDist R).aemeasurable
      (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply ψ)).aestronglyMeasurable]
    rfl
  -- on each basis union inside `U ω`, the restricted kernel has the characteristic functional `Ψ ω`
  have hB : ∀ᵐ ω ∂P, ∀ F : RandomTest.basisFamilies, (RandomTest.basisUnion F.1 : Set ℂ) ⊆ U ω →
      ∀ ψ : TestOn (RandomTest.basisUnion F.1),
        ∫ v, Complex.exp (Complex.I * (v ψ : ℂ)) ∂((κ ω).map (GFF.restrictDist (RandomTest.basisUnion F.1))) =
          Ψ ω (GFF.testIncl (RandomTest.basisUnion F.1) V ψ) := by
    have hall : ∀ᵐ ω ∂P, ∀ p : RatIdx, tsupport (ratTest V p) ⊆ U ω →
        ∫ u, Complex.exp (Complex.I * (u (ratTest V p) : ℂ)) ∂(κ ω) = Ψ ω (ratTest V p) :=
      ae_all_iff.2 fun p => by
        filter_upwards [hcond p, hk (ratTest V p)] with ω h1 h2 hsupp
        rw [← h2, h1 hsupp]
    filter_upwards [hall, hΨ] with ω hω hΨω F hFU ψ
    have hle : RandomTest.basisUnion F.1 ≤ V := fun x hx => hUV ω (hFU hx)
    obtain ⟨μ, hμP, hμ⟩ := hΨω (RandomTest.basisUnion F.1) hFU
    have heq : (κ ω).map (GFF.restrictDist (RandomTest.basisUnion F.1)) = μ := by
      refine RandomTest.ext_of_integral_cexp_rat fun s q => ?_
      have hts : tsupport (ratTest V ⟨F, ⟨s, q⟩⟩) ⊆ U ω := by
        simp only [ratTest]
        rw [GFF.coe_testIncl hle]
        exact (TestFunction.tsupport_subset _).trans hFU
      have h1 := hω ⟨F, ⟨s, q⟩⟩ hts
      simp only [ratTest] at h1
      rw [hmap, h1, hμ]
    rw [heq, hμ]
  -- disintegration at the test function `φ`
  filter_upwards [hk φ, hB] with ω h2ω hBω hTU
  rw [h2ω]
  obtain ⟨F, hF, hTF, hFU⟩ := RandomTest.exists_basisUnion φ.hasCompactSupport.isCompact (hUo ω) hTU
  have hle : RandomTest.basisUnion F ≤ V := fun x hx => hUV ω (hFU hx)
  set TR : TestOn (RandomTest.basisUnion F) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hTF⟩ with hTR
  have hTe : GFF.testIncl (RandomTest.basisUnion F) V TR = φ := by
    ext z
    rw [GFF.coe_testIncl hle]
    rfl
  rw [← hTe, ← hmap, hBω ⟨F, hF⟩ hFU]

end Countable

/-! ### Safe events for paths with the null-modification-stable properties -/

section Weak

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The pathwise properties of a driving path that survive a modification on a null set (by `0`): the driver starts
at `0` and is continuous before `ζ`, and the marks stay on their sides before `ζ`. -/
def IsWeakPath (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  w 0 = 0 ∧ ContinuousOn w {t | (t : ℝ≥0∞) < ζ} ∧ (∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}) ∧
    (∀ j, ContinuousOn (vR j) {t | (t : ℝ≥0∞) < ζ}) ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, vL i t ≤ w t) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ j, w t ≤ vR j t

/-- An integrated `SLE` path has the weak properties. -/
theorem IsIntegratedSLEPath.isWeakPath {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {z : ℝ≥0∞}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b z) : IsWeakPath w vL vR z :=
  ⟨hp.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1⟩

/-- The constant zero path has the weak properties. -/
theorem isWeakPath_zero (z : ℝ≥0∞) :
    IsWeakPath (fun _ => (0 : ℝ)) (fun (_ : Fin nL) _ => (0 : ℝ)) (fun (_ : Fin nR) _ => (0 : ℝ)) z :=
  ⟨rfl, continuousOn_const, fun _ => continuousOn_const, fun _ => continuousOn_const, fun _ _ _ => le_rfl,
    fun _ _ _ => le_rfl⟩

variable (hweak : ∀ ω, IsWeakPath (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))

include hweak in
theorem safeU_subset_avoidSet_of_weak (G : Set Ω) (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) :
    safeU W ζ G ψ q ⊆ avoidSet W ζ ψ q := fun ω hω => by
  obtain ⟨m, hm⟩ := mem_iUnion.1 hω
  have hw : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := (hweak ω).2.1
  have hs : IsSafeAt (tsupport (ψ : ℂ → ℝ)) (1 / ((m : ℝ) + 1)) q q (ζ ω) (W · ω) q := hm.2
  have hd : Disjoint (tsupport (ψ : ℂ → ℝ)) (fwdHull (rpath (W · ω)) q) :=
    disjoint_fwdHull_of_isSafeAt hw (tsupport_subset_H ψ) hs
  exact ⟨hs.1, hd⟩

include hweak in
/-- On the avoidance event, a point of `G` lies in the safe union. -/
theorem mem_safeU_of_mem_avoidSet {G : Set Ω} (ψ : TestOn upperHalfPlaneOpens) {q : ℝ≥0} {ω : Ω} (hωG : ω ∈ G)
    (hω : ω ∈ avoidSet W ζ ψ q) : ω ∈ safeU W ζ G ψ q := by
  have hKH : tsupport (ψ : ℂ → ℝ) ⊆ H := tsupport_subset_H ψ
  have halive : ∀ z ∈ tsupport (ψ : ℂ → ℝ), ∃ v, IsForwardSol (rpath (W · ω)) z q v := fun z hz =>
    exists_isForwardSol_of_mem q.coe_nonneg ⟨hKH hz, fun hzK => Set.disjoint_left.1 hω.2 hz hzK⟩
  obtain ⟨δ, hδ, hs⟩ := exists_isSafeAt_self (hweak ω).2.1 (hweak ω).1 ψ.hasCompactSupport.isCompact hKH hω.1
    halive
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  exact mem_safeU_of_isSafeAt hωG (hs.mono hm.le le_rfl le_rfl)

include hweak in
theorem norm_cfAt_le_one_of_mem_safeU' (u : Ω → ℝ≥0 → ℂ → ℝ) {G : Set Ω} (ψ : TestOn upperHalfPlaneOpens)
    {q : ℝ≥0} {ω : Ω} (hω : ω ∈ safeU W ζ G ψ q) : ‖cfAt κ W u ψ 1 (fun _ => q) ω‖ ≤ 1 := by
  obtain ⟨m, hm⟩ := mem_iUnion.1 hω
  exact norm_cfAt_le_one u 1 ψ (r := fun _ => q) (continuousOn_rpath (hweak ω).2.1 hm.2.1)
    (hweak ω).1 (fun z hz => (hm.2.2.2.2 z hz).1)

variable {𝓖 : Filtration ℝ≥0 mΩ} (hWa : AdaptedBefore 𝓖 ζ W) {G : Set Ω} (hG0 : MeasurableSet[𝓖 0] G)

include hweak hWa hG0 in
theorem measurableSet_safeU (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) :
    MeasurableSet[𝓖 q] (safeU W ζ G ψ q) :=
  MeasurableSet.iUnion fun m => measurableSet_safeSet hWa (fun ω _ => (hweak ω).2.1) hG0 (tsupport_subset_H ψ)
    (by positivity) q

include hweak hWa hG0 in
/-- On a safe event at a fixed time `q`, `cfAt q` is `𝓖_q`-measurable. -/
theorem measurable_safeSet_indicator_cfAt_of_weak (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (ψ : TestOn upperHalfPlaneOpens) {δ : ℝ} (hδ : 0 < δ) (q : ℝ≥0) :
    Measurable[𝓖 q] ((safeSet W ζ G ψ δ q).indicator (cfAt κ W u ψ 1 fun _ => q)) := by
  have hKH : tsupport (ψ : ℂ → ℝ) ⊆ H := tsupport_subset_H ψ
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω _ => (hweak ω).2.1
  have e : (safeSet W ζ G ψ δ q).indicator (cfAt κ W u ψ 1 fun _ => q) =
      (safeSet W ζ G ψ δ q).indicator (fun ω =>
        Complex.exp (Complex.I * 1 * ((meanK κ ρL ρR W VL VR ζ G ψ δ q ω : ℝ) : ℂ) -
          1 ^ 2 * ((energyK W ζ G ψ δ q ω : ℝ) : ℂ) / 2)) := by
    refine indicator_congr fun ω hω => ?_
    have hw := (hweak ω).2.1
    have hvL : ∀ i, VL i q ω ≤ W q ω := (hweak ω).2.2.2.2.1 q hω.2.1
    have hvR : ∀ i, W q ω ≤ VR i q ω := (hweak ω).2.2.2.2.2 q hω.2.1
    have hmean : (∫ z, couplingMean κ (fun x : ℝ => W x.toNNReal ω) q (u ω q) z * ψ z) =
        ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) q z * ψ z := by
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ tsupport (ψ : ℂ → ℝ)
      · have e := couplingMean_eq_meanCan (κ := κ) (ρL := ρL) (ρR := ρR) (w := (W · ω))
          (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hw hKH hω.2 hδ le_rfl hz hvL hvR (hu ω q)
        exact congrArg (· * ψ z) e
      · simp [image_eq_zero_of_notMem_tsupport hz]
    have hm : meanK κ ρL ρR W VL VR ζ G ψ δ q ω =
        ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) q z * ψ z := by
      simp only [meanK, hω, ↓reduceIte]
    have he : energyK W ζ G ψ δ q ω = loewnerGreenEnergy (rpath (W · ω)) q ψ := by
      simp only [energyK, hω, ↓reduceIte]
    rw [hm, he, ← hmean]
    rfl
  rw [e]
  refine Measurable.indicator ?_ (measurableSet_safeSet hWa hGc hG0 hKH hδ q)
  have h1 := measurable_meanK hWa hGc hG0 hKH hδ κ ρL ρR hVLa hVRa ψ.continuous.measurable q
  have h2 := measurable_energyK hWa hGc hG0 hKH hδ ψ.continuous.measurable q
  exact Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp h1)).sub
    ((measurable_const.mul (Complex.measurable_ofReal.comp h2)).div_const 2))

include hweak hWa hG0 in
/-- `cfAt q` restricted to the safe union is `𝓖_q`-measurable. -/
theorem measurable_safeU_indicator_cfAt_of_weak (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) :
    Measurable[𝓖 q] ((safeU W ζ G ψ q).indicator (cfAt κ W u ψ 1 fun _ => q)) := by
  have hmK : ∀ m : ℕ, Measurable[𝓖 q]
      ((safeSet W ζ G ψ (1 / ((m : ℝ) + 1)) q).indicator (cfAt κ W u ψ 1 fun _ => q)) := fun m =>
    measurable_safeSet_indicator_cfAt_of_weak hweak hWa hG0 u hu hVLa hVRa ψ (by positivity) q
  refine @measurable_of_tendsto_metrizable Ω ℂ (𝓖 q) _ _ _ _ _ _ hmK ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ safeU W ζ G ψ q
  · obtain ⟨m₀, hm₀⟩ := mem_iUnion.1 hω
    rw [indicator_of_mem hω]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m₀] with m hm
    have hle : 1 / ((m : ℝ) + 1) ≤ 1 / ((m₀ : ℝ) + 1) := by gcongr
    rw [indicator_of_mem (show ω ∈ safeSet W ζ G ψ (1 / ((m : ℝ) + 1)) q from
      ⟨hm₀.1, hm₀.2.mono hle le_rfl le_rfl⟩)]
  · rw [indicator_of_notMem hω]
    exact tendsto_const_nhds.congr fun m =>
      (indicator_of_notMem (fun h' => hω (mem_iUnion.2 ⟨m, h'⟩)) _).symm

end Weak

/-! ### The restarted data, modified on a null set -/

section Data

open Sec7.Aux122Disint Sec2.Restart Sec5.Markov

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {a : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0}

/-- The restarted driving data on the live event `{T < ζ}`, and `0` off it (indexed as in Aux. lemma 122). -/
def rsData (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (T : Ω → ℝ≥0) : Option (Fin nL ⊕ Fin nR) → ℝ≥0 → Ω → ℝ :=
  wordData (liveSet ζ T) (rsX ζ W W T) (fun i => rsX ζ (VL i) W T) (fun j => rsX ζ (VR j) W T)

/-- The restarted driving data, further set to `0` on a null set `N`. -/
def zData (N : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (i : Option (Fin nL ⊕ Fin nR)) : ℝ≥0 → Ω → ℝ :=
  zeroOn N (rsData ζ W VL VR T i)

omit mΩ in
theorem zData_of_mem {N : Set Ω} {ω : Ω} (h : ω ∈ N) (i : Option (Fin nL ⊕ Fin nR)) (t : ℝ≥0) :
    zData N ζ W VL VR T i t ω = 0 := zeroOn_of_mem h t

omit mΩ in
theorem zData_of_notMem_of_notMem {N : Set Ω} {ω : Ω} (h : ω ∉ N) (hF : ω ∉ liveSet ζ T)
    (i : Option (Fin nL ⊕ Fin nR)) (t : ℝ≥0) : zData N ζ W VL VR T i t ω = 0 := by
  rcases i with _ | i | j <;> simp only [zData, rsData, wordData, zeroOn_of_notMem h, onF_of_notMem hF]

omit mΩ in
theorem zData_none {N : Set Ω} {ω : Ω} (h : ω ∉ N) (hF : ω ∈ liveSet ζ T) (t : ℝ≥0) :
    zData N ζ W VL VR T none t ω = rsX ζ W W T t ω := by
  simp only [zData, rsData, wordData, zeroOn_of_notMem h, onF_of_mem hF]

omit mΩ in
theorem zData_inl {N : Set Ω} {ω : Ω} (h : ω ∉ N) (hF : ω ∈ liveSet ζ T) (i : Fin nL) (t : ℝ≥0) :
    zData N ζ W VL VR T (some (Sum.inl i)) t ω = rsX ζ (VL i) W T t ω := by
  simp only [zData, rsData, wordData, zeroOn_of_notMem h, onF_of_mem hF]

omit mΩ in
theorem zData_inr {N : Set Ω} {ω : Ω} (h : ω ∉ N) (hF : ω ∈ liveSet ζ T) (j : Fin nR) (t : ℝ≥0) :
    zData N ζ W VL VR T (some (Sum.inr j)) t ω = rsX ζ (VR j) W T t ω := by
  simp only [zData, rsData, wordData, zeroOn_of_notMem h, onF_of_mem hF]

omit mΩ in
/-- **Every path of the modified restarted data has the weak properties**, if the restarted paths have them off `N`
on the live event. -/
theorem isWeakPath_zData {N : Set Ω}
    (hN : ∀ ω, ω ∉ N → ω ∈ liveSet ζ T → IsWeakPath (fun t => rsX ζ W W T t ω)
      (fun i t => rsX ζ (VL i) W T t ω) (fun j t => rsX ζ (VR j) W T t ω) (restartLife ζ T ω)) (ω : Ω) :
    IsWeakPath (fun t => zData N ζ W VL VR T none t ω) (fun i t => zData N ζ W VL VR T (some (Sum.inl i)) t ω)
      (fun j t => zData N ζ W VL VR T (some (Sum.inr j)) t ω) (restartLife ζ T ω) := by
  by_cases hωN : ω ∈ N
  · simp only [zData_of_mem hωN]
    exact isWeakPath_zero _
  by_cases hωF : ω ∈ liveSet ζ T
  · simp only [zData_none hωN hωF, zData_inl hωN hωF, zData_inr hωN hωF]
    exact hN ω hωN hωF
  · simp only [zData_of_notMem_of_notMem hωN hωF]
    exact isWeakPath_zero _

/-- The weak properties of the restarted paths hold off a measurable null set, which can be chosen to also exclude
any given null event. -/
theorem exists_null_isWeakPath (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) {p : Ω → Prop}
    (hp : ∀ᵐ ω ∂P, p ω) :
    ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ ∀ ω, ω ∉ N → p ω ∧ (ω ∈ liveSet ζ T →
      IsWeakPath (fun t => rsX ζ W W T t ω) (fun i t => rsX ζ (VL i) W T t ω) (fun j t => rsX ζ (VR j) W T t ω)
        (restartLife ζ T ω)) := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  obtain ⟨𝓕', B', hR⟩ := isRandomWordEvolution_restart hE hX hT
  have hgood : ∀ᵐ ω ∂P, p ω ∧ (ω ∈ liveSet ζ T →
      IsWeakPath (fun t => rsX ζ W W T t ω) (fun i t => rsX ζ (VL i) W T t ω) (fun j t => rsX ζ (VR j) W T t ω)
        (restartLife ζ T ω)) := by
    filter_upwards [hp, hR.2.2.2.2.2.2.2.2] with ω h1 h2
    exact ⟨h1, fun hF => IsIntegratedSLEPath.isWeakPath (h2 hF)⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  refine ⟨N, hNm, hN0, fun ω hω => ?_⟩
  by_contra hc
  exact hω (hNsub hc)

/-! #### Measurability in the restarted filtration -/

/-- A measurable null set is an event of every restarted σ-algebra `𝓓_{T+t}`. -/
theorem measurableSet_restartFiltration_of_null (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) {S : Set Ω} (hS : MeasurableSet S)
    (hS0 : P S = 0) (t : ℝ≥0) : MeasurableSet[restartFiltration (drivingFiltration P hX) T hT t] S := by
  have hnull : ∀ u, MeasurableSet[drivingFiltration P hX u] S := fun u =>
    Ito.measurableSet_usualAugmentation_of_null hS hS0 u
  have hle : drivingFiltration P hX 0 ≤ ⨆ i, drivingFiltration P hX i := le_iSup _ (0 : ℝ≥0)
  refine ⟨hle _ (hnull 0), fun u => ?_⟩
  exact (hnull u).inter (isStoppingTime_add_const hT t u)

/-- A process with measurable killed values and lifetime events is adapted before the lifetime, also after a
modification by `0` on an event of every `𝓖_t`. -/
theorem adaptedBefore_zeroOn_of_killAt {𝓖 : Filtration ℝ≥0 mΩ} {ζ' : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} {N : Set Ω}
    (hlt : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < ζ' ω})
    (hk : ∀ t, Measurable[𝓖 t] (killAt ζ' X t)) (hN : ∀ t, MeasurableSet[𝓖 t] N) :
    AdaptedBefore 𝓖 ζ' (zeroOn N X) := by
  classical
  intro t A hA
  have hk' : Measurable[𝓖 t] (killAt ζ' (zeroOn N X) t) := by
    rw [killAt_zeroOn]
    exact Measurable.ite (hN t) measurable_const (hk t)
  have e : {ω | (t : ℝ≥0∞) < ζ' ω ∧ zeroOn N X t ω ∈ A} =
      {ω | (t : ℝ≥0∞) < ζ' ω} ∩ killAt ζ' (zeroOn N X) t ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, killAt]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa only [h1, ↓reduceIte] using h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa only [h1, ↓reduceIte] using h2⟩
  rw [e]
  exact (hlt t).inter (hk' hA)

variable (hX : IsMeasurableKilledDriving W VL VR ζ)
  (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))

include hT in
/-- The restarted lifetime events are events of the restarted filtration. -/
theorem measurableSet_lt_restartLife (t : ℝ≥0) :
    MeasurableSet[restartFiltration (drivingFiltration P hX) T hT t] {ω | (t : ℝ≥0∞) < restartLife ζ T ω} := by
  have hζ := Ito.isStoppingTime_lifetime (adaptedBefore_driving (P := P) hX).1
  have e : {ω | (t : ℝ≥0∞) < restartLife ζ T ω} = {ω | ((T ω + t : ℝ≥0) : ℝ≥0∞) < ζ ω} := by
    ext ω
    exact coe_lt_sub_iff _ _
  rw [e]
  exact measurableSet_add_lt hT hζ t

/-- The live event is an event of every restarted σ-algebra. -/
theorem measurableSet_liveSet_restart (t : ℝ≥0) :
    MeasurableSet[restartFiltration (drivingFiltration P hX) T hT t] (liveSet ζ T) := by
  have h := measurableSet_liveSet hX hT
  rw [← restartFiltration_zero hT] at h
  exact (restartFiltration (drivingFiltration P hX) T hT).mono (zero_le (a := t)) _ h

/-- The restarted data have `𝓓_{T+t}`-measurable killed values. -/
theorem measurable_killAt_rsData (i : Option (Fin nL ⊕ Fin nR)) (t : ℝ≥0) :
    Measurable[restartFiltration (drivingFiltration P hX) T hT t]
      (killAt (restartLife ζ T) (rsData ζ W VL VR T i) t) := by
  obtain ⟨hWa, hLa, hRa⟩ := adaptedBefore_driving (P := P) hX
  have hζ := Ito.isStoppingTime_lifetime hWa
  have hWp := isStronglyProgressive_progVersion hWa
  have hF := measurableSet_liveSet_restart hX hT t
  rcases i with _ | i | j
  · exact measurable_killAt_onF (adaptedBefore_restart hT hζ hWp hWp) hF
  · exact measurable_killAt_onF (adaptedBefore_restart hT hζ (isStronglyProgressive_progVersion (hLa i)) hWp) hF
  · exact measurable_killAt_onF (adaptedBefore_restart hT hζ (isStronglyProgressive_progVersion (hRa j)) hWp) hF

/-- **The modified restarted data are adapted before the restarted lifetime to the restarted filtration.** -/
theorem adaptedBefore_zData_restart {N : Set Ω} (hNm : MeasurableSet N) (hN0 : P N = 0)
    (i : Option (Fin nL ⊕ Fin nR)) :
    AdaptedBefore (restartFiltration (drivingFiltration P hX) T hT) (restartLife ζ T) (zData N ζ W VL VR T i) :=
  adaptedBefore_zeroOn_of_killAt (measurableSet_lt_restartLife hX hT) (measurable_killAt_rsData hX hT i)
    (measurableSet_restartFiltration_of_null hX hT hNm hN0)

include hX hT in
/-- The data of the modified restarted processes satisfy the standing measurability of Aux. lemma 122
(no Brownian coordinate). -/
theorem dataMeas_rsData {N : Set Ω} (hNm : MeasurableSet N) :
    DataMeas N (restartLife ζ T) (fun _ _ => (0 : ℝ)) (rsData ζ W VL VR T) :=
  ⟨hNm, fun t => (restartFiltration (drivingFiltration P hX) T hT).le t _ (measurableSet_lt_restartLife hX hT t),
    fun _ => measurable_const,
    fun i t => (measurable_killAt_rsData hX hT i t).mono ((restartFiltration (drivingFiltration P hX) T hT).le t)
      le_rfl⟩

/-- **The data filtration of the restarted processes is contained in the restarted filtration.** -/
theorem dataFilt_le_restart {N : Set Ω} (hNm : MeasurableSet N) (hN0 : P N = 0) (t : ℝ≥0) :
    dataFilt N (restartLife ζ T) (fun _ _ => (0 : ℝ)) (rsData ζ W VL VR T) t ≤
      restartFiltration (drivingFiltration P hX) T hT t := by
  classical
  refine inf_le_left.trans (MeasurableSpace.generateFrom_le ?_)
  set 𝓖' := restartFiltration (drivingFiltration P hX) T hT
  intro A hA
  rcases hA with (rfl | rfl) | hA
  · exact measurableSet_restartFiltration_of_null hX hT hNm hN0 t
  · exact measurableSet_lt_restartLife hX hT t
  · obtain ⟨q, hq, hA⟩ := mem_iUnion₂.1 hA
    rcases hA with (rfl | ⟨b, rfl⟩) | hA
    · exact 𝓖'.mono hq _ (measurableSet_lt_restartLife hX hT _)
    · have e : zeroOn N (fun _ _ => (0 : ℝ)) (rt q) = fun _ => (0 : ℝ) := by
        funext ω; by_cases h : ω ∈ N <;> simp [zeroOn, h]
      rw [e]
      exact (measurable_const (a := (0 : ℝ))) measurableSet_Iio
    · obtain ⟨i, b, rfl⟩ := mem_iUnion.1 hA
      rw [killAt_zeroOn]
      refine 𝓖'.mono hq _ ((Measurable.ite (measurableSet_restartFiltration_of_null hX hT hNm hN0 _)
        measurable_const (measurable_killAt_rsData hX hT i _)) measurableSet_Iio)

omit mΩ in
/-- Continuity of the restarted data before the restarted lifetime, off `N`. -/
theorem continuousOn_rsData {N : Set Ω}
    (hN : ∀ ω, ω ∉ N → ω ∈ liveSet ζ T → IsWeakPath (fun t => rsX ζ W W T t ω)
      (fun i t => rsX ζ (VL i) W T t ω) (fun j t => rsX ζ (VR j) W T t ω) (restartLife ζ T ω)) :
    ∀ ω, ω ∉ N → ∀ i, ContinuousOn (fun t => rsData ζ W VL VR T i t ω) {t | (t : ℝ≥0∞) < restartLife ζ T ω} := by
  intro ω hω i
  have hw := isWeakPath_zData hN ω
  have hc : ContinuousOn (fun t => zData N ζ W VL VR T i t ω) {t | (t : ℝ≥0∞) < restartLife ζ T ω} := by
    rcases i with _ | i | j
    · exact hw.2.1
    · exact hw.2.2.1 i
    · exact hw.2.2.2.1 j
  simpa only [zData, zeroOn_of_notMem hω] using hc

end Data

/-! ### The protected-kernel identity at the deterministic restarted times, under `P` -/

section Kernel

open Sec7 Sec7.Aux122Disint Sec2.Restart Sec5.Markov LocalExt

variable {κ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {T : Ω → ℝ≥0} {N : Set Ω}

/-- The modified restarted driver. -/
def zW (N : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (T : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ := zData N ζ W VL VR T none

/-- The modified restarted left marks. -/
def zVL (N : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (T : Ω → ℝ≥0) : Fin nL → ℝ≥0 → Ω → ℝ := fun i => zData N ζ W VL VR T (some (Sum.inl i))

/-- The modified restarted right marks. -/
def zVR (N : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (T : Ω → ℝ≥0) : Fin nR → ℝ≥0 → Ω → ℝ := fun j => zData N ζ W VL VR T (some (Sum.inr j))

/-- The bounded harmonic extension of the modified restarted force data at time `s`. -/
def uZ (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (N : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) : Ω → ℝ≥0 → ℂ → ℝ := fun ω s =>
  bheAt κ ρL ρR (fun i => zVL N ζ W VL VR T i s ω - zW N ζ W VL VR T s ω)
    (fun j => zVR N ζ W VL VR T j s ω - zW N ζ W VL VR T s ω)

omit mΩ in
theorem isBoundedHarmonicExtension_uZ (ω : Ω) (s : ℝ≥0) :
    IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => zVL N ζ W VL VR T i s ω - zW N ζ W VL VR T s ω)
        (fun j => zVR N ζ W VL VR T j s ω - zW N ζ W VL VR T s ω))
      (forceJumpSet (fun i => zVL N ζ W VL VR T i s ω - zW N ζ W VL VR T s ω)
        (fun j => zVR N ζ W VL VR T j s ω - zW N ζ W VL VR T s ω)) (uZ κ ρL ρR N ζ W VL VR T ω s) :=
  isBoundedHarmonicExtension_bheAt κ ρL ρR _ _

/-- The good paths off `N`: the restarted progressive versions agree with `restartDrv`, `restartMark` before the
restarted lifetime, and have the weak properties on the live event. -/
def IsGoodOff (N : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) : Prop :=
  ∀ ω, ω ∉ N → ((T ω : ℝ≥0∞) < ζ ω → ∀ t : ℝ≥0, (t : ℝ≥0∞) < restartLife ζ T ω →
      rsX ζ W W T t ω = restartDrv W T t ω ∧ (∀ i, rsX ζ (VL i) W T t ω = restartMark (VL i) W T t ω) ∧
        ∀ j, rsX ζ (VR j) W T t ω = restartMark (VR j) W T t ω) ∧
    (ω ∈ liveSet ζ T → IsWeakPath (fun t => rsX ζ W W T t ω) (fun i t => rsX ζ (VL i) W T t ω)
      (fun j t => rsX ζ (VR j) W T t ω) (restartLife ζ T ω))

theorem exists_isGoodOff (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) :
    ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ IsGoodOff N ζ W VL VR T := by
  obtain ⟨N, hNm, hN0, hN⟩ := exists_null_isWeakPath hE hX hT
    ((ae_rsX_eq (T := T) hE).mono fun ω h hT => (h hT).2.2)
  exact ⟨N, hNm, hN0, fun ω hω => hN ω hω⟩

omit mΩ in
theorem IsGoodOff.isWeakPath (hN : IsGoodOff N ζ W VL VR T) (ω : Ω) :
    IsWeakPath (fun t => zW N ζ W VL VR T t ω) (fun i t => zVL N ζ W VL VR T i t ω)
      (fun j t => zVR N ζ W VL VR T j t ω) (restartLife ζ T ω) :=
  isWeakPath_zData (fun ω hω hF => (hN ω hω).2 hF) ω

omit mΩ in
/-- Off `N`, before the restarted lifetime, the modified restarted processes are `restartDrv`, `restartMark`. -/
theorem IsGoodOff.eq_restart (hN : IsGoodOff N ζ W VL VR T) {ω : Ω} (hωN : ω ∉ N) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < restartLife ζ T ω) :
    zW N ζ W VL VR T t ω = restartDrv W T t ω ∧ (∀ i, zVL N ζ W VL VR T i t ω = restartMark (VL i) W T t ω) ∧
      ∀ j, zVR N ζ W VL VR T j t ω = restartMark (VR j) W T t ω := by
  have hTζ : (T ω : ℝ≥0∞) < ζ ω := tsub_pos_iff_lt.1 (lt_of_le_of_lt zero_le ht)
  have hF : ω ∈ liveSet ζ T := hTζ
  obtain ⟨h1, h2, h3⟩ := (hN ω hωN).1 hTζ t ht
  refine ⟨?_, fun i => ?_, fun j => ?_⟩
  · simp only [zW, zData_none hωN hF, h1]
  · simp only [zVL, zData_inl hωN hF, h2 i]
  · simp only [zVR, zData_inr hωN hF, h3 j]

/-- **The protected-kernel identity of the restarted field at a deterministic restarted time `q`**, under `P`: on the
safe union `S` (inside the avoidance event of the modified restarted driver),
`E[1_S e^{i(h', ψ)} | 𝓓_{T+q}] = 1_S cfAt q`. -/
theorem condExp_safeU_indicator_eq [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω →
      K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    (hNm : MeasurableSet N) (hN0 : P N = 0) (hN : IsGoodOff N ζ W VL VR T)
    (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) :
    P[(safeU (zW N ζ W VL VR T) (restartLife ζ T) univ ψ q).indicator
        (fun ω => Complex.exp (Complex.I * (restartField κ (h ω, K ω) ψ : ℂ))) |
          restartFiltration (drivingFiltration P hX) T hT q] =ᵐ[P]
      (safeU (zW N ζ W VL VR T) (restartLife ζ T) univ ψ q).indicator
        (cfAt κ (zW N ζ W VL VR T) (uZ κ ρL ρR N ζ W VL VR T) ψ 1 fun _ => q) := by
  set 𝓖' := restartFiltration (drivingFiltration P hX) T hT with h𝓖'
  set S := safeU (zW N ζ W VL VR T) (restartLife ζ T) univ ψ q with hSdef
  have hweak := hN.isWeakPath
  have hWa : AdaptedBefore 𝓖' (restartLife ζ T) (zW N ζ W VL VR T) := adaptedBefore_zData_restart hX hT hNm hN0 none
  have hS : MeasurableSet[𝓖' q] S := measurableSet_safeU hweak hWa MeasurableSet.univ ψ q
  have hKm' : Measurable K := hKm.mono hT.measurableSpace_le le_rfl
  have hXm : Measurable fun ω => restartField κ (h ω, K ω) ψ :=
    (LQGMetric.measurable_distOn_apply ψ).comp ((measurable_restartField κ).comp (hC.2.1.prodMk hKm'))
  have hXi : Integrable (fun ω => Complex.exp (Complex.I * (restartField κ (h ω, K ω) ψ : ℂ))) P :=
    GFF.integrable_exp_I_mul hXm
  have h1 := condExp_indicator hXi hS
  have hτ := isStoppingTime_const 𝓖' q
  have hmain := restartField_condExp_of_lt hC hκ hX hT hKm hK hτ
    (fun ω => bheAt κ ρL ρR
      (fun i => restartMark (VL i) W T (((q : WithTop ℝ≥0)).untopD 0) ω -
        restartDrv W T (((q : WithTop ℝ≥0)).untopD 0) ω)
      (fun j => restartMark (VR j) W T (((q : WithTop ℝ≥0)).untopD 0) ω -
        restartDrv W T (((q : WithTop ℝ≥0)).untopD 0) ω))
    (fun ω => isBoundedHarmonicExtension_bheAt κ ρL ρR _ _) ψ
  rw [IsStoppingTime.measurableSpace_const] at hmain
  simp only [WithTop.untopD_coe] at hmain
  filter_upwards [h1, hmain, measure_eq_zero_iff_ae_notMem.1 hN0] with ω h1ω hmω hωN
  rw [h1ω]
  by_cases hωS : ω ∈ S
  · rw [indicator_of_mem hωS, indicator_of_mem hωS]
    obtain ⟨hqζ, hdis⟩ := safeU_subset_avoidSet_of_weak hweak univ ψ q hωS
    have hagree : ∀ t : ℝ≥0, (t : ℝ≥0∞) < restartLife ζ T ω → restartDrv W T t ω = zW N ζ W VL VR T t ω :=
      fun t ht => (hN.eq_restart hωN ht).1.symm
    have hhull := Exist.Staged.fwdHull_eq_of_agree hagree hqζ
    have hEq := Exist.Staged.eqOn_Icc_of_agree hagree hqζ
    rw [hhull] at hmω
    rw [hmω (by exact_mod_cast hqζ) hdis]
    have hu : (bheAt κ ρL ρR (fun i => restartMark (VL i) W T q ω - restartDrv W T q ω)
        (fun j => restartMark (VR j) W T q ω - restartDrv W T q ω)) = uZ κ ρL ρR N ζ W VL VR T ω q := by
      obtain ⟨e1, e2, e3⟩ := hN.eq_restart hωN hqζ
      simp only [uZ, e1, e2, e3]
    have hint : (∫ z, couplingMean κ (fun s : ℝ => zW N ζ W VL VR T s.toNNReal ω) (q : ℝ≥0)
        (uZ κ ρL ρR N ζ W VL VR T ω q) z * ψ z) =
        ∫ z, couplingMean κ (fun s : ℝ => restartDrv W T s.toNNReal ω) (q : ℝ≥0)
          (uZ κ ρL ρR N ζ W VL VR T ω q) z * ψ z := by
      congr 1
      funext z
      congr 1
      exact Sec7.Lemma71B.couplingMean_congr q.2 hEq κ _ z
    simp only [cfAt]
    rw [hu, hint, Exist.Staged.loewnerGreenEnergy_congr hEq]
    congr 1
    push_cast
    ring
  · rw [indicator_of_notMem hωS, indicator_of_notMem hωS]

end Kernel

end DomainMarkov

end Restart

end InteractingSLE
