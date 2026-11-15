/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtHComap
import InteractingSLE.Spec.Sec7.LocalExtJRef
import InteractingSLE.Spec.Coupling.Assembly11BProvider
import InteractingSLE.Spec.Coupling.ResampleProjBridge
import InteractingSLE.Spec.Restart.ChartGauss

/-!
# A family reference for every ordered word, and its pullback along measure-preserving maps

Packet PROVE-DOMAINMARKOV10 (Aux. lemma 54 by the whole-field route). The extension of a stopped coupling lives on
`Ω × Ω₀`, where `Ω₀` carries a full reference coupling of the word, read through the second factor, and the field is
the stopped coupling's field read through the first factor; the two fields agree almost surely once the joint law of
the field and the stopped history is identified (ruling R38, Part C). This file supplies the reference and the transfer:

* `IsFamilyRef`: a full coupling of the word with Theorem 1.1's two family structures — the protected-kernel family
  (`Coupling.IsFamilySampled`, the conditional-law clause) and the projection family (`Coupling.IsFamilyLocal`,
  locality) — both of which are integral identities over events of stopped σ-algebras at **real** stops, so they pull
  back along measure-preserving maps without a general stopping-time pullback;
* `IsFamilyRef.isOptionalHullCoupling`: such a coupling satisfies the frozen optional hull specification (the proof of
  `Coupling.exists_isOptionalHullCoupling_of_finiteFamilyProj`);
* `exists_isFamilyRef`: Theorem 1.1's construction on a standard Borel driving space (`LocalExt.
  thm22StdBorelStatement_of_ordered`, `Coupling.exists_locCoupling_of_evolution`,
  `Coupling.finiteFamilyProjStatement`) gives a family reference on a standard Borel space, for every ordered word;
* **`IsFamilyRef.comap`**: along a measurable `π : Ω' → Ω₀` with `μ.map π = P₀`, the pulled-back evolution with **any**
  measurable field `h'` that is almost surely `h ∘ π` (and has the GFF law of the initial data) is again a family
  reference (`LocalExt.isStoppingTime_comap`, `LocalExt.isSampledAt_comap`,
  `LocalExt.exists_comap_ae_eq_of_measurableSet_stopped`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace WholeFieldStopped

open Coupling LQGMetric Ito
open SupercriticalConformalCovariance.GM24 (smoothDist)

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-! ### The family reference -/

section Def

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **A family reference**: a full integrated evolution of the word with a measurable field having the GFF law of the
initial data, family-sampled (Theorem 1.1's conditional-law clause at a countable family of real stops) and
family-local for the centred field (Theorem 1.1's locality family). -/
def IsFamilyRef (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens) :
    Prop :=
  IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ ∧ Measurable h ∧
    (∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ →
      IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P) ∧
    IsFamilySampled κ ρL ρR P 𝓕 W VL VR ζ h ∧
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ →
      IsFamilyLocal P 𝓕 W ζ (fun ω => h ω - smoothDist upperHalfPlaneOpens u₀)

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **A family reference is an optional hull coupling** (the assembly of
`Coupling.exists_isOptionalHullCoupling_of_finiteFamilyProj`: the conditional-law clause from the sampled family,
locality from the local family with the explicit bounded harmonic extension `Impl.forceExt`). -/
theorem IsFamilyRef.isOptionalHullCoupling (href : IsFamilyRef κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ) :
    IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h := by
  obtain ⟨hE, hh, hgff, hfamS, hfamL⟩ := href
  set u₀ : ℂ → ℝ := Impl.forceExt κ (weightWord ρL ρR) xL xR with hu₀def
  have hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ :=
    Impl.isBoundedHarmonicExtension_forceExt κ (weightWord ρL ρR) xL xR
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hZ : IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => h ω - smoothDist upperHalfPlaneOpens u₀) P :=
    isZeroBoundaryGFF_sub_smoothDist hh hu₀c (hgff u₀ hu₀)
  have hharm : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H := isHarmonicDistOn_smoothDist_of hu₀
  refine isOptionalHullCoupling_of_isFamilySampled hE hκ hh hgff hfamS fun hX τ hτ hτζ => ?_
  have hl := isLocalSet_hull_of_isFamilyLocal hE hX hZ (hfamL u₀ hu₀) hτ hτζ
  have hl' := IsLocalSet.add_dist hl hharm
  have e : (fun ω => h ω - smoothDist upperHalfPlaneOpens u₀ + smoothDist upperHalfPlaneOpens u₀) = h :=
    funext fun ω => sub_add_cancel _ _
  rw [e] at hl'
  exact hl'

end Def

/-! ### Existence on a standard Borel space -/

/-- **A family reference on a standard Borel space exists** for every ordered word and `κ > 0` (Theorem 1.1's
construction, kept with its two families; the driving space is Theorem 2.2's standard Borel one and the coupling space
is its product with the distribution space). -/
theorem exists_isFamilyRef (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR) :
    ∃ (Ω₀ : Type u) (mΩ₀ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (P₀ : Measure Ω₀)
      (_ : IsProbabilityMeasure P₀) (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W : ℝ≥0 → Ω₀ → ℝ) (VL : Fin nL → ℝ≥0 → Ω₀ → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω₀ → ℝ) (B : ℝ≥0 → Ω₀ → ℝ) (ζ : Ω₀ → ℝ≥0∞) (h : Ω₀ → DistOn upperHalfPlaneOpens),
      IsFamilyRef κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ h := by
  obtain ⟨Ω₀, mΩ₀, hSB, P₀, hP₀, 𝓕₀, W, VL, VR, B, ζ, hE⟩ :=
    LocalExt.thm22StdBorelStatement_of_ordered.{u} (ρL := ρL) (ρR := ρR) hκ hF
  have hc := measurable_coordVal hE
  have hE₁ := isIntegratedSLEEvolution_coordFiltration hE
  have hgen := IsAeGen.usualAugmentation (IsAeGen.usualAugmentation (P₀ := P₀)
    (isAeGen_coordFiltration (P₀ := P₀) hc))
  obtain ⟨α, μ, -, hμp, hμ1, hμ2, hαG, hfamS, hfamL⟩ :=
    exists_locCoupling_of_evolution hκ hE₁ (measurable_coordMap hc) hgen (finiteFamilyProjStatement hκ xL xR ρL ρR)
  have hEμ := IsIntegratedSLEEvolution.fst (X := DistOn upperHalfPlaneOpens) hμ1 hE₁
  exact ⟨Ω₀ × DistOn upperHalfPlaneOpens, inferInstance, inferInstance, μ, hμp, _, _, _, _, _, _, fun p => p.2,
    hEμ, measurable_snd, fun u₀ hu₀ => isZBGFFProcess_comp_snd hμ2 (hαG u₀ hu₀), hfamS, hfamL⟩

/-! ### Pullback along a measure-preserving map -/

section Comap

variable {Ω₀ Ω' : Type*} {mΩ₀ : MeasurableSpace Ω₀} [mΩ' : MeasurableSpace Ω'] {π : Ω' → Ω₀}
  {P₀ : Measure Ω₀} {μ : Measure Ω'} {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W : ℝ≥0 → Ω₀ → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}
  {h : Ω₀ → DistOn upperHalfPlaneOpens}

/-- Set integrals of a pulled-back function over pulled-back sets. -/
theorem setIntegral_comap_eq (hπ : Measurable π) (hμ : μ.map π = P₀) {g : Ω₀ → ℂ}
    (hg : AEStronglyMeasurable g P₀) {A₀ : Set Ω₀} (hA₀ : MeasurableSet A₀) :
    ∫ p in π ⁻¹' A₀, g (π p) ∂μ = ∫ ω in A₀, g ω ∂P₀ := by
  rw [← hμ] at hg ⊢
  exact (setIntegral_map hA₀ hg hπ.aemeasurable).symm

/-- **The pullback of a family reference**: along `π` with `μ.map π = P₀`, the pulled-back evolution, with any
measurable field `h'` that is almost surely `h ∘ π` and has the GFF law of the initial data, is a family reference. -/
theorem IsFamilyRef.comap (href : IsFamilyRef κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ h) (hκ : 0 < κ)
    (hπ : Measurable π) (hμ : μ.map π = P₀) {h' : Ω' → DistOn upperHalfPlaneOpens} (hh' : Measurable h')
    (hgff' : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ →
      IsZBGFFProcess upperHalfPlaneOpens (fun φ p => h' p φ - ∫ z, u₀ z * φ z) μ)
    (hae : ∀ᵐ p ∂μ, h' p = h (π p)) :
    IsFamilyRef κ xL xR ρL ρR μ (filtrationComap 𝓕₀ hπ) (fun t p => W t (π p)) (fun i t p => VL i t (π p))
      (fun i t p => VR i t (π p)) (fun t p => B t (π p)) (fun p => ζ (π p)) h' := by
  obtain ⟨hE, hh, -, hfamS, hfamL⟩ := href
  have hpull : ∀ {Q : Ω₀ → Prop}, (∀ᵐ ω ∂P₀, Q ω) → ∀ᵐ p ∂μ, Q (π p) := fun {Q} hQ => by
    rw [← hμ] at hQ
    exact ae_of_ae_map hπ.aemeasurable hQ
  refine ⟨IsIntegratedSLEEvolution.comap hπ hμ hE, hh', hgff', ?_, fun u₀ hu₀ => ?_⟩
  · -- the sampled family
    obtain ⟨u, hu, ι, hι, U, s, hs, hsafe, hsamp, hexh⟩ := hfamS
    refine ⟨fun p => u (π p), fun p t => hu (π p) t, ι, hι, U, fun i p => s i (π p),
      fun i => LocalExt.isStoppingTime_comap hπ hμ (hs i), fun i => hpull (hsafe i), fun i => ?_, hpull hexh⟩
    refine LocalExt.isSampledAt_comap hπ hμ (hs i) fun ψ hψ A₀ hA₀ => ?_
    have hA₀m : MeasurableSet A₀ := (hs i).measurableSpace_le A₀ hA₀
    have hgm : Measurable fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ)) :=
      Complex.continuous_exp.measurable.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp ((measurable_distOn_apply ψ).comp hh)))
    have hcf : AEStronglyMeasurable (cfAt κ W u ψ 1 (s i)) P₀ :=
      aestronglyMeasurable_cfAt_of_stoppingTime hE hκ u hu ψ (hs i)
        (by filter_upwards [hsafe i] with ω hω using ⟨hω.1, hω.2.mono_left hψ⟩) 1
    have e1 : ∫ p in π ⁻¹' A₀, Complex.exp (Complex.I * (h' p ψ : ℂ)) ∂μ =
        ∫ p in π ⁻¹' A₀, Complex.exp (Complex.I * (h (π p) ψ : ℂ)) ∂μ := by
      refine setIntegral_congr_ae (hπ hA₀m) ?_
      filter_upwards [hae] with p hp _
      rw [hp]
    rw [e1, setIntegral_comap_eq hπ hμ hgm.aestronglyMeasurable hA₀m, hsamp i ψ hψ A₀ hA₀,
      setIntegral_comap_eq hπ hμ hcf hA₀m]
  · -- the local family
    obtain ⟨ι, hι, U, s, hs, hUH, hind, hexh⟩ := hfamL u₀ hu₀
    refine ⟨ι, hι, U, fun i p => s i (π p), fun i => LocalExt.isStoppingTime_comap hπ hμ (hs i), hUH,
      fun i f Ξ D hD => ?_, hpull hexh⟩
    obtain ⟨D₀, hD₀, hDD₀⟩ := LocalExt.exists_comap_ae_eq_of_measurableSet_stopped hπ hμ (hs i) hD
    have hD₀m : MeasurableSet D₀ := (hs i).measurableSpace_le D₀ hD₀
    have hgm : ∀ Ψ : TestOn upperHalfPlaneOpens,
        Measurable fun ω => Complex.exp (Complex.I * ((h ω - smoothDist upperHalfPlaneOpens u₀) Ψ : ℂ)) :=
      fun Ψ => Complex.continuous_exp.measurable.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp ((measurable_distOn_apply Ψ).comp
          ((measurable_sub_distOnConst _).comp hh))))
    have key : ∀ Ψ : TestOn upperHalfPlaneOpens,
        ∫ p in D, Complex.exp (Complex.I * ((h' p - smoothDist upperHalfPlaneOpens u₀) Ψ : ℂ)) ∂μ =
          ∫ ω in D₀, Complex.exp (Complex.I * ((h ω - smoothDist upperHalfPlaneOpens u₀) Ψ : ℂ)) ∂P₀ := by
      intro Ψ
      rw [setIntegral_congr_set hDD₀, ← setIntegral_comap_eq hπ hμ (hgm Ψ).aestronglyMeasurable hD₀m]
      refine setIntegral_congr_ae (hπ hD₀m) ?_
      filter_upwards [hae] with p hp _
      rw [hp]
    rw [key, key]
    exact hind i f Ξ D₀ hD₀

end Comap

end WholeFieldStopped

end InteractingSLE
