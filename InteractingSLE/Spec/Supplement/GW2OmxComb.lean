/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxLoc2
import InteractingSLE.Spec.Supplement.GW2OmxMean
import InteractingSLE.WangWu.PrefixLocalMean

/-!
# GW2's open lines: the instance's launch mean in the kernel union's harmonic form

Packet PROVE-GW2-STAGEMEAN, R120 round. Under the conditional law `ν` of the earlier pieces, for the centred launch
field `h₀`:
* the instance's launch union `L` is marked local for `𝓜` with the Gaussian kernel of mean `m` (RELDET's route), so
  every local-set mean of `L` is `m` (`ae_localSetMean_eq_of_kernel`);
* the kernel union `U` (marked local for field-determined `𝓝`) has, on an event `Cond`, the harmonic form `F` of its
  local-set means (`GW2Stm.exists_unionMean_gw2_stop`);
* on a mark event `G` of `𝓝` (inside a mark event `I` of `𝓜` where `U ⊆ L`) the two sets agree
  (`ae_localSetMean_eq_of_cutoff`).

**`ae_eqOn_launchMean_of_kernel`**: almost surely on `G ∩ Cond`, every harmonic representative `w` of `m` off `L`
satisfies the kernel union mean's property `R` off `L` (in the application: the harmonic form `w + u = F` with the
relative chain data chosen inside `R`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open WholeField LocalSets

/-- **The instance's launch mean in the kernel union's harmonic form.** -/
theorem ae_eqOn_launchMean_of_kernel {Ω : Type u} {𝓜 𝓝 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h₀ ν) (h𝓜 : 𝓜 ≤ mΩ) (h𝓝 : 𝓝 ≤ mΩ)
    {L U : Ω → Set ℂ} (hLm : Measurable[𝓜, hittingSigma] L) (hLc : ∀ ω, L ω ⊆ H ∧ IsOpen (H \ L ω))
    (hLl : IsHistoryAvoidanceLocal 𝓜 L h₀ ν) {m : Ω → DistOn upperHalfPlaneOpens}
    (hmh : ∀ᵐ ω ∂ν, IsHarmonicDistOn (m ω) (H \ L ω))
    (hk : ∀ ψ : TestOn upperHalfPlaneOpens, ν[fun ω => Complex.exp (Complex.I * (h₀ ω ψ : ℂ)) | 𝓜] =ᵐ[ν]
      fun ω => rangeKerCF (m ω) (H \ L ω) ψ)
    (hUm : Measurable[𝓝, hittingSigma] U) (hUc : ∀ᵐ ω ∂ν, U ω ⊆ H ∧ IsOpen (H \ U ω))
    (hUl : IsHistoryAvoidanceLocal 𝓝 U h₀ ν)
    (hdet : 𝓝 ≤ aeSigma (MeasurableSpace.comap h₀ inferInstance) ν)
    {I : Set Ω} (hI : MeasurableSet[𝓜 ⊔ Ito.nullSets ν] I) (hsub : ∀ᵐ ω ∂ν, ω ∈ I → U ω ⊆ L ω)
    {G : Set Ω} (hG : MeasurableSet[𝓝] G) (heq : ∀ᵐ ω ∂ν, ω ∈ G → ω ∈ I ∧ U ω = L ω)
    {Cond : Ω → Prop} {R : Ω → (ℂ → ℝ) → Set ℂ → Prop}
    (hF : ∀ gU : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean U h₀ ν gU →
      ∀ᵐ ω ∂ν, Cond ω → ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ U ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ U ω → gU ω φ = ∫ z, wU z * φ z) →
        R ω wU (H \ U ω)) :
    ∀ᵐ ω ∂ν, ω ∈ G → Cond ω → ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ L ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L ω → m ω φ = ∫ z, w z * φ z) →
      R ω w (H \ L ω) := by
  classical
  have hLm' : Measurable[mΩ, hittingSigma] L := hLm.mono h𝓜 le_rfl
  have hUm' : Measurable[mΩ, hittingSigma] U := hUm.mono h𝓝 le_rfl
  -- local-set means of the two sets
  have hLloc : IsLocalSet L h₀ ν :=
    ((isLocalSet_tfae hh hLm' (Eventually.of_forall hLc)).out 4 1).2 hLl.isAvoidanceLocal
  have hUloc : IsLocalSet U h₀ ν := ((isLocalSet_tfae hh hUm' hUc).out 4 1).2 hUl.isAvoidanceLocal
  obtain ⟨gL, hgL⟩ := IsLocalSet.exists_isLocalSetMean hh hLm' hLloc
  obtain ⟨gU, hgU⟩ := IsLocalSet.exists_isLocalSetMean hh hUm' hUloc
  -- `gL` is `m` in every pairing off `L`
  set mf : Ω → ℂ → ℝ := fun ω => if h : IsHarmonicDistOn (m ω) (H \ L ω) then h.choose else 0 with hmf
  have hmf_spec : ∀ᵐ ω ∂ν, InnerProductSpace.HarmonicOnNhd (mf ω) (H \ L ω) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L ω → m ω φ = ∫ z, mf ω z * φ z := by
    filter_upwards [hmh] with ω hω
    simp only [hmf, hω, ↓reduceDIte]
    exact hω.choose_spec
  have hLc' : ∀ᵐ ω ∂ν, L ω ⊆ H ∧ IsOpen (H \ L ω) := Eventually.of_forall hLc
  have hφ : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂ν, tsupport φ ⊆ H \ L ω →
      gL ω φ = ∫ z, mf ω z * φ z := by
    intro φ
    filter_upwards [ae_localSetMean_eq_of_kernel h𝓜 hh hLm' hLc' hLl hk hgL φ, hmf_spec] with ω h1 h2 hsupp
    rw [h1, h2.2 φ hsupp]
  have hall := WangWu.ae_forall_apply_eq_of_forall_ae hgL.2.1 (Eventually.of_forall fun ω => (hLc ω).2)
    (hmf_spec.mono fun _ h => h.1) hφ
  -- localization
  have hloc := ae_localSetMean_eq_of_cutoff hh h𝓜 h𝓝 hLm hLc hLl hUm hUc hUl hdet hI hsub hG heq hgL hgU
  filter_upwards [hall, hloc, heq, hF gU hgU, hmf_spec] with ω hallω hlocω heqω hFω hmfω hωG hc w hw hwm
  obtain ⟨-, hUL⟩ := heqω hωG
  have hgLU : gL ω = gU ω := hlocω hωG
  rw [← hUL] at hw hwm ⊢
  refine hFω hc w hw fun φ hφs => ?_
  rw [← hgLU, hallω φ (hUL ▸ hφs), ← hmfω.2 φ (hUL ▸ hφs), hwm φ hφs]

end InteractingSLE.Theorem14.GW2Omx
