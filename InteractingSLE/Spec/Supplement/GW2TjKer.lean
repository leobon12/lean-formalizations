/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TjMarks
import InteractingSLE.Spec.Supplement.GW4CLocKernel

/-!
# (T1), probabilistic half: the union's Gaussian kernel under the conditional law of the earlier pieces

Packet PROVE-GW2-RELDET, ruling R117(b), item (T1) (`GW2Olm.KernelUnionLocal`). The route is PROVE-GW4-CLOC's
(`GW4Fix.CLoc.exists_ae_condExpKernel_kernel`), at one stage time `t`:

1. The union `B t = schedUnionS c r l a t` is a history-marked local set for the stage filtration (RELDET's
   `exists_schedLinesLocal_setsT`). By Lemma 3.6 (`isLocalSet_tfae`) it is a local set; let `g` be its local-set mean
   (`IsLocalSet.exists_isLocalSetMean`). Given its germ and the marks, the field has the Gaussian kernel of the mean
   `M = g + u₀` and the covariance of `ℍ ∖ B t` (`GW4Fix.ae_condExp_cexp_boundary_marked`).
2. The conditioning is coarsened to the countably generated `𝓜 = σ(B t) ∨ σ(g) ∨ kerMarks t`, which contains the
   σ-algebra `pastG` of the earlier pieces.
3. The tower property for a countably generated σ-algebra (`GW4Fix.CLoc.ae_ae_condExp_eq_of_le`) transfers the kernel,
   for `P`-almost every `ω₀`, to `ν = condExpKernel P pastG ω₀`: first at the countably many rational combinations of
   the generating tests, then at every test (`GW4Fix.CLoc.ae_condExp_cexp_eq_rangeKerCF_of_ratComb`).

**`exists_kernel_union_of`** (any such union), **`exists_kernel_union`** (the instance's union): the kernel data
and the transfer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open LocalSets WholeField GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Sdi GW4Fix GW4Fix.CLoc

/-- The coarsened marks: the set, the mean and the raw kernel marks. -/
@[instance_reducible]
def unionMarks {Ω : Type*} (B : Ω → Set ℂ) (g : Ω → DistOn upperHalfPlaneOpens) (K : MeasurableSpace Ω) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap B hittingSigma ⊔ MeasurableSpace.comap g inferInstance ⊔ K

theorem unionMarks_def {Ω : Type*} (B : Ω → Set ℂ) (g : Ω → DistOn upperHalfPlaneOpens) (K : MeasurableSpace Ω) :
    unionMarks B g K = MeasurableSpace.comap B hittingSigma ⊔ MeasurableSpace.comap g inferInstance ⊔ K := rfl

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
  (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **The Gaussian kernel of a union, under the conditional law of the earlier pieces** (at one stage time `t`): any
relatively closed set `B`, hitting-measurable, history-marked local for the stage filtration. -/
theorem exists_kernel_union_of {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P) (t : ℝ≥0)
    {B : Ω → Set ℂ} (hBm : Measurable[mΩ, hittingSigma] B) (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hloc : IsHistoryAvoidanceLocal (stgF c r l a t) B (centredField c.h u₀) c.P) :
    ∃ (M : Ω → DistOn upperHalfPlaneOpens) (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}), kerMarks c r l a t ≤ 𝓜.1 ∧
      Measurable[𝓜.1, hittingSigma] B ∧ Measurable[𝓜.1] M ∧
      (∀ᵐ ω ∂c.P, IsHarmonicDistOn (M ω) (H \ B ω)) ∧
      ∀ᵐ ω₀ ∂c.P, ∀ φ : TestOn upperHalfPlaneOpens,
        (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)[fun ω => Complex.exp (Complex.I * (c.h ω φ : ℂ)) | 𝓜.1]
          =ᵐ[condExpKernel c.P (GW2Olm.pastG c r l a) ω₀]
          fun ω => rangeKerCF (M ω) (H \ B ω) φ := by
  have hhm : Measurable c.h := c.hh.1
  have hh0m : Measurable (centredField c.h u₀) := measurable_centredField hhm u₀
  have hℋ : stgF c r l a t ≤ mΩ := (stgFilt _ _ _).le t
  have hl : IsLocalSet B (centredField c.h u₀) c.P :=
    ((isLocalSet_tfae hh0 hBm (Eventually.of_forall hBc)).out 4 1).2 hloc.isAvoidanceLocal
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh0 hBm hl
  have hker := ae_condExp_cexp_boundary_marked hu₀ hh0 hBm hBc hℋ hloc hg
  set M : Ω → DistOn upperHalfPlaneOpens := fun ω => g ω + smoothDist upperHalfPlaneOpens u₀ with hM_def
  -- the coarsened marks
  have hg𝓜 : Measurable[unionMarks B g (kerMarks c r l a t)] g :=
    Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  have hB𝓜 : Measurable[unionMarks B g (kerMarks c r l a t), hittingSigma] B :=
    Measurable.of_comap_le (le_sup_left.trans le_sup_left)
  have hadd : Measurable fun T : DistOn upperHalfPlaneOpens => T + smoothDist upperHalfPlaneOpens u₀ :=
    LQGMetric.measurable_distOn_iff.2 fun φ => ((LQGMetric.measurable_distOn_apply φ).add measurable_const)
  have hM𝓜 : Measurable[unionMarks B g (kerMarks c r l a t)] M := hadd.comp hg𝓜
  have hgerm : unionMarks B g (kerMarks c r l a t) ≤ germSigma B (centredField c.h u₀) ⊔ stgF c r l a t :=
    sup_le (sup_le (le_sup_left.trans' (comap_le_germSigma _ _)) (le_sup_left.trans' hg.1.comap_le))
      ((kerMarks_le_stgFilt c r l a t).trans le_sup_right)
  have hgle : germSigma B (centredField c.h u₀) ⊔ stgF c r l a t ≤ mΩ := sup_le (germSigma_le hBm hh0m) hℋ
  have hle : unionMarks B g (kerMarks c r l a t) ≤ mΩ := hgerm.trans hgle
  have hcg : @MeasurableSpace.CountablyGenerated Ω (unionMarks B g (kerMarks c r l a t)) := by
    rw [unionMarks_def]
    exact MeasurableSpace.CountablyGenerated.sup (MeasurableSpace.CountablyGenerated.sup
        (@MeasurableSpace.CountablyGenerated.comap _ _ hittingSigma countablyGenerated_hittingSigma _)
        (MeasurableSpace.CountablyGenerated.comap _)) (countablyGenerated_kerMarks c r l a t)
  have hJ : GW2Olm.pastG c r l a ≤ unionMarks B g (kerMarks c r l a t) :=
    (pastG_le_kerMarks c r l a t).trans le_sup_right
  -- the kernel given the coarsened marks under `P`
  have hkerP : ∀ φ : TestOn upperHalfPlaneOpens,
      c.P[fun ω' => Complex.exp (Complex.I * (c.h ω' φ : ℂ)) | unionMarks B g (kerMarks c r l a t)] =ᵐ[c.P]
        fun ω => rangeKerCF (M ω) (H \ B ω) φ := by
    intro φ
    have hR : StronglyMeasurable[unionMarks B g (kerMarks c r l a t)] fun ω => rangeKerCF (M ω) (H \ B ω) φ :=
      (measurable_rangeKerCF hM𝓜 hB𝓜 hBc φ).stronglyMeasurable
    have hRi : Integrable (fun ω => rangeKerCF (M ω) (H \ B ω) φ) c.P := by
      refine Integrable.of_bound ((hR.mono hle).aestronglyMeasurable) 1 (Eventually.of_forall fun ω => ?_)
      have hcov : 0 ≤ zeroGFFTestCov (H \ B ω) φ φ := zeroGFFTestCov_self_nonneg (hBc ω).2 sdiff_subset φ
      rw [rangeKerCF, Complex.norm_exp]
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_zero, zero_sub]
      rw [Real.exp_le_one_iff]
      nlinarith
    calc c.P[fun ω' => Complex.exp (Complex.I * (c.h ω' φ : ℂ)) | unionMarks B g (kerMarks c r l a t)]
        =ᵐ[c.P] c.P[c.P[fun ω' => Complex.exp (Complex.I * (c.h ω' φ : ℂ)) |
          germSigma B (centredField c.h u₀) ⊔ stgF c r l a t] | unionMarks B g (kerMarks c r l a t)] :=
          (condExp_condExp_of_le hgerm hgle).symm
      _ =ᵐ[c.P] c.P[fun ω => rangeKerCF (M ω) (H \ B ω) φ | unionMarks B g (kerMarks c r l a t)] :=
          condExp_congr_ae (hker φ)
      _ = fun ω => rangeKerCF (M ω) (H \ B ω) φ := condExp_of_stronglyMeasurable hle hR hRi
  -- the transfer, at rational combinations, then at every test
  have hν : ∀ᵐ ω₀ ∂c.P, ∀ k : Restart.RatComb,
      (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)[fun ω => Complex.exp
        (Complex.I * (c.h ω (Restart.ratComb upperHalfPlaneOpens k) : ℂ)) | unionMarks B g (kerMarks c r l a t)]
        =ᵐ[condExpKernel c.P (GW2Olm.pastG c r l a) ω₀]
          fun ω => rangeKerCF (M ω) (H \ B ω) (Restart.ratComb upperHalfPlaneOpens k) := by
    refine ae_all_iff.2 fun k => ?_
    exact ae_ae_condExp_eq_of_le hJ hle hcg
      (GFF.measurable_exp_I_mul ((LQGMetric.measurable_distOn_apply _).comp hhm)) (C := 1)
      (fun ω => (Complex.norm_exp_I_mul_ofReal _).le) (hkerP _)
  refine ⟨M, ⟨_, hle⟩, le_sup_right, hB𝓜, hM𝓜, ?_, ?_⟩
  · filter_upwards [hg.2.1] with ω hω
    exact Coupling.IsHarmonicDistOn.add' (hBc ω).2 hω
      (IsHarmonicDistOn.mono (isHarmonicDistOn_smoothDist hu₀) sdiff_subset)
  · filter_upwards [hν] with ω₀ hω₀ φ
    exact ae_condExp_cexp_eq_rangeKerCF_of_ratComb (Q := condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)
      hle hhm (Eventually.of_forall fun ω => ⟨(hBc ω).2, sdiff_subset⟩) hω₀ φ

/-- **The union's Gaussian kernel under the conditional law of the earlier pieces** (at one stage time `t`). -/
theorem exists_kernel_union {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P) (t : ℝ≥0)
    (hloc : IsHistoryAvoidanceLocal (stgF c r l a t) (schedUnionS c r l a t) (centredField c.h u₀) c.P) :
    ∃ (M : Ω → DistOn upperHalfPlaneOpens) (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}), kerMarks c r l a t ≤ 𝓜.1 ∧
      Measurable[𝓜.1, hittingSigma] (schedUnionS c r l a t) ∧ Measurable[𝓜.1] M ∧
      (∀ᵐ ω ∂c.P, IsHarmonicDistOn (M ω) (H \ schedUnionS c r l a t ω)) ∧
      ∀ᵐ ω₀ ∂c.P, ∀ φ : TestOn upperHalfPlaneOpens,
        (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)[fun ω => Complex.exp (Complex.I * (c.h ω φ : ℂ)) | 𝓜.1]
          =ᵐ[condExpKernel c.P (GW2Olm.pastG c r l a) ω₀]
          fun ω => rangeKerCF (M ω) (H \ schedUnionS c r l a t ω) φ :=
  exists_kernel_union_of c r l a hu₀ hh0 t (measurable_schedUnionS c r l a t) (schedUnionS_subset_isOpen c r l a t)
    hloc

end InteractingSLE.Theorem14.GW2Rd
