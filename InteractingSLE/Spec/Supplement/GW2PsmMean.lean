/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SpmPhys
import InteractingSLE.Spec.Supplement.GW2RzSched

/-!
# GW2's open lines: the root-`x` stage identity from the pairing and the stage-chart reading

Packet PROVE-GW2-STAGEMEAN, R121 round. The second half of `GW2Spm.StageInst.mean_of_physLaw`, for ROOTX's root-`x`
instance objects (`chartX`, `drvX`, `clockX`, `capX`, `srecX`) and with the pairing of the mean as input: if, almost
surely on an event `G` containing the live event before the cap, the mean `g` pairs with test functions off `B t` as a
harmonic `M`, and `M + u₀ + σa + kc · lift`, read in the stage chart, is the canonical coupling mean, then `g`
satisfies `GW2Rz.stageMeanAtX`:

* **`StageInst.meanX_of_pair`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.Q3Stop GW2Sde GW2Rz GW2Spm GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.SchedRule GW2Rd Supp8.GB6.RelDrv

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- **The root-`x` stage identity from the pairing of the mean and the stage-chart reading.** -/
theorem StageInst.meanX_of_pair (I : StageInst Ω) (x₀ : ℝ) (w : WordType) (t : ℝ≥0)
    (hlc : ∀ ω, ContinuousOn (I.chartX c x₀ ω).2.2 (I.chartX c x₀ ω).dom)
    (hharm : InnerProductSpace.HarmonicOnNhd I.u₀ H) (hBc : ∀ ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω)) {G : Set Ω}
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srecX c r l x₀) → I.clockX c x₀ t ω < I.capX c x₀ ω →
      ω ∈ G)
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srecX c r l x₀) → I.clockX c x₀ t ω < I.capX c x₀ ω →
      H \ I.B t ω = (I.chartX c x₀ ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => I.drvX c x₀ s.toNNReal ω) ((I.clockX c x₀ t ω).toNNReal : ℝ)))
    {M : Ω → ℂ → ℝ} (hMh : ∀ ω, InnerProductSpace.HarmonicOnNhd (M ω) (H \ I.B t ω))
    (g : Ω → DistOn upperHalfPlaneOpens) (hgh : ∀ᵐ ω ∂c.P, IsHarmonicDistOn (g ω) (H \ I.B t ω))
    (hpair : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      g ω φ = ∫ z, M ω z * φ z)
    (hread : ∀ᵐ ω ∂c.P, ω ∈ G → ∀ z ∈ H \ fwdHull (fun s : ℝ => I.drvX c x₀ s.toNNReal ω)
        ((I.clockX c x₀ t ω).toNNReal : ℝ),
      M ω ((I.chartX c x₀ ω).2.1 z) + I.u₀ ((I.chartX c x₀ ω).2.1 z) + I.σa +
          I.kc * (I.chartX c x₀ ω).2.2 ((I.chartX c x₀ ω).2.1 z) =
        couplingMean c.κ (fun s : ℝ => I.drvX c x₀ s.toNNReal ω) (I.clockX c x₀ t ω).toNNReal
          (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c x₀)
            (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
              (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
              (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω)) ω
            (I.clockX c x₀ t ω).toNNReal) z)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, stageMeanAtX I c r l x₀ w t ψ ω (g ω) := by
  classical
  have hu₀c : ContinuousOn I.u₀ H := fun z hz => (hharm z hz).1.continuousAt.continuousWithinAt
  -- the cut-off union and mean
  set A' : Ω → Set ℂ := fun ω => if ω ∈ G then I.B t ω else H with hA'
  set m : Ω → ℂ → ℝ := fun ω => if ω ∈ G then M ω else 0 with hm
  have hφ' : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, tsupport φ ⊆ H \ A' ω →
      g ω φ = ∫ z, m ω z * φ z := by
    intro φ
    filter_upwards [hpair φ] with ω h1 hsupp
    by_cases hω : ω ∈ G
    · simp only [hA', hω, ↓reduceIte] at hsupp
      simp only [hm, hω, ↓reduceIte]
      exact h1 hω hsupp
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self] at hsupp
      have h0 : ∀ z, φ z = 0 := fun z => image_eq_zero_of_notMem_tsupport fun hz => notMem_empty z (hsupp hz)
      have hφ0 : φ = 0 := by
        ext z
        exact h0 z
      rw [hφ0, map_zero]
      have e : (fun z => m ω z * (0 : TestOn upperHalfPlaneOpens) z) = fun _ => 0 := by
        funext z
        rw [← hφ0, h0 z, mul_zero]
      rw [e, integral_zero]
  have hharm' : ∀ᵐ ω ∂c.P, IsHarmonicDistOn (g ω) (H \ A' ω) := by
    filter_upwards [hgh] with ω h
    by_cases hω : ω ∈ G
    · simpa only [hA', hω, ↓reduceIte] using h
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self]
      exact GW2Scl.isHarmonicDistOn_empty _
  have hopen' : ∀ᵐ ω ∂c.P, IsOpen (H \ A' ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ G
    · simpa only [hA', hω, ↓reduceIte] using (hBc ω).2
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self, isOpen_empty]
  have hm' : ∀ᵐ ω ∂c.P, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A' ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hA', hm, hω, ↓reduceIte]
      exact hMh ω
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self]
      exact fun z hz => absurd hz (notMem_empty z)
  have hall := WangWu.ae_forall_apply_eq_of_forall_ae hharm' hopen' hm' hφ'
  filter_upwards [hall, hlive, hshape, hread] with ω hallω hlv hsh hrd hlive' hlt hψ hc
  have hωG : ω ∈ G := hlv hlive' hlt
  set S : ℝ → ℝ := fun s => I.drvX c x₀ s.toNNReal ω with hSdef
  set q : ℝ := ((I.clockX c x₀ t ω).toNNReal : ℝ) with hqdef
  set cs : Chart := I.chartX c x₀ ω with hcs
  have hψO : tsupport ψ ⊆ H \ fwdHull S q := fun y hy =>
    ⟨Coupling.tsupport_subset_H ψ hy, Set.disjoint_left.1 hψ hy⟩
  have hO : cs.2.1 '' (H \ fwdHull S q) = H \ I.B t ω := (hsh hlive' hlt).symm
  have hmcO : ContinuousOn (fun z => M ω z + I.u₀ z) (cs.2.1 '' (H \ fwdHull S q)) := by
    rw [hO]
    exact (Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd (hMh ω)).add (hu₀c.mono sdiff_subset)
  have hT : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ cs.2.1 '' (H \ fwdHull S q) →
      (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens I.u₀) φ =
        ∫ z, (M ω z + I.u₀ z) * φ z := by
    intro φ hφ
    rw [hO] at hφ
    have hsupp : tsupport φ ⊆ H \ A' ω := by
      simp only [hA', hωG, ↓reduceIte]
      exact hφ
    have hmω : m ω = M ω := by simp only [hm, hωG, ↓reduceIte]
    have hi1 := WholeField.integrable_mul_testOn (Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd (hMh ω)) φ hφ
    have hi2 := WholeField.integrable_mul_testOn hu₀c φ φ.tsupport_subset
    rw [add_apply, hallω φ hsupp, Coupling.smoothDist_apply_eq hu₀c φ, hmω, ← integral_add hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [add_mul]
  rw [Sec5.Aux61SlitV.chartTransport_apply_eq_integral_of_subset hc (hlc ω) sdiff_subset hmcO hT I.σa I.kc
    hψO]
  refine congrArg _ (funext fun y => ?_)
  by_cases hy : y ∈ tsupport ψ
  · rw [← hrd hωG y (hψO hy)]
  · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero]

end InteractingSLE.Theorem14.GW2Psm
