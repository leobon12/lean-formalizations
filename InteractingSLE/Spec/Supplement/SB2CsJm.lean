/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CsPock
import InteractingSLE.Spec.Supplement.SB2CrVer
import InteractingSLE.Spec.Supplement.SB2QxVer
import InteractingSLE.Spec.Sec7.PocketCouplingMean
import InteractingSLE.Spec.Sec4.Special3Thin

/-!
# The line mean of the joint union from the line mean of B's own union (D51 item 1)

Packet PROVE-SB2-CONDFIN (round 10, D51). K2 at the root (`Cr.ae_k2_root`) needs the line mean of the version's union
`A₁ t ∪ A₂ t` with the JOINT `A₂ t = fillVer (A ∪ B_{≤ℓ,t})`. LCMEAN's engine computes the line mean of B's own
union `A₁ t ∪ fillVer (B_{≤ℓ,t})`. **`hmean_joint_of_hmeanB`**: at one version, word type and B-time, the second
from the first. On the root cell before the stop, the version's hull clause makes the joint union the step hull
`fill K ∪ Φ⁻¹(K_{a t})` (`Qx.hullChart_inv_image_diff`), which is bounded (`Qw.isHPHull_stepHull`). So the three
filled versions are `fillH ∘ closure` of the raw sets, B's own union lies in the joint union and the pockets are open
(`Cs.isOpen_pockets`). The two local-set means then agree off the pockets (`Cs.ae_localSetMean_eqOn_of_pockets`), in
particular on the chart transport of every test function avoiding the relative hull.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

universe u

namespace InteractingSLE.Theorem14.SB.Cs

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist.StagedLaw LocalSets WholeField Supp8.Q3Stop Lv Ms
  Mf

variable {κ ψ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {Fr : Set Ω} {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
  {β₁ : Ω → BoundaryWord} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L : Ω → ℝ≥0∞}
  {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {u₀ : ℂ → ℝ}

/-- **The line mean of the joint union from that of B's own union**, at one version, word type and B-time. -/
theorem hmean_joint_of_hmeanB (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (V : Cr.RootVersionG κ ψ P Fr 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL L)
    {w : WordType} (hw : w ∈ types) (t : ℝ≥0) {A₂B : Ω → Set ℂ} {X Y : Ω → Set ℂ}
    (hXH : ∀ ω, X ω ⊆ H) (hYH : ∀ ω, Y ω ⊆ H)
    (hA₁ : ∀ᵐ ω ∂P, A₁ t ω = fillVer X ω) (hA₂B : ∀ᵐ ω ∂P, A₂B ω = fillVer Y ω)
    (hA₂ : ∀ᵐ ω ∂P, A₂ t ω = fillVer (fun ω => X ω ∪ Y ω) ω)
    (hBm : Measurable[𝓖 t, hittingSigma] (fun ω => A₁ t ω ∪ A₂B ω))
    (hJm : Measurable[𝓖 t, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω))
    (hBc : ∀ ω, A₁ t ω ∪ A₂B ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂B ω)))
    (hJc : ∀ ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω)))
    (hBloc : IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂B ω) (WholeField.centredField h u₀) P)
    (hJloc : IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P)
    {gB gJ : Ω → DistOn upperHalfPlaneOpens}
    (hgB : IsLocalSetMean (fun ω => A₁ t ω ∪ A₂B ω) (WholeField.centredField h u₀) P gB)
    (hgJ : IsLocalSetMean (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P gJ)
    (d : Ω → DistOn upperHalfPlaneOpens) (σ k : ℝ) (M : Ω → ℝ) (φ : TestOn upperHalfPlaneOpens)
    (hmeanB : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w → 0 < V.a t ω → V.a t ω < V.Λ w ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal) →
      Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 σ k (gB ω + d ω) φ = M ω) :
    ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w → 0 < V.a t ω → V.a t ω < V.Λ w ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal) →
      Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 σ k (gJ ω + d ω) φ = M ω := by
  classical
  set F : Ω → Set ℂ := fun ω => fwdHull (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal with hFdef
  have hFH : ∀ ω, F ω ⊆ H := fun ω _ hz => hz.1
  -- the good samples: the root cell before the stop, with the filled versions
  set Good : Set Ω := {ω | ω ∈ seedCell κ ψ β₁ Fr w ∧ V.a t ω < V.Λ w ω ∧ A₁ t ω = fillVer X ω ∧
    A₂B ω = fillVer Y ω ∧ A₂ t ω = fillVer (fun ω => X ω ∪ Y ω) ω ∧
    H \ (A₁ t ω ∪ A₂ t ω) = (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.1 '' (H \ F ω)} with hGood
  have hgood : ∀ ω ∈ Good, (A₁ t ω ∪ A₂B ω) ⊆ (A₁ t ω ∪ A₂ t ω) ∧
      IsOpen ((H \ (A₁ t ω ∪ A₂B ω)) ∩ (A₁ t ω ∪ A₂ t ω)) := by
    rintro ω ⟨-, -, h1, h2, h3, hhull⟩
    have hK := Mo.isHPHull_fillH hKc hKp ω
    -- the joint union is the step hull, hence bounded
    rw [Qx.hullChart_inv_image_diff hK (x₀ ω) (hFH ω)] at hhull
    have hJeq : A₁ t ω ∪ A₂ t ω = fillH (K ω) ∪ (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.1 '' F ω := by
      have hstep := Qw.isHPHull_stepHull hK (x₀ ω) (W := fun s : ℝ => V.W s.toNNReal ω)
        ((V.W_cont ω).comp continuous_real_toNNReal) (by simp [V.W_zero ω]) (s := ((V.a t ω).toNNReal : ℝ))
        (NNReal.coe_nonneg _)
      exact Qx.eq_of_H_diff_eq (hJc ω).1 hstep.1 hhull
    have hJb : Bornology.IsBounded (A₁ t ω ∪ A₂ t ω) := by
      rw [hJeq]
      exact (Qw.isHPHull_stepHull hK (x₀ ω) (W := fun s : ℝ => V.W s.toNNReal ω)
        ((V.W_cont ω).comp continuous_real_toNNReal) (by simp [V.W_zero ω]) (s := ((V.a t ω).toNNReal : ℝ))
        (NNReal.coe_nonneg _)).2.1
    have hXYsub : X ω ∪ Y ω ⊆ A₁ t ω ∪ A₂ t ω := by
      rw [h3]
      exact (subset_fillVer (B := fun ω => X ω ∪ Y ω) (fun ω => union_subset (hXH ω) (hYH ω)) ω).trans
        subset_union_right
    have hXYb : Bornology.IsBounded (X ω ∪ Y ω) := hJb.subset hXYsub
    have hXb : Bornology.IsBounded (X ω) := hXYb.subset subset_union_left
    have hYb : Bornology.IsBounded (Y ω) := hXYb.subset subset_union_right
    rw [h1, h2, h3, fillVer_of_bounded (B := X) hXb, fillVer_of_bounded (B := Y) hYb,
      fillVer_of_bounded (B := fun ω => X ω ∪ Y ω) hXYb]
    refine ⟨unionFill_subset (X ω) (Y ω), isOpen_pockets (X ω) (Y ω) ?_⟩
    have := (hBc ω).2
    rwa [h1, h2, fillVer_of_bounded (B := X) hXb, fillVer_of_bounded (B := Y) hYb] at this
  have heq := ae_localSetMean_eqOn_of_pockets hh (𝓖.le t) hBm hJm hBc hJc hBloc hJloc hgB hgJ hgood
  filter_upwards [heq, hmeanB, hA₁, hA₂B, hA₂, V.hull w hw t] with ω hω hB h1 h2 h3 hhull hcell hpos hlt hdis
  have hωG : ω ∈ Good := ⟨hcell, hlt, h1, h2, h3, hhull hcell hlt⟩
  -- the transported test is supported off the joint union
  have hsupp : tsupport (Chart.pushTest (Mu.isConformal_canon x₀ hKc hKp ω) φ) ⊆ H \ (A₁ t ω ∪ A₂ t ω) := by
    refine (Sec7.PocketCoupling.tsupport_pushTest_subset_image (Mu.isConformal_canon x₀ hKc hKp ω) φ).trans ?_
    rw [hhull hcell hlt]
    exact image_mono fun z hz => ⟨φ.tsupport_subset hz, fun hzF => Set.disjoint_left.1 hdis hz hzF⟩
  have hpair := hω hωG _ hsupp
  rw [← hB hcell hpos hlt hdis]
  set c := Mu.isConformal_canon x₀ hKc hKp ω
  have e1 : Chart.chartTransport c 1 σ k (gJ ω + d ω) φ = 1 * (gJ ω (Chart.pushTest c φ) +
      d ω (Chart.pushTest c φ)) + σ * Chart.oneDist φ + k * Chart.liftDist _ φ := rfl
  have e2 : Chart.chartTransport c 1 σ k (gB ω + d ω) φ = 1 * (gB ω (Chart.pushTest c φ) +
      d ω (Chart.pushTest c φ)) + σ * Chart.oneDist φ + k * Chart.liftDist _ φ := rfl
  rw [e1, e2, hpair]

end InteractingSLE.Theorem14.SB.Cs
