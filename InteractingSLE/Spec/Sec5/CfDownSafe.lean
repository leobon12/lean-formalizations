/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfDownCoupling

/-!
# The member identities of the continuation hulls under the reflection `σ(z) = −z̄`

Packet PROVE-CFDOWN. `Restart.DomainMarkov.K2.HasSafeMembers` (the shift identities of the field along the Dirichlet
directions `−Δf/2π`, `f ∈ C_c^∞(⋃ balls)`, on events where the rational balls avoid the hull) is reflection
covariant: reflect the ball family (`(q₁, q₂, r) ↦ (−q₁, q₂, r)`), the direction (`f ↦ −f ∘ σ`) and the test function
(`Ξ ↦ −Ξ ∘ σ`). The Gaussian factor `projFactor` is invariant: it only involves the Dirichlet energy of `f` and the
pairing `∫ Ξ f` (`QuantumZipper.Thm11Asm.inner_covVec_gradFeat`), both preserved by the isometry `σ`.

* `reflBall`, `reflBalls`, **`ballsK_reflBalls`**, **`ballsU_reflBalls`**;
* `neg_comp_reflectC_mem_zeroSpace`, `dirichletEnergyOn_neg_comp_reflectC`;
* **`lapTest_reflect`**: `reflTest (lapTest (σV) (−f ∘ σ)) = −lapTest V f`;
* **`projFactor_reflect`**;
* **`hasSafeMembers_reflect`**: the member identities of `−X ∘ σ` along `W` give those of `X` along `−W`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real RealInnerProductSpace

namespace InteractingSLE.Sec5.CfDown

open LP (reflectC reflectC_reflectC)
open Sec7.FlowReflect (reflField reflTest)
open Coupling (ballsK ballsU ratCentre projFactor)
open Restart.DomainMarkov (ballsOpen)
open Restart.DomainMarkov.K2 (HasSafeMembers)
open LocalSets (lapTest)
open QuantumZipper (zeroSpace)
open QuantumZipper.K3 (gradFeat)
open QuantumZipper.Thm11Asm (covVec)
open LQGMetric.MarkovZB (zsSub)

/-! ### Rational balls -/

/-- The reflected rational ball `(−q₁, q₂, r)`. -/
def reflBall (b : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ := (-b.1, b.2.1, b.2.2)

/-- The reflected ball family. -/
def reflBalls (F : Finset (ℚ × ℚ × ℚ)) : Finset (ℚ × ℚ × ℚ) := F.image reflBall

theorem ratCentre_reflBall (b : ℚ × ℚ × ℚ) : ratCentre (reflBall b) = reflectC (ratCentre b) := by
  apply Complex.ext <;> simp [ratCentre, reflBall, LP.reflectC]

theorem image_reflectC_closedBall (z : ℂ) (ε : ℝ) : reflectC '' closedBall z ε = closedBall (reflectC z) ε := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_closedBall, LP.isometry_reflectC.dist_eq]
    exact hv
  · intro hw
    refine ⟨reflectC w, ?_, reflectC_reflectC w⟩
    rw [mem_closedBall, ← LP.isometry_reflectC.dist_eq, reflectC_reflectC]
    exact hw

theorem ballsK_reflBalls (F : Finset (ℚ × ℚ × ℚ)) : ballsK (reflBalls F) = reflectC '' ballsK F := by
  simp only [ballsK, reflBalls, Finset.set_biUnion_finset_image, image_iUnion₂, image_reflectC_closedBall,
    ratCentre_reflBall]
  rfl

theorem ballsU_reflBalls (F : Finset (ℚ × ℚ × ℚ)) : ballsU (reflBalls F) = reflectC '' ballsU F := by
  simp only [ballsU, reflBalls, Finset.set_biUnion_finset_image, image_iUnion₂, LP.image_reflectC_ball,
    ratCentre_reflBall]
  rfl

/-! ### Test directions -/

theorem neg_comp_reflectC_mem_zeroSpace {U : Set ℂ} {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) :
    (fun z => -f (reflectC z)) ∈ zeroSpace (reflectC '' U) := by
  refine ⟨(Sec7.FlowReflect.contDiff_comp_reflectC hf.1).neg,
    (Sec7.FlowReflect.hasCompactSupport_comp_reflectC hf.2.1).neg, ?_⟩
  have e : (fun z => -f (reflectC z)) = -(fun z => f (reflectC z)) := rfl
  rw [e, tsupport_neg, Sec7.FlowReflect.tsupport_comp_reflectC]
  exact image_mono hf.2.2

theorem dirichletEnergyOn_neg_comp_reflectC (U : Set ℂ) (g : ℂ → ℝ) :
    QuantumZipper.dirichletEnergyOn (reflectC '' U) (fun z => -g (reflectC z)) =
      QuantumZipper.dirichletEnergyOn U g := by
  have e : (fun z => -g (reflectC z)) = fun z => (-g) (reflectC z) := rfl
  rw [e, Sec7.FlowReflect.dirichletEnergyOn_comp_reflectC, Sec7.FlowReflect.reflectC_image_image]
  unfold QuantumZipper.dirichletEnergyOn
  simp only [fderiv_neg, norm_neg]

/-- **The Dirichlet direction of the reflected function** is minus the reflected direction. -/
theorem lapTest_reflect {V V' : TopologicalSpace.Opens ℂ} (hV : V ≤ upperHalfPlaneOpens)
    (hV' : V' ≤ upperHalfPlaneOpens) (f : zsSub (V : Set ℂ)) (f' : zsSub (V' : Set ℂ))
    (hf' : ∀ z, f'.1 z = -f.1 (reflectC z)) : reflTest (lapTest V' f') = -lapTest V f := by
  refine DFunLike.ext _ _ fun z => ?_
  rw [Sec7.FlowReflect.reflTest_apply, LocalSets.coe_lapTest hV', neg_apply, LocalSets.coe_lapTest hV,
    LQGMetric.cmTest_apply, LQGMetric.cmTest_apply]
  have e : (⇑(LQGMetric.MarkovZB.zsTest f'.2) : ℂ → ℝ) = -(fun z => f.1 (reflectC z)) :=
    funext fun z => hf' z
  have e' : (⇑(LQGMetric.MarkovZB.zsTest f.2) : ℂ → ℝ) = f.1 := rfl
  rw [e, e', InnerProductSpace.laplacian_neg, Sec7.FlowReflect.laplacian_comp_reflectC]
  simp only [Pi.neg_apply, reflectC_reflectC]
  ring

theorem norm_gradFeat_reflect {V V' : Set ℂ} (hVV : V' = reflectC '' V) {f f' : ℂ → ℝ} (hf : f ∈ zeroSpace V)
    (hf' : f' ∈ zeroSpace V') (hff : ∀ z, f' z = -f (reflectC z)) : ‖gradFeat V' f'‖ = ‖gradFeat V f‖ := by
  have h1 := QuantumZipper.K3.norm_gradFeat_sq ((QuantumZipper.K3.isDNSpace_zeroSpace V').smooth f' hf')
    ((QuantumZipper.K3.isDNSpace_zeroSpace V').energy f' hf')
  have h2 := QuantumZipper.K3.norm_gradFeat_sq ((QuantumZipper.K3.isDNSpace_zeroSpace V).smooth f hf)
    ((QuantumZipper.K3.isDNSpace_zeroSpace V).energy f hf)
  have hE : QuantumZipper.dirichletEnergyOn V' f' = QuantumZipper.dirichletEnergyOn V f := by
    rw [show f' = fun z => -f (reflectC z) from funext hff, hVV, dirichletEnergyOn_neg_comp_reflectC]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.trans (hE.trans h2.symm))

theorem inner_gradFeat_covVec_reflect {V V' : Set ℂ} (hVo : IsOpen V) (hVH : V ⊆ H) (hVV : V' = reflectC '' V)
    {f f' : ℂ → ℝ} (hf : f ∈ zeroSpace V) (hf' : f' ∈ zeroSpace V') (hff : ∀ z, f' z = -f (reflectC z))
    (Ξ : TestOn upperHalfPlaneOpens) :
    ⟪gradFeat V' f', covVec V' ⇑(-reflTest Ξ)⟫ = ⟪gradFeat V f, covVec V Ξ⟫ := by
  have hV'o : IsOpen V' := by
    rw [hVV, LP.reflectC_image_eq_preimage]
    exact hVo.preimage LP.continuous_reflectC
  have hV'H : V' ⊆ H := by
    rw [hVV]
    rintro _ ⟨z, hz, rfl⟩
    exact Sec7.FlowReflect.reflectC_mem_H (hVH hz)
  by_cases hpos : ∃ g ∈ zeroSpace V, 0 < QuantumZipper.dirichletEnergyOn V g
  · have hpos' : ∃ g ∈ zeroSpace V', 0 < QuantumZipper.dirichletEnergyOn V' g := by
      obtain ⟨g, hg, hgE⟩ := hpos
      refine ⟨fun z => -g (reflectC z), hVV ▸ neg_comp_reflectC_mem_zeroSpace hg, ?_⟩
      rw [hVV, dirichletEnergyOn_neg_comp_reflectC]
      exact hgE
    rw [← real_inner_comm (gradFeat V' f'), ← real_inner_comm (gradFeat V f)]
    change ⟪covVec V' (LocalSets.toTestFunH (-reflTest Ξ)).1, gradFeat V' f'⟫ =
      ⟪covVec V (LocalSets.toTestFunH Ξ).1, gradFeat V f⟫
    rw [QuantumZipper.Thm11Asm.inner_covVec_gradFeat hV'o hV'H _ hpos' hf',
      QuantumZipper.Thm11Asm.inner_covVec_gradFeat hVo hVH _ hpos hf]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport fun h' => hz (hf'.2.2 h'), mul_zero],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport fun h' => hz (hf.2.2 h'), mul_zero]]
    rw [← Sec7.FlowReflect.integral_comp_reflectC (fun z => (LocalSets.toTestFunH Ξ).1 z * f z)]
    congr 1
    funext z
    change -(reflTest Ξ z) * f' z = Ξ (reflectC z) * f (reflectC z)
    rw [hff, Sec7.FlowReflect.reflTest_apply]
    ring
  · have hpos' : ¬ ∃ g ∈ zeroSpace V', 0 < QuantumZipper.dirichletEnergyOn V' g := by
      rintro ⟨g, hg, hgE⟩
      refine hpos ⟨fun z => -g (reflectC z), ?_, ?_⟩
      · have h := neg_comp_reflectC_mem_zeroSpace hg
        rwa [hVV, Sec7.FlowReflect.reflectC_image_image] at h
      · have h := dirichletEnergyOn_neg_comp_reflectC V' g
        rw [hVV, Sec7.FlowReflect.reflectC_image_image] at h
        rw [← hVV] at h
        rw [h]
        exact hgE
    rw [LocalSets.gradFeat_eq_zero_of_nopos subset_rfl hpos' hf',
      LocalSets.gradFeat_eq_zero_of_nopos subset_rfl hpos hf, inner_zero_left, inner_zero_left]

/-- **The Gaussian factor is reflection invariant.** -/
theorem projFactor_reflect {V V' : TopologicalSpace.Opens ℂ} (hVH : (V : Set ℂ) ⊆ H)
    (hVV : (V' : Set ℂ) = reflectC '' V) (f : zsSub (V : Set ℂ)) (f' : zsSub (V' : Set ℂ))
    (hf' : ∀ z, f'.1 z = -f.1 (reflectC z)) (Ξ : TestOn upperHalfPlaneOpens) :
    projFactor V' f' (-reflTest Ξ) = projFactor V f Ξ := by
  unfold projFactor
  rw [norm_gradFeat_reflect hVV f.2 f'.2 hf', inner_gradFeat_covVec_reflect V.isOpen hVH hVV f.2 f'.2 hf' Ξ]

/-- **The member identities under the reflection**: if the reflected field `−X ∘ σ` has the member identities along
`W`, then `X` has them along `−W`. -/
theorem hasSafeMembers_reflect {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓗 : MeasureTheory.Filtration ℝ≥0 mΩ} {F : Set Ω} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {X : Ω → DistOn upperHalfPlaneOpens} (hm : HasSafeMembers P 𝓗 F ζ W (fun ω => reflField (X ω))) :
    HasSafeMembers P 𝓗 F ζ (-W) X := by
  intro s Fb hFbH D hD hsafe f Ξ
  have hFbH' : ballsK (reflBalls Fb) ⊆ H := by
    rw [ballsK_reflBalls]
    rintro _ ⟨z, hz, rfl⟩
    exact Sec7.FlowReflect.reflectC_mem_H (hFbH hz)
  have hsafe' : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ F ∧ (s : ℝ≥0∞) < ζ ω ∧
      Disjoint (ballsK (reflBalls Fb)) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ)) := by
    filter_upwards [hsafe] with ω hω hωD
    obtain ⟨h1, h2, h3⟩ := hω hωD
    refine ⟨h1, h2, ?_⟩
    have hwn : (fun r : ℝ => (-W) r.toNNReal ω) = -fun r : ℝ => W r.toNNReal ω := rfl
    rw [hwn, LP.fwdHull_neg] at h3
    rw [ballsK_reflBalls]
    have h4 := (Set.disjoint_image_iff LP.reflectC_injective).2 h3
    rwa [Sec7.FlowReflect.reflectC_image_image] at h4
  have hmem : (fun z => -f.1 (reflectC z)) ∈ zsSub (ballsU (reflBalls Fb)) := by
    rw [ballsU_reflBalls]
    exact neg_comp_reflectC_mem_zeroSpace f.2
  obtain ⟨f', hf'⟩ : ∃ f' : zsSub (ballsU (reflBalls Fb)), ∀ z, f'.1 z = -f.1 (reflectC z) :=
    ⟨⟨_, hmem⟩, fun z => rfl⟩
  have hVH : (ballsOpen Fb : Set ℂ) ⊆ H := (Coupling.ballsU_subset_ballsK Fb).trans hFbH
  have hV'H : (ballsOpen (reflBalls Fb) : Set ℂ) ⊆ H := (Coupling.ballsU_subset_ballsK _).trans hFbH'
  have hlap : reflTest (lapTest (ballsOpen (reflBalls Fb)) f') = -lapTest (ballsOpen Fb) f :=
    lapTest_reflect hVH hV'H f f' hf'
  have key := hm s (reflBalls Fb) hFbH' D hD hsafe' f' (-reflTest Ξ)
  have e1 : ∀ ω, reflField (X ω) (lapTest (ballsOpen (reflBalls Fb)) f' + -reflTest Ξ) =
      X ω (lapTest (ballsOpen Fb) f + Ξ) := fun ω => by
    rw [Sec7.FlowReflect.reflField_apply, map_add, map_neg, Sec7.FlowReflect.reflTest_reflTest, hlap, ← neg_add,
      map_neg, neg_neg]
  have e2 : ∀ ω, reflField (X ω) (-reflTest Ξ) = X ω Ξ := fun ω => by
    rw [Sec7.FlowReflect.reflField_apply, map_neg, Sec7.FlowReflect.reflTest_reflTest, map_neg, neg_neg]
  have e3 : projFactor (ballsOpen (reflBalls Fb)) f' (-reflTest Ξ) = projFactor (ballsOpen Fb) f Ξ :=
    projFactor_reflect (V := ballsOpen Fb) (V' := ballsOpen (reflBalls Fb)) hVH (ballsU_reflBalls Fb) f f' hf' Ξ
  simp only [e1, e2, e3] at key
  exact key

end InteractingSLE.Sec5.CfDown
