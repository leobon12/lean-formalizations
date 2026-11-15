/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerDReflClock
import InteractingSLE.Spec.Sec5.CfDownSafe

/-!
# Theorem 1.5's corrected first-contact kernels: the second path, by reflection

Packet PROVE-T15-FCKER4 (R82). Both fields of `FCK2CapForwardInputsC` for the second canonical chart path
(`FirstContactK2ForwardInputs₂Statement`), from the first path's fields (`FCKerC.hasFCK2CapForwardKernel_path₁`,
`FCKerD.hasFCK2CapForwardMembers_path₁`) applied to the reflected configuration (specification p. 270: "Reflection
and exchange of the path labels"):

* the flow lines `σ ∘ η₂` (seed `−x₂`, angle `−θ₂`) and `σ ∘ η₁` (seed `−x₁`, angle `−θ₁`) of the reflected field
  `−h ∘ σ` with data `y ↦ −b(−y)` (`Sec7.FlowReflect.IsFlowLine.reflect`), seeds and angles in the required order;
* the pair data `reflPair d` (`FCKerDRefl`), the sorted mirror word `sreflWord ∘ β` with Lemma 7.8's mean
  identification (`FCKerDReflWord`), the canonical clock `reflGamma`/`reflLife` and the driver `−W₂`
  (`FCKerDReflClock`);
* the conclusions read back: the same retained driver filtration, the protected sets (types by
  `mem_typeSet_sreflWord_iff`, hulls by `LP.fwdHull_neg`), the field `flowField 0 (−θ₂χ)` of the reflected chart field
  at `−ψ ∘ σ` is the original one at `ψ`, the characteristic functionals agree (`cfAt_reflect`), and the member
  identities of the reflected balls are the original ones (`Sec5.CfDown.lapTest_reflect`, `projFactor_reflect`).

* `hasFCK2CapForwardKernel_congr`, **`fck2CapForwardInputsC_path₂`**;
* **`firstContactK2ForwardInputs₂Statement_of`**, **`firstContactK2ForwardKernelsCStatement_of_lemma75_lemma77`**
  (the corrected statement in full from Lemmas 7.5, 7.7 and Aux. 56),
  `firstContactK2ForwardKernelsCStatement_of_thm12_thm13_lemma76'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb.FCKerD

open LQGMetric LQGMetric.MarkovZB WangWu.ChartConst DomainMarkov DomainMarkov.K2 Coupling LocalSets
open RetAux79 Sec7.PocketTraversal
open LP (reflectC)
open Sec7.FlowReflect (reflTest reflField reflData reflJumps)

universe u

section Congr

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Forward kernel data transfer to a smaller protected set, an equal variable and an a.s. equal limit on it. -/
theorem hasFCK2CapForwardKernel_congr {m : MeasurableSpace Ω} {S S' : Set Ω} {X G G' : Ω → ℂ}
    (h : HasFCK2CapForwardKernel (mΩ := mΩ) P m S' X G') (hS : ∀ᵐ ω ∂P, ω ∈ S → ω ∈ S')
    (hG : ∀ᵐ ω ∂P, ω ∈ S → G ω = G' ω) : HasFCK2CapForwardKernel (mΩ := mΩ) P m S X G := by
  obtain ⟨𝓜, Av, K, τ, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨𝓜, Av, K, τ, h1, h2, h3, h4, fun D hD hs => h5 D hD ?_, ?_⟩
  · filter_upwards [hs, hS] with ω a b hωD using b (a hωD)
  · filter_upwards [h6, hS, hG] with ω hl hs hg hωS
    obtain ⟨a, b⟩ := hl (hs hωS)
    exact ⟨a, by rw [hg hωS]; exact b⟩

end Congr

/-- **The second path's corrected forward inputs, by reflection of the first path's** (specification p. 270). Under
`σ(z) = −z̄` the two flow lines, exchanged, are again two flow lines; the first path's fields
(`FCKerC.hasFCK2CapForwardKernel_path₁`, `hasFCK2CapForwardMembers_path₁`) for the reflected configuration (pair data
`reflPair d`, word `sreflWord ∘ β`, driver `−W₂`, test `−ψ ∘ σ`, balls reflected) are the second path's fields. -/
theorem fck2CapForwardInputsC_path₂
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β : Ω → BoundaryWord} (hβ : Measurable[retSigma d P] β)
    (hsort : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hmean : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β)
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞} (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂)
    {W₂ : ℝ≥0 → Ω → ℝ} (hm₂ : ∀ t, Measurable (W₂ t)) (hc₂ : ∀ ω, Continuous (W₂ · ω))
    (hz₂ : ∀ ω, W₂ 0 ω = 0) (hg₂ : ∀ᵐ ω ∂P, ω ∈ meetSet d → IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) :
    FCK2CapForwardInputsC P κ θ₂ d β (hd.chartField κ h) U₂ W₂ (fcRetainedDriverFiltration P hd W₂ hm₂) := by
  classical
  subst hζ₁ hζ₂
  have hd' := isMeasGood_reflPair hd
  have hb' := Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb
  have hx' : -x₁ < -x₂ := neg_lt_neg hx
  have hθ' : -θ₂ < -θ₁ + Real.pi := by linarith
  have hh' := Sec7.FlowReflect.IsGFFWithBoundaryData.reflect hh
  have hη₁' := Sec7.FlowReflect.IsFlowLine.reflect hb hη₂
  have hη₂' := Sec7.FlowReflect.IsFlowLine.reflect hb hη₁
  have hae' : ∀ᵐ ω ∂P, ω ∈ (reflPair d).G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → (reflPair d).η₁ ω s = reflectC (η₂ ω s)) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → (reflPair d).η₂ ω s = reflectC (η₁ ω s) := by
    filter_upwards [hae] with ω ⟨hG, h1, h2⟩
    exact ⟨hG, fun s hs => by rw [show (reflPair d).η₁ ω s = reflectC (d.η₂ ω s) from rfl, h2 s hs],
      fun s hs => by rw [show (reflPair d).η₂ ω s = reflectC (d.η₁ ω s) from rfl, h1 s hs]⟩
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hu₀' : IsBoundedHarmonicExtension (reflData b) (reflJumps jumps) (fun z => -u₀ (reflectC z)) :=
    Sec7.FlowReflect.IsBoundedHarmonicExtension.reflect hu₀ fun x hx =>
      ⟨fun h => hx (Sec7.FlowReflect.mem_reflJumps.2 h), rfl⟩
  have hβ' : Measurable[retSigma (reflPair d) P] fun ω => sreflWord (β ω) := by
    rw [reflPair_retSigma hd]
    exact measurable_sreflWord.comp hβ
  have hsort' : ∀ᵐ ω ∂P, ω ∈ meetSet (reflPair d) → (sreflWord (β ω)).IsSorted := by
    rw [reflPair_meetSet hd]
    filter_upwards [hsort] with ω h hm using sreflWord_isSorted (h hm)
  have hmean' := isBoxMeanIdentification_refl hu₀c hd hsort hmean
  -- the canonical clock of the reflected configuration
  obtain ⟨E, -, -, hME, -, hs₂, -, -⟩ := FCKerC.exists_fcContEvent h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd rfl rfl hae
  obtain ⟨γ', γ'', U', U'', -, -, -, -, -, -, hc', -⟩ :=
    exists_canonClock Theorem15.aux25Statement h77 hκ hκ4 hb' hx' hθ' hh' hη₁' hη₂' hd' rfl rfl hae'
  have hcanon' := isCanonClock_refl hd hcanon hs₂ hME hc'
  -- the reflected driver
  have hm' : ∀ t, Measurable fun ω => -W₂ t ω := fun t => (hm₂ t).neg
  have hcW' : ∀ ω, Continuous fun t => -W₂ t ω := fun ω => (hc₂ ω).neg
  have hz' : ∀ ω, -W₂ 0 ω = 0 := fun ω => by rw [hz₂, neg_zero]
  have hg' : ∀ᵐ ω ∂P, ω ∈ meetSet (reflPair d) →
      IsGeneratingTrace (fun t => -W₂ t ω) (reflLife d U₂ U' ω) (reflGamma d γ₂ γ' ω) := by
    rw [reflPair_meetSet hd]
    filter_upwards [hg₂] with ω hω hm
    rw [reflLife_of_mem hm, reflGamma_of_mem hm]
    exact LP.isGeneratingTrace_reflect (hω hm)
  have hF := fcRetainedDriverFiltration_reflPair hd P W₂ hm₂ hm'
  have hhull : ∀ ω (q : ℝ≥0), fwdHull (fun s : ℝ => -W₂ s.toNNReal ω) q =
      reflectC '' fwdHull (fun s : ℝ => W₂ s.toNNReal ω) q := fun ω q =>
    LP.fwdHull_neg (fun s : ℝ => W₂ s.toNNReal ω) q
  refine ⟨fun a ψ q => ?_, fun q Fb hFb f Ξ => ?_⟩
  · -- the Gaussian field
    let a' : ForceWordType := ⟨a.nR, a.nL, a.rhoR, a.rhoL⟩
    have key := FCKerC.hasFCK2CapForwardKernel_path₁ h75 h77 h56 hκ hκ4 hb' hx' hθ' hh' hη₁' hη₂' hd' rfl rfl
      hae' hu₀' hβ' hsort' hmean' hcanon' hm' hcW' hz' hg' a' (-reflTest ψ) q
    rw [hF] at key
    have hX : (fun ω => Complex.exp (Complex.I * (Exist.flowField 0 (-θ₂ * chiC κ)
        (hd'.chartField κ (fun ω => reflField (h ω)) ω) (-reflTest ψ) : ℂ))) =
        fun ω => Complex.exp (Complex.I * (Exist.flowField 0 (θ₂ * chiC κ) (hd.chartField κ h ω) ψ : ℂ)) := by
      funext ω
      rw [neg_mul, flowField_chartField_reflPair hd, Sec7.FlowReflect.reflField_apply,
        Sec7.FlowReflect.reflTest_neg, Sec7.FlowReflect.reflTest_reflTest, map_neg, neg_neg]
    rw [hX] at key
    have hsupp : ∀ ω, Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W₂ s.toNNReal ω) q) →
        Disjoint (tsupport ⇑(-reflTest ψ)) (fwdHull (fun s : ℝ => -W₂ s.toNNReal ω) q) := fun ω hdis => by
      rw [show ⇑(-reflTest ψ) = -⇑(reflTest ψ) from rfl, tsupport_neg, Sec7.FlowReflect.tsupport_reflTest,
        hhull]
      exact (Set.disjoint_image_iff LP.reflectC_injective).2 hdis
    refine hasFCK2CapForwardKernel_congr key (ae_of_all P fun ω hω => ?_) (ae_of_all P fun ω hω => ?_)
    · obtain ⟨⟨hM, hT⟩, hq, hdis⟩ := hω
      refine ⟨⟨(reflPair_meetSet hd).symm ▸ hM, ?_⟩, ?_, hsupp ω hdis⟩
      · exact mem_typeSet_sreflWord_iff.2 hT
      · rw [reflLife_of_mem hM]
        exact hq
    · obtain ⟨⟨hM, hT⟩, hq, hdis⟩ := hω
      have hxL : (fun ω => FCDet.typeXL κ (-θ₂) a.nR a.nL a.rhoR a.rhoL (sreflWord (β ω))) =
          fun ω i => -FCDet.typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω) i := funext fun ω => typeXL_sreflWord
      have hxR : (fun ω => FCDet.typeXR κ (-θ₂) a.nR a.nL a.rhoR a.rhoL (sreflWord (β ω))) =
          fun ω j => -FCDet.typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω) j := funext fun ω => typeXR_sreflWord
      refine (cfAt_reflect hc₂ (fun z hz => ?_) (fun z => ?_) (Coupling.tsupport_subset_H ψ) hdis).symm
      · change bheProc κ a.rhoR a.rhoL (fun t ω => -W₂ t ω)
          (geomLW (fun t ω => -W₂ t ω) fun ω => FCDet.typeXL κ (-θ₂) a.nR a.nL a.rhoR a.rhoL (sreflWord (β ω)))
          (geomRW (fun t ω => -W₂ t ω) fun ω => FCDet.typeXR κ (-θ₂) a.nR a.nL a.rhoR a.rhoL (sreflWord (β ω)))
          ω q z = _
        rw [hxL, hxR]
        exact bheProc_reflect κ a.rhoL a.rhoR W₂ _ _ ω q hz
      · simp only [neg_apply, Sec7.FlowReflect.reflTest_apply]
  · -- the member field
    have hFbH' : ballsK (Sec5.CfDown.reflBalls Fb) ⊆ H := by
      rw [Sec5.CfDown.ballsK_reflBalls]
      rintro _ ⟨z, hz, rfl⟩
      exact Sec7.FlowReflect.reflectC_mem_H (hFb hz)
    have hmem : (fun z => -f.1 (reflectC z)) ∈ zsSub (ballsU (Sec5.CfDown.reflBalls Fb)) := by
      rw [Sec5.CfDown.ballsU_reflBalls]
      exact Sec5.CfDown.neg_comp_reflectC_mem_zeroSpace f.2
    obtain ⟨f', hf'⟩ : ∃ f' : zsSub (ballsU (Sec5.CfDown.reflBalls Fb)), ∀ z, f'.1 z = -f.1 (reflectC z) :=
      ⟨⟨_, hmem⟩, fun z => rfl⟩
    have hVH : (ballsOpen Fb : Set ℂ) ⊆ H := (Coupling.ballsU_subset_ballsK Fb).trans hFb
    have hV'H : (ballsOpen (Sec5.CfDown.reflBalls Fb) : Set ℂ) ⊆ H :=
      (Coupling.ballsU_subset_ballsK _).trans hFbH'
    have hlap : reflTest (lapTest (ballsOpen (Sec5.CfDown.reflBalls Fb)) f') = -lapTest (ballsOpen Fb) f :=
      Sec5.CfDown.lapTest_reflect hVH hV'H f f' hf'
    have key := hasFCK2CapForwardMembers_path₁ h75 h77 h56 hκ hκ4 hb' hx' hθ' hh' hη₁' hη₂' hd' rfl rfl hae'
      hu₀' hcanon' hm' hcW' hz' hg' q (Sec5.CfDown.reflBalls Fb) hFbH' f' (-reflTest Ξ)
    rw [hF] at key
    have e1 : ∀ ω, Exist.flowField 0 (-θ₂ * chiC κ) (hd'.chartField κ (fun ω => reflField (h ω)) ω)
        (lapTest (ballsOpen (Sec5.CfDown.reflBalls Fb)) f' + -reflTest Ξ) =
        Exist.flowField 0 (θ₂ * chiC κ) (hd.chartField κ h ω) (lapTest (ballsOpen Fb) f + Ξ) := fun ω => by
      rw [neg_mul, flowField_chartField_reflPair hd, Sec7.FlowReflect.reflField_apply, map_add, map_neg,
        Sec7.FlowReflect.reflTest_reflTest, hlap, ← neg_add, map_neg, neg_neg]
    have e2 : ∀ ω, Exist.flowField 0 (-θ₂ * chiC κ) (hd'.chartField κ (fun ω => reflField (h ω)) ω)
        (-reflTest Ξ) = Exist.flowField 0 (θ₂ * chiC κ) (hd.chartField κ h ω) Ξ := fun ω => by
      rw [neg_mul, flowField_chartField_reflPair hd, Sec7.FlowReflect.reflField_apply, map_neg,
        Sec7.FlowReflect.reflTest_reflTest, map_neg, neg_neg]
    have e3 : projFactor (ballsOpen (Sec5.CfDown.reflBalls Fb)) f' (-reflTest Ξ) = projFactor (ballsOpen Fb) f Ξ :=
      Sec5.CfDown.projFactor_reflect (V := ballsOpen Fb) (V' := ballsOpen (Sec5.CfDown.reflBalls Fb)) hVH
        (Sec5.CfDown.ballsU_reflBalls Fb) f f' hf' Ξ
    simp only [e1, e2, e3] at key
    refine FCKerC.hasFCK2CapForwardMembers_mono (ae_of_all P fun ω hω => ?_) key
    obtain ⟨hM, hq, hdis⟩ := hω
    refine ⟨(reflPair_meetSet hd).symm ▸ hM, by rw [reflLife_of_mem hM]; exact hq, ?_⟩
    rw [Sec5.CfDown.ballsK_reflBalls, hhull]
    exact (Set.disjoint_image_iff LP.reflectC_injective).2 hdis

end InteractingSLE.Restart.FCPlumb.FCKerD

namespace InteractingSLE.Restart.FCPlumb

open LQGMetric.MarkovZB

universe u

/-- **`FirstContactK2ForwardInputs₂Statement` from Lemma 7.5, Lemma 7.7 and Aux. lemma 56** (by reflection). -/
theorem firstContactK2ForwardInputs₂Statement_of (h75 : Theorem15.Lemma75Statement.{u})
    (h77 : Supp10.Lemma77Statement.{u}) (h56 : RetainedRangeEntranceStatement.{u}) :
    FirstContactK2ForwardInputs₂Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  exact FCKerD.fck2CapForwardInputsC_path₂ h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hβ hsort
    hmean hcanon hm₂ hc₂ hz₂ (hg.mono fun _ h hω => (h hω).2)

/-- **The corrected forward-kernel statement from Lemma 7.5, Lemma 7.7 and Aux. lemma 56**: both fields of both
paths are proved. -/
theorem firstContactK2ForwardKernelsCStatement_of_lemma75_lemma77
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) : FirstContactK2ForwardKernelsCStatement.{u} :=
  firstContactK2ForwardKernelsCStatement_of_members₁_inputs₂ h75 h77 h56
    (firstContactK2ForwardMembers₁Statement_of h75 h77 h56) (firstContactK2ForwardInputs₂Statement_of h75 h77 h56)

/-- **The corrected forward-kernel statement from Theorems 1.2–1.3 and Lemma 7.6** (R48: the consumer is
Theorem 1.5). -/
theorem firstContactK2ForwardKernelsCStatement_of_thm12_thm13_lemma76'
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h76 : Sec7.Lemma76Statement.{u}) : FirstContactK2ForwardKernelsCStatement.{u} :=
  firstContactK2ForwardKernelsCStatement_of_lemma75_lemma77 (lemma75Statement_of_thm12_thm13 h12 h13)
    (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76) firstContact_retainedRangeEntranceStatement

end InteractingSLE.Restart.FCPlumb

