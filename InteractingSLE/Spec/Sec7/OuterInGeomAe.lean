/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterInCounterflow
import InteractingSLE.Spec.Sec7.OuterInGeom
import InteractingSLE.Spec.Sec7.R7LeavesFirst

/-!
# Theorem R.7's outer pockets: the `geom` and `geomInf` inputs on every R.7 configuration

Packet PROVE-R7-OUTERIN. `HOuter.R7OuterInputs.geom/geomInf` ask, at every positive rational change time, for the
pocket geometry `OuterGeom(Inf)` almost surely on the change configuration. Here every pathwise configuration fact used
by the per-realization assemblies of `OuterInGeom` is proved almost surely on an R.7 configuration
(`R7Outer.IsR7OuterConfig`), for versions `R`, `L` of the arms and `η` of the counterflow's trace:

* the walls' and frontiers' configuration of each shape (`IsR7OuterConfig.ae_{right,left,outer}Outer`, PROVE-R7-STOPIN;
  the shape is read off the angles: `θ_R < −π/2 ⟺ r_L > d`, `π/2 < θ_L ⟺ r_R > d`, at least one holds on the outer
  range);
* the counterflow: Loewner trace, open half-plane at positive times, Aux. lemma 42, exterior avoidance
  (`OuterInCounterflow`);
* reverse visits and visits of the contained arm and of the certified frontiers `β_R`, `β_L` (Lemma 5.7 in the inversion
  chart, `R7Leaves.firstHit_r7`, at angles in `[−π/2, π/2]`; `WallsPath.ae_walls_of_simpleProper_rat_firstHit`).

What remains is collected in `OuterGeomInputs` (per configuration): Aux. lemma 37 along the contained side of the
bounded mixed pockets (the germ comparison `BarrierAttachConst`); for the bounded two-outer pockets Aux. lemma 37
along the clipped `β_R` and Aux. lemma 41's relative driver; for the mixed pockets opening at the flow seed Aux. lemma
37 along the contained side, §5.4's gap equality and Aux. lemma 41's relative driver; for the two-outer pockets opening
at the flow seed Aux. lemma 37 along the clipped `β_R` and Aux. lemma 41's relative driver.

* **`ae_outerGeom`**, **`ae_outerGeomInf`**: the `geom`, `geomInf` fields from `OuterGeomInputs`.

R48: the named statements used are Propositions 4.11 and 5.1 in chart `Q`, Lemma 4.7Q (`Lemma47QHitStatement`,
`Lemma47QHitTStatement`) and Zhan's Part A, all on R48's list of Theorem 1.2 inputs (as in PROVE-HOUTER and
PROVE-R7-LEAVES); nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.OuterIn

open WangWu Lemma71I PocketCoord PocketJordan PocketWordAssembly PocketSeedOpen R7StopIn HOuter R7Outer R7Leaves

section Inputs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The remaining inputs of the outer pockets' geometry on one configuration** (`β_R`, `β_L` the certified frontiers,
`R`, `L` versions of the arms, `η` a version of the counterflow's trace), at every positive rational change time,
almost surely on the change configuration:
* `attachLeft`, `attachRight` — bounded mixed pockets (exactly one outer arm): Aux. lemma 37 along the contained side;
* `outerOuter` — bounded pockets with two outer arms: Aux. lemma 37 along the clipped `β_R` and Aux. lemma 41's
  relative driver (§5.4's gap equality is proved: `pocketGapEq_outerOuter`);
* `infLeft`, `infRight` — mixed pockets opening at the flow seed: Aux. lemma 37 along the contained side, §5.4's gap
  equality and Aux. lemma 41, at infinity;
* `infOuterOuter` — pockets with two outer arms opening at the flow seed: Aux. lemma 37 along the clipped `β_R` and Aux.
  lemma 41 at infinity (the gap equality is proved: `pocketGapEqInf_outerOuter`). -/
structure OuterGeomInputs (k rL rR : ℝ) (P : Measure Ω) (βR βL R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ) : Prop where
  attachLeft : π / 2 < R7.thetaL k rR → ¬ R7.thetaR k rL < -(π / 2) → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
    IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
    BarrierAttachConst (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q)) (cfArcR (R ω) (L ω) (StripSys.rt q))
      (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0))
  attachRight : R7.thetaR k rL < -(π / 2) → ¬ π / 2 < R7.thetaL k rR → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
    IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
    BarrierAttachConst (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q)) (cfArcL (R ω) (L ω) (StripSys.rt q))
      (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0))
  outerOuter : R7.thetaR k rL < -(π / 2) → π / 2 < R7.thetaL k rR → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
    IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
    OuterOuterAttach (R ω) (L ω) (βR ω) (StripSys.rt q) (η ω) ∧ OuterRelLoewner (R ω) (L ω) (StripSys.rt q) (η ω)
  infLeft : π / 2 < R7.thetaL k rR → ¬ R7.thetaR k rL < -(π / 2) → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
    IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
    BarrierAttachConstInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q)) (cfArcRInf (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) ∧
      PocketGapEqInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) ∧
      OuterRelLoewnerInf (R ω) (L ω) (StripSys.rt q) (η ω)
  infRight : R7.thetaR k rL < -(π / 2) → ¬ π / 2 < R7.thetaL k rR → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
    IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
    BarrierAttachConstInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) ∧
      PocketGapEqInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)) ∧
      OuterRelLoewnerInf (R ω) (L ω) (StripSys.rt q) (η ω)
  infOuterOuter : R7.thetaR k rL < -(π / 2) → π / 2 < R7.thetaL k rR → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
    IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
    OuterOuterAttachInf (R ω) (L ω) (βR ω) (StripSys.rt q) (η ω) ∧ OuterRelLoewnerInf (R ω) (L ω) (StripSys.rt q) (η ω)

end Inputs

section Walls

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- **Reverse visits and visits of a flow line of the R.7 field** (angle `θ ∈ [−π/2, π/2]`, almost surely simple
proper) by a version `η` of the counterflow's trace: Lemma 5.7's rational first exits (`R7Leaves.firstHit_r7`) give
both almost surely (`WallsPath.ae_walls_of_simpleProper_rat_firstHit`). -/
theorem ae_walls_r7 (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ') {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2))
    {γ : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 θ P h γ ζ)
    (hγs : ∀ᵐ ω ∂P, IsSimpleProper (γ ω)) {η : Ω → ℝ → ℂ} (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hη0 : ∀ ω, η ω 0 = 0) (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, IsWallReverseVisit (γ ω) (η ω) ∧ IsWallVisited (γ ω) (η ω) :=
  WallsPath.ae_walls_of_simpleProper_rat_firstHit hγs hηc
    (firstHit_r7 h411 h47 h47T hk4 hc hc' hh hcf hθ hfl hγs hη0 hηtr)

/-- The outer range has an outer arm: `k/2 − 4 < max(r_L, r_R)` gives `θ_R < −π/2` or `π/2 < θ_L`. -/
theorem outer_or_outer (hk4 : 4 < k) (hmax : k / 2 - 4 < max rL rR) :
    R7.thetaR k rL < -(π / 2) ∨ π / 2 < R7.thetaL k rR := by
  rcases lt_max_iff.1 hmax with h | h
  · exact Or.inl ((R7.d_lt_rL_iff hk4).1 h)
  · exact Or.inr ((R7.d_lt_rR_iff hk4).1 h)

end Walls

section Geom

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}

/-- **The `geom` input of `HOuter.R7OuterInputs` on an R.7 configuration** (`max(r_L, r_R) > k/2 − 4`): at every
positive rational change time, almost surely on the bounded change configuration, the pocket geometry `OuterGeom`
holds — every pathwise configuration fact is proved here, the remaining ones are `OuterGeomInputs`. -/
theorem ae_outerGeom (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hmax : k / 2 - 4 < max rL rR) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) (hV : IsR7Versions P W' αR αL R L η)
    (hin : OuterGeomInputs k rL rR P βR βL R L η) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      OuterGeom (R ω) (L ω) (StripSys.rt q) (η ω) := by
  have hpi := Real.pi_pos
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hreg := hcfg.regular
  have hβRs : ∀ᵐ ω ∂P, IsSimpleProper (βR ω) := hreg.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.1
  have hβLs : ∀ᵐ ω ∂P, IsSimpleProper (βL ω) := hreg.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.2.1
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hV.η_trace
  have hH := ae_counterflow_mem_H_r7 hA hk4 hc hc' hcfg.gff hcfg.counterflow hD hV.η_trace
  have h42 := ae_noSimpleArc_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hD hV.η_trace
  have hav := ae_avoid_counterflow_r7 hk4 hc hc' hcfg hV.η_trace
  have hwβR := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := -(π / 2))
    ⟨le_rfl, by linarith⟩ hcfg.flow_βR hβRs hV.η_cont hV.η_zero hV.η_trace
  have hwβL := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := π / 2)
    ⟨by linarith, le_rfl⟩ hcfg.flow_βL hβLs hV.η_cont hV.η_zero hV.η_trace
  by_cases hθR : R7.thetaR k rL < -(π / 2)
  · by_cases hθL : π / 2 < R7.thetaL k rR
    · -- two outer arms
      filter_upwards [hcfg.ae_outerOuter h55 hk4 hL hR hc hc' hθR hθL, hV.R_ae, hV.L_ae, htrace, h42, hav, hwβR,
        hwβL, hin.outerOuter hθR hθL q hq] with ω hω hRe hLe htr h42ω havω hwR hwL hinω hconf hpos
      rw [← hRe, ← hLe] at hω
      obtain ⟨-, hβR, hβL, -, -, hO₁, hO₂, hc₁R, hc₁L, hc₂R, hc₂L, hoR, hoL, -⟩ := hω
      obtain ⟨hAC, hloc⟩ := hinω hconf hpos
      exact outerGeom_outerOuter hconf hpos hβR hβL hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L hoR hoL htr.1 htr.2.1
        (by simpa only [Real.toNNReal_zero] using htr.2.2) havω hwR.1 hwL.1 hwR.2 h42ω hAC hloc
    · -- outer right arm, contained left arm
      have hθLm : R7.thetaL k rR ∈ Icc (-(π / 2)) (π / 2) :=
        ⟨(R7.neg_pi_div_two_lt_thetaL hk4 hR).le, not_lt.1 hθL⟩
      have hLs : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
        filter_upwards [hreg, hV.L_ae] with ω hω he
        rw [he]; exact IsSeedProper.isSimpleProper hω.2.2.2.1
      have hflL := IsFlowLine.congr_path (η' := L) hcfg.flow_αL (hV.L_ae.mono fun ω hω t _ => by rw [hω])
      have hwL := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθLm hflL hLs hV.η_cont
        hV.η_zero hV.η_trace
      filter_upwards [hcfg.ae_rightOuter h55 hk4 hL hR hc hc' hθR, hV.R_ae, hV.L_ae, htrace, hH, h42, hav, hwβR,
        hwL, hin.attachRight hθR hθL q hq] with ω hω hRe hLe htr hHω h42ω havω hwM hwLω hinω hconf hpos
      rw [← hRe, ← hLe] at hω
      obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
      exact outerGeom_rightOuter hconf hpos hM hO hcR hcL ho htr.1 htr.2.1
        (by simpa only [Real.toNNReal_zero] using htr.2.2) hHω (fun t ht hm => havω t ht (Or.inl hm))
        hwLω.1 hwLω.2 hwM.1 hwM.2 h42ω (hinω hconf hpos)
  · by_cases hθL : π / 2 < R7.thetaL k rR
    · -- outer left arm, contained right arm
      have hθRm : R7.thetaR k rL ∈ Icc (-(π / 2)) (π / 2) :=
        ⟨not_lt.1 hθR, (R7.thetaR_lt_pi_div_two hk4 hL).le⟩
      have hRs : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
        filter_upwards [hreg, hV.R_ae] with ω hω he
        rw [he]; exact IsSeedProper.isSimpleProper hω.1
      have hflR := IsFlowLine.congr_path (η' := R) hcfg.flow_αR (hV.R_ae.mono fun ω hω t _ => by rw [hω])
      have hwR := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθRm hflR hRs hV.η_cont
        hV.η_zero hV.η_trace
      filter_upwards [hcfg.ae_leftOuter h55 hk4 hL hR hc hc' hθL, hV.R_ae, hV.L_ae, htrace, hH, h42, hav, hwβL,
        hwR, hin.attachLeft hθL hθR q hq] with ω hω hRe hLe htr hHω h42ω havω hwM hwRω hinω hconf hpos
      rw [← hRe, ← hLe] at hω
      obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
      exact outerGeom_leftOuter hconf hpos hM hO hcR hcL ho htr.1 htr.2.1
        (by simpa only [Real.toNNReal_zero] using htr.2.2) hHω (fun t ht hm => havω t ht (Or.inr hm))
        hwRω.1 hwRω.2 hwM.1 hwM.2 h42ω (hinω hconf hpos)
    · exact absurd (outer_or_outer hk4 hmax) (by tauto)

/-- **The `geomInf` input of `HOuter.R7OuterInputs` on an R.7 configuration** (`max(r_L, r_R) > k/2 − 4`): at every
positive rational change time, almost surely on the change configuration opening at the flow seed, the pocket
geometry `OuterGeomInf` holds from `OuterGeomInputs`. -/
theorem ae_outerGeomInf (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : k / 2 - 4 < max rL rR) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) (hV : IsR7Versions P W' αR αL R L η)
    (hin : OuterGeomInputs k rL rR P βR βL R L η) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      OuterGeomInf (R ω) (L ω) (StripSys.rt q) (η ω) := by
  have hpi := Real.pi_pos
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hreg := hcfg.regular
  have hβRs : ∀ᵐ ω ∂P, IsSimpleProper (βR ω) := hreg.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.1
  have hβLs : ∀ᵐ ω ∂P, IsSimpleProper (βL ω) := hreg.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.2.1
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hV.η_trace
  have hav := ae_avoid_counterflow_r7 hk4 hc hc' hcfg hV.η_trace
  have hwβR := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := -(π / 2))
    ⟨le_rfl, by linarith⟩ hcfg.flow_βR hβRs hV.η_cont hV.η_zero hV.η_trace
  have hwβL := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := π / 2)
    ⟨by linarith, le_rfl⟩ hcfg.flow_βL hβLs hV.η_cont hV.η_zero hV.η_trace
  by_cases hθR : R7.thetaR k rL < -(π / 2)
  · by_cases hθL : π / 2 < R7.thetaL k rR
    · -- two outer arms
      have h42 := ae_noSimpleArc_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hD hV.η_trace
      filter_upwards [hcfg.ae_outerOuter h55 hk4 hL hR hc hc' hθR hθL, hV.R_ae, hV.L_ae, htrace, hav, hwβR,
        hwβL, h42, hin.infOuterOuter hθR hθL q hq] with ω hω hRe hLe htr havω hwR hwL h42ω hinω hconf h0
      rw [← hRe, ← hLe] at hω
      obtain ⟨-, hβR, hβL, -, -, hO₁, hO₂, hc₁R, hc₁L, hc₂R, hc₂L, hoR, hoL, -⟩ := hω
      obtain ⟨hAC, hloc⟩ := hinω hconf h0
      exact outerGeomInf_outerOuter hconf h0 hβR hβL hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L hoR hoL htr.1 havω hwR.1 hwL.1
        hwR.2 h42ω hAC hloc
    · -- outer right arm, contained left arm
      have hθLm : R7.thetaL k rR ∈ Icc (-(π / 2)) (π / 2) :=
        ⟨(R7.neg_pi_div_two_lt_thetaL hk4 hR).le, not_lt.1 hθL⟩
      have hLs : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
        filter_upwards [hreg, hV.L_ae] with ω hω he
        rw [he]; exact IsSeedProper.isSimpleProper hω.2.2.2.1
      have hflL := IsFlowLine.congr_path (η' := L) hcfg.flow_αL (hV.L_ae.mono fun ω hω t _ => by rw [hω])
      have hwL := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθLm hflL hLs hV.η_cont
        hV.η_zero hV.η_trace
      filter_upwards [hcfg.ae_rightOuter h55 hk4 hL hR hc hc' hθR, hV.R_ae, hV.L_ae, htrace, hav, hwβR, hwL,
        hin.infRight hθR hθL q hq] with ω hω hRe hLe htr havω hwM hwLω hinω hconf h0
      rw [← hRe, ← hLe] at hω
      obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
      obtain ⟨hAC, hgap, hloc⟩ := hinω hconf h0
      exact outerGeomInf_rightOuter hconf h0 hM hO hcR hcL ho htr.1 (fun t ht hm => havω t ht (Or.inl hm))
        hwLω.1 hwLω.2 hwM.1 hAC hgap hloc
  · by_cases hθL : π / 2 < R7.thetaL k rR
    · -- outer left arm, contained right arm
      have hθRm : R7.thetaR k rL ∈ Icc (-(π / 2)) (π / 2) :=
        ⟨not_lt.1 hθR, (R7.thetaR_lt_pi_div_two hk4 hL).le⟩
      have hRs : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
        filter_upwards [hreg, hV.R_ae] with ω hω he
        rw [he]; exact IsSeedProper.isSimpleProper hω.1
      have hflR := IsFlowLine.congr_path (η' := R) hcfg.flow_αR (hV.R_ae.mono fun ω hω t _ => by rw [hω])
      have hwR := ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow hθRm hflR hRs hV.η_cont
        hV.η_zero hV.η_trace
      filter_upwards [hcfg.ae_leftOuter h55 hk4 hL hR hc hc' hθL, hV.R_ae, hV.L_ae, htrace, hav, hwβL, hwR,
        hin.infLeft hθL hθR q hq] with ω hω hRe hLe htr havω hwM hwRω hinω hconf h0
      rw [← hRe, ← hLe] at hω
      obtain ⟨-, hM, -, -, hO, hcR, hcL, ho, -⟩ := hω
      obtain ⟨hAC, hgap, hloc⟩ := hinω hconf h0
      exact outerGeomInf_leftOuter hconf h0 hM hO hcR hcL ho htr.1 (fun t ht hm => havω t ht (Or.inr hm))
        hwRω.1 hwRω.2 hwM.1 hAC hgap hloc
    · exact absurd (outer_or_outer hk4 hmax) (by tauto)

end Geom

end InteractingSLE.Sec7.OuterIn
