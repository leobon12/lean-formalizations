/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQData
import InteractingSLE.Spec.Sec5.CrossRestartKernelQEndHit
import InteractingSLE.Spec.Sec5.CrossCondThetaMean

/-!
# Lemma 4.7 at a relative angle: the counterflow word and its round trip

PROVE-L47-ANGLE. The real-flow transport and harmonic uniqueness are reused from
`CrossRestartKernelQData`; only the angle-dependent round trip is generalized.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open scoped Real
open QuantumZipper (H chiC)
namespace InteractingSLE.Sec5.Lemma47Angle
open CrossRestart.KernelQ
open MartChar.RealFlow Restart.RetAux79
open Sec7.StripSysField GlueCond Cond44Ref CrossCond.Theta GlueImg

/-- Left weights of the counterflow of the field shifted by `-θχ`. -/
abbrev qρLT (κ θ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :=
  cfRhoL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR)

/-- Right weights of the counterflow of the field shifted by `-θχ`. -/
abbrev qρRT (κ θ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :=
  cfRhoR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR)

/-- Left seed marks of the shifted counterflow word. -/
abbrev qxLT (κ θ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :=
  flowLineXL (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0

/-- Right seed marks of the shifted counterflow word. -/
abbrev qxRT (κ θ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :=
  flowLineXR (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0

/-- Dualizing the counterflow word at relative angle `-θ` restores `b + θχ`. -/
theorem counterflowData_bDataT_cfWord_angle {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (θ : ℝ) {x : ℝ}
    (hx : x ∉ returnExcept (counterflowJumps J)) :
    counterflowData (16 / κ) (bDataT (cfRhoL κ b J) (cfRhoR κ b J)
      (flowLineXL (counterflowData κ b) (counterflowJumps J) 0)
      (flowLineXR (counterflowData κ b) (counterflowJumps J) 0) (-θ) (16 / κ)) x =
      b x + θ * chiC κ := by
  have h := counterflowData_bDataT_cfWord hκ hb hx
  simp only [counterflowData, inverseData, returnData, bDataT] at h ⊢
  rw [Sec4.chiC_sixteen_div hκ] at h ⊢
  linear_combination h

/-- The slit data at general relative angle recover the original flow word. -/
theorem eqOn_bhe_cfDataAt_flow_angle {κ θ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {w : ℝ → ℝ} (hw : Continuous w) {q : ℝ} (hq : 0 ≤ q) {v u : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension
      (cfDataAt (16 / κ) (bDataT (cfRhoL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR))
        (cfRhoR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR))
        (flowLineXL (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
        (flowLineXR (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
        (-θ) (16 / κ))
        (forceJumpFinset
          (flowLineXL (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
          (flowLineXR (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0))
        w q)
      (forceJumpSet
        (cfMarkL (16 / κ) (bDataT (cfRhoL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR))
          (cfRhoR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR))
          (flowLineXL (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
          (flowLineXR (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
          (-θ) (16 / κ))
          (forceJumpFinset
            (flowLineXL (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
            (flowLineXR (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0))
          w q)
        (cfMarkR (16 / κ) (bDataT (cfRhoL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR))
          (cfRhoR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR))
          (flowLineXL (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
          (flowLineXR (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
          (-θ) (16 / κ))
          (forceJumpFinset
            (flowLineXL (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
            (flowLineXR (counterflowData κ (bDataT ρL ρR xL xR θ κ)) (counterflowJumps (forceJumpFinset xL xR)) 0))
          w q)) v)
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -w s) (-xL i) q - w q)
        (fun j => rightImg w (xR j) q - w q))
      (forceJumpSet (fun i => -rightImg (fun s => -w s) (-xL i) q - w q) (fun j => rightImg w (xR j) q - w q)) u) :
    EqOn v u H := by
  classical
  set b := bDataT ρL ρR xL xR θ κ with hbdef
  set J := forceJumpFinset xL xR with hJ
  set b'' := bDataT (cfRhoL κ b J) (cfRhoR κ b J) (flowLineXL (counterflowData κ b) (counterflowJumps J) 0)
    (flowLineXR (counterflowData κ b) (counterflowJumps J) 0) (-θ) (16 / κ) with hb''def
  set J'' := forceJumpFinset (flowLineXL (counterflowData κ b) (counterflowJumps J) 0)
    (flowLineXR (counterflowData κ b) (counterflowJumps J) 0) with hJ''
  have hk : 0 < 16 / κ := by positivity
  have hkk : (16 : ℝ) / (16 / κ) = κ := by field_simp
  have hkk' : 0 < (16 : ℝ) / (16 / κ) := by rw [hkk]; exact hκ
  have hb : IsPiecewiseConstantBoundaryData b J := isPiecewiseConstant_forceData κ ρL ρR xL xR _
  have hb'' : IsPiecewiseConstantBoundaryData b'' J'' := isPiecewiseConstant_forceData (16 / κ) _ _ _ _ _
  -- the round trip at time `0`
  have h0 : ∀ x ∉ counterflowJumps J'' ∪ returnExcept (counterflowJumps J),
      forceBoundaryData (16 / (16 / κ)) (cfRhoL (16 / κ) b'' J'') (cfRhoR (16 / κ) b'' J'')
        (flowLineXL (counterflowData (16 / κ) b'') (counterflowJumps J'') 0)
        (flowLineXR (counterflowData (16 / κ) b'') (counterflowJumps J'') 0) x =
      forceBoundaryData (16 / (16 / κ)) ρL ρR xL xR x := by
    intro x hx
    rw [Finset.mem_union, not_or] at hx
    have hx0 : x ≠ 0 := fun h => hx.1 (by rw [h]; exact Finset.mem_insert_self _ _)
    rw [Sec4.forceBoundaryData_flowLine hkk' (isPiecewiseConstant_counterflowData (16 / κ) hb'') hx0 hx.1,
      counterflowData_bDataT_cfWord_angle hκ hb θ hx.2, hkk]
    simp only [hbdef, bDataT]
    ring
  obtain ⟨T, hT⟩ := exists_finset_forceBoundaryData_flow_eq hw hq (16 / (16 / κ)) _ _ ρL ρR
    (fun i => Theorem14.GW3Word.flowLineXL_nonpos _ _ i) (fun j => Theorem14.GW3Word.flowLineXR_nonneg _ _ j)
    hxL hxR h0
  set S : Set ℝ := forceJumpSet (cfMarkL (16 / κ) b'' J'' w q) (cfMarkR (16 / κ) b'' J'' w q) ∪
    forceJumpSet (fun i => -rightImg (fun s => -w s) (-xL i) q - w q) (fun j => rightImg w (xR j) q - w q) ∪
    (T : Set ℝ) with hS
  have hSf : S.Finite := by
    refine ((Set.Finite.union ?_ ?_).union T.finite_toSet)
    · rw [← coe_forceJumpFinset]; exact Finset.finite_toSet _
    · rw [← coe_forceJumpFinset]; exact Finset.finite_toSet _
  have hu' : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -w s) (-xL i) q - w q)
        (fun j => rightImg w (xR j) q - w q)) S u :=
    ⟨hu.1, hu.2.1, fun x hx => hu.2.2 x fun h => hx (Or.inl (Or.inr h))⟩
  have hv' : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -w s) (-xL i) q - w q)
        (fun j => rightImg w (xR j) q - w q)) S v := by
    refine ⟨hv.1, hv.2.1, fun x hx => ?_⟩
    have h1 := hv.2.2 x fun h => hx (Or.inl (Or.inl h))
    have h2 := hT x fun h => hx (Or.inr h)
    have e : cfDataAt (16 / κ) b'' J'' w q x =
        forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -w s) (-xL i) q - w q)
          (fun j => rightImg w (xR j) q - w q) x := by
      simp only [cfDataAt]
      rw [h2, hkk]
    rw [← e]
    exact h1
  exact PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension hSf hu' hv'

end InteractingSLE.Sec5.Lemma47Angle
