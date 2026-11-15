/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfFinite
import InteractingSLE.Spec.Supplement.GW3Word

/-!
# Lemma 4.7 in the chart `Q`: the flow-slit data of the counterflow restart are the flow line's own data

Packet PROVE-CFRESTART3. In Lemma 4.7's direction on the glued space of `Prop411Q.CfGlueAE` (chart `Q`), the obstacle
of PROVE-CFRESTART2's `IsCfImgSetup` is the flow slit `R(K_q)`, and the hypothesis `hv` of
`IsCfImgSetup.exists_finite_tendsto_imgChart_restart` asks for a bounded harmonic extension of the flow-slit data
`cfDataAt (16/κ) (bDataT ρ′ … (−θ) (16/κ)) J′ W q`, written through the counterflow word `ρ′` of the chart-`Q` data
`b = forceBoundaryData κ ρL ρR xL xR − π/2 χ` (`GlueImg.bData`). With the relative angle `θ = π/2` these are the flow
line's data at time `q`:

* `exists_finset_forceBoundaryData_flow_eq`: two force words whose data agree off a finite set at time `0` still
  agree off a finite set after the real Loewner flow of any continuous driver (PROVE-CFRESTART-C's
  `forceBoundaryData_flow_*` transport on both sides of the driver);
* `counterflowData_bDataT_cfWord`: the word round trip at time `0` — dualizing the counterflow word of `b` back at
  parameter `16/κ` with relative angle `−π/2` gives `b + π/2 χ` (`returnData_inverseData`'s bookkeeping, with
  `χ(16/κ) = −χ(κ)` and `ℓ(x) + ℓ(−1/x) = −2π`);
* **`eqOn_bhe_cfDataAt_flow`**: every bounded harmonic extension of the flow-slit data at `q` is the flow line's
  bounded harmonic extension `u_q` at `q` (uniqueness off a finite set,
  `PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension`).

Deterministic; no named input. R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open MartChar.RealFlow Restart.RetAux79

/-- **Data agreement survives the real Loewner flow**: if two force words with left marks `≤ 0` and right marks
`≥ 0` have the same data off a finite set at time `0`, their data flowed by a continuous driver `w` to time `t`
agree off a finite set. -/
theorem exists_finset_forceBoundaryData_flow_eq {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) (κ : ℝ)
    {nL nR mL mR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (σL : Fin mL → ℝ) (σR : Fin mR → ℝ)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {yL : Fin mL → ℝ} {yR : Fin mR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hyL : ∀ i, yL i ≤ 0) (hyR : ∀ j, 0 ≤ yR j)
    {T₀ : Finset ℝ} (h0 : ∀ x ∉ T₀, forceBoundaryData κ ρL ρR xL xR x = forceBoundaryData κ σL σR yL yR x) :
    ∃ T : Finset ℝ, ∀ y ∉ T,
      forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -w s) (-xL i) t - w t)
          (fun j => rightImg w (xR j) t - w t) y =
        forceBoundaryData κ σL σR (fun i => -rightImg (fun s => -w s) (-yL i) t - w t)
          (fun j => rightImg w (yR j) t - w t) y := by
  classical
  set gR : ℝ → ℝ := fun x => gImg w x t - w t with hgR
  set gL : ℝ → ℝ := fun x => -gImg (fun s => -w s) x t - w t with hgL
  set SR : Finset ℝ := T₀ ∪ Finset.univ.image xR ∪ Finset.univ.image yR with hSR
  set SL : Finset ℝ := T₀.image (fun x => -x) ∪ Finset.univ.image (fun i => -xL i) ∪
    Finset.univ.image (fun i => -yL i) with hSL
  set aL : ℝ := -rightImg (fun s => -w s) 0 t - w t with haL
  set aR : ℝ := rightImg w 0 t - w t with haR
  refine ⟨{aL, aR} ∪ SR.image gR ∪ SL.image gL ∪
    Finset.univ.image (fun i => -rightImg (fun s => -w s) (-xL i) t - w t) ∪
    Finset.univ.image (fun i => -rightImg (fun s => -w s) (-yL i) t - w t), fun y hy => ?_⟩
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ,
    true_and, not_or] at hy
  obtain ⟨⟨⟨⟨⟨hyaL, hyaR⟩, hySR⟩, hySL⟩, hyxL⟩, hyyL⟩ := hy
  rcases le_or_gt 0 y with hy0 | hy0
  · rcases lt_or_gt_of_ne hyaR with hlt | hgt
    · rw [forceBoundaryData_flow_slit_right ρL ρR hw ht hxR hy0 hlt,
        forceBoundaryData_flow_slit_right σL σR hw ht hyR hy0 hlt]
    · obtain ⟨x, hx0, hxa, hxg⟩ := exists_alive_gImg_eq hw ht (M := y + w t) (by rw [haR] at hgt; linarith)
      have hye : y = gImg w x t - w t := by rw [hxg]; ring
      have hxS : x ∉ SR := fun hx => hySR ⟨x, hx, by rw [hgR]; exact hye.symm⟩
      simp only [hSR, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or] at hxS
      obtain ⟨⟨hxT, hxR'⟩, hyR'⟩ := hxS
      rw [hye, forceBoundaryData_flow_right ρL ρR hw ht hx0 hxa (fun j h => hxR' ⟨j, h⟩),
        forceBoundaryData_flow_right σL σR hw ht hx0 hxa (fun j h => hyR' ⟨j, h⟩)]
      exact h0 x hxT
  · rcases lt_or_gt_of_ne hyaL with hlt | hgt
    · obtain ⟨x, hx0, hxa, hxg⟩ := exists_alive_gImg_eq (show Continuous fun s => -w s from hw.neg) ht (M := -y - w t)
        (by rw [haL] at hlt; linarith)
      have hye : y = -gImg (fun s => -w s) x t - w t := by rw [hxg]; ring
      have hxS : x ∉ SL := fun hx => hySL ⟨x, hx, by rw [hgL]; exact hye.symm⟩
      simp only [hSL, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or] at hxS
      obtain ⟨⟨hxT, hxL'⟩, hyL'⟩ := hxS
      have hxT' : -x ∉ T₀ := fun h => hxT ⟨-x, h, neg_neg x⟩
      rw [hye, forceBoundaryData_flow_left ρL ρR hw ht hx0 hxa (fun i h => hxL' ⟨i, h⟩)
          (fun i h => hyxL ⟨i, by rw [hye]; exact h.symm⟩),
        forceBoundaryData_flow_left σL σR hw ht hx0 hxa (fun i h => hyL' ⟨i, h⟩)
          (fun i h => hyyL ⟨i, by rw [hye]; exact h.symm⟩)]
      exact h0 (-x) hxT'
    · rw [forceBoundaryData_flow_slit_left ρL ρR hw ht hxL hy0 hgt,
        forceBoundaryData_flow_slit_left σL σR hw ht hyL hy0 hgt]


open Sec7.StripSysField GlueCond Cond44Ref CrossCond.Theta GlueImg

/-- **The word round trip at time `0`**: dualizing the counterflow word of `b` back (relative angle `−π/2`) gives
`b + π/2 χ`. -/
theorem counterflowData_bDataT_cfWord {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {x : ℝ} (hx : x ∉ returnExcept (counterflowJumps J)) :
    counterflowData (16 / κ) (bDataT (cfRhoL κ b J) (cfRhoR κ b J)
      (flowLineXL (counterflowData κ b) (counterflowJumps J) 0)
      (flowLineXR (counterflowData κ b) (counterflowJumps J) 0) (-(Real.pi / 2)) (16 / κ)) x =
      b x + Real.pi / 2 * QuantumZipper.chiC κ := by
  have hk : 0 < 16 / κ := by positivity
  have hx0 : x ≠ 0 := ne_zero_of_notMem_returnExcept hx
  have hyJ : -x⁻¹ ∉ counterflowJumps J := negInv_notMem_of_notMem_returnExcept hx
  have hy0 : -x⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hx0)
  have e1 := Sec4.forceBoundaryData_flowLine hk (isPiecewiseConstant_counterflowData κ hb) hy0 hyJ
  have hl := liftBoundary_add_liftBoundary_negInv hx0
  have hc := Sec4.chiC_sixteen_div hκ
  have hkk : (16 : ℝ) / (16 / κ) = κ := by field_simp
  simp only [counterflowData, inverseData, returnData, cfOffset, cfCoeff, hkk, bDataT, cfRhoL, cfRhoR,
    inv_neg, inv_inv, neg_neg] at e1 ⊢
  rw [e1, hc]
  linear_combination (-(QuantumZipper.chiC κ)) * hl


/-- **The flow-slit data are the flow line's data** (relative angle `π/2`): a bounded harmonic extension `v` of
`cfDataAt (16/κ) (bDataT ρ′ … (−π/2) (16/κ)) J′ w q` (the obstacle data of `exists_finite_tendsto_imgChart_restart`,
`ρ′` the counterflow word of `bData ρL ρR xL xR κ`) is, on `ℍ`, the bounded harmonic extension of the flow word
`ρL ρR xL xR` flowed by `w` to time `q`. -/
theorem eqOn_bhe_cfDataAt_flow {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {w : ℝ → ℝ} (hw : Continuous w) {q : ℝ} (hq : 0 ≤ q) {v u : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension
      (cfDataAt (16 / κ) (bDataT (cfRhoL κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR))
        (cfRhoR κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR))
        (flowLineXL (counterflowData κ (bData ρL ρR xL xR κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
        (flowLineXR (counterflowData κ (bData ρL ρR xL xR κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
        (-(Real.pi / 2)) (16 / κ))
        (forceJumpFinset
          (flowLineXL (counterflowData κ (bData ρL ρR xL xR κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
          (flowLineXR (counterflowData κ (bData ρL ρR xL xR κ)) (counterflowJumps (forceJumpFinset xL xR)) 0))
        w q)
      (forceJumpSet
        (cfMarkL (16 / κ) (bDataT (cfRhoL κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR))
          (cfRhoR κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR))
          (flowLineXL (counterflowData κ (bData ρL ρR xL xR κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
          (flowLineXR (counterflowData κ (bData ρL ρR xL xR κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
          (-(Real.pi / 2)) (16 / κ))
          (forceJumpFinset
            (flowLineXL (counterflowData κ (bData ρL ρR xL xR κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
            (flowLineXR (counterflowData κ (bData ρL ρR xL xR κ)) (counterflowJumps (forceJumpFinset xL xR)) 0))
          w q)
        (cfMarkR (16 / κ) (bDataT (cfRhoL κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR))
          (cfRhoR κ (bData ρL ρR xL xR κ) (forceJumpFinset xL xR))
          (flowLineXL (counterflowData κ (bData ρL ρR xL xR κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
          (flowLineXR (counterflowData κ (bData ρL ρR xL xR κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
          (-(Real.pi / 2)) (16 / κ))
          (forceJumpFinset
            (flowLineXL (counterflowData κ (bData ρL ρR xL xR κ)) (counterflowJumps (forceJumpFinset xL xR)) 0)
            (flowLineXR (counterflowData κ (bData ρL ρR xL xR κ)) (counterflowJumps (forceJumpFinset xL xR)) 0))
          w q)) v)
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -w s) (-xL i) q - w q)
        (fun j => rightImg w (xR j) q - w q))
      (forceJumpSet (fun i => -rightImg (fun s => -w s) (-xL i) q - w q) (fun j => rightImg w (xR j) q - w q)) u) :
    EqOn v u H := by
  classical
  set b := bData ρL ρR xL xR κ with hbdef
  set J := forceJumpFinset xL xR with hJ
  set b'' := bDataT (cfRhoL κ b J) (cfRhoR κ b J) (flowLineXL (counterflowData κ b) (counterflowJumps J) 0)
    (flowLineXR (counterflowData κ b) (counterflowJumps J) 0) (-(Real.pi / 2)) (16 / κ) with hb''def
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
      counterflowData_bDataT_cfWord hκ hb hx.2, hkk]
    simp only [hbdef, bData]
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

end InteractingSLE.Sec5.CrossRestart.KernelQ
