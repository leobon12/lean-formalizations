import QuantumZipper.Proofs.Zipper.Cor15ZipCoordTools
import QuantumZipper.Proofs.Zipper.JointModFinal
import QuantumZipper.Proofs.Zipper.Cor15RegBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-ZIPCOORD (2): the zip coordinate reading `Cor15ZipCoordReadStmt`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 and §1.4
(the zipped configuration is described modulo additive constants). Task COR15-ZIPCOORD,
decision D42. Own assembly of proved repository results, following `cor15ZipRead`
(`Cor15ZipRead.lean`) and `zipFld_apply_eq_CInv` (`Cor15MeasVerCInv.lean`).

* `zipFld_fc_eq_CInv_add` (deterministic): on the good set, the zipped field at the `i`-th dyadic
  folded circle is `CInv` read from the B1-FULL data `b1Data x` (normalized coordinates) **plus
  the removed constant** `x.1 (fc 0 1)`: `U_a` commutes with the constant because `x.1` is
  literally `addConst (nrm x.1) c` and `coordChange_apply_of_shift` applies under `CCGoodAt`.
* The good set `A` is the intersection of the reading set of `exists_readVp`, the circle-null hull
  set, the countable certificates `GoodMeas.C1` of the normalized input and of the `CInv`
  candidate (these make the uncountable raw-convergence clause `∀ z` measurable), and `CCGoodAt`
  at every dyadic folded circle.
* `cor15ZipCoordRead`: `Cor15ZipCoordReadStmt` for every genuine setup, from Theorem 1.3 and the
  one remaining analytic input `Cor15ZipPushGoodStmt` (convergence form of the proved input (R)
  `cor15RezipRegStmt`). `theorem1_5_of_theorem1_3_of_zipCoord` is the resulting headline.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CoordsFull GoodMeas B1Full

/-! ## The remaining analytic input -/

/-- **Remaining input (convergence form of (R)).** A.s. the unzipped field `D_a c` is `CCGoodAt`
for the rezipping map `revMapInv (vrev W a) a` at every dyadic folded circle: the regularizing
integrals `∫ avgReg (D_a c) j d(f_* σ_i)` are integrable and converge as `j → ∞`. This is what the
proof of the proved (R) `cor15RezipRegStmt` establishes before identifying the limit
(`CoordReg.ae_evalReg_coordChange_revMap_gen`, `hlim`; Duplantier–Sheffield, *Liouville quantum
gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1); only the identity of the limit is
exported there. -/
def Cor15ZipPushGoodStmt {Ω : Type} [MeasurableSpace Ω] (κ a : ℝ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ i : ℕ, ∀ᵐ ω ∂P, CCGoodAt (unzippedField (Real.sqrt κ) (grpCfg κ B X ω) a)
    (revMapInv (B2.vrev (drive κ B ω) a) a) (foldedCircle (fullIndex i).1 (fullIndex i).2)

/-! ## The pathwise identity -/

/-- **The zipped field at a dyadic folded circle is read from `b1Data x` up to the removed
constant.** -/
theorem zipFld_fc_eq_CInv_add {κ a : ℝ} (ha : 0 < a) {Vp : B1E → ℝ → ℝ}
    (hVc : ∀ b, Continuous (Vp b)) (hV0 : ∀ b, Vp b 0 = 0) {x : FieldSample × (ℝ → ℝ)}
    (hread : EqOn (weldDriver (Real.sqrt κ) x.1 a) (Vp (b1Data x)) (Icc 0 a))
    (hnull : ∀ i, foldedCircle (fullIndex i).1 (fullIndex i).2
      (fwdHull (ArcDriver.trev (Vp (b1Data x)) a) a) = 0)
    (hC1 : C1 (E1.fromC (b1Data x).1.1))
    (hG : ∀ i, CCGoodAt (E1.fromC (b1Data x).1.1) (revMapInv (Vp (b1Data x)) a)
      (foldedCircle (fullIndex i).1 (fullIndex i).2)) (i : ℕ) :
    zipFld κ a x (foldedCircle (fullIndex i).1 (fullIndex i).2) =
      CInv Vp a (Qc (Real.sqrt κ)) (foldedCircle (fullIndex i).1 (fullIndex i).2)
        ((b1Data x).1.1, b1Data x) + x.1 (foldedCircle 0 1) := by
  set b := b1Data x with hbd
  set c0 := x.1 (foldedCircle 0 1) with hc0
  have hcf : coordsFull (E1.fromC b.1.1) = coordsFull (nrm x.1) :=
    E1.coordsFull_fromC (nrm x.1)
  have hxn : addConst (nrm x.1) c0 = x.1 := by
    funext μ
    simp only [addConst, nrm, hc0]
    ring
  have hraw := rawConv_of_C1 (C1_of_coordsFull_eq_add (x := E1.fromC b.1.1) (y := nrm x.1)
    (c := 0) (fun i => by rw [add_zero, hcf]) hC1)
  have hshift : ∀ j w, avgReg x.1 j w = avgReg (E1.fromC b.1.1) j w + c0 := by
    intro j w
    rw [avgReg_congr_full hcf]
    calc avgReg x.1 j w = avgReg (addConst (nrm x.1) c0) j w := by rw [hxn]
      _ = avgReg (nrm x.1) j w + c0 := LocalRule.avgReg_addConst_of_tendsto (hraw j w) c0
  have hψ : revMapInv (weldDriver (Real.sqrt κ) x.1 a) a = revMapInv (Vp b) a :=
    revMapInv_congr_H fun z _ => ReverseFlow.revMap_congr_drive z hread
  show coordChange x.1 (revMapInv (weldDriver (Real.sqrt κ) x.1 a) a) (Qc (Real.sqrt κ))
    (foldedCircle (fullIndex i).1 (fullIndex i).2) = _
  rw [hψ, coordChange_apply_of_shift hshift (hG i),
    coordChange_revMapInv_eq_CInv_fc hVc hV0 ha _ (E1.fromC b.1.1) b i (hnull i), hcf]
  rfl

/-- The `CInv` coordinates only depend on the enumerated circle. -/
theorem CInv_consistent {Vp : B1E → ℝ → ℝ} (a Q : ℝ) (b : B1E) (i j : ℕ)
    (h : foldedCircle (fullIndex i).1 (fullIndex i).2 =
      foldedCircle (fullIndex j).1 (fullIndex j).2) :
    CInv Vp a Q (foldedCircle (fullIndex i).1 (fullIndex i).2) (b.1.1, b) =
      CInv Vp a Q (foldedCircle (fullIndex j).1 (fullIndex j).2) (b.1.1, b) := by
  rw [h]

/-! ## The reading -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **COR15-ZIPCOORD: `Cor15ZipCoordReadStmt`** for every genuine setup, from Theorem 1.3 and
the convergence form `Cor15ZipPushGoodStmt` of input (R). -/
theorem cor15ZipCoordRead (h13 : theorem1_3) {κ a : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hS : IsGrpSetup P B X) (ha : 0 < a) (hP : Cor15ZipPushGoodStmt κ a P B X) :
    Cor15ZipCoordReadStmt κ a P B X := by
  classical
  have ⟨hB, hX, hind⟩ := hS
  obtain ⟨Vp, hVc, hV0, hVm, A0, hA0m, hdet, hyA, -⟩ :=
    exists_readVp h13 RS.rohdeSchrammSimple hκ hκ4 hB hX hind ha
  set Q := Qc (Real.sqrt κ) with hQ
  set Gv : B1E → ℕ → ℝ := fun b i =>
    CInv Vp a Q (foldedCircle (fullIndex i).1 (fullIndex i).2) (b.1.1, b) with hGv
  have hGm : ∀ i, Measurable fun b => Gv b i := fun i =>
    (measurable_CInv hVc hV0 hVm ha Q _).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_id)
  have hGvm : Measurable Gv := measurable_pi_iff.2 hGm
  have hcons : ∀ b : B1E, coordsFull (E1.fromC (Gv b)) = Gv b := fun b =>
    coordsFull_fromC_of_consistent fun i j h => CInv_consistent a Q b i j h
  have hfC : Measurable fun b : B1E => E1.fromC b.1.1 :=
    measurable_fromC.comp (measurable_fst.comp measurable_fst)
  set N : Set B1E := ⋂ i : ℕ, {b | foldedCircle (fullIndex i).1 (fullIndex i).2
    (fwdHull (ArcDriver.trev (Vp b) a) a) = 0} with hN
  set U1 : Set B1E := {b | C1 (E1.fromC b.1.1)} with hU1
  set U2 : Set B1E := {b | C1 (E1.fromC (Gv b))} with hU2
  set S : Set B1E := ⋂ i : ℕ, {b | CCGoodAt (E1.fromC b.1.1) (revMapInv (Vp b) a)
    (foldedCircle (fullIndex i).1 (fullIndex i).2)} with hSd
  have hNm : MeasurableSet N :=
    MeasurableSet.iInter fun i => measurableSet_hullNull_meas hVc hVm ha.le _
  have hC1m : MeasurableSet {x : FieldSample | C1 x} := measurableSet_setOfPred.2 measurable_C1
  have hU1m : MeasurableSet U1 := hC1m.preimage hfC
  have hU2m : MeasurableSet U2 := hC1m.preimage (measurable_fromC.comp hGvm)
  have hSm : MeasurableSet S :=
    MeasurableSet.iInter fun i => measurableSet_ccGoodAt hVc hV0 hVm ha hfC _
  refine ⟨fun b => (fun i => (Gv b i - ∫ z, h0rev κ z ∂foldedCircle (fullIndex i).1
        (fullIndex i).2) - (Gv b 0 - ∫ z, h0rev κ z ∂foldedCircle (fullIndex 0).1
        (fullIndex 0).2),
      fun u : ℝ≥0 => (Real.sqrt κ)⁻¹ * (if (u : ℝ) ≤ a then Vp b (a - u) - Vp b a
        else b.2 ((u : ℝ) - a).toNNReal - Vp b a)),
    A0 ∩ N ∩ U1 ∩ U2 ∩ S, ?_, (((hA0m.inter hNm).inter hU1m).inter hU2m).inter hSm, ?_, ?_⟩
  · refine Measurable.prodMk (measurable_pi_iff.2 fun i =>
      ((hGm i).sub measurable_const).sub ((hGm 0).sub measurable_const))
      (measurable_pi_iff.2 fun u => ?_)
    by_cases hu : (u : ℝ) ≤ a
    · simp only [hu, ↓reduceIte]
      exact measurable_const.mul ((hVm _).sub (hVm _))
    · simp only [hu, ↓reduceIte]
      exact measurable_const.mul
        (((measurable_pi_apply _).comp measurable_snd).sub (hVm _))
  · intro x hx
    obtain ⟨⟨⟨⟨hxA0, hxN⟩, hxU1⟩, hxU2⟩, hxS⟩ := hx
    have hread := (hdet x hxA0).1
    have hkey : ∀ i, zipFld κ a x (foldedCircle (fullIndex i).1 (fullIndex i).2) =
        Gv (b1Data x) i + x.1 (foldedCircle 0 1) := fun i =>
      zipFld_fc_eq_CInv_add ha hVc hV0 hread (fun i => mem_iInter.1 hxN i) hxU1
        (fun i => mem_iInter.1 hxS i) i
    refine ⟨Prod.ext ?_ ?_, fun k z => ?_⟩
    · funext i
      show (zipFld κ a x (foldedCircle (fullIndex i).1 (fullIndex i).2) -
          ∫ z, h0rev κ z ∂foldedCircle (fullIndex i).1 (fullIndex i).2) -
        (zipFld κ a x (foldedCircle (fullIndex 0).1 (fullIndex 0).2) -
          ∫ z, h0rev κ z ∂foldedCircle (fullIndex 0).1 (fullIndex 0).2) = _
      rw [hkey i, hkey 0]
      ring
    · funext u
      show (Real.sqrt κ)⁻¹ * (zipCapUp (Real.sqrt κ) a x).2 (u : ℝ) = _
      congr 1
      simp only [zipCapUp]
      have hu0 : (0 : ℝ) ≤ u := u.2
      by_cases hu : (u : ℝ) ≤ a
      · simp only [hu, ↓reduceIte, max_eq_left hu0]
        rw [hread ⟨by linarith, by linarith⟩, hread ⟨ha.le, le_rfl⟩]
      · simp only [hu, ↓reduceIte]
        rw [hread ⟨ha.le, le_rfl⟩]
        show x.2 ((u : ℝ) - a) - _ = x.2 ((((u : ℝ) - a).toNNReal : ℝ≥0) : ℝ) - _
        rw [Real.coe_toNNReal _ (by linarith [not_le.mp hu])]
    · have hc : ∀ i, coordsFull (zipFld κ a x) i =
          coordsFull (E1.fromC (Gv (b1Data x))) i + x.1 (foldedCircle 0 1) := by
        intro i
        rw [hcons]
        exact hkey i
      exact rawConv_of_C1 (C1_of_coordsFull_eq_add hc hxU2) k z
  · have hK0 : ∀ᵐ ω ∂P, ∀ i : ℕ, foldedCircle (fullIndex i).1 (fullIndex i).2
        (revHull (B2.vrev (drive κ B ω) a) a) = 0 :=
      ae_all_iff.2 fun i => cor15HullNullStmt κ hκ hκ4 a ha P B hB i
    have hX0 : ∀ᵐ ω ∂P, IsRegularSample (ofFun (h0rev κ) + X ω) := by
      filter_upwards [RegSample.ae_isRegularSample hX] with ω hreg
      rw [AtomlessUncond.gamma0_decomp κ (X ω)]
      exact ((hreg.addConst' _).add_ofFun_log' (-2 / Real.sqrt κ) 0).add_ofFun'
        continuousOn_const
    filter_upwards [hyA, hK0, hB.cont, hB.eval_zero_ae_eq_zero,
      RegUnif.ae_forall_isRegularSample (γ := Real.sqrt κ) hB hX hind, ae_all_iff.2 hP, hX0,
      ae_coordsFull_zipFld_zipCapDown h13 hκ hκ4 hS ha]
      with ω ⟨hA, hE⟩ hK hc h0 hrg hpg hx0 hzc
    set y := zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω) with hy
    set W := drive κ B ω with hWd
    have hWc : Continuous W := drive_continuous hc
    have hW0 : W 0 = 0 := drive_zero h0
    have hvc : Continuous (B2.vrev W a) := by unfold B2.vrev; fun_prop
    have hNy : ∀ i, foldedCircle (fullIndex i).1 (fullIndex i).2
        (fwdHull (ArcDriver.trev (Vp (b1Data y)) a) a) = 0 := by
      intro i
      rw [fwdHull_trev_eq_of_eqOn (hVc _) hvc ha.le hE,
        CharFunRhs.fwdHull_eq_of_eqOn (ArcDriver.continuous_trev hvc a) hWc ha.le
          (trev_vrev_eqOn hW0 ha.le), ← revHull_vrev_eq_fwdHull hWc hW0 ha]
      exact hK i
    obtain ⟨F, hF⟩ := (hrg a ha.le).1
    have hyC1 : C1 y.1 := C1_of_regular hF
    have hyraw := rawConv_of_C1 hyC1
    have hcf : coordsFull (E1.fromC (b1Data y).1.1) = coordsFull (nrm y.1) :=
      E1.coordsFull_fromC (nrm y.1)
    have hU1y : C1 (E1.fromC (b1Data y).1.1) := by
      refine C1_of_coordsFull_eq_add (x := y.1) (c := -(y.1 (foldedCircle 0 1))) (fun i => ?_)
        hyC1
      rw [hcf]
      simp [coordsFull, nrm, addConst, measure_univ]
    have hψ : revMapInv (Vp (b1Data y)) a = revMapInv (B2.vrev W a) a :=
      revMapInv_congr_H fun z _ => ReverseFlow.revMap_congr_drive z hE
    have hSy : ∀ i, CCGoodAt (E1.fromC (b1Data y).1.1) (revMapInv (Vp (b1Data y)) a)
        (foldedCircle (fullIndex i).1 (fullIndex i).2) := by
      intro i
      rw [hψ]
      refine ccGoodAt_of_avgReg_shift (y := y.1) (c := -(y.1 (foldedCircle 0 1)))
        (fun j w => ?_) (hpg i)
      rw [avgReg_congr_full hcf]
      exact LocalRule.avgReg_addConst_of_tendsto (hyraw j w) _
    have hkey : ∀ i, zipFld κ a y (foldedCircle (fullIndex i).1 (fullIndex i).2) =
        Gv (b1Data y) i + y.1 (foldedCircle 0 1) := fun i =>
      zipFld_fc_eq_CInv_add ha hVc hV0 (hdet y hA).1 hNy hU1y hSy i
    have hU2y : C1 (E1.fromC (Gv (b1Data y))) := by
      obtain ⟨F0, hF0⟩ := hx0
      refine C1_of_coordsFull_eq_add (x := ofFun (h0rev κ) + X ω)
        (c := -(y.1 (foldedCircle 0 1))) (fun i => ?_) (C1_of_regular hF0)
      rw [hcons]
      have h1 := hkey i
      have h2 := congrFun hzc i
      simp only [coordsFull] at h2 ⊢
      rw [← h2, h1]
      ring
    exact ⟨⟨⟨⟨hA, mem_iInter.2 hNy⟩, hU1y⟩, hU2y⟩, mem_iInter.2 hSy⟩

end Cor15Group
end QuantumZipper
