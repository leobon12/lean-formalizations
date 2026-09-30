import QuantumZipper.Proofs.Thm18.ASepGCUfam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-GC, part 6: the Borel exactness input `GCExStmt` holds

The two exactness identities of `G4SepConcl0` at `(τ, a, i)` are rewritten through the code
families: the re-zipping map `ψ = psiInv (kcode κ c, τ, a)` (`GC.revMapInv_backDrv_eq_psiInv`),
the unzipped field `Ufam γ (v, (c, τ))` (equal to `unzippedField` on every measure carried by
`ℍ`, `GC.unzippedField_eq_Ufam`; its regularized averages, hence `evalReg` and `rescale`, agree
everywhere). Under `BackSepI` the pushed circle `σ_i.map (a ψ)` is carried by `ℍ`
(`map_mul_revMapInv_compl_H`). Each side is a measurable function of
`(path code, circle coordinates, τ, a)` (`ASepGCUfam`), so the set `gcX γ` is Borel.

* **`gcExStmt_holds : GCExStmt`**;
* **`goodCMeasStmt_of_sep : GCSepStmt → GoodCMeasStmt`**.

Own bookkeeping (measurability the paper leaves implicit).
-/

noncomputable section

open MeasureTheory Set Function Filter
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace ASep
namespace GC

open Thm18Asm Thm18Asm.G4Core

/-- Parameters `((c, v), (τ, a))`. -/
abbrev PX : Type := ((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℝ)

/-- The code field parameter. -/
def gU (r : PX) : (ℕ → ℝ) × ((ℕ → ℝ) × ℝ) := (r.1.2, (r.1.1, r.2.1))

theorem measurable_gU : Measurable gU :=
  measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd.fst)

/-- The code re-zipping map. -/
def ψc (κ : ℝ) (r : PX) (w : ℂ) : ℂ := psiInv (kcode κ r.1.1, r.2.1, r.2.2) w

theorem measurable_ψc (κ : ℝ) : Measurable fun q : PX × ℂ => ψc κ q.1 q.2 :=
  Measurable.comp (g := fun s : ((ℕ → ℝ) × ℝ × ℝ) × ℂ => psiInv (kcode κ s.1.1, s.1.2) s.2)
    (f := fun q : PX × ℂ => ((q.1.1.1, (q.1.2.1, q.1.2.2)), q.2)) (measurable_psiInv_code κ)
    ((measurable_fst.fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_fst.snd.snd)).prodMk
      measurable_snd)

theorem measurable_aψc (κ : ℝ) :
    Measurable fun q : PX × ℂ => ((q.1.2.2 : ℝ) : ℂ) * ψc κ q.1 q.2 :=
  (Complex.measurable_ofReal.comp measurable_fst.snd.snd).mul (measurable_ψc κ)

/-- The exactness set at the circle `i`. -/
def gcXS (γ : ℝ) (i : ℕ) : Set PX :=
  {r | evalReg (rescale (Ufam γ (gU r)) (Qc γ) r.2.2) ((fcI i).map (ψc (γ ^ 2) r)) =
      rescale (Ufam γ (gU r)) (Qc γ) r.2.2 ((fcI i).map (ψc (γ ^ 2) r))} ∩
  {r | evalReg (Ufam γ (gU r)) ((fcI i).map fun w => (r.2.2 : ℂ) * ψc (γ ^ 2) r w) =
      Ufam γ (gU r) ((fcI i).map fun w => (r.2.2 : ℂ) * ψc (γ ^ 2) r w)}

theorem measurableSet_gcXS (γ : ℝ) (i : ℕ) : MeasurableSet (gcXS γ i) := by
  have hga : Measurable fun r : PX => r.2.2 := measurable_snd.snd
  refine (measurableSet_eq_fun ?_ ?_).inter (measurableSet_eq_fun ?_ ?_)
  · exact measurable_evalReg_rescaleUfam γ gU measurable_gU (fun r => r.2.2) hga (fcI i)
      (ψc (γ ^ 2)) (measurable_ψc _)
  · exact measurable_rescaleUfam_map γ gU measurable_gU (fun r => r.2.2) hga (fcI i)
      (ψc (γ ^ 2)) (measurable_ψc _)
  · exact measurable_evalReg_Ufam γ gU measurable_gU (fcI i)
      (fun r w => (r.2.2 : ℂ) * ψc (γ ^ 2) r w) (measurable_aψc _)
  · exact measurable_Ufam_map γ gU measurable_gU (fcI i)
      (fun r w => (r.2.2 : ℂ) * ψc (γ ^ 2) r w) (measurable_aψc _)

/-- The Borel exactness set. -/
def gcX (γ : ℝ) : Set (((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℝ × ℕ)) :=
  {s | (s.1, (s.2.1, s.2.2.1)) ∈ gcXS γ s.2.2.2}

theorem measurableSet_gcX (γ : ℝ) : MeasurableSet (gcX γ) := by
  have e : gcX γ = ⋃ i : ℕ, {s : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℝ × ℕ) | s.2.2.2 = i} ∩
      (fun s : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℝ × ℝ × ℕ) => (s.1, (s.2.1, s.2.2.1))) ⁻¹' gcXS γ i := by
    ext s
    simp only [gcX, mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_preimage]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨i, hi, h⟩ => hi ▸ h⟩
  rw [e]
  refine MeasurableSet.iUnion fun i => MeasurableSet.inter ?_ ?_
  · exact measurableSet_eq_fun measurable_snd.snd.snd measurable_const
  · exact (measurableSet_gcXS γ i).preimage
      (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst))

/-! ## Identification with the exactness identities -/

theorem isOpen_H'' : MeasurableSet H :=
  (isOpen_lt continuous_const Complex.continuous_im).measurableSet

/-- Under `BackSepI`, the pushed circle `σ_i.map (a ψ)` is carried by `ℍ`. -/
theorem map_mul_revMapInv_compl_H {W : ℝ → ℝ} (hW : Continuous W) {τ a : ℝ} (hτ : 0 < τ)
    (ha : 0 < a) {i : ℕ} {y : FieldSample} (hsep : BackSepI (y, W) τ 0 a i)
    (hm : Measurable fun w => (a : ℂ) * revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w) :
    ((fcI i).map fun w => (a : ℂ) * revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w) Hᶜ =
      0 := by
  obtain ⟨δ, hδ, h0⟩ := hsep
  have hK : fcI i (revHull (backDrv W τ 0 a).2 (backDrv W τ 0 a).1) = 0 :=
    measure_mono_null (Metric.self_subset_thickening hδ _) h0
  have hHc : fcI i Hᶜ = 0 :=
    ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ (UnzipFull.fullIndex_radius_pos i))
  rw [Measure.map_apply hm isOpen_H''.compl]
  refine measure_mono_null (fun w hw => ?_) (measure_union_null hHc hK)
  by_contra hc
  simp only [mem_union, mem_compl_iff, not_or, not_not] at hc
  obtain ⟨hwH, hwK⟩ := hc
  have hV : Continuous (backDrv W τ 0 a).2 := by
    simp only [backDrv]; fun_prop
  have hT : 0 ≤ (backDrv W τ 0 a).1 := by
    simp only [backDrv]; exact div_nonneg (by linarith) (sq_nonneg a)
  have hwI : w ∈ revMap (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 '' H := by
    by_contra h; exact hwK ⟨hwH, h⟩
  obtain ⟨z, hz, hzw⟩ := hwI
  have hψ : revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w = z := by
    rw [revMapInv_eq_invOn]
    exact invOn_eq_of_mem (injOn_revMap _ hV hT) hz hzw
  apply hw
  show 0 < ((a : ℂ) * revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w).im
  rw [hψ]
  have : 0 < z.im := hz
  simpa using mul_pos ha this

/-- **The Borel exactness input holds.** -/
theorem gcExStmt_holds : GCExStmt := by
  intro γ _ _
  refine ⟨gcX γ, measurableSet_gcX γ, ?_⟩
  intro x hx y τ a hτ ha i hsep
  set W := pathDrive (γ ^ 2) x with hWdef
  have hW : Continuous W := continuous_const.mul (hx.comp continuous_real_toNNReal)
  set U := unzippedField γ (y, W) τ with hUdef
  set Uf := Ufam γ (CoordsFull.coordsFull y, (codeP x, τ)) with hUfdef
  have hψ := revMapInv_backDrv_eq_psiInv (γ ^ 2) hx hτ.le ha
  have hψm : Measurable (psiInv (kcode (γ ^ 2) (codeP x), τ, a)) :=
    Measurable.comp (g := fun q : PX × ℂ => ψc (γ ^ 2) q.1 q.2)
      (f := fun w : ℂ => ((((codeP x, CoordsFull.coordsFull y), (τ, a)) : PX), w))
      (measurable_ψc _) (measurable_const.prodMk measurable_id)
  have havg : avgReg U = avgReg Uf := by
    funext k z
    unfold avgReg
    congr 1
    funext n
    exact unzippedField_eq_Ufam γ hx y hτ.le
      (ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ (by unfold radius; positivity)))
  have hev : evalReg U = evalReg Uf := by
    funext ν; unfold evalReg; rw [havg]
  have hres : rescale U (Qc γ) a = rescale Uf (Qc γ) a := by
    funext μ; simp only [rescale, coordChange, hev]
  have hm : Measurable fun w =>
      (a : ℂ) * revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w := by
    rw [hψ]; exact measurable_const.mul hψm
  have hU2 : U ((fcI i).map fun w =>
        (a : ℂ) * revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w) =
      Uf ((fcI i).map fun w =>
        (a : ℂ) * revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w) :=
    unzippedField_eq_Ufam γ hx y hτ.le (map_mul_revMapInv_compl_H hW hτ ha hsep hm)
  show _ ∈ gcXS γ i ↔ _
  unfold ExactC
  dsimp only
  rw [hres, hev, ← hUdef, hU2, hψ]
  rfl

/-- **`GoodCMeasStmt` from the separation sandwich alone.** -/
theorem goodCMeasStmt_of_sep (hS : GCSepStmt) : GoodCMeasStmt :=
  goodCMeasStmt_of hS gcExStmt_holds

end GC
end ASep
end QuantumZipper
