/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCDetTransfer
import InteractingSLE.Spec.Supplement.BRLeafLift
import InteractingSLE.Spec.Supplement.GB6RelDrvLift
import InteractingSLE.Spec.Restart.Aux54Loc

/-!
# Hull identities by determination: the generic retracing theorem

Packet PROVE-HULLDET. Theorem 1.4's two hull identities (`Theorem14.BR4aPath.BR4aHullDetStatement`, the counterflow of
the field recentred at a visited point `v`; `Supp8.GB6.GB6HullDetStatement`, the counterflow read relative to a stopped
flow prefix) have the same shape: a **relative counterflow** — the original counterflow read in a new chart and a new
capacity clock — is shown to be a coupling of the chart-transported field, and the canonical counterflow of that
field is then identified with it by determination. This file states and proves the determination half once.

* **`ae_flowLineDriver_eq_drvDec`** (universe bridge): a flow-line driver of the GFF of a sorted word `c` on a sample
  space in any universe `u` is, almost surely, the decoded canonical driver code `drvDec (F (c, X))` before its
  lifetime, which is the code's lifetime (Theorem 1.2 at universe `u` through `Exist.Staged.ae_detCode_eq`, and
  PROVE-T14-BR's comparison `Theorem14.BRLeaf.ae_drvOf_eq_drvDec` of the two canonical drivers);
* **`ae_retrace_of_hasSafeLaw`** (the generic retracing theorem, unstopped form): if a globally continuous adapted
  driver `W` from `0` carries the geometric images of the flow-line word of `c` and satisfies K2's inputs (S) and (L)
  (`HasSafeLaw`, `HasSafeMembers`) with the threshold lifetime, then every flow-line driver `(Wv, ζv)` of `X` has
  lifetime `ζv = thr(W)` and agrees with `W` before it (PROVE-FCDET's canonical transfer
  `Restart.FCDet.ae_driverCodeMatch_of_hasSafeLaw_on`, then the universe bridge);
* **`ae_isStopDrvMatch_of_isStoppedHullCouplingR`** (stopped form, for relative explorations with a finite relative
  lifetime such as GB6's): a coupling through a **regular Galmarino stop** of a flow-line word has its driver equal to
  the canonical driver code before the stop — the driver form of Aux. lemma 54 in the corrected form of ruling R79
  (`Restart.Aux54.stoppedHullExtendRStatement`, proved for every `κ > 0`), replacing PROVE-GB6-RELDRV's
  `Supp8.GB6.RelDrv.ae_isStopDrvMatch_of_isStoppedHullCoupling`, which takes the defective arbitrary-stop form.

R48: these results take Theorems 1.2–1.3 (through `h12p`, `h13` and a canonical driver code) as hypotheses; they serve
Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Supp8.HullDetGen

open Restart Restart.FCDet Restart.DomainMarkov Restart.DomainMarkov.K2 Sec2.Assembly Sec7.PocketTraversal LawUnique
  Exist.Staged Supp8.GB6 Supp8.GB6.RelDrv

/-! ### Small facts -/

/-- The flow field of a translation by `0` with constant `0 · k` is the field itself. -/
theorem flowField_zero_zero_mul (k : ℝ) (g : DistOn upperHalfPlaneOpens) :
    Exist.flowField 0 (0 * k) g = g :=
  Theorem14.BRLeaf.eq_of_isTranslateAddConst_zero_mul (Exist.isTranslateAddConst_flowField 0 (0 * k) g)

/-- The pairings of a GFF with piecewise-constant data are integrable (Gaussian plus a constant). -/
theorem integrable_apply_of_isGFF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hX : IsGFFWithBoundaryData P X b J) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => X ω φ) P := by
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hZ := (hX.2 u₀ hu₀).gaussian.hasGaussianLaw_eval φ
  have hi : Integrable (fun ω => X ω φ - ∫ z, u₀ z * φ z) P := hZ.integrable
  have := hi.add (integrable_const (∫ z, u₀ z * φ z))
  refine this.congr (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, sub_add_cancel]

/-- The law of a GFF with the data of a sorted word is the word's GFF law. -/
theorem map_eq_gffLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistOn upperHalfPlaneOpens}
    {c : BoundaryWord} (hc : c.IsSorted) (hX : IsGFFWithBoundaryData P X c.fn c.jumps) : P.map X = c.gffLaw := by
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c.isPiecewiseConstantBoundaryData
  have h := Exist.map_eq_of_isGFFWithBoundaryData hX (BoundaryWord.isGFFWithBoundaryData_gffLaw c hc) hu₀
  rw [h, Measure.map_id]

/-! ### The universe bridge -/

/-- **A flow-line driver at any universe is the decoded canonical driver code.** For the GFF `X` of a sorted word
`c` on a sample space in `Type u` and any flow-line driver `(W, ζ)` of `X` at angle `0`: almost surely `ζ` is the
lifetime of the canonical driver code `F (c, X)` and `W` is its decoded driver before `ζ`. -/
theorem ae_flowLineDriver_eq_drvDec (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ 0 F) {c : BoundaryWord} (hc : c.IsSorted) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : IsGFFWithBoundaryData P X c.fn c.jumps) {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hW : IsFlowLineDriver κ c.fn c.jumps 0 P X W ζ) :
    ∀ᵐ ω ∂P, ζ ω = (F (c, X ω)).2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω = drvDec (F (c, X ω)) t := by
  obtain ⟨h', 𝓕, VL, VR, B, htr, hC⟩ := hW
  have hh' : h' = X := funext fun ω => Theorem14.BRLeaf.eq_of_isTranslateAddConst_zero_mul (htr ω)
  subst hh'
  have hF' := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hΦ := (h12p κ hκ (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0)).choose_spec.2 _ _ _ _ hF' hC
  have hdet := ae_detCode_eq hκ hF' h13 hC hΦ
  have hcmp := Theorem14.BRLeaf.ae_drvOf_eq_drvDec h12p h13 hκ hF hc
  rw [← map_eq_gffLaw hc hX] at hcmp
  have hcmp' := ae_of_ae_map hX.1.aemeasurable hcmp
  filter_upwards [hdet, hcmp'] with ω ⟨x₀, hx₀, hζx, hwx, hcode⟩ ⟨h1, h2⟩
  have hcode' : detCode (paramΦ h12p hκ (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0))
      (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
        (flowLineRhoL κ c.fn c.jumps 0 0, flowLineRhoR κ c.fn c.jumps 0 0)), h' ω) = dOf x₀ := hcode
  rw [hcode', drvOf_of_mem (dOf_mem_DSet hx₀)] at h1 h2
  refine ⟨hζx.symm.trans h1, fun t ht => ?_⟩
  have ht' : (t : ℝ≥0∞) < cζ x₀ := hζx ▸ ht
  have ht'' : (t : ℝ≥0∞) < (F (c, h' ω)).2 := h1 ▸ ht'
  rw [← h2 t ht'', ← (hwx t ht).1]
  exact ((drvPath_dOf_agree x₀).2 t ht').symm

/-! ### The generic retracing theorem -/

/-- A word belongs to the type of its own flow-line word at angle `0`. -/
theorem mem_typeSet_self (κ : ℝ) (c : BoundaryWord) :
    c ∈ typeSet κ 0 (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0) (flowLineRhoL κ c.fn c.jumps 0 0)
      (flowLineRhoR κ c.fn c.jumps 0 0) := by
  refine ⟨rfl, rfl, fun i => ?_, fun j => ?_⟩
  · simp only [flowPad, i.2, ↓reduceDIte]
  · simp only [flowPad, j.2, ↓reduceDIte]

/-- The type positions of a word are its flow-line positions. -/
theorem typeXL_self (κ : ℝ) (c : BoundaryWord) :
    typeXL κ 0 (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0) (flowLineRhoL κ c.fn c.jumps 0 0)
      (flowLineRhoR κ c.fn c.jumps 0 0) c = flowLineXL c.fn c.jumps 0 := by
  funext i
  simp only [typeXL, mem_typeSet_self, ↓reduceIte, flowPad, i.2, ↓reduceDIte]

/-- The type positions of a word are its flow-line positions (right). -/
theorem typeXR_self (κ : ℝ) (c : BoundaryWord) :
    typeXR κ 0 (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0) (flowLineRhoL κ c.fn c.jumps 0 0)
      (flowLineRhoR κ c.fn c.jumps 0 0) c = flowLineXR c.fn c.jumps 0 := by
  funext j
  simp only [typeXR, mem_typeSet_self, ↓reduceIte, flowPad, j.2, ↓reduceDIte]

/-- **The generic retracing theorem (unstopped form).** Let `X` be the GFF of a sorted word `c` on a sample space in
`Type u`, and let `W` be a globally continuous `𝓗`-adapted driver from `0`, carrying the geometric images of the
flow-line marks of `c` at angle `0` (an admissible seed), with K2's inputs (S) and (L) for `X` and the threshold
lifetime `thr`. Then every flow-line driver `(Wv, ζv)` of `X` at angle `0` has lifetime `ζv = thr` and agrees with
`W` before it, almost surely. -/
theorem ae_retrace_of_hasSafeLaw (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ 0 F) {c : BoundaryWord} (hc : c.IsSorted) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : IsGFFWithBoundaryData P X c.fn c.jumps) {Wv : ℝ≥0 → Ω → ℝ} {ζv : Ω → ℝ≥0∞}
    (hWv : IsFlowLineDriver κ c.fn c.jumps 0 P X Wv ζv) {𝓗 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓗 W)
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0) 0
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))
    (hlaw : HasSafeLaw κ (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0) P 𝓗 univ
      (thr (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0) W
        (fun _ => flowLineXL c.fn c.jumps 0) (fun _ => flowLineXR c.fn c.jumps 0)) W
      (geomLW W fun _ => flowLineXL c.fn c.jumps 0) (geomRW W fun _ => flowLineXR c.fn c.jumps 0) X)
    (hmem : HasSafeMembers P 𝓗 univ
      (thr (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0) W
        (fun _ => flowLineXL c.fn c.jumps 0) (fun _ => flowLineXR c.fn c.jumps 0)) W X) :
    ∀ᵐ ω ∂P, ζv ω = thr (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0) W
        (fun _ => flowLineXL c.fn c.jumps 0) (fun _ => flowLineXR c.fn c.jumps 0) ω ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζv ω → Wv t ω = W t ω := by
  have hXf : (fun ω => Exist.flowField 0 (0 * QuantumZipper.chiC κ) (X ω)) = X :=
    funext fun ω => flowField_zero_zero_mul _ (X ω)
  have hxL := typeXL_self κ c
  have hxR := typeXR_self κ c
  have hmatch := ae_driverCodeMatch_of_hasSafeLaw_on (P := P) (θ := 0) hκ (M := univ) MeasurableSet.univ
    (c := fun _ => c) measurable_const (fun _ _ => mem_typeSet_self κ c) hW0 hWc hWa (Hc := X) hX.1
    (fun φ => by
      simp only [flowField_zero_zero_mul, Measure.restrict_univ]
      exact integrable_apply_of_isGFF c.isPiecewiseConstantBoundaryData hX φ)
    (Eventually.of_forall fun _ _ => by rw [hxL, hxR]; exact hseed)
    (by simp only [hxL, hxR, hXf]; exact hlaw) (by simp only [hxL, hxR, hXf]; exact hmem) hF
  have hv := ae_flowLineDriver_eq_drvDec h12p h13 hκ hF hc hX hWv
  filter_upwards [hmatch, hv] with ω hm hvω
  have hm' := hm (mem_univ ω)
  simp only [hxL, hxR] at hm'
  set L := thr (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0) W
    (fun _ => flowLineXL c.fn c.jumps 0) (fun _ => flowLineXR c.fn c.jumps 0) ω with hL
  have hgood := isGoodDrvCode_of_driverCodeMatch hm' ((hWc ω).continuousOn)
  have hstop : IsStopDrvMatch (F (c, X ω)) (fun t => W t ω) L :=
    ⟨hm'.1.le, fun n k hnk => hm'.2.2 n k hnk⟩
  have hdec := eqOn_drvDec_of_isStopDrvMatch hgood (hWc ω).continuousOn hstop
  have hζ : ζv ω = L := hvω.1.trans hm'.1.symm
  refine ⟨hζ, fun t ht => ?_⟩
  rw [hvω.2 t ht]
  exact hdec t (hζ ▸ ht)

/-! ### The stopped form through the corrected Aux. lemma 54 (R79) -/

/-- **A coupling through a regular Galmarino stop of a flow-line word has the stopped driver match** (Aux. lemma 54
in its corrected form, R79, and the determination clause of a canonical driver code). The coupling's processes need
not be measurable: a measurable process `Wb` agreeing with the coupling's driver through `e` carries the conclusion.
This replaces `Supp8.GB6.RelDrv.ae_isStopDrvMatch_of_isStoppedHullCoupling` (whose hypothesis
`StoppedExtend.StoppedHullExtendStatement` is the defective arbitrary-stop form) by its regular-stop form. -/
theorem ae_isStopDrvMatch_of_isStoppedHullCouplingR {κ θ : ℝ} (hκ : 0 < κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode κ θ F)
    (c : BoundaryWord) {Ω : Type} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Hc X : Ω → DistOn upperHalfPlaneOpens}
    (hX : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω)) {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {e : Ω → ℝ≥0∞}
    (hSC : StoppedExtend.IsStoppedHullCoupling κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) Q 𝓕 W VL VR B e X)
    {R : HistorySpace (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0) → ℝ≥0∞} (hRm : Measurable R)
    (hRG : StoppedExtendWF.IsHistGalmarino R) (hRe : ∀ᵐ ω ∂Q, e ω = R (killedHistory W VL VR e ω))
    (hreg : Aux54.IsRegularStop (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) Q W VL VR e)
    {Wb : ℝ≥0 → Ω → ℝ} (hWb : ∀ t, Measurable (Wb t)) (hHc : Measurable Hc) (he : Measurable e)
    (hagb : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω → W t ω = Wb t ω) :
    ∀ᵐ ω ∂Q, IsStopDrvMatch (F (c, Hc ω)) (fun t => Wb t ω) (e ω) := by
  obtain ⟨C, mC, K, hK, 𝓕', W', VL', VR', B', ζ', hC, hag⟩ :=
    Aux54.stoppedHullExtendRStatement.{0} hκ _ _ _ _ (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0) R hRm
      hRG Q 𝓕 W VL VR B e X hSC hRe hreg
  have hmap : (Q ⊗ₘ K).map Prod.fst = Q := by
    rw [← Measure.fst, Measure.fst_compProd]
  have hA := ae_isStopDrvMatch_on_extension hF c hX hC hag
  have hSm : MeasurableSet {ω | IsStopDrvMatch (F (c, Hc ω)) (fun t => Wb t ω) (e ω)} :=
    measurableSet_isStopDrvMatch (hF.1.comp (measurable_const.prodMk hHc)) hWb he
  have hmapE : AEMeasurable (Prod.fst : Ω × C → Ω) (Q ⊗ₘ K) := measurable_fst.aemeasurable
  have hagbE : ∀ᵐ p ∂(Q ⊗ₘ K), ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e p.1 → W t p.1 = Wb t p.1 :=
    ae_of_ae_map hmapE (by rw [hmap]; exact hagb)
  rw [← hmap]
  refine (ae_map_iff hmapE hSm).2 ?_
  filter_upwards [hA, hagbE] with p hp hbp
  refine ⟨hp.1, fun n k hnk => ?_⟩
  show Wb (dyad n k) p.1 = (F (c, Hc p.1)).1 n k
  rw [← hbp _ hnk.le]
  exact hp.2 n k hnk

end InteractingSLE.Supp8.HullDetGen
