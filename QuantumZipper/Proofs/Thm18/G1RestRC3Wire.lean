import QuantumZipper.Proofs.Thm18.G1RestRC3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-REST, RC3 part (2): the measurable certificate set and `G1RestRC3NullMeasStmt`

With the deterministic certificate of G1RestRC3.lean, the set `setM` of pairs (path, data) with

* path in a measurable full-measure set `A1` of paths whose two selected maps are `PsiGood`
  and `PsiExt`,
* `fromC c` regular, and, for both sides, RC2, `C2P` and `C3P` for the pulled-back field,

is measurable (countably many measurable conditions) and contained in the RC3 set
`G1Rest.setRC3`. Under `G1RestUnifStmt` it has full measure for the product law, so
`setRC3` is null-measurable.

Main result: `g1RestRC3NullMeasStmt_of_unif : G1RestUnifStmt → G1RestRC3NullMeasStmt`.

Own argument (measurability bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Rest

open GoodMeas (Sd box qpt mprop_abs_le)

/-! ## 1. Measurability in (path, data) -/

section Meas

variable {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The pulled-back field at a pair (path, data). -/
def xP (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (p : G1PathData) : FieldSample :=
  coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ)

theorem measurable_psiP (hΨ : G1PsiSel γ Ψ) (left : Bool) :
    Measurable fun r : G1PathData × ℂ => Ψ left r.1.1 r.2 :=
  (hΨ.1 left).comp (measurable_fst.fst.prodMk measurable_snd)

theorem measurable_phiP (hΨ : G1PsiSel γ Ψ) (left : Bool) (i : ℕ) (q : ℂ × ℝ) :
    Measurable fun p : G1PathData => PhiP (E1.fromC p.2.1) (Ψ left p.1) i q :=
  (StronglyMeasurable.integral_prod_right'
    (f := fun r : G1PathData × ℂ => avgReg (E1.fromC r.1.2.1) i (Ψ left r.1.1 r.2))
    ((measurable_avgReg i).comp ((G1Meas.measurable_fromC'.comp measurable_fst.snd.fst).prodMk
      (measurable_psiP hΨ left))).stronglyMeasurable).measurable

theorem measurable_rawP (hΨ : G1PsiSel γ Ψ) (left : Bool) (ν : Measure ℂ) [SFinite ν] :
    Measurable fun p : G1PathData => xP γ Ψ left p ν := by
  show Measurable fun p : G1PathData => evalReg (E1.fromC p.2.1) (ν.map (Ψ left p.1)) +
    Qc γ * ∫ z, Real.log ‖deriv (Ψ left p.1) z‖ ∂ν
  exact (G1Meas.measurable_evalReg_map_param (y := fun p : G1PathData => E1.fromC p.2.1)
    (G1Meas.measurable_fromC'.comp measurable_snd.fst)
    ((hΨ.1 left).comp (measurable_fst.fst.prodMk measurable_snd)) ν).add
    (measurable_const.mul (StronglyMeasurable.integral_prod_right'
      (f := fun r : G1PathData × ℂ => Real.log ‖deriv (Ψ left r.1.1) r.2‖)
      ((hΨ.2.1 left).comp (measurable_fst.fst.prodMk measurable_snd)).stronglyMeasurable).measurable)

theorem measurable_canonP (hΨ : G1PsiSel γ Ψ) (left : Bool) (ν : Measure ℂ) [SFinite ν] :
    Measurable fun p : G1PathData => evalReg (xP γ Ψ left p) ν := by
  have e : ∀ p, evalReg (xP γ Ψ left p) ν =
      evalReg (E1.fromC (CoordsFull.coordsFull (xP γ Ψ left p))) ν := fun p => by
    unfold evalReg
    rw [CoordsFull.avgReg_congr_full (E1.coordsFull_fromC (xP γ Ψ left p))]
  simp_rw [e]
  exact (measurable_evalReg ν).comp (G1Meas.measurable_fromC'.comp (measurable_pi_iff.2
    fun i => G1Meas.measurable_coordsFull_coordChange (G1Meas.measurable_fromC'.comp
      measurable_snd.fst) ((hΨ.1 left).comp (measurable_fst.fst.prodMk measurable_snd))
      ((hΨ.2.1 left).comp (measurable_fst.fst.prodMk measurable_snd)) (Qc γ) i))

theorem measurableSet_C2P (hΨ : G1PsiSel γ Ψ) (left : Bool) :
    MeasurableSet {p : G1PathData | C2P (E1.fromC p.2.1) (Ψ left p.1)} := by
  refine measurableSet_setOfPred.2 ?_
  unfold C2P
  refine Measurable.forall fun m => Measurable.forall fun e => Measurable.exists fun J => ?_
  refine Measurable.forall fun i => measurable_const.imp (Measurable.forall fun i' =>
    measurable_const.imp (Measurable.forall fun j => measurable_const.imp
      (measurable_const.imp ?_)))
  exact mprop_abs_le (measurable_phiP hΨ left _ _) (measurable_phiP hΨ left _ _) _

theorem measurableSet_C3P (hΨ : G1PsiSel γ Ψ) (left : Bool) :
    MeasurableSet {p : G1PathData | C3P (xP γ Ψ left p)} := by
  refine measurableSet_setOfPred.2 ?_
  unfold C3P
  refine Measurable.forall fun j => measurable_const.imp ?_
  exact measurableSet_setOfPred.1 (measurableSet_eq_fun (measurable_canonP hΨ left _)
    (measurable_rawP hΨ left _))

/-- The certificate set, for a set of good paths `A1`. -/
def setM (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (A1 : Set (ℝ≥0 → ℝ)) : Set G1PathData :=
  (Prod.fst ⁻¹' A1) ∩ {p | IsRegularSample (E1.fromC p.2.1)} ∩
    ⋂ left : Bool, ({p | IsRegularSample (xP γ Ψ left p)} ∩
      {p | C2P (E1.fromC p.2.1) (Ψ left p.1)} ∩ {p | C3P (xP γ Ψ left p)})

theorem measurableSet_setM (hΨ : G1PsiSel γ Ψ) {A1 : Set (ℝ≥0 → ℝ)} (hA1 : MeasurableSet A1) :
    MeasurableSet (setM γ Ψ A1) := by
  refine ((measurable_fst hA1).inter ?_).inter (MeasurableSet.iInter fun left =>
    ((G1Meas.measurableSet_rc2 hΨ left).inter (measurableSet_C2P hΨ left)).inter
      (measurableSet_C3P hΨ left))
  exact G1Meas.measurable_fromC'.comp measurable_snd.fst GoodMeas.measurableSet_isRegularSample

theorem setM_subset {A1 : Set (ℝ≥0 → ℝ)}
    (hA1 : ∀ a ∈ A1, ∀ left : Bool, G1RC.PsiGood (Ψ left a) ∧ G1RC.PsiExt (Ψ left a)) :
    setM γ Ψ A1 ⊆ setRC3 γ Ψ := by
  rintro p ⟨⟨hpa, hy⟩, hp⟩ left
  obtain ⟨⟨hreg, h2⟩, h3⟩ := mem_iInter.1 hp left
  exact rc3All_of_good (hA1 p.1 hpa left).1 (hA1 p.1 hpa left).2 hy hreg h2 h3

end Meas

end G1Rest

/-! ## 2. The input and the result -/

/-- **Input: uniform Cauchy property at the representative.** For a.e. path and both sides,
a.s. the smoothings `k ↦ ∫ avgReg y k ∘ ψ dfc(q)` of the canonical wedge representative `y`
along the selected map `ψ` are uniformly Cauchy at the dyadic points of each box
`GoodMeas.box m` (locally uniform convergence of the circle-average regularization of the
pulled-back field on `Hbar × (0,∞)`). -/
def G1RestUnifStmt : Prop :=
  G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ᵐ ω' ∂P',
      G1Rest.C2P (wedgeRep γ X A ω') (Ψ left a)

/-- **The RC3 set is null-measurable, given the uniform Cauchy input.** -/
theorem g1RestRC3NullMeasStmt_of_unif (hU : G1RestUnifStmt) : G1RestRC3NullMeasStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  set ν := P.map (pathOf B) with hν
  set D : Ω' → (ℕ → ℝ) × (TestFun H → ℝ) := fun ω' => WedgeMeas.dataFull H (wedgeRep γ X A ω')
    with hDdef
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨alpha_lt_Qc hγ hγ2, Ω', inferInstance, P', X, A, inferInstance, hX, hA, hXA, rfl⟩
  have hD : AEMeasurable D P' :=
    WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
      (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 (alpha_lt_Qc hγ hγ2))
      (WedgeInf.wedgeInfiniteTotal hγ hγ2 (alpha_lt_Qc hγ hγ2)) hγ hγ2 hrep
  -- good paths
  set A0 : Set (ℝ≥0 → ℝ) :=
    {a | ∀ left : Bool, G1RC.PsiGood (Ψ left a) ∧ G1RC.PsiExt (Ψ left a)} with hA0def
  have hA0 : ∀ᵐ a ∂ν, a ∈ A0 := by
    have hg := G1RC.ae_map_pathOf_of_chord G1RC.g1RegPathChordStmt hγ hγ2 hB hΨ
      (fun f => ∀ left, G1RC.PsiGood (f left)) fun a hc hs left =>
        G1RC.psiGood_of_sel hΨ hc hs left
    filter_upwards [hg, G1RC.g1PsiExtStmt_of_holder_α G1RC.g1GoodBMStmt_sideHolderGood
      γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a h1 h2 left using ⟨h1 left, h2 left⟩
  set A1 : Set (ℝ≥0 → ℝ) := (toMeasurable ν A0ᶜ)ᶜ with hA1def
  have hA1m : MeasurableSet A1 := (measurableSet_toMeasurable _ _).compl
  have hA1sub : A1 ⊆ A0 := fun a ha => by
    by_contra h; exact ha (subset_toMeasurable _ _ h)
  have hA1ae : ∀ᵐ a ∂ν, a ∈ A1 := by
    have h0 : ν (toMeasurable ν A0ᶜ) = 0 := by
      rw [measure_toMeasurable]; exact ae_iff.1 hA0
    exact measure_eq_zero_iff_ae_notMem.1 h0
  set M := G1Rest.setM γ Ψ A1 with hMdef
  have hMm : MeasurableSet M := G1Rest.measurableSet_setM hΨ hA1m
  have hMS : M ⊆ G1Rest.setRC3 γ Ψ := G1Rest.setM_subset fun a ha => hA1sub ha
  -- iterated a.s. membership in `M`
  have hae : ∀ᵐ a ∂ν, ∀ᵐ ω' ∂P', (a, D ω') ∈ M := by
    filter_upwards [hA1ae, G1RC.g1RegRepRC2Stmt_of_psiExt
      (G1RC.g1PsiExtStmt_of_holder_α G1RC.g1GoodBMStmt_sideHolderGood)
        γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ,
      hU γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ,
      G1Rest.ae_rc3_rep γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a ha1 h2 hu h3
    filter_upwards [wedgeRegSampleStmt_holds γ P' (wedgeRep γ X A) hγ hγ2 hrep,
      h2 true, h2 false, hu true, hu false, h3 true, h3 false] with ω' hy h2t h2f hut huf h3t h3f
    set y := wedgeRep γ X A ω' with hy_def
    have ea : avgReg (E1.fromC (D ω').1) = avgReg y :=
      CoordsFull.avgReg_congr_full (E1.coordsFull_fromC y)
    have ex : ∀ left : Bool, G1Rest.xP γ Ψ left (a, D ω') = coordChange y (Ψ left a) (Qc γ) :=
      fun left => Factorization.coordChange_congr ea _ _
    have hc2 : ∀ left : Bool, G1Rest.C2P y (Ψ left a) →
        G1Rest.C2P (E1.fromC (D ω').1) (Ψ left a) := fun left h => by
      unfold G1Rest.C2P G1Rest.PhiP at h ⊢; rw [ea]; exact h
    have hb : ∀ left : Bool, IsRegularSample (coordChange y (Ψ left a) (Qc γ)) ∧
        G1Rest.C2P y (Ψ left a) ∧ G1Rest.RC3All (coordChange y (Ψ left a) (Qc γ)) := by
      intro left; cases left
      · exact ⟨h2f, huf, h3f⟩
      · exact ⟨h2t, hut, h3t⟩
    refine ⟨⟨ha1, (G1Meas.isRegularSample_fromC_iff y).2 hy⟩, mem_iInter.2 fun left => ?_⟩
    obtain ⟨hr, hc, h3l⟩ := hb left
    refine ⟨⟨?_, hc2 left hc⟩, ?_⟩
    · show IsRegularSample (G1Rest.xP γ Ψ left (a, D ω'))
      rw [ex]; exact hr
    · show G1Rest.C3P (G1Rest.xP γ Ψ left (a, D ω'))
      rw [ex]; exact fun j hj => h3l _ hj.1 _ hj.2
  -- the complement of `M` is null for the product law
  have h0 : ν.prod (P'.map D) Mᶜ = 0 := by
    rw [Measure.measure_prod_null hMm.compl]
    filter_upwards [hae] with a ha
    show (P'.map D) (Prod.mk a ⁻¹' Mᶜ) = 0
    rw [Measure.map_apply_of_aemeasurable hD (measurable_prodMk_left hMm.compl)]
    exact measure_eq_zero_iff_ae_notMem.2 (ha.mono fun ω' h h' => h' h)
  have hnull : ν.prod (P'.map D) (G1Rest.setRC3 γ Ψ \ M) = 0 :=
    measure_mono_null (fun p hp => hp.2) h0
  rw [← union_sdiff_cancel hMS]
  exact hMm.nullMeasurableSet.union (NullMeasurableSet.of_null hnull)

end Thm18Asm
end QuantumZipper
