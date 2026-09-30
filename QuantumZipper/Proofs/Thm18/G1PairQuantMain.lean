import QuantumZipper.Proofs.Thm18.G1PairQuantLim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PAIR-QUANT (4): `G1RegRepRestStmt` without universal measurability

The set `setQ` of pairs (path, data) at which, for both sides, the pulled-back field is a regular
sample satisfying the countable certificate `CountCond` is **measurable** (countably many
conditions; the certificate integrals are measurable in the pair by Carathéodory's joint
measurability `measurable_uncurry_of_continuous_of_measurable`, since on the regular set the
integrand is continuous in the integration variable) and is contained in the PAIR-LIM set
`setPair` (`pairLimAll_of_count`). Under the quantitative node `G1RestPairLipStmt` the
representative's data lies in `setQ` almost surely, which replaces both `G1RestPairStmt` and the
descriptive-set-theory input `PairLimUnivMeasStmt`.

Main result: `g1RegRepRestStmt_of_pairLip_unif :
G1RestPairLipStmt → G1RestUnifStmt → G1RegRepRestStmt`.

Own argument (measurability bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Rest

section Meas

variable {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The regular set for one side. -/
def setR (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) : Set G1PathData :=
  {p | IsRegularSample (xP γ Ψ left p)}

theorem measurableSet_setR (hΨ : G1PsiSel γ Ψ) (left : Bool) : MeasurableSet (setR γ Ψ left) :=
  G1Meas.measurableSet_rc2 hΨ left

open Classical in
/-- The certificate integrand, made continuous in `u` for every pair. -/
def integQ (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (g : ℂ → ℝ) (t s : ℝ)
    (u : ℂ) (p : G1PathData) : ℝ :=
  (if p ∈ setR γ Ψ left then evalReg (xP γ Ψ left p) (foldedCircle (retr u) t) -
    evalReg (xP γ Ψ left p) (foldedCircle (retr u) s) else 0) * g u

theorem measurable_intQ (hΨ : G1PsiSel γ Ψ) (left : Bool) {g : ℂ → ℝ} (hg : Continuous g)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    Measurable fun p : G1PathData => ∫ u, integQ γ Ψ left g t s u p := by
  have hj : Measurable (uncurry (integQ γ Ψ left g t s)) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun p => ?_) (fun u => ?_)
    · by_cases hp : p ∈ setR γ Ψ left
      · obtain ⟨F, hF⟩ := hp
        have e : ∀ u, integQ γ Ψ left g t s u p = (F (retr u, t) - F (retr u, s)) * g u :=
          fun u => by
            simp only [integQ, ite_eq_left (show p ∈ setR γ Ψ left from ⟨F, hF⟩)]
            rw [hF.evalReg_fc_of_mem (retr_mem u) ht, hF.evalReg_fc_of_mem (retr_mem u) hs]
        simp_rw [e]
        refine Continuous.mul (Continuous.sub ?_ ?_) hg
        · exact hF.1.comp_continuous (continuous_retr.prodMk continuous_const)
            fun u => ⟨retr_mem u, ht⟩
        · exact hF.1.comp_continuous (continuous_retr.prodMk continuous_const)
            fun u => ⟨retr_mem u, hs⟩
      · simp only [integQ, ite_eq_right hp, zero_mul]
        exact continuous_const
    · exact (Measurable.ite (measurableSet_setR hΨ left)
        ((measurable_canonP hΨ left _).sub (measurable_canonP hΨ left _))
        measurable_const).mul_const _
  exact (hj.stronglyMeasurable.integral_prod_left' (μ := volume)).measurable

theorem integral_integQ {left : Bool} {p : G1PathData} (hp : p ∈ setR γ Ψ left) {m : ℕ}
    {g : ℂ → ℝ} (hg0 : ∀ z ∉ Kb m, g z = 0) (t s : ℝ) :
    ∫ u, integQ γ Ψ left g t s u p = pairInt (xP γ Ψ left p) g t s := by
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [integQ, ite_eq_left hp]
  by_cases hu : u ∈ Kb m
  · rw [retr_of_mem (Kb_subset_Hbar m hu)]
  · simp [hg0 u hu]

theorem measurable_imp_of_not {P : Prop} (hP : ¬P) {q : G1PathData → Prop} :
    Measurable fun x => P → q x := by
  have e : (fun x => P → q x) = fun _ => True :=
    funext fun x => propext ⟨fun _ => trivial, fun _ h => absurd h hP⟩
  rw [e]; exact measurable_const

/-- The measurable certificate set. -/
def setQ (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) : Set G1PathData :=
  {p | ∀ left : Bool, IsRegularSample (xP γ Ψ left p) ∧ CountCond (xP γ Ψ left p)}

theorem setQ_subset : setQ γ Ψ ⊆ setPair γ Ψ := fun _ hp left =>
  pairLimAll_of_count (hp left).1 (hp left).2

theorem measurableSet_setQ (hΨ : G1PsiSel γ Ψ) : MeasurableSet (setQ γ Ψ) := by
  have e : setQ γ Ψ = ⋂ left : Bool, (setR γ Ψ left ∩ {p | ∀ m N : ℕ, ∃ C e : ℕ, ∀ i : ℕ,
      ∀ t s : ℚ, (0 : ℝ) < t → (t : ℝ) < 1 / ((e : ℝ) + 1) → (0 : ℝ) < s →
        (s : ℝ) < 1 / ((e : ℝ) + 1) →
          |∫ u, integQ γ Ψ left (dseq m N i) t s u p| ≤
            (C : ℝ) * N * Real.sqrt (max (t : ℝ) s)}) := by
    ext p
    simp only [setQ, mem_ofPred_eq, mem_iInter, mem_inter_iff]
    refine forall_congr' fun left => and_congr_right fun hp => ?_
    unfold CountCond
    simp only [integral_integQ (show p ∈ setR γ Ψ left from hp) (dseq_mem _ _ _).2]
  rw [e]
  refine MeasurableSet.iInter fun left => (measurableSet_setR hΨ left).inter ?_
  refine measurableSet_setOfPred.2 ?_
  refine Measurable.forall fun m => Measurable.forall fun N => Measurable.exists fun C =>
    Measurable.exists fun e => Measurable.forall fun i => Measurable.forall fun t =>
      Measurable.forall fun s => ?_
  by_cases ht : (0 : ℝ) < t
  · by_cases hs : (0 : ℝ) < s
    · refine measurable_const.imp (measurable_const.imp (measurable_const.imp
        (measurable_const.imp ?_)))
      exact measurableSet_setOfPred.1 (measurableSet_le
        (continuous_abs.measurable.comp (measurable_intQ hΨ left (dseq m N i).continuous ht hs))
        measurable_const)
    · exact measurable_const.imp (measurable_const.imp (measurable_imp_of_not hs))
  · exact measurable_imp_of_not ht

end Meas

end G1Rest

/-- **`G1RegRepRestStmt` from the quantitative PAIR-LIM node and the uniform Cauchy input**
(no universal measurability needed). -/
theorem g1RegRepRestStmt_of_pairLip_unif (hP : G1RestPairLipStmt) (hU : G1RestUnifStmt) :
    G1RegRepRestStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨alpha_lt_Qc hγ hγ2, Ω', inferInstance, P', X, A, inferInstance, hX, hA, hXA, rfl⟩
  have hD : AEMeasurable (fun ω' => WedgeMeas.dataFull H (wedgeRep γ X A ω')) P' :=
    WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
      (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 (alpha_lt_Qc hγ hγ2))
      (WedgeInf.wedgeInfiniteTotal hγ hγ2 (alpha_lt_Qc hγ hγ2)) hγ hγ2 hrep
  have hae : ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P',
      (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈
        G1Rest.setRC3 γ Ψ ∩ G1Rest.setQ γ Ψ := by
    filter_upwards [G1Rest.ae_rc3_rep γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ,
      G1RC.g1RegRepRC2Stmt_of_psiExt
        (G1RC.g1PsiExtStmt_of_holder_α G1RC.g1GoodBMStmt_sideHolderGood)
        γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ,
      hP γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a h3 h2 hp
    filter_upwards [h3 true, h3 false, h2 true, h2 false, hp true, hp false]
      with ω' h3t h3f h2t h2f hpt hpf
    set y := wedgeRep γ X A ω' with hy
    have ex : ∀ left : Bool,
        G1Rest.xP γ Ψ left (a, WedgeMeas.dataFull H y) = coordChange y (Ψ left a) (Qc γ) :=
      fun left => Factorization.coordChange_congr
        (CoordsFull.avgReg_congr_full (E1.coordsFull_fromC y)) _ _
    have hb : ∀ left : Bool, G1Rest.RC3All (coordChange y (Ψ left a) (Qc γ)) ∧
        IsRegularSample (coordChange y (Ψ left a) (Qc γ)) ∧
        G1Rest.PairLipMod (coordChange y (Ψ left a) (Qc γ)) := by
      intro left; cases left
      · exact ⟨h3f, h2f, hpf⟩
      · exact ⟨h3t, h2t, hpt⟩
    refine ⟨fun left => ?_, fun left => ?_⟩
    · show G1Rest.RC3All (G1Rest.xP γ Ψ left (a, WedgeMeas.dataFull H y))
      rw [ex]; exact (hb left).1
    · rw [ex]
      exact ⟨(hb left).2.1, G1Rest.countCond_of_pairLipMod (hb left).2.2⟩
  obtain ⟨E', hE'm, hE'S, hE'ae⟩ := G1Rest.exists_measurable_of_nullMeas hD
    ((g1RestRC3NullMeasStmt_of_unif hU γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ).inter
      (G1Rest.measurableSet_setQ hΨ).nullMeasurableSet) hae
  exact ⟨E', hE'm, fun p hp left => G1Rest.coreRest_of_mem
    ⟨(hE'S hp).1, G1Rest.setQ_subset (hE'S hp).2⟩ left, hE'ae⟩

end Thm18Asm
end QuantumZipper
