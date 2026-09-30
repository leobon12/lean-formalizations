import QuantumZipper.Proofs.Zipper.F2WedgeCouplePath
import QuantumZipper.Proofs.Zipper.F2WedgeCoupleIndep
import QuantumZipper.Proofs.Zipper.F2Step2b
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.LQG.WedgeMeasurable

/-!
# WEDGE-COUPLE: `WedgeLogCouplingStmt` holds

Theorem 1.3, node F2, step (2b), input `WedgeLogCouplingStmt` (`F2Step2b.lean`). Sources:
Sheffield, arXiv:1012.4797, §1.6 (the `α`-wedge restricted to `B₁` is a free field plus
`α(−log|·|)`, up to an additive constant) and §5.4, pp. 70–72; Duplantier–Miller–Sheffield,
arXiv:1409.7055, §4.1 and Def. 4.5 (radial/lateral decomposition, the radial part of a wedge).

Construction on `(Ω × Ω, P ⊗ P)` (a second independent copy of `(X, B)`):
* `X' = coupleField X X`: lateral part of `X ∘ fst` plus the radial part of `X ∘ snd`
  (a free field, `isFreeGFFModConstH_coupleField`);
* `A = wedgePath α Q (P̃ ∘ fst) (B̃ ∘ snd)`, `P̃` a continuous version of the radial Brownian
  motion `radialBMpos X` of `X` and `B̃` one of the driver `B` (so the forward part of `A` is the
  radial process of `X ∘ fst`, the backward part uses the driver of the second copy);
* `C = −h_1(0)` of `X ∘ fst`, `j₀ = 1`.
The pathwise identity is `ae_dyCircAgree_couple`; the independences come from the lateral/radial
independence (`indepFun_latF_radialProc`) and the product structure (`indepFun_prod_pair`);
`A` is measurable for the σ-algebra of its two paths (`WedgeMeas.measurable_wedgePath_joint`),
which avoids any measurability of `wedgePath` on non-continuous paths.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace F2

open WedgeTK

/-- The wedge path of continuous, measurable paths is measurable (as a path-valued map). -/
theorem measurable_wedge_fun {Ω : Type*} [MeasurableSpace Ω] (α Q : ℝ) {B B' : ℝ≥0 → Ω → ℝ}
    (hBc : ∀ ω, Continuous fun t => B t ω) (hB'c : ∀ ω, Continuous fun t => B' t ω)
    (hBm : ∀ t, Measurable (B t)) (hB'm : ∀ t, Measurable (B' t)) :
    Measurable (fun ω (t : ℝ) => wedgePath α Q (fun s => B s ω) (fun s => B' s ω) t) :=
  measurable_pi_iff.2 fun t =>
    (WedgeMeas.measurable_wedgePath_joint α Q hBc hB'c hBm hB'm).comp
      (measurable_id.prodMk measurable_const)

/-- `latF` of the identity field is measurable. -/
theorem measurable_latF_id : Measurable (latF (fun x : FieldSample => x)) := by
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : IsAdmissibleH μ
  · have := h.1
    simp only [latF, Set.indicator_of_mem (show μ ∈ {μ : Measure ℂ | IsAdmissibleH μ} from h)]
    exact (measurable_pi_apply μ).sub (measurable_radInt μ)
  · simp only [latF, Set.indicator_of_notMem (show μ ∉ {μ : Measure ℂ | IsAdmissibleH μ} from h)]
    exact measurable_const

theorem measurable_radialPath :
    Measurable fun (x : FieldSample) (s : ℝ≥0) =>
      (√2)⁻¹ * (radAvgReg x (Real.exp (-(s : ℝ))) - radAvgReg x 1) :=
  measurable_pi_iff.2 fun s =>
    ((measurable_radAvgReg₂.comp (measurable_id.prodMk measurable_const)).sub
      (measurable_radAvgReg₂.comp (measurable_id.prodMk measurable_const))).const_mul _

/-- The coupled field as a function of (lateral part, second field). -/
theorem measurable_couplePhi :
    Measurable fun q : FieldSample × FieldSample => q.1 + radF q.2 :=
  measurable_pi_iff.2 fun μ =>
    ((measurable_pi_apply μ).comp measurable_fst).add
      ((measurable_pi_apply μ).comp (measurable_radF.comp measurable_snd))

/-- **`WedgeLogCouplingStmt` holds.** -/
theorem wedgeLogCouplingStmt_holds : WedgeLogCouplingStmt := by
  intro κ _ _ Ω _ P _ B X hB hX hXB
  set α : ℝ := Real.sqrt κ - 2 / Real.sqrt κ with hα
  set Q : ℝ := Qc (Real.sqrt κ) with hQ
  obtain ⟨Pt, hPtm, hPtc, -, hPtB, hPtae⟩ :=
    RS.exists_good_version0 (isBrownianReal_radialBMpos hX)
  obtain ⟨Bt, hBtm, hBtc, -, hBtB, hBtae⟩ := RS.exists_good_version0 hB
  have mPt : Measurable (pathOf Pt) := measurable_pi_iff.2 hPtm
  have mBt : Measurable (pathOf Bt) := measurable_pi_iff.2 hBtm
  -- independences on `Ω`
  have hPtpath : pathOf (radialBMpos X) =ᵐ[P] pathOf Pt :=
    hPtae.mono fun ω h => funext fun t => (h t).symm
  have hBtpath : pathOf B =ᵐ[P] pathOf Bt := hBtae.mono fun ω h => funext fun t => (h t).symm
  have hXBt : IndepFun X (pathOf Bt) P := hXB.symm.congr EventuallyEq.rfl hBtpath
  have hφ : Measurable fun (v : ℝ → ℝ) (s : ℝ≥0) => (√2)⁻¹ * v s :=
    measurable_pi_iff.2 fun s => (measurable_pi_apply (s : ℝ)).const_mul _
  have hLPt : IndepFun (latF X) (pathOf Pt) P := by
    have h : IndepFun (latF X) (pathOf (radialBMpos X)) P :=
      (indepFun_latF_radialProc hX).comp measurable_id hφ
    exact h.congr EventuallyEq.rfl hPtpath
  have hLPB : IndepFun (fun ω => (latF X ω, pathOf Pt ω)) (pathOf Bt) P := by
    have h : IndepFun (fun ω => (latF (fun x : FieldSample => x) (X ω),
        fun s : ℝ≥0 => (√2)⁻¹ * (radAvgReg (X ω) (Real.exp (-(s : ℝ))) - radAvgReg (X ω) 1)))
        (pathOf Bt) P :=
      hXBt.comp (measurable_latF_id.prodMk measurable_radialPath) measurable_id
    refine h.congr ?_ EventuallyEq.rfl
    filter_upwards [hPtpath] with ω hω
    exact Prod.ext rfl hω
  -- the product space
  set F1 : Ω × Ω → FieldSample × FieldSample := fun ω => (latF X ω.1, X ω.2) with hF1
  set F2 : Ω × Ω → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) := fun ω => (pathOf Pt ω.1, pathOf Bt ω.2) with hF2
  have hI12 : IndepFun F1 F2 (P.prod P) :=
    indepFun_prod_pair (measurable_latF hX) mPt (measurable_X_pi hX) mBt hLPt hXBt
  set A : ℝ → Ω × Ω → ℝ :=
    fun t ω => wedgePath α Q (fun s => Pt s ω.1) (fun s => Bt s ω.2) t with hA
  have hX'eq : coupleField X X = (fun q : FieldSample × FieldSample => q.1 + radF q.2) ∘ F1 :=
    funext fun ω => coupleField_eq_add X X ω
  have hX'le : MeasurableSpace.comap (coupleField X X) inferInstance ≤
      MeasurableSpace.comap F1 inferInstance := by
    rw [hX'eq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono measurable_couplePhi.comap_le
  have hAle : MeasurableSpace.comap (fun ω t => A t ω) inferInstance ≤
      MeasurableSpace.comap F2 inferInstance :=
    Measurable.comap_le (@measurable_wedge_fun (Ω × Ω) (MeasurableSpace.comap F2 inferInstance)
      α Q (fun s ω => Pt s ω.1) (fun s ω => Bt s ω.2) (fun ω => hPtc ω.1) (fun ω => hBtc ω.2)
      (fun t => ((measurable_pi_apply t).comp measurable_fst).comp (comap_measurable F2))
      (fun t => ((measurable_pi_apply t).comp measurable_snd).comp (comap_measurable F2)))
  have hind1 : IndepFun (coupleField X X) (fun ω t => A t ω) (P.prod P) := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right
      (indep_of_indep_of_le_left ((IndepFun_iff_Indep _ _ _).1 hI12) hX'le) hAle
  set H : Ω × Ω → (FieldSample × (ℝ≥0 → ℝ)) × (FieldSample × (ℝ≥0 → ℝ)) :=
    fun ω => ((latF X ω.1, pathOf Pt ω.1), (X ω.2, pathOf Bt ω.2)) with hH
  have hIH : IndepFun H (fun ω => (pathOf Bt ω.1, ())) (P.prod P) :=
    indepFun_prod_pair ((measurable_latF hX).prodMk mPt) mBt ((measurable_X_pi hX).prodMk mBt)
      measurable_const hLPB (indepFun_const_right _ ())
  have hIH' : IndepFun H (fun ω => pathOf Bt ω.1) (P.prod P) :=
    hIH.comp measurable_id measurable_fst
  have hpairle : MeasurableSpace.comap (fun ω => (coupleField X X ω, fun t => A t ω))
      inferInstance ≤ MeasurableSpace.comap H inferInstance := by
    have m1 : Measurable[MeasurableSpace.comap H inferInstance] (coupleField X X) := by
      have e : coupleField X X = ((fun q : FieldSample × FieldSample => q.1 + radF q.2) ∘
          fun h : (FieldSample × (ℝ≥0 → ℝ)) × (FieldSample × (ℝ≥0 → ℝ)) => (h.1.1, h.2.1)) ∘ H :=
        funext fun ω => coupleField_eq_add X X ω
      rw [e]
      exact (measurable_couplePhi.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).comp (comap_measurable H)
    have m2 : Measurable[MeasurableSpace.comap H inferInstance] (fun ω t => A t ω) :=
      @measurable_wedge_fun (Ω × Ω) (MeasurableSpace.comap H inferInstance)
        α Q (fun s ω => Pt s ω.1) (fun s ω => Bt s ω.2) (fun ω => hPtc ω.1) (fun ω => hBtc ω.2)
        (fun t => ((measurable_pi_apply t).comp (measurable_snd.comp measurable_fst)).comp
          (comap_measurable H))
        (fun t => ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)).comp
          (comap_measurable H))
    exact (m1.prodMk m2).comap_le
  have hind2 : IndepFun (fun ω => (coupleField X X ω, fun t => A t ω))
      (pathOf (fun t (ω : Ω × Ω) => B t ω.1)) (P.prod P) := by
    have h : IndepFun (fun ω => (coupleField X X ω, fun t => A t ω))
        (fun ω => pathOf Bt ω.1) (P.prod P) := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left ((IndepFun_iff_Indep _ _ _).1 hIH') hpairle
    refine h.congr EventuallyEq.rfl ?_
    filter_upwards [ae_fst (P' := P) hBtpath] with ω hω
    exact hω.symm
  refine ⟨Ω, inferInstance, P, inferInstance, coupleField X X, A,
    fun ω => -radAvgReg (X ω.1) 1, 1, isFreeGFFModConstH_coupleField hX hX,
    ⟨fun s ω => Pt s ω.1, fun s ω => Bt s ω.2,
      NonVacuity.nv_isBrownianReal measurePreserving_fst hPtB,
      NonVacuity.nv_isBrownianReal measurePreserving_snd hBtB,
      NonVacuity.nv_indepFun_prod (pathOf Pt) (pathOf Bt), fun ω t => rfl⟩,
    hind1, NonVacuity.nv_isBrownianReal measurePreserving_fst hB, hind2, ?_⟩
  exact ae_dyCircAgree_couple hX hX hPtae Bt α Q

end F2
end QuantumZipper
