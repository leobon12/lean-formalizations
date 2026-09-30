import QuantumZipper.Proofs.Zipper.Cor15WRCore
import QuantumZipper.Proofs.Zipper.Cor15PosDriver
import QuantumZipper.Proofs.Zipper.Cor15GoodCoords
import QuantumZipper.Proofs.LQG.RevCouplingReg

/-!
# Corollary 1.5(a), `t > 0`: `Cor15WeldReadStmt`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5
(pp. 17–18; no proof in the paper). Task COR15-WR.

* `exists_goodPathRSet`: a Borel set of paths on `[0,t]`, good at time `t` and removable at all
  rational times in `(0,t)`, charged a.s. by `√κ B` (pull back of `exists_goodDriverSet'` at the
  rational times by restriction);
* `bdryApprox_fieldOf`, `qBoundaryMeasure_fieldOf`, `bCert_fieldOf`: the boundary data of
  `fieldOf x` is that of `x` times a positive constant (under `BdryConvAE x`);
* **`cor15WeldRead_of_reg`**: `Cor15WeldReadStmt κ t P B X`, from Theorem 1.3,
  Rohde–Schramm simplicity and one explicit a.s. regularity input on the unzipped field
  `y = zipCapDown √κ t (𝔥₀ + X, √κ B)`: `BdryConvAE y.1`, the boundary certificate
  `E1.M4.BCert √κ y.1` and `ν_{y.1}[0,∞) = ∞`. Atomlessness is taken from the (proved)
  `RevCouplingReg.revCouplingBoundaryMeasureRegular`.

Own assembly (see `Cor15WRCore`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull Thm14Determination Thm14WeldingData Thm14GoodDriverSet

/-! ### Restriction of paths -/

/-- Restriction of a path on `[0,t]` to `[0,q]`. -/
def resPath {q t : ℝ} (hqt : q ≤ t) (g : C(Icc (0 : ℝ) t, ℝ)) : C(Icc (0 : ℝ) q, ℝ) :=
  g.comp ⟨Set.inclusion (Icc_subset_Icc_right hqt), continuous_inclusion _⟩

theorem measurable_resPath {q t : ℝ} (hqt : q ≤ t) : Measurable (resPath hqt) :=
  (ContinuousMap.continuous_precomp _).measurable

theorem resPath_pathC {q t : ℝ} (hqt : q ≤ t) {W : ℝ → ℝ} (hW : Continuous W) :
    resPath hqt (pathC t W) = pathC q W := by
  ext s
  simp [resPath, pathC, hW]

theorem eqOn_extIccPath_resPath {q t : ℝ} (hq : 0 ≤ q) (hqt : q ≤ t)
    (g : C(Icc (0 : ℝ) t, ℝ)) :
    EqOn (extIccPath hq (resPath hqt g)) (extIccPath (hq.trans hqt) g) (Icc 0 q) := by
  intro s hs
  rw [extIccPath_of_mem hq _ hs, extIccPath_of_mem _ _ ⟨hs.1, hs.2.trans hqt⟩]
  rfl

/-- **Borel good set with removability at rational times.** -/
theorem exists_goodPathRSet (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ4 : κ < 4) {t : ℝ} (ht : 0 < t) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∃ G : Set C(Icc (0 : ℝ) t, ℝ), MeasurableSet G ∧ (∀ g ∈ G, GoodPathR ht.le g) ∧
      ∀ᵐ ω ∂P, Continuous (drive κ B ω) ∧ pathC t (drive κ B ω) ∈ G := by
  obtain ⟨G0, hG0m, hG0, hae0⟩ :=
    Thm14OptB.exists_goodDriverSet' CaraR.revMapCaratheodory hRSS hκ0 hκ4 ht P B hB
  have hq : ∀ q : ℚ, ∃ S : Set C(Icc (0 : ℝ) t, ℝ), MeasurableSet S ∧
      (∀ g ∈ S, 0 < (q : ℝ) → (q : ℝ) < t →
        IsConformallyRemovable (closure (revHull (extIccPath ht.le g) q) ∪
          conj '' closure (revHull (extIccPath ht.le g) q))) ∧
      ∀ᵐ ω ∂P, pathC t (drive κ B ω) ∈ S := by
    intro q
    by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) < t
    · obtain ⟨Gq, hGqm, hGq, haeq⟩ :=
        Thm14OptB.exists_goodDriverSet' CaraR.revMapCaratheodory hRSS hκ0 hκ4 hq.1 P B hB
      refine ⟨resPath hq.2.le ⁻¹' Gq, measurable_resPath hq.2.le hGqm,
        fun g hg _ _ => ?_, ?_⟩
      · have := goodDriver_congr hq.1.le (continuous_extIccPath _ _)
          (continuous_extIccPath ht.le g) (eqOn_extIccPath_resPath hq.1.le hq.2.le g)
          (hGq _ hg)
        exact this.2.2.1
      · filter_upwards [haeq] with ω ⟨hc, hmem⟩
        show resPath hq.2.le (pathC t (drive κ B ω)) ∈ Gq
        rwa [resPath_pathC hq.2.le hc]
    · exact ⟨univ, MeasurableSet.univ, fun g _ h1 h2 => absurd ⟨h1, h2⟩ hq,
        ae_of_all _ fun _ => trivial⟩
  choose S hSm hS hSae using hq
  refine ⟨G0 ∩ ⋂ q, S q, hG0m.inter (MeasurableSet.iInter hSm),
    fun g hg => ⟨hG0 g hg.1, fun q h1 h2 => hS q g (mem_iInter.1 hg.2 q) h1 h2⟩, ?_⟩
  filter_upwards [hae0, ae_all_iff.2 hSae] with ω ⟨hc, h0⟩ hq
  exact ⟨hc, h0, mem_iInter.2 hq⟩

/-! ### Boundary data of `fieldOf x` -/

theorem bdryApprox_fieldOf {x : FieldSample} (hx : BdryConvAE x) (γ : ℝ) (k : ℕ) :
    bdryApprox γ (fieldOf x) k =
      ENNReal.ofReal (Real.exp (γ * (-(x (foldedCircle 0 1))) / 2)) • bdryApprox γ x k := by
  have e : bdryApprox γ (fieldOf x) k = bdryApprox γ (nrm x) k := by
    unfold bdryApprox
    rw [show avgReg (fieldOf x) = avgReg (nrm x) from
      CoordsFull.avgReg_congr_full (E1.coordsFull_fromC (nrm x))]
  rw [e, nrm_eq_addConst, bdryApprox_addConst_ae hx]

theorem qBoundaryMeasure_fieldOf {x : FieldSample} (hx : BdryConvAE x) (γ : ℝ) :
    qBoundaryMeasure γ (fieldOf x) =
      ENNReal.ofReal (Real.exp (γ * (-(x (foldedCircle 0 1))) / 2)) • qBoundaryMeasure γ x := by
  rw [show qBoundaryMeasure γ (fieldOf x) = qBoundaryMeasure γ (nrm x) from
    UnzipFull.qBoundaryMeasure_congr_of_coordsFull γ (E1.coordsFull_fromC (nrm x)), nrm_eq_addConst,
    qBoundaryMeasure_addConst_ae hx]

theorem bCert_fieldOf {x : FieldSample} (hx : BdryConvAE x) {γ : ℝ} (h : E1.M4.BCert γ x) :
    E1.M4.BCert γ (fieldOf x) := by
  set C := ENNReal.ofReal (Real.exp (γ * (-(x (foldedCircle 0 1))) / 2))
  have hC : C ≠ ⊤ := ENNReal.ofReal_ne_top
  simp only [E1.M4.BCert, bdryApprox_fieldOf hx, Measure.smul_apply, smul_eq_mul,
    integral_smul_measure]
  refine ⟨fun k N => ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) (h.1 k N), fun N m => ?_,
    fun N => ?_⟩
  · obtain ⟨l, hl⟩ := h.2.1 N m
    exact ⟨_, hl.const_smul C.toReal⟩
  · obtain ⟨l, hl⟩ := h.2.2 N
    exact ⟨_, hl.const_smul C.toReal⟩

/-! ### The driver reading -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **`Cor15WeldReadStmt`**, conditional on one a.s. regularity input on the unzipped field. -/
theorem cor15WeldRead_of_reg (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t)
    (hreg : ∀ᵐ ω ∂P,
      BdryConvAE (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 ∧
      E1.M4.BCert (Real.sqrt κ)
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 ∧
      qBoundaryMeasure (Real.sqrt κ)
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 (Ici 0) = ⊤) :
    Cor15WeldReadStmt κ t P B X := by
  set γ := Real.sqrt κ
  obtain ⟨B', hB', hind', hae⟩ := ae_coordsFull_unzip_map κ hB hX hind ht.le
  obtain ⟨G, hGm, hgood, hGae⟩ := exists_goodPathRSet hRSS hκ hκ4 ht P B' hB'
  obtain ⟨F, hFm, A, hAm, hEq, hcrit⟩ := exists_weldRead_of_goodSet γ ht hGm hgood
  refine ⟨F, hFm, A, hAm, hEq, ?_⟩
  have h4a := Thm14Wire.theorem1_4a_of_theorem1_3_rss h13 hRSS κ hκ hκ4 t ht P B' X hB' hX hind'
  have hrc := RevCouplingReg.revCouplingBoundaryMeasureRegular κ hκ hκ4 t ht P B' X hB' hX hind'
  filter_upwards [hae, h4a, hGae, hrc, hreg] with ω ⟨_, hC⟩ ⟨⟨_, hw⟩, _⟩ ⟨hc, hmemG⟩
    ⟨hatom, _, _⟩ ⟨hbc, hcert, hinf⟩
  set y := zipCapDown γ t (ofFun (h0rev κ) + X ω, drive κ B ω) with hy
  set V := drive κ B' ω
  have hqy : qBoundaryMeasure γ y.1 =
      qBoundaryMeasure γ (couplingFieldRev κ V t (X ω)) :=
    UnzipFull.qBoundaryMeasure_congr_of_coordsFull _ hC
  have hcertf := bCert_fieldOf hbc hcert
  obtain ⟨ν, hν⟩ := E1.M4.exists_isVagueLimitR_of_bCert hcertf
  have hνe : ν = _ • qBoundaryMeasure γ y.1 :=
    (qBoundaryMeasure_eq hν).symm.trans (qBoundaryMeasure_fieldOf hbc γ)
  refine hcrit _ ⟨zeroMinus V t, pathC t V, hmemG, ?_⟩ ((bdryConvAE_fieldOf_iff y.1).2 hbc)
    hcertf (atomQ_of_atomless hν fun s => ?_) (infQ_of_measure_Ici hν ?_)
  · rw [weldingDataC_eq ht.le CaraR.revMapCaratheodory ht (hgood _ hmemG).1.1
      (hgood _ hmemG).1.2.1, weldingData_congr (extIccPath_pathC ht.le hc)]
    unfold weldingData Thm14WDG.candData
    refine Prod.ext rfl (funext fun q => ?_)
    simp only
    split_ifs with hq
    · rw [← weldHomR_eq_weldReadB1 hbc hν q, hw q hq]
      show weldR γ (couplingFieldRev κ V t (X ω)) q = weldHomR γ y.1 q
      unfold weldR weldHomR
      rw [hqy]
    · rfl
  · rw [hνe, Measure.smul_apply, hqy, hatom s, smul_zero]
  · rw [hνe, Measure.smul_apply, hinf, smul_eq_mul, ENNReal.mul_top]
    exact LocalRule.ofReal_exp_ne_zero _

end Cor15Group
end QuantumZipper
