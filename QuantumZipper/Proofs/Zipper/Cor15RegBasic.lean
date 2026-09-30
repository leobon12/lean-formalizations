import QuantumZipper.Proofs.Zipper.Cor15WRCore
import QuantumZipper.Proofs.LQG.RevCouplingReg
import QuantumZipper.Proofs.LQG.WedgeBdryInfA

/-!
# COR15-HREG: a.s. regularity of the unzipped field (Corollary 1.5 (a), `t > 0`)

For `κ ∈ (0,4)`, `t > 0`, a Brownian motion `B` and an independent free-boundary GFF `X`, almost
surely the unzipped field `y = (zipCapDown √κ t (𝔥₀ + X, √κ B)).1` has
1. boundary circle averages converging at Lebesgue-a.e. real point (`BdryConvAE`),
2. the countable boundary certificate `E1.M4.BCert √κ`,
3. infinite boundary mass on `[0,∞)`.

Route (the one of `RevCouplingReg`, via Theorem 1.2 of Sheffield, *Conformal weldings of random
surfaces: SLE and the quantum gravity zipper*, arXiv:1012.4797, Theorem 1.2 = `B1Full.b1_full`):
the three properties of the normalized field `nrm y` form a measurable event `RegC` of the full
circle coordinates; the normalized coordinates of `y` have the law of those of `Γ⁰ = 𝔥₀ + X`,
for which the event holds a.s.: (1) from the regularity of `Γ⁰`, (2) from
`RevCouplingReg.ae_cert_nrm_gamma0`, (3) from `ν_{Γ⁰} = |t| ν_X` (`AtomlessUncond`) and
`ν_X[1,∞) = ∞` (`WedgeBdry.wedgeBdryFreeInfStmt_holds` with `α = 0`). The normalization is an
additive constant, removed with `bdryApprox_addConst_ae`. The bookkeeping is our own
(elementary).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull

/-! ### Additive constants and coordinate congruences -/

theorem addConst_nrm (y : FieldSample) : addConst (nrm y) (y (foldedCircle 0 1)) = y := by
  funext μ; simp only [nrm, addConst]; ring

theorem bdryConvAE_addConst {x : FieldSample} (hx : BdryConvAE x) (c : ℝ) :
    BdryConvAE (addConst x c) := by
  intro k
  filter_upwards [hx k] with s ⟨l, hl⟩
  exact ⟨l + c, by simpa [addConst, measure_univ] using hl.add_const c⟩

theorem bdryConvAE_congr {x x' : FieldSample} (h : coordsFull x = coordsFull x') :
    BdryConvAE x ↔ BdryConvAE x' := by
  have e : ∀ (n k : ℕ) (s : ℝ), x (foldedCircle (dyadicRoundC n (s : ℂ)) (radius k)) =
      x' (foldedCircle (dyadicRoundC n (s : ℂ)) (radius k)) := fun n k s => by
    rw [CoordsFull.radius_eq_div]; exact coordsFull_apply_eq h n s 1 one_pos k
  unfold BdryConvAE
  simp only [e]

theorem infQ_congr {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x') :
    InfQ γ x ↔ InfQ γ x' := by
  have hb := Factorization.bdryApprox_congr h γ
  simp only [InfQ, Thm14WDG.mIcc, InfMass.Psi, LQGMeas.bdryFun, hb]

theorem bCert_addConst {γ : ℝ} {x : FieldSample} (hx : BdryConvAE x) (h : E1.M4.BCert γ x)
    (c : ℝ) : E1.M4.BCert γ (addConst x c) := by
  set C := ENNReal.ofReal (Real.exp (γ * c / 2))
  have hC : C ≠ ⊤ := ENNReal.ofReal_ne_top
  simp only [E1.M4.BCert, bdryApprox_addConst_ae hx, Measure.smul_apply, smul_eq_mul,
    integral_smul_measure]
  refine ⟨fun k N => ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) (h.1 k N), fun N m => ?_,
    fun N => ?_⟩
  · obtain ⟨l, hl⟩ := h.2.1 N m
    exact ⟨_, hl.const_smul C.toReal⟩
  · obtain ⟨l, hl⟩ := h.2.2 N
    exact ⟨_, hl.const_smul C.toReal⟩

/-! ### The coordinate event -/

/-- The regularity event, read on the full circle coordinates. -/
def RegC (γ : ℝ) : Set (ℕ → ℝ) :=
  {c | BdryConvAE (E1.fromC c) ∧ RevCouplingReg.Cert γ (E1.fromC c) ∧ InfQ γ (E1.fromC c)}

theorem measurableSet_regC (γ : ℝ) : MeasurableSet (RegC γ) :=
  measurableSet_bdryConvAE_fromC.inter
    ((measurableSet_setOfPred.2 ((RevCouplingReg.measurable_cert γ).comp
      measurable_fromC)).inter ((measurableSet_infQ γ).preimage measurable_fromC))

theorem mem_regC_iff (γ : ℝ) (y : FieldSample) :
    coordsFull y ∈ RegC γ ↔ BdryConvAE y ∧ RevCouplingReg.Cert γ y ∧ InfQ γ y := by
  have h := E1.coordsFull_fromC y
  have ha := avgReg_congr_full h
  exact and_congr (bdryConvAE_congr h)
    (and_congr (RevCouplingReg.cert_congr ha) (infQ_congr ha))

/-! ### The `Γ⁰` side -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

theorem ae_regC_gamma0 (hX : IsFreeGFFModConstH X P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∀ᵐ ω ∂P, coordsFull (nrm (ofFun (h0rev κ) + X ω)) ∈ RegC (Real.sqrt κ) := by
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hκ.le hκ4
  have hQ : (0 : ℝ) < Qc (Real.sqrt κ) := by unfold Qc; positivity
  filter_upwards [RevCouplingReg.ae_cert_nrm_gamma0 hX hκ hκ4,
    AtomlessUncond.ae_gamma0_logSingularity hX hκ hκ4, RegSample.ae_isRegularSample hX,
    WedgeBdry.wedgeBdryFreeInfStmt_holds P X hX _ hγ hγ2 0 hQ] with ω hcert hlog hreg hinf
  have hYreg : IsRegularSample (ofFun (h0rev κ) + X ω) := by
    rw [AtomlessUncond.gamma0_decomp κ (X ω)]
    exact ((hreg.addConst' _).add_ofFun_log' (-2 / Real.sqrt κ) 0).add_ofFun' continuousOn_const
  have hbc : BdryConvAE (ofFun (h0rev κ) + X ω) := fun k => Eventually.of_forall fun s =>
    hYreg.rawConverges k (s : ℂ) (by simp [Hbar])
  refine (mem_regC_iff _ _).2 ⟨bdryConvAE_addConst hbc _, hcert, ?_⟩
  obtain ⟨ν, hν, -⟩ := RevCouplingReg.good_of_cert hcert
  refine infQ_of_measure_Ici hν ?_
  rw [← qBoundaryMeasure_eq hν, nrm, qBoundaryMeasure_addConst_ae hbc, Measure.smul_apply,
    smul_eq_mul, hlog.2.1]
  refine ENNReal.mul_eq_top.2 (Or.inl ⟨LocalRule.ofReal_exp_ne_zero _, ?_⟩)
  rw [withDensity_apply _ measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  refine top_le_iff.1 ?_
  rw [← hinf]
  calc ∫⁻ t in Ici (1 : ℝ), ENNReal.ofReal (t ^ (-(0 * Real.sqrt κ / 2)))
        ∂qBoundaryMeasure (Real.sqrt κ) (X ω)
      ≤ ∫⁻ t in Ici (1 : ℝ), ENNReal.ofReal |t| ∂qBoundaryMeasure (Real.sqrt κ) (X ω) :=
        setLIntegral_mono (by fun_prop) fun t ht => ENNReal.ofReal_le_ofReal (by
          rw [show -(0 * Real.sqrt κ / 2) = (0 : ℝ) by ring, Real.rpow_zero]
          exact (show (1 : ℝ) ≤ t from ht).trans (le_abs_self t))
    _ ≤ ∫⁻ t in Ici (0 : ℝ) ∩ {0}ᶜ, ENNReal.ofReal |t|
        ∂qBoundaryMeasure (Real.sqrt κ) (X ω) := by
        refine lintegral_mono_set fun t (ht : (1 : ℝ) ≤ t) => ⟨?_, ?_⟩
        · show (0 : ℝ) ≤ t; linarith
        · show t ≠ 0; intro h0; rw [h0] at ht; norm_num at ht

/-! ### The unzipped side, by the law transfer of Theorem 1.2 -/

theorem ae_regC_unzip {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, coordsFull (nrm (zipCapDown (Real.sqrt κ) t
      (ofFun (h0rev κ) + X ω, drive κ B ω)).1) ∈ RegC (Real.sqrt κ) := by
  have hlaw := b1_full κ hκ P B X hB hX hind ht
  have hF1 := B2.aemeasurable_data_unzip (κ := κ) hB hX hind ht.le
  have hF0 := B2.aemeasurable_data0 (κ := κ) hB hX
  have hA : MeasurableSet {p : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) |
      p.1.1 ∈ RegC (Real.sqrt κ)} :=
    (measurableSet_regC _).preimage (measurable_fst.comp measurable_fst)
  have h0side : ∀ᵐ p ∂(P.map fun ω => (lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω,
      fun s : ℝ≥0 => drive κ B ω s)), p.1.1 ∈ RegC (Real.sqrt κ) :=
    (ae_map_iff hF0 (p := fun p : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) =>
      p.1.1 ∈ RegC (Real.sqrt κ)) hA).2 (ae_regC_gamma0 hX hκ hκ4)
  rw [← hlaw] at h0side
  exact ae_of_ae_map hF1 h0side

/-- **COR15-HREG (1).** The regularity input `hreg` of `cor15WeldRead_of_reg`. -/
theorem ae_reg_zipCapDown {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P,
      BdryConvAE (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 ∧
      E1.M4.BCert (Real.sqrt κ)
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 ∧
      qBoundaryMeasure (Real.sqrt κ)
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 (Ici 0) = ⊤ := by
  filter_upwards [ae_regC_unzip hκ hκ4 hB hX hind ht] with ω hω
  generalize (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 = y at hω ⊢
  obtain ⟨hb, hc, hi⟩ := (mem_regC_iff _ _).1 hω
  obtain ⟨ν, hν, -⟩ := RevCouplingReg.good_of_cert hc
  have e := addConst_nrm y
  refine ⟨?_, ?_, ?_⟩
  · rw [← e]; exact bdryConvAE_addConst hb _
  · rw [← e]; exact bCert_addConst hb (E1.M4.bCert_of_isVagueLimitR hc.1 hν) _
  · rw [← e, qBoundaryMeasure_addConst_ae hb, Measure.smul_apply, smul_eq_mul,
      qBoundaryMeasure_eq hν, measure_Ici_eq_top_of_infQ hν hi,
      ENNReal.mul_top (LocalRule.ofReal_exp_ne_zero _)]

end Cor15Group
end QuantumZipper
