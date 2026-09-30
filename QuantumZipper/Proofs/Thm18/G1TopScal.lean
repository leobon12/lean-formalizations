import QuantumZipper.Proofs.Thm18.G1TopMeas
import QuantumZipper.Proofs.Thm18.G1ZB2CLaw
import QuantumZipper.Proofs.Thm18.G1ZB2CGeom
import QuantumZipper.Proofs.Thm18.G1Side3Scal
import QuantumZipper.Proofs.Thm18.G1Side3Rep
import QuantumZipper.Proofs.Thm18.G4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1TOP (2): the scaling argument — the side domain has infinite quantum area

Sheffield, arXiv:1012.4797, §1.6 / proof of Theorem 1.8 (the side of the curve is an
infinite-area surface): for the Theorem 1.8 configuration `(Y, W = √κ B)` and a constant `C`, the
canonicalized shifted configuration `canonConfig γ (Y + C, W) = (canonical (Y + C), W(λ²·)/λ)`,
`λ = scaleParam γ (Y + C)`, has the configuration law of `(Y, W)` (`canonConfig_shift_facts`,
from the proved B4(c) `F1.wedgeAddConstLawStmt_holds`; DMS arXiv:1409.7055 Prop. 4.6, SLE scale
invariance). Its side domain is `λ⁻¹ D` (`g1zB2c_mem_sideDom`, `RS.trace_scale`) and its area
measure satisfies `μ'(λ⁻¹ D) = e^{γC} μ_Y(D)` (`qAreaMeasure_canonical_addConst_apply`). Hence the
side area `X = μ_Y(D)` — a measurable function of the configuration data (`cfgArea`,
G1TopMeas.lean) — satisfies `law(e^{γC} X) = law(X)`, so `X ∈ {0, ∞}` a.s.
(`G1Side.ae_zero_or_top_of_scaleInv`), and `X > 0` (positivity of the area on open sets) gives
`X = ∞` (`ae_cfgArea_top`). Own bookkeeping around the cited facts.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Top

open Thm18Asm G1Side

/-- The selected map sends `ℍ` onto the side domain. -/
theorem image_sel {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ}
    (hc : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool) :
    Ψ left a '' H = sideDom (pathTrace (γ ^ 2) a) left := by
  obtain ⟨φ, hφ, hΨa⟩ := hΨ.2.2 a hc hs left
  rw [hΨa]
  have hb := hφ.1
  exact (hb.invOn_invFunOn.symm.bijOn hb.surjOn.mapsTo_invFunOn hb.mapsTo).image_eq

/-- The Brownian path read off a good driver. -/
theorem drvPath_facts {γ : ℝ} (hγ : 0 < γ) {W : ℝ → ℝ} (hW : G1zDrvGood W) :
    Continuous (fun t : ℝ≥0 => W t / γ) ∧
      pathTrace (γ ^ 2) (fun t : ℝ≥0 => W t / γ) = trace W := by
  have hsq : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hγ.le
  refine ⟨(hW.1.comp NNReal.continuous_coe).div_const γ, ?_⟩
  unfold pathTrace
  congr 1
  funext t
  simp only [hsq, Real.coe_toNNReal']
  rw [mul_div_cancel₀ _ hγ.ne', ← hW.2.2.1 t]

/-- The side domain of a good driver is a nonempty open subset of `ℍ`. -/
theorem sideDom_facts {γ : ℝ} (hγ : 0 < γ) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    {W : ℝ → ℝ} (hW : G1zDrvGood W) (left : Bool) :
    IsOpen (sideDom (trace W) left) ∧ sideDom (trace W) left ⊆ H ∧
      (sideDom (trace W) left).Nonempty := by
  obtain ⟨hc, htr⟩ := drvPath_facts hγ hW
  have hs : IsSimpleChord (pathTrace (γ ^ 2) (fun t : ℝ≥0 => W t / γ)) := htr ▸ hW.2.2.2.1
  obtain ⟨-, -, -, hH, -⟩ := sideMapFacts_of_sel hΨ hc hs left
  have hi := image_sel hΨ hc hs left
  rw [htr] at hi
  refine ⟨G1.isOpen_component hW.2.2.2.1 left, ?_, ?_⟩
  · rw [← hi]; exact hH.image_subset
  · rw [← hi]
    exact ⟨_, Complex.I, by show (0 : ℝ) < Complex.I.im; simp, rfl⟩

/-- The side-area functional of configuration data (driver `W = γ a`). -/
def cfgArea (γ : ℝ) (ψ : (ℝ≥0 → ℝ) → ℂ → ℂ)
    (d : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  areaFn γ ψ (fun t => d.2 t / γ, d.1)

theorem measurable_cfgArea (γ : ℝ) {ψ : (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hψ : ∀ w : ℂ, Measurable fun a => ψ a w) : Measurable (cfgArea γ ψ) :=
  (measurable_areaFn γ hψ).comp ((measurable_pi_iff.2 fun t =>
    ((measurable_pi_apply t).comp measurable_snd).div_const γ).prodMk measurable_fst)

/-- **The functional is the side area** at a good field and a good driver. -/
theorem cfgArea_eq {γ : ℝ} (hγ : 0 < γ) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) {y : FieldSample} (hy : IsLQGGood γ y) {W : ℝ → ℝ} (hW : G1zDrvGood W) :
    cfgArea γ (Ψ left) (WedgeMeas.dataFull H y, fun t : ℝ≥0 => W t) =
      qAreaMeasure γ y (sideDom (trace W) left) := by
  obtain ⟨hc, htr⟩ := drvPath_facts hγ hW
  have hs : IsSimpleChord (pathTrace (γ ^ 2) (fun t : ℝ≥0 => W t / γ)) := htr ▸ hW.2.2.2.1
  obtain ⟨-, hd, -, hH, -⟩ := sideMapFacts_of_sel hΨ hc hs left
  unfold cfgArea
  rw [areaFn_eq, muY_dataFull hy]
  show qAreaMeasure γ y (Prod.mk (fun t : ℝ≥0 => W t / γ) ⁻¹' imgSet (Ψ left)) = _
  rw [imgSet_section hd.continuousOn hH, image_sel hΨ hc hs left, htr]

/-- **The side area is infinite** in the Theorem 1.8 setting, given positivity of the area on
open sets. -/
theorem ae_cfgArea_top {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool)
    (hpos : ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < qAreaMeasure γ (Y ω) V) :
    ∀ᵐ ω ∂P, cfgArea γ (Ψ left) (cfgData (wedgeConfig γ B Y ω)) = ⊤ := by
  have hIn := thm18Inputs_of_setting hS
  have hγ : 0 < γ := hS.1
  have hγ2 : γ < 2 := hS.2.1
  have hB : IsBrownianReal B P := hS.2.2.1
  have hψm : ∀ w, Measurable fun a => Ψ left a w := fun w =>
    (hΨ.1 left).comp (measurable_id.prodMk measurable_const)
  have hF := measurable_cfgArea γ hψm
  set D := fun ω => cfgData (wedgeConfig γ B Y ω) with hDdef
  have hD : AEMeasurable D P := aemeasurable_cfgData_wedgeConfig hS hIn
  set Z := fun ω => cfgArea γ (Ψ left) (D ω) with hZdef
  have hZ : AEMeasurable Z P := hF.comp_aemeasurable hD
  have hWg := ae_g1zDrvGood_of_brownian hγ hγ2 hB
  have hval : ∀ᵐ ω ∂P, Z ω = qAreaMeasure γ (Y ω) (sideDom (trace (drive (γ ^ 2) B ω)) left) := by
    filter_upwards [hIn.1, hWg] with ω hg hW
    exact cfgArea_eq hγ hΨ left hg.1 hW
  have hscal : ∀ C : ℝ,
      P.map (fun ω => ENNReal.ofReal (Real.exp (γ * C)) * Z ω) = P.map Z := by
    intro C
    obtain ⟨hsp, hlaw, hmc, hgood''⟩ := canonConfig_shift_facts hS C
    set c'' := fun ω => canonConfig γ (addConst (Y ω) C, drive (γ ^ 2) B ω) with hc''
    have hlaw2 : P.map (fun ω => cfgArea γ (Ψ left) (g1zCfgData (c'' ω))) = P.map Z := by
      calc P.map (fun ω => cfgArea γ (Ψ left) (g1zCfgData (c'' ω)))
          = (P.map fun ω => g1zCfgData (c'' ω)).map (cfgArea γ (Ψ left)) :=
            (AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hmc).symm
        _ = (configLawFull c'' P).map (cfgArea γ (Ψ left)) := rfl
        _ = (configLawFull (wedgeConfig γ B Y) P).map (cfgArea γ (Ψ left)) := by rw [hlaw]
        _ = (P.map D).map (cfgArea γ (Ψ left)) := rfl
        _ = P.map Z := AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hD
    have hpt : ∀ᵐ ω ∂P, cfgArea γ (Ψ left) (g1zCfgData (c'' ω)) =
        ENNReal.ofReal (Real.exp (γ * C)) * Z ω := by
      filter_upwards [hIn.1, hWg, hsp, hgood'', hval] with ω hg hW hs hW'' hv
      have hg'' : IsLQGGood γ (canonical γ (addConst (Y ω) C)) := (hg.1.addConst C).rescale hγ hs
      have h1 : cfgArea γ (Ψ left) (g1zCfgData (c'' ω)) =
          qAreaMeasure γ (canonical γ (addConst (Y ω) C)) (sideDom (trace (c'' ω).2) left) :=
        cfgArea_eq hγ hΨ left hg'' hW''
      rw [h1, hv]
      have hDD := g1zB2c_mem_sideDom hW hs left
      have hmD : MeasurableSet (sideDom (trace (c'' ω).2) left) :=
        (G1.isOpen_component hW''.2.2.2.1 left).measurableSet
      rw [qAreaMeasure_canonical_addConst_apply hγ hg.1 C hs hmD]
      congr 2
      ext z
      simp only [mem_preimage]
      have hsc : ((scaleParam γ (addConst (Y ω) C) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      have e : ((scaleParam γ (addConst (Y ω) C) : ℝ) : ℂ) *
          (z / ((scaleParam γ (addConst (Y ω) C) : ℝ) : ℂ)) = z := by field_simp
      have := hDD (z / ((scaleParam γ (addConst (Y ω) C) : ℝ) : ℂ))
      rw [e] at this
      exact this
    rw [← hlaw2]
    exact Measure.map_congr (hpt.mono fun ω h => h.symm)
  have hposZ : ∀ᵐ ω ∂P, 0 < Z ω := by
    filter_upwards [hval, hpos, hWg] with ω hv hp hW
    obtain ⟨ho, hsub, hne⟩ := sideDom_facts hγ hΨ hW left
    rw [hv]; exact hp _ ho hsub hne
  set c0 : ℝ≥0∞ := ENNReal.ofReal (Real.exp γ) with hc0
  have hc1 : 1 < c0 := by
    rw [hc0, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos γ)).2 (by have := Real.exp_lt_exp.2 hγ; rwa [Real.exp_zero] at this)
  have hinv : ∀ m : ℕ, P.map (fun ω => c0 ^ m * hZ.mk Z ω) = P.map (hZ.mk Z) := by
    intro m
    have e : c0 ^ m = ENNReal.ofReal (Real.exp (γ * m)) := by
      rw [hc0, ← ENNReal.ofReal_pow (Real.exp_pos γ).le, ← Real.exp_nat_mul, mul_comm]
    calc P.map (fun ω => c0 ^ m * hZ.mk Z ω) = P.map (fun ω => c0 ^ m * Z ω) :=
          Measure.map_congr (hZ.ae_eq_mk.mono fun ω h => by simp only [h])
      _ = P.map Z := by rw [e]; exact hscal m
      _ = P.map (hZ.mk Z) := Measure.map_congr hZ.ae_eq_mk
  filter_upwards [ae_zero_or_top_of_scaleInv hZ.measurable_mk hc1 ENNReal.ofReal_ne_top hinv,
    hZ.ae_eq_mk, hposZ] with ω h1 h2 h3
  show Z ω = ⊤
  rw [h2] at h3 ⊢
  rcases h1 with h | h
  · rw [h] at h3; exact absurd h3 (lt_irrefl 0)
  · exact h

end G1Top
end QuantumZipper
