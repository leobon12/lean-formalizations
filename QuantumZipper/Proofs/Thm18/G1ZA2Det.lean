import QuantumZipper.Proofs.Thm18.G1ZA2Meas
import QuantumZipper.Proofs.Thm18.G1ZA1bArea

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A2, part 2: the deterministic choice-independence chain

Sheffield, arXiv:1012.4797, proof of Thm 1.8 (pp. 69–71): the canonical description of a side
surface does not depend on the choice of uniformizer (the chart is unique up to a positive
dilation, and `canonical` removes it). Own bookkeeping, following `G1Z2MeasMain` (`hkey`) and
`G1ZA1bMain`.

`g1za2_det`: for a configuration `c` with a good driver, whose (path, data) pair `pc` satisfies
`G1RegGood` and whose selected pulled-back field `xc pc` has the measure package
`G1Z2MeasGood`, the rerooted local data and the canonical data of the side field of `c`
(chosen `Classical.epsilon` uniformizer) are those of `x = xc pc`.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA2

open D3Plus Factorization

/-- The path `a` with `W = γ a` on `[0,∞)`. -/
def aOf (γ : ℝ) (W : ℝ → ℝ) : ℝ≥0 → ℝ := fun t => W t / γ

/-- The path-data pair of a configuration. -/
def pOf (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) : G1PathData :=
  (aOf γ c.2, WedgeMeas.dataFull H c.1)

theorem pathTrace_aOf {γ : ℝ} (hγ : 0 < γ) {W : ℝ → ℝ} (hW : ∀ s, W s = W (max s 0)) :
    pathTrace (γ ^ 2) (aOf γ W) = trace W := by
  unfold pathTrace aOf
  congr 1
  funext t
  rw [Real.sqrt_sq hγ.le, Real.coe_toNNReal', ← hW t]
  field_simp

theorem continuous_aOf {γ : ℝ} {W : ℝ → ℝ} (hW : Continuous W) : Continuous (aOf γ W) :=
  (hW.comp NNReal.continuous_coe).div_const γ

theorem isNormalizedUniformizer_sideDom' {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool) :
    IsNormalizedUniformizer (sideDom η left) (uniformizer (sideDom η left)) := by
  unfold uniformizer
  cases left
  · exact Classical.epsilon_spec (CA.Uniformizer.exists_normalizedUniformizer_rightComponent hη)
  · exact Classical.epsilon_spec (CA.Uniformizer.exists_normalizedUniformizer_leftComponent hη)

/-- **Choice independence, deterministic form.** -/
theorem g1za2_det {γ : ℝ} (hγ : 0 < γ) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) (ℓ : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞)
    {c : FieldSample × (ℝ → ℝ)} (hW : G1zDrvGood c.2) (hreg : G1RegGood γ (pOf γ c))
    (hM : G1Z2MeasGood γ left (xc γ Ψ left (pOf γ c))) :
    IsRegularSample (xc γ Ψ left (pOf γ c)) ∧ G1ZAreaEx γ (xc γ Ψ left (pOf γ c)) ∧
    g1zRerootF γ left ℓ R Γ c =
      Γ (locFieldFull R (canonical γ (translate (xc γ Ψ left (pOf γ c))
        (g1SidePt γ left (xc γ Ψ left (pOf γ c)) ℓ : ℂ)))) ∧
    WedgeMeas.dataFull H (canonical γ (g1CfgSideField γ left c)) =
      WedgeMeas.dataFull H (canonical γ (xc γ Ψ left (pOf γ c))) := by
  obtain ⟨hWc, -, hWmax, hη, -⟩ := hW
  have htr : pathTrace (γ ^ 2) (aOf γ c.2) = trace c.2 := pathTrace_aOf hγ hWmax
  have hcont : Continuous (pOf γ c).1 := continuous_aOf hWc
  have hη' : IsSimpleChord (pathTrace (γ ^ 2) (pOf γ c).1) := by
    show IsSimpleChord (pathTrace (γ ^ 2) (aOf γ c.2))
    rw [htr]; exact hη
  obtain ⟨φ, hφ, hcore⟩ := hreg hcont hη' c.1 rfl left
  obtain ⟨φ₀, hφ₀, hΨe⟩ := hΨ.2.2 (pOf γ c).1 hcont hη' left
  have e1 : pathTrace (γ ^ 2) (pOf γ c).1 = trace c.2 := htr
  rw [e1] at hφ hcore hφ₀ hΨe
  have hu : IsNormalizedUniformizer (sideDom (trace c.2) left)
      (uniformizer (sideDom (trace c.2) left)) := isNormalizedUniformizer_sideDom' hη left
  have hcore' : G1.ChoiceRegularCore γ c.1 (invFunOn φ₀ (sideDom (trace c.2) left)) :=
    G1.choiceRegularCore_invFunOn_of_normalized hη left hφ hφ₀ hcore
  have hxeq : xc γ Ψ left (pOf γ c) =
      coordChange c.1 (invFunOn φ₀ (sideDom (trace c.2) left)) (Qc γ) := by
    rw [← hΨe]
    exact (g1z2_coordChange_congr (Cor15Group.regEq_fromC_coordsFull c.1) _ _).symm
  rw [hxeq] at hM ⊢
  have hx : G1Z2Good γ left (coordChange c.1 (invFunOn φ₀ (sideDom (trace c.2) left)) (Qc γ)) :=
    g1z2Good_of_core hcore' hM
  have hD : IsOpen (sideDom (trace c.2) left) := G1.isOpen_component hη left
  obtain ⟨hψd, hψ0, hψm, -⟩ := G1.invFunOn_props hD hφ₀
  have hint := G1.choiceRegular_logDeriv hD hφ₀
  obtain ⟨b, hb, hbeq⟩ := g1z2_invFunOn_eq_dilate hη left hφ₀ hu
  have hZ : RegEq (g1CfgSideField γ left c)
      (rescale (coordChange c.1 (invFunOn φ₀ (sideDom (trace c.2) left)) (Qc γ)) (Qc γ) b) :=
    g1z2_regEq_dilate c.1 (Qc γ) hψd hψ0 hψm hb hbeq hint hcore'.2.1
  obtain ⟨-, ⟨μ, hμ, hsm, htop⟩, -, -⟩ := id hx
  obtain ⟨F, hF⟩ := hcore'.1
  refine ⟨⟨F, hF⟩, ⟨μ, g1z2_isVagueLimitOn_of_hasAreaLimit hF hμ⟩, ?_, ?_⟩
  · unfold g1zRerootF
    rw [g1z2_rerootData_rescale hγ hx hb hZ R ℓ]
  · rw [Factorization.canonical_congr (funext fun k => funext fun z => hZ k z) γ]
    obtain ⟨hsmall, hbig⟩ := g1z2_translate_mass 0 (hsm 0) htop
    have hmap : (μ.map fun z : ℂ => z - ((0 : ℝ) : ℂ)) = μ := by
      simp only [Complex.ofReal_zero, sub_zero, Measure.map_id']
    rw [hmap] at hsmall hbig
    have hs := g1z2_scaleParam_pos hcore'.1 hμ hsmall hbig
    exact G1ZA1b.g1za1b_dataFull_canonical_rescale hγ hcore'.1 hμ hb hs
      fun ρ σ hσ => G1ZA1b.g1za1b_scaleConsistent_of_core hcore' hb (div_pos hs hb) ρ σ hσ

end G1ZA2
end Thm18Asm
end QuantumZipper
