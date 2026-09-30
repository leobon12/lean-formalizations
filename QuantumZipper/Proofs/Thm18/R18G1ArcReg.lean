import QuantumZipper.Proofs.Thm18.R18G1ArcDefs
import QuantumZipper.Proofs.Thm18.G1ZA1bArea
import QuantumZipper.Proofs.Thm18.G1Z2MeasMain
import QuantumZipper.Proofs.Thm18.G1CoreScale
import QuantumZipper.Proofs.Thm18.G1FM2Final

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G1ARC: A1b with open arcs (`G1RerootRegArcStmt`)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8,
pp. 69–71: after unzipping by quantum length `ℓ` the side surface is the old one, rerooted; the
conformal map between the two side uniformizations is affine (A1a), so the canonical
descriptions agree.

Verbatim copy of `Thm18Asm.g1RerootRegStmt_of` (G1ZA1bMain.lean) under the substitution rule
(`zipLenDown ↦ zipLenDownArc`, `unzipTime ↦ lenTimeArc`, `unzipScale ↦ unzipScaleArc`); the
argument does not depend on how the unzipping time is chosen.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen

/-- **A1b (open arcs)** from the pushed-circle node and the area part of the side goodness node. -/
theorem g1RerootRegArcStmt_of (hN : G1ZA1bSideExactArcStmt) (hG : G1Z2SideGoodStmt) :
    G1RerootRegArcStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ left
  have hγ : 0 < γ := hS.1
  have hR : G1RegExSide γ P B Y left := by
    have := g1RegExStmt_of_rest g1RegRepRestStmt_holds γ P B Y hS hIn
    cases left
    · exact this.2
    · exact this.1
  filter_upwards [hN γ P B Y hS hIn ℓ hℓ left, hG γ P B Y hS hIn left, hR, hIn.2.2]
    with ω hNω hGω hRω hin
  intro lam β hlam hEq
  obtain ⟨φ, hφ, hcore⟩ := hRω
  have hU : IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)
      (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)) := by
    cases left
    · exact hin.2.2.2
    · exact hin.2.2.1
  set ψ := invFunOn (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left))
    (sideDom (sleTrace (γ ^ 2) B ω) left) with hψ
  have hcore' : G1.ChoiceRegularCore γ (Y ω) ψ :=
    G1.choiceRegularCore_invFunOn_of_normalized hin.1 left hφ hU hcore
  obtain ⟨hψd, hψ0, hψm, -⟩ := G1.invFunOn_props (G1.isOpen_component hin.1 left) hU
  have hint := G1.choiceRegular_logDeriv (G1.isOpen_component hin.1 left) hU
  obtain ⟨⟨μ, hμ, hsm, htop⟩, -⟩ := hGω _ hU
  -- positivity of the unzipping scale, from the affine identity and injectivity of `ψ`
  have hmemH : ∀ s : ℝ, 0 < s → Complex.I * (s : ℂ) / (lam : ℂ) ∈ H := fun s hs => by
    show 0 < (Complex.I * (s : ℂ) / (lam : ℂ)).im
    rw [Complex.div_ofReal_im]
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    exact div_pos hs hlam
  have ha : 0 < unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) := by
    have h0 : 0 ≤ unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) := by
      unfold unzipScaleArc scaleParam
      exact Real.sInf_nonneg fun x hx => hx.1.le
    refine lt_of_le_of_ne h0 fun h => ?_
    have hinj : InjOn ψ H := by
      have := Function.invFunOn_injOn_image (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left))
        (sideDom (sleTrace (γ ^ 2) B ω) left)
      rwa [hU.1.image_eq] at this
    have hH : ∀ s : ℝ, 0 < s → Complex.I * (s : ℂ) ∈ H := fun s hs => by
      show 0 < (Complex.I * (s : ℂ)).im
      simpa using hs
    have e1 := hEq (hH 1 one_pos)
    have e2 := hEq (hH 2 two_pos)
    simp only [← h, Complex.ofReal_zero, zero_mul] at e1 e2
    have key := hinj (hmemH 1 one_pos) (hmemH 2 two_pos) (e1.symm.trans e2)
    have := congrArg Complex.im key
    rw [Complex.div_ofReal_im, Complex.div_ofReal_im] at this
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add] at this
    rw [div_eq_div_iff hlam.ne' hlam.ne'] at this
    nlinarith
  -- the field identity up to `RegEq`
  have hGm : Measurable fun u : ℂ => ψ (u / (lam : ℂ)) :=
    hψm.comp (measurable_id.div_const _)
  have h1 := G1ZA1b.g1za1b_regEq_translate (Y ω)
    (g1CfgSideField γ left (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω))) (Qc γ)
    (Φ := fun u => fwdMapInv (drive (γ ^ 2) B ω) (lenTimeArc γ ℓ (wedgeConfig γ B Y ω))
      ((unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) : ℂ) *
        g1zSideMap left (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω)).2 u))
    β hGm hEq (hNω ha)
  have e : (fun u : ℂ => ψ (u / (lam : ℂ))) = fun w => ψ (((lam⁻¹ : ℝ) : ℂ) * w) := by
    funext w
    congr 1
    push_cast
    ring
  have h2 : RegEq (coordChange (Y ω) (fun u : ℂ => ψ (u / (lam : ℂ))) (Qc γ))
      (rescale (coordChange (Y ω) ψ (Qc γ)) (Qc γ) lam⁻¹) := by
    rw [e]
    exact G1.regEq_coordChange_comp_mul (Y ω) (Qc γ) hψd hψ0 hψm (inv_pos.2 hlam) hint
      hcore'.2.1
  have hcan : canonical γ (translate (g1CfgSideField γ left
      (zipLenDownArc γ ℓ (wedgeConfig γ B Y ω))) (β : ℂ)) =
      canonical γ (rescale (coordChange (Y ω) ψ (Qc γ)) (Qc γ) lam⁻¹) :=
    S5.FieldShift.canonical_congr (fun k z => (h1 k z).trans (h2 k z)) γ
  rw [hcan]
  -- area-only choice independence
  obtain ⟨hsmall, hbig⟩ := g1z2_translate_mass 0 (hsm 0) htop
  have hmap : (μ.map fun z : ℂ => z - ((0 : ℝ) : ℂ)) = μ := by
    simp only [Complex.ofReal_zero, sub_zero, Measure.map_id']
  rw [hmap] at hsmall hbig
  have hs := g1z2_scaleParam_pos hcore'.1 hμ hsmall hbig
  exact (G1ZA1b.g1za1b_dataFull_canonical_rescale hγ hcore'.1 hμ (inv_pos.2 hlam) hs
    fun ρ σ hσ => G1ZA1b.g1za1b_scaleConsistent_of_core hcore' (inv_pos.2 hlam)
      (div_pos hs (inv_pos.2 hlam)) ρ σ hσ).symm

end R18
end QuantumZipper
