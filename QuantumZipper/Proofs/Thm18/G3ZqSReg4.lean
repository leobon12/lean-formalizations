import QuantumZipper.Proofs.Thm18.G3ZqSReg3
import QuantumZipper.Proofs.Thm18.G1CoreScale
import QuantumZipper.Proofs.Thm18.G3ZrCmp2
import QuantumZipper.Proofs.Thm18.G3Z2b2Dil2
import QuantumZipper.Proofs.Zipper.RegShiftUnifBasic
import QuantumZipper.Proofs.Zipper.F2Gamma0Trunc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3ZqS (6): the choice regularity of the unscaled field along the unscaled path

For the unscaled wedge `W` (scale `b`, `canonical W = rescale W Q b`) and a good path `a`, let
`φ_a` be the selected normalized uniformizer of the side domain `D_a` (`Ψ_a = φ_a⁻¹`). Then
`φ'' = φ_a(b ·)` is a normalized uniformizer of the side domain of the scaled path `S_b a`
(`G1Zm.isNormalizedUniformizer_dil`) with `b · φ''⁻¹ = Ψ_a` on `ℍ` (`bInv_eq`). By
`G3Zr.raw_rescale_side` the pulled-back fields `coordChange W Ψ_a Q` and
`coordChange (canonical W) φ''⁻¹ Q` have the same values at every folded circle, so the
regularity core and the area limit of the latter (setting-level results for the canonical wedge
and the scaled path, `thm18Setting_rs`) are those of the former (`core_of_fc_eq`,
`hasAreaLimit_of_fc_eq`); Z-REG's `choiceRegularA_translate` then gives the area-only choice
regularity at every point. The unscaled length partner is `b ×` the canonical one
(`g3zPartner_rescale`).

Headline: **`g3ZqSChoiceUStmt_holds`**, hence **`g3ZqResclRegStmt_holds : G3ZqResclRegStmt`**.
Sheffield, arXiv:1012.4797, p. 70. Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqS

open G1Zm G3Zq G3Zr G3Z2b2 G1SSR2

/-! ## Transfer along equality at folded circles -/

theorem avgReg_eq_of_fc {Z₁ Z₂ : FieldSample}
    (h : ∀ (d : ℂ) (r : ℝ), 0 < r → Z₁ (foldedCircle d r) = Z₂ (foldedCircle d r)) :
    avgReg Z₁ = avgReg Z₂ := by
  funext k z
  unfold avgReg
  congr 1
  funext n
  exact h _ _ (radius_pos k)

theorem core_of_fc_eq {γ : ℝ} {y₁ y₂ : FieldSample} {ψ₁ ψ₂ : ℂ → ℂ}
    (hc : G1.ChoiceRegularCore γ y₁ ψ₁)
    (h : ∀ (d : ℂ) (r : ℝ), 0 < r →
      coordChange y₂ ψ₂ (Qc γ) (foldedCircle d r) = coordChange y₁ ψ₁ (Qc γ) (foldedCircle d r)) :
    G1.ChoiceRegularCore γ y₂ ψ₂ := by
  have ha := avgReg_eq_of_fc h
  have he : ∀ ν, evalReg (coordChange y₂ ψ₂ (Qc γ)) ν = evalReg (coordChange y₁ ψ₁ (Qc γ)) ν :=
    fun ν => F2.evalReg_congr_avgReg ha ν
  obtain ⟨⟨F, hF⟩, h2, h3⟩ := hc
  refine ⟨⟨F, RegUnif.isRegularWith_of_raw_eq (fun n k z => h _ _ (radius_pos k)) hF⟩,
    fun d hd r hr => ?_, fun c hc ρ σ hσ => ?_⟩
  · rw [he, h d r hr]; exact h2 d hd r hr
  · simp_rw [he]; exact h3 c hc ρ σ hσ

theorem hasAreaLimit_of_fc_eq {γ : ℝ} {Z₁ Z₂ : FieldSample} {μ : Measure ℂ}
    (hμ : HasAreaLimit γ Z₁ μ)
    (h : ∀ (d : ℂ) (r : ℝ), 0 < r → Z₂ (foldedCircle d r) = Z₁ (foldedCircle d r)) :
    HasAreaLimit γ Z₂ μ := by
  have ha := avgReg_eq_of_fc h
  have hR : ∀ r, areaR γ Z₂ r = areaR γ Z₁ r := by
    intro r
    unfold areaR areaDens
    simp_rw [F2.evalReg_congr_avgReg ha]
  obtain ⟨h1, h2, h3⟩ := hμ
  exact ⟨h1, h2, fun f hf hfc hfH => by simp_rw [hR]; exact h3 f hf hfc hfH⟩

/-! ## The dilated uniformizer -/

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **The dilated uniformizer of the scaled side domain.** -/
theorem exists_dilUnif {γ : ℝ} {b : ℝ} (hb : 0 < b) {a : ℝ≥0 → ℝ}
    (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (hWd : Continuous (pathDrive (γ ^ 2) a))
    (hW0 : pathDrive (γ ^ 2) a 0 = 0)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv (pathDrive (γ ^ 2) a) t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))
    (left : Bool) {φ : ℂ → ℂ} (hφ : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) a) left) φ) :
    ∃ φ'' : ℂ → ℂ,
      IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) (scalePath b a)) left) φ'' ∧
      ∀ w ∈ H, (b : ℂ) * invFunOn φ'' (sideDom (pathTrace (γ ^ 2) (scalePath b a)) left) w =
        invFunOn φ (sideDom (pathTrace (γ ^ 2) a) left) w := by
  set D := sideDom (pathTrace (γ ^ 2) a) left with hDdef
  set D' := sideDom (pathTrace (γ ^ 2) (scalePath b a)) left with hD'def
  have hD : ∀ w, w ∈ D' ↔ (((b⁻¹ : ℝ) : ℂ))⁻¹ * w ∈ D :=
    mem_sideDom_dil (inv_pos.2 hb) (mem_pathTrace_scalePath hb a hWd hW0 hex) left
  have hN'' := isNormalizedUniformizer_dil hφ (inv_pos.2 hb) hD
  refine ⟨_, hN'', fun w hw => ?_⟩
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  obtain ⟨hbij, -, -, -⟩ := hφ
  have hexw : ∃ z ∈ D, φ z = w := hbij.surjOn hw
  set v := invFunOn φ D w with hv
  have hvD : v ∈ D := invFunOn_mem hexw
  have hφv : φ v = w := invFunOn_eq hexw
  have hmem : (b : ℂ)⁻¹ * v ∈ D' := by
    rw [hD]
    convert hvD using 1
    push_cast
    field_simp
  have hval : (fun w => φ ((((b⁻¹ : ℝ) : ℂ))⁻¹ * w)) ((b : ℂ)⁻¹ * v) = w := by
    simp only
    rw [show (((b⁻¹ : ℝ) : ℂ))⁻¹ * ((b : ℂ)⁻¹ * v) = v by push_cast; field_simp]
    exact hφv
  have hex' : ∃ z ∈ D', (fun w => φ ((((b⁻¹ : ℝ) : ℂ))⁻¹ * w)) z = w := ⟨_, hmem, hval⟩
  obtain ⟨hbij', -, -, -⟩ := hN''
  have e := hbij'.injOn (invFunOn_mem hex') hmem ((invFunOn_eq hex').trans hval.symm)
  rw [e]
  field_simp

/-! ## The pointwise choice regularity -/

/-- **Area-only choice regularity of the unscaled field along the unscaled path, at every
point**, from the core and the area limit of the canonical field along the scaled path. -/
theorem choiceRegularA_unscaled_pt {γ : ℝ} (hsel : G1PsiSel γ Ψ) {y : FieldSample}
    (hg : IsLQGGood γ y) (hb : 0 < scaleParam γ y) {a : ℝ≥0 → ℝ} (hac : Continuous a)
    (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (hWd : Continuous (pathDrive (γ ^ 2) a))
    (hW0 : pathDrive (γ ^ 2) a 0 = 0)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv (pathDrive (γ ^ 2) a) t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))
    (left : Bool)
    (hcore : ∀ φ, IsNormalizedUniformizer
        (sideDom (pathTrace (γ ^ 2) (scalePath (scaleParam γ y) a)) left) φ →
      G1.ChoiceRegularCore γ (canonical γ y)
        (invFunOn φ (sideDom (pathTrace (γ ^ 2) (scalePath (scaleParam γ y) a)) left)) ∧
      G1Z2MeasGood γ left (coordChange (canonical γ y)
        (invFunOn φ (sideDom (pathTrace (γ ^ 2) (scalePath (scaleParam γ y) a)) left)) (Qc γ)))
    (hcont : ∀ (d : ℂ) (r : ℝ), 0 < r → F1.ContData y ((foldedCircle d r).map (Ψ left a)))
    (L x : ℝ) :
    G1.ChoiceRegularA γ (addConst (translate y (x : ℂ)) (L / γ)) (g3mapB Ψ left a 1 x) := by
  set b := scaleParam γ y with hbdef
  obtain ⟨φ, hφ, hΨa⟩ := hsel.2.2 a hac hs left
  obtain ⟨φ'', hN'', hdil⟩ := exists_dilUnif (γ := γ) hb hs hWd hW0 hex left hφ
  set D' := sideDom (pathTrace (γ ^ 2) (scalePath b a)) left with hD'def
  have hsb : IsSimpleChord (pathTrace (γ ^ 2) (scalePath b a)) :=
    isSimpleChord_scalePath hb _ hWd hW0 hex hs
  obtain ⟨hcB, ⟨μ, hμ, hsm, htop⟩, -⟩ := hcore φ'' hN''
  obtain ⟨hd'', hd0'', hm'', hH''⟩ := G1.invFunOn_props (G1.isOpen_component hsb left) hN''
  have hH''H : MapsTo (invFunOn φ'' D') H H := fun w hw =>
    G1ZA1a.sideDom_subset_H _ left (hH'' hw)
  have hinj'' : InjOn (invFunOn φ'' D') H := hN''.1.invOn_invFunOn.2.injOn
  have hΨm : Measurable (Ψ left a) := (hsel.1 left).comp (measurable_const.prodMk measurable_id)
  have hΨH : MapsTo (Ψ left a) H H := (G1RC.psiGood_of_sel hsel hac hs left).2.2.2.1
  have hEq : EqOn (Ψ left a) (fun u => (b : ℂ) * invFunOn φ'' D' u) H := fun w hw => by
    rw [hΨa]; exact (hdil w hw).symm
  -- equality of the pulled-back fields at every folded circle
  have hfc : ∀ (d : ℂ) (r : ℝ), 0 < r →
      coordChange y (Ψ left a) (Qc γ) (foldedCircle d r) =
        coordChange (canonical γ y) (invFunOn φ'' D') (Qc γ) (foldedCircle d r) := by
    intro d r hr
    rw [g1zMeas_coordChange_fc_congr y hEq (Qc γ) d hr]
    have hc' : F1.ContData y ((foldedCircle d r).map fun u => (b : ℂ) * invFunOn φ'' D' u) := by
      rw [← Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => hEq hw)]
      exact hcont d r hr
    exact raw_rescale_side hg.1 hb hm'' hH''H hd0'' d hr
      (G1.integrable_log_norm_deriv_foldedCircle_of_injOn hd'' hinj'' d hr) hc'
  have hcoreA : G1.ChoiceRegularCore γ y (Ψ left a) := core_of_fc_eq hcB hfc
  have hμA : HasAreaLimit γ (coordChange y (Ψ left a) (Qc γ)) μ :=
    hasAreaLimit_of_fc_eq hμ hfc
  have hg3 : g3mapB Ψ left a 1 x =
      fun w => Ψ left a (w + (g3bpre Ψ left a (x / 1) : ℂ)) - (x : ℂ) := by
    funext w
    simp [g3mapB, g3locM]
  rw [hg3]
  exact choiceRegularA_translate hg.1 hΨm hΨH hcoreA hμA hsm htop hcont _ x (L / γ)

end G3ZqS
end Thm18Asm
end QuantumZipper
