import QuantumZipper.Proofs.Thm18.G1Z5Main
import QuantumZipper.Proofs.Thm18.G1ZSplitDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z5 (D58): the side transport with the transport map identified (reflection data)

The G1 zoom Z1 route needs the transport map `Φ` identified with the boundary values of the side
map (`SideReflGood`). This file keeps the reflection data through the whole B0 chain:

* `G1Z4SideLimStmt'`: `G1Z4SideLimStmt` with `SideReflGood left (Ψ left p.1) Φ` as a conjunct;
  `g1Z4SideLimStmt'_of_path : G1Z4SideLimPathStmt → G1RegRepRC2Stmt → G1Z4SideLimStmt'`;
* `refl_dilate_eq`: the boundary values of `ψ(b ·)` are `Φ(b ·)` (the reflection data of the
  `Classical.epsilon` side map and of the selected map differ by the dilation of U6);
* **`g1SideTransportId_of_path`**: for the Theorem 1.8 configuration, a.s. there is `Φ` with
  `SideReflGood left (g1zSideMap left (drive (γ ^ 2) B ω)) Φ` and
  `g1SideNu γ left (g1SideField γ B Y left ω) = ((qBoundaryMeasure γ (Y ω))|_S).map Φ.symm`,
  i.e. the body of `G1SideTransportIdStmt` (G1ZZ1Main.lean), from `G1Z4SideLimPathStmt`,
  `G1RegRepRC2Stmt`, `G1RegRepRestStmt`.

Independence/Fubini and the law transfer are copied from `g1SideTransportStmt_of_bdryFixed` and
`g1BdryFixedStmt_of_rep` (G1Z3Fixed.lean). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Z5

open GoodSample GoodMeas
open BdryVague (testFam bump continuous_testFam hasCompactSupport_testFam continuous_bump
  hasCompactSupport_bump)

/-- Boundary values of a dilated side map. -/
theorem refl_dilate_eq {left : Bool} {ψ ψ' : ℂ → ℂ} {Φ Φ' : ℝ ≃o ℝ}
    (hR : SideReflGood left ψ Φ) (hR' : SideReflGood left ψ' Φ') {b : ℝ} (hb : 0 < b)
    (heq : EqOn ψ' (fun w => ψ ((b : ℂ) * w)) H) {t : ℝ} (ht : t ∈ g1SideHalf left) :
    Φ' t = Φ (b * t) := by
  have hbt : b * t ∈ g1SideHalf left := by
    rw [mem_side_iff] at ht ⊢; rw [mul_left_comm]; exact mul_pos hb ht
  rw [← bm_eq_of_refl hR' ht]
  obtain ⟨p, q, hpq, hS, htpq⟩ := exists_side_window left (isCompact_singleton (x := b * t))
    (singleton_subset_iff.2 hbt)
  obtain ⟨U, Ψ', hU, hJU, hΨd, hΨΦ, -, hEq⟩ := hR.2 p q hpq hS
  have htI : b * t ∈ Icc p q := Ioo_subset_Icc_self (htpq (mem_singleton _))
  have hc : ContinuousAt Ψ' ((b * t : ℝ) : ℂ) :=
    (hΨd.differentiableAt (hU.mem_nhds (hJU _ htI))).continuousAt
  have hlim : Tendsto (fun n => (b : ℂ) * appr t n) atTop (𝓝 ((b * t : ℝ) : ℂ)) := by
    have := (tendsto_appr t).const_mul (b : ℂ)
    simpa [Complex.ofReal_mul] using this
  have hmem : ∀ n, (b : ℂ) * appr t n ∈ H := fun n => by
    have h := appr_mem_H t n
    show 0 < ((b : ℂ) * appr t n).im
    have h' : 0 < (appr t n).im := h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos hb h'
  have h3 : Tendsto (fun n => Ψ' ((b : ℂ) * appr t n)) atTop (𝓝 (Ψ' ((b * t : ℝ) : ℂ))) :=
    hc.tendsto.comp hlim
  rw [hΨΦ _ htI] at h3
  have h4 := (Complex.continuous_re.tendsto _).comp h3
  simp only [Complex.ofReal_re] at h4
  have h5 : Tendsto (fun n : ℕ => (ψ' (appr t n)).re) atTop (𝓝 (Φ (b * t))) :=
    h4.congr fun n => by
      simp only [Function.comp]
      rw [heq (appr_mem_H t n), ← hEq (hmem n)]
  unfold bm
  rw [if_pos ht]
  exact h5.limUnder_eq

/-- The pullback only depends on `Φ` on the side half-line. -/
theorem pullback_congr {left : Bool} (μ : Measure ℝ) {Φ₁ Φ₂ : ℝ ≃o ℝ} (h1 : Φ₁ 0 = 0)
    (h : ∀ t ∈ g1SideHalf left, Φ₁ t = Φ₂ t) :
    (μ.restrict (g1SideHalf left)).map Φ₁.symm = (μ.restrict (g1SideHalf left)).map Φ₂.symm := by
  refine Measure.map_congr ((ae_restrict_mem (g1z2_isOpen_sideHalf left).measurableSet).mono
    fun u hu => ?_)
  have hS1 : Φ₁.symm u ∈ g1SideHalf left := by
    rw [← image_g1SideHalf h1 left] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    simpa using ht
  show Φ₁.symm u = Φ₂.symm u
  rw [eq_comm, OrderIso.symm_apply_eq, ← h _ hS1]
  simp

/-- **Per-sample transport with identified map** for the `Classical.epsilon` side map. -/
theorem good_of_selected' {γ : ℝ} (hγ : 0 < γ) {η : ℝ → ℂ} (hη : IsSimpleChord η) {left : Bool}
    {φ₀ : ℂ → ℂ} (hφ₀ : IsNormalizedUniformizer (sideDom η left) φ₀) {y : FieldSample}
    {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith (coordChange y (invFunOn φ₀ (sideDom η left)) (Qc γ)) F)
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (coordChange y (invFunOn φ₀ (sideDom η left)) (Qc γ)) (foldedCircle d r) =
        coordChange y (invFunOn φ₀ (sideDom η left)) (Qc γ) (foldedCircle d r))
    {Φ₀ : ℝ ≃o ℝ} (hR₀ : SideReflGood left (invFunOn φ₀ (sideDom η left)) Φ₀)
    (hν : G1Z2SideBdryLim γ left (coordChange y (invFunOn φ₀ (sideDom η left)) (Qc γ))
      (((qBoundaryMeasure γ y).restrict (g1SideHalf left)).map Φ₀.symm)) :
    ∃ Φ : ℝ ≃o ℝ,
      SideReflGood left (invFunOn (uniformizer (sideDom η left)) (sideDom η left)) Φ ∧
      g1SideNu γ left (coordChange y
          (invFunOn (uniformizer (sideDom η left)) (sideDom η left)) (Qc γ)) =
        ((qBoundaryMeasure γ y).restrict (g1SideHalf left)).map Φ.symm := by
  have hu : IsNormalizedUniformizer (sideDom η left) (uniformizer (sideDom η left)) :=
    Classical.epsilon_spec ⟨φ₀, hφ₀⟩
  have hD : IsOpen (sideDom η left) := G1.isOpen_component hη left
  obtain ⟨hψd, hψ0, hψm, -⟩ := G1.invFunOn_props hD hφ₀
  have hint := G1.choiceRegular_logDeriv hD hφ₀
  obtain ⟨b, hb, hbeq⟩ := g1z2_invFunOn_eq_dilate hη left hφ₀ hu
  have hR := g1z2_regEq_dilate y (Qc γ) hψd hψ0 hψm hb hbeq hint hexact
  have havg : avgReg (coordChange y
      (invFunOn (uniformizer (sideDom η left)) (sideDom η left)) (Qc γ)) =
      avgReg (rescale (coordChange y (invFunOn φ₀ (sideDom η left)) (Qc γ)) (Qc γ) b) :=
    funext fun k => funext fun z => hR k z
  obtain ⟨Φu, hRu⟩ := G1Z2.sideReflChordStmt_holds η hη left _ hu
  refine ⟨Φu, hRu, ?_⟩
  rw [G1Z4.g1SideNu_congr_avg havg, g1z2_sideNu_rescale hγ hF hν hb,
    Measure.map_map (show Measurable fun u : ℝ => u / b from measurable_id.div_const b)
      Φ₀.symm.continuous.measurable]
  have hΦb : ((fun u : ℝ => u / b) ∘ Φ₀.symm) = ((OrderIso.mulLeft₀ b hb).trans Φ₀).symm := by
    funext u
    simp only [Function.comp, OrderIso.symm_trans_apply]
    rw [eq_comm, OrderIso.symm_apply_eq]
    show _ = b * (Φ₀.symm u / b)
    field_simp
  rw [hΦb]
  refine pullback_congr _ (by simp [hR₀.1]) fun t ht => ?_
  rw [refl_dilate_eq hR₀ hRu hb hbeq ht]
  rfl

/-- The side limit on the good set, with the reflection data. -/
theorem sideLim_of_repGood' {γ : ℝ} {left : Bool} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hΨ : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} {c : ℕ → ℝ} (hc : Continuous a)
    (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (h : RepGood γ left (Ψ left a) c) :
    ∃ Φ : ℝ ≃o ℝ, SideReflGood left (Ψ left a) Φ ∧ G1Z2SideBdryLim γ left
      (coordChange (E1.fromC c) (Ψ left a) (Qc γ))
      (((qBoundaryMeasure γ (E1.fromC c)).restrict (g1SideHalf left)).map Φ.symm) := by
  obtain ⟨⟨F, hF⟩, hcert, hb, hT, hB⟩ := h
  obtain ⟨ν, hν⟩ := sideLim_of_cert hF hcert
  obtain ⟨φ₀, hφ₀, hΨa⟩ := hΨ.2.2 a hc hs left
  obtain ⟨Φ, hR⟩ := G1Z2.sideReflChordStmt_holds _ hs left φ₀ hφ₀
  rw [← hΨa] at hR
  have hy := E1.M4.isVagueLimitR_qBoundaryMeasure (E1.M4.exists_isVagueLimitR_of_bCert hb)
  refine ⟨Φ, hR, ?_⟩
  have key : ∀ G : ℝ → ℝ, Continuous G → HasCompactSupport G →
      IdT γ left (Ψ left a) c (glue left G) →
      Tendsto (fun k => ∫ t, glue left G (Φ t)
        ∂bdryR γ (coordChange (E1.fromC c) (Ψ left a) (Qc γ)) (goodRad (k, 1))) atTop
        (𝓝 (∫ t, glue left G t ∂qBoundaryMeasure γ (E1.fromC c))) := by
    intro G hG hGc hI
    unfold IdT at hI
    rw [(hy.2 _ (continuous_glue left hG hGc) (hasCompactSupport_glue left hG hGc)).limUnder_eq]
      at hI
    simp_rw [glue_bm hR]
    exact hI
  rw [← eq_pullback_of_ident hν hy hR.1 ?_]
  · exact hν
  rintro g (⟨N, n, rfl⟩ | ⟨N, rfl⟩)
  · exact key _ (continuous_testFam N n) (hasCompactSupport_testFam N n) (hT N n)
  · exact key _ (continuous_bump N) (hasCompactSupport_bump N) (hB N)

end G1Z5

/-- **`G1Z4SideLimStmt` with the reflection data of the selected map.** -/
def G1Z4SideLimStmt' : Prop :=
  G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∃ E₁ : Set G1PathData, MeasurableSet E₁ ∧
      (∀ p ∈ E₁, Continuous p.1 → IsSimpleChord (pathTrace (γ ^ 2) p.1) → ∀ left : Bool,
        ∃ Φ : ℝ ≃o ℝ, SideReflGood left (Ψ left p.1) Φ ∧ G1Z2SideBdryLim γ left
          (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ))
          (((qBoundaryMeasure γ (E1.fromC p.2.1)).restrict (g1SideHalf left)).map Φ.symm)) ∧
      ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P',
        (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ E₁

/-- The good pairs with the transport map identified by the reflection data. -/
def G1BdryGood' (γ : ℝ) (p : G1PathData) : Prop :=
  Continuous p.1 → IsSimpleChord (pathTrace (γ ^ 2) p.1) →
    ∀ y : FieldSample, WedgeMeas.dataFull H y = p.2 → ∀ left : Bool,
      ∃ Φ : ℝ ≃o ℝ, SideReflGood left (g1zSideMap left (pathDrive (γ ^ 2) p.1)) Φ ∧
        g1SideNu γ left (g1CfgSideField γ left (y, pathDrive (γ ^ 2) p.1)) =
          ((qBoundaryMeasure γ y).restrict (g1SideHalf left)).map Φ.symm

end Thm18Asm
end QuantumZipper
