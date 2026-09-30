import QuantumZipper.Proofs.Thm18.G3ZqResc
import QuantumZipper.Proofs.Thm18.G3ZrWire2
import QuantumZipper.Proofs.Thm18.G3Z2b2Dil2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (6): the two-point rescaling identity along a fixed path

Two-point analog of `G1Zm.g1PhiM_canonical_scalePath` (G1ZmResc), in the area-only form of D93:
for a good unscaled field `W` with scale `b = scaleParam γ W > 0` and a good path `a` whose
Brownian scaling `S_b a` is good,

  `g3PhiM2 (canonical γ W, S_b a) = g3PhiM2 (W, a)`,

under explicit regularity conditions at the window points (`G3ZqRegU`, area-only; `DilReg`;
`G3FacRegA`). Chain: the two-point functional of the canonical field is its geometric Palm-window
integral (`G3Zr.g3Inner_eq_g3PhiM2A`); the dilation to the unscaled field
(`G3Z2b2.wedgePalm2_rescale`) produces the maps `b · φ^{S_b a}_{x/b}` at `x` and at `R(x)`; these
are the maps `φ^a` of the unscaled path precomposed with a fixed dilation
(`G1Zm.g3locM_scalePath`), which the canonical data do not see
(`G3Zr.data_canonical_zoomFieldVia_comp_mulA`, `G3Zr.g3zoomLawM_eqA`).

Sheffield, arXiv:1012.4797, p. 70 (independent curve, SLE scale invariance). Own bookkeeping
(AGENT_GUIDE cost rule), following G1ZmResc.
-/

noncomputable section

open MeasureTheory Filter Set Function Complex
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zq

open G3Z2b2 G1Zm D3Plus

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The area-only regularity of the unscaled field `W` at the point `x` for the local map of
the path `a` on side `left` (all precomposed dilations). -/
def G3ZqRegU (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (W : FieldSample)
    (a : ℝ≥0 → ℝ) (x : ℝ) : Prop :=
  (∀ (d : ℂ) (j : ℕ), E1.RegShift (translate W (x : ℂ))
      ((foldedCircle d (radius j)).map (g3mapB Ψ left a 1 x))) ∧
    (∀ k : ℝ, 0 < k → ∀ (d : ℂ) (j : ℕ), E1.RegShift (translate W (x : ℂ))
      ((foldedCircle d (radius j)).map fun w => g3mapB Ψ left a 1 x ((k : ℂ) * w))) ∧
    G1.ChoiceRegularA γ (addConst (translate W (x : ℂ)) (L / γ)) (g3mapB Ψ left a 1 x)

/-- **One point: the dilated scaled-path map gives the zoom datum of the unscaled path.** -/
theorem data_dil_scalePath_eq {γ : ℝ} (hγ : 0 < γ) (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ}
    (hac : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool) {b : ℝ}
    (hb : 0 < b) {c μ : ℝ} (hc : 0 < c) (hμ : 0 < μ)
    (hloc' : ∀ x ∈ g1SideHalf left, ∀ w : ℂ, g1zLocMap left (pathDrive (γ ^ 2) (scalePath b a)) x w =
      g3locM Ψ left (scalePath b a, x, (c : ℂ) * w))
    (hsc : ∀ x ∈ g1SideHalf left, ∀ w ∈ H,
      (b : ℂ) * g3locM Ψ left (scalePath b a, x / b, w) = g3locM Ψ left (a, x, ((μ : ℂ))⁻¹ * w))
    (W : FieldSample) (L : ℝ) {x : ℝ} (hx : x ∈ g1SideHalf left)
    (hreg : G3ZqRegU γ L Ψ left W a x) :
    WedgeMeas.dataFull H (canonical γ (zoomFieldVia γ L W x
      (fun w => (b : ℂ) * g1zLocMap left (pathDrive (γ ^ 2) (scalePath b a)) (x / b) w))) =
      g1zM γ L Ψ left ((W, a), x) := by
  obtain ⟨hs1, hs2, hcr⟩ := hreg
  have hxb : x / b ∈ g1SideHalf left := (Set.ext_iff.1 (preimage_div_half hb left) x).2 hx
  set k : ℝ := c / μ with hk
  have hk0 : 0 < k := div_pos hc hμ
  have heq : EqOn (fun w => (b : ℂ) * g1zLocMap left (pathDrive (γ ^ 2) (scalePath b a)) (x / b) w)
      (fun w => g3mapB Ψ left a 1 x ((k : ℂ) * w)) H := by
    intro w hw
    have hcw : (c : ℂ) * w ∈ H := by
      show 0 < ((c : ℂ) * w).im
      simpa [Complex.mul_im] using mul_pos hc (show 0 < w.im from hw)
    simp only
    rw [hloc' (x / b) hxb w, hsc x hx _ hcw]
    simp only [g3mapB, hk]
    push_cast
    ring_nf
  rw [canonical_zoomFieldVia_congr_H γ L W x heq]
  obtain ⟨hfd, hf0, hfm⟩ := g3mapB_props hsel hac hs left one_pos x
  have hint : ∀ d ∈ Hbar, ∀ r > 0, Integrable
      (fun z => Real.log ‖deriv (g3mapB Ψ left a 1 x) z‖) (foldedCircle d r) :=
    fun d _ r hr => G1.integrable_log_norm_deriv_foldedCircle_of_injOn hfd
      (injOn_g3mapB hsel hac hs left one_pos x) d hr
  rw [G3Zr.data_canonical_zoomFieldVia_comp_mulA hγ W x L hfd hf0 hfm hint hk0 hs1 (hs2 k hk0) hcr]
  unfold g1zM
  have hp : g3mapP Ψ left (W, a, 1, x) = g3mapB Ψ left a 1 x := by simp [g3mapP]
  have hs1' : ∀ (d : ℂ) (j : ℕ), E1.RegShift (translate W (x : ℂ))
      ((foldedCircle d (radius j)).map (g3mapP Ψ left (W, a, 1, x))) := by
    rw [hp]; exact hs1
  have hcr' : G1.ChoiceRegularA γ (addConst (translate W (x : ℂ)) (L / γ))
      (g3mapP Ψ left (W, a, 1, x)) := by rw [hp]; exact hcr
  rw [G3Zr.g3zoomLawM_eqA hsel L left (p := (W, a, 1, x)) hac hs one_pos hs1' hcr', hp]

/-- **The two-point rescaling identity along a fixed path** (two-point analog of
`G1Zm.g1PhiM_canonical_scalePath`, area-only regularity). -/
theorem g3PhiM2_canonical_scalePath {γ : ℝ} (hγ : 0 < γ) (hsel : G1PsiSel γ Ψ)
    {a : ℝ≥0 → ℝ} (hac : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a))
    (hWd : Continuous (pathDrive (γ ^ 2) a)) (hW0 : pathDrive (γ ^ 2) a 0 = 0)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv (pathDrive (γ ^ 2) a) t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))
    {W : FieldSample} (hWg : IsLQGGood γ W) (hb : 0 < scaleParam γ W)
    (hac' : Continuous (scalePath (scaleParam γ W) a))
    (hs' : IsSimpleChord (pathTrace (γ ^ 2) (scalePath (scaleParam γ W) a)))
    (hNl' : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) (scalePath (scaleParam γ W) a)) true)
      (uniformizer (sideDom (pathTrace (γ ^ 2) (scalePath (scaleParam γ W) a)) true)))
    (hNr' : IsNormalizedUniformizer
      (sideDom (pathTrace (γ ^ 2) (scalePath (scaleParam γ W) a)) false)
      (uniformizer (sideDom (pathTrace (γ ^ 2) (scalePath (scaleParam γ W) a)) false)))
    (hy : IsLQGGood γ (canonical γ W)) (U L : ℝ) (s t : Set LawD)
    (hreg1 : ∀ᵐ x ∂(qBoundaryMeasure γ (canonical γ W)),
      x ∈ g1zWedgeWin γ true (canonical γ W) U →
        G3Zr.G3FacRegA γ L Ψ (canonical γ W) (scalePath (scaleParam γ W) a) x)
    (hdil : ∀ x ∈ g1SideHalf true,
      DilReg γ W (scaleParam γ W) x
        (g1zLocMap true (pathDrive (γ ^ 2) (scalePath (scaleParam γ W) a))
          (x / scaleParam γ W)) ∧
      DilReg γ W (scaleParam γ W) (R18.g3zPartner γ W x)
        (g1zLocMap false (pathDrive (γ ^ 2) (scalePath (scaleParam γ W) a))
          (R18.g3zPartner γ W x / scaleParam γ W)))
    (hreg3 : ∀ᵐ x ∂(qBoundaryMeasure γ W), x ∈ g1zWedgeWin γ true W U →
      G3ZqRegU γ L Ψ true W a x ∧ 0 < R18.g3zPartner γ W x ∧
        G3ZqRegU γ L Ψ false W a (R18.g3zPartner γ W x)) :
    g3PhiM2 γ L Ψ U s t (canonical γ W, scalePath (scaleParam γ W) a) =
      g3PhiM2 γ L Ψ U s t (W, a) := by
  classical
  set b := scaleParam γ W with hbdef
  rw [← G3Zr.g3Inner_eq_g3PhiM2A hγ hsel hac' hs' hNl' hNr' hy U L s t hreg1]
  have e : canonical γ W = rescale W (Qc γ) b := rfl
  have hmeas : ∀ side x, Measurable
      (g1zLocMap side (pathDrive (γ ^ 2) (scalePath b a)) x) := fun side x => by
    have hN : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) (scalePath b a)) side)
        (uniformizer (sideDom (pathTrace (γ ^ 2) (scalePath b a)) side)) := by
      cases side
      · exact hNr'
      · exact hNl'
    exact (G0Map.measurable_g1zLocMap (W := pathDrive (γ ^ 2) (scalePath b a)) hs' hN).comp
      (measurable_const.prodMk measurable_id)
  rw [e, wedgePalm2_rescale hγ hWg hb U L s t
    (fun side x => g1zLocMap side (pathDrive (γ ^ 2) (scalePath b a)) x) hmeas
    (fun x hx => (hdil x hx).1) (fun x hx => (hdil x hx).2)]
  obtain ⟨c, hc, hloc'⟩ := g1zLocMap_eq_g3locM hsel hac' hs' true hNl'
  obtain ⟨c', hc', hloc''⟩ := g1zLocMap_eq_g3locM hsel hac' hs' false hNr'
  obtain ⟨μ, hμ, hsc⟩ := g3locM_scalePath hsel hb hac hs hac' hs' hWd hW0 hex true
  obtain ⟨μ', hμ', hsc'⟩ := g3locM_scalePath hsel hb hac hs hac' hs' hWd hW0 hex false
  have hbM : bdryM γ W = qBoundaryMeasure γ W := by
    unfold bdryM; rw [if_pos (G4Core.bCert_of_isLQGGood hWg)]
  have hhalf : MeasurableSet (g1SideHalf true) := measurableSet_Iio
  have hwin := measurableSet_g1zWedgeWin γ true W U
  unfold g3PhiM2
  rw [hbM, Measure.restrict_restrict hwin, ← lintegral_indicator (hwin.inter hhalf)]
  refine lintegral_congr_ae ?_
  filter_upwards [hreg3] with x hrx
  have hmem : x ∈ g1zWedgeWin γ true W U ↔
      (x ∈ g1SideHalf true ∧ qBoundaryMeasure γ W (g1SideSeg true x) ≤ ENNReal.ofReal U) :=
    Iff.rfl
  have hpart : partM γ W x = R18.g3zPartner γ W x := by simp only [partM, R18.g3zPartner, hbM]
  by_cases hx : x ∈ g1zWedgeWin γ true W U
  · have hxh : x ∈ g1SideHalf true := hx.1
    rw [indicator_of_mem (show x ∈ g1zWedgeWin γ true W U ∩ g1SideHalf true from ⟨hx, hxh⟩)]
    simp only [g3IntM2, hbM]
    rw [if_pos (hmem.1 hx), hpart]
    obtain ⟨h1, hp, h2⟩ := hrx hx
    have hph : R18.g3zPartner γ W x ∈ g1SideHalf false := by simpa [g1SideHalf] using hp
    rw [data_dil_scalePath_eq hγ hsel hac hs true hb hc hμ hloc' hsc W L hxh h1,
      data_dil_scalePath_eq hγ hsel hac hs false hb hc' hμ' hloc'' hsc' W L hph h2]
  · rw [indicator_of_notMem (fun h => hx h.1)]
    simp only [g3IntM2, hbM]
    rw [if_neg (fun h => hx (hmem.2 h))]

end G3Zq
end Thm18Asm
end QuantumZipper
