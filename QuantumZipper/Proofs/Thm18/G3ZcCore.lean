import QuantumZipper.Proofs.Thm18.G1ZoomWeighted
import QuantumZipper.Proofs.Thm18.G3Cv2Setup
import QuantumZipper.Proofs.Zipper.D3PlusIII
import QuantumZipper.Proofs.Zipper.LocRichD3
import QuantumZipper.Proofs.Section5.Prop16MarkovMask2Agree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C (c), step 5: D3⁺(i) transferred to a field that agrees with the model near `0`

`d3_transfer_of_agree`: let `(X, Ξ, g)` be D3⁺ `Setup` data (any `α`) and `Zf L ω` a family of
fields that a.s., for every level `L`, agrees near `0` (`AgreeNear`, dyadic folded circles) with the
D3⁺ model `zoomModel γ α L ρ₀ (X ω) (g ω)`. Then the conclusion of D3⁺(i) holds for `Zf` in place of
the model: eventually in `L`, **uniformly over `condSigma Ξ X r ⊗ Borel`-measurable test
functionals** `Φ(ω, ·) ∈ [0, 1]`,

  `E Φ(ω, loc_R canonicalOn(Zf L ω)) ≈ E ∫ Φ(ω, loc_R Y') dP'(Y')`  (within `2η`).

Proof as in `g0_onePoint_free` (G3Cv2TV): on the event where the model's local scale lies in
`(0, r/(R+1))` the local canonical data coincide (`locFieldFull_canonicalOn_congr`), and that
event has probability `→ 1` (D3⁺(iii), `d3PlusIII_holds`); the model satisfies D3⁺(i).

This applies to the zooms of `exists_g0Setup` (`α = 0`), of `exists_g0Setup_two` (both points, one
field `W`; G3ZcTwoSetup) and of ZOOM-A's Palm-case core `G3Za.exists_g0Setup_logSing` (`α = γ`).

* `twoPoint_of_agree`: with `Φ(ω, y) = F₂^L(ω) Γ₁(y)` and `tendsto_lintegral_mul_of_unif`
  (G3ZcTwo): if the second zoom's functional `F₂^L ∈ [0,1]` is `condSigma Ξ X r`-measurable and
  `E F₂^L → c₂`, then `E[F₂^L Γ₁(loc_R canonicalOn(Zf L))] → c₂ · E Γ₁(loc_R Y')` (the two-point
  decorrelation of Sheffield, arXiv:1012.4797, p. 71).

Own bookkeeping on top of D3⁺(i), D3⁺(iii) (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open D3Plus

/-- **D3⁺(i) for a field agreeing with the model near `0`.** -/
theorem d3_transfer_of_agree (hD3 : D3PlusIStmtRich) {γ α r : ℝ} {ρ₀ : Measure ℂ}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} {E' : Type} [MeasurableSpace E'] {Ξ : Ω → E'} {g : Ω → ℂ → ℝ}
    (hS : Setup γ α r ρ₀ P X Ξ g) {Zf : ℝ → Ω → FieldSample}
    (hag : ∀ᵐ ω ∂P, ∀ L : ℝ, AgreeNear (Zf L ω) (zoomModel γ α L ρ₀ (X ω) (g ω)) r)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y' : Ω' → FieldSample} (hY' : IsQuantumWedge γ α Y' P') (R : ℕ) (η : ℝ≥0∞) (hη : 0 < η) :
    ∀ᶠ L in atTop, ∀ Φ : Ω × ((ℕ → ℝ) × (TestFun H → ℝ)) → ℝ≥0∞,
      Measurable[(condSigma Ξ X r).prod inferInstance] Φ → (∀ p, Φ p ≤ 1) →
        ∫⁻ ω, Φ (ω, locFieldFull R (canonicalOn γ (Zf L ω) (halfDisc r))) ∂P ≤
            ∫⁻ ω, ∫⁻ ω', Φ (ω, locFieldFull R (Y' ω')) ∂P' ∂P + η + η ∧
          ∫⁻ ω, ∫⁻ ω', Φ (ω, locFieldFull R (Y' ω')) ∂P' ∂P ≤
            ∫⁻ ω, Φ (ω, locFieldFull R (canonicalOn γ (Zf L ω) (halfDisc r))) ∂P + η + η := by
  have hr : 0 < r := hS.hr
  set a : ℝ → Ω → ℝ := fun L ω =>
    scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) with ha
  set good : ℝ → Set Ω := fun L => {ω | 0 < a L ω ∧ a L ω * R < r} with hgood
  set F : ℝ → Ω → ℝ≥0∞ := fun L => (good L)ᶜ.indicator 1 with hF
  have hFm : ∀ L, AEMeasurable (F L) P := by
    intro L
    have hm := Prop16Asm.aemeasurable_scaleParamOn_zoomModel_mm hS L
    have hns : NullMeasurableSet (good L) P := by
      have h1 : NullMeasurableSet {ω | 0 < a L ω} P :=
        nullMeasurableSet_lt aemeasurable_const hm
      have h2 : NullMeasurableSet {ω | a L ω * R < r} P :=
        nullMeasurableSet_lt (hm.mul_const _) aemeasurable_const
      exact h1.inter h2
    exact (aemeasurable_const.indicator₀ hns.compl)
  have hRr : 0 < r / (R + 1) := by positivity
  have hF0 : Tendsto (fun L => ∫⁻ ω, F L ω ∂P) atTop (𝓝 0) := by
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun L => F L ω) atTop (𝓝 0) := by
      filter_upwards [d3PlusIII_holds γ α r ρ₀ P X Ξ g hS] with ω hω
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hω _ hRr] with L hL
      have hmem : ω ∈ good L := by
        refine ⟨hL.1, ?_⟩
        have h1 : a L ω * R ≤ a L ω * (R + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hL.1.le
        have h2 : a L ω * (R + 1) < r := by
          have := hL.2
          rw [lt_div_iff₀ (by positivity)] at this
          linarith
        linarith
      simp [hF, hmem]
    have := tendsto_lintegral_filter_of_dominated_convergence' (μ := P)
      (fun _ => (1 : ℝ≥0∞)) (Eventually.of_forall hFm)
      (Eventually.of_forall fun L => ae_of_all _ fun ω => by
        simp only [hF]; exact Set.indicator_le (fun _ _ => le_rfl) ω)
      (by simp) hlim
    simpa using this
  have hη2 : ∀ᶠ L in atTop, ∫⁻ ω, F L ω ∂P ≤ η :=
    hF0.eventually (Iic_mem_nhds hη)
  filter_upwards [hD3 γ α r ρ₀ P X Ξ g P' Y' hS hY' R η hη, hη2] with L hL hFL Φ hΦ hΦ1
  obtain ⟨h1, h2⟩ := hL Φ hΦ hΦ1
  set M := fun ω => Φ (ω, locFieldFull R (canonicalOn γ (zoomModel γ α L ρ₀ (X ω) (g ω))
    (halfDisc r))) with hM
  set V := fun ω => Φ (ω, locFieldFull R (canonicalOn γ (Zf L ω) (halfDisc r))) with hV
  have hpt : ∀ᵐ ω ∂P, V ω ≤ M ω + F L ω ∧ M ω ≤ V ω + F L ω := by
    filter_upwards [hag] with ω hω
    by_cases hg : ω ∈ good L
    · have e := locFieldFull_canonicalOn_congr (γ := γ) (hω L) hg.1 hg.2
      simp only [hV, hM, e, hF, Set.indicator_of_notMem (show ω ∉ (good L)ᶜ from fun h => h hg)]
      simp
    · simp only [hF, Set.indicator_of_mem (show ω ∈ (good L)ᶜ from hg), Pi.one_apply]
      exact ⟨(hΦ1 _).trans le_add_self, (hΦ1 _).trans le_add_self⟩
  have iV : ∫⁻ ω, V ω ∂P ≤ ∫⁻ ω, M ω ∂P + ∫⁻ ω, F L ω ∂P :=
    (lintegral_mono_ae (hpt.mono fun ω h => h.1)).trans_eq
      (lintegral_add_right' _ (hFm L))
  have iM : ∫⁻ ω, M ω ∂P ≤ ∫⁻ ω, V ω ∂P + ∫⁻ ω, F L ω ∂P :=
    (lintegral_mono_ae (hpt.mono fun ω h => h.2)).trans_eq
      (lintegral_add_right' _ (hFm L))
  constructor
  · calc ∫⁻ ω, V ω ∂P ≤ ∫⁻ ω, M ω ∂P + ∫⁻ ω, F L ω ∂P := iV
      _ ≤ _ + η + η := by gcongr
  · calc _ ≤ ∫⁻ ω, M ω ∂P + η := h2
      _ ≤ (∫⁻ ω, V ω ∂P + ∫⁻ ω, F L ω ∂P) + η := by gcongr
      _ ≤ ∫⁻ ω, V ω ∂P + η + η := by
          rw [add_right_comm]; gcongr

end G3Cv
end QuantumZipper
