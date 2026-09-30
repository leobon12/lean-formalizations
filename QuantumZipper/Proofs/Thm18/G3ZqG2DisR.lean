import QuantumZipper.Proofs.Thm18.G3ZqG2DisX
import QuantumZipper.Proofs.Thm18.G3ZqG2PalmR
import QuantumZipper.Proofs.Thm18.G2DisintRG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 engine with an abstract zoom: the `R`-side disintegration and the smoothing headline

Generalized copy (D92) of the zoom-dependent parts of `G2DisintRE.lean`, `G2DisintRF.lean` and
`G2DisintRG.lean` (and of the wiring in `G2Close.lean`), with the plain zoom `zoomLaw γ C`
replaced by an abstract zoom `Z C h y` satisfying `hZm` (joint measurability) and `hZa`
(invariance under equal regularized averages); zoom locality is the hypothesis
`G2ZoomLocStmtZ Z γ`. Zoom-free lemmas (`g2r_kernel_mass`, `g2r_outer_meas`, `g2rMfun`,
`g3Mass_eq_g2rMfun`, `g2OutV_eq_Psi₂`, …) are reused.

Headlines:
* `g2RootLenSmoothZ_of_zoomLoc`: both smoothing nodes `G2RootXLenSmoothStmtZ Z γ`,
  `G2RootRLenSmoothStmtZ Z' γ` from `hZm`, `hZa` and zoom locality, for `Z` and `Z'`;
* `g2FixMixStmtZ_of_fix_zoomLoc`: `G2FixMixStmtZ Z Z' γ` with only the two fixed-point zoom
  nodes and the two zoom-locality nodes open (the Palm identities need `hZc` as well).

Sheffield, arXiv:1012.4797, proof of Prop. 5.5, pp. 65–66, and of Thm. 1.8, p. 71. Own
bookkeeping copied from the originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

variable {Z : ℝ → FieldSample → ℝ → LawD}

/-- **The comparison bound.** -/
theorem g2r_boundZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    {α : Ω₀ → ℝ} (hα : Measurable α)
    (hind : IndepFun (g2Y (g2rφ i m) α) α gffBase.P) (C : ℝ) {s : Set LawD}
    (hs : MeasurableSet s) {E : Type*} [MeasurableSpace E] (Psi : (AdmIdx → ℝ) → E)
    (hPsi : Measurable Psi) {G' : Set (E × ℝ)} (hG' : MeasurableSet G')
    (Λ : (AdmIdx → ℝ) × ℝ → ℝ → ℝ) (hΛ : Measurable (Function.uncurry Λ))
    (T : Set (Ω₀ × ℝ × ℝ))
    (hT : ∀ᵐ ω ∂gffBase.P, (∀ x ∈ g2rM i m, (g2Y (g2rφ i m) α ω, x) ∈ g2rGood γ i m) →
      g2rκM γ i m (g2Y (g2rφ i m) α ω) = (g3Hν γ ω).restrict (g2rM i m) →
      (∀ x ∈ g2rM i m, g2rf γ i m (g2Y (g2rφ i m) α ω, x) (α ω) =
        (g3Hν γ ω (Icc 0 x)).toReal) →
      (∀ κ : ℝ, 0 ≤ κ → κ < g2rR i m → ∀ x ∈ g2rM i m,
        (g3Hν γ ω (Icc 0 (x - κ))).toReal =
          g2rf γ i m (g2Y (g2rφ i m) α ω, x) (α ω) - g2rgap γ i m κ (g2Y (g2rφ i m) α ω, x)) →
      ∀ x ∈ Icc 0 (i.t₂ + i.r₂), T.indicator (1 : Ω₀ × ℝ × ℝ → ℝ≥0∞) (ω, (g3Hν γ ω (Icc 0 x)).toReal, x) =
        (g2rM i m).indicator (fun x =>
          {p : (AdmIdx → ℝ) × ℝ × ℝ | Z C (g2Field γ (g2rφ i m) p.1 p.2.2) p.2.1 ∈ s ∧
            (Psi p.1, Λ (p.1, p.2.1) (g2rf γ i m (p.1, p.2.1) p.2.2)) ∈ G'}.indicator
            (1 : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞) (g2Y (g2rφ i m) α ω, x, α ω)) x) :
    |(g3RootIntR γ i (T.indicator (1 : Ω₀ × ℝ × ℝ → ℝ≥0∞))).toReal -
      (((gffBase.P.map (g2Y (g2rφ i m) α)) ⊗ₘ g2rκM γ i m).prod (gffBase.P.map α)).real
        {p | (p.1, Λ p.1 (g2rf γ i m p.1 p.2)) ∈
          {q : ((AdmIdx → ℝ) × ℝ) × ℝ | Z C (g2Field γ (g2rφ i m) q.1.1 0) q.1.2 ∈ s ∧
            (Psi q.1.1, q.2) ∈ G'}}| ≤
      (∫⁻ ω, ∫⁻ x, g2xZDZ Z γ C (g2rφ i m) s (g2Y (g2rφ i m) α ω, x, α ω)
        ∂(g2rκM γ i m (g2Y (g2rφ i m) α ω)) ∂gffBase.P).toReal := by
  set φ := g2rφ i m
  set Y := g2Y φ α
  set κ := g2rκM γ i m
  set N := gffBase.P.map α
  have hYm : Measurable Y := measurable_g2Y φ hα
  have hf := measurable_g2rf γ i m
  -- the two integrands
  have hZa : Measurable fun p : (AdmIdx → ℝ) × ℝ × ℝ =>
      Λ (p.1, p.2.1) (g2rf γ i m (p.1, p.2.1) p.2.2) :=
    hΛ.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (hf.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))))
  have hz1 : MeasurableSet {p : (AdmIdx → ℝ) × ℝ × ℝ |
      Z C (g2Field γ φ p.1 p.2.2) p.2.1 ∈ s} :=
    (hZm C).comp (((measurable_g2Field γ φ).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).prodMk
      (measurable_fst.comp measurable_snd)) hs
  have hz0 : MeasurableSet {p : (AdmIdx → ℝ) × ℝ × ℝ |
      Z C (g2Field γ φ p.1 0) p.2.1 ∈ s} :=
    (hZm C).comp (((measurable_g2Field γ φ).comp
      (measurable_fst.prodMk measurable_const)).prodMk (measurable_fst.comp measurable_snd)) hs
  have hGp : MeasurableSet {p : (AdmIdx → ℝ) × ℝ × ℝ |
      (Psi p.1, Λ (p.1, p.2.1) (g2rf γ i m (p.1, p.2.1) p.2.2)) ∈ G'} :=
    ((hPsi.comp measurable_fst).prodMk hZa) hG'
  set A₁ := {p : (AdmIdx → ℝ) × ℝ × ℝ | Z C (g2Field γ φ p.1 p.2.2) p.2.1 ∈ s ∧
    (Psi p.1, Λ (p.1, p.2.1) (g2rf γ i m (p.1, p.2.1) p.2.2)) ∈ G'} with hA₁
  set A₂ := {p : (AdmIdx → ℝ) × ℝ × ℝ | Z C (g2Field γ φ p.1 0) p.2.1 ∈ s ∧
    (Psi p.1, Λ (p.1, p.2.1) (g2rf γ i m (p.1, p.2.1) p.2.2)) ∈ G'} with hA₂
  have hA₁m : MeasurableSet A₁ := hz1.inter hGp
  have hA₂m : MeasurableSet A₂ := hz0.inter hGp
  have hZDm := measurable_g2xZDZ hZm γ C φ hs
  have hle : ∀ p, A₁.indicator (1 : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞) p ≤ A₂.indicator 1 p + g2xZDZ Z γ C φ s p ∧
      A₂.indicator (1 : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞) p ≤ A₁.indicator 1 p + g2xZDZ Z γ C φ s p := by
    intro p
    by_cases hd : (Z C (g2Field γ φ p.1 p.2.2) p.2.1 ∈ s ↔
        Z C (g2Field γ φ p.1 0) p.2.1 ∈ s)
    · have hmem : p ∈ A₁ ↔ p ∈ A₂ := and_congr_left fun _ => hd
      have : A₁.indicator (1 : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞) p = A₂.indicator 1 p := by
        by_cases h : p ∈ A₁
        · rw [indicator_of_mem h, indicator_of_mem (hmem.1 h)]
        · rw [indicator_of_notMem h, indicator_of_notMem (mt hmem.2 h)]
      rw [this]; exact ⟨le_self_add, le_self_add⟩
    · have h1 : g2xZDZ Z γ C φ s p = 1 := by
        unfold g2xZDZ; rw [indicator_of_mem (show p ∈ _ from hd)]; rfl
      rw [h1]
      exact ⟨(indicator_le_self' (fun _ _ => zero_le_one) p).trans le_add_self,
        (indicator_le_self' (fun _ _ => zero_le_one) p).trans le_add_self⟩
  -- rooted side
  have hroot := g2r_root_eq hγ hγ2 i hm α T (A₁.indicator 1) hT
  -- product side
  have hprod : (((gffBase.P.map Y) ⊗ₘ κ).prod N)
      {p | (p.1, Λ p.1 (g2rf γ i m p.1 p.2)) ∈
        {q : ((AdmIdx → ℝ) × ℝ) × ℝ | Z C (g2Field γ φ q.1.1 0) q.1.2 ∈ s ∧
          (Psi q.1.1, q.2) ∈ G'}} =
      ∫⁻ ω, ∫⁻ x, A₂.indicator 1 (Y ω, x, α ω) ∂(κ (Y ω)) ∂gffBase.P := by
    have hTm : MeasurableSet {p : ((AdmIdx → ℝ) × ℝ) × ℝ | (p.1, Λ p.1 (g2rf γ i m p.1 p.2)) ∈
        {q : ((AdmIdx → ℝ) × ℝ) × ℝ | Z C (g2Field γ φ q.1.1 0) q.1.2 ∈ s ∧
          (Psi q.1.1, q.2) ∈ G'}} := by
      have e : {p : ((AdmIdx → ℝ) × ℝ) × ℝ | (p.1, Λ p.1 (g2rf γ i m p.1 p.2)) ∈
          {q : ((AdmIdx → ℝ) × ℝ) × ℝ | Z C (g2Field γ φ q.1.1 0) q.1.2 ∈ s ∧
            (Psi q.1.1, q.2) ∈ G'}} = (fun p => (p.1.1, p.1.2, p.2)) ⁻¹' A₂ := by
        ext p; rfl
      rw [e]
      exact (measurable_fst.comp measurable_fst |>.prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) hA₂m
    rw [g2_prod_compProd_apply _ _ _ hTm,
      g2_core_transfer' hYm hα hind κ (measurable_one.indicator hA₂m)]
    rfl
  -- finiteness
  have hmass := g2r_kernel_mass hγ hγ2 i hm α
  have hfin : ∀ {F : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞}, (∀ p, F p ≤ 1) →
      ∫⁻ ω, ∫⁻ x, F (Y ω, x, α ω) ∂(κ (Y ω)) ∂gffBase.P ≠ ⊤ := fun hF =>
    ne_top_of_le_ne_top hmass.ne (lintegral_mono fun ω =>
      (lintegral_mono fun x => hF _).trans_eq lintegral_one)
  have hind1 : ∀ (A : Set ((AdmIdx → ℝ) × ℝ × ℝ)) p, A.indicator (1 : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞) p ≤ 1 :=
    fun A p => indicator_le_self' (fun _ _ => zero_le_one) p
  have hsum : ∀ {F₁ F₂ : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞}, Measurable F₂ →
      (∀ p, F₁ p ≤ F₂ p + g2xZDZ Z γ C φ s p) →
      ∫⁻ ω, ∫⁻ x, F₁ (Y ω, x, α ω) ∂(κ (Y ω)) ∂gffBase.P ≤
        ∫⁻ ω, ∫⁻ x, F₂ (Y ω, x, α ω) ∂(κ (Y ω)) ∂gffBase.P +
          ∫⁻ ω, ∫⁻ x, g2xZDZ Z γ C φ s (Y ω, x, α ω) ∂(κ (Y ω)) ∂gffBase.P := by
    intro F₁ F₂ hF₂ h
    refine (lintegral_mono fun ω => (lintegral_mono fun x => h _).trans_eq
      (lintegral_add_left (hF₂.comp (measurable_const.prodMk
        (measurable_id.prodMk measurable_const))) _)).trans_eq ?_
    exact lintegral_add_left (g2r_outer_meas γ i m hα hF₂) _
  rw [measureReal_def, hprod, hroot]
  exact g2clip_abs_toReal_sub_le (hfin (hind1 A₁)) (hfin (hind1 A₂))
    (hfin fun p => by unfold g2xZDZ; exact indicator_le_self' (fun _ _ => zero_le_one) p)
    (hsum (measurable_one.indicator hA₂m) fun p => (hle p).1)
    (hsum (measurable_one.indicator hA₁m) fun p => (hle p).2)

end Thm18Asm
end QuantumZipper
