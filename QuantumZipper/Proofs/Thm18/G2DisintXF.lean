import QuantumZipper.Proofs.Thm18.G2DisintXE

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `x` side: the comparison of a rooted event with its product form

`g2x_bound`: for an event `T` of margin roots whose indicator is `H(h₀, x, α)` with
`H = 1{zoom(𝔥₀ + h₀ + aφ) ∈ s, (Ψ h₀, Λ(ξ, f ξ a)) ∈ G'}`, the rooted measure of `T` and the
`Q ⊗ N`-measure of `{(ξ, Λ(ξ, f ξ a)) ∈ S}` (zoom read at `a = 0`) differ by at most the zoom error.
Proof: the rooted integral is a root-kernel integral (`g2x_root_eq`), the product measure is the
same integral with `α` integrated out (`g2_core_transfer'`, independence), and the two integrands
differ only on the zoom-disagreement set. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

theorem g2x_outer_meas (γ : ℝ) (i : G3Idx) (m : ℝ) {α : Ω₀ → ℝ} (hα : Measurable α)
    {H : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞} (hH : Measurable H) :
    Measurable fun ω => ∫⁻ x, H (g2Y (g2xφ i m) α ω, x, α ω)
      ∂(g2xκM γ i m (g2Y (g2xφ i m) α ω)) := by
  have hYm := measurable_g2Y (g2xφ i m) hα
  have hf : Measurable fun q : Ω₀ × ℝ => H (g2Y (g2xφ i m) α q.1, q.2, α q.1) :=
    hH.comp ((hYm.comp measurable_fst).prodMk (measurable_snd.prodMk (hα.comp measurable_fst)))
  exact hf.lintegral_kernel_prod_right' (κ := (g2xκM γ i m).comap _ hYm)

/-- **The comparison bound.** -/
theorem g2x_bound {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    {α : Ω₀ → ℝ} (hα : Measurable α)
    (hind : IndepFun (g2Y (g2xφ i m) α) α gffBase.P) (C : ℝ) {s : Set LawD}
    (hs : MeasurableSet s) {E : Type*} [MeasurableSpace E] (Psi : (AdmIdx → ℝ) → E)
    (hPsi : Measurable Psi) {G' : Set (E × ℝ)} (hG' : MeasurableSet G')
    (Λ : (AdmIdx → ℝ) × ℝ → ℝ → ℝ) (hΛ : Measurable (Function.uncurry Λ))
    (T : Set (Ω₀ × ℝ × ℝ))
    (hT : ∀ᵐ ω ∂gffBase.P, (∀ x ∈ g2xM i m, (g2Y (g2xφ i m) α ω, x) ∈ g2xGood γ i m) →
      g2xκM γ i m (g2Y (g2xφ i m) α ω) = (g3Hν γ ω).restrict (g2xM i m) →
      (∀ x ∈ g2xM i m, g2xf γ i m (g2Y (g2xφ i m) α ω, x) (α ω) =
        (g3Hν γ ω (Icc x 0)).toReal) →
      (∀ κ : ℝ, 0 ≤ κ → κ < g2xR i m → ∀ x ∈ g2xM i m,
        (g3Hν γ ω (Icc (x + κ) 0)).toReal =
          g2xf γ i m (g2Y (g2xφ i m) α ω, x) (α ω) - g2xgap γ i m κ (g2Y (g2xφ i m) α ω, x)) →
      ∀ x ∈ Icc (-i.δ) 0, T.indicator (1 : Ω₀ × ℝ × ℝ → ℝ≥0∞) (ω, (g3Hν γ ω (Icc x 0)).toReal, x) =
        (g2xM i m).indicator (fun x =>
          {p : (AdmIdx → ℝ) × ℝ × ℝ | zoomLaw γ C (g2Field γ (g2xφ i m) p.1 p.2.2) p.2.1 ∈ s ∧
            (Psi p.1, Λ (p.1, p.2.1) (g2xf γ i m (p.1, p.2.1) p.2.2)) ∈ G'}.indicator
            (1 : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞) (g2Y (g2xφ i m) α ω, x, α ω)) x) :
    |(g3RootInt γ i (T.indicator (1 : Ω₀ × ℝ × ℝ → ℝ≥0∞))).toReal -
      (((gffBase.P.map (g2Y (g2xφ i m) α)) ⊗ₘ g2xκM γ i m).prod (gffBase.P.map α)).real
        {p | (p.1, Λ p.1 (g2xf γ i m p.1 p.2)) ∈
          {q : ((AdmIdx → ℝ) × ℝ) × ℝ | zoomLaw γ C (g2Field γ (g2xφ i m) q.1.1 0) q.1.2 ∈ s ∧
            (Psi q.1.1, q.2) ∈ G'}}| ≤
      (∫⁻ ω, ∫⁻ x, g2xZD γ C (g2xφ i m) s (g2Y (g2xφ i m) α ω, x, α ω)
        ∂(g2xκM γ i m (g2Y (g2xφ i m) α ω)) ∂gffBase.P).toReal := by
  set φ := g2xφ i m
  set Y := g2Y φ α
  set κ := g2xκM γ i m
  set N := gffBase.P.map α
  have hYm : Measurable Y := measurable_g2Y φ hα
  have hf := measurable_g2xf γ i m
  -- the two integrands
  have hZa : Measurable fun p : (AdmIdx → ℝ) × ℝ × ℝ =>
      Λ (p.1, p.2.1) (g2xf γ i m (p.1, p.2.1) p.2.2) :=
    hΛ.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (hf.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))))
  have hz1 : MeasurableSet {p : (AdmIdx → ℝ) × ℝ × ℝ |
      zoomLaw γ C (g2Field γ φ p.1 p.2.2) p.2.1 ∈ s} :=
    (measurable_zoomLaw γ C).comp (((measurable_g2Field γ φ).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).prodMk
      (measurable_fst.comp measurable_snd)) hs
  have hz0 : MeasurableSet {p : (AdmIdx → ℝ) × ℝ × ℝ |
      zoomLaw γ C (g2Field γ φ p.1 0) p.2.1 ∈ s} :=
    (measurable_zoomLaw γ C).comp (((measurable_g2Field γ φ).comp
      (measurable_fst.prodMk measurable_const)).prodMk (measurable_fst.comp measurable_snd)) hs
  have hGp : MeasurableSet {p : (AdmIdx → ℝ) × ℝ × ℝ |
      (Psi p.1, Λ (p.1, p.2.1) (g2xf γ i m (p.1, p.2.1) p.2.2)) ∈ G'} :=
    ((hPsi.comp measurable_fst).prodMk hZa) hG'
  set A₁ := {p : (AdmIdx → ℝ) × ℝ × ℝ | zoomLaw γ C (g2Field γ φ p.1 p.2.2) p.2.1 ∈ s ∧
    (Psi p.1, Λ (p.1, p.2.1) (g2xf γ i m (p.1, p.2.1) p.2.2)) ∈ G'} with hA₁
  set A₂ := {p : (AdmIdx → ℝ) × ℝ × ℝ | zoomLaw γ C (g2Field γ φ p.1 0) p.2.1 ∈ s ∧
    (Psi p.1, Λ (p.1, p.2.1) (g2xf γ i m (p.1, p.2.1) p.2.2)) ∈ G'} with hA₂
  have hA₁m : MeasurableSet A₁ := hz1.inter hGp
  have hA₂m : MeasurableSet A₂ := hz0.inter hGp
  have hZDm := measurable_g2xZD γ C φ hs
  have hle : ∀ p, A₁.indicator (1 : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞) p ≤ A₂.indicator 1 p + g2xZD γ C φ s p ∧
      A₂.indicator (1 : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞) p ≤ A₁.indicator 1 p + g2xZD γ C φ s p := by
    intro p
    by_cases hd : (zoomLaw γ C (g2Field γ φ p.1 p.2.2) p.2.1 ∈ s ↔
        zoomLaw γ C (g2Field γ φ p.1 0) p.2.1 ∈ s)
    · have hmem : p ∈ A₁ ↔ p ∈ A₂ := and_congr_left fun _ => hd
      have : A₁.indicator (1 : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞) p = A₂.indicator 1 p := by
        by_cases h : p ∈ A₁
        · rw [indicator_of_mem h, indicator_of_mem (hmem.1 h)]
        · rw [indicator_of_notMem h, indicator_of_notMem (mt hmem.2 h)]
      rw [this]; exact ⟨le_self_add, le_self_add⟩
    · have h1 : g2xZD γ C φ s p = 1 := by
        unfold g2xZD; rw [indicator_of_mem (show p ∈ _ from hd)]; rfl
      rw [h1]
      exact ⟨(indicator_le_self' (fun _ _ => zero_le_one) p).trans le_add_self,
        (indicator_le_self' (fun _ _ => zero_le_one) p).trans le_add_self⟩
  -- rooted side
  have hroot := g2x_root_eq hγ hγ2 i hm α T (A₁.indicator 1) hT
  -- product side
  have hprod : (((gffBase.P.map Y) ⊗ₘ κ).prod N)
      {p | (p.1, Λ p.1 (g2xf γ i m p.1 p.2)) ∈
        {q : ((AdmIdx → ℝ) × ℝ) × ℝ | zoomLaw γ C (g2Field γ φ q.1.1 0) q.1.2 ∈ s ∧
          (Psi q.1.1, q.2) ∈ G'}} =
      ∫⁻ ω, ∫⁻ x, A₂.indicator 1 (Y ω, x, α ω) ∂(κ (Y ω)) ∂gffBase.P := by
    have hTm : MeasurableSet {p : ((AdmIdx → ℝ) × ℝ) × ℝ | (p.1, Λ p.1 (g2xf γ i m p.1 p.2)) ∈
        {q : ((AdmIdx → ℝ) × ℝ) × ℝ | zoomLaw γ C (g2Field γ φ q.1.1 0) q.1.2 ∈ s ∧
          (Psi q.1.1, q.2) ∈ G'}} := by
      have e : {p : ((AdmIdx → ℝ) × ℝ) × ℝ | (p.1, Λ p.1 (g2xf γ i m p.1 p.2)) ∈
          {q : ((AdmIdx → ℝ) × ℝ) × ℝ | zoomLaw γ C (g2Field γ φ q.1.1 0) q.1.2 ∈ s ∧
            (Psi q.1.1, q.2) ∈ G'}} = (fun p => (p.1.1, p.1.2, p.2)) ⁻¹' A₂ := by
        ext p; rfl
      rw [e]
      exact (measurable_fst.comp measurable_fst |>.prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) hA₂m
    rw [g2_prod_compProd_apply _ _ _ hTm,
      g2_core_transfer' hYm hα hind κ (measurable_one.indicator hA₂m)]
    rfl
  -- finiteness
  have hmass := g2x_kernel_mass hγ hγ2 i hm α
  have hfin : ∀ {F : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞}, (∀ p, F p ≤ 1) →
      ∫⁻ ω, ∫⁻ x, F (Y ω, x, α ω) ∂(κ (Y ω)) ∂gffBase.P ≠ ⊤ := fun hF =>
    ne_top_of_le_ne_top hmass.ne (lintegral_mono fun ω =>
      (lintegral_mono fun x => hF _).trans_eq lintegral_one)
  have hind1 : ∀ (A : Set ((AdmIdx → ℝ) × ℝ × ℝ)) p, A.indicator (1 : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞) p ≤ 1 :=
    fun A p => indicator_le_self' (fun _ _ => zero_le_one) p
  have hsum : ∀ {F₁ F₂ : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞}, Measurable F₂ →
      (∀ p, F₁ p ≤ F₂ p + g2xZD γ C φ s p) →
      ∫⁻ ω, ∫⁻ x, F₁ (Y ω, x, α ω) ∂(κ (Y ω)) ∂gffBase.P ≤
        ∫⁻ ω, ∫⁻ x, F₂ (Y ω, x, α ω) ∂(κ (Y ω)) ∂gffBase.P +
          ∫⁻ ω, ∫⁻ x, g2xZD γ C φ s (Y ω, x, α ω) ∂(κ (Y ω)) ∂gffBase.P := by
    intro F₁ F₂ hF₂ h
    refine (lintegral_mono fun ω => (lintegral_mono fun x => h _).trans_eq
      (lintegral_add_left (hF₂.comp (measurable_const.prodMk
        (measurable_id.prodMk measurable_const))) _)).trans_eq ?_
    exact lintegral_add_left (g2x_outer_meas γ i m hα hF₂) _
  rw [measureReal_def, hprod, hroot]
  exact g2clip_abs_toReal_sub_le (hfin (hind1 A₁)) (hfin (hind1 A₂))
    (hfin fun p => by unfold g2xZD; exact indicator_le_self' (fun _ _ => zero_le_one) p)
    (hsum (measurable_one.indicator hA₂m) fun p => (hle p).1)
    (hsum (measurable_one.indicator hA₁m) fun p => (hle p).2)

end Thm18Asm
end QuantumZipper
