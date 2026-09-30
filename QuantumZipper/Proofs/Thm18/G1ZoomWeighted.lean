import QuantumZipper.Proofs.Thm18.G1ZoomModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-ZOOM: the wedge law from D3⁺(i) and a *weighted, approximate* model mixture

Theorem 1.8, node G1, part (a) (`G1ZoomPartStmt`). `G1ZoomModel.lean` reduces it to D3⁺(i) and
an *exact, unweighted* mixture of D3⁺ models (`G1ZoomMix`). The route chosen in
`handoff/G1-ZOOM.md` (rerooting invariance of the side surface from E6, then a Palm average over
the new root, then the zoom of Proposition 1.6 at a quantum-typical boundary point) produces
instead a mixture with **weights** (the Palm window `1{ν[b,0] ≤ U}`, and the local density of the
`(γ − 2/γ)`-wedge with respect to the free field near a boundary point `b ≠ 0`), and only up to an
arbitrary error `ε` (the weights are made `condSigma`-measurable by conditioning at a small
radius). This file gives the interface for that form and proves the wedge law from it.

Sources. The zoom convergence itself is D3⁺(i) (`D3PlusIStmtRich`, decision D25; Sheffield,
arXiv:1012.4797, proof of Prop. 1.6, p. 25; TV-local form Duplantier–Miller–Sheffield,
arXiv:1409.7055, Props. 4.7–4.8), whose conclusion is uniform over `condSigma`-measurable test
functionals `Φ(ω, ·)`; the weights enter exactly there. The rest (per-model limit, dominated
convergence over the mixture, `ε → 0`, uniqueness of laws via `fieldLawFull_eq_of_locFieldFull`)
is own elementary bookkeeping, as in `isQuantumWedge_of_mix`.

* `g1zWMdl`: the weighted model integral `E[w · Γ(local canonical data of the level-`L` model)]`.
* `G1ZoomWApproxT γ tgt` / `G1ZoomWApprox γ P Z` (target `E Γ(locFieldFull R (canonical γ Z))`): for every `R`, measurable `Γ ∈ [0,1]` and `ε > 0` there is a finite
  mixture of D3⁺ models (`α = γ`) with bounded `condSigma`-measurable weights `w`, of total mass
  within `ε` of `1`, whose weighted integrals are eventually (in `L`) within `ε` of
  `E Γ(locFieldFull R (canonical γ Z))`.
* `isQuantumWedge_of_wapprox`: D3⁺(i) + `G1ZoomWApprox` ⇒ `canonical γ Z` is a `γ`-quantum wedge.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus

/-- The **weighted model integral**: `E[w · Γ(locFieldFull R (canonicalOn γ Y_L (halfDisc r)))]`
for the D3⁺ model `Y_L = zoomModel γ γ L ρ₀ X g` (`α = γ`). -/
def g1zWMdl (γ r L : ℝ) (R : ℕ) (ρ₀ : Measure ℂ) {Ω₀ : Type} [MeasurableSpace Ω₀]
    (P₀ : Measure Ω₀) (X : Ω₀ → FieldSample) (g : Ω₀ → ℂ → ℝ) (w : Ω₀ → ℝ≥0∞)
    (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, w ω * Γ (locFieldFull R (canonicalOn γ (zoomModel γ γ L ρ₀ (X ω) (g ω)) (halfDisc r))) ∂P₀

/-- **Weighted approximate model mixture at one test functional** (the interface produced by
the Palm step of G1-ZOOM, `handoff/G1-ZOOM.md`): for the rich local data at radius `R`, the
functional `Γ`, the error `ε` and the target value `a`: a finite measure `ρ` on an index type `T`,
for each `x ∈ T` a D3⁺ `Setup` with `α = γ` on a common probability space, weights `w x`
measurable for `condSigma (Ξ x) (X x) (r x)` and bounded by a constant `M`, the weighted model
integrals and the masses `E w x` a.e.-measurable in `x`, total mass `∫ E w x dρ` within `ε` of
`1`, and eventually in `L` the mixed weighted integral within `ε` of `a`. -/
def G1WApproxAt (γ : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) (ε a : ℝ≥0∞) :
    Prop :=
  ∃ (T : Type) (_ : MeasurableSpace T) (ρ : Measure T) (r : T → ℝ) (ρ₀ : T → Measure ℂ)
    (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (X : T → Ω₀ → FieldSample)
    (E' : Type) (_ : MeasurableSpace E') (Ξ : T → Ω₀ → E') (g : T → Ω₀ → ℂ → ℝ)
    (w : T → Ω₀ → ℝ≥0∞) (M : ℝ≥0),
    IsFiniteMeasure ρ ∧ IsProbabilityMeasure P₀ ∧
    (∀ x, Setup γ γ (r x) (ρ₀ x) P₀ (X x) (Ξ x) (g x)) ∧
    (∀ x, Measurable[condSigma (Ξ x) (X x) (r x)] (w x)) ∧ (∀ x ω, w x ω ≤ M) ∧
    (∀ L, AEMeasurable (fun x => g1zWMdl γ (r x) L R (ρ₀ x) P₀ (X x) (g x) (w x) Γ) ρ) ∧
    AEMeasurable (fun x => ∫⁻ ω, w x ω ∂P₀) ρ ∧
    ∫⁻ x, ∫⁻ ω, w x ω ∂P₀ ∂ρ ≤ 1 + ε ∧ 1 ≤ ∫⁻ x, ∫⁻ ω, w x ω ∂P₀ ∂ρ + ε ∧
    ∀ᶠ L in atTop,
      ∫⁻ x, g1zWMdl γ (r x) L R (ρ₀ x) P₀ (X x) (g x) (w x) Γ ∂ρ ≤ a + ε ∧
        a ≤ ∫⁻ x, g1zWMdl γ (r x) L R (ρ₀ x) P₀ (X x) (g x) (w x) Γ ∂ρ + ε

/-- **Weighted approximate model mixtures** for a target functional `tgt R Γ`: `G1WApproxAt` for
every `R`, measurable `Γ ∈ [0,1]` and `ε > 0`. -/
def G1ZoomWApproxT (γ : ℝ)
    (tgt : ℕ → ((ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) → ℝ≥0∞) : Prop :=
  ∀ R : ℕ, ∀ Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
  ∀ ε : ℝ≥0∞, 0 < ε → G1WApproxAt γ R Γ ε (tgt R Γ)

/-- `G1ZoomWApproxT` for the target `E Γ(locFieldFull R (canonical γ Z))`. -/
def G1ZoomWApprox (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → FieldSample) : Prop :=
  G1ZoomWApproxT γ fun R Γ => ∫⁻ ω, Γ (locFieldFull R (canonical γ (Z ω))) ∂P

/-- The target of `G1ZoomWApproxT` only matters for measurable `Γ ∈ [0,1]`. -/
theorem G1ZoomWApproxT.congr {γ : ℝ}
    {tgt tgt' : ℕ → ((ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) → ℝ≥0∞}
    (h : ∀ R Γ, Measurable Γ → (∀ y, Γ y ≤ 1) → tgt R Γ = tgt' R Γ)
    (happ : G1ZoomWApproxT γ tgt) : G1ZoomWApproxT γ tgt' := by
  intro R Γ hΓ hΓ1 ε hε
  rw [← h R Γ hΓ hΓ1]
  exact happ R Γ hΓ hΓ1 ε hε

/-- **D3⁺(i) with a weight**: the weighted model integrals converge to `E w · E Γ(wedge)`. -/
theorem g1zW_tendsto_of_D3 (hD3 : D3PlusIStmtRich) {γ r : ℝ} {ρ₀ : Measure ℂ} {Ω₀ : Type}
    [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {X : Ω₀ → FieldSample}
    {E' : Type} [MeasurableSpace E'] {Ξ : Ω₀ → E'} {g : Ω₀ → ℂ → ℝ}
    (hS : Setup γ γ r ρ₀ P₀ X Ξ g) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y' : Ω' → FieldSample} (hW : IsQuantumWedge γ γ Y' P') (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (hΓ1 : ∀ y, Γ y ≤ 1)
    {w : Ω₀ → ℝ≥0∞} {M : ℝ≥0} (hw : Measurable[condSigma Ξ X r] w) (hwM : ∀ ω, w ω ≤ M) :
    Tendsto (fun L => g1zWMdl γ r L R ρ₀ P₀ X g w Γ) atTop
      (𝓝 ((∫⁻ ω, w ω ∂P₀) * ∫⁻ ω', Γ (locFieldFull R (Y' ω')) ∂P')) := by
  set c := ∫⁻ ω', Γ (locFieldFull R (Y' ω')) ∂P' with hc
  set M' : ℝ≥0∞ := (M : ℝ≥0∞) + 1 with hM'
  have hM'0 : M' ≠ 0 := by simp [hM']
  have hM'top : M' ≠ ⊤ := by simp [hM']
  have hinv : M'⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hM'0
  have hc1 : c ≤ 1 := g1z_lintegral_le_one hΓ1 _
  have hwtop : ∫⁻ ω, w ω ∂P₀ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := (M : ℝ≥0∞)) ENNReal.coe_ne_top ?_
    calc ∫⁻ ω, w ω ∂P₀ ≤ ∫⁻ _ω, (M : ℝ≥0∞) ∂P₀ := lintegral_mono hwM
      _ = M := by simp
  set t := (∫⁻ ω, w ω ∂P₀) * c with ht
  have httop : t ≠ ⊤ := ENNReal.mul_ne_top hwtop (ne_top_of_le_ne_top ENNReal.one_ne_top hc1)
  -- the test functional `Φ = M'⁻¹ · w · Γ`
  let Φ : Ω₀ × ((ℕ → ℝ) × (TestFun H → ℝ)) → ℝ≥0∞ := fun p => M'⁻¹ * (w p.1 * Γ p.2)
  have hmΦ : Measurable[(condSigma Ξ X r).prod inferInstance] Φ := by
    let _ : MeasurableSpace Ω₀ := condSigma Ξ X r
    exact ((hw.comp measurable_fst).mul (hΓ.comp measurable_snd)).const_mul _
  have hΦ1 : ∀ p, Φ p ≤ 1 := by
    intro p
    have h1 : w p.1 * Γ p.2 ≤ M' :=
      calc w p.1 * Γ p.2 ≤ (M : ℝ≥0∞) * 1 := mul_le_mul' (hwM _) (hΓ1 _)
        _ ≤ M' := by rw [mul_one, hM']; exact le_self_add
    calc Φ p ≤ M'⁻¹ * M' := mul_le_mul' le_rfl h1
      _ = 1 := ENNReal.inv_mul_cancel hM'0 hM'top
  have hlhs : ∀ L, ∫⁻ ω, Φ (ω, locFieldFull R
      (canonicalOn γ (zoomModel γ γ L ρ₀ (X ω) (g ω)) (halfDisc r))) ∂P₀ =
      M'⁻¹ * g1zWMdl γ r L R ρ₀ P₀ X g w Γ := fun L =>
    lintegral_const_mul' _ _ hinv
  have hrhs : ∫⁻ ω, ∫⁻ ω', Φ (ω, locFieldFull R (Y' ω')) ∂P' ∂P₀ = M'⁻¹ * t := by
    have hin : ∀ ω, ∫⁻ ω', Φ (ω, locFieldFull R (Y' ω')) ∂P' = M'⁻¹ * w ω * c := by
      intro ω
      have hne : M'⁻¹ * w ω ≠ ⊤ :=
        ENNReal.mul_ne_top hinv (ne_top_of_le_ne_top ENNReal.coe_ne_top (hwM ω))
      simp only [Φ, ← mul_assoc]
      exact lintegral_const_mul' _ _ hne
    simp only [hin]
    rw [lintegral_mul_const' _ _ (ne_top_of_le_ne_top ENNReal.one_ne_top hc1),
      lintegral_const_mul' _ _ hinv, ht, mul_assoc]
  have hlim : Tendsto (fun L => M'⁻¹ * g1zWMdl γ r L R ρ₀ P₀ X g w Γ) atTop (𝓝 (M'⁻¹ * t)) := by
    rw [ENNReal.tendsto_nhds (ENNReal.mul_ne_top hinv httop)]
    intro ε hε
    filter_upwards [hD3 γ γ r ρ₀ P₀ X Ξ g P' Y' hS hW R ε hε] with L hL
    have hd := hL Φ hmΦ hΦ1
    dsimp only at hd
    rw [hlhs L, hrhs] at hd
    exact ⟨tsub_le_iff_right.2 hd.2, hd.1⟩
  have h2 := ENNReal.Tendsto.const_mul hlim (Or.inr hM'top)
  have hcancel : ∀ y : ℝ≥0∞, M' * (M'⁻¹ * y) = y := fun y => by
    rw [← mul_assoc, ENNReal.mul_inv_cancel hM'0 hM'top, one_mul]
  simp only [hcancel] at h2
  exact h2

/-- **One approximation step**: with `a = E Γ(canonical Z)` and `c = E Γ(wedge)`,
`a ≤ c + 2ε` and `c ≤ a + 2ε` (per-model limit, dominated convergence over `ρ`, mass bounds). -/
theorem g1zW_close (hD3 : D3PlusIStmtRich) {γ : ℝ}
    {tgt : ℕ → ((ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) → ℝ≥0∞} (happ : G1ZoomWApproxT γ tgt)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y' : Ω' → FieldSample} (hW : IsQuantumWedge γ γ Y' P') (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞}
    (hΓ : Measurable Γ) (hΓ1 : ∀ y, Γ y ≤ 1) (ε : ℝ≥0∞) (hε : 0 < ε) :
    tgt R Γ ≤ ∫⁻ ω', Γ (locFieldFull R (Y' ω')) ∂P' + ε + ε ∧
      ∫⁻ ω', Γ (locFieldFull R (Y' ω')) ∂P' ≤ tgt R Γ + ε + ε := by
  obtain ⟨T, _, ρ, r, ρ₀, Ω₀, _, P₀, X, E', _, Ξ, g, w, M, hρ, hP₀, hS, hwm, hwM, hmeas,
    hmeasw, hm1, hm2, hev⟩ := happ R Γ hΓ hΓ1 ε hε
  set a := tgt R Γ with ha
  set c := ∫⁻ ω', Γ (locFieldFull R (Y' ω')) ∂P' with hc
  set m := ∫⁻ x, ∫⁻ ω, w x ω ∂P₀ ∂ρ with hm
  have hc1 : c ≤ 1 := g1z_lintegral_le_one hΓ1 _
  have hctop : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc1
  have hbound : ∀ L x, g1zWMdl γ (r x) L R (ρ₀ x) P₀ (X x) (g x) (w x) Γ ≤ M := by
    intro L x
    calc g1zWMdl γ (r x) L R (ρ₀ x) P₀ (X x) (g x) (w x) Γ ≤ ∫⁻ _ω, (M : ℝ≥0∞) ∂P₀ :=
          lintegral_mono fun ω => (mul_le_mul' (hwM x ω) (hΓ1 _)).trans (by rw [mul_one])
      _ = M := by rw [lintegral_const, measure_univ, mul_one]
  have hmix : Tendsto (fun L => ∫⁻ x, g1zWMdl γ (r x) L R (ρ₀ x) P₀ (X x) (g x) (w x) Γ ∂ρ)
      atTop (𝓝 (m * c)) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := ρ)
      (fun _ => (M : ℝ≥0∞)) (Eventually.of_forall hmeas)
      (Eventually.of_forall fun L => ae_of_all _ fun x => hbound L x)
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      (ae_of_all _ fun x => g1zW_tendsto_of_D3 hD3 (hS x) hW R hΓ hΓ1 (hwm x) (hwM x))
    rwa [lintegral_mul_const' _ _ hctop] at h
  have h1 : m * c ≤ a + ε := le_of_tendsto hmix (hev.mono fun L h => h.1)
  have h2 : a - ε ≤ m * c :=
    ge_of_tendsto hmix (hev.mono fun L h => tsub_le_iff_right.2 h.2)
  have h2' : a ≤ m * c + ε := tsub_le_iff_right.1 h2
  have hεc : ε * c ≤ ε := by
    calc ε * c ≤ ε * 1 := mul_le_mul' le_rfl hc1
      _ = ε := mul_one ε
  constructor
  · calc a ≤ m * c + ε := h2'
      _ ≤ (1 + ε) * c + ε := add_le_add (mul_le_mul' hm1 le_rfl) le_rfl
      _ = c + ε * c + ε := by rw [add_mul, one_mul]
      _ ≤ c + ε + ε := add_le_add (add_le_add le_rfl hεc) le_rfl
  · calc c = 1 * c := (one_mul c).symm
      _ ≤ (m + ε) * c := mul_le_mul' hm2 le_rfl
      _ = m * c + ε * c := add_mul _ _ _
      _ ≤ a + ε + ε := add_le_add h1 hεc

/-- **The wedge law from D3⁺(i) and a weighted approximate model mixture** (own bookkeeping; the
zoom convergence is D3⁺(i): Sheffield Prop. 1.6, DMS Props. 4.7–4.8). -/
theorem isQuantumWedge_of_wapprox (hD3 : D3PlusIStmtRich) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → FieldSample}
    (hZ : AEMeasurable (fun ω => WedgeMeas.dataFull H (canonical γ (Z ω))) P)
    (happ : G1ZoomWApprox γ P Z) :
    IsQuantumWedge γ γ (fun ω => canonical γ (Z ω)) P := by
  have hα := gamma_lt_Qc hγ hγ2
  obtain ⟨Ω', _, P', Y', -, hP', hW, -, -, -⟩ :=
    NonVacuity.exists_wedge_indep_BM_uncond_prob_uncond hγ hγ2 hα
  have hW' : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y' ω)) P' :=
    WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
      (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα)
      (WedgeInf.wedgeInfiniteTotal hγ hγ2 hα) hγ hγ2 hW
  have heq : fieldLawFull H (fun ω => canonical γ (Z ω)) P = fieldLawFull H Y' P' := by
    refine fieldLawFull_eq_of_locFieldFull hZ hW' fun R Γ hΓ hΓ1 => ?_
    have key : ∀ ε : ℝ≥0, 0 < ε →
        (∫⁻ ω, Γ (locFieldFull R (canonical γ (Z ω))) ∂P ≤
            ∫⁻ ω', Γ (locFieldFull R (Y' ω')) ∂P' + ε) ∧
          ∫⁻ ω', Γ (locFieldFull R (Y' ω')) ∂P' ≤
            ∫⁻ ω, Γ (locFieldFull R (canonical γ (Z ω))) ∂P + ε := by
      intro ε hε
      have hε2 : 0 < (ε : ℝ≥0∞) / 2 :=
        ENNReal.half_pos (by exact_mod_cast hε.ne')
      obtain ⟨k1, k2⟩ := g1zW_close hD3 happ hW R hΓ hΓ1 _ hε2
      rw [add_assoc, ENNReal.add_halves] at k1 k2
      exact ⟨k1, k2⟩
    exact le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => (key ε hε).1)
      (ENNReal.le_of_forall_pos_le_add fun ε hε _ => (key ε hε).2)
  obtain ⟨-, Ω'', _, P'', X'', A'', h1, h2, h3, h4, h5⟩ := hW
  exact ⟨hα, Ω'', _, P'', X'', A'', h1, h2, h3, h4, heq.trans h5⟩

end Thm18Asm
end QuantumZipper
