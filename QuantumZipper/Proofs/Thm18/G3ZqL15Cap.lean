import QuantumZipper.Proofs.Thm18.G3ZqG3LRegG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (15): pathwise cap locality from goodness at typical points only

Copy of `R18.G3PlCapLocGZ` / `g3PlCapLocGZ_of_ball` (G3ZqG3LCap) where the goodness of the second
field is asked only at `ν_{y'}`-a.e. point `x` and at its length partner `R(x)`, instead of at
every point: the consumer is a dominated convergence against the boundary measure on the window,
which equals `ν_{y'}` there. Sheffield, arXiv:1012.4797, pp. 70–72. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

namespace G3ZqL

/-- **Pathwise locality of the capped functional under goodness conditions** (hypothesis form). -/
def G3PlCapLocAE (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ : ℝ)
    (Gd Gd' : FieldSample → ℝ → Prop) : Prop :=
  ∀ δ U : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ s ∈ lawCyl, ∀ t ∈ lawCyl, ∀ y y' : FieldSample,
    IsLQGGood γ y → IsLQGGood γ y' → FcAgree (ball (0 : ℂ) 1) y y' →
    (∀ᵐ x ∂(qBoundaryMeasure γ y'), Gd y' x ∧ Gd' y' (g3zPartner γ y' x)) →
    g3pl4Sep γ δ y → ∀ ε : ℝ≥0∞, 0 < ε →
    ∀ᶠ L in (atTop : Filter ℝ),
      g3pl4PhiCapZ Z Z' γ δ U L s t y ≤ g3pl4PhiCapZ Z Z' γ δ U L s t y' + ε

section PtwAE

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}
variable {γ δ U : ℝ} {s t : Set LawD} {y y' : FieldSample}

variable (hag : FcAgree (ball (0 : ℂ) 1) y y')
  (hνr : (qBoundaryMeasure γ y).restrict (Icc (-(1 / 2)) (1 / 2)) =
    (qBoundaryMeasure γ y').restrict (Icc (-(1 / 2)) (1 / 2)))
  (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
  (hsep : qBoundaryMeasure γ y (Icc (-δ) 0) < qBoundaryMeasure γ y (Icc (-(1 / 2)) 0))
  (hR : qBoundaryMeasure γ y (Icc (-δ) 0) ≤ qBoundaryMeasure γ y (Icc 0 (1 / 4)))

include hag hνr hδ hδ4 hsep hR in
/-- The disagreement mass on the window tends to `0` as the level grows. -/
theorem g3pl4_tendsto_EAE
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    {Gd Gd' : FieldSample → ℝ → Prop}
    (hB : G3ZqZoomBallLocGZ Z Gd) (hB' : G3ZqZoomBallLocGZ Z' Gd') (hs : s ∈ lawCyl) (ht : t ∈ lawCyl)
    (hgood : ∀ᵐ x ∂(qBoundaryMeasure γ y'), Gd y' x ∧ Gd' y' (g3zPartner γ y' x)) :
    Tendsto (fun L => ∫⁻ x in g3pl4W γ δ U y, (g3pl4EZ Z Z' γ L s t y y').indicator 1 x
      ∂qBoundaryMeasure γ y) atTop (𝓝 0) := by
  have hsm := measurableSet_lawCyl hs
  have htm := measurableSet_lawCyl ht
  have h0 : (0 : ℝ≥0∞) = ∫⁻ _ in g3pl4W γ δ U y, 0 ∂qBoundaryMeasure γ y := by simp
  rw [h0]
  refine tendsto_lintegral_filter_of_dominated_convergence' (fun _ => 1)
    (Eventually.of_forall fun L =>
      (measurable_const.indicator (g3pl4_measurableSet_EZ hZm hZm' γ L hsm htm y y')).aemeasurable)
    (Eventually.of_forall fun L => ae_of_all _ fun x => Set.indicator_le (fun _ _ => le_rfl) x)
    ?_ ?_
  · rw [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    refine ne_top_of_le_ne_top (qBoundaryMeasure_Icc_lt_top γ y (-(1 / 2)) 0).ne
      (measure_mono fun x hx => ⟨(g3pl4_W_gt hsep hx).le, hx.1.le⟩)
  · have hWm := g3pl4_measurableSet_W γ δ U y
    have hWsub : g3pl4W γ δ U y ⊆ Icc (-(1 / 2) : ℝ) (1 / 2) := fun x hx =>
      ⟨(g3pl4_W_gt hsep hx).le, by linarith [hx.1]⟩
    have hrest : (qBoundaryMeasure γ y).restrict (g3pl4W γ δ U y) =
        (qBoundaryMeasure γ y').restrict (g3pl4W γ δ U y) := by
      rw [← Measure.restrict_restrict_of_subset hWsub, hνr,
        Measure.restrict_restrict_of_subset hWsub]
    rw [hrest]
    filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem hWm] with x hgx hx
    obtain ⟨hpe, hp0, hp4⟩ := g3pl4_partner_eq hνr hδ hδ4 hsep hR hx
    have hx2 := g3pl4_W_gt hsep hx
    have hxa : |x| < 1 := by rw [abs_lt]; constructor <;> linarith [hx.1]
    have hpa : |g3zPartner γ y x| < 1 := by rw [abs_lt]; constructor <;> linarith
    have ev1 := hB s hs y y' x _ isOpen_ball hag
      (by rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hxa) hgx.1
    have ev2 := hB' t ht y y' _ _ isOpen_ball hag
      (by rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hpa) (hpe ▸ hgx.2)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [ev1, ev2] with L h1 h2
    have hn : x ∉ g3pl4EZ Z Z' γ L s t y y' := by
      intro hE
      simp only [g3pl4EZ, mem_union, mem_symmDiff, mem_preimage] at hE
      rcases hE with (⟨ha, hb⟩ | ⟨ha, hb⟩) | (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · exact hb (h1.1 ha)
      · exact hb (h1.2 ha)
      · exact hb (h2.1 ha)
      · exact hb (h2.2 ha)
    rw [indicator_of_notMem hn]

include hag hνr hδ hδ4 hsep hR in
/-- **Pathwise locality of the capped Palm functional.** -/
theorem g3pl4_phiCap_le_of_agreeAE
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    {Gd Gd' : FieldSample → ℝ → Prop}
    (hB : G3ZqZoomBallLocGZ Z Gd) (hB' : G3ZqZoomBallLocGZ Z' Gd') (hs : s ∈ lawCyl) (ht : t ∈ lawCyl)
    (hgood : ∀ᵐ x ∂(qBoundaryMeasure γ y'), Gd y' x ∧ Gd' y' (g3zPartner γ y' x))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ L in atTop, g3pl4PhiCapZ Z Z' γ δ U L s t y ≤ g3pl4PhiCapZ Z Z' γ δ U L s t y' + ε := by
  have hT := g3pl4_tendsto_EAE (U := U) hag hνr hδ hδ4 hsep hR hZm hZm' hB hB' hs ht hgood
  filter_upwards [(tendsto_order.1 hT).2 ε hε] with L hL
  have hWm := g3pl4_measurableSet_W γ δ U y
  have hWsub : g3pl4W γ δ U y ⊆ Icc (-(1 / 2) : ℝ) (1 / 2) := fun x hx =>
    ⟨(g3pl4_W_gt hsep hx).le, by linarith [hx.1]⟩
  have hrest : (qBoundaryMeasure γ y).restrict (g3pl4W γ δ U y) =
      (qBoundaryMeasure γ y').restrict (g3pl4W γ δ U y) := by
    rw [← Measure.restrict_restrict_of_subset hWsub, hνr, Measure.restrict_restrict_of_subset hWsub]
  have hmain : ∫⁻ x in g3pl4W γ δ U y, s.indicator (1 : LawD → ℝ≥0∞) (Z L y' x) *
      t.indicator 1 (Z' L y' (g3zPartner γ y' x)) ∂qBoundaryMeasure γ y =
      g3pl4PhiCapZ Z Z' γ δ U L s t y' := by
    rw [hrest, g3pl4_W_eq hνr hδ hδ4 hsep]
    rfl
  change ∫⁻ x in g3pl4W γ δ U y, _ ∂_ ≤ _
  calc ∫⁻ x in g3pl4W γ δ U y, s.indicator 1 (Z L y x) *
        t.indicator 1 (Z' L y (g3zPartner γ y x)) ∂qBoundaryMeasure γ y
      ≤ ∫⁻ x in g3pl4W γ δ U y, (s.indicator 1 (Z L y' x) *
          t.indicator 1 (Z' L y' (g3zPartner γ y' x)) +
          (g3pl4EZ Z Z' γ L s t y y').indicator 1 x) ∂qBoundaryMeasure γ y :=
        setLIntegral_mono' hWm fun x hx => g3pl4_integrand_leZ hνr hδ hδ4 hsep hR L hx
    _ = ∫⁻ x in g3pl4W γ δ U y, s.indicator 1 (Z L y' x) *
          t.indicator 1 (Z' L y' (g3zPartner γ y' x)) ∂qBoundaryMeasure γ y +
        ∫⁻ x in g3pl4W γ δ U y, (g3pl4EZ Z Z' γ L s t y y').indicator 1 x ∂qBoundaryMeasure γ y :=
        lintegral_add_right _ (measurable_const.indicator
          (g3pl4_measurableSet_EZ hZm hZm' γ L (measurableSet_lawCyl hs) (measurableSet_lawCyl ht) y y'))
    _ ≤ _ := add_le_add (le_of_eq hmain) hL.le

end PtwAE

theorem g3PlCapLocAE_of_ball {Z Z' : ℝ → FieldSample → ℝ → LawD} {γ : ℝ}
    {Gd Gd' : FieldSample → ℝ → Prop}
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (hB : G3ZqZoomBallLocGZ Z Gd) (hB' : G3ZqZoomBallLocGZ Z' Gd') :
    G3PlCapLocAE Z Z' γ Gd Gd' := by
  intro δ U hδ hδ4 s hs t ht y y' h1 h2 ha hg hsep' ε hε
  obtain ⟨hsep, hR⟩ := hsep'
  have hνr := g3pl4_restrict_eq_of_agree h1 h2 ha
  exact g3pl4_phiCap_le_of_agreeAE (U := U) ha hνr hδ hδ4 hsep hR hZm hZm' hB hB' hs ht hg hε

end G3ZqL
end R18
end QuantumZipper
