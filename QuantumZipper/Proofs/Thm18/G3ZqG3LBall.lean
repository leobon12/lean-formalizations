import QuantumZipper.Proofs.Thm18.G3ZqG3RSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3 above G2 with abstract zooms: one pathwise ball-locality property of the zoom

`G3ZqZoomBallLocZ Z γ` (the abstract-zoom analogue of `zoomLaw_mem_lawCyl_iff` combined with
the growth of the area proxy, i.e. of `g3pl4_eventually_zoom_iff`, `G3Pl4Loc.lean`): if two
fields agree on the dyadic (folded) circles inside an open set `W` containing the point `x`, the
second is good at `x` (translated field `IsLQGGood`) with positive area on every half-ball about
`x`, then for all large levels the cylinder events of the two zooms at `x` coincide.
`g3ZqZoomBallLocZ_zoomLaw` proves it for the plain zoom.

From it (and `hZm`), `G3PlCapLocZ` follows by the generalized copy (D92) of the pathwise
comparison of `G3Pl4Ptw.lean` (`g3pl4_integrand_le`, `g3pl4_tendsto_E`,
`g3pl4_phiCap_le_of_agree`); zoom-free lemmas (`g3pl4W`, `g3pl4_W_eq`, `g3pl4_partner_eq`, …) are
reused.

Sheffield, arXiv:1012.4797, proof of Thm. 1.8, pp. 71–72 and Remark 5.7. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology symmDiff

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

/-- **Pathwise ball locality of a zoom at large level.** -/
def G3ZqZoomBallLocZ (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) : Prop :=
  ∀ s ∈ lawCyl, ∀ (y y' : FieldSample) (x : ℝ) (W : Set ℂ), IsOpen W → FcAgree W y y' →
    (x : ℂ) ∈ W → IsLQGGood γ (translate y' (x : ℂ)) →
    (∀ q : ℝ, 0 < q → 0 < areaProxy γ (translate y' (x : ℂ)) q) →
    ∀ᶠ C in (atTop : Filter ℝ), (Z C y x ∈ s ↔ Z C y' x ∈ s)

/-- The plain zoom is ball-local (`g3pl4_eventually_zoom_iff`). -/
theorem g3ZqZoomBallLocZ_zoomLaw {γ : ℝ} (hγ : 0 < γ) : G3ZqZoomBallLocZ (zoomLaw γ) γ := by
  intro s hs y y' x W hWo hag hxW hgood hpos
  obtain ⟨R, hR, H⟩ := g3pl4_eventually_zoom_iff hs
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWo _ hxW
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  obtain ⟨q₀, hq₀, hq₀lt⟩ := exists_rat_btwn (div_pos hr hR0)
  have hqR : (q₀ : ℝ) * R < r := by rwa [lt_div_iff₀ hR0] at hq₀lt
  refine H γ hγ y y' x W hWo hag q₀ hq₀ (fun z hz => ?_) hgood (hpos _ hq₀)
  apply hrW
  simp only [mem_ball, dist_eq_norm, add_sub_cancel_right]
  have : ‖z‖ ≤ q₀ * R := by simpa [dist_zero_right] using hz.1
  linarith

section PtwZ

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}
variable {γ δ U : ℝ} {s t : Set LawD} {y y' : FieldSample}

/-- The disagreement set of the two zoom events at level `L` (abstract zooms). -/
def g3pl4EZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ L : ℝ) (s t : Set LawD)
    (y y' : FieldSample) : Set ℝ :=
  (((fun x : ℝ => Z L y x) ⁻¹' s) ∆ ((fun x : ℝ => Z L y' x) ⁻¹' s)) ∪
    (((fun x : ℝ => Z' L y (g3zPartner γ y x)) ⁻¹' t) ∆
      ((fun x : ℝ => Z' L y' (g3zPartner γ y x)) ⁻¹' t))

theorem g3pl4_measurableSet_EZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (γ L : ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (y y' : FieldSample) : MeasurableSet (g3pl4EZ Z Z' γ L s t y y') := by
  have h1 : Measurable fun x : ℝ => Z L y x := measurable_zoomZ_pt hZm L y measurable_id
  have h2 : Measurable fun x : ℝ => Z L y' x := measurable_zoomZ_pt hZm L y' measurable_id
  have h3 := measurable_zoomZ_pt hZm' L y (g3pl4_measurable_partner γ y)
  have h4 := measurable_zoomZ_pt hZm' L y' (g3pl4_measurable_partner γ y)
  exact ((h1 hs).symmDiff (h2 hs)).union ((h3 ht).symmDiff (h4 ht))

variable (hag : FcAgree (ball (0 : ℂ) 1) y y')
  (hνr : (qBoundaryMeasure γ y).restrict (Icc (-(1 / 2)) (1 / 2)) =
    (qBoundaryMeasure γ y').restrict (Icc (-(1 / 2)) (1 / 2)))
  (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
  (hsep : qBoundaryMeasure γ y (Icc (-δ) 0) < qBoundaryMeasure γ y (Icc (-(1 / 2)) 0))
  (hR : qBoundaryMeasure γ y (Icc (-δ) 0) ≤ qBoundaryMeasure γ y (Icc 0 (1 / 4)))

include hνr hδ hδ4 hsep hR in
/-- The pointwise comparison on the window. -/
theorem g3pl4_integrand_leZ (L : ℝ) {x : ℝ} (hx : x ∈ g3pl4W γ δ U y) :
    s.indicator (1 : LawD → ℝ≥0∞) (Z L y x) *
        t.indicator 1 (Z' L y (g3zPartner γ y x)) ≤
      s.indicator 1 (Z L y' x) * t.indicator 1 (Z' L y' (g3zPartner γ y' x)) +
        (g3pl4EZ Z Z' γ L s t y y').indicator 1 x := by
  obtain ⟨hp, -, -⟩ := g3pl4_partner_eq hνr hδ hδ4 hsep hR hx
  by_cases hE : x ∈ g3pl4EZ Z Z' γ L s t y y'
  · rw [indicator_of_mem hE]
    exact (g3pl4_ind_mul_le_one _ _ _ _).trans (le_add_left le_rfl)
  · rw [indicator_of_notMem hE, add_zero, ← hp]
    simp only [g3pl4EZ, mem_union, mem_symmDiff, mem_preimage, not_or, not_and, not_not] at hE
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hE
    have e1 : (Z L y x ∈ s ↔ Z L y' x ∈ s) := ⟨h1, h2⟩
    have e2 : (Z' L y (g3zPartner γ y x) ∈ t ↔
        Z' L y' (g3zPartner γ y x) ∈ t) := ⟨h3, h4⟩
    have i1 : s.indicator (1 : LawD → ℝ≥0∞) (Z L y x) =
        s.indicator 1 (Z L y' x) := by
      by_cases ha : Z L y x ∈ s
      · rw [indicator_of_mem ha, indicator_of_mem (e1.1 ha)]; rfl
      · rw [indicator_of_notMem ha, indicator_of_notMem (mt e1.2 ha)]
    have i2 : t.indicator (1 : LawD → ℝ≥0∞) (Z' L y (g3zPartner γ y x)) =
        t.indicator 1 (Z' L y' (g3zPartner γ y x)) := by
      by_cases ha : Z' L y (g3zPartner γ y x) ∈ t
      · rw [indicator_of_mem ha, indicator_of_mem (e2.1 ha)]; rfl
      · rw [indicator_of_notMem ha, indicator_of_notMem (mt e2.2 ha)]
    rw [i1, i2]

end PtwZ

end R18
end QuantumZipper
