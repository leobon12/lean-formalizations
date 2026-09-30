import QuantumZipper.Proofs.Section5.Prop16LitMain
import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: joint measurability of the inverse charts (COORD-CHANGE, D98)

For a literal chart family (`Prop16Lit.LitFamily`), the map `(x, u) ↦ (x, ψ_x u)` on the Borel
set `{x ∈ (a,b), u ∈ B(0, r₀ x) ∩ ℍ}` is measurable and injective, hence a measurable embedding
(Lusin–Souslin, mathlib `Measurable.measurableEmbedding`; Kechris, *Classical Descriptive Set
Theory*, Thm 15.1). Consequently the inverse charts `(x, w) ↦ ψ_x⁻¹ w` have a jointly measurable
version `Prop16Lit.chartInv` (`measurable_chartInv`, `chartInv_apply`). Input for testing the chart
identity against pulled-back test functions under the Palm transfer. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Metric

namespace QuantumZipper
namespace Prop16Lit

variable {D : Set ℂ} {a b : ℝ} {ψ : ℝ → ℂ → ℂ} {r₀ : ℝ → ℝ}

/-- The domain of the chart family. -/
def chartDom (a b : ℝ) (r₀ : ℝ → ℝ) : Set (ℝ × ℂ) :=
  {q | q.1 ∈ Ioo a b ∧ q.2 ∈ ball 0 (r₀ q.1) ∩ H}

theorem measurableSet_chartDom {r₀ : ℝ → ℝ} (hr : Measurable r₀) (a b : ℝ) :
    MeasurableSet (chartDom a b r₀) := by
  have e : chartDom a b r₀ = {q : ℝ × ℂ | q.1 ∈ Ioo a b} ∩
      ({q : ℝ × ℂ | ‖q.2‖ < r₀ q.1} ∩ {q : ℝ × ℂ | 0 < q.2.im}) := by
    ext q
    simp only [chartDom, mem_inter_iff, mem_ball, dist_zero_right]
    rfl
  rw [e]
  refine (measurableSet_Ioo.preimage measurable_fst).inter ?_
  refine (measurableSet_lt (f := fun q : ℝ × ℂ => ‖q.2‖) (g := fun q => r₀ q.1)
    (by fun_prop) (hr.comp measurable_fst)).inter ?_
  exact measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_snd)

/-- The chart pair map. -/
def chartPair (ψ : ℝ → ℂ → ℂ) (a b : ℝ) (r₀ : ℝ → ℝ) : chartDom a b r₀ → ℝ × ℂ :=
  fun q => (q.1.1, ψ q.1.1 q.1.2)

theorem measurable_chartPair (hfam : LitFamily D a b ψ r₀) :
    Measurable (chartPair ψ a b r₀) :=
  (measurable_fst.comp measurable_subtype_coe).prodMk (hfam.1.comp measurable_subtype_coe)

theorem injective_chartPair (hfam : LitFamily D a b ψ r₀) :
    Function.Injective (chartPair ψ a b r₀) := by
  rintro ⟨⟨x, u⟩, hx, hu⟩ ⟨⟨x', u'⟩, hx', hu'⟩ h
  simp only [chartPair, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  have := (hfam.2.2 x hx).2.1 hu.2 hu'.2 h2
  subst this
  rfl

theorem measurableEmbedding_chartPair (hfam : LitFamily D a b ψ r₀) :
    MeasurableEmbedding (chartPair ψ a b r₀) := by
  have := (measurableSet_chartDom hfam.2.1 a b).standardBorel
  exact (measurable_chartPair hfam).measurableEmbedding (injective_chartPair hfam)

open Classical in
/-- **The inverse charts**, jointly measurable (junk `0` off the chart images). -/
def chartInv (ψ : ℝ → ℂ → ℂ) (a b : ℝ) (r₀ : ℝ → ℝ) (x : ℝ) (w : ℂ) : ℂ :=
  if h : (x, w) ∈ range (chartPair ψ a b r₀) then
    (rangeSplitting (chartPair ψ a b r₀) ⟨(x, w), h⟩).1.2 else 0

open Classical in
theorem measurable_chartInv (hfam : LitFamily D a b ψ r₀) :
    Measurable fun q : ℝ × ℂ => chartInv ψ a b r₀ q.1 q.2 := by
  have hE := measurableEmbedding_chartPair hfam
  have hR : MeasurableSet (range (chartPair ψ a b r₀)) := hE.measurableSet_range
  unfold chartInv
  exact Measurable.dite (s := range (chartPair ψ a b r₀))
    (f := fun q => (rangeSplitting (chartPair ψ a b r₀) q).1.2)
    (measurable_snd.comp (measurable_subtype_coe.comp hE.measurable_rangeSplitting))
    measurable_const hR

theorem chartInv_apply (hfam : LitFamily D a b ψ r₀) {x : ℝ} (hx : x ∈ Ioo a b) {u : ℂ}
    (hu : u ∈ ball 0 (r₀ x) ∩ H) : chartInv ψ a b r₀ x (ψ x u) = u := by
  have hmem : (x, ψ x u) ∈ range (chartPair ψ a b r₀) := ⟨⟨(x, u), hx, hu⟩, rfl⟩
  unfold chartInv
  rw [dif_pos hmem]
  have h := apply_rangeSplitting (chartPair ψ a b r₀) ⟨(x, ψ x u), hmem⟩
  have h' : rangeSplitting (chartPair ψ a b r₀) ⟨(x, ψ x u), hmem⟩ = ⟨(x, u), hx, hu⟩ :=
    injective_chartPair hfam (h.trans rfl)
  rw [h']

end Prop16Lit
end QuantumZipper
