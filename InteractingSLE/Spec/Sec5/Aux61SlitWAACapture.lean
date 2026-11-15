/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWAAWindows
import InteractingSLE.Spec.Sec5.Aux61SlitWAAFinite
import InteractingSLE.Spec.Sec5.Aux61GR1FBuffer

/-! # Countable capture with a finite physical inverse buffer

Pole avoidance on the chosen compact buffer is proved from the completed
physical access, rather than assumed. The countable candidate family is
unchanged; the capturing index is still a pointwise existential choice.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAA
open Aux61FibData Aux61GInst Aux61GNext Aux61GWord

/-- A finite access with a nonzero real endpoint has a countable capturing
window with an arbitrarily small seed gap and a bounded physical inverse
image. Pole avoidance on its compact outer buffer is a conclusion. -/
theorem exists_countable_finite_capture {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E)
    (hpos : 0 < T x) (hfin : T x < ⊤)
    (hF : ContinuousOn (boundedInverse (c x)) Hbar)
    {y ε : ℝ} (hy : y ≠ 0) (hε : 0 < ε)
    (hend : Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 (y : ℂ)))
    {O : Set ℝ} (hO : IsOpen O) (hO0 : 0 ∈ O) (hOy : y ∈ O) :
    ∃ i : SeedWindowIndex,
      0 < ((i : WindowIndex).2.2 : ℝ) ∧ ((i : WindowIndex).2.2 : ℝ) < ε ∧
      IsOpen (bufferedWindow i) ∧ (0 : ℂ) ∈ bufferedWindow i ∧
      IsCompact (closure (outerBuffer i)) ∧
      (∀ z ∈ closure (outerBuffer i) ∩ Hbar, boundedInverse (c x) z ≠ 1) ∧
      Bornology.IsBounded ((c x).2.1 '' (bufferedWindow i ∩ H)) ∧
      (∀ z ∈ closure (outerBuffer i), z.im = 0 → z.re ∈ O) ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < T x → inPath E c ρ T x u ∈ bufferedWindow i) ∧
      (y : ℂ) ∉ bufferedWindow i ∧
      Aux61FibData.exitTime E c ρ T (bufferedWindow i) x = T x := by
  obtain ⟨γ, hγc, hγeq, hγ0, hγend, hγH⟩ :=
    exists_continuous_access_completion hs hx hpos hfin hend
  have hfree := completed_access_avoids_pole hs hx hpos hfin hF hend hγeq hγ0 hγend
  have hγA : γ '' Iic (T x).toNNReal ⊆ poleFreeRegion (boundedInverse (c x)) := by
    rintro _ ⟨u, hu, rfl⟩ hbad
    exact hfree u hu hbad.2
  obtain ⟨i, hi0, hiε, hVo, hV0, -, hBc, hBA, hBr, hin, hout⟩ :=
    exists_bufferedWindow_in_open hγc hγ0 hγH hγend hy hε hO hO0 hOy
      (isOpen_poleFreeRegion hF) hγA
  have hfinite : ∀ z ∈ closure (outerBuffer i) ∩ Hbar, boundedInverse (c x) z ≠ 1 := by
    intro z hz he
    exact hBA hz.1 ⟨hz.2, he⟩
  have hsub : bufferedWindow i ⊆ outerBuffer i :=
    fun _ hz => i.property.2.2.1 (subset_closure hz.1)
  have hbounded := Aux61GR1F.isBounded_inverse_window (hs.conf x hx) hsub hBc hF hfinite
  have hbefore : ∀ u : ℝ≥0, (u : ℝ≥0∞) < T x → inPath E c ρ T x u ∈ bufferedWindow i := by
    intro u hu
    have hue : u < (T x).toNNReal := by
      rw [← ENNReal.coe_toNNReal hfin.ne] at hu
      exact ENNReal.coe_lt_coe.1 hu
    rw [← hγeq hue]
    exact hin u hue
  exact ⟨i, hi0, hiε, hVo, hV0, hBc, hfinite, hbounded, hBr, hbefore, hout,
    Aux61GCont.exitTime_eq_of_before_mem hs hVo hx hbefore⟩

end InteractingSLE.Sec5.Aux61SlitWAA
