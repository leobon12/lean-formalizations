/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketTraversal
import InteractingSLE.Spec.Sec7.Lemma71CMeas

/-!
# The canonical driver of a random driven curve is adapted to its filled prefixes

Packet PROVE-STRIPSYS10 (proof of Lemma 7.25, p. 414: the relative driver of the erased traversal is a process to
which Aux. lemma 122's martingale characterization is applied, so it must be adapted).

PROVE-LEMMA71C proved, for random *simple* mapped segments, that the canonical driver `segDriver` at a capacity time is
measurable for every σ-algebra in which the filled prefixes up to that capacity time are measurable for the dyadic
hitting events (`Lemma71C.measurable_indicator_segDrv`), hence adapted before the terminal capacity time
(`Lemma71C.adaptedBefore_segDriver`). Simplicity enters there only through the driver formula, which
`PocketTraversal.lean` proves for every curve with local drivers. This file repeats the two statements for random
driven curves (in particular the relative curve of the erased pocket traversal), with the curve required to be driven
only on the event under consideration.

## Main results

* `measurable_indicator_segDrv_of_isDrivenCurve`: measurability at a fixed capacity time on an event;
* **`adaptedBefore_segDriver_of_isDrivenCurve`**: adaptedness before the terminal capacity time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketTraversal

open Lemma71C Restart

variable {Ω : Type*}

/-! ### Measurability at a fixed capacity time -/

section Fixed

variable [MeasurableSpace Ω] {γ : Ω → ℝ → ℂ}

omit [MeasurableSpace Ω] in
theorem isCompact_prefixOn_of_isDrivenCurve {E : Set Ω} (hγ : ∀ ω ∈ E, IsDrivenCurve (γ ω)) (r : ℝ) (ω : Ω) :
    IsCompact (prefixOn γ E r ω) := by
  classical
  unfold prefixOn
  split_ifs with hω
  · exact isCompact_Icc.image_of_continuousOn ((hγ ω hω).continuousOn.mono fun u hu => hu.1)
  · exact isCompact_empty

omit [MeasurableSpace Ω] in
theorem isPreconnected_prefixOn_of_isDrivenCurve {E : Set Ω} (hγ : ∀ ω ∈ E, IsDrivenCurve (γ ω)) (r : ℝ)
    (ω : Ω) : IsPreconnected (prefixOn γ E r ω ∪ lowerHalf) := by
  classical
  unfold prefixOn
  split_ifs with hω
  · refine (isPreconnected_Icc.image _ ((hγ ω hω).continuousOn.mono fun u hu => hu.1)).union 0
      ⟨0, ⟨le_rfl, capInv_nonneg _ _⟩, (hγ ω hω).zero⟩ zero_mem_lowerHalf isPreconnected_lowerHalf
  · rw [empty_union]
    exact isPreconnected_lowerHalf

omit [MeasurableSpace Ω] in
/-- On `E`, the mapping-out function at capacity time `r` is that of `prefixOn`. -/
theorem segG_eq_prefixOn_of_isDrivenCurve {E : Set Ω} {ω : Ω} (hω : ω ∈ E) (hγω : IsDrivenCurve (γ ω)) (r : ℝ)
    (z : ℂ) : segG (γ ω) r z = ConformalImage.mapOut (fillH (prefixOn γ E r ω)) z := by
  classical
  have e : capInv (γ ω) r = capInv (γ ω) (max r 0) := by
    rcases le_or_gt 0 r with hr | hr
    · rw [max_eq_left hr]
    · rw [max_eq_right hr.le, hγω.capInv_of_nonpos hr.le, hγω.capInv_of_nonpos le_rfl]
  simp only [segG, prefixOn, hω, ↓reduceIte, e]

/-- **The driver at a fixed capacity time is measurable** on an event `E` below the terminal capacity time, on which
the curve is driven, as soon as the prefixes up to that capacity time are measurable for the dyadic hitting events on
`E` (`Lemma71C.measurable_indicator_segDrv` for driven curves). -/
theorem measurable_indicator_segDrv_of_isDrivenCurve {s : ℝ} (hs0 : 0 ≤ s) {E : Set Ω}
    (hγ : ∀ ω ∈ E, IsDrivenCurve (γ ω)) (hE : MeasurableSet E)
    (hEs : ∀ ω ∈ E, ENNReal.ofReal s < capLife (γ ω))
    (hpre : ∀ r, 0 ≤ r → r ≤ s → ∀ (n : ℕ) (k : ℤ × ℤ),
      MeasurableSet (E ∩ {ω | (dyadicSquare n k ∩ γ ω '' Icc 0 (capInv (γ ω) r)).Nonempty})) :
    Measurable (E.indicator fun ω => segDrv (γ ω) s) := by
  classical
  have hdy : ∀ r ≤ s, IsDyadicHitMeasurable (prefixOn γ E r) := by
    intro r hr n k
    have heq : {ω | (dyadicSquare n k ∩ prefixOn γ E r ω).Nonempty} =
        E ∩ {ω | (dyadicSquare n k ∩ γ ω '' Icc 0 (capInv (γ ω) (max r 0))).Nonempty} := by
      ext ω
      by_cases hω : ω ∈ E
      · simp [prefixOn, hω]
      · simp [prefixOn, hω]
    rw [heq]
    exact hpre _ (le_max_right _ _) (max_le hr hs0) n k
  set G : ℝ → ℂ → Ω → ℂ := fun r z => {ω | z ∈ H \ fillH (prefixOn γ E r ω)}.indicator
    fun ω => ConformalImage.mapOut (fillH (prefixOn γ E r ω)) z with hGdef
  have hGm : ∀ r ≤ s, ∀ z, Measurable (G r z) := fun r hr z =>
    measurable_indicator_mapOut (hdy r hr) (isCompact_prefixOn_of_isDrivenCurve hγ r)
      (isPreconnected_prefixOn_of_isDrivenCurve hγ r) z
  set X : ℕ → ℕ → Ω → ℝ := fun N k ω => (G s (zPt N) ω - 2 / (((k : ℂ) + 1) *
    (G s (zPt N) ω - G (s - 1 / ((k : ℝ) + 1)) (zPt N) ω))).re with hXdef
  have hXm : ∀ N k, Measurable (X N k) := by
    intro N k
    have h1 := hGm s le_rfl (zPt N)
    have h2 := hGm (s - 1 / ((k : ℝ) + 1)) (by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith) (zPt N)
    exact Complex.measurable_re.comp (h1.sub (measurable_const.div (measurable_const.mul (h1.sub h2))))
  set Y : ℕ → Ω → ℝ := fun N ω => limUnder atTop fun k => X N k ω with hYdef
  have hYm : ∀ N, Measurable (Y N) := fun N =>
    (StronglyMeasurable.limUnder fun k => (hXm N k).stronglyMeasurable).measurable
  refine measurable_of_tendsto_metrizable (f := fun N => E.indicator (Y N)) (fun N => (hYm N).indicator hE) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ E
  · simp only [indicator_of_mem hω]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(hγ ω hω).eventually_tendsto_segDrv hs0 (hEs ω hω)] with N hN
    obtain ⟨hout, hlim⟩ := hN
    have hXN : ∀ k, X N k ω = segQuot (γ ω) s (zPt N) k := by
      intro k
      have hG : ∀ r ≤ s, G r (zPt N) ω = segG (γ ω) r (zPt N) := by
        intro r hr
        have hmem : ω ∈ {ω | zPt N ∈ H \ fillH (prefixOn γ E r ω)} := by
          refine ⟨zPt_mem_H N, ?_⟩
          have e : prefixOn γ E r ω = γ ω '' Icc 0 (capInv (γ ω) r) := by
            rcases le_or_gt 0 r with hr0 | hr0
            · simp only [prefixOn, hω, ↓reduceIte, max_eq_left hr0]
            · simp only [prefixOn, hω, ↓reduceIte, max_eq_right hr0.le,
                (hγ ω hω).capInv_of_nonpos hr0.le, (hγ ω hω).capInv_of_nonpos le_rfl]
          rw [e]
          exact hout r hr
        rw [hGdef]
        dsimp only
        rw [indicator_of_mem hmem, segG_eq_prefixOn_of_isDrivenCurve hω (hγ ω hω)]
      have hk : s - 1 / ((k : ℝ) + 1) ≤ s := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      simp only [hXdef, segQuot, hG s le_rfl, hG _ hk]
    have : Y N ω = segDrv (γ ω) s := by
      simp only [hYdef, hXN]
      exact hlim.limUnder_eq
    exact this.symm
  · simp only [indicator_of_notMem hω]
    exact tendsto_const_nhds

end Fixed

/-! ### Adaptedness before the terminal capacity time -/

section Adapted

variable {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {γ : Ω → ℝ → ℂ}

/-- **The canonical driver of a random driven curve is adapted before its terminal capacity time** to every
filtration in which its filled prefixes are adapted at capacity times (`Lemma71C.adaptedBefore_segDriver` for driven
curves). -/
theorem adaptedBefore_segDriver_of_isDrivenCurve (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hpre : IsPrefixAdapted 𝓖 γ) :
    AdaptedBefore 𝓖 (fun ω => capLife (γ ω)) (fun s ω => segDriver (γ ω) s) := by
  intro t A hA
  set E := {ω | (t : ℝ≥0∞) < capLife (γ ω)} with hEdef
  have hE : MeasurableSet[𝓖 t] E := measurableSet_lt_capLife hpre (fun ω => (hγ ω).zero) t
  have hEs : ∀ ω ∈ E, ENNReal.ofReal (t : ℝ) < capLife (γ ω) := fun ω hω => by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hω
  have hpre' : ∀ r : ℝ, 0 ≤ r → r ≤ t → ∀ (n : ℕ) (k : ℤ × ℤ), MeasurableSet[𝓖 t]
      (E ∩ {ω | (dyadicSquare n k ∩ γ ω '' Icc 0 (capInv (γ ω) r)).Nonempty}) := by
    intro r hr0 hrt n k
    have hrt' : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hrt
    have h1 := 𝓖.mono hrt' _ (hpre r.toNNReal n k)
    have heq : E ∩ {ω | (dyadicSquare n k ∩ γ ω '' Icc 0 (capInv (γ ω) r)).Nonempty} =
        E ∩ {ω | ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) ∧
          (dyadicSquare n k ∩ γ ω '' Icc 0 (capInv (γ ω) (r.toNNReal : ℝ))).Nonempty} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, Real.coe_toNNReal _ hr0]
      constructor
      · rintro ⟨hω, h⟩
        exact ⟨hω, lt_of_le_of_lt (by exact_mod_cast hrt') hω, h⟩
      · rintro ⟨hω, -, h⟩
        exact ⟨hω, h⟩
    rw [heq]
    exact hE.inter h1
  have hm := @measurable_indicator_segDrv_of_isDrivenCurve Ω (𝓖 t) γ (t : ℝ) t.coe_nonneg E
    (fun ω _ => hγ ω) hE hEs hpre'
  have heq : {ω | (t : ℝ≥0∞) < capLife (γ ω) ∧ segDriver (γ ω) t ∈ A} =
      E ∩ (E.indicator fun ω => segDrv (γ ω) t) ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, segDriver]
    constructor
    · rintro ⟨hω, h⟩
      exact ⟨hω, by rwa [indicator_of_mem (show ω ∈ E from hω)]⟩
    · rintro ⟨hω, h⟩
      exact ⟨hω, by rwa [indicator_of_mem hω] at h⟩
  rw [heq]
  exact hE.inter (hm hA)

end Adapted

end InteractingSLE.Sec7.PocketTraversal
