/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76FMark
import InteractingSLE.Spec.Sec7.Lemma76FClock

/-!
# Lemma 7.6: G7's retained chart only depends on the two retained prefixes

Packet PROVE-T15-CLOSE1 (2). G7's retained data `Supp7.RetData` (two paths with deterministic cutoffs `u`, `r` and a
good event) defines the retained chart at the second tip pathwise from the two prefixes `η₁([0, u])`, `η₂([0, r])`.
To condition on the retained histories, (R1) works with a second copy of the retained data built from the stopped
capped versions of the flow lines, which is measurable for the retained σ-algebra. This file proves that the two
copies have the same chart wherever both are good and their prefixes agree:

* `retPath_congr`, **`isRetChart_congr`**: G7's chart predicate only reads the prefixes;
* **`RetData.chart_eq_of_agree`**: equal chart events, domains and charts (hence chart fields,
  `RetData.chartField_eq_of_agree`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

namespace Lemma76F

open Supp7 Restart

/-! ### The chart predicate reads only the prefixes -/

section Congr

variable {η₁ η₁' η₂ η₂' : ℝ≥0 → ℂ} {u r : ℝ≥0}

/-- G7's fake first path (the first prefix, back, a real segment, then the second prefix) only reads the two
prefixes. -/
theorem retPath_congr (h₁ : ∀ s ≤ u, η₁' s = η₁ s) (h₂ : ∀ t ≤ r, η₂' t = η₂ t) (s : ℝ≥0)
    (hs : (s : ℝ≥0∞) ≤ (retLen u r : ℝ≥0∞)) : retPath η₁' u η₂' s = retPath η₁ u η₂ s := by
  have hs' : s ≤ retLen u r := ENNReal.coe_le_coe.1 hs
  unfold retPath
  split_ifs with ha hb hc
  · exact h₁ s ha
  · exact h₁ _ (by
      have : u < s := not_le.1 ha
      rw [tsub_le_iff_right]
      calc 2 * u = u + u := two_mul u
        _ ≤ u + s := add_le_add_right this.le u)
  · rw [h₁ 0 zero_le, h₂ 0 zero_le]
  · exact h₂ _ (by
      rw [tsub_le_iff_right]
      calc s ≤ retLen u r := hs'
        _ = r + (2 * u + 1) := by rw [retLen, add_comm])

/-- **G7's chart predicate only reads the two prefixes.** -/
theorem isRetChart_congr (h₁ : ∀ s ≤ u, η₁' s = η₁ s) (h₂ : ∀ t ≤ r, η₂' t = η₂ t) {φ ψ : ℂ → ℂ}
    {lift : ℂ → ℝ} : IsRetChart η₁' u η₂' r φ ψ lift ↔ IsRetChart η₁ u η₂ r φ ψ lift :=
  isFirstContactChart_congr (ζ₁ := (retLen u r : ℝ≥0∞)) (ζ₂ := (r : ℝ≥0∞)) (retPath_congr h₁ h₂)
    (fun t ht => h₂ t (ENNReal.coe_le_coe.1 ht)) le_rfl le_rfl

theorem prefixSet_congr' (h₁ : ∀ s ≤ u, η₁' s = η₁ s) (h₂ : ∀ t ≤ r, η₂' t = η₂ t) :
    prefixSet η₁' u η₂' r = prefixSet η₁ u η₂ r := by
  rw [prefixSet, prefixSet, image_congr fun s hs => h₁ s hs.2, image_congr fun t ht => h₂ t ht.2]

end Congr

/-! ### Two copies of retained data with agreeing prefixes -/

section Agree

variable {Ω : Type*}

/-- **Retained data with agreeing prefixes have the same chart.** If `ω` is good for both copies (same cutoffs) and
their prefixes agree, the chart events, the domains and the charts coincide at `ω`. -/
theorem RetData.chart_eq_of_agree {d : RetData Ω} {G' : Set Ω} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ω : Ω} (hG : ω ∈ d.G)
    (hG' : ω ∈ G') (h₁ : ∀ s ≤ d.u, η₁' ω s = d.η₁ ω s) (h₂ : ∀ t ≤ d.r, η₂' ω t = d.η₂ ω t) :
    (ω ∈ (⟨G', η₁', η₂', d.u, d.r⟩ : RetData Ω).E ↔ ω ∈ d.E) ∧
      (⟨G', η₁', η₂', d.u, d.r⟩ : RetData Ω).D ω = d.D ω ∧
      (⟨G', η₁', η₂', d.u, d.r⟩ : RetData Ω).chart ω = d.chart ω := by
  classical
  set d' : RetData Ω := ⟨G', η₁', η₂', d.u, d.r⟩ with hd'
  have hpre : prefixSet (d'.η₁ ω) d'.u (d'.η₂ ω) d'.r = prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r :=
    prefixSet_congr' h₁ h₂
  have hi₁ : d'.η₁ ω '' Icc 0 d'.u = d.η₁ ω '' Icc 0 d.u := image_congr fun s hs => h₁ s hs.2
  have htip : d'.η₂ ω d'.r = d.η₂ ω d.r := h₂ d.r le_rfl
  have hE₀ : ω ∈ d'.E₀ ↔ ω ∈ d.E₀ := by
    simp only [RetData.E₀, mem_inter_iff, mem_ofPred_eq]
    rw [htip, hi₁]
    exact ⟨fun h => ⟨⟨hG, h.1.2⟩, h.2⟩, fun h => ⟨⟨hG', h.1.2⟩, h.2⟩⟩
  have hKOf : d'.KOf d'.E₀ ω = d.KOf d.E₀ ω := by
    by_cases h : ω ∈ d.E₀
    · rw [RetData.KOf_of_mem h, RetData.KOf_of_mem (hE₀.2 h), hpre]
    · rw [RetData.KOf_of_notMem h, RetData.KOf_of_notMem (fun h' => h (hE₀.1 h'))]
  have hDOf : d'.DOf d'.E₀ ω = d.DOf d.E₀ ω := by
    show H \ fillH (d'.KOf d'.E₀ ω) = H \ fillH (d.KOf d.E₀ ω)
    rw [hKOf]
  have hE : ω ∈ d'.E ↔ ω ∈ d.E := by
    show ω ∈ d'.E₀ ∩ {ω | d'.η₂ ω d'.r ∈ closure (d'.DOf d'.E₀ ω)} ↔
      ω ∈ d.E₀ ∩ {ω | d.η₂ ω d.r ∈ closure (d.DOf d.E₀ ω)}
    simp only [mem_inter_iff, mem_ofPred_eq]
    rw [htip, hDOf, hE₀]
  have hK : d'.K ω = d.K ω := by
    by_cases h : ω ∈ d.E
    · rw [RetData.K_of_mem h, RetData.K_of_mem (hE.2 h), hpre]
    · rw [RetData.K_of_notMem h, RetData.K_of_notMem (fun h' => h (hE.1 h'))]
  have hD : d'.D ω = d.D ω := by
    show H \ fillH (d'.K ω) = H \ fillH (d.K ω)
    rw [hK]
  refine ⟨hE, hD, ?_⟩
  by_cases h : ω ∈ d.E
  · have h' : ω ∈ d'.E := hE.2 h
    have hg : d'.g ω = d.g ω := by
      show ConformalImage.mapOut (fillH (d'.K ω)) = ConformalImage.mapOut (fillH (d.K ω))
      rw [hK]
    have hp : d'.p ω = d.p ω := by
      simp only [RetData.p, h, h', ↓reduceIte]
      exact htip
    have hsh : d'.shift ω = d.shift ω := by
      show limUnder (𝓝[d'.D ω] (d'.p ω)) (d'.g ω) = limUnder (𝓝[d.D ω] (d.p ω)) (d.g ω)
      rw [hD, hp, hg]
    have hfwd : d'.fwd ω = d.fwd ω := by
      funext z
      show d'.g ω z - d'.shift ω = d.g ω z - d.shift ω
      rw [hg, hsh]
    have hlift : d'.lift ω = d.lift ω := by
      funext z
      show (canonDerivLog (fillH (d'.K ω)) z).im = (canonDerivLog (fillH (d.K ω)) z).im
      rw [hK]
    have hpred : (fun ψ => IsRetChart (d'.η₁ ω) d'.u (d'.η₂ ω) d'.r (d'.fwd ω) ψ (d'.lift ω)) =
        fun ψ => IsRetChart (d.η₁ ω) d.u (d.η₂ ω) d.r (d.fwd ω) ψ (d.lift ω) := by
      funext ψ
      rw [hfwd, hlift]
      exact propext (isRetChart_congr h₁ h₂)
    have hinv : d'.inv ω = d.inv ω := by
      unfold RetData.inv
      simp only [hpred]
    rw [RetData.chart_of_mem h, RetData.chart_of_mem h', hfwd, hinv, hlift]
  · rw [RetData.chart_of_notMem h, RetData.chart_of_notMem (fun h' => h (hE.1 h'))]

end Agree

end Lemma76F

end Sec7

end InteractingSLE
