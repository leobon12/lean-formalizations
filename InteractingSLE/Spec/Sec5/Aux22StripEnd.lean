/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22StripAvoid
import InteractingSLE.Spec.Sec5.Aux22StripWord

/-!
# Aux. lemma 22 in the strip, step 3c: the strip endpoint along one path

Packet PROVE-SEC5-L (specification §4.1, Aux. lemmas 21–22, pp. 109–115). Zhan's strip endpoint theorem
(`Strip.HasStripEndpoint`) says that the strip clock is unbounded on the strip life, that a continuous generating
trace exists on the strip life, and that every such trace converges, along the strip life, to a point `x < −1` (the
chordal image of a point of the upper line). Together with the protection of the real points during the strip life
(lower noncollision, `Zhan.ae_stripLife_noncollision`, and passive points, `ae_real_alive_of_forall_ne`), this file
derives, along one path:

* `isOpen_stripLife`: the strip life is relatively open (continuity of the gap);
* **`exists_stripEnd`**: the strip life is a bounded interval `[0, S)` (a trace converging to a finite point has
  bounded hulls, hence bounded capacity time, `two_mul_le_sq_of_isGeneratingTrace`), the trace generates the chain on
  `[0, s]` for every `s < S`, never visits `ℝ \ {0}` before `S` (`ne_ofReal_of_isGeneratingTrace_lt`), and tends to
  `x < −1` as `s ↑ S`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (IsForwardSol)

namespace InteractingSLE

namespace Sec5

namespace Aux22Strip

open Strip

variable {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The strip life is open**: past every strip-life time there is a later one. -/
theorem exists_gt_isStripLife (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hvc : ContinuousOn v {s | (s : ℝ≥0∞) < ζ}) {s : ℝ≥0} (hs : IsStripLife w v ζ s) :
    ∃ s', s < s' ∧ IsStripLife w v ζ s' := by
  have hopen : IsOpen {r : ℝ≥0 | (r : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hnhds : {r : ℝ≥0 | (r : ℝ≥0∞) < ζ} ∈ 𝓝 s := hopen.mem_nhds hs.1
  have hgap : ContinuousAt (fun r => w r - v r) s :=
    ((hwc.continuousAt hnhds).sub (hvc.continuousAt hnhds))
  have hpos : 0 < w s - v s := sub_pos.2 (hs.2 s le_rfl)
  have hev : ∀ᶠ r : ℝ≥0 in 𝓝 s, (r : ℝ≥0∞) < ζ ∧ 0 < w r - v r :=
    (show ∀ᶠ r : ℝ≥0 in 𝓝 s, (r : ℝ≥0∞) < ζ from hnhds).and (hgap.eventually (lt_mem_nhds hpos))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set s' : ℝ≥0 := s + (ε / 2).toNNReal with hs'
  have hcoe : (((ε / 2).toNNReal : ℝ≥0) : ℝ) = ε / 2 := Real.coe_toNNReal _ (half_pos hε).le
  have hss' : s < s' := lt_add_of_pos_right _ (Real.toNNReal_pos.2 (half_pos hε))
  have hd : ∀ r : ℝ≥0, s ≤ r → r ≤ s' → dist r s < ε := fun r h1 h2 => by
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h1))]
    have : (r : ℝ) ≤ s + ε / 2 := by
      have h3 := NNReal.coe_le_coe.2 h2
      rw [hs', NNReal.coe_add, hcoe] at h3
      exact h3
    linarith
  refine ⟨s', hss', (hball (hd s' hss'.le le_rfl)).1, fun r hr => ?_⟩
  rcases le_total r s with h | h
  · exact hs.2 r h
  · exact sub_pos.1 (hball (hd r h hr)).2

/-- **The strip endpoint along one path.** If the driver and the end mark are continuous before the lifetime, the
path has Zhan's strip endpoint, and every nonzero real point is alive during the strip life, then the strip life is
`[0, S)` for some `S > 0`, a trace generates the chain on `[0, s]` for every `s < S`, never visits `ℝ \ {0}` before
`S`, and converges to a point `x < −1` as `s ↑ S`. -/
theorem exists_stripEnd (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hvc : ContinuousOn v {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hE : HasStripEndpoint w v ζ)
    (halive : ∀ s, IsStripLife w v ζ s → ∀ y : ℝ, y ≠ 0 →
      ∃ u, IsForwardSol (fun r : ℝ => w r.toNNReal) (y : ℂ) s u) :
    ∃ (S : ℝ≥0) (η : ℝ≥0 → ℂ) (x : ℝ), 0 < S ∧ x < -1 ∧ (∀ s, IsStripLife w v ζ s ↔ s < S) ∧
      (∀ s, s < S → IsGeneratingTrace w s η) ∧ (∀ s, s < S → ∀ y : ℝ, y ≠ 0 → η s ≠ y) ∧
      Tendsto η (𝓝[<] S) (𝓝 (x : ℂ)) := by
  obtain ⟨hclock, ⟨η, hη⟩, hconv⟩ := hE
  obtain ⟨x, hx, hxconv⟩ := hconv η hη
  set L : Set ℝ≥0 := {s | IsStripLife w v ζ s} with hL
  have hLne : L.Nonempty := by
    obtain ⟨s, hs, -⟩ := hclock 0
    exact ⟨s, hs⟩
  have hdown : ∀ s ∈ L, ∀ r ≤ s, r ∈ L := fun s hs r hr => IsStripLife.mono hs hr
  have hup : ∀ s ∈ L, ∃ s' ∈ L, s < s' := fun s hs => by
    obtain ⟨s', h1, h2⟩ := exists_gt_isStripLife hwc hvc hs
    exact ⟨s', h2, h1⟩
  -- the strip life is bounded: a trace converging to `x` is bounded, so its capacity time is bounded
  have hbdd : BddAbove L := by
    obtain ⟨s₀, hs₀L, hs₀⟩ := hxconv 1 one_pos
    have hcpt : IsCompact (η '' Icc 0 s₀) :=
      isCompact_Icc.image_of_continuousOn ((hη s₀ hs₀L).2.1.mono fun r hr =>
        show (r : ℝ≥0∞) ≤ s₀ from ENNReal.coe_le_coe.2 hr.2)
    obtain ⟨B₀, hB₀⟩ := hcpt.isBounded.exists_norm_le
    set B : ℝ := max B₀ (|x| + 1) with hB
    have hnorm : ∀ s ∈ L, ∀ r ≤ s, ‖η r‖ ≤ B := by
      intro s hs r hr
      rcases le_total r s₀ with h | h
      · exact (hB₀ _ ⟨r, ⟨zero_le, h⟩, rfl⟩).trans (le_max_left _ _)
      · have h1 := hs₀ r h (hdown s hs r hr)
        have h2 : ‖η r‖ ≤ ‖η r - x‖ + ‖(x : ℂ)‖ := by
          have := norm_add_le (η r - x) x
          rwa [sub_add_cancel] at this
        rw [Complex.norm_real, Real.norm_eq_abs] at h2
        exact (by linarith : ‖η r‖ ≤ |x| + 1).trans (le_max_right _ _)
    refine ⟨(B ^ 2 / 2).toNNReal, fun s hs => ?_⟩
    obtain ⟨s', hs'L, hss'⟩ := hup s hs
    have hcap := two_mul_le_sq_of_isGeneratingTrace (hwc.mono fun r (hr : (r : ℝ≥0∞) < s') =>
      show (r : ℝ≥0∞) < ζ from hr.trans hs'L.1) hw0 (hη s' hs'L) (ENNReal.coe_lt_coe.2 hss')
      (hnorm s hs)
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
    linarith
  set S : ℝ≥0 := sSup L with hS
  have hLS : ∀ s, s ∈ L ↔ s < S := by
    intro s
    constructor
    · intro hs
      obtain ⟨s', hs'L, hss'⟩ := hup s hs
      exact lt_of_lt_of_le hss' (le_csSup hbdd hs'L)
    · intro hs
      obtain ⟨s', hs'L, hss'⟩ := (lt_csSup_iff hbdd hLne).1 hs
      exact hdown s' hs'L s hss'.le
  have hS0 : 0 < S := by
    obtain ⟨s, hs⟩ := hLne
    exact (hLS 0).1 (hdown s hs 0 zero_le)
  refine ⟨S, η, x, hS0, hx, hLS, fun s hs => hη s ((hLS s).2 hs), fun s hs y hy => ?_, ?_⟩
  · obtain ⟨s', hs'L, hss'⟩ := hup s ((hLS s).2 hs)
    exact ne_ofReal_of_isGeneratingTrace_lt (hwc.mono fun r (hr : (r : ℝ≥0∞) < s') =>
      show (r : ℝ≥0∞) < ζ from hr.trans hs'L.1) hw0 (hη s' hs'L) (isClosed_singleton (x := y))
      (by simpa using hy.symm) (ENNReal.coe_lt_coe.2 hss')
      (fun z hz => by rw [mem_singleton_iff.1 hz]; exact halive s ((hLS s).2 hs) y hy) s le_rfl y rfl
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨s₀, hs₀L, hs₀⟩ := hxconv ε hε
    have hs₀S : s₀ < S := (hLS s₀).1 hs₀L
    refine ⟨(S : ℝ) - s₀, sub_pos.2 (NNReal.coe_lt_coe.2 hs₀S), fun s hs hd => ?_⟩
    have hsS : s < S := hs
    have hs₀s : s₀ ≤ s := by
      rw [NNReal.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 (NNReal.coe_lt_coe.2 hsS))] at hd
      exact NNReal.coe_le_coe.1 (by linarith)
    rw [dist_eq_norm]
    exact hs₀ s hs₀s ((hLS s).2 hsS)

end Aux22Strip

end Sec5

end InteractingSLE
