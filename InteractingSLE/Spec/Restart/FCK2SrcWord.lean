/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2SrcClock
import InteractingSLE.Spec.Sec5.Aux22ChartE

/-!
# Incident heights at exterior chart points, including original jumps

The exterior boundary correspondence preserves order. Consequently each
one-sided word height is the corresponding original one-sided height, even
when the physical terminal point is an original jump candidate.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (Hbar)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData

/-- A continuous increasing local coordinate preserves both incident
heights of piecewise constant data. -/
theorem incident_limits_of_local_increasing
    {b f g : ℝ → ℝ} {J : Finset ℝ} {S : Set ℝ} {w : ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hS : IsOpen S) (hw : w ∈ S)
    (hmono : StrictMonoOn g S) (hcont : ContinuousAt g w)
    (hfg : ∀ t ∈ S, f t = b (g t)) :
    leftLim f w = leftLim b (g w) ∧ rightLim f w = rightLim b (g w) := by
  have hnear : ∀ᶠ t in 𝓝 w, t ∈ S := hS.mem_nhds hw
  constructor
  · obtain ⟨lo, hlo, hc⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_leftLim hb (g w)
    have hlow : ∀ᶠ t in 𝓝 w, lo < g t := hcont.eventually (Ioi_mem_nhds hlo)
    have he : ∀ᶠ t in 𝓝[<] w, f t = leftLim b (g w) := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
        hlow.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hl htlt
      rw [hfg t ht]
      exact hc _ ⟨hl, hmono ht hw htlt⟩
    exact (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)).limUnder_eq
  · obtain ⟨hi, hhi, hc⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_rightLim hb (g w)
    have hhigh : ∀ᶠ t in 𝓝 w, g t < hi := hcont.eventually (Iio_mem_nhds hhi)
    have he : ∀ᶠ t in 𝓝[>] w, f t = rightLim b (g w) := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
        hhigh.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hh htgt
      rw [hfg t ht]
      exact hc _ ⟨hmono hw ht htgt, hh⟩
    exact (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)).limUnder_eq

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

/-- A real chart point with preimage outside the retained union lies on an
untouched exterior ray. -/
theorem real_chart_point_exterior_of_notMem_K (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E)
    {z : ℂ} (him : z.im = 0) (hn : d.inv ω z ∉ d.K ω) :
    z.re < d.wordL ω ∨ d.wordR ω < z.re := by
  by_contra hbad
  push Not at hbad
  have hK := hd.inv_mem_K_of_mem_Icc hE hbad.1 hbad.2
  rw [Sec7.SideHeightBox.ofReal_re_of_im him] at hK
  exact hn hK

/-- The real chart inverse is increasing on each untouched exterior ray. -/
theorem strictMonoOn_inv_real_exterior (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    StrictMonoOn (fun w : ℝ => (d.inv ω w).re) (Iio (d.wordL ω)) ∧
      StrictMonoOn (fun w : ℝ => (d.inv ω w).re) (Ioi (d.wordR ω)) := by
  constructor
  · intro v hv w hw hvw
    obtain ⟨hyv, -, hev⟩ := hd.inv_of_lt_wordL hE hv
    obtain ⟨hyw, -, hew⟩ := hd.inv_of_lt_wordL hE hw
    apply (hd.strictMonoOn_bdry_Iio hE).lt_iff_lt hyv hyw |>.1
    rwa [hev, hew]
  · intro v hv w hw hvw
    obtain ⟨hyv, -, hev⟩ := hd.inv_of_wordR_lt hE hv
    obtain ⟨hyw, -, hew⟩ := hd.inv_of_wordR_lt hE hw
    apply (hd.strictMonoOn_bdry_Ioi hE).lt_iff_lt hyv hyw |>.1
    rwa [hev, hew]

/-- At every untouched real chart point, including the images of original
jumps, both incident word heights read the original incident heights. -/
theorem word_incident_limits_of_exterior (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E)
    {b : ℝ → ℝ} {J : Finset ℝ} {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hb₀ : ∀ y ∉ J, c₀.fn y = b y)
    (hL hR : ℝ) {w : ℝ} (hw : w < d.wordL ω ∨ d.wordR ω < w) :
    leftLim (d.word c₀ hL hR ω).fn w = leftLim b (d.inv ω w).re ∧
      rightLim (d.word c₀ hL hR ω).fn w = rightLim b (d.inv ω w).re := by
  obtain ⟨-, -, -, -, -, -, -, hψc, -⟩ := (hd.isFirstContactChart hE).2
  have hm : Continuous fun r : ℝ => (d.inv ω (r : ℂ)).re :=
    Complex.continuous_re.comp (hψc.comp_continuous Complex.continuous_ofReal
      (fun r => by simp only [Hbar, Complex.ofReal_im, Set.mem_ofPred_eq, le_refl]))
  have he : leftLim (d.word c₀ hL hR ω).fn w = leftLim c₀.fn (d.inv ω w).re ∧
      rightLim (d.word c₀ hL hR ω).fn w = rightLim c₀.fn (d.inv ω w).re := by
    rcases hw with hw | hw
    · exact incident_limits_of_local_increasing c₀.isPiecewiseConstantBoundaryData isOpen_Iio hw
        (strictMonoOn_inv_real_exterior hd hE).1 hm.continuousAt
        (fun _ ht => hd.word_fn_of_lt_wordL hE hc₀ hL hR ht)
    · exact incident_limits_of_local_increasing c₀.isPiecewiseConstantBoundaryData isOpen_Ioi hw
        (strictMonoOn_inv_real_exterior hd hE).2 hm.continuousAt
        (fun _ ht => hd.word_fn_of_wordR_lt hE hc₀ hL hR ht)
  simpa only [leftLim_congr hb₀, rightLim_congr hb₀] using he

end InteractingSLE.Restart.FCPlumb
