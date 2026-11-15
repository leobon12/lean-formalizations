/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aGreenBoundary
import InteractingSLE.Spec.Sec6.CircleAverageGreen

/-!
# The regular residual Green kernel is nonnegative and harmonic

Packet PROVE-G7A-MEANIDENT. The active part reuses the landed conformal-radius
kernel `Sec6.greenDiff`; source points swallowed by the hull contribute the
original half-plane Green kernel. The diagonal uses the regular extension.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap greenH)
open QuantumZipper.CA (cayley cayleyInv)
open scoped ComplexConjugate

namespace InteractingSLE.Restart.FlowLocalityGen

/-- The disk chart used by the landed regular Green-difference kernel. -/
def activeDiskChart (w : ℝ → ℝ) (t : ℝ) : ℂ → ℂ := cayley ∘ fwdMap w t

open Classical in
/-- The regular extension of G_H - G_D, including source points outside D. -/
def residualGreenKernel (w : ℝ → ℝ) (t : ℝ) (a z : ℂ) : ℝ :=
  if a ∈ H then
    if a ∈ H \ fwdHull w t then Sec6.greenDiff (activeDiskChart w t) z a else greenH z a
  else 0

/-- The active disk chart is holomorphic, injective and maps the active domain into the disk. -/
theorem activeDiskChart_facts {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableOn ℂ (activeDiskChart w t) (H \ fwdHull w t) ∧
      InjOn (activeDiskChart w t) (H \ fwdHull w t) ∧
      MapsTo (activeDiskChart w t) (H \ fwdHull w t) (ball 0 1) := by
  have hm := QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht
  exact ⟨QuantumZipper.CA.differentiableOn_cayley_Hbar.comp
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw ht)
      (fun _ hz => le_of_lt (show 0 < (fwdMap w t _).im from hm hz)),
    QuantumZipper.CA.bijOn_cayley_H.injOn.comp (QuantumZipper.FwdHolo.injOn_fwdMap hw ht) hm,
    QuantumZipper.CA.bijOn_cayley_H.mapsTo.comp hm⟩

/-- Off the diagonal, the regular kernel is the difference of the two Green kernels. -/
theorem residualGreenKernel_eq {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t)
    {z a : ℂ} (hz : z ∈ H \ fwdHull w t) (ha : a ∈ H) (hza : z ≠ a) :
    residualGreenKernel w t a z = greenH z a -
      (H \ fwdHull w t).indicator (fun a => greenH (fwdMap w t z) (fwdMap w t a)) a := by
  classical
  rw [residualGreenKernel, ite_eq_left ha]
  by_cases haD : a ∈ H \ fwdHull w t
  · rw [ite_eq_left haD, indicator_of_mem haD]
    obtain ⟨_, hi, hm⟩ := activeDiskChart_facts hw ht
    have he := Sec6.greenH_sub_greenH_cayleyInv_eq_greenDiff hi hm hz haD hza
    have hcz : cayleyInv (activeDiskChart w t z) = fwdMap w t z :=
      QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg
        (le_of_lt (show 0 < (fwdMap w t z).im from QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht hz)))
    have hca : cayleyInv (activeDiskChart w t a) = fwdMap w t a :=
      QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg
        (le_of_lt (show 0 < (fwdMap w t a).im from QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht haD)))
    rw [hcz, hca] at he
    exact he.symm
  · rw [ite_eq_right haD, indicator_of_notMem haD, sub_zero]

/-- Every section of the residual kernel is harmonic in the active variable. -/
theorem harmonicOnNhd_residualGreenKernel {w : ℝ → ℝ} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) (a : ℂ) :
    InnerProductSpace.HarmonicOnNhd (residualGreenKernel w t a) (H \ fwdHull w t) := by
  classical
  by_cases ha : a ∈ H
  · by_cases haD : a ∈ H \ fwdHull w t
    · obtain ⟨hd, hi, hm⟩ := activeDiskChart_facts hw ht
      unfold residualGreenKernel
      simp only [ite_eq_left ha, ite_eq_left haD]
      exact Sec6.harmonicOnNhd_greenDiff (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht)
          sdiff_subset hd hi hm haD
    · intro z hz
      have hza : z ≠ a := fun he => haD (he ▸ hz)
      have hzc : z ≠ conj a := by
        intro he
        have hz' : 0 < z.im := hz.1
        have ha' : 0 < a.im := ha
        rw [he, Complex.conj_im] at hz'
        linarith
      have h1 := (analyticAt_id.sub analyticAt_const).harmonicAt_log_norm (sub_ne_zero.2 hzc)
      have h2 := (analyticAt_id.sub analyticAt_const).harmonicAt_log_norm (sub_ne_zero.2 hza)
      unfold residualGreenKernel
      simp only [ite_eq_left ha, ite_eq_right haD, greenH]
      exact h1.sub h2
  · unfold residualGreenKernel
    simp only [ite_eq_right ha]
    exact fun z (_ : z ∈ H \ fwdHull w t) => InnerProductSpace.harmonicAt_const (0 : ℝ)

/-- The residual kernel is nonnegative, including at the regularized diagonal. -/
theorem residualGreenKernel_nonneg {w : ℝ → ℝ} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) (a : ℂ) {z : ℂ} (hz : z ∈ H \ fwdHull w t) :
    0 ≤ residualGreenKernel w t a z := by
  classical
  by_cases ha : a ∈ H
  · by_cases haD : a ∈ H \ fwdHull w t
    · have hoff : ∀ y ∈ H \ fwdHull w t, y ≠ a → 0 ≤ residualGreenKernel w t a y := by
        intro y hy hya
        rw [residualGreenKernel_eq hw ht hy ha hya, indicator_of_mem haD]
        exact sub_nonneg.2 (GB7a.greenH_fwdMap_le hw ht hy haD hya).2
      by_cases hza : z = a
      · subst z
        have hc := (harmonicOnNhd_residualGreenKernel hw ht a a haD).1.continuousAt
        have hlim : Tendsto (residualGreenKernel w t a) (𝓝[≠] a)
            (𝓝 (residualGreenKernel w t a a)) := hc.tendsto.mono_left nhdsWithin_le_nhds
        apply isClosed_Ici.mem_of_tendsto hlim
        filter_upwards [nhdsWithin_le_nhds
          ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht).mem_nhds haD), self_mem_nhdsWithin]
          with y hy hya using hoff y hy hya
      · exact hoff z hz hza
    · rw [residualGreenKernel, ite_eq_left ha, ite_eq_right haD]
      exact QuantumZipper.greenH_nonneg
        (show z ∈ Hbar from le_of_lt (show 0 < z.im from hz.1))
        (show a ∈ Hbar from le_of_lt (show 0 < a.im from ha)) (fun he => haD (he ▸ hz))
  · rw [residualGreenKernel, ite_eq_right ha]

end InteractingSLE.Restart.FlowLocalityGen
