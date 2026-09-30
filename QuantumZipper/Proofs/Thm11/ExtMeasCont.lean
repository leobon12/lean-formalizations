/-
Own elementary proof (no source needed): continuity in time of the forward field below the
swallowing time; the SLE/GFF field is an ODE-solution-based expression, so this is standard
plumbing.
-/

import QuantumZipper.Proofs.Loewner.ForwardFlow
import QuantumZipper.Statements.CouplingFields
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.Thm11Asm.MeasCont

variable {W : ℝ → ℝ} {z : ℂ}

/-! ## Membership in the forward hull via the swallowing time

`fwdHull W t = {z ∈ ℍ | τ(z) ≤ t}` by definition, so for `t ≥ 0` membership is equivalent to
`σ ≤ t` when `τ(z) = ENNReal.ofReal σ`. (`t ≥ 0` is needed: for `t < 0` the right-hand side
`ENNReal.ofReal t` collapses to `0`.) -/

/-- Below the swallowing time `σ` of `z`, and at times `t ≥ 0`, the point `z` is not swallowed. -/
theorem not_mem_fwdHull_of_lt_tau {σ t : ℝ} (hz : 0 < z.im)
    (hσ : swallowTime W z = ENNReal.ofReal σ) (ht0 : 0 ≤ t) (ht : t < σ) :
    z ∉ fwdHull W t := by
  intro hmem
  have hle : ENNReal.ofReal σ ≤ ENNReal.ofReal t := by simpa [hσ] using hmem.2
  exact absurd ((ENNReal.ofReal_le_ofReal_iff ht0).mp hle) (not_le.mpr ht)

/-- For `t ≥ 0`, membership in the hull is exactly `σ ≤ t`, where `τ(z) = ENNReal.ofReal σ`. -/
theorem mem_fwdHull_ofReal_iff {σ t : ℝ} (hz : 0 < z.im)
    (hσ : swallowTime W z = ENNReal.ofReal σ) (ht0 : 0 ≤ t) :
    z ∈ fwdHull W t ↔ σ ≤ t := by
  constructor
  · intro hmem
    exact (ENNReal.ofReal_le_ofReal_iff ht0).mp (by simpa [hσ] using hmem.2)
  · intro hst
    exact ⟨hz, by rw [hσ]; exact ENNReal.ofReal_le_ofReal hst⟩

/-! ## Continuity in time below the swallowing time -/

/-- The imaginary part of `fwdMap W t z` is positive while `z` is not swallowed: `fwdMap`
agrees with the (non-vanishing, positive-imaginary-part) solution on `[0,b]`. -/
theorem fwdMap_im_pos_of_not_mem_fwdHull (hW : Continuous W) (hz : 0 < z.im)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : z ∉ fwdHull W b) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) b) :
    0 < (fwdMap W t z).im := by
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hb0 hz hb
  rw [fwdMap_eq hW hz hu ht]
  exact (im_isForwardSol_le hW hz hu).2 t ht

/-- `t ↦ fwdMap W t z` is continuous on `[a,b]` as long as `z` is not swallowed by time `b`. -/
theorem continuousOn_fwdMap_Icc (hW : Continuous W) (hz : 0 < z.im)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : z ∉ fwdHull W b) :
    ContinuousOn (fun t => fwdMap W t z) (Icc a b) := by
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull (t := b) (ha.trans hab) hz hb
  refine (hu.1.mono (Icc_subset_Icc ha le_rfl)).congr ?_
  intro t ht
  exact fwdMap_eq hW hz hu ⟨ha.trans ht.1, ht.2⟩

/-- `t ↦ Im logDerivFwd W t z` is continuous on `[a,b]` below the swallowing time: it is the
interval primitive of the continuous integrand `s ↦ 2 / (fwdMap W s z)²`. -/
theorem continuousOn_imLogDerivFwd_Icc (hW : Continuous W) (hz : 0 < z.im)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : z ∉ fwdHull W b) :
    ContinuousOn (fun t => (logDerivFwd W t z).im) (Icc a b) := by
  have hb0 : (0 : ℝ) ≤ b := ha.trans hab
  have hmap : ContinuousOn (fun s => fwdMap W s z) (Icc (0 : ℝ) b) :=
    continuousOn_fwdMap_Icc hW hz le_rfl hb0 hb
  have hne : ∀ s ∈ Icc (0 : ℝ) b, fwdMap W s z ≠ 0 := by
    intro s hs h0
    have hpos := fwdMap_im_pos_of_not_mem_fwdHull hW hz hb0 hb hs
    have : (fwdMap W s z).im = 0 := by simp [h0]
    linarith
  have hpow_ne : ∀ s ∈ Icc (0 : ℝ) b, (fwdMap W s z) ^ 2 ≠ 0 := by
    intro s hs h
    rw [sq] at h
    exact mul_ne_zero (hne s hs) (hne s hs) h
  have hdiv : ContinuousOn (fun s => (2 : ℂ) / (fwdMap W s z) ^ 2) (Icc (0 : ℝ) b) :=
    ContinuousOn.div (s := Icc (0 : ℝ) b) continuousOn_const (hmap.pow 2) hpow_ne
  have hint : IntegrableOn (fun s => (2 : ℂ) / (fwdMap W s z) ^ 2)
      (Set.uIcc (0 : ℝ) b) volume := by
    rw [Set.uIcc_of_le hb0]
    exact hdiv.integrableOn_Icc
  have hcont0 : ContinuousOn (fun t => (logDerivFwd W t z).im) (Icc (0 : ℝ) b) := by
    have hprim : ContinuousOn
        (fun t => ∫ s in (0 : ℝ)..t, (2 : ℂ) / (fwdMap W s z) ^ 2) (Icc (0 : ℝ) b) := by
      have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := b) hint
      rwa [Set.uIcc_of_le hb0] at h
    refine ((Complex.continuous_im.comp_continuousOn hprim.neg)).congr ?_
    intro t _
    show (logDerivFwd W t z).im = -(∫ s in (0 : ℝ)..t, 2 / (fwdMap W s z) ^ 2).im
    simp only [logDerivFwd, Complex.neg_im]
  exact hcont0.mono (Icc_subset_Icc ha le_rfl)

/-- **The forward field is continuous in time below the swallowing time.** The map
`t ↦ h0fwd κ (fwdMap W t z) - chiC κ * Im logDerivFwd W t z` is continuous on `[a,b]`: the
first term is `Complex.arg` applied to a continuous curve lying in the slit plane (the
imaginary part stays positive), the second is continuous by
`continuousOn_imLogDerivFwd_Icc`. -/
theorem continuousOn_fieldAt_Icc (hW : Continuous W) (κ : ℝ) (hz : 0 < z.im)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : z ∉ fwdHull W b) :
    ContinuousOn (fun t => h0fwd κ (fwdMap W t z) - chiC κ * (logDerivFwd W t z).im)
      (Icc a b) := by
  have hb0 : (0 : ℝ) ≤ b := ha.trans hab
  have hmap := continuousOn_fwdMap_Icc hW hz ha hab hb
  have hmaps : MapsTo (fun t => fwdMap W t z) (Icc a b) slitPlane := fun t ht =>
    Or.inr (fwdMap_im_pos_of_not_mem_fwdHull hW hz hb0 hb ⟨ha.trans ht.1, ht.2⟩).ne'
  have harg : ContinuousOn (fun t => Complex.arg (fwdMap W t z)) (Icc a b) :=
    Complex.continuousOn_arg.comp' hmap hmaps
  have h0 : ContinuousOn (fun t => h0fwd κ (fwdMap W t z)) (Icc a b) :=
    (harg.const_mul (-(2 / Real.sqrt κ))).congr (fun _ _ => rfl)
  exact h0.sub ((continuousOn_imLogDerivFwd_Icc hW hz ha hab hb).const_mul (chiC κ))

end QuantumZipper.Thm11Asm.MeasCont
