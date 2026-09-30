import QuantumZipper.Proofs.Zipper.SWCoreA8Rand
import QuantumZipper.Proofs.LQG.WedgeCanonical2
import QuantumZipper.Proofs.Thm18.G1Z3AddFun

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A8 (6): the wedge add-on for regularized values away from `0`

For a good free sample `x` (`WedgeTK.GoodRad x F`, raw dyadic agreement) and a continuous radial
process `A`, the wedge field `wedgeField (lateralPart x) A Q` has the same dyadic averages as
`x + ofFun (wedgeProfile x A Q)` off the circles through `0` (`WedgeCan.avgReg_wedgeField_eq`).
Hence, for a probability measure `ν` carried by a compact set at height `≥ 3δ` along which the
smoothed pairings of `x` converge,

  `evalReg (wedgeField (lateralPart x) A Q) ν = evalReg x ν + ∫ p̃ dν`   (`a8_evalReg_wedge_add`),

with `p̃ = a8Cut` the globally continuous cutoff of the profile at modulus `δ` (the proved add-on
identity `Thm18Asm.G1Z3.evalReg_add_ofFun_of_ae_z3`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ}

open RegClosure in
/-- Smoothed circle pairings of a regular sample converge to `evalReg`. -/
theorem a8_reg_tendsto (h : IsRegularWith x F) (v : ℂ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun k => ∫ u, avgReg x k u ∂foldedCircle v s) atTop
      (𝓝 (evalReg x (foldedCircle v s))) := by
  have e : ∀ k : ℕ, ∫ u, avgReg x k u ∂foldedCircle v s =
      ∫ u, F (u, radius k) ∂foldedCircle (foldH v) s := by
    intro k
    rw [integral_congr_ae ((fc_ae_mem_Hbar v s).mono fun u hu => h.avgReg_eq k hu),
      integral_fc_foldH (continuousOn_slice h.1 (radius_pos k))]
  simp_rw [e]
  rw [h.evalReg_fc v hs]
  exact (h.2.2.tendsto_at (a := (foldH v, s)) ⟨CircleFubini.foldH_mem_Hbar' v, hs⟩).comp tendsto_radius_nhdsGT

/-- `evalReg` only reads eventual `ν`-a.e. values of the dyadic averages. -/
theorem a8_evalReg_congr {y : FieldSample} {ν : Measure ℂ}
    (h : ∀ᶠ j in atTop, ∀ᵐ u ∂ν, avgReg x j u = avgReg y j u) : evalReg x ν = evalReg y ν := by
  have h' : (fun j => ∫ u, avgReg x j u ∂ν) =ᶠ[atTop] fun j => ∫ u, avgReg y j u ∂ν :=
    h.mono fun j hj => integral_congr_ae hj
  unfold evalReg limUnder
  rw [Filter.map_congr h']

/-- The cutoff of the wedge profile at modulus `δ`. -/
def a8Cut (x : FieldSample) (A : ℝ → ℝ) (Q δ : ℝ) (u : ℂ) : ℝ :=
  -radAvgReg x (max ‖u‖ δ) + Q * -Real.log (max ‖u‖ δ) + A (-Real.log (max ‖u‖ δ))

theorem continuous_a8Cut (hG : WedgeTK.GoodRad x F) (hA : Continuous A) (Q : ℝ) {δ : ℝ}
    (hδ : 0 < δ) : Continuous (a8Cut x A Q δ) := by
  have h0 : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
  have h1 : ContinuousOn (fun t : ℝ => radAvgReg x t) (Ioi 0) :=
    ContinuousOn.congr (f := fun t => F (0, t))
      (hG.1.1.comp (continuousOn_const.prodMk continuousOn_id) fun t ht => ⟨h0, ht⟩)
      fun t ht => hG.radAvgReg_eq ht
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono fun t ht => ne_of_gt (show (0 : ℝ) < t from ht)
  have hwg : ContinuousOn (fun t : ℝ => -radAvgReg x t + Q * -Real.log t + A (-Real.log t))
      (Ioi 0) := by
    exact (h1.neg.add (continuousOn_const.mul hlog.neg)).add (hA.comp_continuousOn hlog.neg)
  have hm : Continuous fun u : ℂ => max ‖u‖ δ := continuous_norm.max continuous_const
  exact hwg.comp_continuous hm fun u => lt_of_lt_of_le hδ (le_max_right _ _)

theorem a8Cut_eq (Q : ℝ) {δ : ℝ} {u : ℂ} (hu : δ ≤ ‖u‖) :
    a8Cut x A Q δ u = WedgeCan.wedgeProfile x A Q u := by
  simp only [a8Cut, max_eq_left hu]
  rfl

/-- Dyadic averages of the wedge field away from `0`. -/
theorem a8_evalReg_wedge (hG : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (Q : ℝ) {δ : ℝ} (hδ : 0 < δ) {ν : Measure ℂ}
    (hν : ∀ᵐ u ∂ν, δ ≤ u.im) :
    evalReg (wedgeField (lateralPart x) A Q) ν =
      evalReg (x + ofFun (WedgeCan.wedgeProfile x A Q)) ν := by
  apply a8_evalReg_congr
  have hrad : Tendsto radius atTop (𝓝 0) := by
    unfold radius
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hrad.eventually (gt_mem_nhds hδ)] with j hj
  filter_upwards [hν] with u hu
  have hHb : u ∈ Hbar := show 0 ≤ u.im by linarith
  have hne : ‖u‖ ≠ radius j := ne_of_gt (lt_of_lt_of_le hj (hu.trans (Complex.im_le_norm u)))
  exact WedgeCan.avgReg_wedgeField_eq hG hraw hA Q hHb hne

theorem a8_cth_im {K : Set ℂ} {δ : ℝ} (hδ : 0 < δ) (hK : ∀ u ∈ K, 3 * δ ≤ u.im) :
    ∀ u ∈ cthickening δ K, δ ≤ u.im := by
  intro u hu
  obtain ⟨v, hv, huv⟩ := mem_iUnion₂.1
    (cthickening_subset_iUnion_closedBall_of_lt K (by linarith : 0 < 2 * δ)
      (by linarith : δ < 2 * δ) hu)
  rw [mem_closedBall, dist_eq_norm] at huv
  have h := (Complex.abs_im_le_norm (u - v)).trans huv
  rw [Complex.sub_im, abs_le] at h
  linarith [hK v hv, h.1]

/-- **The wedge add-on for `evalReg`.** -/
theorem a8_evalReg_wedge_add (hG : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (Q : ℝ) {δ : ℝ} (hδ : 0 < δ) {ν : Measure ℂ} [IsProbabilityMeasure ν]
    {Kψ : Set ℂ} (hK : IsCompact Kψ) (hKim : ∀ u ∈ Kψ, 3 * δ ≤ u.im) (hν : ∀ᵐ u ∂ν, u ∈ Kψ)
    {L : ℝ} (hL : Tendsto (fun j => ∫ u, avgReg x j u ∂ν) atTop (𝓝 L)) :
    evalReg (wedgeField (lateralPart x) A Q) ν = evalReg x ν + ∫ u, a8Cut x A Q δ u ∂ν := by
  have hcth := a8_cth_im hδ hKim
  rw [a8_evalReg_wedge hG hraw hA Q hδ
    (hν.mono fun u hu => hcth u (self_subset_cthickening _ hu))]
  exact Thm18Asm.G1Z3.evalReg_add_ofFun_of_ae_z3 hG.1
    (continuous_a8Cut hG hA Q hδ).continuousOn hK
    (fun u hu => show 0 ≤ u.im by linarith [hKim u hu, hδ]) hδ
    (fun u hu => a8Cut_eq Q ((hcth u hu).trans (Complex.im_le_norm u))) hν hL

end SWCore
end QuantumZipper
