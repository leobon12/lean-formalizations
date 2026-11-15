/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelSlitBase
import InteractingSLE.Spec.Sec5.CrossRestartKernelSlitData

/-!
# The flow-slit side comparison for the counterflow restart

The obstacle is read in its own reversed-slit chart. At a real inverse image different
from zero, the image chain's real flow transports the boundary data, and reflection
makes its derivative argument tend to zero. The new curve can be nonsimple.

`RealSlitSideStatement` is the pointwise comparison interface: its inputs are the
union mean's boundary comparison, the obstacle mean's chart identity, and the initial
boundary-data match. It makes no assertion that those inputs have been proved for a
particular random restart configuration.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped Real
open QuantumZipper (H fwdHull fwdMapInv logDerivFwd)

namespace InteractingSLE.Sec5.CrossRestart

open WangWu hiding ratPt exists_ratPt_dist_lt
open MartChar.RealFlow Restart.RetAux79

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {T : ℝ}

/-- Real-flow transport of force data needs interior traces, not simple traces. -/
theorem forceBoundaryData_imgChart_eq_of_mem_H
    (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T)
    {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0)
    {x r : ℝ} (hr : r ≠ 0) (hF : extendFrom H (fwdMapInv W T) x = r)
    (hrL : ∀ i, xL i ≠ r) (hrR : ∀ j, xR j ≠ r) :
    forceBoundaryData κ ρL ρR
        (fun i => -rightImg (fun s => -W s) (-xL i) T - W T)
        (fun j => rightImg W (xR j) T - W T) x =
      forceBoundaryData κ ρL ρR xL xR r := by
  rcases eq_realFlow_of_extendFrom_of_mem_H hη hηH hW hW0 hT hr hF with
    ⟨hneg, he⟩ | ⟨hpos, he⟩
  · rw [he]
    have hal := alive_neg_of_mem_H hη hηH hW hW0 hT
    have hh := forceBoundaryData_flow_left (κ := κ) ρL ρR (xR := xR) hW hT
      (neg_pos.2 hneg) (hal _ (neg_pos.2 hneg))
      (xL := xL) (fun i hn => hrL i (by linarith only [hn])) (fun i => ?_)
    · rwa [neg_neg] at hh
    · intro hn
      have he' : gImg (fun s => -W s) (-r) T =
          rightImg (fun s => -W s) (-xL i) T := by linarith only [hn]
      have hne : -xL i ≠ -r := fun h => hrL i (neg_injective h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hh := GlueImg.rightImg_lt_gImg_of_lt hW.neg hT hal
          (neg_nonneg.2 (hxL i)) hlt
        have hh' : rightImg (fun s => -W s) (-xL i) T <
            gImg (fun s => -W s) (-r) T := hh
        exact hh'.ne he'.symm
      · have hh := (rightImg_le_gImg_iff hW.neg hT (hal _ (neg_pos.2 hneg)) hne).1 he'.ge
        exact (not_lt.2 hgt.le) hh
  · rw [he]
    exact forceBoundaryData_flow_right ρL ρR hW hT hpos
      (alive_of_mem_H hη hηH hW hW0 hT _ hpos) hrR

/-- The deterministic flow-slit comparison, with the initial data match explicit.
The hull `A` is the explored counterflow and `negInv '' fwdHull w s` the flow slit. -/
def RealSlitSideStatement : Prop :=
  ∀ (w : ℝ → ℝ) (s : ℝ), Continuous w → w 0 = 0 → 0 ≤ s →
    HasBdryLimits (fwdMapInv w s) →
    ∀ (A : Set ℂ), Bornology.IsBounded A →
      (∀ z ∈ closure A, z ∈ A ∨ z = 0) →
      Disjoint A (negInv '' fwdHull w s) → A ⊆ H →
      ∀ (M mG V : ℂ → ℝ) (χ : ℝ),
        (∀ z₀ ∈ negInv '' fwdHull w s ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, A ∩ ball z₀ r ⊆ negInv '' fwdHull w s) →
          Tendsto (fun z => M z - mG z)
            (𝓝[H \ (A ∪ negInv '' fwdHull w s)] z₀) (𝓝 0)) →
        Tendsto (fun z => M z - mG z)
          (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (A ∪ negInv '' fwdHull w s))) (𝓝 0) →
        (∀ z ∈ H \ negInv '' fwdHull w s,
          mG z + χ * (GlueImg.logDerivPsi w s z).im = V (revChart w s z)) →
        ∀ (dV : ℝ → ℝ) (SV : Set ℝ), IsBoundedHarmonicExtension dV SV V →
          ∀ (W : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ),
            Continuous W → W 0 = 0 → IsLoewnerTrace W η →
            (∀ t ∈ Ioc (0 : ℝ) T, η t ∈ H) → 0 ≤ T →
            (∀ r : ℝ, r ≠ 0 → (r : ℂ) ∉ closure (fwdHull W T)) →
            ∀ (κ : ℝ) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
              (xL : Fin nL → ℝ) (xR : Fin nR → ℝ), (∀ i, xL i ≤ 0) →
              ∀ u : ℂ → ℝ,
                IsBoundedHarmonicExtension
                  (forceBoundaryData κ ρL ρR
                    (fun i => -rightImg (fun t => -W t) (-xL i) T - W T)
                    (fun j => rightImg W (xR j) T - W T))
                  (forceJumpSet (fun i => -rightImg (fun t => -W t) (-xL i) T - W T)
                    (fun j => rightImg W (xR j) T - W T)) u →
                ∀ (x r c : ℝ), r ≠ 0 → extendFrom H (fwdMapInv W T) x = r →
                  r ∉ SV →
                  x ∉ forceJumpSet (fun i => -rightImg (fun t => -W t) (-xL i) T - W T)
                    (fun j => rightImg W (xR j) T - W T) →
                  (∀ i, xL i ≠ r) → (∀ j, xR j ≠ r) →
                  forceBoundaryData κ ρL ρR xL xR r = dV r + c →
                  Tendsto (fun y => M (revChartInv w s (fwdMapInv W T y)) + c -
                    (u y - χ * ((logDerivFwd W T (fwdMapInv W T y)).im +
                      (GlueImg.logDerivPsi w s
                        (revChartInv w s (fwdMapInv W T y))).im)))
                    (𝓝[H] (x : ℂ)) (𝓝 0)

/-- The flow-slit comparison holds for nonsimple interior image curves. -/
theorem realSlitSideStatement : RealSlitSideStatement := by
  intro w s hw hw0 hs hB A hAb hAcl hAG hAH M mG V χ hG hInf hId dV SV hV
    W η T hW hW0 hη hηH hT hreal κ nL nR ρL ρR xL xR hxL u hu
    x r c hr hF hrV hxI hrL hrR hmatch
  have h1 := GlueImg.tendsto_fwdMapInv_nhdsWithin_of_real hη hW hW0 hT hF
  have h3 := (GlueImg.tendsto_add_argPsi_sub_of_real hw hw0 hs hB hAb hAcl hAG hAH
    hG hInf hId hr).comp h1
  have h4 := (hV.2.2 r hrV).comp h1
  obtain ⟨ρ, hρ, hd⟩ := GlueImg.exists_ball_disjoint_of_notMem_closure (hreal r hr)
  have h5 := (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero
    (isHPHull_fwdHull hW hT) (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hW hW0 hT)
    (isMapOut_fwdMap hW hW0 hT) hρ hd).comp h1
  have h6 := hu.2.2 x hxI
  rw [forceBoundaryData_imgChart_eq_of_mem_H hη hηH hW hW0 hT ρL ρR hxL hr hF hrL hrR,
    hmatch] at h6
  have hh := ((h3.add h4).add_const c).sub (h6.sub (h5.const_mul χ))
  have hv : (0 : ℝ) + dV r + c - (dV r + c - χ * 0) = 0 := by ring
  rw [hv] at hh
  refine hh.congr fun y => ?_
  simp only [Function.comp_apply]
  ring

end InteractingSLE.Sec5.CrossRestart
