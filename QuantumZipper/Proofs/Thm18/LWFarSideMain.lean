import QuantumZipper.Proofs.Thm18.LWFarSideLimit
import QuantumZipper.Proofs.Thm18.LWFarSideCross
import QuantumZipper.Proofs.Thm18.LWBeurlingMain
import QuantumZipper.Proofs.Complex.KoebeHalfPlane
import QuantumZipper.Proofs.Loewner.CaraR8
import QuantumZipper.Proofs.Loewner.ArcDeterminesDriver
import QuantumZipper.Proofs.RS.Simple
import QuantumZipper.Proofs.RS.TraceMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node LWF-5: the side bound `SideStmt κ` (PROVED for `0 < κ < 4`)

`sideStmt_holds : SideStmt κ`. Source: G. Lawler, B. Werness, *Multi-point Green's functions for
SLE and an estimate of Beffara*, Ann. Probab. 41 (2013), eq. (2), p. 6 (with the harmonic
function `arg Z_t/π`, p. 8), and V. Beffara, *The dimension of the SLE curves*, Ann. Probab. 36
(2008), Lemma 6, p. 13.

* `lwfSide_det`: the deterministic bound in the context `SideCtx` (`LWFarSideDet.lean`,
  `LWFarSideSign.lean`), with the Beurling estimate LWF-4 (`beurlingHarmStmt_holds`);
* `lwfSide_ctx`: the context holds for a driver whose trace is a continuous simple curve
  generating the hulls (a.s. for `κ < 4`: `RS.ae_sleTrace_good`, `RS.ae_sleTrace_simple_of_lt_four`,
  `RS.ae_fwdHull_eq_sleTrace_image_of_lt_four`), via the Carathéodory extension of the time-reversed
  reverse map (`CaraR.extExists`, `CaraR.revMapCaratheodory`; Pommerenke, *Boundary Behaviour of
  Conformal Maps*, Thm 2.1, Prop 2.5, Thm 2.6);
* time `t = 0` is elementary (`Z_0 = id`, `Υ_0(w) = Im w`).
-/

noncomputable section

open Set Filter Metric Complex MeasureTheory ProbabilityTheory
open scoped Topology Real NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- **The context holds** for a driver whose trace is a continuous simple curve generating the
hulls: `F` is the Carathéodory extension of the time-reversed reverse map. -/
theorem lwfSide_ctx (hW : Continuous W) (hW0 : W 0 = 0) (htr0 : trace W 0 = 0)
    (htrc : ContinuousOn (trace W) (Ici 0)) (hinj : InjOn (trace W) (Ici 0))
    (htrH : ∀ s > (0 : ℝ), trace W s ∈ H)
    (hhull : ∀ s : ℝ, 0 ≤ s → fwdHull W s = trace W '' Ioc 0 s) (ht : 0 < t) :
    ∃ F : ℂ → ℂ, SideCtx W t F := by
  set γ : ℝ → ℂ := fun s => trace W (t * s) with hγdef
  have hγc : ContinuousOn γ (Icc 0 1) :=
    htrc.comp (continuousOn_const.mul continuousOn_id) fun s hs => mul_nonneg ht.le hs.1
  have hγi : InjOn γ (Icc 0 1) := fun a ha b hb h =>
    mul_left_cancel₀ ht.ne' (hinj (mul_nonneg ht.le ha.1) (mul_nonneg ht.le hb.1) h)
  have hγ0 : (γ 0).im = 0 := by simp [hγdef, htr0]
  have hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H := fun u hu => htrH _ (mul_pos ht hu.1)
  have himg : γ '' Ioc 0 1 = trace W '' Ioc 0 t := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨t * s, ⟨mul_pos ht hs.1, mul_le_of_le_one_right ht.le hs.2⟩, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r / t, ⟨div_pos hr.1 ht, (div_le_one ht).2 hr.2⟩, by
        simp only [hγdef, mul_div_cancel₀ _ ht.ne']⟩
  have hrev : revHull (ArcDriver.trev W t) t = γ '' Ioc 0 1 := by
    rw [ArcDriver.revHull_trev hW hW0 ht, hhull t ht.le, himg]
  obtain ⟨F, hF⟩ := CaraR.extExists _ (ArcDriver.continuous_trev hW t) (ArcDriver.trev_zero W t)
    t ht γ hγc hγi hγ0 hγH hrev
  have hK : IsSimpleCurveHull (fwdHull W t) :=
    ⟨γ, hγc, hγi, hγ0, hγH, by rw [hhull t ht.le, himg]⟩
  obtain ⟨C, hC⟩ := ArcDriver.exists_bound_revMap_trev hW hW0 ht CaraR.revMapCaratheodory hK
  have hFeq : EqOn F (fwdMapInv W t) H := fun u hu => by
    rw [hF.eqOn hu, UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht.le hu]
    rfl
  have hF0 : F 0 = trace W t := by
    have h1 : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝[Hbar] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) * I)) :=
          ((Complex.continuous_ofReal.mul continuous_const).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        show 0 ≤ ((y : ℂ) * I).im
        simpa using (le_of_lt (show (0 : ℝ) < y from hy))
    have h2 := (hF.cont 0 (show (0 : ℂ) ∈ Hbar by simp [Hbar])).tendsto.comp h1
    have hT : Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 (F 0)) := by
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hFeq (show 0 < ((y : ℂ) * I).im by simpa using (show (0 : ℝ) < y from hy))
    exact (hT.limUnder_eq).symm
  have hγ1 : γ 1 = trace W t := by simp [hγdef]
  refine ⟨F, ⟨hW, hW0, ht, hF.cont, hFeq, fun x hx => ?_, hF0, ⟨C, fun u hu => ?_⟩,
    hhull t ht.le, htrc.mono Icc_subset_Ici_self, htr0⟩⟩
  · have h0 : F ((0 : ℝ) : ℂ) = γ 1 := by rw [Complex.ofReal_zero, hF0, hγ1]
    exact hF.inj_tip x 0 (by rw [hx, hγ1]) h0
  · rw [hF.eqOn hu]; exact hC u hu

end LWFar
end Thm18Asm
end QuantumZipper
