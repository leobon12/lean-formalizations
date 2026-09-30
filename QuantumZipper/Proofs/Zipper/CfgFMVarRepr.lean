import QuantumZipper.Proofs.Zipper.CfgFMVarDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FM-VAR (1): stochastic Fubini for the pushed first mode at scale 1

`CfgFM.tRepr`: the scale-free copy of `Thm18Asm.G1FM2.g1FMReprStmt_holds`
(`G1FM2Repr.lean`), for a single map `ψ` and a process `V(d, r)` without scale coordinate.
Source as there: stochastic Fubini `CoordReg.integral_kernelAvg_ae_eq_bind`
(Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), proof of
Prop. 3.1); the lift is own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6
namespace CfgFM

open Thm18Asm Thm18Asm.G1FM2 Thm18Asm.G1RC CircleFubini CoordReg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **Stochastic Fubini on one arc.** -/
theorem ae_integral_tArc_eq {ψ : ℂ → ℂ} (hψ : PsiGood ψ) (hX : IsFreeGFFModConstH X P)
    {V : ℂ × ℝ → Ω → ℝ}
    (hVc : ∀ ω, ContinuousOn (fun p => V p ω) (univ ×ˢ Ioi 0))
    (hVV : ∀ (d : ℂ) (r : ℝ), 0 < r → r < d.im → (fun ω => V (d, r) ω) =ᵐ[P]
      fun ω => X ω ((foldedCircle d r).map fun z => ((1 : ℝ) : ℂ) * ψ z))
    {w v : ℂ} {τ s : ℝ} (hv : ‖v‖ = τ) (hτ : 0 < τ) (hs : 0 < s) (hτs : τ + s < w.im) :
    ∀ᵐ ω ∂P, ∫ z, V (z, s) ω ∂D3Plus.fmArc w v = X ω (Thm18Asm.pfmMeas ψ 1 w v s) := by
  have hψm : Measurable ψ := hψ.1
  set f : ℂ → ℂ := fun u => ((1 : ℝ) : ℂ) * ψ u with hf_def
  have hf : Measurable f := measurable_const.mul hψm
  set h := w.im - τ with hh
  have hsh : s < h := by rw [hh]; linarith
  set K := closedBall w τ with hK_def
  have hKim : ∀ z ∈ K, h ≤ z.im := by
    intro z hz
    have h1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [Complex.sub_im] at h1
    rw [hh]; linarith [neg_abs_le (z.im - w.im)]
  have hKH : K ⊆ Hbar := fun z hz => show (0 : ℝ) ≤ z.im by linarith [hKim z hz]
  have hlift : ∀ z ∈ K, liftH h z = z := fun z hz => liftH_of_le (hKim z hz)
  set Φ : Kernel ℂ ℂ := (pushKernel f hf s).comap (liftH h) (continuous_liftH h).measurable
    with hΦ_def
  have hΦK : ∀ z ∈ K, Φ z = (foldedCircle z s).map f := fun z hz => by
    rw [hΦ_def, Kernel.comap_apply, pushKernel_apply, hlift z hz]
  -- kernel bounds on `K`
  obtain ⟨R, C₁, hC₁, hB⟩ := pushFrost_unif hψ (w := w) (ρ := τ + s) (S := 1) (α := 1)
    (C₀ := 6 / s) (M := 1) (by linarith) hτs one_pos one_pos (by positivity) zero_le_one
  have hBz : ∀ z ∈ K, ((foldedCircle z s).map f) (ballH R)ᶜ = 0 ∧
      TwoPoint.IsFrostman ((foldedCircle z s).map f) 1 C₁ := fun z hz =>
    hB (foldedCircle z s) (by simp) (Cor15Group.isFrostman_fc z hs) (by
      filter_upwards [foldedCircle_ae_dist_le' (hKH hz) hs.le] with x hx
      have := mem_closedBall.1 hz
      linarith [dist_triangle x z w])
  have hcS : ∀ z ∈ K, Φ z (ballH R)ᶜ = 0 := fun z hz => by rw [hΦK z hz]; exact (hBz z hz).1
  have hcP : ∀ z ∈ K, ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂Φ z ≤
      ENNReal.ofReal (C₁ / 1) := fun z hz y => by
    rw [hΦK z hz]; exact frostman_pot_le (hBz z hz).2 one_pos hC₁ y
  have hw : w ∈ K := mem_closedBall_self hτ.le
  -- the continuous process
  have hsl : ∀ ω, Continuous fun z => V (z, s) ω := fun ω =>
    (hVc ω).comp_continuous (by fun_prop) fun z => ⟨mem_univ _, hs⟩
  set Y : ℂ → Ω → ℝ := fun z ω => V (liftH h z, s) ω - V (liftH h w, s) ω with hY_def
  have hYc : ∀ ω, ContinuousOn (fun z => Y z ω) Hbar := fun ω =>
    (((hsl ω).comp (continuous_liftH h)).sub continuous_const).continuousOn
  have hlim : ∀ z, s < (liftH h z).im := fun z => by
    rw [liftH_im]; exact lt_of_lt_of_le hsh (le_max_right _ _)
  have hY : ∀ z ∈ Hbar, (fun ω => Y z ω) =ᵐ[P] fun ω => X ω (Φ z) - X ω (Φ w) := by
    intro z _
    filter_upwards [hVV (liftH h z) s hs (hlim z),
      hVV (liftH h w) s hs (hlim w)] with ω h1 h2
    simp only [hY_def]
    rw [h1, h2]; rfl
  set ν := D3Plus.fmArc w v with hν_def
  have hνK : ν Kᶜ = 0 := by
    have : ∀ᵐ z ∂ν, z ∈ K := by
      filter_upwards [G1FM.ae_dist_fmArc_le w v] with x hx
      rw [hv] at hx; exact hx
    exact ae_iff.1 this
  have hF := integral_kernelAvg_ae_eq_bind hX Φ (K' := K) (R := R) ENNReal.ofReal_ne_top
    hcS hcP hw hYc hY ν (isCompact_closedBall w τ) hKH subset_rfl hνK
  -- the constant term
  have hadm : IsAdmissibleH (Φ w) :=
    admissible_of_bounds (hcS w hw) ENNReal.ofReal_ne_top (hcP w hw)
  set m : ℝ≥0 := (ν univ).toNNReal with hm_def
  have hm : ν univ = (m : ℝ≥0∞) := (ENNReal.coe_toNNReal (measure_ne_top ν _)).symm
  have hlin := hX.linear (Φ w) (Φ w) hadm hadm m 0
  have hsm : ν univ • Φ w = m • Φ w + (0 : ℝ≥0) • Φ w := by
    rw [zero_smul, add_zero, hm]
    exact (ENNReal.smul_def m _).symm
  -- the bind
  have hae : ∀ᵐ z ∂ν, z ∈ K := ae_iff.2 hνK
  have hbind : ν.bind Φ = Thm18Asm.pfmMeas ψ 1 w v s := by
    rw [show Thm18Asm.pfmMeas ψ 1 w v s = ν.bind (pushKernel f hf s) from
      (bind_pushKernel f hf s ν).symm]
    ext A hA
    rw [Measure.bind_apply hA Φ.measurable.aemeasurable,
      Measure.bind_apply hA (pushKernel f hf s).measurable.aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hΦK z hz, pushKernel_apply]
  filter_upwards [hF, hlin, hVV w s hs (by linarith)] with ω h2 h3 h4
  have hYi : Integrable (fun z => V (liftH h z, s) ω) ν := by
    have : IntegrableOn (fun z => V (liftH h z, s) ω) K ν :=
      ((hsl ω).comp (continuous_liftH h)).continuousOn.integrableOn_compact
        (isCompact_closedBall w τ)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at this
  have e0 : ∫ z, V (z, s) ω ∂ν = ∫ z, V (liftH h z, s) ω ∂ν :=
    integral_congr_ae (hae.mono fun z hz => by simp only [hlift z hz])
  have e1 : ∫ z, V (liftH h z, s) ω ∂ν =
      ∫ z, Y z ω ∂ν + (ν univ).toReal * V (liftH h w, s) ω := by
    simp only [hY_def]
    rw [integral_sub hYi (integrable_const _), integral_const, smul_eq_mul, measureReal_def]
    ring
  have h4' : V (liftH h w, s) ω = X ω (Φ w) := by
    rw [hlift w hw, hΦK w hw]; exact h4
  rw [e0, e1, h2, hsm, h3, h4', hm, ← hbind]
  simp only [ENNReal.coe_toReal, NNReal.coe_zero, zero_mul, add_zero]
  ring

/-- **Scale-1 representation of the first mode.** -/
theorem tRepr {ψ : ℂ → ℂ} (hψ : G1RC.PsiGood ψ) (hX : IsFreeGFFModConstH X P)
    {V : ℂ × ℝ → Ω → ℝ} (hVc : ∀ ω, ContinuousOn (fun p => V p ω) (univ ×ˢ Ioi 0))
    (hVV : ∀ (d : ℂ) (r : ℝ), 0 < r → r < d.im → (fun ω => V (d, r) ω) =ᵐ[P]
      fun ω => X ω ((foldedCircle d r).map fun z => ((1 : ℝ) : ℂ) * ψ z))
    (k : Fin 2) {w : ℂ} {τ s : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ + s < w.im) :
    ∀ᵐ ω ∂P, D3Plus.fmPart k (D3Plus.fmInt (fun p => V p ω) w τ s) =
      X ω (Thm18Asm.pfmMeas ψ 1 w ((τ : ℂ) * D3Plus.fmDir k) s) -
        X ω (Thm18Asm.pfmMeas ψ 1 w (-((τ : ℂ) * D3Plus.fmDir k)) s) := by
  have hnv : ‖(τ : ℂ) * D3Plus.fmDir k‖ = τ := by
    rw [norm_mul, D3Plus.norm_fmDir, Complex.norm_real, Real.norm_of_nonneg hτ.le, mul_one]
  filter_upwards [ae_integral_tArc_eq hψ hX hVc hVV hnv hτ hs hτs,
    ae_integral_tArc_eq hψ hX hVc hVV (by rw [norm_neg, hnv]) hτ hs hτs] with ω h1 h2
  have hg : ContinuousOn (fun p : ℂ × ℝ => V p ω) (Hbar ×ˢ Ioi 0) :=
    (hVc ω).mono fun p hp => ⟨mem_univ _, hp.2⟩
  refine (D3Plus.fmPart_fmInt_eq_arc hg k hτ (by linarith) hs).trans ?_
  rw [← h1, ← h2]

end CfgFM
end QuantumZipper.E6
