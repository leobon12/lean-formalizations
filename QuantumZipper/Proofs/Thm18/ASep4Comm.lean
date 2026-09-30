import QuantumZipper.Proofs.Thm18.ASep3InnerGlob
import QuantumZipper.Proofs.GFF.CoordRegFubini
import QuantumZipper.Proofs.GFF.CoordRegPush
import QuantumZipper.Proofs.Zipper.JointModKolm
import QuantumZipper.Proofs.Thm18.G1PathCoordFam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP4 (step 1): the commutation identity of the dilated pushed-circle modification

For the continuous modification `Y` of `q ↦ X(nu5 W T q)` (`exists_contMod_νT_rescale`,
ASep3InnerGlob), at parameters `q5 t u s ρ = (t, Re u, Im u, s, ρ)` the measure is
`fc(u, ρ).map (s · f_t⁻¹)` (`nu5_q5`). Stochastic Fubini (`CoordReg.integral_kernelAvg_ae_eq_bind`,
with the pushed kernel of `z ↦ s · revMap (vRev W t) t z`) and the commutation of folded-circle
binds (`CoordReg.pushKernel_bind_comm`) give, almost surely,
`∫ Y(q5 t u s ρ) dfc(w, r)(u) = ∫ Y(q5 t v s r) dfc(w, ρ)(v)` (`ae_comm_Y5`).

This is the proof of `ASep.ae_comm_Y_fixed` (ASepWitB) / `G1Kolm.ae_integral_Vhat_eq_map` with the
map dilated by `s`. Source: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (stochastic
Fubini for the GFF); own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace ASep

open CircleFubini

/-- Parameters of the five-parameter family `nu5`. -/
def q5 (t : ℝ) (u : ℂ) (s ρ : ℝ) : Fin 5 → ℝ := ![t, u.re, u.im, s, ρ]

theorem continuous_q5 : Continuous fun p : ((ℝ × ℂ) × ℝ) × ℝ => q5 p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [q5] <;> fun_prop

theorem continuous_q5_fst (t s ρ : ℝ) : Continuous fun u : ℂ => q5 t u s ρ :=
  continuous_q5.comp (by fun_prop : Continuous fun u : ℂ => (((t, u), s), ρ))

/-- The dilated reverse flow map. -/
def dmap (W : ℝ → ℝ) (t s : ℝ) (z : ℂ) : ℂ := (s : ℂ) * revMap (RegCont.vRev W t) t z

theorem measurable_dmap {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    Measurable (dmap W t s) :=
  (measurable_const_mul _).comp
    (TwoPoint.measurable_revMap (RegCont.continuous_vRev hW t) ht)

theorem fc_map_dmap {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (s : ℝ) (u : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    (foldedCircle u ρ).map (dmap W t s) = (RegCont.νT W u ρ t).map fun z => (s : ℂ) * z := by
  rw [RegCont.νT_eq_pfc hW hW0 ht u hρ, Measure.map_map (measurable_const_mul _)
    (TwoPoint.measurable_revMap (RegCont.continuous_vRev hW t) ht)]
  rfl

theorem nu5_q5 {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T t : ℝ} (ht : t ∈ Icc 0 T)
    {u : ℂ} (hu : u ∈ Hbar) (s : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    nu5 W T (q5 t u s ρ) = (foldedCircle u ρ).map (dmap W t s) := by
  have h0 : clampT T (Fin.init (Fin.init (q5 t u s ρ))) 0 = t := by
    simp [clampT, q5, Fin.init, min_eq_left ht.2, max_eq_left ht.1]
  have h1 : cpt (clampT T (Fin.init (Fin.init (q5 t u s ρ)))) = u := by
    have hu' : 0 ≤ u.im := hu
    apply Complex.ext <;> simp [cpt, clampT, q5, Fin.init, abs_of_nonneg hu']
  have h3 : q5 t u s ρ 3 = s := rfl
  have h4 : q5 t u s ρ 4 = ρ := rfl
  rw [fc_map_dmap hW hW0 ht.1 s u hρ]
  unfold nu5
  rw [h0, h1, h3, h4]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Stochastic Fubini for the dilated modification.** -/
theorem ae_integral_Y5_eq_bind [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    {Y : (Fin 5 → ℝ) → Ω → ℝ}
    (hYc : ∀ ω, ContinuousOn (fun q => Y q ω) {q | 0 < q 3 ∧ 0 < q 4})
    (hYeq : ∀ q ∈ {q : Fin 5 → ℝ | 0 < q 3 ∧ 0 < q 4},
      (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (nu5 W T q))
    {t : ℝ} (ht : t ∈ Icc 0 T) {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : w ∈ Hbar) {r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∫ u, Y (q5 t u s ρ) ω ∂foldedCircle w r =
      X ω ((foldedCircle w r).bind
        (CoordReg.pushKernel (dmap W t s) (measurable_dmap hW ht.1 s) ρ)) := by
  set hf := measurable_dmap hW ht.1 s
  set Φ := CoordReg.pushKernel (dmap W t s) hf ρ with hΦ
  set R₁ : ℝ := ‖w‖ + r with hR₁
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hW T
  set B : ℝ := RegCont.revBound (2 * M) T (R₁ + ρ) with hB
  set C : ℝ := RegCont.frostC T ρ (R₁ + ρ) with hC
  have hC0 : 0 ≤ C := by simp only [hC, RegCont.frostC]; positivity
  have hfacts : ∀ z ∈ ballH R₁, Φ z (ballH (s * B))ᶜ = 0 ∧
      TwoPoint.IsFrostman (Φ z) (1 / 3) (C * s⁻¹ ^ (1 / 3 : ℝ)) := by
    intro z hz
    have hzR : ‖z‖ + ρ ≤ R₁ + ρ := by
      have := hz.1; rw [mem_closedBall, dist_zero_right] at this; linarith
    obtain ⟨-, hFr, hae⟩ := RegUnif.νT_box_facts hW hW0 hρ hM ht le_rfl hzR
    have e : Φ z = (RegCont.νT W z ρ t).map fun x => (s : ℂ) * x := by
      rw [hΦ, CoordReg.pushKernel_apply, fc_map_dmap hW hW0 ht.1 s z hρ]
    rw [e]
    refine ⟨?_, isFrostman_map_mul_of (by norm_num) hC0 hs le_rfl hFr⟩
    refine ae_iff.1 ((ae_map_iff (measurable_const_mul _).aemeasurable
      (isCompact_ballH _).isClosed.measurableSet).2 ?_)
    filter_upwards [hae] with x hx
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hs.le]
      exact mul_le_mul_of_nonneg_left hx.2 hs.le
    · show 0 ≤ ((s : ℂ) * x).im
      have : 0 < x.im := hx.1
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      positivity
  have hcS : ∀ z ∈ ballH R₁, Φ z (ballH (s * B))ᶜ = 0 := fun z hz => (hfacts z hz).1
  have hcP : ∀ z ∈ ballH R₁, ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂Φ z ≤
      ENNReal.ofReal (C * s⁻¹ ^ (1 / 3 : ℝ) / (1 / 3)) := fun z hz y =>
    Thm18Asm.G1RC.frostman_pot_le (hfacts z hz).2 (by norm_num) (by positivity) y
  have hw' : w ∈ ballH R₁ := ⟨by rw [mem_closedBall, dist_zero_right]; linarith, hw⟩
  have hmem : ∀ u : ℂ, q5 t u s ρ ∈ {q : Fin 5 → ℝ | 0 < q 3 ∧ 0 < q 4} := fun u => ⟨hs, hρ⟩
  have hYc' : ∀ ω, ContinuousOn (fun u => Y (q5 t u s ρ) ω - Y (q5 t w s ρ) ω) Hbar :=
    fun ω => (((hYc ω).comp_continuous (continuous_q5_fst t s ρ) hmem).sub
      continuous_const).continuousOn
  have hY : ∀ u ∈ Hbar, (fun ω => Y (q5 t u s ρ) ω - Y (q5 t w s ρ) ω) =ᵐ[P]
      fun ω => X ω (Φ u) - X ω (Φ w) := by
    intro u hu
    filter_upwards [hYeq _ (hmem u), hYeq _ (hmem w)] with ω h1 h2
    rw [h1, h2, nu5_q5 hW hW0 ht hu s hρ, nu5_q5 hW hW0 ht hw s hρ]
    rfl
  have hF := CoordReg.integral_kernelAvg_ae_eq_bind hX Φ (K' := ballH R₁) (R := s * B)
    ENNReal.ofReal_ne_top hcS hcP hw' hYc' hY (foldedCircle w r) (isCompact_ballH R₁)
    inter_subset_right subset_rfl (foldedCircle_support hr.le le_rfl)
  filter_upwards [hF, hYeq _ (hmem w)] with ω h1 h2
  have hint : Integrable (fun u => Y (q5 t u s ρ) ω) (foldedCircle w r) :=
    RegClosure.integrable_fc ((hYc ω).comp_continuous (continuous_q5_fst t s ρ)
      hmem).continuousOn w hr.le
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul,
    measure_univ, one_smul] at h1
  rw [nu5_q5 hW hW0 ht hw s hρ] at h2
  have e : X ω (Φ w) = X ω ((foldedCircle w ρ).map (dmap W t s)) := rfl
  linarith

/-- **The commutation identity for the dilated modification.** -/
theorem ae_comm_Y5 [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    {Y : (Fin 5 → ℝ) → Ω → ℝ}
    (hYc : ∀ ω, ContinuousOn (fun q => Y q ω) {q | 0 < q 3 ∧ 0 < q 4})
    (hYeq : ∀ q ∈ {q : Fin 5 → ℝ | 0 < q 3 ∧ 0 < q 4},
      (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (nu5 W T q))
    {t : ℝ} (ht : t ∈ Icc 0 T) {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : w ∈ Hbar) {r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∫ u, Y (q5 t u s ρ) ω ∂foldedCircle w r =
      ∫ v, Y (q5 t v s r) ω ∂foldedCircle w ρ := by
  filter_upwards [ae_integral_Y5_eq_bind hX hW hW0 hYc hYeq ht hs hw hr hρ,
    ae_integral_Y5_eq_bind hX hW hW0 hYc hYeq ht hs hw hρ hr] with ω h1 h2
  rw [h1, h2, CoordReg.pushKernel_bind_comm]

end ASep
end QuantumZipper
