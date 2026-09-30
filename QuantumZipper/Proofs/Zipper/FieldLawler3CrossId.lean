import QuantumZipper.Proofs.Zipper.FieldLawler3Cross
import QuantumZipper.Proofs.Zipper.FieldLawler2Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 3: the harmonic measure of a real interval in `ℍ` is `fl3IntHarm`

`fl3IntHarm c d = π⁻¹ arg((p − d)/(p − c))` satisfies `IsHarmMeas ℍ (c, d)` (`fl3_isHarmMeas`),
and every harmonic measure of `(c, d)` in `ℍ` equals it (`fl3_isHarmMeas_eq`, Lindelöf maximum
principle `fl2_harm_le_zero_off_finite` with the exceptional points `c, d`). Together with
`fl3_excR_symm` this identifies the fluxes of harmonic measures of real intervals in `ℍ`.
Own elementary proof.
-/

noncomputable section

open MeasureTheory Filter Set Complex Metric
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- The Möbius quotient `(p − d)/(p − c)`. -/
def fl3Q (c d : ℝ) (p : ℂ) : ℂ := (p - d) / (p - c)

theorem fl3IntHarm_eq_arg (c d : ℝ) (p : ℂ) : fl3IntHarm c d p = arg (fl3Q c d p) / π := by
  simp [fl3IntHarm, fl3IntF, fl3Q, Complex.log_im]

theorem fl3Q_im {c d : ℝ} (p : ℂ) : (fl3Q c d p).im = (d - c) * p.im / ‖p - c‖ ^ 2 := by
  rw [fl3Q, Complex.div_im, ← Complex.normSq_eq_norm_sq]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero, Complex.normSq_apply]
  field_simp
  ring

theorem fl3_sub_ne {c : ℝ} {p : ℂ} (hp : 0 < p.im) : p - c ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem fl3Q_mem_H {c d : ℝ} (hcd : c < d) {p : ℂ} (hp : 0 < p.im) : 0 < (fl3Q c d p).im := by
  rw [fl3Q_im]
  have : 0 < ‖p - c‖ := norm_pos_iff.2 (fl3_sub_ne hp)
  have : 0 < d - c := by linarith
  positivity

theorem fl3IntHarm_harm {c d : ℝ} (hcd : c < d) :
    InnerProductSpace.HarmonicOnNhd (fl3IntHarm c d) H := by
  intro z hz
  have hz' : 0 < z.im := hz
  have hF : AnalyticAt ℂ (fl3Q c d) z :=
    (analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) (fl3_sub_ne hz')
  have hsl : fl3Q c d z ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; exact (fl3Q_mem_H hcd hz').ne'
  have h := ((AnalyticAt.comp (g := log) (f := fl3Q c d) (analyticAt_clog hsl) hF).harmonicAt_im)
  have h2 := h.const_smul (c := (π⁻¹ : ℝ))
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 h2
  exact Eventually.of_forall fun w => by
    simp [fl3IntHarm, fl3IntF, fl3Q, Function.comp, div_eq_inv_mul, smul_eq_mul]

theorem fl3IntHarm_mem01 {c d : ℝ} (hcd : c < d) {p : ℂ} (hp : 0 < p.im) :
    0 ≤ fl3IntHarm c d p ∧ fl3IntHarm c d p ≤ 1 := by
  rw [fl3IntHarm_eq_arg]
  have hq := fl3Q_mem_H hcd hp
  refine ⟨div_nonneg (arg_nonneg_iff.2 hq.le) Real.pi_pos.le, ?_⟩
  rw [div_le_one Real.pi_pos]
  exact arg_le_pi _

theorem fl3Q_real {c d x : ℝ} : fl3Q c d (x : ℂ) = (((x - d) / (x - c) : ℝ) : ℂ) := by
  simp [fl3Q]

theorem fl3Q_contAt {c d x : ℝ} (hxc : x ≠ c) : ContinuousAt (fl3Q c d) (x : ℂ) := by
  have h : (x : ℂ) - c ≠ 0 := by
    rw [← ofReal_sub, ofReal_ne_zero, sub_ne_zero]; exact hxc
  exact (continuousAt_id.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const) h

/-- Boundary value `0` at real points outside `[c, d]`. -/
theorem fl3IntHarm_tendsto_zero {c d x : ℝ} (hcd : c < d) (hx : x < c ∨ d < x) :
    Tendsto (fl3IntHarm c d) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hxc : x ≠ c := by rcases hx with h | h <;> [exact h.ne; exact (hcd.trans h).ne']
  have hpos : 0 < (x - d) / (x - c) := by
    rcases hx with h | h
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    · exact div_pos (by linarith) (by linarith)
  have hmem : fl3Q c d (x : ℂ) ∈ slitPlane := by
    rw [fl3Q_real]; exact ofReal_mem_slitPlane.2 hpos
  have h1 : Tendsto (fun p => arg (fl3Q c d p)) (𝓝 (x : ℂ)) (𝓝 (arg (fl3Q c d x))) :=
    ((continuousAt_arg hmem).comp (fl3Q_contAt hxc)).tendsto
  rw [fl3Q_real, arg_ofReal_of_nonneg hpos.le] at h1
  have h2 := (h1.div_const π).mono_left (nhdsWithin_le_nhds (s := H))
  rw [zero_div] at h2
  refine h2.congr fun p => ?_
  rw [fl3IntHarm_eq_arg]

/-- Boundary value `1` at points of `(c, d)`. -/
theorem fl3IntHarm_tendsto_one {c d x : ℝ} (hcd : c < d) (hx : x ∈ Ioo c d) :
    Tendsto (fl3IntHarm c d) (𝓝[H] (x : ℂ)) (𝓝 1) := by
  have hneg : (x - d) / (x - c) < 0 := div_neg_of_neg_of_pos (by linarith [hx.2]) (by linarith [hx.1])
  have hq : Tendsto (fl3Q c d) (𝓝[H] (x : ℂ)) (𝓝[{z : ℂ | 0 ≤ z.im}] (fl3Q c d x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨((fl3Q_contAt hx.1.ne').tendsto).mono_left nhdsWithin_le_nhds,
      ?_⟩
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (fl3Q_mem_H hcd hp).le
  have ha := tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := fl3Q c d x) (by rw [fl3Q_real, ofReal_re]; exact hneg) (by rw [fl3Q_real, ofReal_im])
  have h2 := ((ha.comp hq).div_const π)
  rw [div_self Real.pi_pos.ne'] at h2
  refine h2.congr fun p => ?_
  rw [fl3IntHarm_eq_arg]; rfl

/-- Decay at `∞`. -/
theorem fl3IntHarm_tendsto_infty {c d : ℝ} :
    Tendsto (fl3IntHarm c d) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 0) := by
  have hinv : Tendsto (fun p : ℂ => (p - c)⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
    have := tendsto_inv₀_cobounded.comp (tendsto_add_const_cobounded (-(c : ℂ)))
    refine this.congr fun p => ?_
    simp [sub_eq_add_neg]
  have hq : Tendsto (fl3Q c d) (Bornology.cobounded ℂ) (𝓝 1) := by
    have h1 : Tendsto (fun p : ℂ => 1 - ((d : ℂ) - c) * (p - c)⁻¹) (Bornology.cobounded ℂ)
        (𝓝 (1 - ((d : ℂ) - c) * 0)) := tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
    rw [mul_zero, sub_zero] at h1
    refine h1.congr' ?_
    have hb : ∀ᶠ p : ℂ in Bornology.cobounded ℂ, p - c ≠ 0 := by
      have hs : Bornology.IsBounded ({(c : ℂ)} : Set ℂ) := Bornology.isBounded_singleton
      filter_upwards [Bornology.isBounded_def.1 hs] with p hp
      exact sub_ne_zero.2 hp
    filter_upwards [hb] with p hp
    rw [fl3Q]
    field_simp
    ring
  have h1 : Tendsto (fun p => arg (fl3Q c d p)) (Bornology.cobounded ℂ) (𝓝 (arg 1)) :=
    (continuousAt_arg (by simp [mem_slitPlane_iff])).tendsto.comp hq
  rw [arg_one] at h1
  have h2 := (h1.div_const π).mono_left (inf_le_left : Bornology.cobounded ℂ ⊓ 𝓟 H ≤ _)
  rw [zero_div] at h2
  refine h2.congr fun p => ?_
  rw [fl3IntHarm_eq_arg]

end FieldLawler
end QuantumZipper
