import QuantumZipper.Proofs.Thm18.G1RCCircle

/-!
# G1-RC, part 4: circle commutation of the pushed-circle process, for all scales at once

For the process `V(d, r, s)` of `G1RC.exists_pushed_limit` (G1RCCircle.lean), a continuous
modification of `X((s ψ)_* fc(d, r))`, the smoothing symmetry needed for a regular-sample witness
holds almost surely **simultaneously for all scales `s > 0`** (`G1RC.ae_comm_pushed`):

  `∫ V(u, ρ, s) dfc(w, r)(u) = ∫ V(v, r, s) dfc(w, ρ)(v)` for all `w ∈ Hbar`, `r, ρ, s > 0`.

Proof (as `G1Kolm.exists_modification_map`, with the extra parameter `s`): for fixed parameters
both sides are a.s. `X(fc(w, r) ⋆ (sψ)_* fc(·, ρ)) = X(fc(w, ρ) ⋆ (sψ)_* fc(·, r))` by stochastic
Fubini (`CoordReg.integral_kernelAvg_ae_eq_bind`) and the commutation of folded-circle
convolutions (`CoordReg.pushKernel_bind_comm`); then a countable dense set of parameters and
continuity of both sides. The support/potential bounds of the kernels come from the `t = 0`
face of `PushFamBounds`. Source: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1;
the density step is an own elementary argument (as in `CoordRegRC2.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open WedgeTK CircleFubini CoordReg KolmD

theorem snoc_qOf_mem_box {z : ℂ} {ρ s : ℝ} {N : ℕ} (hz : ‖z‖ ≤ N) (hρ : |Real.log ρ| ≤ N)
    (hs : |Real.log s| ≤ N) : (Fin.snoc (qOf z ρ s) 0 : Fin 5 → ℝ) ∈ boxD (d := 5) N := by
  intro i
  fin_cases i
  · simpa [qOf, Fin.snoc] using (Complex.abs_re_le_norm z).trans hz
  · simpa [qOf, Fin.snoc] using (Complex.abs_im_le_norm z).trans hz
  · exact hρ
  · exact hs
  · simp [Fin.snoc]

theorem smoothFam_qOf_eq {ψ : ℂ → ℂ} (hψm : Measurable ψ) (z : ℂ) {ρ s : ℝ} (hρ : 0 < ρ)
    (hs : 0 < s) (hf : Measurable fun u => (s : ℂ) * ψ u) :
    smoothFam circM (pushPhi ψ) (Fin.snoc (qOf z ρ s) 0 : Fin 5 → ℝ) =
      pushKernel (fun u => (s : ℂ) * ψ u) hf ρ z := by
  rw [smoothFam_snoc_zero, pushKernel_apply, map_foldedCircle_eq ψ hψm z hρ hs]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- Stochastic Fubini for the pushed kernel at a fixed scale. -/
theorem ae_integral_V_eq_bind {ψ : ℂ → ℂ} (hψm : Measurable ψ) {β : ℝ}
    (hB : PushFamBounds ψ β) (hX : IsFreeGFFModConstH X P) {V : ℂ × ℝ × ℝ → Ω → ℝ}
    (hVc : ∀ ω, ContinuousOn (fun p => V p ω) (univ ×ˢ Ioi 0 ×ˢ Ioi 0))
    (hVV : ∀ (d : ℂ) (r s : ℝ), 0 < r → 0 < s → (fun ω => V (d, r, s) ω) =ᵐ[P]
      fun ω => X ω ((foldedCircle d r).map fun z => (s : ℂ) * ψ z))
    {w : ℂ} (hw : w ∈ Hbar) {r ρ s : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hs : 0 < s) :
    ∀ᵐ ω ∂P, ∫ u, V (u, ρ, s) ω ∂foldedCircle w r =
      X ω ((foldedCircle w r).bind
        (pushKernel (fun u => (s : ℂ) * ψ u) (measurable_const.mul hψm) ρ)) := by
  set f : ℂ → ℂ := fun u => (s : ℂ) * ψ u with hf_def
  have hf : Measurable f := measurable_const.mul hψm
  set R₁ := ‖w‖ + r with hR₁
  obtain ⟨N, hN⟩ := exists_nat_ge (max R₁ (max |Real.log ρ| |Real.log s|))
  obtain ⟨⟨Bd, hBd⟩, ⟨C, hCt, hC⟩, -⟩ := hB.2 N
  have hbox : ∀ z ∈ ballH R₁, (Fin.snoc (qOf z ρ s) 0 : Fin 5 → ℝ) ∈ boxD (d := 5) N := by
    intro z hz
    have hz' : ‖z‖ ≤ R₁ := by have := hz.1; rwa [mem_closedBall, dist_zero_right] at this
    exact snoc_qOf_mem_box (hz'.trans ((le_max_left _ _).trans hN))
      ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
      ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hcS : ∀ z ∈ ballH R₁, pushKernel f hf ρ z (ballH Bd)ᶜ = 0 := fun z hz => by
    rw [← smoothFam_qOf_eq hψm z hρ hs hf]; exact hBd _ (hbox z hz)
  have hcP : ∀ z ∈ ballH R₁, ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖)
      ∂(pushKernel f hf ρ z) ≤ C := fun z hz y => by
    rw [← smoothFam_qOf_eq hψm z hρ hs hf]; exact hC _ (hbox z hz) y
  have hslice : ∀ ω, ContinuousOn (fun u => V (u, ρ, s) ω) Hbar := fun ω =>
    (hVc ω).comp (continuous_id.prodMk continuous_const).continuousOn
      fun u _ => ⟨mem_univ _, hρ, hs⟩
  have hYc : ∀ ω, ContinuousOn (fun u => V (u, ρ, s) ω - V (w, ρ, s) ω) Hbar := fun ω =>
    (hslice ω).sub continuousOn_const
  have hY : ∀ u ∈ Hbar, (fun ω => V (u, ρ, s) ω - V (w, ρ, s) ω) =ᵐ[P]
      fun ω => X ω (pushKernel f hf ρ u) - X ω (pushKernel f hf ρ w) := by
    intro u _
    filter_upwards [hVV u ρ s hρ hs, hVV w ρ s hρ hs] with ω h1 h2
    rw [h1, h2]; rfl
  have hw' : w ∈ ballH R₁ := ⟨by rw [mem_closedBall, dist_zero_right]; linarith, hw⟩
  have hF := integral_kernelAvg_ae_eq_bind hX (pushKernel f hf ρ) (K' := ballH R₁) (R := Bd)
    hCt hcS hcP hw' hYc hY (foldedCircle w r) (isCompact_ballH R₁) inter_subset_right
    subset_rfl (foldedCircle_support hr.le le_rfl)
  filter_upwards [hF, hVV w ρ s hρ hs] with ω h1 h2
  have h2' : V (w, ρ, s) ω = X ω (pushKernel f hf ρ w) := h2
  have hint : Integrable (fun u => V (u, ρ, s) ω) (foldedCircle w r) :=
    RegClosure.integrable_fc (hslice ω) w hr.le
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul,
    measure_univ, one_smul] at h1
  linarith

/-- **Circle commutation for all scales at once.** -/
theorem ae_comm_pushed {ψ : ℂ → ℂ} (hψm : Measurable ψ) {β : ℝ}
    (hB : PushFamBounds ψ β) (hX : IsFreeGFFModConstH X P) {V : ℂ × ℝ × ℝ → Ω → ℝ}
    (hVc : ∀ ω, ContinuousOn (fun p => V p ω) (univ ×ˢ Ioi 0 ×ˢ Ioi 0))
    (hVV : ∀ (d : ℂ) (r s : ℝ), 0 < r → 0 < s → (fun ω => V (d, r, s) ω) =ᵐ[P]
      fun ω => X ω ((foldedCircle d r).map fun z => (s : ℂ) * ψ z)) :
    ∀ᵐ ω ∂P, ∀ w ∈ Hbar, ∀ r ρ s : ℝ, 0 < r → 0 < ρ → 0 < s →
      ∫ u, V (u, ρ, s) ω ∂foldedCircle w r = ∫ v, V (v, r, s) ω ∂foldedCircle w ρ := by
  set S4 : Set (((ℂ × ℝ) × ℝ) × ℝ) := ((Hbar ×ˢ Ioi 0) ×ˢ Ioi 0) ×ˢ Ioi 0 with hS4
  have hpt : ∀ p ∈ S4, ∀ᵐ ω ∂P,
      ∫ u, V (u, p.1.2, p.2) ω ∂foldedCircle p.1.1.1 p.1.1.2 =
        ∫ v, V (v, p.1.1.2, p.2) ω ∂foldedCircle p.1.1.1 p.1.2 := by
    rintro ⟨⟨⟨w, r⟩, ρ⟩, s⟩ ⟨⟨⟨hw, hr⟩, hρ⟩, hs⟩
    simp only [mem_Ioi] at hr hρ hs
    filter_upwards [ae_integral_V_eq_bind hψm hB hX hVc hVV hw hr hρ hs,
      ae_integral_V_eq_bind hψm hB hX hVc hVV hw hρ hr hs] with ω h1 h2
    show ∫ u, V (u, ρ, s) ω ∂foldedCircle w r = ∫ v, V (v, r, s) ω ∂foldedCircle w ρ
    rw [h1, h2, pushKernel_bind_comm]
  obtain ⟨Dn, hDc, hDS, hSD⟩ := TopologicalSpace.exists_countable_dense_subset S4
  have hall : ∀ᵐ ω ∂P, ∀ p ∈ Dn,
      ∫ u, V (u, p.1.2, p.2) ω ∂foldedCircle p.1.1.1 p.1.1.2 =
        ∫ v, V (v, p.1.1.2, p.2) ω ∂foldedCircle p.1.1.1 p.1.2 :=
    (eventually_countable_ball hDc).2 fun p hp => hpt p (hDS hp)
  filter_upwards [hall] with ω hD
  have hL : ContinuousOn (fun p : ((ℂ × ℝ) × ℝ) × ℝ =>
      ∫ u, V (u, p.1.2, p.2) ω ∂foldedCircle p.1.1.1 p.1.1.2) S4 := by
    refine RegClosure.continuousOn_integral_fc (P := ((ℂ × ℝ) × ℝ) × ℝ)
      (H := fun p u => V (u, p.1.2, p.2) ω) (c := fun p => p.1.1.1) (r := fun p => p.1.1.2)
      ?_ (by fun_prop) (by fun_prop)
    refine (hVc ω).comp (by fun_prop : Continuous fun q : (((ℂ × ℝ) × ℝ) × ℝ) × ℂ =>
      (q.2, q.1.1.2, q.1.2)).continuousOn fun q hq => ⟨mem_univ _, hq.1.1.2, hq.1.2⟩
  have hR : ContinuousOn (fun p : ((ℂ × ℝ) × ℝ) × ℝ =>
      ∫ v, V (v, p.1.1.2, p.2) ω ∂foldedCircle p.1.1.1 p.1.2) S4 := by
    refine RegClosure.continuousOn_integral_fc (P := ((ℂ × ℝ) × ℝ) × ℝ)
      (H := fun p u => V (u, p.1.1.2, p.2) ω) (c := fun p => p.1.1.1) (r := fun p => p.1.2)
      ?_ (by fun_prop) (by fun_prop)
    refine (hVc ω).comp (by fun_prop : Continuous fun q : (((ℂ × ℝ) × ℝ) × ℝ) × ℂ =>
      (q.2, q.1.1.1.2, q.1.2)).continuousOn fun q hq => ⟨mem_univ _, hq.1.1.1.2, hq.1.2⟩
  have hEq := Set.EqOn.of_subset_closure (fun p hp => hD p hp) hL hR hDS hSD
  intro w hw r ρ s hr hρ hs
  exact hEq (show (((w, r), ρ), s) ∈ S4 from ⟨⟨⟨hw, hr⟩, hρ⟩, hs⟩)

end G1RC
end Thm18Asm
end QuantumZipper
