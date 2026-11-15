/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37Witness
import InteractingSLE.Spec.Sec7.Aux119Reflect
import InteractingSLE.Spec.Supplement.R6RefPhase
import InteractingSLE.Spec.Sec5.Heights

/-!
# Aux. lemma 37 at one rational witness: the branch relation and the pathwise exclusion

Packet PROVE-STRIPSYS36, item (BR). Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L130–L134,
p. 199): "Let `L_f, L_c` be the inherited logarithmic derivatives of the own-flow and counterflow coordinates just used
[…]. Each transition from either own coordinate to `Φ` takes the same incident collar to the upper half-plane. It
extends across a smaller open real interval by Schwarz reflection and has positive derivative there. Thus on that
interval `Im(L_E − L_f) = 2πk_f` and `Im(L_E − L_c) = 2πk_c`, for integers `k_f, k_c` fixed by the inherited
branches."

* **`exists_int_tendsto_im_sub_of_transition`** (BR, deterministic): let `φ_f`, `φ_c` be two coordinates on an open
  set `D` with derivative logarithms `L_f`, `L_c`, and `g` a continuous inverse of `φ_f` on the upper half-disc
  `ℍ ∩ B(x, ρ)` around a real point `x` (with values in `D`). If the transition `φ_c ∘ g` is conformal on the
  half-disc with real boundary values on its diameter (`R16.IsRealBoundaryConformal`: the collar goes to the upper
  half-plane in both coordinates), then along every approach `F` inside `D` on which `φ_f → x` from `ℍ`, the branch
  `Im(L_c − L_f)` tends to `2πk` for one integer `k`. This is the comparison of the two own coordinates directly (the
  source's `k = k_c − k_f` through the intermediate chart `Φ`): Schwarz reflection of the transition, its positive
  derivative on the diameter (`R16.IsRealBoundaryConformal.deriv_schwarzReflect_pos`), and the integer lift of
  `Aux119.exists_int_tendsto_im_of_reflect`.
* **`false_of_flat_germs`** (pathwise, (PFI2)–(PFI4)): two means `M_r`, `M_s` that agree along the approach (the flat
  clock), with the flow-side germ `ελ − θχ` for `M_r` in the own-flow coordinate and the counterflow-side germ
  `ελ′ − πχ` for `M_s` in the counterflow coordinate, and the branch relation, are contradictory for `θ` in the
  side-dependent range of `Aux37Witness.phase_ne_of_side`.
* **`false_of_flat_germs_strip`**: the same with the strip parameters `λ = λ(κ)`, `λ′ = λ(16/κ)`, `χ = χ(κ)`,
  `0 < κ < 4`.

No Theorem 1.2/1.3 (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open QuantumZipper (H Hbar chiC)
open QuantumZipper.CA (schwarzReflect)
open scoped Real

namespace InteractingSLE.Sec7.Aux37Germ

/-! ### The branch relation -/

section Branch

variable {φf φc Lf Lc g : ℂ → ℂ} {D : Set ℂ} {x ρ : ℝ}

/-- A coordinate with a derivative logarithm on an open set is holomorphic there (its derivative `exp L` never
vanishes, so it is not the junk value `0`). -/
theorem differentiableAt_of_isDerivLog {φ L : ℂ → ℂ} (hL : IsDerivLog φ L D) {z : ℂ} (hz : z ∈ D) :
    DifferentiableAt ℂ φ z := by
  by_contra hnd
  have h0 := deriv_zero_of_not_differentiableAt hnd
  rw [← hL.2 z hz] at h0
  exact Complex.exp_ne_zero _ h0

/-- **The derivative of the transition in the inverse coordinate**: if `g` inverts `φ_f` near `g w` and `φ_c = ψ ∘ φ_f`
there (`ψ = φ_c ∘ g`), then `exp (L_c − L_f)(g w) = ψ′(w)`. -/
theorem exp_sub_eq_deriv_transition (hD : IsOpen D) (hLf : IsDerivLog φf Lf D) (hLc : IsDerivLog φc Lc D)
    (hB : IsOpen (H ∩ ball (x : ℂ) ρ)) (hg : MapsTo g (H ∩ ball (x : ℂ) ρ) D)
    (hfg : ∀ w ∈ H ∩ ball (x : ℂ) ρ, φf (g w) = w)
    (hgf : ∀ z ∈ D, φf z ∈ H ∩ ball (x : ℂ) ρ → g (φf z) = z)
    (hψ : DifferentiableOn ℂ (φc ∘ g) (H ∩ ball (x : ℂ) ρ)) {w : ℂ} (hw : w ∈ H ∩ ball (x : ℂ) ρ) :
    exp (Lc (g w) - Lf (g w)) = deriv (φc ∘ g) w := by
  set z := g w with hzdef
  have hzD : z ∈ D := hg hw
  have hfz : φf z = w := hfg w hw
  have hdf : DifferentiableAt ℂ φf z := differentiableAt_of_isDerivLog hLf hzD
  have hdψ : DifferentiableAt ℂ (φc ∘ g) (φf z) := by
    rw [hfz]
    exact hψ.differentiableAt (hB.mem_nhds hw)
  -- `φ_c = (φ_c ∘ g) ∘ φ_f` near `z`
  have hN : ∀ᶠ z' in 𝓝 z, z' ∈ D ∧ φf z' ∈ H ∩ ball (x : ℂ) ρ := by
    have h1 : ∀ᶠ z' in 𝓝 z, z' ∈ D := hD.mem_nhds hzD
    have h2 : ∀ᶠ z' in 𝓝 z, φf z' ∈ H ∩ ball (x : ℂ) ρ :=
      hdf.continuousAt.preimage_mem_nhds (hB.mem_nhds (by rw [hfz]; exact hw))
    exact h1.and h2
  have heq : φc =ᶠ[𝓝 z] (φc ∘ g) ∘ φf := by
    filter_upwards [hN] with z' hz'
    simp only [Function.comp_apply, hgf z' hz'.1 hz'.2]
  have hchain : deriv φc z = deriv (φc ∘ g) (φf z) * deriv φf z := by
    rw [heq.deriv_eq]
    exact deriv_comp z hdψ hdf
  have hne : deriv φf z ≠ 0 := by rw [← hLf.2 z hzD]; exact Complex.exp_ne_zero _
  rw [Complex.exp_sub, hLf.2 z hzD, hLc.2 z hzD, hchain, hfz, mul_div_assoc, div_self hne, mul_one]

/-- **(BR) The branch relation of two coordinates of one collar** (Aux. lemma 37, p. 199): if the transition `φ_c ∘ g`
from the own-flow coordinate `φ_f` (continuous inverse `g` on the upper half-disc `ℍ ∩ B(x, ρ)`, values in `D`) to the
counterflow coordinate `φ_c` is conformal on the half-disc with real boundary values on its diameter, then along every
approach `F` inside `D` on which `φ_f → x` from `ℍ`, `Im(L_c − L_f) → 2πk` for one integer `k`. -/
theorem exists_int_tendsto_im_sub_of_transition (hD : IsOpen D) (hLf : IsDerivLog φf Lf D)
    (hLc : IsDerivLog φc Lc D) (hρ : 0 < ρ) (hg : MapsTo g (H ∩ ball (x : ℂ) ρ) D)
    (hgc : ContinuousOn g (H ∩ ball (x : ℂ) ρ)) (hfg : ∀ w ∈ H ∩ ball (x : ℂ) ρ, φf (g w) = w)
    (hgf : ∀ z ∈ D, φf z ∈ H ∩ ball (x : ℂ) ρ → g (φf z) = z)
    (hψ : R16.IsRealBoundaryConformal (φc ∘ g) x ρ) {F : Filter ℂ} (hF : Tendsto φf F (𝓝[H] (x : ℂ)))
    (hFD : ∀ᶠ z in F, z ∈ D) :
    ∃ k : ℤ, Tendsto (fun z => (Lc z - Lf z).im) F (𝓝 (2 * π * k)) := by
  have hB : IsOpen (H ∩ ball (x : ℂ) ρ) := QuantumZipper.isOpen_H.inter isOpen_ball
  set Φ : ℂ → ℂ := deriv (schwarzReflect (φc ∘ g)) with hΦdef
  have hR := hψ.differentiableOn_schwarzReflect
  have hΦc : ContinuousOn Φ (ball (x : ℂ) ρ) := (hR.deriv isOpen_ball).continuousOn
  have hxb : ((x : ℝ) : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  obtain ⟨hΦim, hΦre⟩ := hψ.deriv_schwarzReflect_pos hxb
  -- on the half-disc the reflected map is the transition itself
  have hΦeq : ∀ w ∈ H ∩ ball (x : ℂ) ρ, Φ w = deriv (φc ∘ g) w := by
    intro w hw
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hB.mem_nhds hw] with w' hw'
    have hw'0 : 0 ≤ w'.im := le_of_lt hw'.1
    simp only [schwarzReflect, hw'0, ↓reduceIte]
  set Λ : ℂ → ℂ := fun w => Lc (g w) - Lf (g w) with hΛdef
  have hΛc : ContinuousOn Λ (ball (x : ℂ) ρ ∩ H) := by
    rw [inter_comm]
    exact (hLc.1.continuousOn.comp hgc hg).sub (hLf.1.continuousOn.comp hgc hg)
  have hexp : ∀ w ∈ ball (x : ℂ) ρ ∩ H, exp (Λ w) = Φ w := by
    intro w hw
    have hw' : w ∈ H ∩ ball (x : ℂ) ρ := ⟨hw.2, hw.1⟩
    rw [hΦeq w hw']
    exact exp_sub_eq_deriv_transition hD hLf hLc hB hg hfg hgf hψ.1 hw'
  obtain ⟨k, hk⟩ := Aux119.exists_int_tendsto_im_of_reflect hρ hΦc hΦre hΦim hΛc hexp
  refine ⟨k, (hk.comp hF).congr' ?_⟩
  have hFB : ∀ᶠ z in F, φf z ∈ H ∩ ball (x : ℂ) ρ := by
    have h1 : ∀ᶠ z in F, φf z ∈ H := hF (self_mem_nhdsWithin)
    have h2 : ∀ᶠ z in F, φf z ∈ ball (x : ℂ) ρ :=
      hF (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hρ))
    exact h1.and h2
  filter_upwards [hFB, hFD] with z hzB hzD
  simp only [Function.comp_apply, hΛdef, hgf z hzD hzB]

end Branch

/-! ### The pathwise exclusion -/

section Exclusion

/-- **(PFI2)–(PFI4) with the flat clock** (Aux. lemma 37, pp. 199–200): along one approach `F`, two means `M_r`, `M_s`
that agree eventually (the unchanged central mean), the flow-side germ `M_r + u₀ + χ Im L_f → ελ − θχ`, the
counterflow-side germ `M_s + u₀ + χ Im L_c → ελ′ − πχ`, and the branch relation `Im(L_c − L_f) → 2πk` are
contradictory when `χ > 0`, `λ − λ′ = πχ/2` and `θ` lies in the side-dependent range. -/
theorem false_of_flat_germs {F : Filter ℂ} [F.NeBot] {Mr Ms u₀ : ℂ → ℝ} {Lf Lc : ℂ → ℂ}
    {χ lam lam' ε θ : ℝ} {k : ℤ} (hχ : 0 < χ) (hlam : lam - lam' = π * χ / 2)
    (hside : (ε = 1 ∧ θ ∈ Ioc (-(π / 2)) (π / 2)) ∨ (ε = -1 ∧ θ ∈ Ico (-(π / 2)) (π / 2)))
    (hFC : Mr =ᶠ[F] Ms)
    (hG1 : Tendsto (fun z => Mr z + u₀ z + χ * (Lf z).im) F (𝓝 (ε * lam - θ * χ)))
    (hG2 : Tendsto (fun z => Ms z + u₀ z + χ * (Lc z).im) F (𝓝 (ε * lam' - π * χ)))
    (hBR : Tendsto (fun z => (Lc z - Lf z).im) F (𝓝 (2 * π * k))) : False := by
  have hc : Tendsto (fun z => (Mr z + u₀ z) + χ * (Lc z).im) F (𝓝 (ε * lam' - π * χ)) := by
    refine hG2.congr' ?_
    filter_upwards [hFC] with z hz
    rw [hz]
  have hk : Tendsto (fun z => (Lf z).im - (Lc z).im) F (𝓝 (2 * π * ((-k : ℤ) : ℝ))) := by
    have h := hBR.neg
    rw [show -(2 * π * (k : ℝ)) = 2 * π * ((-k : ℤ) : ℝ) by push_cast; ring] at h
    refine h.congr fun z => ?_
    simp only [Complex.sub_im]
    ring
  exact Aux37Witness.false_of_side_germs_of_side (M := fun z => Mr z + u₀ z) (Lf := fun z => (Lf z).im)
    (Lc := fun z => (Lc z).im) hχ hlam hside hG1 hc hk

/-- `λ(κ) − λ(16/κ) = πχ(κ)/2`. -/
theorem sleLambda_sub_sixteen_div {κ : ℝ} (hκ : 0 < κ) :
    sleLambda κ - sleLambda (16 / κ) = π * chiC κ / 2 := by
  rw [Sec4.sleLambda_sixteen_div_eq_sub hκ]
  ring

/-- **The pathwise exclusion with the strip parameters** (`λ = λ(κ)`, `λ′ = λ(16/κ)`, `χ = χ(κ)`, `0 < κ < 4`). -/
theorem false_of_flat_germs_strip {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {F : Filter ℂ} [F.NeBot]
    {Mr Ms u₀ : ℂ → ℝ} {Lf Lc : ℂ → ℂ} {ε θ : ℝ} {k : ℤ}
    (hside : (ε = 1 ∧ θ ∈ Ioc (-(π / 2)) (π / 2)) ∨ (ε = -1 ∧ θ ∈ Ico (-(π / 2)) (π / 2)))
    (hFC : Mr =ᶠ[F] Ms)
    (hG1 : Tendsto (fun z => Mr z + u₀ z + chiC κ * (Lf z).im) F (𝓝 (ε * sleLambda κ - θ * chiC κ)))
    (hG2 : Tendsto (fun z => Ms z + u₀ z + chiC κ * (Lc z).im) F
      (𝓝 (ε * sleLambda (16 / κ) - π * chiC κ)))
    (hBR : Tendsto (fun z => (Lc z - Lf z).im) F (𝓝 (2 * π * k))) : False :=
  false_of_flat_germs (Sec4.chiC_pos hκ hκ4) (sleLambda_sub_sixteen_div hκ) hside hFC hG1 hG2 hBR

end Exclusion

end InteractingSLE.Sec7.Aux37Germ
