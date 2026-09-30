import QuantumZipper.Proofs.Complex.KernelTheorem
import QuantumZipper.Proofs.Complex.KernelChordBasic

/-!
# Kernel theorem for maps onto a fixed model domain (EXT-CA KT2, first step)

KT1 (`caratheodory_kernel_theorem`) is Pommerenke's kernel theorem for maps *from* the disk.
KT2 (DECISIONS D7) needs it for uniformizers `Φ_n : Ω_n → V` *onto* a fixed domain `V`
(`V = ℂ \ [0,∞)` for the doubled chord components, `w₀ = −1`, `Φ_n(−1) = −1`). Given one
conformal map `S : 𝔻 → V` with `S 0 = a`, `S'(0) > 0` (here `slitDiskMap`), the maps
`f_n := Φ_n⁻¹ ∘ S` satisfy the hypotheses of KT1, so `f_n → Φ⁻¹ ∘ S` locally uniformly in `𝔻`;
composing with `S⁻¹` gives `Φ_n⁻¹ → Φ⁻¹` locally uniformly on `V`
(`kernel_theorem_of_model`, `kernel_theorem_slitNeg`).

Source: Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Thm 1.8, p. 14 (via KT1).
The reduction by a fixed model map is an own elementary argument.
-/

noncomputable section

open Set Metric Filter Topology Complex Function
open scoped ComplexOrder

namespace QuantumZipper.CA.Kernel

section Model

variable {V : Set ℂ} {S : ℂ → ℂ} {a : ℂ}

/-- Positivity of `c⁻¹ * s` for positive `c, s`. -/
theorem inv_mul_pos_of_pos {c s : ℂ} (hc : 0 < c) (hs : 0 < s) : 0 < c⁻¹ * s := by
  obtain ⟨r, hr, rfl⟩ := exists_ofReal_of_pos hc
  obtain ⟨t, ht, rfl⟩ := exists_ofReal_of_pos hs
  rw [← ofReal_inv, ← ofReal_mul]
  exact zero_lt_real.2 (mul_pos (inv_pos.2 hr) ht)

/-- The pull-back `Φ⁻¹ ∘ S` of a uniformizer `Φ : Ω → V` is a normalized conformal map of the
disk onto `Ω`. -/
theorem modelPullback_props (hSd : DifferentiableOn ℂ S (ball 0 1))
    (hSi : InjOn S (ball 0 1)) (hSim : S '' ball 0 1 = V) (hS0 : S 0 = a)
    (hS' : 0 < deriv S 0) {Ω : Set ℂ} {Φ : ℂ → ℂ} {w₀ : ℂ} (hΩ : IsOpen Ω)
    (hΦd : DifferentiableOn ℂ Φ Ω) (hΦb : BijOn Φ Ω V) (hw₀ : w₀ ∈ Ω) (hΦ0 : Φ w₀ = a)
    (hΦ' : 0 < deriv Φ w₀) :
    DifferentiableOn ℂ (invFunOn Φ Ω ∘ S) (ball 0 1) ∧ InjOn (invFunOn Φ Ω ∘ S) (ball 0 1) ∧
      (invFunOn Φ Ω ∘ S) '' ball 0 1 = Ω ∧ (invFunOn Φ Ω ∘ S) 0 = w₀ ∧
      0 < deriv (invFunOn Φ Ω ∘ S) 0 := by
  have hinv : InvOn (invFunOn Φ Ω) Φ Ω V := hΦb.invOn_invFunOn
  have hbinv : BijOn (invFunOn Φ Ω) V Ω := hΦb.symm hinv.symm
  have hSmaps : MapsTo S (ball 0 1) V := fun w hw => hSim ▸ mem_image_of_mem S hw
  -- derivative of the inverse at a point `S w`
  have hder : ∀ w ∈ ball (0 : ℂ) 1, HasDerivAt (invFunOn Φ Ω)
      (deriv Φ (invFunOn Φ Ω (S w)))⁻¹ (S w) := fun w hw => by
    have hz := hbinv.mapsTo (hSmaps hw)
    have h := Koebe.hasDerivAt_invFunOn_of_injOn hΩ hΦd hΦb.injOn hz
    rwa [hinv.2 (hSmaps hw)] at h
  have hSD : ∀ w ∈ ball (0 : ℂ) 1, HasDerivAt S (deriv S w) w := fun w hw =>
    (hSd.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hinvw₀ : invFunOn Φ Ω a = w₀ := by rw [← hΦ0]; exact hinv.1 hw₀
  refine ⟨fun w hw => ((hder w hw).comp w (hSD w hw)).differentiableAt.differentiableWithinAt,
    hbinv.injOn.comp hSi hSmaps, ?_, by simp [hS0, hinvw₀], ?_⟩
  · rw [image_comp, hSim, hbinv.image_eq]
  · have h := (hder 0 h0).comp 0 (hSD 0 h0)
    rw [h.deriv, hS0, hinvw₀]
    exact inv_mul_pos_of_pos hΦ' hS'

/-- **Kernel theorem for uniformizers onto a model domain.** Let `S : 𝔻 → V` be conformal with
`S 0 = a`, `S'(0) > 0`. Let `Φ n : Ω n → V` and `Φ∞ : Ω∞ → V` be conformal bijections with
`Φ n w₀ = Φ∞ w₀ = a` and positive derivatives at `w₀`. If `Ω n → Ω∞` with respect to `w₀`
(kernel convergence), then the inverse maps converge locally uniformly on `V`. -/
theorem kernel_theorem_of_model (hSd : DifferentiableOn ℂ S (ball 0 1))
    (hSi : InjOn S (ball 0 1)) (hSim : S '' ball 0 1 = V) (hS0 : S 0 = a)
    (hS' : 0 < deriv S 0) {Ω : ℕ → Set ℂ} {Ωi : Set ℂ} {w₀ : ℂ} {Φ : ℕ → ℂ → ℂ}
    {Φi : ℂ → ℂ} (hΩ : ∀ n, IsOpen (Ω n)) (hΦd : ∀ n, DifferentiableOn ℂ (Φ n) (Ω n))
    (hΦb : ∀ n, BijOn (Φ n) (Ω n) V) (hw₀ : ∀ n, w₀ ∈ Ω n) (hΦ0 : ∀ n, Φ n w₀ = a)
    (hΦ' : ∀ n, 0 < deriv (Φ n) w₀) (hΩi : IsOpen Ωi) (hΦid : DifferentiableOn ℂ Φi Ωi)
    (hΦib : BijOn Φi Ωi V) (hw₀i : w₀ ∈ Ωi) (hΦi0 : Φi w₀ = a) (hΦi' : 0 < deriv Φi w₀)
    (hker : KernelConvergesTo Ω Ωi w₀) :
    TendstoLocallyUniformlyOn (fun n => invFunOn (Φ n) (Ω n)) (invFunOn Φi Ωi) atTop V := by
  have hP := fun n => modelPullback_props hSd hSi hSim hS0 hS' (hΩ n) (hΦd n) (hΦb n) (hw₀ n)
    (hΦ0 n) (hΦ' n)
  have hPi := modelPullback_props hSd hSi hSim hS0 hS' hΩi hΦid hΦib hw₀i hΦi0 hΦi'
  have hlim := caratheodory_kernel_theorem (fun n => (hP n).1) (fun n => (hP n).2.1)
    (fun n => (hP n).2.2.1) (fun n => (hP n).2.2.2.1) (fun n => (hP n).2.2.2.2) hPi.1 hPi.2.1
    hPi.2.2.1 hPi.2.2.2.1 hPi.2.2.2.2 hker
  -- transport by `S⁻¹ : V → 𝔻`
  have hVS : ∀ v ∈ V, ∃ w ∈ ball (0 : ℂ) 1, S w = v := fun v hv => by
    rw [← hSim] at hv; exact hv
  have hSinvMaps : MapsTo (invFunOn S (ball 0 1)) V (ball 0 1) := fun v hv =>
    invFunOn_mem (hVS v hv)
  have hSinvC : ContinuousOn (invFunOn S (ball 0 1)) V := fun v hv => by
    obtain ⟨w, hw, rfl⟩ := hVS v hv
    exact (Koebe.hasDerivAt_invFunOn_of_injOn isOpen_ball hSd hSi hw).continuousAt
      |>.continuousWithinAt
  have hSS : ∀ v ∈ V, S (invFunOn S (ball 0 1) v) = v := fun v hv => invFunOn_eq (hVS v hv)
  have h := hlim.comp (invFunOn S (ball 0 1)) hSinvMaps hSinvC
  refine (h.congr fun n v hv => ?_).congr_right fun v hv => ?_
  · simp only [comp_apply, hSS v hv]
  · simp only [comp_apply, hSS v hv]

/-- **KT2, analytic core.** Kernel theorem for uniformizers onto the slit plane `ℂ \ [0,∞)`
normalized at `w₀ ↦ −1` with positive derivative (the doubled-domain situation of D7). -/
theorem kernel_theorem_slitNeg {Ω : ℕ → Set ℂ} {Ωi : Set ℂ} {w₀ : ℂ} {Φ : ℕ → ℂ → ℂ}
    {Φi : ℂ → ℂ} (hΩ : ∀ n, IsOpen (Ω n)) (hΦd : ∀ n, DifferentiableOn ℂ (Φ n) (Ω n))
    (hΦb : ∀ n, BijOn (Φ n) (Ω n) slitNeg) (hw₀ : ∀ n, w₀ ∈ Ω n) (hΦ0 : ∀ n, Φ n w₀ = -1)
    (hΦ' : ∀ n, 0 < deriv (Φ n) w₀) (hΩi : IsOpen Ωi) (hΦid : DifferentiableOn ℂ Φi Ωi)
    (hΦib : BijOn Φi Ωi slitNeg) (hw₀i : w₀ ∈ Ωi) (hΦi0 : Φi w₀ = -1)
    (hΦi' : 0 < deriv Φi w₀) (hker : KernelConvergesTo Ω Ωi w₀) :
    TendstoLocallyUniformlyOn (fun n => invFunOn (Φ n) (Ω n)) (invFunOn Φi Ωi) atTop
      slitNeg :=
  kernel_theorem_of_model differentiableOn_slitDiskMap injOn_slitDiskMap image_slitDiskMap
    slitDiskMap_zero (by rw [deriv_slitDiskMap_zero]; norm_num) hΩ hΦd hΦb hw₀ hΦ0 hΦ' hΩi
    hΦid hΦib hw₀i hΦi0 hΦi' hker

end Model

end QuantumZipper.CA.Kernel
