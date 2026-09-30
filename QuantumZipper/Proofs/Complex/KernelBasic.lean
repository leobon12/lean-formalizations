import QuantumZipper.Proofs.Complex.KoebeDistortion
import QuantumZipper.Proofs.Complex.BasicsAutomorphisms
import Mathlib.Analysis.Complex.Order

/-!
# Carathéodory kernel convergence: definition and basic tools (EXT-CA KT1, D7)

* `KernelConvergesTo G D w₀`: Pommerenke's kernel convergence `G n → D` with respect to `w₀`,
  conditions (i)–(ii) of Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §1.4, p. 13.
* `infDist_compl_le_schwarzPick`: for `F` injective holomorphic on `𝔻` and `z ∈ 𝔻`,
  `dist (F z, ∂F(𝔻)) ≤ (1 − |z|²) |F'(z)|` (the upper half of Pommerenke, *loc. cit.*,
  Cor. 1.4, p. 9, used in the proof of Thm 1.8, p. 14). Proof: Schwarz's lemma for
  `φ_z ∘ F⁻¹` on the disk `D(F z, dist)`, with `φ_z` the disk automorphism `z ↦ 0`
  (`Koebe.radius_mul_norm_deriv_le_of_ball_subset_image`).
* `eqOn_of_image_eq_of_deriv_pos`: uniqueness of the normalized Riemann map
  (`f(0) = g(0)`, `f'(0), g'(0) > 0`, same image), via `exists_rotation_of_bijOn_ball`
  (Ahlfors, *Complex Analysis*, 3rd ed., Ch. 6 §1.1, p. 230, uniqueness part).
-/

noncomputable section

open Set Metric Filter Topology Complex
open scoped ComplexConjugate ComplexOrder

namespace QuantumZipper.CA.Kernel

/-- **Kernel convergence** (Pommerenke, *Boundary Behaviour of Conformal Maps*, §1.4, p. 13):
`G n → D` as `n → ∞` with respect to `w₀` iff
(i) either `D = {w₀}`, or `D` is a domain `≠ ℂ` with `w₀ ∈ D` such that some neighbourhood of
every `w ∈ D` lies in `G n` for large `n`; and
(ii) for `w ∈ ∂D` there exist `w_n ∈ ∂G_n` with `w_n → w`. -/
def KernelConvergesTo (G : ℕ → Set ℂ) (D : Set ℂ) (w₀ : ℂ) : Prop :=
  (D = {w₀} ∨ (IsOpen D ∧ IsConnected D ∧ D ≠ univ ∧ w₀ ∈ D ∧
      ∀ w ∈ D, ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ G n)) ∧
    ∀ w ∈ frontier D, ∃ u : ℕ → ℂ, (∀ n, u n ∈ frontier (G n)) ∧ Tendsto u atTop (𝓝 w)

theorem hasDerivAt_diskMobius_self {a : ℂ} (ha : ‖a‖ < 1) :
    HasDerivAt (diskMobius a) (1 / (1 - ((‖a‖ ^ 2 : ℝ) : ℂ))) a := by
  have hden : (1 : ℂ) - conj a * a ≠ 0 := diskMobius_denom_ne_zero ha ha.le
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 a := (hasDerivAt_id a).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => 1 - conj a * w) (-conj a) a := by
    simpa using ((hasDerivAt_id a).const_mul (conj a)).const_sub 1
  have h : HasDerivAt (fun w : ℂ => (w - a) / (1 - conj a * w))
      ((1 * (1 - conj a * a) - (a - a) * -conj a) / (1 - conj a * a) ^ 2) a := h1.div h2 hden
  have hca : conj a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; push_cast; rfl
  have he : (1 : ℂ) / (1 - ((‖a‖ ^ 2 : ℝ) : ℂ)) =
      (1 * (1 - conj a * a) - (a - a) * -conj a) / (1 - conj a * a) ^ 2 := by
    rw [← hca]
    field_simp
    ring
  rw [he]
  exact h

/-- Koebe's estimate, upper half, Schwarz–Pick form (Pommerenke, Cor. 1.4, p. 9):
`dist (F z, ℂ \ F(𝔻)) ≤ (1 − |z|²) |F'(z)|`. -/
theorem infDist_compl_le_schwarzPick {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    infDist (F z) (F '' ball 0 1)ᶜ ≤ (1 - ‖z‖ ^ 2) * ‖deriv F z‖ := by
  set R := infDist (F z) (F '' ball 0 1)ᶜ with hRdef
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hq : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rcases le_or_gt R 0 with hR | hR
  · exact hR.trans (by positivity)
  have hsub : ball (F z) R ⊆ F '' ball 0 1 := by
    intro w hw
    rw [mem_ball, dist_comm] at hw
    by_contra h
    exact notMem_of_dist_lt_infDist hw h
  have hψ : DifferentiableOn ℂ (diskMobius z) (ball 0 1) :=
    (differentiableOn_diskMobius hz1).mono ball_subset_closedBall
  have hmaps : MapsTo (diskMobius z) (ball 0 1) (closedBall (diskMobius z z) 1) := by
    intro w hw
    rw [diskMobius_self]
    exact ball_subset_closedBall (diskMobius_mem_ball hz1 hw)
  have key := Koebe.radius_mul_norm_deriv_le_of_ball_subset_image isOpen_ball hd hinj hz hψ
    hmaps hR hsub
  rw [(hasDerivAt_diskMobius_self hz1).deriv] at key
  have hc : (1 : ℂ) - ((‖z‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hc, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hq.le, one_mul,
    mul_one_div, div_le_iff₀ hq] at key
  linarith

/-- Positive complex numbers (in `ComplexOrder`) are positive reals. -/
theorem exists_ofReal_of_pos {z : ℂ} (hz : 0 < z) : ∃ a : ℝ, 0 < a ∧ z = a := by
  rw [Complex.pos_iff] at hz
  exact ⟨z.re, hz.1, Complex.ext (by simp) (by simp [← hz.2])⟩

/-- **Uniqueness of the normalized conformal map** onto a given domain. -/
theorem eqOn_of_image_eq_of_deriv_pos {f g : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f (ball 0 1)) (hfi : InjOn f (ball 0 1))
    (hgd : DifferentiableOn ℂ g (ball 0 1)) (hgi : InjOn g (ball 0 1))
    (him : f '' ball 0 1 = g '' ball 0 1) (h0 : f 0 = g 0)
    (hf' : 0 < deriv f 0) (hg' : 0 < deriv g 0) : EqOn f g (ball 0 1) := by
  set B : Set ℂ := ball 0 1 with hB
  set k := Function.invFunOn g B with hk
  have hfim : ∀ z ∈ B, f z ∈ g '' B := fun z hz => him ▸ mem_image_of_mem f hz
  have hkmem : ∀ z ∈ B, k (f z) ∈ B := fun z hz => Function.invFunOn_mem (hfim z hz)
  have hgk : ∀ z ∈ B, g (k (f z)) = f z := fun z hz => Function.invFunOn_eq (hfim z hz)
  have hkg : ∀ y ∈ B, k (g y) = y := fun y hy =>
    hgi (Function.invFunOn_mem ⟨y, hy, rfl⟩) hy (Function.invFunOn_eq ⟨y, hy, rfl⟩)
  set h : ℂ → ℂ := k ∘ f with hh
  have h0B : (0 : ℂ) ∈ B := mem_ball_self one_pos
  have hhd : DifferentiableOn ℂ h B := by
    intro z hz
    obtain ⟨z', hz', hfz⟩ := hfim z hz
    have hk' := Koebe.hasDerivAt_invFunOn_of_injOn isOpen_ball hgd hgi hz'
    rw [hfz] at hk'
    exact (hk'.differentiableAt.comp z
      (hfd.differentiableAt (isOpen_ball.mem_nhds hz))).differentiableWithinAt
  have hbij : BijOn h B B := by
    refine ⟨fun z hz => hkmem z hz, fun a ha b hb hab => ?_, fun y hy => ?_⟩
    · have := congrArg g hab
      simp only [hh, Function.comp_apply] at this
      rw [hgk a ha, hgk b hb] at this
      exact hfi ha hb this
    · obtain ⟨x, hx, hfx⟩ : g y ∈ f '' B := by rw [him]; exact ⟨y, hy, rfl⟩
      exact ⟨x, hx, by simp only [hh, Function.comp_apply, hfx, hkg y hy]⟩
  have hh0 : h 0 = 0 := by simp only [hh, Function.comp_apply, h0, hkg 0 h0B]
  obtain ⟨u, hu, hEq⟩ := exists_rotation_of_bijOn_ball hhd hbij hh0
  have hfg : ∀ z ∈ B, f z = g (u * z) := by
    intro z hz
    rw [← hgk z hz]
    exact congrArg g (hEq hz)
  have hev : f =ᶠ[𝓝 0] fun z => g (u * z) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds h0B) hfg
  have hgdiff : HasDerivAt g (deriv g 0) (u * 0) := by
    rw [mul_zero]; exact (hgd.differentiableAt (isOpen_ball.mem_nhds h0B)).hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => u * z) u 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul u
  have hcomp : HasDerivAt (fun z => g (u * z)) (deriv g 0 * u) 0 := hgdiff.comp (0 : ℂ) hlin
  have hd' : deriv f 0 = deriv g 0 * u := by rw [hev.deriv_eq]; exact hcomp.deriv
  obtain ⟨a, ha, hfa⟩ := exists_ofReal_of_pos hf'
  obtain ⟨b, hb, hgb⟩ := exists_ofReal_of_pos hg'
  have hu' : u = ((a / b : ℝ) : ℂ) := by
    rw [hfa, hgb] at hd'
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp
    linear_combination -hd'
  have hab : a / b = 1 := by
    rw [hu', Complex.norm_real, Real.norm_of_nonneg (div_pos ha hb).le] at hu
    exact hu
  rw [hab, Complex.ofReal_one] at hu'
  intro z hz
  rw [hfg z hz, hu', one_mul]

end QuantumZipper.CA.Kernel
