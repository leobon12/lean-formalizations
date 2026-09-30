import QuantumZipper.Proofs.Zipper.SWCoreA7Id
import QuantumZipper.Proofs.Zipper.SWCoreNA2Final

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A7 (2): the distortion bound along a Lipschitz family, fixed maps

From the finite-parameter primed area core `swcNA2I_primed` (decision D64) for a five-parameter
family `(t, v, Re z, Im z, α)` whose diagonal `(t, V t, Re z, Im z, 1)` carries the maps `Ψ t`
at centre `z` and radius factor `1`: almost surely, for every `η > 0`, eventually in `k`, for all
`t ∈ I` and `z ∈ K` (a set at positive distance inside the family rectangle),
`|pushErr γ x (Ψ t) k z| ≤ η`.

The pushed average is identified through `a7_pushErr_eq` (continuity of the pushed `evalReg`
in the centre, which is the second conjunct of the primed core). Own bookkeeping around
Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

/-- The open rectangle. -/
def a7Open (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ :=
  {w | x₁ < w.re ∧ w.re < x₂ ∧ y₁ < w.im ∧ w.im < y₂}

theorem isOpen_a7Open (x₁ x₂ y₁ y₂ : ℝ) : IsOpen (a7Open x₁ x₂ y₁ y₂) := by
  unfold a7Open
  refine (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

theorem a7Open_subset (x₁ x₂ y₁ y₂ : ℝ) : a7Open x₁ x₂ y₁ y₂ ⊆ rectC x₁ x₂ y₁ y₂ :=
  fun _ hw => ⟨⟨hw.1.le, hw.2.1.le⟩, ⟨hw.2.2.1.le, hw.2.2.2.le⟩⟩

/-- The diagonal parameter. -/
def a7Diag (V : ℝ → ℝ) (t : ℝ) (w : ℂ) : Fin 5 → ℝ := ![t, V t, w.re, w.im, 1]

theorem continuous_a7Diag (V : ℝ → ℝ) (t : ℝ) : Continuous (a7Diag V t) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [a7Diag] <;> fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **The distortion bound for a family with a Lipschitz diagonal** (fixed maps). -/
theorem a7_fixed_of_fam [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {F : (Fin 5 → ℝ) → ℂ → ℂ} {cf : (Fin 5 → ℝ) → ℂ} {af : (Fin 5 → ℝ) → ℝ}
    {x₁ x₂ y₁ y₂ ρ M m H : ℝ} (h : SwcNA2Unif F cf af x₁ x₂ y₁ y₂ ρ M m H)
    {Ψ : ℝ → ℂ → ℂ} {V : ℝ → ℝ} {I : Set ℝ} {K : Set ℂ}
    (hdiag : ∀ t ∈ I, ∀ w ∈ rectC x₁ x₂ y₁ y₂,
      F (a7Diag V t w) = Ψ t ∧ cf (a7Diag V t w) = w ∧ af (a7Diag V t w) = 1)
    (R : ℕ) (hR : ∀ t ∈ I, ∀ w ∈ rectC x₁ x₂ y₁ y₂, a7Diag V t w ∈ KolmD.boxD (d := 5) R)
    {δ : ℝ} (hδ : 0 < δ) (hK : ∀ z ∈ K, closedBall z δ ⊆ a7Open x₁ x₂ y₁ y₂) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ t ∈ I, ∀ z ∈ K,
      |pushErr γ (X ω) (Ψ t) k z| ≤ η := by
  obtain ⟨k₀, hae⟩ := swcNA2I_primed hX h
  filter_upwards [hae] with ω hω
  obtain ⟨-, hcont, herr⟩ := hω
  intro η hη
  have hrad : Tendsto radius atTop (𝓝 0) := by
    unfold radius
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsm : ∀ᶠ k in atTop, 2 * radius k ≤ δ :=
    hrad.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < δ / 2)) |>.mono fun k hk => by linarith
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 ((herr R η hη).and hsm)
  refine eventually_atTop.2 ⟨K₁ + k₀, fun k hk t ht z hz => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + k₀ := ⟨k - k₀, (Nat.sub_add_cancel (by omega)).symm⟩
  have hk' : K₁ ≤ k' := by omega
  obtain ⟨hE, hsmall⟩ := hK₁ k' hk'
  have hsmall' : 2 * radius (k' + k₀) ≤ δ := by
    have : radius (k' + k₀) ≤ radius k' := by
      unfold radius; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hzO : z ∈ a7Open x₁ x₂ y₁ y₂ := hK z hz (mem_closedBall_self hδ.le)
  have hzR : z ∈ rectC x₁ x₂ y₁ y₂ := a7Open_subset _ _ _ _ hzO
  obtain ⟨hF, hc, ha⟩ := hdiag t ht z hzR
  set r := radius (k' + k₀) with hr
  have hr0 : 0 < r := radius_pos _
  -- the open set and the map
  have hcls := h.cls (a7Diag V t z)
  rw [hF] at hcls
  have hdiff : DifferentiableOn ℂ (Ψ t) (a7Open x₁ x₂ y₁ y₂) :=
    hcls.1.mono ((a7Open_subset _ _ _ _).trans (self_subset_thickening h.rho_pos _))
  have hne : ∀ u ∈ a7Open x₁ x₂ y₁ y₂, deriv (Ψ t) u ≠ 0 := fun u hu =>
    norm_pos_iff.1 (lt_of_lt_of_le h.m_pos (hcls.2.2.2 u (a7Open_subset _ _ _ _ hu)))
  have hB : closedBall z (2 * r) ⊆ a7Open x₁ x₂ y₁ y₂ :=
    (closedBall_subset_closedBall hsmall').trans (hK z hz)
  have him : 2 * r ≤ z.im := by
    have hm : z - ((2 * r : ℝ) : ℂ) * Complex.I ∈ closedBall z (2 * r) := by
      rw [mem_closedBall, dist_eq_norm]
      simp [abs_of_pos hr0]
    have := (hB hm).2.2.1
    simp at this
    linarith [h.y_pos]
  -- continuity of the pushed value in the centre
  have hc1 : ContinuousAt (fun w => evalReg (X ω) ((foldedCircle (cf (a7Diag V t w))
      (af (a7Diag V t w) * r)).map (F (a7Diag V t w)))) z :=
    ((hcont k').comp (continuous_a7Diag V t)).continuousAt
  have hev : ∀ᶠ w in 𝓝 z, evalReg (X ω) ((foldedCircle (cf (a7Diag V t w))
      (af (a7Diag V t w) * r)).map (F (a7Diag V t w))) =
      evalReg (X ω) ((foldedCircle w r).map (Ψ t)) := by
    filter_upwards [(isOpen_a7Open x₁ x₂ y₁ y₂).mem_nhds hzO] with w hw
    obtain ⟨h1, h2, h3⟩ := hdiag t ht w (a7Open_subset _ _ _ _ hw)
    rw [h1, h2, h3, one_mul]
  have hc2 : ContinuousAt (fun w => evalReg (X ω) ((foldedCircle w r).map (Ψ t))) z :=
    hc1.congr hev
  have h1 := hc2.tendsto.comp (RegClosure.tendsto_dyadicRoundC z)
  rw [a7_pushErr_eq (isOpen_a7Open x₁ x₂ y₁ y₂) hdiff hne hB him h1]
  have hq := hE (a7Diag V t z) (hR t ht z hzR)
  rw [hF, hc, ha, one_mul, hr] at hq
  exact hq

end SWCore
end QuantumZipper
