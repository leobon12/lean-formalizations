/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71EJordan

/-!
# The two-point uniformizer of a pocket closing at `∞`

Packet PROVE-LEMMA71F (PROVE-LEMMA71E's "What remains" C: "**Unbounded pockets** (`y₀ = ∞`, e.g. if the outer curves
do not meet again) are not covered: one needs the Jordan theorem on the sphere (e.g. after `cayley`, the frontier plus
the point `1` is a Jordan curve)"). Specification §7.1, setup (p. 222): "Let `ψ : C → ℍ` be a conformal transformation
which sends `x₀` to `0` and `y₀` to `∞`"; proof of Lemma 7.1 (p. 223): "Compactify their parameter intervals"; p. 225:
"or after the fixed Möbius map to the compactified disk".

The compactified picture is the image under the Cayley map `cayley z = (z − i)/(z + i)` (`ℍ → 𝔻`, `∞ ↦ 1`). A pocket
`C ⊆ ℍ` is a Jordan pocket in that picture when `cayley '' C` (a bounded subset of the disc) has a Jordan curve as
frontier; the pocket is unbounded exactly when `1` is one of its frontier points (`one_mem_frontier_cayley_image`).

* `exists_twoPoint_uniformizer_of_jordan_cayley`: for two distinct frontier points `p ≠ q` of `cayley '' C`, a conformal
  `ψ : C → ℍ` with `ψ ∘ cayleyInv → 0` at `p` and `|ψ ∘ cayleyInv| → ∞` at `q` (within `cayley '' C`) — this covers
  bounded pockets, pockets closing at `∞`, and pockets opening at `∞` alike;
* **`exists_twoPoint_uniformizer_of_jordan_infty`**: the case `y₀ = ∞` in the coordinates of `C`: `ψ → 0` at
  `x₀ ∈ frontier C` and `|ψ| → ∞` along `cobounded ℂ ⊓ 𝓟 C`;
* **`exists_measurable_jordanPocketChart_infty`**: the measurable chart of a random pocket closing at `∞`
  (the analogue of `Lemma71E.exists_measurable_jordanPocketChart`), through `exists_measurable_approach_infty` and
  `exists_measurable_twoPointChart`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec7.Lemma71F

open Lemma71E

/-! ### The Cayley image of a subset of `ℍ` -/

section Cayley

variable {C : Set ℂ}

theorem add_I_ne_zero_of_mem_H {z : ℂ} (hz : z ∈ H) : z + I ≠ 0 :=
  QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt hz)

/-- Points of the closure of a subset of `ℍ` have nonnegative imaginary part. -/
theorem im_nonneg_of_mem_closure (hCH : C ⊆ H) {z : ℂ} (hz : z ∈ closure C) : 0 ≤ z.im := by
  have hcl : closure C ⊆ {w : ℂ | 0 ≤ w.im} :=
    closure_minimal (fun w hw => show 0 ≤ w.im from le_of_lt (hCH hw : (0 : ℝ) < w.im)) (isClosed_le continuous_const continuous_im)
  exact hcl hz

/-- The Cayley map is injective on `{z + i ≠ 0}`. -/
theorem cayley_injOn : InjOn cayley {z : ℂ | z + I ≠ 0} := fun z₁ h₁ z₂ h₂ h => by
  rw [← QuantumZipper.CA.cayleyInv_cayley h₁, ← QuantumZipper.CA.cayleyInv_cayley h₂, h]

/-- `cayley` maps a subset of `ℍ` conformally onto its image. -/
theorem isConformalBijection_cayley_image (hCH : C ⊆ H) : IsConformalBijection cayley C (cayley '' C) :=
  ⟨fun _ hz => (QuantumZipper.CA.differentiableAt_cayley
      (add_I_ne_zero_of_mem_H (hCH hz))).differentiableWithinAt,
    (cayley_injOn.mono fun _ hz => add_I_ne_zero_of_mem_H (hCH hz)).bijOn_image⟩

theorem cayley_image_subset_ball (hCH : C ⊆ H) : cayley '' C ⊆ ball (0 : ℂ) 1 := by
  rintro _ ⟨z, hz, rfl⟩
  exact QuantumZipper.CA.cayley_mem_ball (hCH hz)

/-- The Cayley image of a subset of `ℍ`, read through `cayleyInv`. -/
theorem cayley_image_eq (hCH : C ⊆ H) : cayley '' C = ball (0 : ℂ) 1 ∩ cayleyInv ⁻¹' C := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨QuantumZipper.CA.cayley_mem_ball (hCH hz), ?_⟩
    show cayleyInv (cayley z) ∈ C
    rw [QuantumZipper.CA.cayleyInv_cayley (add_I_ne_zero_of_mem_H (hCH hz))]
    exact hz
  · rintro ⟨hw, hwC⟩
    have hw1 : w ≠ 1 := fun h => by
      rw [h, mem_ball_zero_iff, norm_one] at hw
      exact lt_irrefl _ hw
    exact ⟨cayleyInv w, hwC, QuantumZipper.CA.cayley_cayleyInv hw1⟩

theorem ne_one_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 := fun h => by
  rw [h, mem_ball_zero_iff, norm_one] at hw
  exact lt_irrefl _ hw

theorem isOpen_cayley_image (hCo : IsOpen C) (hCH : C ⊆ H) : IsOpen (cayley '' C) := by
  rw [cayley_image_eq hCH]
  exact (QuantumZipper.CA.continuousOn_cayleyInv.mono fun w hw => ne_one_of_mem_ball hw).isOpen_inter_preimage
    isOpen_ball hCo

theorem isConnected_cayley_image (hCc : IsConnected C) (hCH : C ⊆ H) : IsConnected (cayley '' C) :=
  hCc.image _ (QuantumZipper.CA.continuousOn_cayley.mono fun z hz => by
    show z ≠ -I
    exact QuantumZipper.CA.ne_neg_I_iff.2 (add_I_ne_zero_of_mem_H (hCH hz)))

theorem isBounded_cayley_image (hCH : C ⊆ H) : IsBounded (cayley '' C) :=
  isBounded_ball.subset (cayley_image_subset_ball hCH)

/-- `cayley` tends to `cayley x₀` within the image, at a point `x₀` of the closure of `C ⊆ ℍ`. -/
theorem tendsto_cayley_nhdsWithin (hCH : C ⊆ H) {x₀ : ℂ} (hx : x₀ ∈ closure C) :
    Tendsto cayley (𝓝[C] x₀) (𝓝[cayley '' C] (cayley x₀)) := by
  have hx0 : x₀ + I ≠ 0 := QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (im_nonneg_of_mem_closure hCH hx)
  exact tendsto_nhdsWithin_iff.2 ⟨(QuantumZipper.CA.differentiableAt_cayley hx0).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun z hz => mem_image_of_mem _ hz⟩

/-- `cayley` tends to `1` within the image, along `cobounded ℂ ⊓ 𝓟 C`. -/
theorem tendsto_cayley_cobounded_inf :
    Tendsto cayley (cobounded ℂ ⊓ 𝓟 C) (𝓝[cayley '' C] 1) :=
  tendsto_nhdsWithin_iff.2 ⟨QuantumZipper.CA.tendsto_cayley_cobounded.mono_left inf_le_left,
    (eventually_principal.2 fun _ hz => mem_image_of_mem cayley hz).filter_mono inf_le_right⟩

/-- An unbounded set has a nontrivial filter `cobounded ℂ ⊓ 𝓟 C`. -/
theorem neBot_cobounded_inf (hCu : ¬ IsBounded C) : (cobounded ℂ ⊓ 𝓟 C).NeBot := by
  refine inf_principal_neBot_iff.2 fun U hU => ?_
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hsub : C ⊆ Uᶜ := fun z hz hzU => (hne ▸ (⟨hzU, hz⟩ : z ∈ U ∩ C) : z ∈ (∅ : Set ℂ))
  exact hCu ((isBounded_compl_iff.2 hU).subset hsub)

/-- A frontier point of `C ⊆ ℍ` (open) is mapped to a frontier point of the Cayley image. -/
theorem cayley_mem_frontier (hCo : IsOpen C) (hCH : C ⊆ H) {x₀ : ℂ} (hx : x₀ ∈ frontier C) :
    cayley x₀ ∈ frontier (cayley '' C) := by
  rw [hCo.frontier_eq] at hx
  rw [(isOpen_cayley_image hCo hCH).frontier_eq]
  have hx0 : x₀ + I ≠ 0 := QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (im_nonneg_of_mem_closure hCH hx.1)
  refine ⟨(QuantumZipper.CA.differentiableAt_cayley hx0).continuousAt.continuousWithinAt.mem_closure_image hx.1,
    ?_⟩
  rintro ⟨z, hz, hzx⟩
  exact hx.2 (cayley_injOn (add_I_ne_zero_of_mem_H (hCH hz)) hx0 hzx ▸ hz)

/-- The pocket `C ⊆ ℍ` is unbounded iff `1` (the image of `∞`) is a frontier point of its Cayley image. -/
theorem one_mem_frontier_cayley_image (hCo : IsOpen C) (hCH : C ⊆ H) (hCu : ¬ IsBounded C) :
    (1 : ℂ) ∈ frontier (cayley '' C) := by
  rw [(isOpen_cayley_image hCo hCH).frontier_eq]
  have := neBot_cobounded_inf hCu
  refine ⟨mem_closure_of_tendsto (QuantumZipper.CA.tendsto_cayley_cobounded.mono_left inf_le_left)
    ((eventually_principal.2 fun _ hz => mem_image_of_mem cayley hz).filter_mono inf_le_right), ?_⟩
  rintro ⟨z, hz, hz1⟩
  exact QuantumZipper.CA.cayley_ne_one (add_I_ne_zero_of_mem_H (hCH hz)) hz1

end Cayley

/-! ### The pathwise uniformizer -/

/-- **The two-point uniformizer in the compactified picture.** Let `C ⊆ ℍ` be open and connected and let the frontier
of its Cayley image be a Jordan curve. For two distinct frontier points `p ≠ q` of `cayley '' C` there is a conformal
map `ψ : C → ℍ` with `ψ ∘ cayleyInv → 0` at `p` and `|ψ ∘ cayleyInv| → ∞` at `q` (within `cayley '' C`). -/
theorem exists_twoPoint_uniformizer_of_jordan_cayley {C : Set ℂ} (hCo : IsOpen C) (hCc : IsConnected C)
    (hCH : C ⊆ H) (hJ : LQGMetric.JordanMap.IsJordanCurve (frontier (cayley '' C))) {p q : ℂ}
    (hp : p ∈ frontier (cayley '' C)) (hq : q ∈ frontier (cayley '' C)) (hpq : p ≠ q) :
    ∃ ψ : ℂ → ℂ, IsConformalBijection ψ C H ∧ ∃ ψU : ℂ → ℂ, (∀ z ∈ C, ψ z = ψU (cayley z)) ∧
      Tendsto ψU (𝓝[cayley '' C] p) (𝓝 0) ∧ Tendsto (fun w => ‖ψU w‖) (𝓝[cayley '' C] q) atTop := by
  obtain ⟨ψU, hψU, h0, hinf⟩ := exists_twoPoint_uniformizer_of_jordan (isOpen_cayley_image hCo hCH)
    (isConnected_cayley_image hCc hCH) (isBounded_cayley_image hCH) hJ hp hq hpq
  exact ⟨ψU ∘ cayley, isConformalBijection_comp hψU (isConformalBijection_cayley_image hCH), ψU,
    fun _ _ => rfl, h0, hinf⟩

/-- **The two-point uniformizer of a pocket closing at `∞`** (`y₀ = ∞`). Let `C ⊆ ℍ` be open, connected and unbounded,
with the frontier of its Cayley image a Jordan curve (the pocket is a Jordan domain of the compactified picture). For
every frontier point `x₀` of `C` there is a conformal map `ψ : C → ℍ` with `ψ → 0` at `x₀` (within `C`) and `|ψ| → ∞`
along `cobounded ℂ ⊓ 𝓟 C`. -/
theorem exists_twoPoint_uniformizer_of_jordan_infty {C : Set ℂ} (hCo : IsOpen C) (hCc : IsConnected C)
    (hCH : C ⊆ H) (hCu : ¬ IsBounded C) (hJ : LQGMetric.JordanMap.IsJordanCurve (frontier (cayley '' C)))
    {x₀ : ℂ} (hx : x₀ ∈ frontier C) :
    ∃ ψ : ℂ → ℂ, IsConformalBijection ψ C H ∧ Tendsto ψ (𝓝[C] x₀) (𝓝 0) ∧
      Tendsto (fun z => ‖ψ z‖) (cobounded ℂ ⊓ 𝓟 C) atTop := by
  have hp := cayley_mem_frontier hCo hCH hx
  have h1 := one_mem_frontier_cayley_image hCo hCH hCu
  have hx0 : x₀ + I ≠ 0 :=
    QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (im_nonneg_of_mem_closure hCH (frontier_subset_closure hx))
  obtain ⟨ψ, hψ, ψU, hψeq, h0, hinf⟩ := exists_twoPoint_uniformizer_of_jordan_cayley hCo hCc hCH hJ hp h1
    (QuantumZipper.CA.cayley_ne_one hx0)
  refine ⟨ψ, hψ, ?_, ?_⟩
  · exact (h0.comp (tendsto_cayley_nhdsWithin hCH (frontier_subset_closure hx))).congr'
      (eventually_nhdsWithin_of_forall fun z hz => (hψeq z hz).symm)
  · exact (hinf.comp tendsto_cayley_cobounded_inf).congr'
      ((eventually_principal.2 fun z hz => by
        show ‖ψU (cayley z)‖ = ‖ψ z‖
        rw [hψeq z hz]).filter_mono inf_le_right)

/-! ### The measurable chart of a random pocket closing at `∞` -/

/-- **The measurable chart of a random pocket closing at `∞`.** For a random unbounded pocket `C ω ⊆ ℍ` (open,
connected, simply connected, the frontier of its Cayley image a Jordan curve) observed through closed balls, with a
measurable marked frontier point `x₀ ω`, there is a random chart, conformal with domain `C ω`, with measurable domain
events, forward map and lift, the lift a continuous branch of `arg ψ′`, and `ψ → 0` at `x₀`, `|ψ| → ∞` at `∞`. -/
theorem exists_measurable_jordanPocketChart_infty {Ω : Type*} [MeasurableSpace Ω] {C : Ω → Set ℂ}
    (hCo : ∀ ω, IsOpen (C ω)) (hCc : ∀ ω, IsConnected (C ω)) (hCsc : ∀ ω, IsSimplyConnected (C ω))
    (hCH : ∀ ω, C ω ⊆ H) (hCu : ∀ ω, ¬ IsBounded (C ω))
    (hJ : ∀ ω, LQGMetric.JordanMap.IsJordanCurve (frontier (cayley '' C ω)))
    (hCm : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ C ω}) {x₀ : Ω → ℂ}
    (hx : Measurable x₀) (hxC : ∀ ω, x₀ ω ∈ frontier (C ω)) :
    ∃ c : Ω → Chart,
      (∀ ω, (c ω).IsConformal) ∧ (∀ ω, ((c ω).dom : Set ℂ) = C ω) ∧
      (∀ ω, IsConformalBijection (c ω).1 (C ω) H) ∧
      (∀ z, MeasurableSet {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      (∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L (C ω) ∧ ∀ z ∈ C ω, (c ω).2.2 z = (L z).im) ∧
      (∀ ω, Tendsto (c ω).1 (𝓝[C ω] (x₀ ω)) (𝓝 0) ∧
        Tendsto (fun z => ‖(c ω).1 z‖) (cobounded ℂ ⊓ 𝓟 (C ω)) atTop) := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  have hmem := measurableSet_mem_of_closedBall hCo hCm
  obtain ⟨Nx, hNx, hNxC, hNxt⟩ := exists_measurable_approach hCo hmem he hx fun ω =>
    frontier_subset_closure (hxC ω)
  obtain ⟨Ny, hNy, hNyC, hNyt⟩ := exists_measurable_approach_infty hCo hmem he hCu
  have hψ : ∀ ω, ∃ ψ : ℂ → ℂ, IsConformalBijection ψ (C ω) H ∧ Tendsto ψ (𝓝[C ω] (x₀ ω)) (𝓝 0) ∧
      Tendsto (fun z => ‖ψ z‖) (cobounded ℂ ⊓ 𝓟 (C ω)) atTop := fun ω =>
    exists_twoPoint_uniformizer_of_jordan_infty (hCo ω) (hCc ω) (hCH ω) (hCu ω) (hJ ω) (hxC ω)
  obtain ⟨c, hconf, hdom, hbij, hdm, hfm, hlm, hlc, hL, -, huniq⟩ :=
    exists_measurable_twoPointChart hCo hCc hCsc hCH hCm he hNx hNy hNxC hNyC fun ω => by
      obtain ⟨ψ, hψc, h0, hi⟩ := hψ ω
      exact ⟨ψ, hψc, h0.comp (hNxt ω), hi.comp (hNyt ω)⟩
  refine ⟨c, hconf, hdom, hbij, hdm, hfm, hlm, hlc, hL, fun ω => ?_⟩
  obtain ⟨ψ, hψc, h0, hi⟩ := hψ ω
  obtain ⟨a, ha, hEq⟩ := huniq ω ψ hψc (h0.comp (hNxt ω)) (hi.comp (hNyt ω))
  refine ⟨?_, ?_⟩
  · have := h0.const_mul (a : ℂ)
    rw [mul_zero] at this
    exact this.congr' (eventually_nhdsWithin_of_forall fun z hz => (hEq hz).symm)
  · have h1 : Tendsto (fun z => a * ‖ψ z‖) (cobounded ℂ ⊓ 𝓟 (C ω)) atTop := hi.const_mul_atTop ha
    refine h1.congr' ((eventually_principal.2 fun z hz => ?_).filter_mono inf_le_right)
    show a * ‖ψ z‖ = ‖(c ω).1 z‖
    rw [hEq hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]

end InteractingSLE.Sec7.Lemma71F
