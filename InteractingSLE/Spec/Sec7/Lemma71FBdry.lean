/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71FInfty

/-!
# The boundary homeomorphism of the two-point pocket uniformizer

Packet PROVE-LEMMA71F. Remark 6.14 (p. 217): "Let `ψ : C → ℍ` send `x₀` to zero and `y₀` to infinity. Its Jordan
boundary homeomorphism makes `ψ(η_C)` a continuous simple path from zero to infinity"; proof of Lemma 7.1 (p. 225):
"together with the Jordan boundary homeomorphism, give the endpoint assertions".

The landed geometric part of Remark 6.14 (`Sec7.mappedSegment_props_finite`, `…_infinite`, `Lemma71Pocket.lean`) takes
a boundary map `Ψ`, continuous and injective on a set `E` containing the segment, with values in `ℍ̄`, mapping the pocket
into `ℍ`, `x₀` to `0` and neighbourhoods of `y₀` to neighbourhoods of `∞`. This file constructs it: the two-point
uniformizer itself extends to such a `Ψ`.

* `continuousOn_bdryMob`, `injOn_bdryMob`, `bdryMob_mem_Hbar`, `bdryMob_self`, `tendsto_norm_bdryMob_nhdsNE`: the
  Möbius map `M_{p,q} : 𝔻 → ℍ` on the closed disc minus `q`;
* **`exists_twoPoint_uniformizer_ext_of_jordan`** (bounded Jordan pocket, `y₀` finite): a conformal `Ψ : D → ℍ`,
  continuous and injective on `closure D ∖ {y₀}` with values in `ℍ̄`, `Ψ(x₀) = 0`, `|Ψ| → ∞` at `y₀`;
* **`exists_twoPoint_uniformizer_ext_of_jordan_infty`** (pocket closing at `∞`): the same on all of `closure C`, with
  `|Ψ| → ∞` along `cobounded ℂ ⊓ 𝓟 (closure C)`.

Proof: the Schoenflies parametrization `φ` of the closed disc onto `closure D` has a continuous inverse on `closure D`
(`Lemma71E.tendsto_inv_of_isCompact`), and `M_{p,q}` is continuous and injective on the closed disc minus `q`, maps the
circle into `ℝ`, and tends to `∞` at `q`. For `y₀ = ∞`, transport through the Cayley map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped ComplexConjugate

namespace InteractingSLE.Sec7.Lemma71F

open Lemma71E

/-! ### The Möbius map on the closed disc -/

section Mobius

variable {p q : ℂ}

theorem conj_ne_zero_of_norm_eq_one (hq : ‖q‖ = 1) : conj q ≠ 0 := fun h => by
  have := conj_mul_self hq
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem continuousOn_bdryMob (hq : ‖q‖ = 1) : ContinuousOn (bdryMob p q) {w | w ≠ q} := by
  intro w hw
  have h1 : ContinuousAt (fun w => cayleyInv (conj q * w)) w :=
    ContinuousAt.comp (f := fun w => conj q * w) (g := cayleyInv)
      (QuantumZipper.CA.differentiableAt_cayleyInv (conj_mul_ne_one_of_ne hq hw)).continuousAt
      (by fun_prop)
  exact (h1.sub continuousAt_const).continuousWithinAt

theorem injOn_bdryMob (hq : ‖q‖ = 1) : InjOn (bdryMob p q) {w | w ≠ q} := by
  intro w₁ h₁ w₂ h₂ h
  have h' : cayleyInv (conj q * w₁) = cayleyInv (conj q * w₂) := sub_left_inj.1 h
  have := congrArg cayley h'
  rw [QuantumZipper.CA.cayley_cayleyInv (conj_mul_ne_one_of_ne hq h₁),
    QuantumZipper.CA.cayley_cayleyInv (conj_mul_ne_one_of_ne hq h₂)] at this
  exact mul_left_cancel₀ (conj_ne_zero_of_norm_eq_one hq) this

theorem bdryMob_mem_Hbar (hq : ‖q‖ = 1) {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) : bdryMob p q w ∈ Hbar := by
  show 0 ≤ (bdryMob p q w).im
  rw [bdryMob, sub_im, ofReal_im, sub_zero]
  have hw' : conj q * w ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_conj, hq, one_mul]
    exact mem_closedBall_zero_iff.1 hw
  exact QuantumZipper.CA.cayleyInv_mem_Hbar hw'

theorem bdryMob_self (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) : bdryMob p q p = 0 :=
  tendsto_nhds_unique ((continuousOn_bdryMob hq).continuousAt (isOpen_ne.mem_nhds hpq)).tendsto
    (tendsto_bdryMob_left hp hq hpq)

theorem tendsto_norm_bdryMob_nhdsNE (hq : ‖q‖ = 1) :
    Tendsto (fun w => ‖bdryMob p q w‖) (𝓝[≠] q) atTop := by
  have h1 : Tendsto (fun w => conj q * w) (𝓝[≠] q) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw =>
      conj_mul_ne_one_of_ne hq hw⟩
    have hc : Continuous fun w : ℂ => conj q * w := by fun_prop
    have := (hc.tendsto q).mono_left (nhdsWithin_le_nhds (s := {q}ᶜ))
    rwa [conj_mul_self hq] at this
  have h2 := QuantumZipper.CA.tendsto_cayleyInv_nhdsNE_one.comp h1
  have h3 : Tendsto (fun w => bdryMob p q w) (𝓝[≠] q) (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded] at h2 ⊢
    refine tendsto_atTop_mono' _ (Eventually.of_forall fun w => ?_)
      (tendsto_atTop_add_const_right _ (-‖((cayleyInv (conj q * p)).re : ℂ)‖) h2)
    have := norm_sub_norm_le (cayleyInv (conj q * w)) ((cayleyInv (conj q * p)).re : ℂ)
    simp only [Function.comp_apply, bdryMob]
    linarith
  exact tendsto_norm_atTop_iff_cobounded.2 h3

end Mobius

/-! ### Bounded Jordan pockets -/

/-- **The boundary homeomorphism of the two-point uniformizer of a bounded Jordan pocket.** For a bounded domain `D`
whose frontier is a Jordan curve and distinct frontier points `x₀ ≠ y₀`, there is a conformal map `Ψ : D → ℍ` which is
continuous and injective on `closure D ∖ {y₀}` with values in `ℍ̄`, sends `x₀` to `0`, and tends to `∞` at `y₀`. -/
theorem exists_twoPoint_uniformizer_ext_of_jordan {D : Set ℂ} (hDo : IsOpen D) (hDc : IsConnected D)
    (hDb : IsBounded D) (hJ : LQGMetric.JordanMap.IsJordanCurve (frontier D)) {x₀ y₀ : ℂ}
    (hx : x₀ ∈ frontier D) (hy : y₀ ∈ frontier D) (hxy : x₀ ≠ y₀) :
    ∃ Ψ : ℂ → ℂ, IsConformalBijection Ψ D H ∧ ContinuousOn Ψ (closure D \ {y₀}) ∧
      InjOn Ψ (closure D \ {y₀}) ∧ MapsTo Ψ (closure D \ {y₀}) Hbar ∧ Ψ x₀ = 0 ∧
      Tendsto (fun z => ‖Ψ z‖) (𝓝[closure D \ {y₀}] y₀) atTop := by
  obtain ⟨p₀, hp₀⟩ := hDc.nonempty
  have hDeq := connectedComponentIn_compl_frontier_eq hDo hDc hp₀
  have hp₀Γ : p₀ ∈ (frontier D)ᶜ := by
    rw [← hDeq] at hp₀
    exact connectedComponentIn_subset _ _ hp₀
  obtain ⟨φ, hφc, hφi, hφd, -, hφball, hφsph⟩ :=
    Foundations.Schoenflies.schoenflies_disc hJ hp₀Γ (by rw [hDeq]; exact hDb)
  rw [hDeq] at hφball
  have hφbij : IsConformalBijection φ (ball 0 1) D := by
    refine ⟨hφd, ?_⟩
    rw [← hφball]
    exact (hφi.mono ball_subset_closedBall).bijOn_image
  have hcl : φ '' closedBall 0 1 = closure D := by
    rw [← ball_union_sphere, image_union, hφball, hφsph, closure_eq_self_union_frontier]
  -- the continuous inverse on the closure
  set G := invFunOn φ (closedBall (0 : ℂ) 1) with hGdef
  have hGmem : ∀ w ∈ closure D, G w ∈ closedBall (0 : ℂ) 1 ∧ φ (G w) = w := fun w hw => by
    rw [← hcl] at hw
    exact invFunOn_pos hw
  have hGφ : ∀ z ∈ closedBall (0 : ℂ) 1, G (φ z) = z := fun z hz => hφi.leftInvOn_invFunOn hz
  have hGc : ContinuousOn G (closure D) := fun w hw =>
    tendsto_inv_of_isCompact (isCompact_closedBall 0 1) hφc hφi nhdsWithin_le_nhds (hGmem w hw).1
      (hGmem w hw).2 (eventually_nhdsWithin_of_forall fun z hz => (hGmem z hz).1)
      (eventually_nhdsWithin_of_forall fun z hz => (hGmem z hz).2)
  have hGi : InjOn G (closure D) := fun w₁ h₁ w₂ h₂ h => by
    rw [← (hGmem w₁ h₁).2, ← (hGmem w₂ h₂).2, h]
  have hGsph : ∀ w ∈ frontier D, ‖G w‖ = 1 := fun w hw => by
    rw [← hφsph] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    rw [hGφ s (sphere_subset_closedBall hs)]
    exact mem_sphere_zero_iff_norm.1 hs
  have hxcl : x₀ ∈ closure D := frontier_subset_closure hx
  have hycl : y₀ ∈ closure D := frontier_subset_closure hy
  set pa := G x₀ with hpa
  set qb := G y₀ with hqb
  have hp1 : ‖pa‖ = 1 := hGsph x₀ hx
  have hq1 : ‖qb‖ = 1 := hGsph y₀ hy
  have hpq : pa ≠ qb := fun h => hxy (hGi hxcl hycl h)
  have hne : ∀ w ∈ closure D \ {y₀}, G w ≠ qb := fun w hw h =>
    hw.2 (hGi hw.1 hycl h)
  have hmaps : MapsTo G (closure D \ {y₀}) {w | w ≠ qb} := fun w hw => hne w hw
  refine ⟨bdryMob pa qb ∘ G, ?_, (continuousOn_bdryMob hq1).comp (hGc.mono sdiff_subset) hmaps,
    (injOn_bdryMob hq1).comp (hGi.mono sdiff_subset) hmaps,
    fun w hw => bdryMob_mem_Hbar hq1 (hGmem w hw.1).1, bdryMob_self hp1 hq1 hpq, ?_⟩
  · -- conformal: on `D` the extension is the conformal uniformizer
    have hG' := isConformalBijection_invFunOn isOpen_ball hφbij
    have hψ := isConformalBijection_comp (isConformalBijection_bdryMob (p := pa) hq1) hG'
    have heq : EqOn (bdryMob pa qb ∘ G) (bdryMob pa qb ∘ invFunOn φ (ball (0 : ℂ) 1)) D := by
      intro w hw
      have hb : invFunOn φ (ball (0 : ℂ) 1) w ∈ ball (0 : ℂ) 1 := hG'.2.mapsTo hw
      have hφb : φ (invFunOn φ (ball (0 : ℂ) 1) w) = w := invFunOn_eq (hφbij.2.surjOn hw)
      show bdryMob pa qb (G w) = bdryMob pa qb (invFunOn φ (ball (0 : ℂ) 1) w)
      conv_lhs => rw [← hφb]
      rw [hGφ _ (ball_subset_closedBall hb)]
    exact ⟨hψ.1.congr heq, hψ.2.congr heq.symm⟩
  · have hGy : Tendsto G (𝓝[closure D \ {y₀}] y₀) (𝓝[≠] qb) :=
      tendsto_nhdsWithin_iff.2 ⟨((hGc y₀ hycl).mono sdiff_subset).tendsto,
        eventually_nhdsWithin_of_forall fun w hw => hne w hw⟩
    exact (tendsto_norm_bdryMob_nhdsNE (p := pa) hq1).comp hGy

/-! ### Pockets closing at `∞` -/

/-- **The boundary homeomorphism of the two-point uniformizer of a pocket closing at `∞`.** Let `C ⊆ ℍ` be open,
connected and unbounded, with the frontier of its Cayley image a Jordan curve. For every frontier point `x₀` of `C`
there is a conformal map `Ψ : C → ℍ` which is continuous and injective on `closure C` with values in `ℍ̄`, sends `x₀` to
`0`, and tends to `∞` along `cobounded ℂ ⊓ 𝓟 (closure C)`. -/
theorem exists_twoPoint_uniformizer_ext_of_jordan_infty {C : Set ℂ} (hCo : IsOpen C) (hCc : IsConnected C)
    (hCH : C ⊆ H) (hCu : ¬ IsBounded C) (hJ : LQGMetric.JordanMap.IsJordanCurve (frontier (cayley '' C)))
    {x₀ : ℂ} (hx : x₀ ∈ frontier C) :
    ∃ Ψ : ℂ → ℂ, IsConformalBijection Ψ C H ∧ ContinuousOn Ψ (closure C) ∧ InjOn Ψ (closure C) ∧
      MapsTo Ψ (closure C) Hbar ∧ Ψ x₀ = 0 ∧
      Tendsto (fun z => ‖Ψ z‖) (cobounded ℂ ⊓ 𝓟 (closure C)) atTop := by
  set U := cayley '' C with hU
  have hp := cayley_mem_frontier hCo hCH hx
  have h1 := one_mem_frontier_cayley_image hCo hCH hCu
  have hI : ∀ w ∈ closure C, w + I ≠ 0 := fun w hw =>
    QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (im_nonneg_of_mem_closure hCH hw)
  obtain ⟨ΨU, hΨU, hΨc, hΨi, hΨH, hΨ0, hΨinf⟩ := exists_twoPoint_uniformizer_ext_of_jordan
    (isOpen_cayley_image hCo hCH) (isConnected_cayley_image hCc hCH) (isBounded_cayley_image hCH) hJ hp h1
    (QuantumZipper.CA.cayley_ne_one (hI x₀ (frontier_subset_closure hx)))
  have hcc : ContinuousOn cayley (closure C) := QuantumZipper.CA.continuousOn_cayley.mono fun w hw => by
    show w ≠ -I
    exact QuantumZipper.CA.ne_neg_I_iff.2 (hI w hw)
  have hmaps : MapsTo cayley (closure C) (closure U \ {1}) := fun w hw =>
    ⟨((hcc w hw).mono subset_closure).mem_closure_image hw, QuantumZipper.CA.cayley_ne_one (hI w hw)⟩
  refine ⟨ΨU ∘ cayley, isConformalBijection_comp hΨU (isConformalBijection_cayley_image hCH),
    hΨc.comp hcc hmaps, hΨi.comp (cayley_injOn.mono fun w hw => hI w hw) hmaps,
    fun w hw => hΨH (hmaps hw), hΨ0, ?_⟩
  have hT : Tendsto cayley (cobounded ℂ ⊓ 𝓟 (closure C)) (𝓝[closure U \ {1}] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨QuantumZipper.CA.tendsto_cayley_cobounded.mono_left inf_le_left,
      (eventually_principal.2 fun w hw => hmaps hw).filter_mono inf_le_right⟩
  exact hΨinf.comp hT

end InteractingSLE.Sec7.Lemma71F
