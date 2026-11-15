/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FcChart
import InteractingSLE.Spec.Sec7.Aux125Life
import InteractingSLE.Spec.Sec5.TimeDensity

/-!
# Local geometry of two nested current charts near the outer landing

Packet PROVE-R6-FACE2. Deterministic lemmas for the R.6 face (`R6FcCore`), in the Jordan coordinates `ψ` of the outer
pocket `C` and `ψ'` of the contained pocket `U ⊆ C`:

* `mem_of_increment` (**the increment stays near the tip**): in `U`'s chain, a point of `U` alive at the relative time
  `q_T` and outside a set `B` containing the physical image `E_T(ℍ̄ ∩ B(0, ρ₀))` of a small half-disc at the driver
  stays alive at every `q ∈ [q_T, q_T + ε)` (the hull increment `f_{q_T}⁻¹(K^{shift}_{q − q_T})` lies in that image;
  `Sec5.fwdHull_add_sdiff_eq_image`, `Aux125.fwdHull_subset_closedBall_of_bound`);
* `inter_ball_subset_of_noncorner` (**local containment**): if `p ∈ Ū ∩ C̄`, `p ≠ x₀` and
  `p ∉ closure (∂U ∩ C)`, then `C ∩ B(p, ε) ⊆ U` for some `ε > 0` (`R6Safe.exists_halfDisc_subset_image`);
* `alive_iff` (**the two charts agree on aliveness near the landing**): with `C ∩ B(p_F, ε) ⊆ U`,
  `D_C ∩ B(p_F, ε) ⊆ D_U ⊆ D_C`, a point `p ∈ B(p_F, ε/2)` of both closures is alive for `C` iff it is alive for `U`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Fc

/-! ### The increment of the inner chain stays near the tip -/

/-- **The hull increment of a continuous chain is small for short times**: for `ρ > 0` there is `θ > 0` with
`fwdHull (shiftDrive W q) u ⊆ closedBall 0 (ρ / 2)` for `0 ≤ u < θ`. -/
theorem exists_shift_hull_small {W : ℝ → ℝ} (hW : Continuous W) (q : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ θ > 0, ∀ u : ℝ, 0 ≤ u → u < θ →
      fwdHull (QuantumZipper.RS.shiftDrive W q) u ⊆ closedBall 0 (ρ / 2) := by
  obtain ⟨θ₁, hθ₁, hθ₁W⟩ := Metric.continuousAt_iff.1 hW.continuousAt (ρ / 4) (by positivity)
  set θ : ℝ := min θ₁ ((ρ / 12) ^ 2) with hθ
  have hθpos : 0 < θ := lt_min hθ₁ (by positivity)
  refine ⟨θ, hθpos, fun u hu huθ => ?_⟩
  set w : ℝ≥0 → ℝ := fun t => QuantumZipper.RS.shiftDrive W q t with hw
  have hwc : ContinuousOn w (Iio θ.toNNReal) :=
    ((QuantumZipper.RS.continuous_shiftDrive hW q).comp NNReal.continuous_coe).continuousOn
  have hM : ∀ t : ℝ≥0, t < θ.toNNReal → |w t| ≤ ρ / 4 := by
    intro t ht
    have ht' : (t : ℝ) < θ := by
      have := (Real.lt_toNNReal_iff_coe_lt).1 ht
      exact this
    have hd : dist (q + t) q < θ₁ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg t.coe_nonneg]
      exact ht'.trans_le (min_le_left _ _)
    have h := hθ₁W hd
    rw [Real.dist_eq] at h
    exact h.le
  have hs : u.toNNReal < θ.toNNReal := (Real.toNNReal_lt_toNNReal_iff hθpos).2 huθ
  have hsub := Aux125.fwdHull_subset_closedBall_of_bound hwc hM hs
  have heq : fwdHull (fun r : ℝ => w r.toNNReal) u.toNNReal = fwdHull (QuantumZipper.RS.shiftDrive W q) u := by
    rw [Real.coe_toNNReal _ hu]
    refine fwdHull_eq_of_eqOn hu (lt_add_one u) fun r hr => ?_
    simp only [hw, Real.coe_toNNReal _ hr.1]
  rw [heq] at hsub
  refine hsub.trans (closedBall_subset_closedBall ?_)
  have hsq : Real.sqrt (θ.toNNReal : ℝ) ≤ ρ / 12 := by
    rw [Real.coe_toNNReal _ hθpos.le]
    calc Real.sqrt θ ≤ Real.sqrt ((ρ / 12) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
      _ = ρ / 12 := Real.sqrt_sq (by positivity)
  linarith

/-- **A point alive at `q_T` and away from the tip's image stays alive** (`mem_of_increment`; see the module
docstring). `E_T` is the continuous inverse extension of `U`'s chart at `q_T`, written `E₀ ∘ F̄_{q_T}`. -/
theorem mem_of_increment {U : Set ℂ} {ψ' : ℂ → ℂ} {E₀ : ℂ → ℂ} (hE₀ : EqOn E₀ (Function.invFunOn ψ' U) H)
    (hψ' : SupercriticalConformalCovariance.IsConformalBijection ψ' U H)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {qT : ℝ} (hqT : 0 ≤ qT) {ρ₀ : ℝ} {B : Set ℂ}
    (hB : ∀ z ∈ H, ‖z‖ ≤ ρ₀ / 2 → E₀ (fwdMapInv W qT z) ∈ B) {q : ℝ} (hq : qT ≤ q)
    (hsmall : fwdHull (QuantumZipper.RS.shiftDrive W qT) (q - qT) ⊆ closedBall 0 (ρ₀ / 2))
    {w : ℂ} (hwU : w ∈ U) (hwT : ψ' w ∉ fwdHull W qT) (hwB : w ∉ B) : ψ' w ∉ fwdHull W q := by
  intro hwq
  have hdiff : ψ' w ∈ fwdHull W (qT + (q - qT)) \ fwdHull W qT := by
    rw [add_sub_cancel]; exact ⟨hwq, hwT⟩
  rw [Sec5.fwdHull_add_sdiff_eq_image hW hW0 hqT (sub_nonneg.2 hq)] at hdiff
  obtain ⟨z, hz, hzw⟩ := hdiff
  have hzH : z ∈ H := hz.1
  have hzb : ‖z‖ ≤ ρ₀ / 2 := by simpa [mem_closedBall, dist_zero_right] using hsmall hz
  have hw : E₀ (fwdMapInv W qT z) = w := by
    rw [hzw, hE₀ (hψ'.2.mapsTo hwU)]
    exact hψ'.2.injOn.leftInvOn_invFunOn hwU
  exact hwB (hw ▸ hB z hzH hzb)

/-! ### Local containment at a non-corner point -/

/-- **Local containment at a non-corner point of the shared boundary**: if `p ∈ Ū ∩ C̄`, `p ≠ x₀` and
`p ∉ closure (∂U ∩ C)`, then `C ∩ B(p, ε) ⊆ U` for some `ε > 0`. -/
theorem inter_ball_subset_of_noncorner {C U : Set ℂ} {x₀ y₀ : ℂ} {ψ : ℂ → ℂ} (hψ : Sec6.IsJordanCoord C x₀ y₀ ψ)
    (hCb : Bornology.IsBounded C) (hx₀ : x₀ ∉ C) (hUo : IsOpen U) (hUC : U ⊆ C) {p : ℂ} (hpU : p ∈ closure U)
    (hpC : p ∈ closure C) (hpx : p ≠ x₀) (hpM : p ∉ closure (frontier U ∩ C)) :
    ∃ ε > 0, C ∩ ball p ε ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := R6Safe.exists_halfDisc_subset_image hψ hCb hx₀ hUo hUC isClosed_closure subset_closure hpU hpC
    hpx hpM
  obtain ⟨ε, hε, hεψ⟩ := Metric.continuousWithinAt_iff.1 (hψ.1 p ⟨hpC, hpx⟩) r hr
  refine ⟨ε, hε, fun w hw => ?_⟩
  have hwx : w ∈ closure C \ {x₀} := ⟨subset_closure hw.1, fun h => hx₀ (h ▸ hw.1)⟩
  have hψw : ψ w ∈ H ∩ ball (ψ p) r := ⟨hψ.2.2.2.1.2.mapsTo hw.1, hεψ hwx (mem_ball.1 hw.2)⟩
  obtain ⟨u, huU, hu⟩ := hrU hψw
  rwa [← hψ.2.2.2.1.2.injOn (hUC huU) hw.1 hu]

/-! ### Aliveness in the two charts near the landing -/

/-- **Alive for `C` iff alive for `U` near the landing** (`alive_iff`; see the module docstring). -/
theorem alive_iff {C U : Set ℂ} {x₀ y₀ x₀' y₀' : ℂ} {ψ ψ' : ℂ → ℂ}
    (hψ : Sec6.IsJordanCoord C x₀ y₀ ψ) (hCb : Bornology.IsBounded C) (hx₀ : x₀ ∉ C)
    (hψ' : Sec6.IsJordanCoord U x₀' y₀' ψ') (hUb : Bornology.IsBounded U) (hx₀' : x₀' ∉ U) (hUC : U ⊆ C)
    {K K' : Set ℂ} (hKH : K ⊆ H) (hK'H : K' ⊆ H)
    (hIncl : U ∩ ψ' ⁻¹' (H \ K') ⊆ C ∩ ψ ⁻¹' (H \ K))
    {pF : ℂ} {ε : ℝ} (hΛa : C ∩ ball pF ε ⊆ U) (hΛ : C ∩ ψ ⁻¹' (H \ K) ∩ ball pF ε ⊆ U ∩ ψ' ⁻¹' (H \ K'))
    {p : ℂ} (hp : p ∈ ball pF (ε / 2)) (hpC : p ∈ closure C \ {x₀}) (hpU : p ∈ closure U \ {x₀'}) :
    ψ p ∉ closure K ↔ ψ' p ∉ closure K' := by
  have hε : 0 < ε := by
    have := mem_ball.1 hp
    linarith [dist_nonneg (x := p) (y := pF)]
  have hpball : ∀ ρ : ℝ, ∀ z ∈ ball p (min ρ (ε / 2)), z ∈ ball pF ε ∧ z ∈ ball p ρ := fun ρ z hz => by
    have h1 := mem_ball.1 hz
    have h2 := mem_ball.1 hp
    exact ⟨mem_ball.2 (by linarith [dist_triangle z p pF, min_le_right ρ (ε / 2)]),
      mem_ball.2 (lt_of_lt_of_le h1 (min_le_left _ _))⟩
  constructor
  · intro halive
    obtain ⟨ρ, hρ, hρsub⟩ := exists_ball_subset_of_alive hψ hx₀ hpC halive
    refine notMem_closure_of_ball_subset hψ' hUb hx₀' hK'H hpU (lt_min hρ (half_pos hε)) fun z hz => ?_
    obtain ⟨hzF, hzp⟩ := hpball ρ z hz.2
    exact hΛ ⟨hρsub ⟨hUC hz.1, hzp⟩, hzF⟩
  · intro halive
    obtain ⟨ρ, hρ, hρsub⟩ := exists_ball_subset_of_alive hψ' hx₀' hpU halive
    refine notMem_closure_of_ball_subset hψ hCb hx₀ hKH hpC (lt_min hρ (half_pos hε)) fun z hz => ?_
    obtain ⟨hzF, hzp⟩ := hpball ρ z hz.2
    exact hIncl (hρsub ⟨hΛa ⟨hz.1, hzF⟩, hzp⟩)

end InteractingSLE.Sec7.R6Fc
