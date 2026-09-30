import QuantumZipper.Proofs.Zipper.SWCoreB7bExist
import QuantumZipper.Proofs.Thm18.G1Z3AddFun
import QuantumZipper.Statements.CouplingFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b (4): the `𝔥₀` add-on on pushed semicircles of a family

Decision D64, item (2). Almost surely, for a finite-parameter Lipschitz family of class maps whose
values on the `ρ`-thickening stay at distance `≥ c₀ > 0` from `0`, for all small `r`, all maps of
the family and all real centres `t ∈ [a − r, b + r]`,

  `evalReg (X + 𝔥₀) (fc(t,r).map Ψ_q) = evalReg X (fc(t,r).map Ψ_q) + ∫ 𝔥₀ d(fc(t,r).map Ψ_q)`

(`ae_evalReg_add_h0rev_family`), where `𝔥₀ = h0rev κ = (2/√κ) log|·|`. Proof: the existence of
the pushed limits (`swcB7_push_tendsto`) plus the proved deterministic add-on identity
`Thm18Asm.G1Z3.evalReg_add_ofFun_of_ae_z3` (regular sample, compact carrier in `Hbar`, a cutoff
`(2/√κ) log (max |z| (c₀/2))` of `𝔥₀`, continuous on `Hbar` and equal to `𝔥₀` near the carrier).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), (5.1) / Prop. 2.1 (adding a continuous
function), through the cited repository nodes. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

open Thm18Asm.G1RC

/-- The continuous cutoff of `𝔥₀` below radius `c`. -/
def h0cut (κ c : ℝ) (z : ℂ) : ℝ := 2 / Real.sqrt κ * Real.log (max ‖z‖ c)

theorem continuous_h0cut (κ : ℝ) {c : ℝ} (hc : 0 < c) : Continuous (h0cut κ c) := by
  unfold h0cut
  refine continuous_const.mul (Continuous.log (continuous_norm.max continuous_const) fun z => ?_)
  exact (lt_of_lt_of_le hc (le_max_right _ _)).ne'

theorem h0cut_eq {κ c : ℝ} {z : ℂ} (hz : c ≤ ‖z‖) : h0cut κ c z = h0rev κ z := by
  simp only [h0cut, h0rev, max_eq_left hz]

variable {n : ℕ} {a b ρ M m L : ℝ} {Ψ : (Fin n → ℝ) → ℂ → ℂ} {K : Set (Fin n → ℝ)}
  {Kπ : ℝ≥0} {pr : (Fin n → ℝ) → Fin n → ℝ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **The `𝔥₀` add-on on the pushed semicircles of a family, a.s.** -/
theorem ae_evalReg_add_h0rev_family (κ : ℝ) (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m)
    (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m) (hL0 : 0 ≤ L)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ pr) (hπK : ∀ q, pr q ∈ K) (hπid : ∀ q ∈ K, pr q = q)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hsep : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), c₀ ≤ ‖Ψ q z‖)
    (hX : IsFreeGFFModConstH X P) :
    ∃ r₂ : ℝ, 0 < r₂ ∧ ∀ r ∈ Ioo 0 r₂, ∀ᵐ ω ∂P, ∀ q ∈ K, ∀ t ∈ Icc (a - r) (b + r),
      evalReg (ofFun (h0rev κ) + X ω) ((foldedCircle (t : ℂ) r).map (Ψ q)) =
        evalReg (X ω) ((foldedCircle (t : ℂ) r).map (Ψ q)) +
          ∫ w, h0rev κ w ∂((foldedCircle (t : ℂ) r).map (Ψ q)) := by
  obtain ⟨r₁, hr₁, hT⟩ := swcB7_push_tendsto hab hρ hm hΨ hL0 hL hπ hπK hπid hX
  obtain ⟨r₂, hr₂, hB⟩ := swcN2_push_bounds hab hρ hm hΨ hL0 hL hπ hπK
  refine ⟨min (min r₁ r₂) (ρ / 3), lt_min (lt_min hr₁ hr₂) (by linarith), fun r hr => ?_⟩
  have hr1 : r ∈ Ioo 0 r₁ :=
    ⟨hr.1, lt_of_lt_of_le hr.2 ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hr2 : r ∈ Ioo 0 r₂ :=
    ⟨hr.1, lt_of_lt_of_le hr.2 ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hrρ : 3 * r < ρ := by have := lt_of_lt_of_le hr.2 (min_le_right _ _); linarith
  obtain ⟨hc, hH, -⟩ := hB r hr2
  filter_upwards [hT r hr1, RegSample.ae_isRegularSample hX] with ω hω hreg q hq t ht
  obtain ⟨F, hF⟩ := hreg
  set p : Fin (n + 1) → ℝ := Fin.snoc q t with hp
  set Φ := swcN2PushΦ Ψ pr a b r p with hΦ
  have hΦc : Continuous Φ := hc.comp (continuous_const.prodMk continuous_id)
  have hν : (foldedCircle (t : ℂ) r).map (Ψ q) = circM.map Φ :=
    (swcN2_push_eq hab.le hr.1 hrρ hΨ hπid hq ht).symm
  set Kψ : Set ℂ := Φ '' Icc 0 (2 * Real.pi) with hKψ
  have hKc : IsCompact Kψ := isCompact_Icc.image hΦc
  have hKH : Kψ ⊆ Hbar := by rintro _ ⟨θ, -, rfl⟩; exact hH p θ
  -- values of the family on `Kψ` stay away from `0`
  have hKsep : ∀ w ∈ Kψ, c₀ ≤ ‖w‖ := by
    rintro _ ⟨θ, -, rfl⟩
    have hinit : Fin.init p = q := by rw [hp, Fin.init_snoc]
    have hlast : p (Fin.last n) = t := by rw [hp, Fin.snoc_last]
    simp only [hΦ, swcN2PushΦ, hinit, hlast, hπid q hq]
    have hu := swcN2Clamp_mem (by linarith [hr.1] : a - r ≤ b + r) t
    refine hsep q hq _ (swcN2_ball_sub_thick (swcN2Clamp_mem hab.le _) (R := 2 * r)
      (by linarith) (swcN2_fold_mem_ball2 hab.le hr.1.le hu θ))
  have hnear : ∀ w ∈ cthickening (c₀ / 2) Kψ, c₀ / 2 ≤ ‖w‖ := by
    intro w hw
    rw [hKc.cthickening_eq_biUnion_closedBall (by positivity)] at hw
    obtain ⟨y, hy, hwy⟩ := mem_iUnion₂.1 hw
    have h1 := hKsep y hy
    rw [mem_closedBall, dist_eq_norm] at hwy
    have h3 := norm_sub_norm_le y w
    have : ‖y - w‖ = ‖w - y‖ := norm_sub_rev y w
    linarith
  have heq : EqOn (h0cut κ (c₀ / 2)) (h0rev κ) (cthickening (c₀ / 2) Kψ) :=
    fun w hw => h0cut_eq (hnear w hw)
  have : IsProbabilityMeasure (circM.map Φ) :=
    (Measure.isProbabilityMeasure_map_iff hΦc.measurable.aemeasurable).2 inferInstance
  have hcarry : ∀ᵐ w ∂(circM.map Φ), w ∈ Kψ := by
    refine (ae_map_iff hΦc.measurable.aemeasurable hKc.isClosed.measurableSet).2 ?_
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) circM_compl
    intro hθI
    exact hθ ⟨θ, hθI, rfl⟩
  have hlim := hω q hq t ht
  rw [hν] at hlim ⊢
  have key := Thm18Asm.G1Z3.evalReg_add_ofFun_of_ae_z3 hF
    (continuous_h0cut κ (by positivity : (0 : ℝ) < c₀ / 2)).continuousOn hKc hKH
    (by positivity : (0 : ℝ) < c₀ / 2) heq hcarry hlim
  have hint : ∫ w, h0cut κ (c₀ / 2) w ∂(circM.map Φ) = ∫ w, h0rev κ w ∂(circM.map Φ) :=
    integral_congr_ae (hcarry.mono fun w hw =>
      heq (self_subset_cthickening Kψ hw))
  rw [add_comm (ofFun (h0rev κ)), key, hint]

end SWCore
end QuantumZipper
