import QuantumZipper.Proofs.Loewner.ForwardODE
import QuantumZipper.Proofs.Zipper.GenUCOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (d): the open parameter set of the `τ' = 0` family

For the A-sep family at `τ' = 0` (D84), a parameter `p = (τ, a)` is *good* for a set `K₀` (the
points of the folded circle) when the forward flow started at `a w` survives a little beyond `τ`
for every `w` in a closed neighbourhood of `K₀` in the closed upper half-plane (`ParGood`). The
engine `ASep.ae_exact_open_dep` needs an open parameter set and, on each compact box inside it,
the uniform survival hypothesis `hgood` of the energy moduli (task ASEP-MOD). Here:

* `parGood_local`: a good parameter has a neighbourhood of good parameters with a common margin;
* `isOpen_parGood`;
* `exists_unif_of_isCompact`: on a compact set of good parameters the margin is uniform.

Own elementary bookkeeping (dilation `a' w = a (a'/a) w`, restriction of solutions,
finite subcover).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

/-- Closed upper half-plane. -/
def HbarC : Set ℂ := {w : ℂ | 0 ≤ w.im}

/-- **Good parameters** `p = (τ, a)`: `τ, a > 0` and the flow from `a w` survives until `τ + δ`
for all `w` within `δ` of `K₀` in the closed upper half-plane. -/
def ParGood (W : ℝ → ℝ) (K₀ : Set ℂ) (p : Fin 2 → ℝ) : Prop :=
  0 < p 0 ∧ 0 < p 1 ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ cthickening δ K₀ ∩ HbarC,
    ∃ u, IsForwardSol W ((p 1 : ℂ) * w) (p 0 + δ) u

theorem abs_apply_sub_le_dist (p q : Fin 2 → ℝ) (i : Fin 2) : |p i - q i| ≤ dist p q := by
  rw [← Real.dist_eq]; exact dist_le_pi_dist p q i

/-- **Local uniformity**: a good parameter has a ball of good parameters with a common margin. -/
theorem parGood_local {W : ℝ → ℝ} {K₀ : Set ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hK₀ : K₀ ⊆ closedBall 0 R) {p : Fin 2 → ℝ} (hp : ParGood W K₀ p) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ q : Fin 2 → ℝ, dist q p < ε →
      0 < q 0 ∧ 0 < q 1 ∧ ∀ w ∈ cthickening δ K₀ ∩ HbarC,
        ∃ u, IsForwardSol W ((q 1 : ℂ) * w) (q 0 + δ) u := by
  obtain ⟨hτ, ha, δ, hδ, hsol⟩ := hp
  set a := p 1 with hadef
  set τ := p 0 with hτdef
  set ε : ℝ := min (min (τ / 2) (a / 2)) (min (δ / 2) (a * δ / (4 * (R + δ + 1)))) with hεdef
  have hden : 0 < 4 * (R + δ + 1) := by positivity
  have hε : 0 < ε := by positivity
  refine ⟨ε, hε, δ / 4, by positivity, fun q hq => ?_⟩
  have h0 : |q 0 - τ| < ε := (abs_apply_sub_le_dist q p 0).trans_lt hq
  have h1 : |q 1 - a| < ε := (abs_apply_sub_le_dist q p 1).trans_lt hq
  have hε1 : ε ≤ τ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ a / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε4 : ε ≤ a * δ / (4 * (R + δ + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hq0 : 0 < q 0 := by linarith [(abs_lt.1 h0).1]
  have hq1 : 0 < q 1 := by linarith [(abs_lt.1 h1).1]
  refine ⟨hq0, hq1, fun w hw => ?_⟩
  obtain ⟨hwK, hwH⟩ := hw
  -- the dilated point
  set c : ℝ := q 1 / a with hcdef
  have hc : 0 < c := div_pos hq1 ha
  set w' : ℂ := (c : ℂ) * w with hw'def
  have hwn : ‖w‖ ≤ R + δ / 4 := by
    have hsub : cthickening (δ / 4) K₀ ⊆ closedBall 0 (δ / 4 + R) := by
      rw [← cthickening_closedBall (by positivity) hR]
      exact cthickening_subset_of_subset _ hK₀
    have := hsub hwK
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hcd : |c - 1| ≤ ε / a := by
    rw [hcdef, show q 1 / a - 1 = (q 1 - a) / a by field_simp, abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right h1.le ha.le
  have hdist : dist w' w ≤ δ / 4 := by
    rw [dist_eq_norm, hw'def, show (c : ℂ) * w - w = ((c - 1 : ℝ) : ℂ) * w by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hεa : ε / a ≤ δ / (4 * (R + δ + 1)) := by
      rw [div_le_iff₀ ha]
      calc ε ≤ a * δ / (4 * (R + δ + 1)) := hε4
        _ = δ / (4 * (R + δ + 1)) * a := by ring
    have hwn' : ‖w‖ ≤ R + δ + 1 := by linarith
    calc |c - 1| * ‖w‖ ≤ δ / (4 * (R + δ + 1)) * (R + δ + 1) :=
          mul_le_mul (hcd.trans hεa) hwn' (norm_nonneg _) (by positivity)
      _ = δ / 4 := by field_simp
  have hw'K : w' ∈ cthickening δ K₀ := by
    have h := mem_cthickening_of_dist_le w' w (δ / 4) (cthickening (δ / 4) K₀) hwK hdist
    have hs := cthickening_cthickening_subset (by positivity : (0 : ℝ) ≤ δ / 4)
      (by positivity : (0 : ℝ) ≤ δ / 4) K₀
    exact cthickening_mono (by linarith : δ / 4 + δ / 4 ≤ δ) K₀ (hs h)
  have hw'H : w' ∈ HbarC := by
    show 0 ≤ ((c : ℂ) * w).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_nonneg hc.le hwH
  obtain ⟨u, hu⟩ := hsol w' ⟨hw'K, hw'H⟩
  have heq : (a : ℂ) * w' = (q 1 : ℂ) * w := by
    rw [hw'def, hcdef, ← mul_assoc, ← Complex.ofReal_mul, mul_div_cancel₀ _ ha.ne']
  rw [heq] at hu
  refine ⟨u, isForwardSol_restrict hu (by positivity) ?_⟩
  linarith [(abs_lt.1 h0).2]

/-- The good parameters form an open set. -/
theorem isOpen_parGood {W : ℝ → ℝ} {K₀ : Set ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hK₀ : K₀ ⊆ closedBall 0 R) : IsOpen {p : Fin 2 → ℝ | ParGood W K₀ p} := by
  refine isOpen_iff.2 fun p hp => ?_
  obtain ⟨ε, hε, δ, hδ, h⟩ := parGood_local hR hK₀ hp
  exact ⟨ε, hε, fun q hq => let h' := h q hq; ⟨h'.1, h'.2.1, δ, hδ, h'.2.2⟩⟩

/-- **Uniform margin on a compact set of good parameters.** -/
theorem exists_unif_of_isCompact {W : ℝ → ℝ} {K₀ : Set ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hK₀ : K₀ ⊆ closedBall 0 R) {S : Set (Fin 2 → ℝ)} (hS : IsCompact S)
    (hSU : S ⊆ {p | ParGood W K₀ p}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ S, ∀ w ∈ cthickening δ K₀ ∩ HbarC,
      ∃ u, IsForwardSol W ((p 1 : ℂ) * w) (p 0 + δ) u := by
  classical
  have hloc : ∀ p ∈ S, ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ q : Fin 2 → ℝ, dist q p < ε →
      0 < q 0 ∧ 0 < q 1 ∧ ∀ w ∈ cthickening δ K₀ ∩ HbarC,
        ∃ u, IsForwardSol W ((q 1 : ℂ) * w) (q 0 + δ) u :=
    fun p hp => parGood_local hR hK₀ (hSU hp)
  choose! εf hεf δf hδf hgood using hloc
  obtain ⟨t, htS, hcov⟩ := hS.elim_nhds_subcover (fun p => ball p (εf p))
    fun p hp => ball_mem_nhds p (hεf p hp)
  by_cases ht : t.Nonempty
  · refine ⟨t.inf' ht δf, (Finset.lt_inf'_iff ht).2 fun p hp => hδf p (htS p hp),
      fun p hp w hw => ?_⟩
    obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.1 (hcov hp)
    have hle : t.inf' ht δf ≤ δf k := Finset.inf'_le _ hk
    have hw' : w ∈ cthickening (δf k) K₀ ∩ HbarC := ⟨cthickening_mono hle K₀ hw.1, hw.2⟩
    obtain ⟨-, -, h⟩ := hgood k (htS k hk) p hpk
    obtain ⟨u, hu⟩ := h w hw'
    exact ⟨u, isForwardSol_restrict hu (by
      have := (hgood k (htS k hk) p hpk).1
      linarith [(Finset.lt_inf'_iff ht).2 fun p hp => hδf p (htS p hp)]) (by linarith)⟩
  · refine ⟨1, one_pos, fun p hp => ?_⟩
    obtain ⟨k, hk, -⟩ := mem_iUnion₂.1 (hcov hp)
    exact absurd ⟨k, hk⟩ ht

end ASep
end QuantumZipper
