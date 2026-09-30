import QuantumZipper.Proofs.Thm18.G1Side3Eq

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (8): the wedge field as free field plus profile on interior measures

For a probability measure `ν` carried by a compact set of `{Im ≥ c₀}` (`c₀ > 0`):
* `evalReg_wedge_split`: if the regularizations of the free sample `x` on `ν` converge, then
  `evalReg w ν = evalReg x ν + ∫ g dν`, `w` the wedge field and `g` the profile cut off inside
  the disc of radius `c₀/2`;
* `evalReg_wedge_fc`: on a folded circle `fc(p, ρ)` inside `{Im ≥ c₀}`,
  `evalReg w (fc(p, ρ)) = F(p, ρ) + ∫ g d fc(p, ρ)`.
Duplantier–Sheffield 2011 (5.1) (the profile is continuous off `0`); own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

/-- Regularized values agree when the dyadic averages agree on a carrier, eventually. -/
theorem evalReg_congr_carried {y y' : FieldSample} {T : Set ℂ}
    (h : ∀ᶠ j in atTop, ∀ u ∈ T, avgReg y j u = avgReg y' j u) {ν : Measure ℂ}
    (hν : ∀ᵐ u ∂ν, u ∈ T) : evalReg y ν = evalReg y' ν := by
  unfold evalReg
  refine limUnder_congr_side ?_
  filter_upwards [h] with j hj
  exact integral_congr_ae (hν.mono fun u hu => hj u hu)

theorem im_le_norm' (u : ℂ) : u.im ≤ ‖u‖ := (le_abs_self _).trans (Complex.abs_im_le_norm u)

variable {Q : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ}

/-- The wedge field and the free field plus the cut-off profile agree on `{Im ≥ c₀}`. -/
theorem avgReg_wedge_eq_on (hgood : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∀ᶠ j in atTop, ∀ u ∈ {u : ℂ | c₀ ≤ u.im},
      avgReg (wedgeField (lateralPart x) A Q) j u =
        avgReg (x + ofFun (profCut x A Q (c₀ / 2))) j u := by
  filter_upwards [radius_eventually_lt (by positivity : (0 : ℝ) < c₀ / 4)] with j hj u hu
  have hu' : u ∈ Hbar := show (0 : ℝ) ≤ u.im from hc₀.le.trans hu
  exact avgReg_wedge_eq_profCut hgood hraw hA hc₀ j u hu' (hu.trans (im_le_norm' u)) hj

/-- **Split on an interior measure.** -/
theorem evalReg_wedge_split (hgood : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) {c₀ : ℝ} (hc₀ : 0 < c₀) {K : Set ℂ} (hK : IsCompact K)
    (hKc : K ⊆ {u : ℂ | c₀ ≤ u.im}) {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν, u ∈ K) {L : ℝ}
    (hL : Tendsto (fun j => ∫ u, avgReg x j u ∂ν) atTop (𝓝 L)) :
    evalReg (wedgeField (lateralPart x) A Q) ν =
      evalReg x ν + ∫ u, profCut x A Q (c₀ / 2) u ∂ν := by
  have hg := continuous_profCut hgood hA Q (by positivity : (0 : ℝ) < c₀ / 2)
  rw [evalReg_congr_carried (avgReg_wedge_eq_on hgood hraw hA hc₀)
    (hν.mono fun u hu => hKc hu)]
  have hKH : K ⊆ Hbar := fun u hu => show (0 : ℝ) ≤ u.im from hc₀.le.trans (hKc hu)
  exact Thm18Asm.G1Z3.evalReg_add_ofFun_of_ae_z3 hgood.1 hg.continuousOn hK hKH one_pos
    (fun _ _ => rfl) hν hL

/-- **Split on an interior folded circle.** -/
theorem evalReg_wedge_fc (hgood : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) {c₀ : ℝ} (hc₀ : 0 < c₀) {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hp : c₀ + ρ ≤ p.im) :
    evalReg (wedgeField (lateralPart x) A Q) (foldedCircle p ρ) =
      F (p, ρ) + ∫ u, profCut x A Q (c₀ / 2) u ∂foldedCircle p ρ := by
  have hg := continuous_profCut hgood hA Q (by positivity : (0 : ℝ) < c₀ / 2)
  have hpH : p ∈ Hbar := show (0 : ℝ) ≤ p.im by linarith
  have hν : ∀ᵐ u ∂foldedCircle p ρ, u ∈ {u : ℂ | c₀ ≤ u.im} := by
    filter_upwards [ae_fc_mem_closedBall hpH hρ.le] with u hu
    have h := Complex.abs_im_le_norm (u - p)
    rw [← dist_eq_norm] at h
    have := mem_closedBall.1 hu
    rw [Complex.sub_im, abs_le] at h
    show c₀ ≤ u.im
    linarith [h.1]
  rw [evalReg_congr_carried (avgReg_wedge_eq_on hgood hraw hA hc₀) hν,
    (GoodSample.gs_add_ofFun hgood.1 hg.continuousOn).evalReg_fc_of_mem hpH hρ]

end G1Side
end QuantumZipper
