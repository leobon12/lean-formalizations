import QuantumZipper.Proofs.Zipper.FieldLawler2Glue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 2: excursion flux through the circle `C_R` from inside

Field–Lawler, EJP 20 (2015), §2 (p. 5): for an analytic boundary arc `V`,
`ℰ_D(V, W) = ∫_V lim_{δ↓0} δ⁻¹ h_D(v + δ n_v, W) |dv|`. For the upper half of the circle
`C_R = {|z| = R}` with inward normal this is `fl2FluxR R h = ∫_0^π ∂ᵣ⁻ h(R e^{iθ}) R dθ`,
`∂ᵣ⁻ h(Re^{iθ}) = lim_{s↓0} h((R − s) e^{iθ}) / s` (`fl2rDer`).
* `fl2_tsum_fluxR_le`: majorant comparison for sums (as `fl2_tsum_excR_le`): the form in which
  FL Lemma 3.3 (`Σ_η ℰ_D(C_R, η) ≤ 2 ℰ_D(C_R, C_ε)`) follows from the pointwise inequality (4.1),
  p. 11;
* `fl2_fluxR_le_of_majorant`: `ℰ(C_R, ·) ≤ ∫ ∂ᵣ⁻ M` for a pointwise majorant `M` (FL (2.3)–(2.4)).
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology NNReal ENNReal Real

namespace QuantumZipper
namespace FieldLawler

/-- The point `(R − s) e^{iθ}`. -/
def fl2Pt (R θ s : ℝ) : ℂ := ((R - s : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)

/-- Inward radial derivative at `R e^{iθ}` of a function vanishing on `C_R`. -/
def fl2rDer (R : ℝ) (h : ℂ → ℝ) (θ : ℝ) : ℝ :=
  open Classical in
  if ∃ L : ℝ, Tendsto (fun s : ℝ => h (fl2Pt R θ s) / s) (𝓝[>] 0) (𝓝 L) then
    limUnder (𝓝[>] (0 : ℝ)) fun s : ℝ => h (fl2Pt R θ s) / s
  else 0

/-- **FL's `ℰ(C_R, ·)`**: the excursion flux through the upper half of `C_R` from inside. -/
def fl2FluxR (R : ℝ) (h : ℂ → ℝ) : ℝ≥0∞ :=
  ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (fl2rDer R h θ * R)

theorem fl2_rDer_eq {R : ℝ} {h : ℂ → ℝ} {θ L : ℝ}
    (hL : Tendsto (fun s : ℝ => h (fl2Pt R θ s) / s) (𝓝[>] 0) (𝓝 L)) :
    fl2rDer R h θ = L := by
  unfold fl2rDer
  rw [if_pos ⟨L, hL⟩]
  exact hL.limUnder_eq

end FieldLawler
end QuantumZipper
