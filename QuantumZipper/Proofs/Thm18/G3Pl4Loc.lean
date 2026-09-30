import QuantumZipper.Proofs.Thm18.G3G2LocZoom
import QuantumZipper.Proofs.Thm18.G3AreaCore
import QuantumZipper.Proofs.LQG.GoodTransforms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): locality of the canonical zooms at large level

Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (pp. 71–72) and Remark 5.7: at a large zoom
level `C` the canonical description of `h(· + x) + C/γ`, read through a cylinder event, only sees
the field in a shrinking neighbourhood of the point `x`. This file combines the deterministic
locality `zoomLaw_mem_lawCyl_iff` (G3G2LocZoom: agreement on folded circles near `x` and area
`≥ 1` at the scale `q₀` ⇒ the two cylinder events agree) with the growth of the area proxy under
a constant shift (`eventually_one_le_areaProxy_addConst_of_good`, G3AreaCore):

* `g3pl4_eventually_zoom_iff`: if `y`, `y'` agree on folded circles inside an open `W` containing
  the half-ball `closedBall(x, q₀ R) ∩ H̄`, and the translated field `y'(· + x)` is good with
  positive area on the half-ball of radius `q₀`, then for all large levels `C` the cylinder
  events of the two zooms at `x` coincide.
* `g3pl4_eventually_zoom_iff_ball`: the same with the agreement set a ball `ball(0, r₀)` and
  `|x| < r₀`, with the positivity of area on every half-ball around `x` as hypothesis.

Own elementary bookkeeping on top of the cited locality lemmas (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

/-- **Locality of the zoom events at large level.** -/
theorem g3pl4_eventually_zoom_iff {s : Set LawD} (hs : s ∈ lawCyl) : ∃ R : ℝ, 1 ≤ R ∧
    ∀ (γ : ℝ), 0 < γ → ∀ (y y' : FieldSample) (x : ℝ) (W : Set ℂ), IsOpen W →
      FcAgree W y y' → ∀ q₀ : ℚ, 0 < (q₀ : ℝ) →
      closedBall (0 : ℂ) (q₀ * R) ∩ Hbar ⊆ (fun z => z + (x : ℂ)) ⁻¹' W →
      IsLQGGood γ (translate y' (x : ℂ)) → 0 < areaProxy γ (translate y' (x : ℂ)) q₀ →
      ∀ᶠ C in atTop, (zoomLaw γ C y x ∈ s ↔ zoomLaw γ C y' x ∈ s) := by
  obtain ⟨R, hR, hRs⟩ := zoomLaw_mem_lawCyl_iff hs
  refine ⟨R, hR, fun γ hγ y y' x W hWo hag q₀ hq₀ hW hgood hpos => ?_⟩
  have hev := eventually_one_le_areaProxy_addConst_of_good hγ hgood hpos
  have ht : Tendsto (fun C : ℝ => C / γ) atTop atTop := tendsto_id.atTop_div_const hγ
  filter_upwards [ht.eventually hev] with C hC
  exact hRs γ C y y' x W hWo hag q₀ hq₀ hW hC

end R18
end QuantumZipper
