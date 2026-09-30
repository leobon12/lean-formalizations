import QuantumZipper.Proofs.Thm18.G2DisintPhi
import QuantumZipper.Proofs.Thm18.G2DisintLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `x` side: the bump in region 1 and its geometry

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66) puts the bump `φ₁` in `U₁`, away from the
root. For the index `i` (region 1 = `B(t₁, r₁)`) and the margin `m` we take the radial bump
`g2Phi p R` with `m' = min m r₁`, `p = t₁ + r₁ − m'/2`, `R = m'/4`:

* it is admissible for `G2BumpDecompStmt` (`g2xPhi_bump_hyps`): support in `B(t₁, r₁) ⊆ B(0, 1)`;
* a root `x` with margin `m` satisfies `x + R < p − R` (`g2x_margin_left`), so `φ` vanishes on
  `(−∞, x + R]` and on the disc `B(x, R)`; the bump lies left of `0` (`g2x_bump_neg`);
* the boundary measure of `h` is `e^{γαφ/2}` times that of `h₀` (`g2_ae_g3Hν_eq`), hence equal to
  it off the bump.
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The margin used for the bump. -/
def g2xM' (i : G3Idx) (m : ℝ) : ℝ := min m i.r₁
/-- Centre of the bump. -/
def g2xP (i : G3Idx) (m : ℝ) : ℝ := i.t₁ + i.r₁ - g2xM' i m / 2
/-- Radius of the bump. -/
def g2xR (i : G3Idx) (m : ℝ) : ℝ := g2xM' i m / 4

theorem g2xM'_pos (i : G3Idx) {m : ℝ} (hm : 0 < m) : 0 < g2xM' i m := lt_min hm i.r₁_pos

theorem g2xR_pos (i : G3Idx) {m : ℝ} (hm : 0 < m) : 0 < g2xR i m := by
  unfold g2xR; linarith [g2xM'_pos i hm]

theorem g2x_t₁r₁ (i : G3Idx) : i.t₁ + i.r₁ = -(3 / 4) * i.η := by
  unfold G3Idx.t₁ G3Idx.r₁; ring

theorem g2x_bump_neg (i : G3Idx) {m : ℝ} (hm : 0 < m) : g2xP i m + g2xR i m < 0 := by
  have := g2xM'_pos i hm; have := i.hη
  unfold g2xP g2xR; rw [g2x_t₁r₁]; linarith

theorem g2x_bump_sub (i : G3Idx) {m : ℝ} (hm : 0 < m) :
    closedBall (g2xP i m : ℂ) (g2xR i m) ⊆ ball (i.t₁ : ℂ) i.r₁ := by
  intro z hz
  rw [mem_closedBall, Complex.dist_eq] at hz
  rw [mem_ball, Complex.dist_eq]
  have h1 : g2xM' i m ≤ i.r₁ := min_le_right _ _
  have h2 := g2xM'_pos i hm
  calc ‖z - i.t₁‖ ≤ ‖z - g2xP i m‖ + ‖((g2xP i m : ℂ) - i.t₁)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < i.r₁ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by unfold g2xP; linarith)]
        unfold g2xP g2xR at *; linarith

theorem g2x_ball_sub_unit (i : G3Idx) : ball (i.t₁ : ℂ) i.r₁ ⊆ ball (0 : ℂ) 1 := by
  intro z hz
  rw [mem_ball, Complex.dist_eq] at hz
  rw [mem_ball, dist_zero_right]
  have h := i.inUnit₁
  have h2 : |i.t₁| + i.r₁ < 1 := by
    have := i.hη; have := i.hηδ; have := i.hδ
    rw [abs_of_neg (by unfold G3Idx.t₁; linarith)]; unfold G3Idx.t₁ G3Idx.r₁; linarith
  calc ‖z‖ ≤ ‖z - i.t₁‖ + ‖(i.t₁ : ℂ)‖ := norm_le_norm_sub_add _ _
    _ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith

/-- The bump of the `x` side. -/
def g2xφ (i : G3Idx) (m : ℝ) : ℂ → ℝ := g2Phi (g2xP i m) (g2xR i m)

theorem g2xφ_bump_hyps (i : G3Idx) {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g2xφ i m) ∧ HasCompactSupport (g2xφ i m) ∧
      tsupport (g2xφ i m) ⊆ ball (0 : ℂ) 1 ∧
      (∀ z, g2xφ i m (starRingEnd ℂ z) = g2xφ i m z) ∧ (∃ z, g2xφ i m z ≠ 0) :=
  ⟨contDiff_g2Phi _ _, hasCompactSupport_g2Phi (g2xR_pos i hm).le,
    ((tsupport_g2Phi_subset (g2xR_pos i hm).le).trans (g2x_bump_sub i hm)).trans
      (g2x_ball_sub_unit i),
    g2Phi_conj _ _, ⟨_, g2Phi_center_ne_zero (g2xR_pos i hm)⟩⟩

theorem g2xφ_zero_off (i : G3Idx) {m : ℝ} (hm : 0 < m) {z : ℂ}
    (hz : z ∉ ball (i.t₁ : ℂ) i.r₁) : g2xφ i m z = 0 := by
  by_contra h
  exact hz (g2x_bump_sub i hm (tsupport_g2Phi_subset (g2xR_pos i hm).le
    (subset_tsupport _ (Function.mem_support.2 h))))

/-- A root with margin `m` lies at distance `> 2R` left of the bump centre. -/
theorem g2x_margin_left (i : G3Idx) {m x : ℝ} (hm : 0 < m) (hx : |x - i.t₁| + m < i.r₁) :
    x + g2xR i m < g2xP i m - g2xR i m := by
  have h1 : g2xM' i m ≤ m := min_le_left _ _
  have h2 := g2xM'_pos i hm
  have h3 := (le_abs_self (x - i.t₁))
  unfold g2xP g2xR; linarith

/-- `φ` vanishes on the reals left of the bump. -/
theorem g2xφ_real_left (i : G3Idx) {m t : ℝ} (hm : 0 < m) (ht : t ≤ g2xP i m - g2xR i m) :
    g2xφ i m (t : ℂ) = 0 := by
  refine g2Phi_eq_zero (g2xR_pos i hm).le ?_
  have hR := g2xR_pos i hm
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith

/-- `φ` vanishes on the disc of radius `R` around a margin root. -/
theorem g2xφ_ball_root (i : G3Idx) {m x : ℝ} (hm : 0 < m) (hx : |x - i.t₁| + m < i.r₁) :
    ∀ z ∈ ball (x : ℂ) (g2xR i m), g2xφ i m z = 0 := by
  intro z hz
  refine g2Phi_eq_zero (g2xR_pos i hm).le ?_
  rw [mem_ball, Complex.dist_eq] at hz
  have hl := g2x_margin_left i hm hx
  have hR := g2xR_pos i hm
  have : ‖((g2xP i m : ℂ) - x)‖ = g2xP i m - x := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have ht := norm_sub_le_norm_sub_add_norm_sub (g2xP i m : ℂ) z x
  rw [norm_sub_rev (g2xP i m : ℂ) z] at ht
  linarith

/-- The resampled field reads like `h + (a − α) φ` (same regularized averages). -/
theorem avgReg_g2Field_eq_add (γ : ℝ) (φ : ℂ → ℝ) (α : Ω₀ → ℝ) (ω : Ω₀) (a : ℝ) :
    avgReg (g2Field γ φ (g2Y φ α ω) a) =
      avgReg (normField γ gffBase.X ω + ofFun fun z => (a - α ω) * φ z) := by
  funext k z
  unfold avgReg
  congr 1
  funext n
  rw [g2Field_sub γ φ _ a (α ω), g2Field_Y_prob γ φ α ω _
    (D3Plus.isAdmissibleH_foldedCircle' _ (radius_pos k))]
  simp only [Pi.add_apply, ofFun, integral_const_mul]

theorem zoomLaw_g2Field_eq_add (γ : ℝ) (φ : ℂ → ℝ) (α : Ω₀ → ℝ) (ω : Ω₀) (a C x : ℝ) :
    zoomLaw γ C (g2Field γ φ (g2Y φ α ω) a) x =
      zoomLaw γ C (normField γ gffBase.X ω + ofFun fun z => (a - α ω) * φ z) x := by
  unfold zoomLaw zoomField
  rw [Factorization.translate_congr (avgReg_g2Field_eq_add γ φ α ω a)]

/-- **Node (zoom locality; Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 66: the zoom at
the root does not see a bump away from it).** A.s., for every root `x` and every continuous `φ`
vanishing on `B(x, r)`, adding `b φ` to `h` does not change the event `{zoom at x ∈ s}` once `C`
is large. Deterministic part: `zoomLaw` reads `h` only on `B(x, R_s · scaleProxy)`; probabilistic
part: `scaleProxy (zoomField γ C h x) → 0` as `C → ∞` (the area measure charges every ball). -/
def G2ZoomLocStmt (γ : ℝ) : Prop :=
  ∀ s ∈ lawCyl, ∀ φ : ℂ → ℝ, Continuous φ → ∀ r : ℝ, 0 < r →
    ∀ᵐ ω ∂gffBase.P, ∀ x : ℝ, (∀ z ∈ ball (x : ℂ) r, φ z = 0) → ∀ b : ℝ,
      ∀ᶠ C in (atTop : Filter ℝ),
        (zoomLaw γ C (normField γ gffBase.X ω + ofFun fun z => b * φ z) x ∈ s ↔
          zoomLaw γ C (normField γ gffBase.X ω) x ∈ s)

end Thm18Asm
end QuantumZipper
