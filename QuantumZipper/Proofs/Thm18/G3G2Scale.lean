import QuantumZipper.Proofs.Thm18.G3G2LocZoom

/-!
# The scale statement from a geometric and an area statement

`G3ScaleStmt γ` (the probabilistic input of the locality of the zoom, `G3G2LocZoom.lean`) splits
along the order of the limits of `g3Filter` (first `C → ∞`, then `η → 0`, then `δ → 0`):

* `G3GeoStmt γ` (no zoom involved): for small `δ`, then small `η`, there is a rational margin
  `m > 0` such that, with Palm probability close to `1`, the Palm point `x` is at distance `> m`
  from the edge of region 1, i.e. `|x − t₁| + m < r₁` (and `|R(x) − t₂| + m < r₂` for region 2).
  For `x` this needs `η → 0` (region 1 covers `(−δ − η/4, −3η/4)` and `x ∈ [−δ, 0]`); for `R(x)`
  it needs `δ → 0` as well (region 2 ends at `1/2 + η/4`; Sheffield p. 71: "We may choose δ
  small enough so that with high probability R(x) ∈ B₁(0)").
* `G3AreaStmt γ` (fixed `δ, η`, `C → ∞`): for every rational `q > 0`, the zoomed full field at
  `x` (and at `R(x)`) has `areaProxy ≥ 1` on the half-ball of radius `q` with Palm probability
  `→ 1` as `C → ∞` (the zoomed area is `e^C` times the area of `h` near `x`, which is positive).

`g3ScaleStmt_of_geo_area : G3GeoStmt γ → G3AreaStmt γ → G3ScaleStmt γ` (union bound; own
elementary bookkeeping, AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm

theorem bad_subset_geo_union_area {α : Type*} (pt : α → ℝ) (ar : α → ℚ → ℝ≥0∞) (t r m R : ℝ)
    (q : ℚ) (hq : 0 < (q : ℝ)) (hqm : (q : ℝ) * R < m) :
    {p | ¬ ∃ q' : ℚ, 0 < (q' : ℝ) ∧
      closedBall (0 : ℂ) (q' * R) ∩ Hbar ⊆ (fun z => z + (pt p : ℂ)) ⁻¹' ball (t : ℂ) r ∧
      1 ≤ ar p q'} ⊆ {p | r ≤ |pt p - t| + m} ∪ {p | ar p q < 1} := by
  intro p hp
  by_contra hc
  simp only [mem_union, mem_ofPred_eq, not_or, not_le, not_lt] at hc
  refine hp ⟨q, hq, fun u hu => ?_, hc.2⟩
  have hu1 := hu.1
  rw [mem_closedBall, dist_zero_right] at hu1
  show u + (pt p : ℂ) ∈ ball (t : ℂ) r
  rw [mem_ball, dist_eq_norm]
  calc ‖u + (pt p : ℂ) - t‖ = ‖u + ((pt p - t : ℝ) : ℂ)‖ := by push_cast; ring_nf
    _ ≤ ‖u‖ + ‖((pt p - t : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = ‖u‖ + |pt p - t| := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ < r := by linarith

/-- The union bound along `g3Filter`. -/
theorem tendsto_bad_of_geo_area {α : Type*} [MeasurableSpace α] {P : G3Idx → Measure α}
    [∀ i, IsFiniteMeasure (P i)] (pt : G3Idx → α → ℝ) (t r : G3Idx → ℝ)
    (ar : G3Idx → α → ℚ → ℝ≥0∞) {R : ℝ} (hR : 1 ≤ R)
    (hG : ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ m : ℚ, 0 < (m : ℝ) ∧
      ∀ i : G3Idx, i.1.1 = δ → i.1.2.1 = η → (P i).real {p | r i ≤ |pt i p - t i| + m} < ε)
    (hA : ∀ q : ℚ, 0 < (q : ℝ) → ∀ ε > 0, ∀ δ η : ℝ, ∀ᶠ C in (atTop : Filter ℝ),
      ∀ i : G3Idx, i.1 = (δ, η, C) → (P i).real {p | ar i p q < 1} < ε) :
    Tendsto (fun i => (P i).real {p | ¬ ∃ q : ℚ, 0 < (q : ℝ) ∧
      closedBall (0 : ℂ) (q * R) ∩ Hbar ⊆ (fun z => z + (pt i p : ℂ)) ⁻¹' ball (t i : ℂ) (r i) ∧
      1 ≤ ar i p q}) g3Filter (𝓝 0) := by
  rw [tendsto_g3Filter_iff]
  intro ε hε
  filter_upwards [hG (ε / 2) (half_pos hε)] with δ hδ
  filter_upwards [hδ] with η hη
  obtain ⟨m, hm, hgeo⟩ := hη
  have hR0 : 0 < R := by linarith
  obtain ⟨q, hq0, hqm⟩ := exists_rat_btwn (div_pos hm hR0)
  have hq0' : 0 < (q : ℝ) := by exact_mod_cast hq0
  have hqR : (q : ℝ) * R < m := by rwa [lt_div_iff₀ hR0] at hqm
  filter_upwards [hA q hq0' (ε / 2) (half_pos hε) δ η] with C hC i hi
  have hiδ : i.1.1 = δ := by rw [hi]
  have hiη : i.1.2.1 = η := by rw [hi]
  rw [sub_zero, abs_of_nonneg measureReal_nonneg]
  calc _ ≤ (P i).real ({p | r i ≤ |pt i p - t i| + m} ∪ {p | ar i p q < 1}) :=
        measureReal_mono (bad_subset_geo_union_area (pt i) (ar i) (t i) (r i) m R q hq0' hqR)
    _ ≤ (P i).real {p | r i ≤ |pt i p - t i| + m} + (P i).real {p | ar i p q < 1} :=
        measureReal_union_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hgeo i hiδ hiη) (hC i hi)
    _ = ε := add_halves ε

/-- **Geometric input**: the Palm point and its length partner stay away from the region edges. -/
def G3GeoStmt (γ : ℝ) : Prop :=
  (∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ m : ℚ, 0 < (m : ℝ) ∧
    ∀ i : G3Idx, i.1.1 = δ → i.1.2.1 = η →
      (g3PalmLaw γ i).real {p | i.r₁ ≤ |g3X γ i p - i.t₁| + m} < ε) ∧
  (∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ m : ℚ, 0 < (m : ℝ) ∧
    ∀ i : G3Idx, i.1.1 = δ → i.1.2.1 = η →
      (g3PalmLaw γ i).real {p | i.r₂ ≤ |g3R γ i p - i.t₂| + m} < ε)

/-- **Area input**: at fixed `δ, η`, the zoomed area of every fixed half-ball tends to infinity in
Palm probability as `C → ∞`, at `x` and at `R(x)`. -/
def G3AreaStmt (γ : ℝ) : Prop :=
  ∀ q : ℚ, 0 < (q : ℝ) → ∀ ε > 0, ∀ δ η : ℝ, ∀ᶠ C in (atTop : Filter ℝ),
    ∀ i : G3Idx, i.1 = (δ, η, C) →
      (g3PalmLaw γ i).real {p | areaProxy γ
        (zoomField γ i.C (normField γ gffBase.X p.1) (g3X γ i p)) q < 1} < ε ∧
      (g3PalmLaw γ i).real {p | areaProxy γ
        (zoomField γ i.C (normField γ gffBase.X p.1) (g3R γ i p)) q < 1} < ε

theorem g3ScaleStmt_of_geo_area {γ : ℝ} (hG : G3GeoStmt γ) (hA : G3AreaStmt γ) :
    G3ScaleStmt γ := fun _R hR =>
  ⟨tendsto_bad_of_geo_area (P := g3PalmLaw γ) (fun i => g3X γ i) (fun i => i.t₁)
      (fun i => i.r₁) (fun i p q => areaProxy γ
        (zoomField γ i.C (normField γ gffBase.X p.1) (g3X γ i p)) q) hR hG.1
      fun q hq ε hε δ η => (hA q hq ε hε δ η).mono fun _ h i hi => (h i hi).1,
    tendsto_bad_of_geo_area (P := g3PalmLaw γ) (fun i => g3R γ i) (fun i => i.t₂)
      (fun i => i.r₂) (fun i p q => areaProxy γ
        (zoomField γ i.C (normField γ gffBase.X p.1) (g3R γ i p)) q) hR hG.2
      fun q hq ε hε δ η => (hA q hq ε hε δ η).mono fun _ h i hi => (h i hi).2⟩

/-- **G2 for the concrete scheme from the full-field G2, geometry and area.** -/
theorem g2ConcreteStmt_of_inputs {γ : ℝ} (hG : G3GeoStmt γ) (hA : G3AreaStmt γ)
    (hF : G2FullStmt γ) : G2ConcreteStmt γ :=
  g2ConcreteStmt_of_loc (g3LocStmt_of_scale (g3ScaleStmt_of_geo_area hG hA)) hF

end Thm18Asm
end QuantumZipper
