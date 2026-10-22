import HigherDimLQGMetric.Metric.WeylAxioms
import HigherDimLQGMetric.Shell.Defs

/-!
# Euclidean-ball diameters of a continuous metric (packet W3b, [S] Lemma 2.6)

`w3bBallDiam D z t = sup_{x,y ∈ B̄_t(z)} D(x,y) ∈ [0,∞]`, the quantity whose upper tail is
controlled in MA1 A8 (Steps 2–4). Contents:

* `w3b_exists_countable_ballDiam`: the supremum can be taken over one countable set (independent of
  `D`), since `D` is continuous; hence `w3b_measurable_ballDiam`: for a measurable family of metrics
  the ball diameter is measurable (so Markov's inequality applies; no measurability of internal
  metrics is needed);
* `w3b_ballDiam_le_of_weyl`: if `E = e^{ξf}·D'` (Weyl scaling) and `ξ f ≤ b` on an open `V`, then
  `sup_{B̄_t(z)} E ≤ e^b · sup_{x,y ∈ S} D'(x,y;V)` for every `S ⊇ B̄_t(z)` (the local Weyl
  comparison of MA1 A8, Step 1, against the internal metric that (E5) controls).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- The diameter `sup_{x,y ∈ B̄_t(z)} D(x,y)` of a closed Euclidean ball, in `[0,∞]`. -/
def w3bBallDiam (D : ContMetric d) (z : Rd d) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (x ∈ closedBall z t) (y ∈ closedBall z t), ENNReal.ofReal (D.1 (x, y))

theorem w3b_ofReal_le_ballDiam (D : ContMetric d) {z x y : Rd d} {t : ℝ}
    (hx : x ∈ closedBall z t) (hy : y ∈ closedBall z t) :
    ENNReal.ofReal (D.1 (x, y)) ≤ w3bBallDiam D z t :=
  le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)

/-- The ball diameter is a supremum over one countable set, for all continuous metrics at once. -/
theorem w3b_exists_countable_ballDiam (z : Rd d) (t : ℝ) :
    ∃ T : Set (Rd d), T.Countable ∧ ∀ D : ContMetric d,
      w3bBallDiam D z t = ⨆ (x ∈ T) (y ∈ T), ENNReal.ofReal (D.1 (x, y)) := by
  obtain ⟨T, hTS, hTc, hST⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (closedBall z t)).exists_countable_dense_subset
  refine ⟨T, hTc, fun D => le_antisymm ?_ ?_⟩
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    set c : ℝ≥0∞ := ⨆ (x ∈ T) (y ∈ T), ENNReal.ofReal (D.1 (x, y))
    have hclosed : IsClosed {p : Rd d × Rd d | ENNReal.ofReal (D.1 p) ≤ c} :=
      isClosed_le (ENNReal.continuous_ofReal.comp D.1.continuous) continuous_const
    have hsub : T ×ˢ T ⊆ {p : Rd d × Rd d | ENNReal.ofReal (D.1 p) ≤ c} := fun p hp => by
      show ENNReal.ofReal (D.1 (p.1, p.2)) ≤ c
      exact le_iSup₂_of_le p.1 hp.1 (le_iSup₂_of_le p.2 hp.2 le_rfl)
    have hcl : closure (T ×ˢ T) ⊆ {p : Rd d × Rd d | ENNReal.ofReal (D.1 p) ≤ c} :=
      hclosed.closure_subset_iff.2 hsub
    rw [closure_prod_eq] at hcl
    exact hcl ⟨hST hx, hST hy⟩
  · exact iSup₂_le fun x hx => iSup₂_le fun y hy => w3b_ofReal_le_ballDiam D (hTS hx) (hTS hy)

/-- Measurability of the ball diameter along a measurable family of continuous metrics. -/
theorem w3b_measurable_ballDiam {α : Type*} [MeasurableSpace α] {G : α → ContMetric d}
    (hG : Measurable G) (z : Rd d) (t : ℝ) : Measurable fun a => w3bBallDiam (G a) z t := by
  obtain ⟨T, hTc, hT⟩ := w3b_exists_countable_ballDiam (d := d) z t
  simp_rw [hT]
  refine Measurable.biSup T hTc fun x _ => Measurable.biSup T hTc fun y _ => ?_
  exact ((ContinuousMap.measurable_eval (x, y)).comp
    (measurable_subtype_coe.comp hG)).ennreal_ofReal

/-- **Local Weyl comparison** for ball diameters: if `E = e^{ξ f}·D'` and `ξ f ≤ b` on `V`, then
`sup_{B̄_t(z)} E ≤ e^b sup_{x,y ∈ S} D'(x,y;V)` for every `S ⊇ B̄_t(z)`. -/
theorem w3b_ballDiam_le_of_weyl {ξ b : ℝ} {f : C(Rd d, ℝ)} {D' E : ContMetric d}
    (hE : ∀ x y, weylScale ξ f D' x y = ENNReal.ofReal (E.1 (x, y))) {V S : Set (Rd d)}
    (hb : ∀ x ∈ V, ξ * f x ≤ b) {z : Rd d} {t : ℝ} (hS : closedBall z t ⊆ S) :
    w3bBallDiam E z t ≤ ENNReal.ofReal (Real.exp b) * ⨆ (x ∈ S) (y ∈ S), D'.internal V x y := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
  calc ENNReal.ofReal (E.1 (x, y)) = weylScale ξ f D' x y := (hE x y).symm
    _ ≤ weylScaleOn ξ f D' V x y := weylScale_le_weylScaleOn
    _ ≤ ENNReal.ofReal (Real.exp b) * D'.internal V x y := weylScaleOn_le_of_le hb
    _ ≤ ENNReal.ofReal (Real.exp b) * ⨆ (x ∈ S) (y ∈ S), D'.internal V x y := by
        gcongr
        exact le_iSup₂_of_le x (hS hx) (le_iSup₂_of_le y (hS hy) le_rfl)

end HigherDimLQGMetric
