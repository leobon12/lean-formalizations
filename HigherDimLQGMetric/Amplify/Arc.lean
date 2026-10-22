import HigherDimLQGMetric.Amplify.Globalize

/-! Turning a short witness into a confined simple arc. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry
open scoped ENNReal

variable {d : ℕ}

/-- Once the collar dominates both endpoint distances, replace a possibly
self-intersecting witness by a simple `Dt` geodesic inside the trial annulus.
The upper `D` length bound is kept in the comparison form useful for later
normalization. -/
theorem amplify_short_witness_to_arc (D Dt : ContMetric d)
    (hD : D.IsLength) [ProperSpace D.Space]
    (hDt : Dt.IsLength) [ProperSpace Dt.Space]
    {s cs C c : ℝ} (hs : 0 < s) (w : Rd d)
    {u v : Rd d} (hu : u ∈ annCl w s (2 * s)) (hv : v ∈ annCl w s (2 * s))
    (huv : u ≠ v)
    {P : ℝ → Rd d} (hP0 : P 0 = u) (hP1 : P 1 = v)
    (hcomp : ∀ x y, cs * D.1 (x, y) ≤ Dt.1 (x, y))
    (hcoll : ENNReal.ofReal C <
      setDistIn D (ann w (s / 2) (5 * s)) (annCl w s (2 * s))
        (Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s)))
    (hshortD : D.1 (u, v) < C)
    (hshortDt : ENNReal.ofReal (Dt.1 (u, v)) <
      ENNReal.ofReal cs * ENNReal.ofReal C)
    {a L : ℝ≥0∞}
    (hlower : a ≤ D.internal (ann w (3 * s / 4) (3 * s)) u v)
    (hratio : Dt.len P 0 1 ≤ ENNReal.ofReal c *
      D.internal (ann w (3 * s / 4) (3 * s)) u v)
    (hupper : Dt.len P 0 1 ≤ L) :
    ∃ γ : ℝ → Rd d, IsSimpleArc γ ∧ γ 0 = u ∧ γ 1 = v ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ ann w (3 * s / 4) (3 * s)) ∧
      Dt.len γ 0 1 ≤ ENNReal.ofReal c * ENNReal.ofReal (D.1 (u, v)) ∧
      a ≤ ENNReal.ofReal (D.1 (u, v)) ∧
      ENNReal.ofReal cs * D.len γ 0 1 ≤ L := by
  have hglobal := amplify_global_eq_internal_of_collar D hD hs w hu hv hcoll hshortD
  obtain ⟨γ, hγ, hγ0, hγ1, hγlen⟩ :=
    amplify_exists_simple_geodesic Dt hDt huv
  have hmin : ENNReal.ofReal (Dt.1 (u, v)) ≤ Dt.len P 0 1 := by
    rw [← Dt.edist_pt, ← hP0, ← hP1]
    exact edist_le_curveLength (Dt.pt ∘ P) zero_le_one
  have hrange : ∀ t ∈ Icc (0 : ℝ) 1,
      γ t ∈ ann w (3 * s / 4) (3 * s) :=
    amplify_path_stays_trial_annulus D Dt hs w hu hγ.1 hγ0 hcomp hcoll
      (hγlen.trans_lt hshortDt)
  have hlenD := ContMetric.mul_len_le_of_le (D := D) (E := Dt) hcomp γ 0 1
  refine ⟨γ, hγ, hγ0, hγ1, hrange, ?_, ?_, ?_⟩
  · calc
      Dt.len γ 0 1 = ENNReal.ofReal (Dt.1 (u, v)) := hγlen
      _ ≤ Dt.len P 0 1 := hmin
      _ ≤ ENNReal.ofReal c * D.internal (ann w (3 * s / 4) (3 * s)) u v := hratio
      _ = ENNReal.ofReal c * ENNReal.ofReal (D.1 (u, v)) := by rw [hglobal]
  · rwa [hglobal] at hlower
  · exact hlenD.trans (hγlen ▸ hmin.trans hupper)

end HigherDimLQGMetric
