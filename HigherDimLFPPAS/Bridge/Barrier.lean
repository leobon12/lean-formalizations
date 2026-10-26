import HigherDimLQGMetric.Metric.Internal

/-!
# Deterministic confinement and geodesic bridges

This module records the elementary barrier argument for internal distances of length metrics.
-/

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped ENNReal

namespace HigherDimLFPPAS.Bridge

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- If every path from `x` that reaches the Euclidean sphere has length at least `L`,
then pairs whose global distance is below `L` have the same global and internal distance
in the open ball. -/
theorem internal_eq_global_of_barrier
    (D : ContMetric d) (hD : D.IsLength) {R L : ℝ} {x y : Rd d}
    (hx : ‖x‖ < R) (hy : ‖y‖ < R) (hxy : D.1 (x,y) < L)
    (hbarrier : ∀ {P : ℝ → Rd d} {a b : ℝ}, a ≤ b →
      ContinuousOn P (Icc a b) → P a = x → ‖P b‖ = R →
        ENNReal.ofReal L ≤ D.len P a b) :
    D.internal (Metric.ball 0 R) x y = ENNReal.ofReal (D.1 (x,y)) := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hgap : 0 < L - D.1 (x,y) := sub_pos.mpr hxy
    have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
    let ε' : ℝ := min (ε : ℝ) ((L - D.1 (x,y)) / 2)
    have hε' : 0 < ε' := lt_min hεR (by positivity)
    have hε'ε : ε' ≤ (ε : ℝ) := min_le_left _ _
    have hεle : ENNReal.ofReal ε' ≤ ε := by
      calc
        ENNReal.ofReal ε' ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal hε'ε
        _ = ε := ENNReal.ofReal_coe_nnreal
    have hε'gap : ε' < L - D.1 (x,y) := by
      dsimp [ε']
      calc
        min (ε : ℝ) ((L - D.1 (x,y)) / 2) ≤ (L - D.1 (x,y)) / 2 := min_le_right _ _
        _ < L - D.1 (x,y) := by linarith
    have hLpos : 0 < L := lt_of_le_of_lt (D.nonneg x y) hxy
    obtain ⟨P, hPc, hP0, hP1, hPlen⟩ :=
      (ContMetric.isLength_iff_curves D).1 hD x y ε' hε'
    have hstay : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t‖ < R := by
      intro t ht
      by_cases ht0 : t = 0
      · rw [ht0, hP0]
        exact hx
      by_cases ht1 : t = 1
      · rw [ht1, hP1]
        exact hy
      by_contra hnot
      have htR : R ≤ ‖P t‖ := le_of_not_gt hnot
      have hPct : ContinuousOn P (Icc (0 : ℝ) t) :=
        hPc.mono (Icc_subset_Icc le_rfl ht.2)
      have hnorm : ContinuousOn (fun u : ℝ => ‖P u‖) (Icc (0 : ℝ) t) := hPct.norm
      have hRmem : R ∈ Icc (‖P 0‖) (‖P t‖) := by
        rw [hP0]
        exact ⟨by simpa using hx.le, htR⟩
      obtain ⟨s, hs, hseq⟩ := intermediate_value_Icc ht.1 hnorm hRmem
      have hbar := hbarrier (P := P) (a := 0) (b := s) hs.1
        (hPct.mono (Icc_subset_Icc le_rfl hs.2)) hP0 hseq
      have hlen : D.len P 0 t ≤ D.len P 0 1 := by
        change curveLength (D.pt ∘ P) 0 t ≤ curveLength (D.pt ∘ P) 0 1
        exact curveLength_mono (D.pt ∘ P) le_rfl ht.2
      have hlen' : D.len P 0 s ≤ D.len P 0 t := by
        change curveLength (D.pt ∘ P) 0 s ≤ curveLength (D.pt ∘ P) 0 t
        exact curveLength_mono (D.pt ∘ P) le_rfl hs.2
      have hadd : ENNReal.ofReal (D.1 (x,y)) + ENNReal.ofReal ε' =
          ENNReal.ofReal (D.1 (x,y) + ε') :=
        (ENNReal.ofReal_add (D.nonneg x y) hε'.le).symm
      have hsum : D.1 (x,y) + ε' < L := by linarith
      have hlt : ENNReal.ofReal (D.1 (x,y) + ε') < ENNReal.ofReal L :=
        (ENNReal.ofReal_lt_ofReal_iff hLpos).2 hsum
      have htop : ENNReal.ofReal L ≤ ENNReal.ofReal (D.1 (x,y) + ε') := by
        calc
          ENNReal.ofReal L ≤ D.len P 0 s := hbar
          _ ≤ D.len P 0 t := hlen'
          _ ≤ D.len P 0 1 := hlen
          _ ≤ ENNReal.ofReal (D.1 (x,y)) + ENNReal.ofReal ε' := hPlen
          _ = ENNReal.ofReal (D.1 (x,y) + ε') := hadd
      exact (not_le_of_gt hlt) htop
    have hmap : MapsTo P (Icc (0 : ℝ) 1) (Metric.ball 0 R) := by
      intro t ht
      simpa only [Metric.mem_ball, dist_zero_right] using hstay t ht
    have hlen := D.internal_le_len (U := Metric.ball 0 R) (P := P)
      zero_le_one hPc hmap
    rw [hP0, hP1] at hlen
    calc
      D.internal (Metric.ball 0 R) x y ≤ D.len P 0 1 := hlen
      _ ≤ ENNReal.ofReal (D.1 (x,y)) + ENNReal.ofReal ε' := hPlen
      _ = ENNReal.ofReal ε' + ENNReal.ofReal (D.1 (x,y)) := add_comm _ _
      _ ≤ ε + ENNReal.ofReal (D.1 (x,y)) := add_le_add_left hεle _
      _ = ENNReal.ofReal (D.1 (x,y)) + ε := add_comm _ _
  · exact D.ofReal_le_internal (Metric.ball 0 R) x y

end HigherDimLFPPAS.Bridge
