import HigherDimLQGMetric.Events.ConfigLocal
import HigherDimLQGMetric.Select.MetricBorel
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Borel measurability of the compact-pair ratio event

The strict ratio condition is written as a countable union of closed
conditions. Compactness of the pair domain makes each projection closed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Topology Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

private abbrev RatioData (d : ℕ) :=
  C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ) × ℝ

private def ratioPairs (R : ℝ) : Set (Rd d × Rd d) :=
  closedBall (0 : Rd d) (2 * R) ×ˢ closedBall (0 : Rd d) (2 * R)

private theorem compact_ratioPairs (R : ℝ) : IsCompact (ratioPairs (d := d) R) :=
  (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)

private def ratioClosed (u β R : ℝ) (n : ℕ) :
    Set (RatioData d × ratioPairs (d := d) R) :=
  {p | β * R ≤ ‖p.2.1.1 - p.2.1.2‖ ∧
    β * p.1.2.2 ≤ p.1.1 (p.2.1) ∧
    p.1.1 (p.2.1) ≤ β⁻¹ * p.1.2.2 ∧
    u * p.1.1 (p.2.1) + 1 / (n + 1 : ℝ) ≤ p.1.2.1 (p.2.1)}

private theorem isClosed_ratioClosed (u β R : ℝ) (n : ℕ) :
    IsClosed (ratioClosed (d := d) u β R n) := by
  have hxy : Continuous fun p : RatioData d × ratioPairs (d := d) R => p.2.1 :=
    continuous_subtype_val.comp continuous_snd
  have hA : Continuous fun p : RatioData d × ratioPairs (d := d) R => p.1.1 (p.2.1) := by
    exact continuous_eval.comp
      (((continuous_fst.comp continuous_fst).prodMk hxy))
  have hB : Continuous fun p : RatioData d × ratioPairs (d := d) R => p.1.2.1 (p.2.1) := by
    exact continuous_eval.comp
      (((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk hxy))
  have hs : Continuous fun p : RatioData d × ratioPairs (d := d) R => p.1.2.2 := by
    fun_prop
  unfold ratioClosed
  exact (isClosed_le continuous_const ((hxy.fst.sub hxy.snd).norm)).inter
    ((isClosed_le (continuous_const.mul hs) hA).inter
      ((isClosed_le hA (continuous_const.mul hs)).inter
        (isClosed_le ((continuous_const.mul hA).add continuous_const) hB)))

private theorem isClosed_ratioProjection (u β R : ℝ) (n : ℕ) :
    IsClosed (Prod.fst '' ratioClosed (d := d) u β R n) := by
  letI : CompactSpace (ratioPairs (d := d) R) :=
    isCompact_iff_compactSpace.mp (compact_ratioPairs R)
  exact isClosedMap_fst_of_compactSpace _ (isClosed_ratioClosed u β R n)

private def ratioDataEvent (u β R : ℝ) : Set (RatioData d) :=
  {p | ∃ x ∈ closedBall (0 : Rd d) (2 * R),
    ∃ y ∈ closedBall (0 : Rd d) (2 * R),
      β * R ≤ ‖x - y‖ ∧ β * p.2.2 ≤ p.1 (x, y) ∧
      p.1 (x, y) ≤ β⁻¹ * p.2.2 ∧ u * p.1 (x, y) < p.2.1 (x, y)}

private theorem measurableSet_ratioDataEvent (u β R : ℝ) :
    MeasurableSet (ratioDataEvent (d := d) u β R) := by
  have he : ratioDataEvent (d := d) u β R =
      ⋃ n : ℕ, Prod.fst '' ratioClosed (d := d) u β R n := by
    ext p
    constructor
    · rintro ⟨x, hx, y, hy, hsep, hlo, hhi, hstrict⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hstrict)
      refine mem_iUnion.mpr ⟨n, ?_⟩
      refine ⟨(p, ⟨(x, y), ⟨hx, hy⟩⟩), ?_, rfl⟩
      exact ⟨hsep, hlo, hhi, by dsimp; linarith⟩
    · intro hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      rcases hn with ⟨q, hq, rfl⟩
      rcases q with ⟨p, ⟨⟨x, y⟩, hxy⟩⟩
      rcases hq with ⟨hsep, hlo, hhi, hratio⟩
      refine ⟨x, hxy.1, y, hxy.2, hsep, hlo, hhi, ?_⟩
      have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
      linarith
  rw [he]
  exact MeasurableSet.iUnion fun n => (isClosed_ratioProjection u β R n).measurableSet

/-- The ratio event of Definition 5.3 is Borel in the field. -/
theorem measurableSet_GEvent {ξ Q u β R : ℝ}
    {A B : DistRd d → ContMetric d} (hA : Measurable A) (hB : Measurable B) :
    MeasurableSet (GEvent A B ξ Q u β R) := by
  let f : DistRd d → RatioData d := fun g =>
    ((A g).1, (B g).1, sNorm ξ Q g R 0)
  have hf : Measurable f := by
    exact (measurable_subtype_coe.comp hA).prodMk
      ((measurable_subtype_coe.comp hB).prodMk
        (measurable_const.mul (Real.measurable_exp.comp
          (measurable_const.mul (measurable_sphereAvg_left R 0)))))
  have he : GEvent A B ξ Q u β R = f ⁻¹' ratioDataEvent u β R := by
    ext g
    rfl
  rw [he]
  exact hf (measurableSet_ratioDataEvent u β R)

end HigherDimLQGMetric
