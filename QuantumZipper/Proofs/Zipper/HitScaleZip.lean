import QuantumZipper.Proofs.Zipper.LocHitScalePStar
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Section5.Prop16LocalRule

/-!
# E6-HITSCALEZIP: `HitScaleZipStmt` from all-times goodness and three length/area nodes

Theorem 1.3, node E6 (`LocHitScalePStar.lean`). `HitScaleZipStmt` asks, for a `P_*` sample
`y = (Y, √κ B')` and `ℓ > 0`, almost surely: global boundary limits of the unzipped fields `x_q`
at the positive rational times, a monotone left length `L⁻`, reaching `ℓ` in finite time,
`τ = tHit γ ℓ y > 0`, an area limit of `x_τ` on `ℍ` and `scaleParam γ x_τ > 0`.

Reduction (`hitScaleZipStmt_of`):

* boundary and area limits at every time `t ≥ 0` (hence at rational times and at the random
  time `τ ≥ 0`) from `WedgeUnzip.PStarGoodAllStmt` (itself reduced to the D29 cores
  PStarRealize + W-G + W-X + W-C by `WedgeUnzip.pStarGoodAll_of_core`; see
  `hitScaleZipStmt_of_core`);
* monotonicity of `L⁻` on `[0,∞)` from `F1.LenStrictMonoStmt`;
* reaching `ℓ` from infinite total left length (`PStarLenInfStmt`, open);
* `τ > 0` from `L⁻_t → 0` as `t → 0⁺` (`PStarLenStartStmt`, open) and monotonicity;
* `scaleParam γ x_τ > 0` from finite area of every half-disc `B_a(0) ∩ ℍ` and infinite total area
  of the unzipped fields at all times (`PStarAreaAllStmt`, open), by the deterministic
  `scaleParam_pos_of_area` (the argument of `S5.FieldLaw.Raw.scaleParam_zoomField_pos` with
  `C = 0`, `x = 0`).

Source: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4, pp. 70–72
(the paper uses these properties of the unzipped wedge without proof: the left side of
`η[0,t]` has quantum length tending to `0` as `t → 0` and to `∞` as `t → ∞`, and unzipping
preserves local finiteness and infinite total mass of the area measure). The reduction is own
elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open D3Plus MeasUnzip

/-! ## The open nodes -/

/-- **Area of the unzipped fields at all times** (open): a.s., for all `t ≥ 0`, the quantum area
measure of `x_t` is finite on every half-disc `B_a(0) ∩ ℍ` and has infinite total mass. -/
def PStarAreaAllStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ∀ t : ℝ, 0 ≤ t →
      (∀ a : ℝ, qAreaMeasure (Real.sqrt κ)
          (unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t) (Metric.ball 0 a ∩ H) < ⊤) ∧
        qAreaMeasure (Real.sqrt κ) (unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t) H = ⊤

/-! ## Deterministic bookkeeping -/

/-- **Positive scale from finite local and infinite total area** (deterministic). The argument
of `S5.FieldLaw.Raw.scaleParam_zoomField_pos` with `C = 0`, `x = 0` (own elementary). -/
theorem scaleParam_pos_of_area {γ : ℝ} {x : FieldSample}
    (hfin : ∀ a : ℝ, qAreaMeasure γ x (Metric.ball 0 a ∩ H) < ⊤)
    (hinf : qAreaMeasure γ x H = ⊤) : 0 < scaleParam γ x := by
  set μ := qAreaMeasure γ x with hμ
  have hmeasB : ∀ b : ℝ, MeasurableSet (Metric.ball (0 : ℂ) b ∩ H) := fun b =>
    (Metric.isOpen_ball.inter isOpen_H).measurableSet
  -- a half-disc with area `≥ 1`
  have hup : Tendsto (fun n : ℕ => μ (Metric.ball (0 : ℂ) n ∩ H)) atTop (𝓝 (μ H)) := by
    have hU : (⋃ n : ℕ, Metric.ball (0 : ℂ) n ∩ H) = H := by
      rw [← iUnion_inter, Metric.iUnion_ball_nat, univ_inter]
    have hmono : Monotone fun n : ℕ => Metric.ball (0 : ℂ) n ∩ H := fun m n hmn =>
      inter_subset_inter_left _ (Metric.ball_subset_ball (by exact_mod_cast hmn))
    have := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rwa [hU] at this
  rw [hinf] at hup
  obtain ⟨N, hN⟩ := (hup.eventually (lt_mem_nhds ENNReal.one_lt_top)).exists
  have hmem : ((N : ℝ) + 1) ∈ {a : ℝ | 0 < a ∧ 1 ≤ μ (Metric.ball 0 a ∩ H)} :=
    ⟨by positivity, hN.le.trans (measure_mono (inter_subset_inter_left _
      (Metric.ball_subset_ball (by linarith))))⟩
  -- a small half-disc has area `< 1`
  set s : ℕ → Set ℂ := fun n => Metric.ball (0 : ℂ) (1 / ((n : ℝ) + 1)) ∩ H with hs
  have hanti : Antitone s := by
    intro m n hmn
    refine inter_subset_inter_left _ (Metric.ball_subset_ball ?_)
    gcongr
  have hempty : (⋂ n, s n) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
    rw [mem_iInter] at hz
    have hz0 : z ∈ H := (hz 0).2
    have hzy : dist z (0 : ℂ) = 0 := by
      refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) dist_nonneg
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      have := (hz n).1
      rw [Metric.mem_ball] at this
      linarith
    rw [dist_eq_zero] at hzy
    have him : z.im = 0 := by rw [hzy]; simp
    exact absurd hz0 (by simp [H, him])
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hmeasB _).nullMeasurableSet)
    hanti ⟨0, (hfin _).ne⟩
  rw [hempty, measure_empty] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))).exists
  have hlb : ∀ a ∈ {a : ℝ | 0 < a ∧ 1 ≤ μ (Metric.ball 0 a ∩ H)}, 1 / ((n : ℝ) + 1) ≤ a := by
    rintro a ⟨-, h1a⟩
    by_contra hlt
    rw [not_le] at hlt
    exact absurd (h1a.trans (measure_mono (inter_subset_inter_left _
      (Metric.ball_subset_ball hlt.le)))) (not_le.2 hn)
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact hpos.trans_le (le_csInf ⟨_, hmem⟩ hlb)

/-! ## The reduction -/

end QuantumZipper.E6
