import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Sec4.Lemma41Uniform
import HigherDimLQGMetric.Field.Measurable
import QuantumZipper.Proofs.LQG.ZeroOneCM
import GaussianLQG.Field.Pairing.Quasi

/-!
# Metric-valued versions (packet E5): frame shifts, Cameron–Martin and the zero–one law

Part C, `c:lem-opt-cm` and `c:lem-opt-01` (blueprint `blueprint/sections/c3-median.tex`, section `c:sec-optional`),
for a pairing frame `F` (interface I19, `PairingFrame d`).

* `mvFrameShift F v = f_v = ∑_j v_j e_j` for a rational finitely supported `v` (the countable group `H₀` of Part C),
  additive in `v`, bounded.
* `ae_addFun_frame_of_ae` (`c:lem-opt-cm`): almost-sure events are almost sure after a frame shift (the frame
  realization `T` of the normalized LGF on `(ℝ^ℕ, stdP)`, `T(ω + v) = T(ω) + f_v` on the good set, and the
  quasi-invariance of `stdP` under finitely supported shifts, `GaussianLQG.map_shiftBy_absolutelyContinuous`).
* `measure_zero_or_one_of_frame_invariant` (`c:lem-opt-01`): a measurable set of fields invariant under all
  rational frame shifts has probability `0` or `1` under `normLGFLaw d`. Its preimage under `T`, intersected with the
  good set, is invariant under all rational finitely supported coordinate shifts, and the Cameron–Martin zero–one law
  of the coordinate Gaussian process (`QuantumZipper.ZeroOneCM.measure_preimage_eq_zero_or_one_of_ratShift`, with
  `GaussianLQG.isGaussianProcess_coordProc`, `GaussianLQG.covK_coordProc`) applies. This replaces the blueprint's
  section/Fubini argument (a route change, recorded in the handoff; same statement).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## Frame shifts -/

theorem mv_frameFunRd_zero (e : ℕ → C(Rd d, ℝ)) : frameFunRd e 0 = 0 := by
  simp [frameFunRd]

theorem mv_frameFunRd_add (e : ℕ → C(Rd d, ℝ)) (v w : ℕ →₀ ℝ) :
    frameFunRd e (v + w) = frameFunRd e v + frameFunRd e w := by
  unfold frameFunRd
  exact Finsupp.sum_add_index' (fun i => zero_smul ℝ (e i)) (fun i b₁ b₂ => add_smul b₁ b₂ (e i))

theorem mv_frameFunRd_apply (e : ℕ → C(Rd d, ℝ)) (v : ℕ →₀ ℝ) (x : Rd d) :
    frameFunRd e v x = ∑ j ∈ v.support, v j * e j x := by
  unfold frameFunRd Finsupp.sum
  rw [ContinuousMap.coe_sum, Finset.sum_apply]
  rfl

/-- The rational frame shift `f_v = ∑_j v_j e_j` (`v ∈ ℕ →₀ ℚ`; Part C's group `H₀`). -/
def mvFrameShift (F : PairingFrame d) (v : ℕ →₀ ℚ) : C(Rd d, ℝ) :=
  frameFunRd F.e (v.mapRange ((↑) : ℚ → ℝ) Rat.cast_zero)

theorem mvFrameShift_zero (F : PairingFrame d) : mvFrameShift F 0 = 0 := by
  simp [mvFrameShift, mv_frameFunRd_zero]

theorem mvFrameShift_add (F : PairingFrame d) (v w : ℕ →₀ ℚ) :
    mvFrameShift F (v + w) = mvFrameShift F v + mvFrameShift F w := by
  unfold mvFrameShift
  rw [Finsupp.mapRange_add (fun a b => Rat.cast_add a b), mv_frameFunRd_add]

/-- The rational frame shifts are bounded. -/
theorem exists_abs_mvFrameShift_le (F : PairingFrame d) (v : ℕ →₀ ℚ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Rd d, |mvFrameShift F v x| ≤ M := by
  choose B hB using F.bdd
  set w : ℕ →₀ ℝ := v.mapRange ((↑) : ℚ → ℝ) Rat.cast_zero
  have hB0 : ∀ j, 0 ≤ B j := fun j => (abs_nonneg _).trans (hB j 0)
  refine ⟨∑ j ∈ w.support, |w j| * B j, Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hB0 j),
    fun x => ?_⟩
  rw [mvFrameShift, mv_frameFunRd_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hB j x) (abs_nonneg _)

/-! ## The law of the frame realization -/

theorem mv_isProbabilityMeasure_stdP : IsProbabilityMeasure GaussianLQG.stdP := by
  unfold GaussianLQG.stdP LQGDimension.ExistAsm.stdP
  infer_instance

/-- The frame realization has the normalized law. -/
theorem mv_map_frame_T (hd : 2 ≤ d) (F : PairingFrame d) :
    GaussianLQG.stdP.map F.T = normLGFLaw d := by
  have := mv_isProbabilityMeasure_stdP
  exact l9b_map_eq_normLGFLaw hd F.normalized

theorem mv_measurable_shiftBy (v : ℕ →₀ ℝ) : Measurable fun ω => GaussianLQG.shiftBy ω v := by
  show Measurable fun ω : ℕ → ℝ => ω + ⇑v
  refine measurable_pi_iff.2 fun j => ?_
  simp only [Pi.add_apply]
  exact (measurable_pi_apply j : Measurable fun ω : ℕ → ℝ => ω j).add_const (v j)

/-- The good set of the frame is invariant under all finitely supported shifts. -/
theorem mv_shiftBy_mem_good_iff (F : PairingFrame d) (ω : GaussianLQG.Coord) (v : ℕ →₀ ℝ) :
    GaussianLQG.shiftBy ω v ∈ F.good ↔ ω ∈ F.good := by
  refine ⟨fun h => ?_, fun h => F.shift_mem ω h v⟩
  have := F.shift_mem _ h (-v)
  have e : GaussianLQG.shiftBy (GaussianLQG.shiftBy ω v) (-v) = ω := by
    funext j
    simp [GaussianLQG.shiftBy]
  rwa [e] at this

/-! ## Cameron–Martin along frame shifts (`c:lem-opt-cm`) -/

/-- **`c:lem-opt-cm`**: for a finitely supported `v`, an almost-sure event of the normalized field is almost sure for
the frame-shifted field `g + f_v`. -/
theorem ae_addFun_frame_of_ae (hd : 2 ≤ d) (F : PairingFrame d) (v : ℕ →₀ ℝ) {A : Set (DistRd d)}
    (hA : ∀ᵐ g ∂(normLGFLaw d), g ∈ A) :
    ∀ᵐ g ∂(normLGFLaw d), addFun g (frameFunRd F.e v) ∈ A := by
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hA)
  have hlaw := mv_map_frame_T hd F
  have hTN : GaussianLQG.stdP (F.T ⁻¹' N) = 0 := by
    rw [← Measure.map_apply F.measurable_T hNm, hlaw, hN0]
  have hshift : GaussianLQG.stdP {ω | F.T (GaussianLQG.shiftBy ω v) ∈ N} = 0 := by
    have h := GaussianLQG.map_shiftBy_absolutelyContinuous v hTN
    rwa [Measure.map_apply (mv_measurable_shiftBy v) (F.measurable_T hNm)] at h
  have hmeasS : MeasurableSet {g : DistRd d | addFun g (frameFunRd F.e v) ∈ N} :=
    measurable_addFun_left _ hNm
  have hnull : normLGFLaw d {g : DistRd d | addFun g (frameFunRd F.e v) ∈ N} = 0 := by
    rw [← hlaw, Measure.map_apply F.measurable_T hmeasS]
    refine measure_mono_null (fun ω hω => ?_) (measure_union_null F.ae_good hshift)
    by_cases hg : ω ∈ F.good
    · right
      show F.T (GaussianLQG.shiftBy ω v) ∈ N
      rw [F.shift ω hg v]
      exact hω
    · left
      exact hg
  rw [ae_iff]
  refine measure_mono_null (fun g hg => ?_) hnull
  have h' := hNsub (show addFun g (frameFunRd F.e v) ∈ {a | a ∉ A} from hg)
  exact h'

/-! ## The zero–one law for frame-invariant events (`c:lem-opt-01`) -/

/-- **`c:lem-opt-01`**: a measurable set of fields invariant under every rational frame shift has probability `0`
or `1` under `normLGFLaw d`. -/
theorem measure_zero_or_one_of_frame_invariant (hd : 2 ≤ d) (F : PairingFrame d) {A : Set (DistRd d)}
    (hA : MeasurableSet A)
    (hinv : ∀ (v : ℕ →₀ ℚ) (g : DistRd d), addFun g (mvFrameShift F v) ∈ A ↔ g ∈ A) :
    normLGFLaw d A = 0 ∨ normLGFLaw d A = 1 := by
  have := mv_isProbabilityMeasure_stdP
  set B : Set GaussianLQG.Coord := F.T ⁻¹' A ∩ F.good with hB
  have hBm : MeasurableSet B := (F.measurable_T hA).inter F.measurableSet_good
  have hPB : GaussianLQG.stdP B = normLGFLaw d A := by
    rw [hB, measure_inter_conull F.ae_good, ← Measure.map_apply F.measurable_T hA, mv_map_frame_T hd F]
  -- `B` is invariant under rational finitely supported shifts
  have hshiftB : ∀ (v : ℕ →₀ ℚ) (ω : GaussianLQG.Coord),
      GaussianLQG.shiftBy ω (v.mapRange ((↑) : ℚ → ℝ) Rat.cast_zero) ∈ B ↔ ω ∈ B := by
    intro v ω
    by_cases hω : ω ∈ F.good
    · have hω' := F.shift_mem ω hω (v.mapRange ((↑) : ℚ → ℝ) Rat.cast_zero)
      simp only [hB, mem_inter_iff, mem_preimage, hω, hω', and_true]
      rw [F.shift ω hω]
      exact hinv v (F.T ω)
    · have hω' : GaussianLQG.shiftBy ω (v.mapRange ((↑) : ℚ → ℝ) Rat.cast_zero) ∉ F.good :=
        fun h => hω ((mv_shiftBy_mem_good_iff F ω _).1 h)
      simp only [hB, mem_inter_iff, mem_preimage, hω, hω', and_false]
  have h01 := QuantumZipper.ZeroOneCM.measure_preimage_eq_zero_or_one_of_ratShift
    GaussianLQG.isGaussianProcess_coordProc (fun i => measurable_pi_apply i)
    (fun i => LQGDimension.ExistAsm.integral_eval i) hBm (fun i q => by
      have hset : (fun x : ℕ → ℝ => x + (q : ℝ) • fun j =>
          QuantumZipper.CameronMartin.covK GaussianLQG.coordProc GaussianLQG.stdP j i) ⁻¹' B = B := by
        ext x
        have hx : x + (q : ℝ) • (fun j =>
            QuantumZipper.CameronMartin.covK GaussianLQG.coordProc GaussianLQG.stdP j i) =
            GaussianLQG.shiftBy x ((Finsupp.single i q).mapRange ((↑) : ℚ → ℝ) Rat.cast_zero) := by
          funext j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, GaussianLQG.covK_coordProc,
            GaussianLQG.shiftBy, Finsupp.mapRange_single, Finsupp.single_apply]
          by_cases hji : j = i
          · subst hji
            simp
          · simp [hji, Ne.symm hji]
        simp only [mem_preimage]
        rw [hx]
        exact hshiftB _ x
      rw [hset])
  rw [← hPB]
  exact h01

end HigherDimLQGContinuity
