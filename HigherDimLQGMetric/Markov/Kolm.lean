import HigherDimLQGMetric.Markov.Lipschitz
import LQGMetric.Field.MarkovVer2Rect
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-! Kolmogorov continuity for locally Lipschitz Gaussian Hilbert-space families. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped RealInnerProductSpace NNReal

namespace HigherDimLQGMetric

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A measurable representative of an `L²` random variable. -/
def markovLpProc (u : Lp ℝ 2 P) : Ω → ℝ :=
  (Lp.aestronglyMeasurable u).aemeasurable.mk _

omit [IsProbabilityMeasure P] in
theorem measurable_markovLpProc (u : Lp ℝ 2 P) : Measurable (markovLpProc u) :=
  (Lp.aestronglyMeasurable u).aemeasurable.measurable_mk

omit [IsProbabilityMeasure P] in
theorem markovLpProc_ae (u : Lp ℝ 2 P) :
    markovLpProc u =ᵐ[P] (u : Ω → ℝ) :=
  ((Lp.aestronglyMeasurable u).aemeasurable.ae_eq_mk).symm

/-- A Gaussian `L²` increment has the Gaussian law with variance given by its squared norm. -/
theorem markovLpProc_hasLaw_sub (u v : Lp ℝ 2 P)
    (hG : LQGMetric.MarkovGauss.IsCGauss P (u - v)) :
    HasLaw (fun ω => markovLpProc u ω - markovLpProc v ω)
      (gaussianReal 0 (‖u - v‖ ^ 2).toNNReal) P := by
  have hL : HasLaw (fun ω => (u - v : Lp ℝ 2 P) ω)
      (gaussianReal 0 (‖u - v‖ ^ 2).toNNReal) P :=
    ⟨(Lp.aestronglyMeasurable _).aemeasurable,
      LQGMetric.MarkovVer2.map_eq_gaussianReal_norm hG⟩
  refine hL.congr ?_
  filter_upwards [markovLpProc_ae u, markovLpProc_ae v, Lp.coeFn_sub u v] with ω e1 e2 e3
  rw [e3, Pi.sub_apply, e1, e2]

/-- A locally `L²`-Lipschitz family with centered Gaussian increments has a version continuous
at every sample and measurable at every parameter. -/
theorem markov_exists_contVersion_gauss {d : ℕ} (u : (Fin d → ℝ) → Lp ℝ 2 P)
    (hG : ∀ q q', LQGMetric.MarkovGauss.IsCGauss P (u q - u q'))
    (hu : ∀ R : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q q' : Fin d → ℝ,
      ‖q‖ ≤ R → ‖q'‖ ≤ R → ‖u q - u q'‖ ^ 2 ≤ C * ‖q - q'‖ ^ 2) :
    ∃ Y : (Fin d → ℝ) → Ω → ℝ,
      (∀ ω, Continuous fun q => Y q ω) ∧
      (∀ q, Measurable (Y q)) ∧
      ∀ q, (fun ω => Y q ω) =ᵐ[P] (u q : Ω → ℝ) := by
  let Z : (Fin d → ℝ) → Ω → ℝ := fun q => markovLpProc (u q)
  have hZm : ∀ q, Measurable (Z q) := fun q => measurable_markovLpProc _
  let M : ℝ := QuantumZipper.gaussianAbsMoment (2 * (d + 1))
  have hM : 0 ≤ M := QuantumZipper.gaussianAbsMoment_nonneg _
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧
      QuantumZipper.KolmG.MomentBoundG Z P (2 * (d + 1))
        ((2 * (d + 1) : ℕ) : ℝ) K R := by
    intro R
    obtain ⟨C, hC, hbound⟩ := hu R
    refine ⟨C ^ (d + 1) * M, by positivity, fun q hq q' hq' => ?_⟩
    have hlaw := markovLpProc_hasLaw_sub (u q) (u q') (hG q q')
    have hE := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq
      (P := P) ((hZm q).sub (hZm q')) (d + 1) hlaw.map_eq
    simp only [Pi.sub_apply] at hE
    simp only [Z]
    rw [hE]
    refine ENNReal.ofReal_le_ofReal ?_
    let a : ℝ := ‖u q - u q'‖ ^ 2
    have ha : 0 ≤ a := sq_nonneg _
    have hqn : ‖q‖ ≤ (R : ℝ) :=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
        simpa [Real.norm_eq_abs] using hq i
    have hq'n : ‖q'‖ ≤ (R : ℝ) :=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
        simpa [Real.norm_eq_abs] using hq' i
    have hbd : a ≤ C * ‖q - q'‖ ^ 2 := hbound q q' hqn hq'n
    have hcoe : ((a.toNNReal : NNReal) : ℝ) = a := Real.coe_toNNReal _ ha
    rw [hcoe, Real.rpow_natCast]
    calc
      a ^ (d + 1) * M ≤ (C * ‖q - q'‖ ^ 2) ^ (d + 1) * M := by gcongr
      _ = C ^ (d + 1) * M * ‖q - q'‖ ^ (2 * (d + 1)) := by ring
  have hpos : (d : ℝ) < ((2 * (d + 1) : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨Y, hYc, hYm, hYZ⟩ := LQGMetric.WhiteNoise.exists_meas_continuous_modification_N
    (P := P) (Z := Z) hZm (p := 2 * (d + 1)) (by omega) hpos hmom
  exact ⟨Y, hYc, hYm, fun q => (hYZ q).trans (markovLpProc_ae (u q))⟩

open HigherDimLFPP (Rd)

/-- Every exterior point-vector increment is a centered Gaussian variable. -/
theorem markovPointVec_sub_isCGauss {d : ℕ} {h : Ω → DistRd d}
    (hh : IsWholeSpaceLGF h P) (V : TopologicalSpace.Opens (Rd d))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    {u v : Lp ℝ 2 P} (hu : u ∈ markovInsideSpace hh V hρ)
    (hv : v ∈ markovInsideSpace hh V hρ) :
    LQGMetric.MarkovGauss.IsCGauss P (u - v) := by
  apply LQGMetric.MarkovGauss.isCGauss_of_mem_gaussSpace
    hh.gaussian hh.centered (markov_memLp_pair hh)
  exact markov_insideSpace_le_global hh V hρ (Submodule.sub_mem _ hu hv)

/-- The smooth global chart into a Euclidean ball. -/
def markovBallChart {d : ℕ} (x₀ : Rd d) (r : ℝ) : Rd d → Rd d :=
  OpenPartialHomeomorph.univBall x₀ r

theorem markovBallChart_mem {d : ℕ} (x₀ : Rd d) {r : ℝ} (hr : 0 < r)
    (q : Rd d) : markovBallChart x₀ r q ∈ ball x₀ r := by
  have hq : q ∈ (OpenPartialHomeomorph.univBall x₀ r).source := by simp
  have h := (OpenPartialHomeomorph.univBall x₀ r).map_source hq
  simpa [markovBallChart, OpenPartialHomeomorph.univBall_target x₀ hr] using h

theorem markovBallChart_contDiff {d : ℕ} (x₀ : Rd d) (r : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (markovBallChart x₀ r) := by
  exact OpenPartialHomeomorph.contDiff_univBall

theorem markovBallChart_local_lipschitz {d : ℕ} (x₀ : Rd d) (r : ℝ)
    (R : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (markovBallChart x₀ r)
      (closedBall (0 : Rd d) R) := by
  exact (markovBallChart_contDiff x₀ r).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)

/-- A continuous modification on one ball about an exterior point. -/
theorem markov_exists_local_pointVersion {d : ℕ} {h : Ω → DistRd d}
    (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : TopologicalSpace.Opens (Rd d))
    (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (x₀ : Rd d) (hx₀ : x₀ ∈ extOpen V) :
    ∃ r : ℝ, 0 < r ∧ ball x₀ r ⊆ extOpen V ∧
      ∃ H : Rd d → Ω → ℝ,
        (∀ ω, ContinuousOn (fun x => H x ω) (ball x₀ r)) ∧
        (∀ x, Measurable (H x)) ∧
        (∀ x (_hx : x ∈ ball x₀ r) (hxo : x ∈ extOpen V),
          (fun ω => H x ω) =ᵐ[P]
            (markovPointVec hd hh V hVb hρ hρV x hxo : Ω → ℝ)) := by
  obtain ⟨r, C, hr, hC, hball, hLip⟩ :=
    markovPointVec_local_lipschitz hd hh V hVb hρ hρV x₀ hx₀
  let c : Rd d → Rd d := markovBallChart x₀ r
  have hc (q : Rd d) : c q ∈ ball x₀ r := markovBallChart_mem x₀ hr q
  have hco (q : Rd d) : c q ∈ extOpen V := hball (hc q)
  let u : (Fin d → ℝ) → Lp ℝ 2 P := fun q =>
    markovPointVec hd hh V hVb hρ hρV (c (WithLp.toLp 2 q)) (hco _)
  have huG (q q' : Fin d → ℝ) :
      LQGMetric.MarkovGauss.IsCGauss P (u q - u q') :=
    markovPointVec_sub_isCGauss hh V hρ
      (markovPointVec_mem hd hh V hVb hρ hρV _ (hco _))
      (markovPointVec_mem hd hh V hVb hρ hρV _ (hco _))
  have huLip : ∀ R : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ q q' : Fin d → ℝ,
      ‖q‖ ≤ R → ‖q'‖ ≤ R → ‖u q - u q'‖ ^ 2 ≤ B * ‖q - q'‖ ^ 2 := by
    intro R
    let S : ℝ := ((d : ℝ) + 1) * (R : ℝ)
    obtain ⟨K, hK⟩ := markovBallChart_local_lipschitz x₀ r S
    let B : ℝ := C ^ 2 * (K : ℝ) ^ 2 * d
    refine ⟨B, by positivity, ?_⟩
    intro q q' hq hq'
    have hmem (w : Fin d → ℝ) (hw : ‖w‖ ≤ (R : ℝ)) :
        WithLp.toLp 2 w ∈ closedBall (0 : Rd d) S := by
      have hw2 := HigherDimLFPP.norm_toLp_sq_le_dim_mul w
      have hd0 : 0 ≤ (d : ℝ) := by positivity
      have hR0 : 0 ≤ (R : ℝ) := by positivity
      have hS0 : 0 ≤ S := mul_nonneg (by positivity) hR0
      have hsq : ‖(WithLp.toLp 2 w : Rd d)‖ ^ 2 ≤ S ^ 2 := by
        calc
          _ ≤ (d : ℝ) * ‖w‖ ^ 2 := hw2
          _ ≤ (d : ℝ) * (R : ℝ) ^ 2 := by gcongr
          _ ≤ S ^ 2 := by dsimp [S]; nlinarith [sq_nonneg ((d : ℝ) * (R : ℝ))]
      rw [mem_closedBall, dist_zero_right]
      nlinarith [norm_nonneg (WithLp.toLp 2 w : Rd d)]
    have hqmem := hmem q hq
    have hq'mem := hmem q' hq'
    have hxy := hLip (c (WithLp.toLp 2 q')) (hco _) (c (WithLp.toLp 2 q)) (hco _)
      (ball_subset_closedBall (hc _)) (ball_subset_closedBall (hc _))
    have hchart := hK.dist_le_mul _ hqmem _ hq'mem
    rw [dist_eq_norm] at hchart
    have hchart' : ‖c (WithLp.toLp 2 q) - c (WithLp.toLp 2 q')‖ ≤
        (K : ℝ) * ‖(WithLp.toLp 2 q : Rd d) - WithLp.toLp 2 q'‖ := by
      simpa [dist_eq_norm] using hchart
    have hto := HigherDimLFPP.norm_toLp_sq_le_dim_mul (q - q')
    rw [WithLp.toLp_sub] at hto
    have hxy2 := pow_le_pow_left₀ (norm_nonneg _) hxy 2
    have hchart2 := pow_le_pow_left₀ (norm_nonneg _) hchart' 2
    dsimp [u]
    calc
      _ ≤ (C * ‖c (WithLp.toLp 2 q) - c (WithLp.toLp 2 q')‖) ^ 2 := hxy2
      _ ≤ (C * ((K : ℝ) * ‖(WithLp.toLp 2 q : Rd d) - WithLp.toLp 2 q'‖)) ^ 2 := by
        gcongr
      _ = C ^ 2 * (K : ℝ) ^ 2 * ‖(WithLp.toLp 2 q : Rd d) - WithLp.toLp 2 q'‖ ^ 2 := by ring
      _ ≤ C ^ 2 * (K : ℝ) ^ 2 * (d * ‖q - q'‖ ^ 2) := by gcongr
      _ = B * ‖q - q'‖ ^ 2 := by simp only [B]; ring
  obtain ⟨Y, hYc, hYm, hYu⟩ := markov_exists_contVersion_gauss u huG huLip
  let H : Rd d → Ω → ℝ := fun x ω =>
    Y (WithLp.ofLp ((OpenPartialHomeomorph.univBall x₀ r).symm x)) ω
  refine ⟨r, hr, hball, H, ?_, ?_, ?_⟩
  · intro ω
    have hcont : ContinuousOn
        (fun x : Rd d => WithLp.ofLp ((OpenPartialHomeomorph.univBall x₀ r).symm x))
        (ball x₀ r) :=
      (PiLp.continuous_ofLp 2 _).comp_continuousOn
        (OpenPartialHomeomorph.continuousOn_univBall_symm x₀ r)
    exact (hYc ω).comp_continuousOn hcont
  · intro x
    exact hYm _
  · intro x hx hxO
    have htarget : x ∈ (OpenPartialHomeomorph.univBall x₀ r).target := by
      simpa [OpenPartialHomeomorph.univBall_target x₀ hr] using hx
    have hinv := (OpenPartialHomeomorph.univBall x₀ r).right_inv htarget
    have hq := hYu (WithLp.ofLp ((OpenPartialHomeomorph.univBall x₀ r).symm x))
    simpa only [H, u, c, WithLp.toLp_ofLp, markovBallChart, hinv] using hq

end HigherDimLQGMetric
