/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvXProof

/-!
# Flow locality with a general agreement set: the setting

Packet PROVE-G7A-LOC. The explicit Cameron–Martin chain of PROVE-L1-CMI/CMIC (`FlowStopIdentCMI.CMIVSetting`) asks
the buffer's real points to lie in ONE interval `[a, c] ⊆ O` whose filled shift hull lies in the cutoff buffer `N`.
Corollary G7a (supplement p. 499) needs the comparison with a general open agreement set `O`, where a stopped
curve may swallow real points outside `O` into a retained pocket. Here:

* `GSetting`: the explicit-shift setting with the three interval fields removed (only `closure V ⊆ N`, the real
  points of `N` in `O`);
* `GSetting.toFake`: the same source-side data viewed as a `CMIVSetting` of the trivial comparison (`bR = b`,
  `O = N = univ`, zero cutoff); every source-side result of the CMI chain (measurable exit, announcements, frozen
  driver, path data, zero-exit case) is used through it without change;
* the reference-side facts that do not need the interval: the tilt, the chart field and its law, the zero-exit
  reference coupling, the chart locality transfer (copies of the `CMIVSetting` proofs, no interval used).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowLocalityGen
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open Sec7.PocketTraversal
open FlowStopIdentCMI StoppedExtend

/-! ### The zero cutoff -/

/-- The zero cutoff field. -/
def zeroCut : CMCut where
  f := fun _ => 0
  smooth := contDiff_const
  compact := HasCompactSupport.zero
  odd := fun _ => by simp

theorem greenDensity_zeroCut (z : ℂ) : QuantumZipper.K3.greenDensity zeroCut.f z = 0 := by
  simp [QuantumZipper.K3.greenDensity, zeroCut, InnerProductSpace.laplacian_const]

theorem src_zeroCut (z : ℂ) : zeroCut.src z = 0 := by
  by_cases hz : z ∈ H
  · rw [zeroCut.src_of_mem hz, greenDensity_zeroCut, neg_zero]
  · exact zeroCut.src_of_notMem hz

/-- The zero function is the bounded harmonic extension of `b − b`. -/
theorem isBoundedHarmonicExtension_sub_self (b : ℝ → ℝ) (S : Set ℝ) :
    IsBoundedHarmonicExtension (fun x => b x - b x) S fun _ => 0 := by
  refine ⟨fun z _ => InnerProductSpace.harmonicAt_const 0, ⟨0, fun z _ => by simp⟩, fun x _ => ?_⟩
  simp only [sub_self]
  exact tendsto_const_nhds

/-! ### The setting -/

/-- **The explicit-shift setting with a general agreement set.** As `FlowStopIdentCMI.CMIVSetting`, without the
interval `[a, c]`: data `b`, `bR` agreeing on an open `O`, a cutoff buffer `N` with real points over `O` containing
the closure of the bounded buffer `V`, the cutoff `F = q` harmonic on `N`, the source approximations `s`, the pairing
`Λ`, the density `k e^{−Λ}`, and the original chart coupling of a flow line `Γ` of `H₀` from `y` at angle `θ`. -/
structure GSetting (S : Type u) [m : MeasurableSpace S] where
  κ : ℝ
  κ_pos : 0 < κ
  κ_lt_four : κ < 4
  b : ℝ → ℝ
  bR : ℝ → ℝ
  J : Finset ℝ
  JR : Finset ℝ
  b_pc : IsPiecewiseConstantBoundaryData b J
  bR_pc : IsPiecewiseConstantBoundaryData bR JR
  O : Set ℝ
  O_open : IsOpen O
  boundary_eq : ∀ x ∈ O, b x = bR x
  N : Set ℂ
  N_open : IsOpen N
  N_real : ∀ z ∈ N, z.im = 0 → z.re ∈ O
  V : Set ℂ
  V_open : IsOpen V
  V_bounded : Bornology.IsBounded V
  closureV_subset : closure V ⊆ N
  F : CMCut
  q : ℂ → ℝ
  q_extension : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ JR : Finset ℝ) : Set ℝ) q
  cutoff_eq : ∀ z ∈ N, z ∈ H → F.f z = q z
  cutoff_harmonic : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0
  y : ℝ
  θ : ℝ
  Q₀ : Measure S
  Q₀_prob : IsProbabilityMeasure Q₀
  H₀ : S → DistOn upperHalfPlaneOpens
  H₀_gff : IsGFFWithBoundaryData Q₀ H₀ b J
  s : ℕ → TestOn upperHalfPlaneOpens
  s_bound : ∀ n z, |s n z| ≤ |F.src z|
  s_limit : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))
  Λ : S → ℝ
  Λ_measurable : Measurable Λ
  pairing_limit : ∀ᵐ x ∂Q₀, Tendsto (fun n => H₀ x (s n)) atTop (𝓝 (Λ x))
  k : ℝ
  k_pos : 0 < k
  tilt_prob : IsProbabilityMeasure (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x)))
  Γ : S → ℝ≥0 → ℂ
  U : S → ℝ≥0∞
  h' : S → DistOn upperHalfPlaneOpens
  filt : Filtration ℝ≥0 m
  W₀ : ℝ≥0 → S → ℝ
  VL₀ : Fin (flowLineNL b J y) → ℝ≥0 → S → ℝ
  VR₀ : Fin (flowLineNR b J y) → ℝ≥0 → S → ℝ
  B₀ : ℝ≥0 → S → ℝ
  translate : ∀ x, IsTranslateAddConst y (θ * QuantumZipper.chiC κ) (H₀ x) (h' x)
  coupling : IsOptionalHullCoupling κ (flowLineXL b J y) (flowLineXR b J y)
    (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ) Q₀ filt W₀ VL₀ VR₀ B₀ U h'
  trace : ∀ᵐ x ∂Q₀, IsGeneratingTrace (W₀ · x) (U x) (fun t => Γ x t - y)
  killed : IsMeasurableKilledDriving W₀ VL₀ VR₀ U

namespace GSetting
variable {S : Type u} [MeasurableSpace S] (D : GSetting S)

/-- The explicit comparison measure. -/
def tilt : Measure S := D.Q₀.withDensity fun x => ENNReal.ofReal (D.k * Real.exp (-D.Λ x))
/-- The original driving filtration. -/
def driving := drivingFiltration D.Q₀ D.killed
/-- The shifted chart field. -/
def chartField : S → DistOn upperHalfPlaneOpens := fun ω => D.h' ω + chartShift D.F D.q D.y
/-- The shifted field in physical coordinates. -/
def shiftedField : S → DistOn upperHalfPlaneOpens := fun ω => D.H₀ ω +
  SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (fun z => D.q z - D.F.f z)

/-- A radius containing the closure of the buffer. -/
theorem exists_radius : ∃ r : ℝ, closure D.V ⊆ Metric.closedBall (0 : ℂ) r :=
  (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 D.V_bounded.closure

/-- The chosen radius. -/
def radius : ℝ := Classical.choose D.exists_radius

theorem closureV_real_radius : ∀ z ∈ closure D.V, z.im = 0 → z.re ∈ Icc (-D.radius) D.radius := by
  intro z hz _
  have h := Classical.choose_spec D.exists_radius hz
  rw [Metric.mem_closedBall, dist_zero_right] at h
  exact abs_le.1 ((Complex.abs_re_le_norm z).trans h)

/-- **The trivial comparison of the source data**: the same flow line, coupling, buffer and seed, viewed as a
`CMIVSetting` for `bR = b`, `O = N = univ`, the zero cutoff, the zero source and `Λ = 0`, `k = 1`. Its
source-side clock (exit, announcements, frozen driver, path data) is the one of `D`. -/
def toFake : CMIVSetting S where
  κ := D.κ
  κ_pos := D.κ_pos
  κ_lt_four := D.κ_lt_four
  b := D.b
  bR := D.b
  J := D.J
  JR := D.J
  b_pc := D.b_pc
  bR_pc := D.b_pc
  O := univ
  O_open := isOpen_univ
  boundary_eq := fun _ _ => rfl
  N := univ
  N_open := isOpen_univ
  N_real := fun _ _ _ => mem_univ _
  V := D.V
  V_open := D.V_open
  V_bounded := D.V_bounded
  closureV_subset := subset_univ _
  a := -D.radius
  c := D.radius
  interval_subset := subset_univ _
  closureV_real := D.closureV_real_radius
  hull_subset := subset_univ _
  F := zeroCut
  q := fun _ => 0
  q_extension := isBoundedHarmonicExtension_sub_self D.b _
  cutoff_eq := fun _ _ _ => rfl
  cutoff_harmonic := fun z _ => greenDensity_zeroCut z
  y := D.y
  θ := D.θ
  Q₀ := D.Q₀
  Q₀_prob := D.Q₀_prob
  H₀ := D.H₀
  H₀_gff := D.H₀_gff
  s := fun _ => 0
  s_bound := fun _ z => by
    show |(0 : TestOn upperHalfPlaneOpens) z| ≤ _
    exact (abs_nonneg _).trans_eq' (by simp)
  s_limit := fun z => by
    rw [src_zeroCut]
    exact tendsto_const_nhds
  Λ := fun _ => 0
  Λ_measurable := measurable_const
  pairing_limit := ae_of_all _ fun x => by
    simp only [map_zero]
    exact tendsto_const_nhds
  k := 1
  k_pos := one_pos
  tilt_prob := by
    have : (D.Q₀.withDensity fun _ => ENNReal.ofReal (1 * Real.exp (-0))) = D.Q₀ := by
      simp only [neg_zero, Real.exp_zero, mul_one, ENNReal.ofReal_one]
      exact withDensity_one
    rw [this]
    exact D.Q₀_prob
  Γ := D.Γ
  U := D.U
  h' := D.h'
  filt := D.filt
  W₀ := D.W₀
  VL₀ := D.VL₀
  VR₀ := D.VR₀
  B₀ := D.B₀
  translate := D.translate
  coupling := D.coupling
  trace := D.trace
  killed := D.killed

theorem toFake_driving : D.toFake.driving = D.driving := rfl

/-! ### The reference side (copies of the `CMIVSetting` proofs; no interval is used) -/

/-- Both directions of absolute continuity of the explicit tilt. -/
theorem tilt_equivalent : D.tilt ≪ D.Q₀ ∧ D.Q₀ ≪ D.tilt :=
  ⟨withDensity_absolutelyContinuous _ _, absolutelyContinuous_withDensity_exp D.Λ_measurable D.k_pos⟩

/-- Equivalent laws give the same completed driving filtration. -/
theorem driving_tilt_eq {nL nR : ℕ} {W : ℝ≥0 → S → ℝ}
    {VL : Fin nL → ℝ≥0 → S → ℝ} {VR : Fin nR → ℝ≥0 → S → ℝ} {e : S → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR e) :
    drivingFiltration D.tilt hX = drivingFiltration D.Q₀ hX :=
  le_antisymm (RetAux79.drivingFiltration_le_of_absolutelyContinuous hX D.tilt_equivalent.2)
    (RetAux79.drivingFiltration_le_of_absolutelyContinuous hX D.tilt_equivalent.1)

/-- The shifted chart field is measurable. -/
theorem measurable_chartField : Measurable D.chartField :=
  (Coupling.measurable_add_distOnConst (chartShift D.F D.q D.y)).comp D.coupling.2.1

/-- The chart and physical fields satisfy the frozen translation predicate. -/
theorem translate_shift : ∀ ω, IsTranslateAddConst D.y (D.θ * QuantumZipper.chiC D.κ)
    (D.shiftedField ω) (D.chartField ω) := fun ω =>
  isTranslateAddConst_add_chartShift (D.translate ω) D.F D.q_extension.1.continuousOn

end GSetting

end InteractingSLE.Restart.FlowLocalityGen
