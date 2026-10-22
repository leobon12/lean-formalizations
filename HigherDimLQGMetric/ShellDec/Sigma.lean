import HigherDimLQGMetric.ShellDec.Defs
import HigherDimLQGMetric.Sphere.Conv

/-!
# Recentred shell events

The recentred restriction of an LGF is almost surely measurable from the mean-zero
pairings on an open set containing the averaging sphere. The dimension is at least
two, since the sphere average defined by mollification need not converge in one
dimension.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

private def shellCenterTest0 {d : ℕ} (hd : 1 ≤ d) (V : Opens (Rd d))
    (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ V)
    (φ : {ψ : TestRd d // tsupport (ψ : Rd d → ℝ) ⊆ V}) (n : ℕ) :
    {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ V} := by
  let ψ : TestRd d := (∫ x, φ.1 x) • sphBump (n + N) z r
  have hmass : ∫ x, φ.1 x = ∫ x, ψ x := by
    change (∫ x, φ.1 x) = ∫ x, (∫ y, φ.1 y) * sphBump (n + N) z r x
    rw [integral_const_mul, integral_sphBump hd]
    ring
  refine ⟨testSub0 φ.1 ψ hmass, ?_⟩
  change tsupport (⇑(φ.1 - ψ)) ⊆ V
  refine (tsupport_sub _ _).trans (union_subset φ.2 ?_)
  change tsupport (fun x => (∫ y, φ.1 y) • sphBump (n + N) z r x) ⊆ V
  exact (tsupport_smul_subset_right (fun _ => ∫ y, φ.1 y)
    (fun x => sphBump (n + N) z r x)).trans (hN n)

private theorem shellCenterTest0_apply {d : ℕ} (hd : 1 ≤ d) (V : Opens (Rd d))
    (z : Rd d) (r : ℝ) (N : ℕ)
    (hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ V)
    (φ : {ψ : TestRd d // tsupport (ψ : Rd d → ℝ) ⊆ V}) (n : ℕ) (g : DistRd d) :
    g ((shellCenterTest0 hd V z r N hN φ n).1.1) =
      g φ.1 - (∫ x, φ.1 x) * sphereAvgSeq g r z (n + N) := by
  simp only [shellCenterTest0, testSub0_val, map_sub, map_smul,
    sphereAvgSeq_eq_apply_sphBump, smul_eq_mul]

private theorem shellMeasurable_pairing {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (h : Ω → DistRd d) (V : Set (Rd d))
    (φ : {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ V}) :
    Measurable[fieldSigma0 h V] (fun ω => h ω φ.1.1) := by
  have hsrc : Measurable[fieldSigma0 h V]
      (fun ω (ψ : {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ V}) => h ω ψ.1.1) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply φ).comp hsrc

/-- A source shell event belongs modulo null sets to the mean-zero shell sigma-algebra.
The sphere-average convergence used here requires d ≥ 2. -/
theorem aeEventIn_of_recentred {d : ℕ} (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsWholeSpaceLGF h P) {V : Set (Rd d)} (hV : IsOpen V)
    {r : ℝ} (hr : 0 < r) {z : Rd d} (hS : Metric.sphere z r ⊆ V) {E : Set Ω}
    (hE : MeasurableSet[fieldSigmaOn
      (fun ω => addConst (h ω) (-sphereAvg (h ω) r z)) V] E) :
    AEEventIn P (fieldSigma0 h V) E := by
  let U : Opens (Rd d) := ⟨V, hV⟩
  have hd1 : 1 ≤ d := by omega
  obtain ⟨N, hN₀⟩ := exists_tsupport_sphBump_subset
    (U := U) (r := r) (z := z) (by simpa [U, abs_of_pos hr] using hS)
  have hN : ∀ n : ℕ, tsupport (⇑(sphBump (n + N) z r)) ⊆ U :=
    fun n => hN₀ (n + N) (Nat.le_add_left N n)
  let X : Ω → ({φ : TestRd d // tsupport (φ : Rd d → ℝ) ⊆ V} → ℝ) :=
    fun ω ψ => addConst (h ω) (-sphereAvg (h ω) r z) ψ.1
  let Y : Ω → ({φ : TestRd d // tsupport (φ : Rd d → ℝ) ⊆ V} → ℝ) :=
    fun ω ψ => limUnder atTop (fun n => h ω ((shellCenterTest0 hd1 U z r N hN ψ n).1.1))
  have hYm : Measurable[fieldSigma0 h V] Y := by
    refine @measurable_pi_iff _ _ _ (fieldSigma0 h V) _ _ |>.2 fun ψ => ?_
    have hm : ∀ n : ℕ, StronglyMeasurable[fieldSigma0 h V]
        (fun ω => h ω ((shellCenterTest0 hd1 U z r N hN ψ n).1.1)) :=
      fun n => (shellMeasurable_pairing h V
        (shellCenterTest0 hd1 U z r N hN ψ n)).stronglyMeasurable
    exact (@StronglyMeasurable.limUnder ℕ Ω ℝ (fieldSigma0 h V) _ _ atTop _
      (fun n ω => h ω ((shellCenterTest0 hd1 U z r N hN ψ n).1.1))
      _ _ hm).measurable
  have hXY : X =ᵐ[P] Y := by
    filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq hd hr z] with ω hc
    funext ψ
    have ha := tendsto_sphereAvgSeq_sphereAvg hc
    have hashift : Tendsto (fun n => sphereAvgSeq (h ω) r z (n + N)) atTop
        (𝓝 (sphereAvg (h ω) r z)) := ha.comp (tendsto_add_atTop_nat N)
    have hlim : Tendsto (fun n => h ω
        ((shellCenterTest0 hd1 U z r N hN ψ n).1.1)) atTop
        (𝓝 (h ω ψ.1 - (∫ x, ψ.1 x) * sphereAvg (h ω) r z)) := by
      simp_rw [shellCenterTest0_apply]
      exact tendsto_const_nhds.sub (tendsto_const_nhds.mul hashift)
    change addConst (h ω) (-sphereAvg (h ω) r z) ψ.1 =
      limUnder atTop (fun n => h ω ((shellCenterTest0 hd1 U z r N hN ψ n).1.1))
    rw [hlim.limUnder_eq, addConst_apply]
    ring
  change MeasurableSet[MeasurableSpace.comap X MeasurableSpace.pi] E at hE
  obtain ⟨B, hB, rfl⟩ := hE
  refine ⟨Y ⁻¹' B, hYm hB, ?_⟩
  filter_upwards [hXY] with ω hω
  change (X ω ∈ B) = (Y ω ∈ B)
  rw [hω]

end HigherDimLQGMetric
