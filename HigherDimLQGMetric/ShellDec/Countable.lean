import HigherDimLQGMetric.ShellDec.Sigma
import HigherDimLQGMetric.Field.StandardBorelDist

/-!
# Countable coordinates for the mean-zero field sigma algebra

Fix a unit-mass test function in the open set. Subtracting its integral
multiple from each member of the countable generating family for distributions
gives mean-zero coordinates which generate `fieldSigma0` exactly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set TopologicalSpace
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

private def shellRecenterTest0 {d : ℕ} (U : Opens (Rd d))
    (ρ : TestRd d) (hρ : tsupport (ρ : Rd d → ℝ) ⊆ U)
    (hρmass : ∫ x, ρ x = 1) (φ : TestOn U) :
    {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ U} := by
  let ψ : TestRd d := (∫ x, φ x) • ρ
  have hIncl : (testIncl U φ : Rd d → ℝ) = φ :=
    funext fun x => testIncl_apply φ x
  have hmass : ∫ x, (testIncl U φ) x = ∫ x, ψ x := by
    rw [show (∫ x, (testIncl U φ) x) = ∫ x, φ x by simp only [testIncl_apply]]
    change (∫ x, φ x) = ∫ x, (∫ y, φ y) * ρ x
    rw [integral_const_mul, hρmass]
    ring
  refine ⟨testSub0 (testIncl U φ) ψ hmass, ?_⟩
  change tsupport (⇑(testIncl U φ - ψ)) ⊆ U
  have hφs : tsupport (⇑(testIncl U φ)) ⊆ U := by
    simpa only [hIncl] using φ.tsupport_subset
  refine (tsupport_sub _ _).trans (union_subset hφs ?_)
  change tsupport (fun x => (∫ y, φ y) • ρ x) ⊆ U
  exact (tsupport_smul_subset_right (fun _ => ∫ y, φ y)
    (fun x => ρ x)).trans hρ

private theorem shellRecenterTest0_apply {d : ℕ} (U : Opens (Rd d))
    (ρ : TestRd d) (hρ : tsupport (ρ : Rd d → ℝ) ⊆ U)
    (hρmass : ∫ x, ρ x = 1) (φ : TestOn U) (g : DistRd d) :
    g (shellRecenterTest0 U ρ hρ hρmass φ).1.1 =
      restrictTo U (addConst g (-g ρ)) φ := by
  rw [restrictTo_apply, addConst_apply]
  simp only [shellRecenterTest0, testSub0_val, map_sub, map_smul, smul_eq_mul]
  simp only [testIncl_apply]
  ring

/-- The countable `distGen` family, recentered by a local unit-mass test, generates
all mean-zero pairings supported in the open set. -/
theorem fieldSigma0_eq_comap_shellCoords {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (h : Ω → DistRd d) (U : Opens (Rd d))
    (ρ : TestRd d) (hρ : tsupport (ρ : Rd d → ℝ) ⊆ U)
    (hρmass : ∫ x, ρ x = 1) :
    fieldSigma0 h U = MeasurableSpace.comap
      (fun ω (j : ℕ × ℕ) => h ω (shellRecenterTest0 U ρ hρ hρmass
        (distGen U j)).1.1) MeasurableSpace.pi := by
  let Y : Ω → DistOn U := fun ω => restrictTo U (addConst (h ω) (-(h ω ρ)))
  have hYeq : fieldSigma0 h U = MeasurableSpace.comap Y (DistOn.measurableSpace U) := by
    apply le_antisymm
    · have hsrc : @Measurable Ω (DistOn U)
          (MeasurableSpace.comap Y (DistOn.measurableSpace U))
          (DistOn.measurableSpace U) Y := Measurable.of_comap_le le_rfl
      have hm : Measurable[MeasurableSpace.comap Y (DistOn.measurableSpace U)]
          (fun ω (ψ : {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ U}) =>
            h ω ψ.1.1) := by
        refine (@measurable_pi_iff _ _ _
          (MeasurableSpace.comap Y (DistOn.measurableSpace U)) _ _).2 fun ψ => ?_
        have hcoord : (fun ω => h ω ψ.1.1) =
            fun ω => Y ω (testOnOf U ψ.1.1 ψ.2) := by
          funext ω
          rw [restrictTo_testOnOf, addConst_apply_testRd0]
        rw [hcoord]
        exact (measurable_distOn_apply _).comp hsrc
      exact hm.comap_le
    · rw [distOn_measurableSpace_eq_comap, MeasurableSpace.comap_comp]
      have hm : Measurable[fieldSigma0 h U]
          (fun ω (j : ℕ × ℕ) => Y ω (distGen U j)) := by
        refine (@measurable_pi_iff _ _ _ (fieldSigma0 h U) _ _).2 fun j => ?_
        have hcoord : (fun ω => Y ω (distGen U j)) =
            fun ω => h ω (shellRecenterTest0 U ρ hρ hρmass (distGen U j)).1.1 := by
          funext ω
          exact (shellRecenterTest0_apply U ρ hρ hρmass (distGen U j) (h ω)).symm
        rw [hcoord]
        have hsrc : Measurable[fieldSigma0 h U]
            (fun ω (ψ : {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ U}) =>
              h ω ψ.1.1) := Measurable.of_comap_le le_rfl
        exact (measurable_pi_apply
          (shellRecenterTest0 U ρ hρ hρmass (distGen U j))).comp hsrc
      exact hm.comap_le
  rw [hYeq, distOn_measurableSpace_eq_comap, MeasurableSpace.comap_comp]
  congr 1
  funext ω j
  exact (shellRecenterTest0_apply U ρ hρ hρmass (distGen U j) (h ω)).symm

private theorem exists_shell_unitMass {d : ℕ} (hd : 1 ≤ d)
    {a b r : ℝ} (_ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hr : 0 < r) (z : Rd d) :
    ∃ ρ : TestRd d,
      tsupport (ρ : Rd d → ℝ) ⊆ ann z (a * r) (b * r) ∧
        ∫ x, ρ x = 1 := by
  let U : Opens (Rd d) := ⟨ann z (a * r) (b * r), isOpen_ann z _ _⟩
  have hs : Metric.sphere z r ⊆ U := by
    intro x hx
    have hnorm : ‖x - z‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hx
    change a * r < ‖x - z‖ ∧ ‖x - z‖ < b * r
    rw [hnorm]
    exact ⟨by simpa using mul_lt_mul_of_pos_right ha1 hr,
      by simpa using mul_lt_mul_of_pos_right hb1 hr⟩
  obtain ⟨N, hN⟩ := exists_tsupport_sphBump_subset
    (U := U) (r := r) (z := z) (by simpa [U, abs_of_pos hr] using hs)
  exact ⟨sphBump N z r, hN N le_rfl, integral_sphBump hd N z r⟩

private def shellUnitMass {d : ℕ} (hd : 1 ≤ d)
    {a b r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hr : 0 < r) (z : Rd d) : TestRd d :=
  Classical.choose (exists_shell_unitMass hd ha ha1 hb1 hr z)

private theorem shellUnitMass_spec {d : ℕ} (hd : 1 ≤ d)
    {a b r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hr : 0 < r) (z : Rd d) :
    tsupport (shellUnitMass hd ha ha1 hb1 hr z : Rd d → ℝ) ⊆
      ann z (a * r) (b * r) ∧
      ∫ x, shellUnitMass hd ha ha1 hb1 hr z x = 1 :=
  Classical.choose_spec (exists_shell_unitMass hd ha ha1 hb1 hr z)

/-- The deterministic countable mean-zero test functions used for one shell. -/
def shellCountableTest {d : ℕ} (hd : 1 ≤ d)
    {a b r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hr : 0 < r) (z : Rd d) (j : ℕ × ℕ) :
    {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ ann z (a * r) (b * r)} :=
  shellRecenterTest0 ⟨ann z (a * r) (b * r), isOpen_ann z _ _⟩
    (shellUnitMass hd ha ha1 hb1 hr z)
    (shellUnitMass_spec hd ha ha1 hb1 hr z).1
    (shellUnitMass_spec hd ha ha1 hb1 hr z).2
    (distGen ⟨ann z (a * r) (b * r), isOpen_ann z _ _⟩ j)

/-- The exact countable coordinate presentation of the field modulo constants on one shell. -/
theorem fieldSigma0_ann_eq_comap_shellCountable {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d)
    {a b r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hr : 0 < r) (z : Rd d) :
    fieldSigma0 h (ann z (a * r) (b * r)) = MeasurableSpace.comap
      (fun ω (j : ℕ × ℕ) => h ω (shellCountableTest hd ha ha1 hb1 hr z j).1.1)
        MeasurableSpace.pi := by
  exact fieldSigma0_eq_comap_shellCoords h
    ⟨ann z (a * r) (b * r), isOpen_ann z _ _⟩
    (shellUnitMass hd ha ha1 hb1 hr z)
    (shellUnitMass_spec hd ha ha1 hb1 hr z).1
    (shellUnitMass_spec hd ha ha1 hb1 hr z).2

private theorem comap_pi_nat_unpair {Ω : Type*} (X : Ω → ℕ × ℕ → ℝ) :
    MeasurableSpace.comap X MeasurableSpace.pi =
      MeasurableSpace.comap (fun ω (n : ℕ) => X ω (Nat.unpair n))
        MeasurableSpace.pi := by
  apply le_antisymm
  · have hm : @Measurable Ω (ℕ × ℕ → ℝ)
        (MeasurableSpace.comap (fun ω (n : ℕ) => X ω (Nat.unpair n))
          MeasurableSpace.pi) MeasurableSpace.pi X := by
      refine (@measurable_pi_iff _ _ _
        (MeasurableSpace.comap (fun ω (n : ℕ) => X ω (Nat.unpair n))
          MeasurableSpace.pi) _ _).2 fun j => ?_
      have hsrc : Measurable[MeasurableSpace.comap
          (fun ω (n : ℕ) => X ω (Nat.unpair n)) MeasurableSpace.pi]
          (fun ω (n : ℕ) => X ω (Nat.unpair n)) :=
        Measurable.of_comap_le le_rfl
      have heq : (fun ω => X ω j) =
          fun ω => X ω (Nat.unpair (Nat.pair j.1 j.2)) := by
        funext ω
        rw [Nat.unpair_pair]
      rw [heq]
      exact (measurable_pi_apply (Nat.pair j.1 j.2)).comp hsrc
    exact hm.comap_le
  · have hm : Measurable[MeasurableSpace.comap X MeasurableSpace.pi]
        (fun ω (n : ℕ) => X ω (Nat.unpair n)) := by
      refine (@measurable_pi_iff _ _ _ (MeasurableSpace.comap X MeasurableSpace.pi)
        _ _).2 fun n => ?_
      have hsrc : Measurable[MeasurableSpace.comap X MeasurableSpace.pi] X :=
        Measurable.of_comap_le le_rfl
      exact (measurable_pi_apply (Nat.unpair n)).comp hsrc
    exact hm.comap_le

/-- A Nat-indexed version convenient for finite prefixes and filtrations. -/
theorem fieldSigma0_ann_eq_comap_shellNat {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d)
    {a b r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hr : 0 < r) (z : Rd d) :
    fieldSigma0 h (ann z (a * r) (b * r)) = MeasurableSpace.comap
      (fun ω (n : ℕ) =>
        h ω (shellCountableTest hd ha ha1 hb1 hr z (Nat.unpair n)).1.1)
        MeasurableSpace.pi := by
  rw [fieldSigma0_ann_eq_comap_shellCountable hd h ha ha1 hb1 hr z]
  exact comap_pi_nat_unpair _

end HigherDimLQGMetric
