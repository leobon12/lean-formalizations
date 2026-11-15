/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.FlowReflectLocal
import InteractingSLE.Spec.Sec4.RepulsionNoncollision
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling

/-!
# The optional hull coupling under the reflection `R(z) = −z̄`

Packet PROVE-LEMMA76C. If `(W, V^L, V^R, B, ζ)` with the field `h` satisfies the frozen `IsOptionalHullCoupling` for the
force word `(x_L; x_R)`, `(ρ_L; ρ_R)`, then the reflected evolution `(−W, −V^R, −V^L, −B, ζ)` (sides exchanged) with the
field `−h ∘ R` satisfies it for the reflected word `(−x_R; −x_L)`, `(ρ_R; ρ_L)` (**`IsOptionalHullCoupling.reflect`**).

* `forceBoundaryData_reflect`: off the jump set, the reflected data is `x ↦ −g(−x)`;
* `IsBoundedHarmonicExtension.reflect`: `−u ∘ R` extends `x ↦ −g(−x)`;
* `isMeasurableKilledDriving_reflect`, `drivingFiltration_reflect` (the reflected killed driving process generates
  the same filtration);
* `couplingMean_reflect`, `loewnerGreenEnergy_reflect` (from `LP.fwdMap_neg`, `LP.logDerivFwd_neg` and the
  `R`-invariance of the half-plane Green function).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal ComplexConjugate

open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Sec7

namespace FlowReflect

open LP (reflectC)

/-! ### Boundary data -/

theorem reflectC_ofReal (x : ℝ) : reflectC (x : ℂ) = ((-x : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [LP.reflectC]

theorem mem_forceJumpSet_neg_iff {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (x : ℝ) :
    -x ∈ forceJumpSet (fun i => -xR i) (fun i => -xL i) ↔ x ∈ forceJumpSet xL xR := by
  simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range, neg_eq_zero, neg_inj]
  tauto

/-- **The force data of the reflected word** is `x ↦ −g(−x)` off the jump set. -/
theorem forceBoundaryData_reflect (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) {x : ℝ} (hx : x ∉ forceJumpSet xL xR) :
    forceBoundaryData κ ρR ρL (fun i => -xR i) (fun i => -xL i) (-x) = -forceBoundaryData κ ρL ρR xL xR x := by
  have hx0 : x ≠ 0 := fun h => hx (by simp [forceJumpSet, h])
  have hxL : ∀ i, xL i ≠ x := fun i h => hx (by simp only [forceJumpSet]; exact Or.inr (Or.inl ⟨i, h⟩))
  have hxR : ∀ i, xR i ≠ x := fun i h => hx (by simp only [forceJumpSet]; exact Or.inr (Or.inr ⟨i, h⟩))
  unfold forceBoundaryData
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have h1 : ¬ -x < 0 := by linarith
    simp only [h1, hneg, ↓reduceIte, neg_mul, neg_neg]
    have e : (Finset.univ.filter fun i => -xL i ≤ -x) = Finset.univ.filter fun i => x < xL i := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact lt_of_le_of_ne (by linarith) (hxL i).symm
      · intro h; linarith
    rw [e]
  · have h1 : -x < 0 := by linarith
    have h2 : ¬ x < 0 := by linarith
    simp only [h1, h2, ↓reduceIte, neg_mul]
    have e : (Finset.univ.filter fun i => -x < -xR i) = Finset.univ.filter fun i => xR i ≤ x := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; linarith
      · intro h; have := lt_of_le_of_ne h (hxR i); linarith
    rw [e]

theorem tendsto_reflectC_nhdsWithin_H (z : ℂ) : Tendsto reflectC (𝓝[H] z) (𝓝[H] (reflectC z)) :=
  (LP.continuous_reflectC.continuousWithinAt).tendsto_nhdsWithin fun _ hw => reflectC_mem_H hw

/-- **Bounded harmonic extensions under `R`**: if `u` extends `g` off `S`, and `g' x = −g(−x)` with `−x ∉ S` off
`S'`, then `−u ∘ R` extends `g'` off `S'`. -/
theorem IsBoundedHarmonicExtension.reflect {g g' : ℝ → ℝ} {S S' : Set ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (hg : ∀ x, x ∉ S' → -x ∉ S ∧ g' x = -g (-x)) :
    IsBoundedHarmonicExtension g' S' fun z => -u (reflectC z) := by
  obtain ⟨hh, ⟨C, hC⟩, hlim⟩ := hu
  refine ⟨?_, ⟨C, fun z hz => ?_⟩, fun x hx => ?_⟩
  · have h := (harmonicOnNhd_comp_reflectC hh).neg
    rwa [reflectC_image_H] at h
  · rw [abs_neg]
    exact hC _ (reflectC_mem_H hz)
  · obtain ⟨hxS, hgx⟩ := hg x hx
    have hR := tendsto_reflectC_nhdsWithin_H (x : ℂ)
    rw [reflectC_ofReal] at hR
    have h := (hlim (-x) hxS).comp hR
    rw [hgx]
    exact h.neg

/-- The bounded harmonic extension of the reflected force data, reflected, extends the original data. -/
theorem IsBoundedHarmonicExtension.reflect_force {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρR ρL (fun i => -xR i) (fun i => -xL i))
      (forceJumpSet (fun i => -xR i) (fun i => -xL i)) u) :
    IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR)
      fun z => -u (reflectC z) := by
  refine IsBoundedHarmonicExtension.reflect hu fun x hx => ⟨fun h => hx ((mem_forceJumpSet_neg_iff xL xR x).1 h), ?_⟩
  rw [forceBoundaryData_reflect κ ρL ρR xL xR hx, neg_neg]


/-! ### The killed driving process -/

/-- The reflection of the state space `(w, v_L, v_R) ↦ (−w, −v_R, −v_L)`. -/
def stateRefl {nL nR : ℕ} (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ × (Fin nR → ℝ) × (Fin nL → ℝ) :=
  (-p.1, fun i => -p.2.2 i, fun i => -p.2.1 i)

theorem measurable_stateRefl {nL nR : ℕ} : Measurable (stateRefl (nL := nL) (nR := nR)) := by
  refine measurable_fst.neg.prodMk (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.2 fun i => ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)).neg
  · exact measurable_pi_iff.2 fun i => ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).neg

theorem stateRefl_stateRefl {nL nR : ℕ} (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : stateRefl (stateRefl p) = p := by
  simp [stateRefl]

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem killedSet_reflect (r : ℝ≥0) (A : Set (ℝ × (Fin nR → ℝ) × (Fin nL → ℝ))) :
    {ω | (r : ℝ≥0∞) < ζ ω ∧ ((-W) r ω, fun i => (fun i => -VR i) i r ω, fun i => (fun i => -VL i) i r ω) ∈ A} =
      {ω | (r : ℝ≥0∞) < ζ ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ stateRefl ⁻¹' A} := rfl

theorem isMeasurableKilledDriving_reflect (hX : IsMeasurableKilledDriving W VL VR ζ) :
    IsMeasurableKilledDriving (-W) (fun i => -VR i) (fun i => -VL i) ζ := fun r A hA => by
  rw [killedSet_reflect]
  exact hX r _ (measurable_stateRefl hA)

theorem killedDrivingSigma_reflect (t : ℝ≥0) :
    killedDrivingSigma (-W) (fun i => -VR i) (fun i => -VL i) ζ t = killedDrivingSigma W VL VR ζ t := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (MeasurableSpace.generateFrom_le ?_)
  · rintro _ ⟨r, hr, A, hA, rfl⟩
    rw [killedSet_reflect]
    exact MeasurableSpace.measurableSet_generateFrom ⟨r, hr, _, measurable_stateRefl hA, rfl⟩
  · rintro _ ⟨r, hr, A, hA, rfl⟩
    refine MeasurableSpace.measurableSet_generateFrom ⟨r, hr, stateRefl ⁻¹' A, measurable_stateRefl hA, ?_⟩
    rw [killedSet_reflect, ← preimage_comp]
    have e : stateRefl ∘ stateRefl = (id : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → _) := funext stateRefl_stateRefl
    rw [e, preimage_id]

/-- **The reflected killed driving process generates the same driving filtration.** -/
theorem drivingFiltration_reflect (P : Measure Ω) (hX : IsMeasurableKilledDriving W VL VR ζ) :
    drivingFiltration P (isMeasurableKilledDriving_reflect hX) = drivingFiltration P hX := by
  have e : killedDrivingFiltration (isMeasurableKilledDriving_reflect hX) = killedDrivingFiltration hX :=
    Filtration.ext (funext fun t => killedDrivingSigma_reflect t)
  unfold drivingFiltration
  rw [e]

theorem IsStoppingTime.measurableSpace_congr {f g : Filtration ℝ≥0 mΩ} (e : f = g) {τ : Ω → WithTop ℝ≥0}
    (hf : IsStoppingTime f τ) (hg : IsStoppingTime g τ) : hf.measurableSpace = hg.measurableSpace := by
  subst e
  rfl

/-! ### The mean and the energy -/

theorem greenH_reflectC (x y : ℂ) : QuantumZipper.greenH (reflectC x) (reflectC y) = QuantumZipper.greenH x y := by
  unfold QuantumZipper.greenH
  have h1 : reflectC x - conj (reflectC y) = -conj (x - conj y) := by
    simp only [LP.reflectC, map_neg, Complex.conj_conj, map_sub]; ring
  have h2 : reflectC x - reflectC y = -conj (x - y) := by
    simp only [LP.reflectC, map_sub]; ring
  rw [h1, h2, norm_neg, norm_neg, Complex.norm_conj, Complex.norm_conj]

/-- **The coupling mean under `R`**: `M_t(−W, u)(R z) = −M_t(W, −u ∘ R)(z)`. -/
theorem couplingMean_reflect (κ : ℝ) (w : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (u : ℂ → ℝ) (z : ℂ) :
    couplingMean κ (-w) t u (reflectC z) = -couplingMean κ w t (fun y => -u (reflectC y)) z := by
  unfold couplingMean
  rw [LP.fwdMap_neg w ht, LP.logDerivFwd_neg w ht, Complex.conj_im]
  ring

/-- **The Green energy under `R`**: `E_t(−W)(φ) = E_t(W)(φ ∘ R)`. -/
theorem loewnerGreenEnergy_reflect (w : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (φ : ℂ → ℝ) :
    loewnerGreenEnergy (-w) t φ = loewnerGreenEnergy w t fun z => φ (reflectC z) := by
  unfold loewnerGreenEnergy
  rw [← integral_comp_reflectC]
  congr 1
  funext y
  rw [← integral_comp_reflectC]
  congr 1
  funext z
  rw [LP.fwdMap_neg w ht, LP.fwdMap_neg w ht, greenH_reflectC]

theorem loewnerGreenEnergy_neg (w : ℝ → ℝ) (t : ℝ) (φ : ℂ → ℝ) :
    loewnerGreenEnergy w t (fun z => -φ z) = loewnerGreenEnergy w t φ := by
  unfold loewnerGreenEnergy
  congr 1
  funext y
  congr 1
  funext z
  ring

theorem integral_couplingMean_reflect (κ : ℝ) (w : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (u : ℂ → ℝ)
    (φ : TestOn upperHalfPlaneOpens) :
    ∫ z, couplingMean κ w t (fun y => -u (reflectC y)) z * (-reflTest φ) z =
      ∫ z, couplingMean κ (-w) t u z * φ z := by
  rw [← integral_comp_reflectC (fun z => couplingMean κ (-w) t u z * φ z)]
  congr 1
  funext z
  rw [couplingMean_reflect κ w ht]
  simp only [neg_apply, reflTest_apply]
  ring

theorem disjoint_reflTest {φ : TestOn upperHalfPlaneOpens} {K : Set ℂ}
    (h : Disjoint (tsupport φ) (reflectC '' K)) : Disjoint (tsupport ⇑(-reflTest φ)) K := by
  have e : ⇑(-reflTest φ) = -⇑(reflTest φ) := rfl
  rw [e, tsupport_neg, tsupport_reflTest]
  have h' := (Set.disjoint_image_iff LP.reflectC_injective).2 h
  rwa [reflectC_image_image] at h'

/-! ### The coupling -/

/-- **The optional hull coupling under `R(z) = −z̄`**: the reflected evolution `(−W, −V^R, −V^L, −B, ζ)` (sides
exchanged) and the reflected field `−h ∘ R` satisfy the frozen optional hull specification of the reflected word
`(−x_R; −x_L)`, `(ρ_R; ρ_L)`. -/
theorem IsOptionalHullCoupling.reflect {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hc : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    IsOptionalHullCoupling κ (fun i => -xR i) (fun i => -xL i) ρR ρL P 𝓕 (-W) (fun i => -VR i)
      (fun i => -VL i) (-B) ζ (fun ω => reflField (h ω)) := by
  obtain ⟨hev, hm, hgff, hX, hloc⟩ := hc
  refine ⟨hev.reflect, measurable_reflField.comp hm, fun u₀ hu₀ => ?_, isMeasurableKilledDriving_reflect hX,
    fun τ hτ' hτζ => ?_⟩
  · have hZ := isZBGFFProcess_refl (hgff _ (IsBoundedHarmonicExtension.reflect_force hu₀))
    have e : (fun φ ω => reflField (h ω) φ - ∫ z, u₀ z * φ z) = fun φ ω =>
        -(h ω (reflTest φ) - ∫ z, (fun y => -u₀ (reflectC y)) z * reflTest φ z) := by
      funext φ ω
      have hi : ∫ z, (fun y => -u₀ (reflectC y)) z * reflTest φ z = -∫ z, u₀ z * φ z := by
        rw [← integral_neg, ← integral_comp_reflectC (fun z => -(u₀ z * φ z))]
        congr 1
        funext z
        simp only [reflTest_apply, neg_mul]
      rw [hi, reflField_apply]
      ring
    rw [e]
    exact hZ
  · have hτ : IsStoppingTime (drivingFiltration P hX) τ := drivingFiltration_reflect P hX ▸ hτ'
    obtain ⟨hls, hlaw⟩ := hloc τ hτ hτζ
    have hw : ∀ ω, (fun s : ℝ => (-W) s.toNNReal ω) = -fun s : ℝ => W s.toNNReal ω := fun ω => rfl
    have hhull : ∀ ω, QuantumZipper.fwdHull (fun s : ℝ => (-W) s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) =
        reflectC '' QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) :=
      fun ω => by rw [hw ω, LP.fwdHull_neg]
    refine ⟨?_, fun u hu φ => ?_⟩
    · simp only [hhull]
      exact IsLocalSet.reflectC hls
    · have hu' : ∀ ω, IsBoundedHarmonicExtension
          (forceBoundaryData κ ρR ρL (fun i => -(VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
            (fun i => -(VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)))
          (forceJumpSet (fun i => -(VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
            (fun i => -(VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))) (u ω) := fun ω => by
        convert hu ω using 3 <;> simp only [Pi.neg_apply] <;> ring
      have hl := hlaw (fun ω y => -u ω (reflectC y)) (fun ω => IsBoundedHarmonicExtension.reflect_force (hu' ω))
        (-reflTest φ)
      filter_upwards [hl] with ω hω hdisj
      rw [hhull ω] at hdisj
      have hcm := IsStoppingTime.measurableSpace_congr (drivingFiltration_reflect P hX) hτ' hτ
      have e1 : (fun ω' => Complex.exp (Complex.I * ((reflField (h ω') φ : ℝ) : ℂ))) =
          fun ω' => Complex.exp (Complex.I * ((h ω' (-reflTest φ) : ℝ) : ℂ)) :=
        funext fun ω' => by rw [reflField_apply_eq]
      rw [hcm, e1, hω (disjoint_reflTest hdisj), hw ω,
        integral_couplingMean_reflect κ _ (NNReal.coe_nonneg _),
        loewnerGreenEnergy_reflect _ (NNReal.coe_nonneg _)]
      congr 4
      exact loewnerGreenEnergy_neg _ _ _

end FlowReflect

end Sec7

end InteractingSLE
