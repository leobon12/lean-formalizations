import HigherDimLQGMetric.DGZ.NondegIndep

/-!
# Compact set-distance observables for the DGZ joint state

Infima of continuous candidate metrics over fixed compact pairs vary continuously
under local uniform convergence. These observables make the exit relations closed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

/-- Minimum of a candidate metric over a compact set of endpoint pairs. -/
def nd_pairInf {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    (K : Set X) (D : C(X, ℝ)) : ℝ := sInf (D '' K)

theorem nd_continuous_pairInf {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] {K : Set X} (hK : IsCompact K) :
    Continuous (nd_pairInf K : C(X, ℝ) → ℝ) :=
  hK.continuous_sInf (f := fun (D : C(X, ℝ)) p => D p) continuous_eval

theorem nd_pairInf_le {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {K : Set X} (hK : IsCompact K) (D : C(X, ℝ)) {p : X} (hp : p ∈ K) :
    nd_pairInf K D ≤ D p :=
  csInf_le (hK.image D.continuous).bddBelow ⟨p, hp, rfl⟩

theorem nd_pairInf_nonneg {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {K : Set X} (D : C(X, ℝ)) (hD : ∀ p, 0 ≤ D p) :
    0 ≤ nd_pairInf K D :=
  Real.sInf_nonneg (by rintro _ ⟨p, -, rfl⟩; exact hD p)

/-- Minimum metric value between two compact subsets of `Rd`. -/
def nd_setInf (A B : Set (Rd d)) (D : C(Rd d × Rd d, ℝ)) : ℝ :=
  nd_pairInf (A ×ˢ B) D

theorem nd_continuous_setInf {A B : Set (Rd d)}
    (hA : IsCompact A) (hB : IsCompact B) :
    Continuous (nd_setInf A B : C(Rd d × Rd d, ℝ) → ℝ) :=
  nd_continuous_pairInf (hA.prod hB)

/-- The same observable on an open-domain internal metric. -/
def nd_internalSetInf {U : Set (Rd d)} [LocallyCompactSpace U] (A B : Set U)
    (D : C(U × U, ℝ)) : ℝ := nd_pairInf (A ×ˢ B) D

theorem nd_continuous_internalSetInf {U : Set (Rd d)} [LocallyCompactSpace U]
    {A B : Set U} (hA : IsCompact A) (hB : IsCompact B) :
    Continuous (nd_internalSetInf A B : C(U × U, ℝ) → ℝ) := by
  change Continuous (nd_pairInf (A ×ˢ B) : C(U × U, ℝ) → ℝ)
  exact nd_continuous_pairInf (hA.prod hB)

theorem nd_sInf_image_mul {X : Type*} (K : Set X) (f : X → ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    sInf ((fun x => a * f x) '' K) = a * sInf (f '' K) := by
  have heq : ((fun x => a * f x) '' K) = a • (f '' K) := by
    ext y
    simp only [Set.mem_image, Set.mem_smul_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
    · rintro ⟨v, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp [smul_eq_mul]⟩
  rw [heq, Real.sInf_smul_of_nonneg ha]
  simp only [smul_eq_mul]

theorem nd_setInf_normMetricC {φ : Rd d → ℝ} (hφ : Continuous φ)
    {a : ℝ} (ha : 0 < a) (ξ : ℝ) (A B : Set (Rd d)) :
    nd_setInf A B (normMetricC ξ φ a) =
      a⁻¹ * lfppSetDist ξ φ univ A B := by
  have hf : ∀ p : Rd d × Rd d,
      normMetricC ξ φ a p = a⁻¹ * lfppMetric ξ φ p.1 p.2 :=
    normMetricC_apply hφ a
  unfold nd_setInf nd_pairInf lfppSetDist
  simp_rw [hf]
  exact nd_sInf_image_mul (A ×ˢ B) (fun p => lfppMetric ξ φ p.1 p.2)
    (inv_nonneg.2 ha.le)

theorem nd_internalSetInf_apply {U : Set (Rd d)} [LocallyCompactSpace U]
    {φ : Rd d → ℝ} (hφ : Continuous φ) (hU : IsOpen U)
    (hUc : IsPreconnected U) (ξ a : ℝ) (A B : Set U) (ha : 0 ≤ a⁻¹) :
    nd_internalSetInf A B (internalMetricC ξ φ U a) =
      a⁻¹ * lfppSetDist ξ φ U ((↑) '' A) ((↑) '' B) := by
  have hf : ∀ p : U × U,
      internalMetricC ξ φ U a p = a⁻¹ * lfppDistOn ξ φ U p.1.1 p.2.1 :=
    internalMetricC_apply hφ hU hUc a
  unfold nd_internalSetInf nd_pairInf lfppSetDist
  simp_rw [hf]
  have himage : ((fun p : U × U => lfppDistOn ξ φ U p.1.1 p.2.1) '' (A ×ˢ B)) =
      ((fun p : Rd d × Rd d => lfppDistOn ξ φ U p.1 p.2) ''
        (((↑) '' A : Set (Rd d)) ×ˢ ((↑) '' B : Set (Rd d)))) := by
    ext y
    simp only [Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨p, ⟨hpA, hpB⟩, rfl⟩
      exact ⟨(p.1.1, p.2.1), ⟨⟨p.1, hpA, rfl⟩, ⟨p.2, hpB, rfl⟩⟩, rfl⟩
    · rintro ⟨p, ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩, hy⟩
      refine ⟨(u, v), ⟨hu, hv⟩, ?_⟩
      change lfppDistOn ξ φ U u.1 v.1 = y
      rw [hu', hv']
      exact hy
  rw [nd_sInf_image_mul _ _ ha, himage]

end HigherDimLQGMetric.DGZ
