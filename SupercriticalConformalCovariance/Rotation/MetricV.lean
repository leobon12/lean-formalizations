import SupercriticalConformalCovariance.Rotation.Metric

set_option autoImplicit false
noncomputable section

open MeasureTheory Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness

namespace SupercriticalConformalCovariance.Rotation

def rotOpen (a : ℂ) (U : TopologicalSpace.Opens ℂ) :
    TopologicalSpace.Opens ℂ :=
  ⟨(fun z : ℂ => a * z) ⁻¹' (U : Set ℂ),
    U.isOpen.preimage (by fun_prop)⟩

private def rotSet (a : ℂ) (K : Set ℂ) : Set ℂ :=
  (fun z : ℂ => a⁻¹ * z) '' K

private theorem rotOpen_mem_iff (a : ℂ) (ha : a ≠ 0)
    (U : TopologicalSpace.Opens ℂ) (z : ℂ) :
    a⁻¹ * z ∈ (rotOpen a U : Set ℂ) ↔ z ∈ U := by
  simp only [rotOpen, TopologicalSpace.Opens.coe_mk, mem_preimage,
    mul_inv_cancel_left₀ ha]
  rfl

private theorem rotSet_subset_rotOpen (a : ℂ) (ha : a ≠ 0)
    (U : TopologicalSpace.Opens ℂ) (K : Set ℂ)
    (hK : K ⊆ U) : rotSet a K ⊆ rotOpen a U := by
  rintro _ ⟨x, hx, rfl⟩
  exact (rotOpen_mem_iff a ha U x).2 (hK hx)

private theorem rotSet_isCompact (a : ℂ) (K : Set ℂ)
    (hK : IsCompact K) : IsCompact (rotSet a K) :=
  hK.image (by fun_prop)

private theorem rotSet_isConnected (a : ℂ) (K : Set ℂ)
    (hK : IsConnected K) : IsConnected (rotSet a K) :=
  hK.image _ (by fun_prop)

private theorem rotSet_nontrivial (a : ℂ) (ha : a ≠ 0)
    (K : Set ℂ) (hK : K.Nontrivial) : (rotSet a K).Nontrivial :=
  hK.image (GaussianLQG.mulCLE a⁻¹ (inv_ne_zero ha)).injective

private theorem rotSet_disjoint (a : ℂ) (ha : a ≠ 0)
    {K₁ K₂ : Set ℂ} (hK : Disjoint K₁ K₂) :
    Disjoint (rotSet a K₁) (rotSet a K₂) :=
  disjoint_image_of_injective
    (GaussianLQG.mulCLE a⁻¹ (inv_ne_zero ha)).injective hK

private theorem rotOpen_eq_rotSet (a : ℂ) (ha : a ≠ 0)
    (U : TopologicalSpace.Opens ℂ) :
    (rotOpen a U : Set ℂ) = rotSet a U := by
  ext z
  constructor
  · intro hz
    exact ⟨a * z, hz, by change a⁻¹ * (a * z) = z; rw [inv_mul_cancel_left₀ ha]⟩
  · rintro ⟨w, hw, rfl⟩
    exact (rotOpen_mem_iff a ha U w).2 hw

private theorem rotOpen_isConnected (a : ℂ) (ha : a ≠ 0)
    (U : TopologicalSpace.Opens ℂ) (hU : IsConnected (U : Set ℂ)) :
    IsConnected (rotOpen a U : Set ℂ) := by
  rw [rotOpen_eq_rotSet a ha U]
  exact rotSet_isConnected a U hU

private theorem internalSetDist_rotMetric_lt_top (M : LSCMetric)
    (a : ℂ) (ha : a ≠ 0) (U : TopologicalSpace.Opens ℂ)
    (K₁ K₂ : Set ℂ)
    (hfin : M.internalSetDist (rotOpen a U : Set ℂ)
      (Subtype.val ⁻¹' (rotSet a K₁)) (Subtype.val ⁻¹' (rotSet a K₂)) < ∞) :
    (rotMetric a ha M).internalSetDist (U : Set ℂ)
      (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂) < ∞ := by
  unfold LSCMetric.internalSetDist at hfin ⊢
  simp only [iInf_lt_iff] at hfin ⊢
  obtain ⟨x, hx, y, hy, hxy⟩ := hfin
  let x0 : (U : Set ℂ) := ⟨a * (x : ℂ), x.property⟩
  let y0 : (U : Set ℂ) := ⟨a * (y : ℂ), y.property⟩
  have hx0 : (x0 : ℂ) ∈ K₁ := by
    obtain ⟨w, hw, hwEq⟩ := hx
    change a * (x : ℂ) ∈ K₁
    rw [← hwEq, mul_inv_cancel_left₀ ha]
    exact hw
  have hy0 : (y0 : ℂ) ∈ K₂ := by
    obtain ⟨w, hw, hwEq⟩ := hy
    change a * (y : ℂ) ∈ K₂
    rw [← hwEq, mul_inv_cancel_left₀ ha]
    exact hw
  refine ⟨x0, hx0, y0, hy0, ?_⟩
  rw [internal_rotMetric M a ha (U : Set ℂ) (rotOpen a U : Set ℂ)
    (rotOpen_mem_iff a ha U)]
  simpa only [x0, y0, inv_mul_cancel_left₀ ha] using hxy

theorem ae_rotatedAssignment_finiteSetDist
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusCont h P) {a : ℂ} (ha : ‖a‖ = 1)
    (U : TopologicalSpace.Opens ℂ) (hU : IsConnected (U : Set ℂ))
    (K₁ K₂ : Set ℂ) (hc₁ : IsCompact K₁) (hc₂ : IsCompact K₂)
    (hconn₁ : IsConnected K₁) (hconn₂ : IsConnected K₂)
    (hn₁ : K₁.Nontrivial) (hn₂ : K₂.Nontrivial)
    (hsub₁ : K₁ ⊆ U) (hsub₂ : K₂ ⊆ U)
    (hdisj : Disjoint K₁ K₂) :
    ∀ᵐ ω ∂P,
      (rotatedAssignment a (GaussianLQG.ne_zero_of_norm_eq_one ha) D
        (h ω)).internalSetDist (U : Set ℂ)
        (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂) < ∞ := by
  let ha0 := GaussianLQG.ne_zero_of_norm_eq_one ha
  have hg := isGFFPlusCont_rotDist hh ha
  have hfin := hD.2.2.2.2.2 P (fun ω => GaussianLQG.rotDist a (h ω)) hg
    (rotOpen a U) (rotOpen_isConnected a ha0 U hU)
    (rotSet a K₁) (rotSet a K₂)
    (rotSet_isCompact a K₁ hc₁) (rotSet_isCompact a K₂ hc₂)
    (rotSet_isConnected a K₁ hconn₁) (rotSet_isConnected a K₂ hconn₂)
    (rotSet_nontrivial a ha0 K₁ hn₁) (rotSet_nontrivial a ha0 K₂ hn₂)
    (rotSet_subset_rotOpen a ha0 U K₁ hsub₁)
    (rotSet_subset_rotOpen a ha0 U K₂ hsub₂)
    (rotSet_disjoint a ha0 hdisj)
  filter_upwards [hfin] with ω hω
  exact internalSetDist_rotMetric_lt_top (D (GaussianLQG.rotDist a (h ω)))
    a ha0 U K₁ K₂ hω


end SupercriticalConformalCovariance.Rotation
