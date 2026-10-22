import HigherDimLQGMetric.Shell.Geom
import LQGMetric.Metric.Geodesic

/-!
# Across distances are determined by an internal metric

Port of `LQGMetric.GM.setDist_spheres_eq_internal` from `ℂ` to `Rd d`.
The path segment between the last inner-sphere hit and the first outer-sphere hit
stays in the closed annulus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric Filter Topology
open scoped ENNReal
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- A length metric's across distance can be computed using the internal metric of any
neighbourhood of the closed annulus. -/
theorem acrossDist_eq_setDistIn (D : ContMetric d) (hD : D.IsLength)
    {V : Set (Rd d)} {z : Rd d} {a b : ℝ} (_hV : IsOpen V) (hab : a < b)
    (hsub : annCl z a b ⊆ V) :
    acrossDist D z a b = setDistIn D V (sphere z a) (sphere z b) := by
  unfold acrossDist setDistIn
  refine le_antisymm (iInf₂_mono fun x _ => iInf₂_mono fun y _ => D.ofReal_le_internal V x y)
    (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨P, hPc, hPa, hPb, hlen⟩ :=
    (D.isLength_iff_curves.mp hD) x y ε (by exact_mod_cast hε)
  set f : ℝ → ℝ := fun t => ‖P t - z‖ with hf
  have hfc : ContinuousOn f (Icc 0 1) :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).comp_continuousOn hPc
  have hfa : f 0 = a := by simpa only [hf, hPa] using mem_sphere_iff_norm.mp hx
  have hfb : f 1 = b := by simpa only [hf, hPb] using mem_sphere_iff_norm.mp hy
  obtain ⟨t₂, ht₂, hft₂, hbef⟩ := exists_first_hit (P := f) hfc (isClosed_Ici (a := b))
    ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [hfb]; exact mem_Ici.2 le_rfl⟩
  have hft₂' : b ≤ f t₂ := hft₂
  have hat₂ : 0 < t₂ := by
    rcases ht₂.1.eq_or_lt with h | h
    · rw [← h, hfa] at hft₂'; linarith
    · exact h
  have hf2 : f t₂ = b := by
    refine le_antisymm ?_ hft₂'
    have hne : (𝓝[Ico 0 t₂] t₂).NeBot := right_nhdsWithin_Ico_neBot hat₂
    have hcw : ContinuousWithinAt f (Ico 0 t₂) t₂ :=
      (hfc t₂ ht₂).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht₂.2))
    exact le_of_tendsto hcw (eventually_nhdsWithin_of_forall fun t ht =>
      (not_le.1 fun h => hbef t ht (mem_Ici.2 h)).le)
  set S : Set ℝ := Icc 0 t₂ ∩ f ⁻¹' Iic a with hS
  have hSc : IsClosed S :=
    (hfc.mono (Icc_subset_Icc le_rfl ht₂.2)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
  have hSne : S.Nonempty := ⟨0, ⟨le_rfl, hat₂.le⟩,
    by rw [mem_preimage, hfa]; exact mem_Iic.2 le_rfl⟩
  have hSb : BddAbove S := ⟨t₂, fun t ht => ht.1.2⟩
  set t₁ := sSup S with ht₁def
  have ht₁S : t₁ ∈ S := hSc.csSup_mem hSne hSb
  have hft₁ : f t₁ ≤ a := ht₁S.2
  have hafter : ∀ t ∈ Ioc t₁ t₂, a < f t := fun t ht => by
    by_contra hc
    exact absurd (le_csSup hSb ⟨⟨ht₁S.1.1.trans ht.1.le, ht.2⟩,
      mem_Iic.2 (not_lt.1 hc)⟩) (not_le.2 ht.1)
  have ht₁₂ : t₁ < t₂ := by
    rcases ht₁S.1.2.eq_or_lt with h | h
    · rw [h, hf2] at hft₁; linarith
    · exact h
  have hf1 : f t₁ = a := by
    refine le_antisymm hft₁ ?_
    have hne : (𝓝[Ioc t₁ t₂] t₁).NeBot := left_nhdsWithin_Ioc_neBot ht₁₂
    have hcw : ContinuousWithinAt f (Ioc t₁ t₂) t₁ :=
      (hfc t₁ ⟨ht₁S.1.1, ht₁S.1.2.trans ht₂.2⟩).mono
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht₁S.1.1 ht₂.2))
    exact ge_of_tendsto hcw (eventually_nhdsWithin_of_forall fun t ht => (hafter t ht).le)
  have hsub12 : Icc t₁ t₂ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ht₁S.1.1 ht₂.2
  have hmaps : MapsTo P (Icc t₁ t₂) V := fun t ht => by
    apply hsub
    constructor
    · rcases ht.1.eq_or_lt with h | h
      · rw [← h]; exact hf1.ge
      · exact (hafter t ⟨h, ht.2⟩).le
    · rcases ht.2.eq_or_lt with h | h
      · rw [h]; exact hf2.le
      · exact (not_le.1 fun hc => hbef t ⟨ht₁S.1.1.trans ht.1, h⟩
          (mem_Ici.2 hc)).le
  have hx' : P t₁ ∈ sphere z a := mem_sphere_iff_norm.2 hf1
  have hy' : P t₂ ∈ sphere z b := mem_sphere_iff_norm.2 hf2
  calc
    ⨅ x ∈ sphere z a, ⨅ y ∈ sphere z b, D.internal V x y
        ≤ D.internal V (P t₁) (P t₂) := iInf₂_le_of_le _ hx' (iInf₂_le _ hy')
    _ ≤ D.len P t₁ t₂ := D.internal_le_len ht₁₂.le (hPc.mono hsub12) hmaps
    _ ≤ D.len P 0 1 := eVariationOn.mono _ hsub12
    _ ≤ ENNReal.ofReal (D.1 (x, y)) + ENNReal.ofReal ε := hlen
    _ = ENNReal.ofReal (D.1 (x, y)) + ε := by rw [ENNReal.ofReal_coe_nnreal]

end HigherDimLQGMetric
