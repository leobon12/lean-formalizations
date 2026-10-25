import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.CMUM
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.GeodesicScale




 

set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

theorem badSetGeodesic_rescale
    (D E : LSCMetric) (k : ℝ) (hk : 0 < k)
    (hscale : ∀ x y : ℂ, E (x, y) = ENNReal.ofReal k * D (x, y))
    (K₁ K₂ U V : Set ℂ) :
    Geodesics.SetGeodesics.BadSetGeodesic D K₁ K₂ U V →
      Geodesics.SetGeodesics.BadSetGeodesic E K₁ K₂ U V := by
  rintro ⟨P, T, hP, hAvoid, Q, S, hQ, ⟨u, hu, huV⟩⟩
  refine ⟨P ∘ fun t => t / k, k * T,
    EndSaving.Scaling.setGeodesic_rescale D E k hk hscale K₁ K₂ P T hP,
    ?_, Q ∘ fun t => t / k, k * S,
    EndSaving.Scaling.setGeodesic_rescale D E k hk hscale K₁ K₂ Q S hQ, ?_⟩
  · intro t ht
    change P (t / k) ∉ U
    apply hAvoid
    constructor
    · exact div_nonneg ht.1 hk.le
    · apply (div_le_iff₀ hk).2
      simpa only [mul_comm] using ht.2
  · refine ⟨k * u, ?_, ?_⟩
    · exact ⟨mul_nonneg hk.le hu.1, mul_le_mul_of_nonneg_left hu.2 hk.le⟩
    · change Q ((k * u) / k) ∈ V
      simpa only [mul_div_cancel_left₀ _ hk.ne'] using huV

theorem badSetGeodesic_rescale_iff
    (D E : LSCMetric) (k : ℝ) (hk : 0 < k)
    (hscale : ∀ x y : ℂ, E (x, y) = ENNReal.ofReal k * D (x, y))
    (K₁ K₂ U V : Set ℂ) :
    Geodesics.SetGeodesics.BadSetGeodesic D K₁ K₂ U V ↔
      Geodesics.SetGeodesics.BadSetGeodesic E K₁ K₂ U V := by
  constructor
  · exact badSetGeodesic_rescale D E k hk hscale K₁ K₂ U V
  · have hkinv : 0 < 1 / k := one_div_pos.mpr hk
    have hInv : ∀ x y : ℂ,
        D (x, y) = ENNReal.ofReal (1 / k) * E (x, y) := by
      intro x y
      rw [hscale, ← mul_assoc, ← ENNReal.ofReal_mul hkinv.le]
      have hmul : (1 / k) * k = 1 := by field_simp
      simp only [hmul, ENNReal.ofReal_one, one_mul]
    exact badSetGeodesic_rescale E D (1 / k) hkinv hInv K₁ K₂ U V

 

theorem badSetGeoCode_addConst_iff_regular
    (D : LQGMetric.DistC → LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (g : LQGMetric.DistC) (hg : EndSaving.Choices.RegularAt D ξ g)
    (c : ℝ) (K₁ K₂ U V : Set ℂ) :
    Geodesics.SetGeodesics.BadSetGeoCode (D g) K₁ K₂ U V ↔
      Geodesics.SetGeodesics.BadSetGeoCode (D (LQGMetric.addConst g c)) K₁ K₂ U V := by
  let k := Real.exp (ξ * c)
  have hk : 0 < k := Real.exp_pos _
  have hscale : ∀ x y : ℂ,
      D (LQGMetric.addConst g c) (x, y) =
        ENNReal.ofReal k * D g (x, y) := by
    intro x y
    exact EndSaving.Scaling.metric_addConst_eq_mul_of_regular D ξ g hg c (x, y)
  have hweyl : ∀ p : ℂ × ℂ,
      D (LQGMetric.addConst g c) p =
        weylScale ξ (ContinuousMap.const ℂ c) (D g) p :=
    fun p => (congrFun (hg.weyl (ContinuousMap.const ℂ c)) p).symm
  have hforget2 : Continuous (BiLipschitz.Barrier.forget (D (LQGMetric.addConst g c))) :=
    Toolkit.WeylShift.continuous_forget_of_weyl (D g) (D (LQGMetric.addConst g c))
      ξ hξ (ContinuousMap.const ℂ c) hg.forget hweyl
  exact (Geodesics.SetGeodesics.badSetGeodesic_iff_code (D g) K₁ K₂ U V hg.forget).symm.trans
    ((badSetGeodesic_rescale_iff (D g) (D (LQGMetric.addConst g c))
      k hk hscale K₁ K₂ U V).trans
      (Geodesics.SetGeodesics.badSetGeodesic_iff_code
        (D (LQGMetric.addConst g c)) K₁ K₂ U V hforget2))

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
