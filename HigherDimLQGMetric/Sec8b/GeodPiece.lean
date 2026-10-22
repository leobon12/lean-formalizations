import HigherDimLQGMetric.Sec8b.StartDrop
import HigherDimLQGMetric.Sec6.Collar
import LQGMetric.Metric.CurveLength

/-! An affine restriction of a global geodesic is an internal geodesic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

theorem s7b_affine_geod_piece (D : ContMetric d) (P : ℝ → Rd d)
    (V : Set (Rd d)) {a b : ℝ}
    (hP : IsGeod D P) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hPV : ∀ t ∈ Icc a b, P t ∈ V) :
    ∃ R : ℝ → Rd d,
      IsGeodIn D V R ∧
      (∀ t ∈ Icc (0 : ℝ) 1, R t = P (a + t * (b - a))) ∧
      R 0 = P a ∧ R 1 = P b ∧
      D.len R 0 1 = D.len P a b := by
  let φ : ℝ → ℝ := fun t => a + t * (b - a)
  have hφmono : MonotoneOn φ (Icc (0 : ℝ) 1) := by
    intro s _ t _ hst
    change a + s * (b - a) ≤ a + t * (b - a)
    simpa only [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_right hst (sub_nonneg.mpr hab)) a)
  have hφcont : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
  have hφimg : φ '' Icc (0 : ℝ) 1 = Icc a b := by
    have hi := hφcont.image_Icc_of_monotoneOn zero_le_one hφmono
    convert hi using 1
    simp [φ]
  have hφmaps : MapsTo φ (Icc (0 : ℝ) 1) (Icc 0 1) := by
    intro t ht
    have htab : φ t ∈ Icc a b := hφimg ▸ ⟨t, ht, rfl⟩
    exact ⟨ha.trans htab.1, htab.2.trans hb⟩
  let R : ℝ → Rd d := P ∘ φ
  have hRc : ContinuousOn R (Icc (0 : ℝ) 1) := hP.1.comp hφcont hφmaps
  have hRV : ∀ t ∈ Icc (0 : ℝ) 1, R t ∈ V := by
    intro t ht
    exact hPV (φ t) (hφimg ▸ ⟨t, ht, rfl⟩)
  have hR0 : R 0 = P a := by simp [R, φ]
  have hR1 : R 1 = P b := by simp [R, φ]
  have hRlen : D.len R 0 1 = D.len P a b := by
    rw [D.len_def]
    have hcomp : (D.pt ∘ R) = (D.pt ∘ P) ∘ φ := rfl
    rw [hcomp, curveLength_comp_of_monotoneOn _ hφmono hφimg]
    rfl
  have hseg : D.len P a b = ENNReal.ofReal (D.1 (P a, P b)) := by
    exact le_antisymm (S6a.len_le_of_isGeod hP ha hab hb)
      (D.ofReal_le_len P hab)
  have hRint : D.internal V (R 0) (R 1) = D.len R 0 1 := by
    apply le_antisymm
    · exact D.internal_le_len zero_le_one hRc hRV
    · rw [hRlen, hseg, hR0, hR1]
      exact D.ofReal_le_internal V _ _
  exact ⟨R, ⟨hRc, hRV, hRint.symm⟩,
    (fun t _ => rfl), hR0, hR1, hRlen⟩

/-- A subsegment of the affine piece has the same length as the
corresponding subsegment of the original path. -/
theorem s7b_affine_piece_len (D : ContMetric d) (P R : ℝ → Rd d)
    {a b τ₁ τ₂ : ℝ} (hab : a ≤ b)
    (hτ₁ : 0 ≤ τ₁) (hτ₁₂ : τ₁ ≤ τ₂) (hτ₂ : τ₂ ≤ 1)
    (hR : ∀ t ∈ Icc (0 : ℝ) 1,
      R t = P (a + t * (b - a))) :
    D.len R τ₁ τ₂ =
      D.len P (a + τ₁ * (b - a)) (a + τ₂ * (b - a)) := by
  let φ : ℝ → ℝ := fun t => a + t * (b - a)
  have hφmono : Monotone φ := by
    intro s t hst
    change a + s * (b - a) ≤ a + t * (b - a)
    simpa only [add_comm] using
      (add_le_add_left
        (mul_le_mul_of_nonneg_right hst (sub_nonneg.mpr hab)) a)
  have hφcont : ContinuousOn φ (Icc τ₁ τ₂) :=
    (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
  have hφimg : φ '' Icc τ₁ τ₂ = Icc (φ τ₁) (φ τ₂) := by
    have hi := hφcont.image_Icc_of_monotoneOn hτ₁₂
      (hφmono.monotoneOn _)
    exact hi
  rw [D.len_def, D.len_def]
  have hcongr : EqOn (D.pt ∘ R) ((D.pt ∘ P) ∘ φ) (Icc τ₁ τ₂) := by
    intro t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 :=
      ⟨hτ₁.trans ht.1, ht.2.trans hτ₂⟩
    exact congrArg D.pt (hR t ht01)
  rw [curveLength_congr hcongr,
    curveLength_comp_of_monotoneOn _ (hφmono.monotoneOn _) hφimg]

end HigherDimLQGMetric
