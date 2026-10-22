import HigherDimLQGContinuity.Improve.StepDepth
import HigherDimLQGContinuity.Improve.SeedDepth
import HigherDimLQGContinuity.Improve.SeedClip

/-!
# One fixed polynomial depth after the certificate parameters are selected
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- A factor four pays separately for the forcing depth, the certificate
lower bound, the tolerance, and every fixed auxiliary threshold. -/
theorem q11_step_choice {A45 k45 Ap kp L d0 a v θ : ℝ}
    (hL : 1 ≤ L) (hd0 : 0 < d0) (ha : 0 < a) (hv : 0 < v)
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (hθlo : Real.exp (-polyB Ap kp 0 v⁻¹) ≤ θ) :
    let dclip := min 1 (d0 / 2)
    let C := max L (max 0 (Real.log dclip⁻¹))
    let A := 4 * (|A45| + |Ap| + C + 3)
    let k := max (max k45 kp) 1
    let V := polyB A k a⁻¹ v⁻¹
    let Δ := Real.exp (-V)
    1 ≤ V ∧ L ≤ V ∧ a⁻¹ ≤ V ∧ v⁻¹ ≤ V ∧
      polyB Ap kp 0 v⁻¹ ≤ V ∧
      polyB A45 k45 a⁻¹ v⁻¹ ≤ V ∧
      Δ ≤ v * min 1 (θ * d0 / 2) := by
  let dclip : ℝ := min 1 (d0 / 2)
  let C : ℝ := max L (max 0 (Real.log dclip⁻¹))
  let A0 : ℝ := |A45| + |Ap| + C + 3
  let k : ℝ := max (max k45 kp) 1
  let V0 : ℝ := polyB A0 k a⁻¹ v⁻¹
  let V : ℝ := polyB (4 * A0) k a⁻¹ v⁻¹
  have hc := q11_seed_clip hθ hθ1.le hd0
  have hdclip : 0 < dclip := hc.1
  have hC0 : 0 ≤ C := by dsimp [C]; linarith [le_max_right L (max 0 (Real.log dclip⁻¹)), le_max_left (0 : ℝ) (Real.log dclip⁻¹)]
  have hLC : L ≤ C := le_max_left _ _
  have hlogC : Real.log dclip⁻¹ ≤ C :=
    (le_max_right (0 : ℝ) _).trans (le_max_right L _)
  obtain ⟨hV01, haV0, hvV0, hpV0, h45V0, -⟩ :=
    q11_step_depth_site (A45 := A45) (k45 := k45)
      (Ap := Ap) (kp := kp) (C := C) hC0 ha hv
  have hVeq : V = 4 * V0 := by
    dsimp [V, V0, A0, polyB]
    ring
  have hCsmall : C ≤ V0 := by
    have hX : 1 ≤ 1 + a⁻¹ + v⁻¹ := by
      have := inv_pos.mpr ha
      have := inv_pos.mpr hv
      linarith
    have hk : 0 ≤ k := by dsimp [k]; linarith [le_max_right (max k45 kp) (1 : ℝ)]
    have hpow : 1 ≤ (1 + a⁻¹ + v⁻¹) ^ k := Real.one_le_rpow hX hk
    have hA0 : C ≤ A0 := by dsimp [A0]; linarith [abs_nonneg A45, abs_nonneg Ap]
    change C ≤ A0 * (1 + a⁻¹ + v⁻¹) ^ k
    have hApos : 0 ≤ A0 := by linarith
    exact hA0.trans (le_mul_of_one_le_right hApos hpow)
  have hlogv : Real.log v⁻¹ ≤ V0 :=
    (Real.log_le_self (inv_pos.mpr hv).le).trans hvV0
  have hsum : polyB Ap kp 0 v⁻¹ + Real.log v⁻¹ +
      Real.log dclip⁻¹ ≤ V := by
    rw [hVeq]
    have hlogd : Real.log dclip⁻¹ ≤ V0 := hlogC.trans hCsmall
    linarith only [hpV0, hlogv, hlogd, hV01]
  have hΔseed : Real.exp (-V) ≤ v * (θ * dclip) := by
    have h := q11_depth_below_seed hθ (show 0 < 2 * dclip by positivity)
      hv hθlo
      (by simpa only [show (2 * dclip) / 2 = dclip by ring,
        show (2 : ℝ) / (2 * dclip) = dclip⁻¹ by field_simp] using hsum)
    simpa only [show θ * (2 * dclip) / 2 = θ * dclip by ring] using h
  have hseed : θ * dclip ≤ min 1 (θ * d0 / 2) := hc.2.2.2.1
  have hV1 : 1 ≤ V := by rw [hVeq]; linarith only [hV01]
  have hLV : L ≤ V := by rw [hVeq]; linarith only [hLC, hCsmall, hV01]
  change 1 ≤ V ∧ L ≤ V ∧ a⁻¹ ≤ V ∧ v⁻¹ ≤ V ∧
      polyB Ap kp 0 v⁻¹ ≤ V ∧ polyB A45 k45 a⁻¹ v⁻¹ ≤ V ∧
      Real.exp (-V) ≤ v * min 1 (θ * d0 / 2)
  refine ⟨hV1, hLV, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hVeq]; linarith only [haV0, hV01]
  · rw [hVeq]; linarith only [hvV0, hV01]
  · rw [hVeq]; linarith only [hpV0, hV01]
  · rw [hVeq]; linarith only [h45V0, hV01]
  · exact hΔseed.trans (mul_le_mul_of_nonneg_left hseed hv.le)

end HigherDimLQGContinuity
