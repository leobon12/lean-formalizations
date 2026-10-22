import HigherDimLQGMetric.Amplify.TrialLocal
import HigherDimLQGMetric.Amplify.NormWitness

/-! The deterministic return transfer from a fine-field trial to the full field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The four inequalities (15), in normalized form. The comparisons are the
output of Weyl scaling with a coarse oscillation at most `δ`. -/
theorem amplify_back_norm_bounds
    (D Dt : DistRd d → ContMetric d) (ξ Q cs c1 ℓ δ : ℝ) (hc1 : 0 < c1)
    {s : ℝ} (hs : 0 < s) (w : Rd d) (F H : DistRd d)
    (hT : F ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s w)
    (hDJ : ∀ u ∈ annCl w s (2 * s),
      ∀ v ∈ Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s),
      ENNReal.ofReal (Real.exp (-ξ * δ)) *
        normInt ξ Q D F s w (ann w (s / 2) (5 * s)) u v ≤
        normInt ξ Q D H s w (ann w (s / 2) (5 * s)) u v)
    (hDOlow : ∀ u v : Rd d,
      ENNReal.ofReal (Real.exp (-ξ * δ)) *
        normInt ξ Q D F s w (ann w (3 * s / 4) (3 * s)) u v ≤
        normInt ξ Q D H s w (ann w (3 * s / 4) (3 * s)) u v)
    (hDOhigh : ∀ u v : Rd d,
      normInt ξ Q D F s w (ann w (3 * s / 4) (3 * s)) u v ≤
        ENNReal.ofReal (Real.exp (ξ * δ)) *
          normInt ξ Q D H s w (ann w (3 * s / 4) (3 * s)) u v)
    (hDtO : ∀ u v : Rd d,
      normInt ξ Q Dt H s w (ann w (3 * s / 4) (3 * s)) u v ≤
        ENNReal.ofReal (Real.exp (ξ * δ)) *
          normInt ξ Q Dt F s w (ann w (3 * s / 4) (3 * s)) u v) :
    ENNReal.ofReal (Real.exp (-2 * ξ * δ) * (4 * max 1 cs⁻¹ * ℓ)) <
      amplify_normSetDist ξ Q D H s w (ann w (s / 2) (5 * s))
        (annCl w s (2 * s))
        (Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s)) ∧
    ∃ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ annCl w s (2 * s)) ∧
      ENNReal.ofReal (Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1))) ≤
        normInt ξ Q D H s w (ann w (3 * s / 4) (3 * s)) (P 0) (P 1) ∧
      curveLengthWith (normInt ξ Q Dt H s w (ann w (3 * s / 4) (3 * s))) P 0 1 ≤
        ENNReal.ofReal (Real.exp (2 * ξ * δ) * ℓ) ∧
      curveLengthWith (normInt ξ Q Dt H s w (ann w (3 * s / 4) (3 * s))) P 0 1 ≤
        ENNReal.ofReal (Real.exp (4 * ξ * δ) * c1) *
          normInt ξ Q D H s w (ann w (3 * s / 4) (3 * s)) (P 0) (P 1) := by
  let J := ann w (s / 2) (5 * s)
  let O := ann w (3 * s / 4) (3 * s)
  let K := annCl w s (2 * s)
  let B := Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s)
  let em := Real.exp (-ξ * δ)
  let ep := Real.exp (ξ * δ)
  have hem : 0 < em := Real.exp_pos _
  have hep : 0 < ep := Real.exp_pos _
  have hem0 : ENNReal.ofReal em ≠ 0 := (ENNReal.ofReal_pos.mpr hem).ne'
  have hemTop : ENNReal.ofReal em ≠ ⊤ := ENNReal.ofReal_ne_top
  have hem2 : em * em = Real.exp (-2 * ξ * δ) := by
    dsimp [em]
    rw [← Real.exp_add]
    congr 1
    ring
  have hep2 : ep * ep = Real.exp (2 * ξ * δ) := by
    dsimp [ep]
    rw [← Real.exp_add]
    congr 1
    ring
  have hep4 : ep * (Real.exp (2 * ξ * δ) * c1) * ep =
      Real.exp (4 * ξ * δ) * c1 := by
    rw [← hep2]
    have h : (ep * ep) * (ep * ep) = Real.exp (4 * ξ * δ) := by
      rw [hep2, ← Real.exp_add]
      congr 1
      ring
    calc
      ep * (ep * ep * c1) * ep = (ep * ep) * (ep * ep) * c1 := by ring
      _ = _ := by rw [h]
  obtain ⟨hcoll, P, hPc, hPK, hlow, hhigh, hratio⟩ :=
    (amplify_normTrial_iff D Dt ξ Q cs c1 ℓ δ hs w F).1 hT
  have hcmp : ENNReal.ofReal em * amplify_normSetDist ξ Q D F s w J K B ≤
      amplify_normSetDist ξ Q D H s w J K B := by
    unfold amplify_normSetDist
    simp only [ENNReal.mul_iInf_of_ne hem0 hemTop]
    exact iInf_mono fun u => iInf_mono fun hu =>
      iInf_mono fun v => iInf_mono fun hv => hDJ u hu v hv
  have hcoll' : ENNReal.ofReal (em * (em * (4 * max 1 cs⁻¹ * ℓ))) <
      amplify_normSetDist ξ Q D H s w J K B := by
    rw [ENNReal.ofReal_mul hem.le]
    calc
      ENNReal.ofReal em * ENNReal.ofReal (em * (4 * max 1 cs⁻¹ * ℓ)) <
          ENNReal.ofReal em * amplify_normSetDist ξ Q D F s w J K B := by
            simpa only [em, J, K, B, mul_comm, mul_left_comm, mul_assoc] using
              (ENNReal.mul_lt_mul_left hem0 hemTop hcoll)
      _ ≤ amplify_normSetDist ξ Q D H s w J K B := hcmp
  have hlen : curveLengthWith (normInt ξ Q Dt H s w O) P 0 1 ≤
      ENNReal.ofReal ep * curveLengthWith (normInt ξ Q Dt F s w O) P 0 1 := by
    rw [← curveLengthWith_const_mul]
    exact curveLengthWith_mono fun (u v : ℝ) _ _ _ => hDtO (P u) (P v)
  refine ⟨?_, P, hPc, hPK, ?_, ?_, ?_⟩
  · have heq : Real.exp (-2 * ξ * δ) * (4 * max 1 cs⁻¹ * ℓ) =
        em * (em * (4 * max 1 cs⁻¹ * ℓ)) := by
      calc
        _ = (em * em) * (4 * max 1 cs⁻¹ * ℓ) := by rw [hem2]
        _ = _ := by ring
    simpa only [J, K, B, heq] using hcoll'
  · calc
      ENNReal.ofReal (Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1))) =
          ENNReal.ofReal em * ENNReal.ofReal (em * (ℓ / (2 * c1))) := by
            rw [← ENNReal.ofReal_mul hem.le, ← mul_assoc]
            congr 1
            rw [hem2]
      _ ≤ ENNReal.ofReal em * normInt ξ Q D F s w O (P 0) (P 1) := by gcongr
      _ ≤ normInt ξ Q D H s w O (P 0) (P 1) := hDOlow _ _
  · calc
      curveLengthWith (normInt ξ Q Dt H s w O) P 0 1 ≤
          ENNReal.ofReal ep * curveLengthWith (normInt ξ Q Dt F s w O) P 0 1 := hlen
      _ ≤ ENNReal.ofReal ep * ENNReal.ofReal (ep * ℓ) := by gcongr
      _ = ENNReal.ofReal (Real.exp (2 * ξ * δ) * ℓ) := by
            rw [← ENNReal.ofReal_mul hep.le, ← mul_assoc]
            congr 1
            rw [hep2]
  · calc
      curveLengthWith (normInt ξ Q Dt H s w O) P 0 1 ≤
          ENNReal.ofReal ep * curveLengthWith (normInt ξ Q Dt F s w O) P 0 1 := hlen
      _ ≤ ENNReal.ofReal ep *
          (ENNReal.ofReal (Real.exp (2 * ξ * δ) * c1) *
            normInt ξ Q D F s w O (P 0) (P 1)) := by gcongr
      _ ≤ ENNReal.ofReal ep *
          (ENNReal.ofReal (Real.exp (2 * ξ * δ) * c1) *
            (ENNReal.ofReal ep * normInt ξ Q D H s w O (P 0) (P 1))) := by
              gcongr
              exact hDOhigh _ _
      _ = ENNReal.ofReal (Real.exp (4 * ξ * δ) * c1) *
          normInt ξ Q D H s w O (P 0) (P 1) := by
            calc
              ENNReal.ofReal ep *
                  (ENNReal.ofReal (Real.exp (2 * ξ * δ) * c1) *
                    (ENNReal.ofReal ep * normInt ξ Q D H s w O (P 0) (P 1))) =
                  (ENNReal.ofReal ep * ENNReal.ofReal (Real.exp (2 * ξ * δ) * c1) *
                    ENNReal.ofReal ep) * normInt ξ Q D H s w O (P 0) (P 1) := by ac_rfl
              _ = ENNReal.ofReal (ep * (Real.exp (2 * ξ * δ) * c1) * ep) *
                  normInt ξ Q D H s w O (P 0) (P 1) := by
                    rw [← ENNReal.ofReal_mul hep.le,
                      ← ENNReal.ofReal_mul (mul_nonneg hep.le
                        (mul_nonneg (Real.exp_pos _).le hc1.le))]
              _ = _ := by rw [hep4]

end HigherDimLQGMetric
