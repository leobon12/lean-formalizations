import HigherDimLQGMetric.Amplify.NormWitness

/-! Deterministic transfer of a full-field witness to a fine-field trial,
given the normalized metric comparisons supplied by Weyl scaling. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

theorem amplify_normSetDist_union (ξ Q : ℝ)
    (D : DistRd d → ContMetric d) (g : DistRd d) (s : ℝ) (w : Rd d)
    (V K B₁ B₂ : Set (Rd d)) :
    amplify_normSetDist ξ Q D g s w V K (B₁ ∪ B₂) =
      amplify_normSetDist ξ Q D g s w V K B₁ ⊓
        amplify_normSetDist ξ Q D g s w V K B₂ := by
  unfold amplify_normSetDist
  apply le_antisymm
  · refine le_inf ?_ ?_
    · refine le_iInf fun u => le_iInf fun hu => le_iInf fun v => le_iInf fun hv => ?_
      exact iInf_le_of_le u (iInf_le_of_le hu
        (iInf_le_of_le v (iInf_le_of_le (Or.inl hv) le_rfl)))
    · refine le_iInf fun u => le_iInf fun hu => le_iInf fun v => le_iInf fun hv => ?_
      exact iInf_le_of_le u (iInf_le_of_le hu
        (iInf_le_of_le v (iInf_le_of_le (Or.inr hv) le_rfl)))
  · refine le_iInf fun u => le_iInf fun hu => le_iInf fun v => le_iInf fun hv => ?_
    rcases hv with hv | hv
    · exact (inf_le_left).trans (iInf_le_of_le u (iInf_le_of_le hu
        (iInf_le_of_le v (iInf_le_of_le hv le_rfl))))
    · exact (inf_le_right).trans (iInf_le_of_le u (iInf_le_of_le hu
        (iInf_le_of_le v (iInf_le_of_le hv le_rfl))))

/-- Transfer the witness to the fine field under the four local normalized
metric inequalities arising from a bounded coarse oscillation. -/
theorem amplify_trial_of_wit_norm_bounds
    (D Dt : DistRd d → ContMetric d)
    (ξ Q cs a A₀ ℓ β₀ c1 δ : ℝ) (hc1 : 0 < c1) (hℓ : 0 < ℓ)
    {s : ℝ} (hs : 0 < s) (w : Rd d) (H F : DistRd d)
    (hW : H ∈ WitEvent Dt D ξ Q cs⁻¹ a A₀ ℓ β₀ c1⁻¹ s w)
    (hDJ : ∀ u ∈ annCl w s (2 * s),
      ∀ v ∈ Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s),
      ENNReal.ofReal (Real.exp (-ξ * δ)) *
          normInt ξ Q D H s w (ann w (s / 2) (5 * s)) u v ≤
        normInt ξ Q D F s w (ann w (s / 2) (5 * s)) u v)
    (hDOlow : ∀ u v : Rd d,
      ENNReal.ofReal (Real.exp (-ξ * δ)) *
          normInt ξ Q D H s w (ann w (3 * s / 4) (3 * s)) u v ≤
        normInt ξ Q D F s w (ann w (3 * s / 4) (3 * s)) u v)
    (hDOhigh : ∀ u v : Rd d,
      normInt ξ Q D H s w (ann w (3 * s / 4) (3 * s)) u v ≤
        ENNReal.ofReal (Real.exp (ξ * δ)) *
          normInt ξ Q D F s w (ann w (3 * s / 4) (3 * s)) u v)
    (hDtO : ∀ u v : Rd d,
      normInt ξ Q Dt F s w (ann w (3 * s / 4) (3 * s)) u v ≤
        ENNReal.ofReal (Real.exp (ξ * δ)) *
          normInt ξ Q Dt H s w (ann w (3 * s / 4) (3 * s)) u v) :
    F ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s w := by
  let J := ann w (s / 2) (5 * s)
  let O := ann w (3 * s / 4) (3 * s)
  let K := annCl w s (2 * s)
  let B := Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s)
  let ep := Real.exp (ξ * δ)
  let em := Real.exp (-ξ * δ)
  have hep : 0 < ep := Real.exp_pos _
  have hem : 0 < em := Real.exp_pos _
  obtain ⟨hcoll, P, hPc, hPK, hLow, hHigh, hRatio⟩ :=
    amplify_wit_normalized_data D Dt ξ Q cs a A₀ ℓ β₀ c1 hs w H hW
  have htr : amplify_normTrial D Dt ξ Q cs c1 ℓ δ s w F := by
    dsimp [amplify_normTrial]
    constructor
    · -- A strict bound transfers through each sphere infimum; the union is finite.
      have hpos : ENNReal.ofReal em ≠ 0 := (ENNReal.ofReal_pos.mpr hem).ne'
      have hfin : ENNReal.ofReal em ≠ ⊤ := ENNReal.ofReal_ne_top
      have hcmp (S : Set (Rd d)) (hSB : S ⊆ B) :
          ENNReal.ofReal em * amplify_normSetDist ξ Q D H s w J K S ≤
            amplify_normSetDist ξ Q D F s w J K S := by
        unfold amplify_normSetDist
        simp only [ENNReal.mul_iInf_of_ne hpos hfin]
        exact iInf_mono fun u => iInf_mono fun hu =>
          iInf_mono fun v => iInf_mono fun hv => hDJ u hu v (hSB hv)
      have hstrict (ρ : ℝ) (hρ : ρ ∈ ({3 * s / 4, 3 * s} : Set ℝ))
          (hsub : Metric.sphere w ρ ⊆ B) :
          ENNReal.ofReal (em * (4 * max 1 cs⁻¹ * ℓ)) <
            amplify_normSetDist ξ Q D F s w J K (Metric.sphere w ρ) := by
        rw [ENNReal.ofReal_mul hem.le]
        have hm : ENNReal.ofReal em * ENNReal.ofReal (4 * max 1 cs⁻¹ * ℓ) <
            ENNReal.ofReal em * amplify_normSetDist ξ Q D H s w J K
              (Metric.sphere w ρ) := by
          calc
            ENNReal.ofReal em * ENNReal.ofReal (4 * max 1 cs⁻¹ * ℓ) =
                ENNReal.ofReal (4 * max 1 cs⁻¹ * ℓ) * ENNReal.ofReal em := mul_comm _ _
            _ < amplify_normSetDist ξ Q D H s w J K (Metric.sphere w ρ) *
                ENNReal.ofReal em := ENNReal.mul_lt_mul_left hpos hfin (hcoll ρ hρ)
            _ = ENNReal.ofReal em * amplify_normSetDist ξ Q D H s w J K
                (Metric.sphere w ρ) := mul_comm _ _
        exact hm.trans_le (hcmp _ hsub)
      have h₁ := hstrict (3 * s / 4) (by simp) (subset_union_left)
      have h₂ := hstrict (3 * s) (by simp) (subset_union_right)
      simpa only [J, K, B, em, amplify_normSetDist_union] using
        ((lt_inf_iff).2 ⟨h₁, h₂⟩)
    · have hDFl := hDOlow (P 0) (P 1)
      have hDFh := hDOhigh (P 0) (P 1)
      have hlenF : curveLengthWith (normInt ξ Q Dt F s w O) P 0 1 ≤
          ENNReal.ofReal ep * curveLengthWith (normInt ξ Q Dt H s w O) P 0 1 := by
        rw [← curveLengthWith_const_mul]
        exact curveLengthWith_mono fun (u v : ℝ) _ _ _ => hDtO (P u) (P v)
      refine ⟨P, hPc, hPK, ?_, ?_, ?_⟩
      -- The three path inequalities now follow by positive scalar arithmetic.
      · -- lower endpoint separation
        have hpair : ENNReal.ofReal c1⁻¹ * ENNReal.ofReal (ℓ / 2) ≤
            normInt ξ Q D H s w O (P 0) (P 1) :=
          (by
            have hmul : ENNReal.ofReal c1⁻¹ * ENNReal.ofReal (ℓ / 2) ≤
                ENNReal.ofReal c1⁻¹ *
                  curveLengthWith (normInt ξ Q Dt H s w O) P 0 1 := by gcongr
            exact hmul.trans hRatio.le)
        calc
          ENNReal.ofReal (em * (ℓ / (2 * c1))) =
              ENNReal.ofReal em *
                (ENNReal.ofReal c1⁻¹ * ENNReal.ofReal (ℓ / 2)) := by
                  have hre : ℓ / (2 * c1) = c1⁻¹ * (ℓ / 2) := by
                    field_simp
                  rw [hre, ENNReal.ofReal_mul hem.le,
                    ENNReal.ofReal_mul (inv_nonneg.mpr hc1.le)]
          _ ≤ ENNReal.ofReal em * normInt ξ Q D H s w O (P 0) (P 1) := by gcongr
          _ ≤ normInt ξ Q D F s w O (P 0) (P 1) := hDFl
      · -- upper fine-field length
        calc
          curveLengthWith (normInt ξ Q Dt F s w O) P 0 1 ≤
              ENNReal.ofReal ep * curveLengthWith (normInt ξ Q Dt H s w O) P 0 1 := hlenF
          _ ≤ ENNReal.ofReal ep * ENNReal.ofReal ℓ := by gcongr
          _ = ENNReal.ofReal (ep * ℓ) := by rw [ENNReal.ofReal_mul hep.le]
      · -- endpoint ratio
        have hR : curveLengthWith (normInt ξ Q Dt H s w O) P 0 1 ≤
            ENNReal.ofReal c1 * normInt ξ Q D H s w O (P 0) (P 1) := by
          have hscaled : ENNReal.ofReal c1 *
              (ENNReal.ofReal c1⁻¹ *
                curveLengthWith (normInt ξ Q Dt H s w O) P 0 1) ≤
              ENNReal.ofReal c1 * normInt ξ Q D H s w O (P 0) (P 1) := by
            gcongr
          have hcancel : ENNReal.ofReal c1 * ENNReal.ofReal c1⁻¹ = 1 := by
            rw [← ENNReal.ofReal_mul hc1.le, mul_inv_cancel₀ hc1.ne']
            norm_num
          simpa only [← mul_assoc, hcancel, one_mul] using hscaled
        calc
          curveLengthWith (normInt ξ Q Dt F s w O) P 0 1 ≤
              ENNReal.ofReal ep * curveLengthWith (normInt ξ Q Dt H s w O) P 0 1 := hlenF
          _ ≤ ENNReal.ofReal ep *
              (ENNReal.ofReal c1 * normInt ξ Q D H s w O (P 0) (P 1)) := by gcongr
          _ ≤ ENNReal.ofReal ep *
              (ENNReal.ofReal c1 * (ENNReal.ofReal ep *
                normInt ξ Q D F s w O (P 0) (P 1))) := by
                  gcongr
          _ = ENNReal.ofReal (Real.exp (2 * ξ * δ) * c1) *
                normInt ξ Q D F s w O (P 0) (P 1) := by
                  have hre : ep * c1 * ep = Real.exp (2 * ξ * δ) * c1 := by
                    dsimp [ep]
                    calc
                      Real.exp (ξ * δ) * c1 * Real.exp (ξ * δ) =
                          (Real.exp (ξ * δ) * Real.exp (ξ * δ)) * c1 := by ring
                      _ = Real.exp (2 * ξ * δ) * c1 := by
                            rw [← Real.exp_add]
                            congr 1
                            ring
                  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hep.le,
                    ← ENNReal.ofReal_mul (mul_nonneg hep.le hc1.le), hre]
  exact (amplify_normTrial_iff D Dt ξ Q cs c1 ℓ δ hs w F).2 htr

end HigherDimLQGMetric
