import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo
import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcMeas
import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-EXCLOWER: `FLExcLowerStmt` (lower bound in the proof of Field–Lawler Prop. 3.1)

`flExcLower_holds : FLExcLowerStmt`: for a crosscut `η` of `ℍ` with real endpoints `a = η(0+)`,
`b = η(1−)` on one side of `0`, `ℰ_ℍ(η, opposite half-line) ≥ c₁ (diam η/|a| ∧ 1)`
(L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015), proof of
Prop. 3.1, p. 7, where it is taken from their Cor. 5.2, pp. 12–13).

Proof: reverse the parameter if `|b| < |a|` (the bound for the endpoint closer to `0` is the
stronger one), then normalize by the similarity `flSim σ |a|` (`σ = −sign a`), which maps `a` to
`−1`, `b` to a point `≤ −1`, divides the diameter by `|a|`, preserves harmonic measure
(`flSim_isHarmMeas`) and does not increase the excursion integral (`flSim_excR_le`, conformal
invariance, Lawler, *Conformally invariant processes in the plane*, §5.2); the normalized bound
`flExcNorm_holds` is the lower half of the key estimate of Lawler–Werness (Ann. Probab. 41 (2013),
proof of Lemma 4.3, p. 24) with `diam η` replaced by `diam η ∧ 1`. We do not follow FL's own
proof of Cor. 5.2 (which goes through their Lemma 5.1 on Brownian excursions); own elementary
route via the repository's proof of LW Lemma 4.3.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

lemma fl_set_eq {a b : ℝ} (hab : 0 < a * b) : {x : ℝ | x * b ≤ 0} = {x : ℝ | x * a ≤ 0} := by
  ext x
  simp only [mem_setOf_eq]
  constructor
  · intro hx; by_contra hc; push Not at hc
    nlinarith [mul_pos hc hab, mul_nonpos_of_nonpos_of_nonneg hx (mul_self_nonneg a)]
  · intro hx; by_contra hc; push Not at hc
    nlinarith [mul_pos hc hab, mul_nonpos_of_nonpos_of_nonneg hx (mul_self_nonneg b)]

/-- The bound when `a` is the endpoint closer to `0`. -/
theorem flExcLower_ordered {c : ℝ}
    (hN : ∀ (η : ℝ → ℂ) (a : ℝ) (h : ℂ → ℝ),
      IsCrosscutH η → Tendsto η (𝓝[>] 0) (𝓝 (-1 : ℂ)) → Tendsto η (𝓝[<] 1) (𝓝 (a : ℂ)) →
      a ≤ -1 → IsHarmMeas (hullComp η) (arcH η) h →
      ENNReal.ofReal (c * min (Metric.diam (arcH η)) 1) ≤ excR h (Ici 0))
    (η : ℝ → ℂ) (a b : ℝ) (h : ℂ → ℝ) (hη : IsCrosscutH η)
    (h0 : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (h1 : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hab : 0 < a * b) (hle : |a| ≤ |b|) (hh : IsHarmMeas (hullComp η) (arcH η) h) :
    ENNReal.ofReal (c * min (Metric.diam (arcH η) / |a|) 1) ≤ excR h {x : ℝ | x * a ≤ 0} := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab
  set σ : ℝ := if a < 0 then 1 else -1 with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by
    by_cases ha : a < 0
    · left; simp [hσdef, ha]
    · right; simp [hσdef, ha]
  set m : ℝ := |a| with hmdef
  have hm : 0 < m := abs_pos.2 ha0
  set e := flSimHomeo σ m (fl_sigma_sq hσ) hm.ne' with he
  have hcoe : ∀ z, e z = flSim σ m z := fun z => rfl
  -- endpoint values
  have hA : σ * a / m = -1 := by
    rw [div_eq_iff hm.ne']
    by_cases ha : a < 0
    · simp [hσdef, ha, hmdef, abs_of_neg ha]
    · push Not at ha
      have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      simp [hσdef, not_lt.2 ha, hmdef, abs_of_pos ha']
  have hB : σ * b / m ≤ -1 := by
    rw [div_le_iff₀ hm]
    by_cases ha : a < 0
    · have hb : b < 0 := by
        by_contra hb; push Not at hb; nlinarith
      simp only [hσdef, if_pos ha, hmdef, abs_of_neg ha]
      rw [hmdef, abs_of_neg ha, abs_of_neg hb] at hle; linarith
    · push Not at ha
      have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb : 0 < b := by
        by_contra hb; push Not at hb; nlinarith
      simp only [hσdef, if_neg (not_lt.2 ha), hmdef, abs_of_pos ha']
      rw [hmdef, abs_of_pos ha', abs_of_pos hb] at hle; linarith
  have h0' : Tendsto (fun t => e (η t)) (𝓝[>] 0) (𝓝 (-1 : ℂ)) := by
    have := (e.continuous.tendsto _).comp h0
    rwa [hcoe, flSim_real, hA, Complex.ofReal_neg, Complex.ofReal_one] at this
  have h1' : Tendsto (fun t => e (η t)) (𝓝[<] 1) (𝓝 ((σ * b / m : ℝ) : ℂ)) := by
    have := (e.continuous.tendsto _).comp h1
    rwa [hcoe, flSim_real] at this
  have hh' := flSim_isHarmMeas hσ hm hh
  rw [← flSim_hullComp hσ hm, ← flSim_arcH hσ hm] at hh'
  have hmain := hN _ _ _ (flSim_crosscut hσ hm hη) h0' h1' hB hh'
  have hdiam : Metric.diam (arcH (fun t => e (η t))) = Metric.diam (arcH η) / m := by
    rw [flSim_arcH hσ hm]; exact flSim_diam hσ hm _
  have hset : {x : ℝ | 0 ≤ σ * x} = {x : ℝ | x * a ≤ 0} := by
    ext x
    simp only [mem_setOf_eq]
    by_cases ha : a < 0
    · simp only [hσdef, if_pos ha, one_mul]
      constructor
      · intro hx; nlinarith
      · intro hx; by_contra hc; push Not at hc; nlinarith
    · push Not at ha
      have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      simp only [hσdef, if_neg (not_lt.2 ha)]
      constructor
      · intro hx; nlinarith
      · intro hx; by_contra hc; push Not at hc; nlinarith
  rw [hdiam] at hmain
  calc ENNReal.ofReal (c * min (Metric.diam (arcH η) / |a|) 1)
      ≤ excR (fun w => h (flSim σ m⁻¹ w)) (Ici 0) := hmain
    _ ≤ excR h {x : ℝ | 0 ≤ σ * x} := flSim_excR_le hσ hm h
    _ = excR h {x : ℝ | x * a ≤ 0} := by rw [hset]

/-- **`FLExcLowerStmt`** (Field–Lawler, EJP 20 (2015), lower bound in the proof of Prop. 3.1,
p. 7, from their Cor. 5.2). -/
theorem flExcLower_holds : FLExcLowerStmt := by
  obtain ⟨c, hc, hN⟩ := flExcNorm_holds
  refine ⟨c, hc, fun η a b h hη h0 h1 hab hh => ?_⟩
  rcases le_total |a| |b| with hle | hle
  · exact flExcLower_ordered hN η a b h hη h0 h1 hab hle hh
  · have hba : 0 < b * a := by rwa [mul_comm]
    have hhull : hullComp (fun t => η (1 - t)) = hullComp η := by
      unfold hullComp; rw [fl_rev_arcH]
    have hrev := flExcLower_ordered hN (fun t => η (1 - t)) b a h (fl_rev_crosscut hη)
      (h1.comp fl_rev_tendsto0) (h0.comp fl_rev_tendsto1) hba hle
      (by rw [hhull, fl_rev_arcH]; exact hh)
    rw [fl_rev_arcH, fl_set_eq hab] at hrev
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hrev
    have hb0 : 0 < |b| := abs_pos.2 (by rintro rfl; simp at hab)
    have hd := Metric.diam_nonneg (s := arcH η)
    gcongr

end FieldLawler
end QuantumZipper
