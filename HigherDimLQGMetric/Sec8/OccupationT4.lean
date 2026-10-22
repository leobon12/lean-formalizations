import HigherDimLQGMetric.Sec8.Occupation

/-!
# Integrated form of the trap occupation estimate (T4b)

The loss for a finite sum of nonnegative bumps is at most the sum of the
individual losses. Each individual loss is supported in its collector, so
the weighted-length occupation lemma bounds it by the corresponding `occLen`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Topology Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- A finite Weyl discount loses at most the sum of the base-metric lengths
spent in the individual collector sets. -/
theorem sec8_length_loss_le_sum_occLen (D E : ContMetric d)
    (ξ : ℝ) (hξ : 0 < ξ) (r : ℝ) (hr : 0 < r)
    (V : Set (Rd d)) (f : ℕ → C(Rd d, ℝ)) (J : ℕ)
    (hf0 : ∀ j < J, ∀ x, 0 ≤ f j x)
    (hfV : ∀ j < J, ∀ x, 0 < f j x → x ∈ V)
    (Z : Finset (Rd d × ℕ)) (hJ : ∀ q ∈ Z, q.2 < J)
    (hE : IsWeylOf ξ (-F_Z f r Z) D E)
    (P : ℝ → Rd d) (hP : IsGeod E P) :
    D.len P 0 1 ≤ E.len P 0 1 +
      ∑ q ∈ Z, occLen D P (sec8Collector V r q.1) := by
  let loss : D.Space → ℝ :=
    fun x => 1 - D.weylWeight ξ (-F_Z f r Z) x
  let lossSite : (Rd d × ℕ) → D.Space → ℝ :=
    fun q x => 1 - D.weylWeight ξ (-bumpAt (f q.2) r q.1) x
  have hF0 : ∀ x, 0 ≤ F_Z f r Z x := by
    intro x
    rw [F_Z, ContinuousMap.sum_apply]
    exact Finset.sum_nonneg fun q hq => hf0 q.2 (hJ q hq) _
  have hDfin : D.len P 0 1 ≠ ⊤ := by
    have hEfin : E.len P 0 1 ≠ ⊤ := by
      rw [hP.2]
      exact ENNReal.ofReal_ne_top
    exact (curveLength_weyl_ne_top_iff hE zero_le_one hP.1).mp hEfin
  have hPc : ContinuousOn (D.pt ∘ P) (Icc 0 1) :=
    D.continuous_pt.comp_continuousOn hP.1
  have hpoint (x : D.Space) : loss x ≤ ∑ q ∈ Z, lossSite q x := by
    have ha : ∀ q ∈ Z, 0 ≤ ξ * bumpAt (f q.2) r q.1 (D.unpt x) := by
      intro q hq
      exact mul_nonneg hξ.le (hf0 q.2 (hJ q hq) _)
    have h := sec8_one_sub_exp_neg_sum_le_sum Z
      (fun q => ξ * bumpAt (f q.2) r q.1 (D.unpt x)) ha
    have hsum : (∑ q ∈ Z, ξ * bumpAt (f q.2) r q.1 (D.unpt x)) =
        ξ * F_Z f r Z (D.unpt x) := by
      simp [F_Z, Finset.mul_sum]
    rw [hsum] at h
    convert h using 1 <;> simp [loss, lossSite, ContMetric.weylWeight]
  have hmono : weightedLength loss (D.pt ∘ P) 0 1 ≤
      weightedLength (fun x => ∑ q ∈ Z, lossSite q x) (D.pt ∘ P) 0 1 :=
    weightedLength_mono_weight fun t _ => hpoint _
  have hsiteCont : ∀ q ∈ Z, Continuous (lossSite q) := by
    intro q _
    exact continuous_const.sub (D.continuous_weylWeight ξ (-bumpAt (f q.2) r q.1))
  have hsite0 : ∀ q ∈ Z, ∀ x, 0 ≤ lossSite q x := by
    intro q hq x
    change 0 ≤ 1 - Real.exp (ξ * (-bumpAt (f q.2) r q.1 (D.unpt x)))
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    have hb : 0 ≤ bumpAt (f q.2) r q.1 (D.unpt x) := hf0 q.2 (hJ q hq) _
    nlinarith [mul_nonneg hξ.le hb]
  have hadd := sec8_weightedLength_finset_sum (D.pt ∘ P) zero_le_one hPc hDfin
    Z lossSite hsiteCont hsite0
  have hsiteOcc : ∀ q ∈ Z,
      weightedLength (lossSite q) (D.pt ∘ P) 0 1 ≤
        occLen D P (sec8Collector V r q.1) := by
    intro q hq
    apply sec8_weightedLength_le_occLen D P (sec8Collector V r q.1) (lossSite q)
    · intro τ _
      change 1 - Real.exp (ξ * (-bumpAt (f q.2) r q.1 (P τ))) ≤ 1
      linarith [Real.exp_pos (ξ * (-bumpAt (f q.2) r q.1 (P τ)))]
    · intro τ _ hpos
      have hexp : Real.exp (ξ * (-bumpAt (f q.2) r q.1 (P τ))) < 1 := by
        simpa only [lossSite, ContMetric.weylWeight_pt,
          ContinuousMap.neg_apply, sub_pos] using hpos
      have hmul : ξ * (-bumpAt (f q.2) r q.1 (P τ)) < 0 :=
        Real.exp_lt_one_iff.mp hexp
      have hbump : 0 < bumpAt (f q.2) r q.1 (P τ) := by
        nlinarith [hξ]
      have hpull : r⁻¹ • (P τ - q.1) ∈ V :=
        hfV q.2 (hJ q hq) _ hbump
      exact ⟨_, hpull, S6a.affine_pull hr.ne' q.1 (P τ)⟩
  calc
    D.len P 0 1 = E.len P 0 1 + weightedLength loss (D.pt ∘ P) 0 1 :=
      sec8_length_eq_weyl_plus_loss D E ξ (F_Z f r Z) hF0 hE P hP hξ
    _ ≤ E.len P 0 1 + weightedLength
        (fun x => ∑ q ∈ Z, lossSite q x) (D.pt ∘ P) 0 1 :=
      add_le_add_right hmono _
    _ = E.len P 0 1 + ∑ q ∈ Z, weightedLength (lossSite q) (D.pt ∘ P) 0 1 := by
      rw [hadd]
    _ ≤ E.len P 0 1 + ∑ q ∈ Z, occLen D P (sec8Collector V r q.1) := by
      exact add_le_add_right (Finset.sum_le_sum fun q hq => hsiteOcc q hq) _

/-- **(T4b).** The integrated loss of length along a geodesic of the
discounted metric is bounded by the sum of the per-site (T4) occupation
bounds. This is the exact form used by Lemmas 8.3 and 8.5. -/
theorem lemma82_T4b (D Dt E : ContMetric d)
    (ξ : ℝ) (hξ : 0 < ξ) (r : ℝ) (hr : 0 < r)
    (V : Set (Rd d)) (f : ℕ → C(Rd d, ℝ)) (J : ℕ)
    (hf0 : ∀ j < J, ∀ x, 0 ≤ f j x)
    (hfV : ∀ j < J, ∀ x, 0 < f j x → x ∈ V)
    (a b c g H c' : ℝ) (s : Rd d × ℕ → ℝ)
    (Z : Finset (Rd d × ℕ)) (hJ : ∀ q ∈ Z, q.2 < J)
    (hdisj : (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (ball q.1 (4 * r)) (ball q'.1 (4 * r))))
    (htrap : ∀ q ∈ Z,
      TrapProps ξ V f J a b c g H c' D Dt (s q) r q.1 q.2)
    (hE : IsWeylOf ξ (-F_Z f r Z) D E)
    (P : ℝ → Rd d) (hP : IsGeod E P) :
    D.len P 0 1 ≤ E.len P 0 1 +
      ∑ q ∈ Z, ENNReal.ofReal (H * s q) := by
  have hbase := sec8_length_loss_le_sum_occLen D E ξ hξ r hr V f J hf0 hfV
    Z hJ hE P hP
  have hocc (q : Rd d × ℕ) (hq : q ∈ Z) :
      occLen D P (sec8Collector V r q.1) ≤ ENNReal.ofReal (H * s q) := by
    have hT4 := (htrap q hq).2.2.2 Z hq hJ hdisj E
    have hW : IsWeylOf ξ (-(∑ q ∈ Z, bumpAt (f q.2) r q.1)) D E := hE
    exact (hT4 hW P hP).2
  exact hbase.trans (add_le_add_right
    (Finset.sum_le_sum fun q hq => hocc q hq) _)

end HigherDimLQGMetric
