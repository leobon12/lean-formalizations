import QuantumZipper.Proofs.Zipper.AreaWinSWCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINSPLIT (2): the pathwise comparison and geometric sums

Bookkeeping for the application of the window core bound (`AreaWinSWCore.lean`) in SW's proof of
Theorem 1.1 (arXiv:1605.06171, p. 9):

* `win_path_le`: a deterministic comparison, for one sample, of the normalized window integral
  `c ∫_ℍ W φ` with the reference `∫_ℍ d φ` when `c W = d (1 + g)` on `S ⊇ supp φ`: outside an
  exceptional set `T` the difference is `|∫_{S∖T} φ d g|`, on `S ∩ T` both are bounded by
  `M ∫_{S∩T} d (2 + g)`.
* `tsum_ofReal_geom_ne_top`: `Σ_j C q^j < ∞` in `ℝ≥0∞` for `0 ≤ q < 1`.

Own elementary bookkeeping (cost rule).
-/

open MeasureTheory Real Set
open scoped NNReal ENNReal

namespace QuantumZipper.E6

/-- **Pathwise window comparison.** -/
theorem win_path_le {S T Hs : Set ℂ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hSH : S ⊆ Hs) {φ d g : ℂ → ℝ} {W : ℂ → ℝ≥0∞} {c M : ℝ}
    (hφ0 : ∀ w, 0 ≤ φ w) (hφM : ∀ w, φ w ≤ M) (hφS : ∀ w, w ∉ S → φ w = 0)
    (hid : ∀ w ∈ S, 0 ≤ d w ∧ 0 ≤ 1 + g w ∧ ENNReal.ofReal c * W w = ENNReal.ofReal (d w * (1 + g w)))
    (hi1 : IntegrableOn (fun w => φ w * d w) (S \ T))
    (hi2 : IntegrableOn (fun w => φ w * (d w * g w)) (S \ T)) :
    ENNReal.ofReal c * (∫⁻ w in Hs, W w * ENNReal.ofReal (φ w))
        ≤ (∫⁻ w in Hs, ENNReal.ofReal (d w * φ w)) +
          (ENNReal.ofReal |∫ w in S \ T, φ w * (d w * g w)| +
            ENNReal.ofReal M * ∫⁻ w in S ∩ T, ENNReal.ofReal (d w * (2 + g w))) ∧
      (∫⁻ w in Hs, ENNReal.ofReal (d w * φ w))
        ≤ ENNReal.ofReal c * (∫⁻ w in Hs, W w * ENNReal.ofReal (φ w)) +
          (ENNReal.ofReal |∫ w in S \ T, φ w * (d w * g w)| +
            ENNReal.ofReal M * ∫⁻ w in S ∩ T, ENNReal.ofReal (d w * (2 + g w))) := by
  set F : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal c * (W w * ENNReal.ofReal (φ w)) with hF
  set Fb : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (d w * φ w) with hFb
  set e := ENNReal.ofReal |∫ w in S \ T, φ w * (d w * g w)| with he
  set n := ENNReal.ofReal M * ∫⁻ w in S ∩ T, ENNReal.ofReal (d w * (2 + g w)) with hn
  have hsuppF : Function.support F ⊆ S := by
    intro w hw
    by_contra hwS
    exact hw (by simp [hF, hφS w hwS])
  have hsuppFb : Function.support Fb ⊆ S := by
    intro w hw
    by_contra hwS
    exact hw (by simp [hFb, hφS w hwS])
  have hA : ENNReal.ofReal c * ∫⁻ w in Hs, W w * ENNReal.ofReal (φ w) = ∫⁻ w in S, F w := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      setLIntegral_eq_of_support_subset (hsuppF.trans hSH),
      setLIntegral_eq_of_support_subset hsuppF]
  have hB : ∫⁻ w in Hs, ENNReal.ofReal (d w * φ w) = ∫⁻ w in S, Fb w := by
    rw [setLIntegral_eq_of_support_subset (hsuppFb.trans hSH),
      setLIntegral_eq_of_support_subset hsuppFb]
  have hFS : ∀ w ∈ S, F w = ENNReal.ofReal (φ w * d w + φ w * (d w * g w)) := by
    intro w hw
    obtain ⟨hd, hg, hW⟩ := hid w hw
    simp only [hF]
    rw [← mul_assoc, hW, ← ENNReal.ofReal_mul (mul_nonneg hd hg)]
    congr 1; ring
  -- far parts
  have hSTm : MeasurableSet (S \ T) := hS.diff hT
  have hx : ∫⁻ w in S \ T, F w
      = ENNReal.ofReal (∫ w in S \ T, (φ w * d w + φ w * (d w * g w))) := by
    rw [setLIntegral_congr_fun hSTm (fun w hw => hFS w hw.1)]
    refine (ofReal_integral_eq_lintegral_ofReal (hi1.add hi2) ?_).symm
    refine (ae_restrict_iff' hSTm).2 (ae_of_all _ fun w hw => ?_)
    obtain ⟨hd, hg, -⟩ := hid w hw.1
    have : φ w * d w + φ w * (d w * g w) = φ w * (d w * (1 + g w)) := by ring
    show 0 ≤ φ w * d w + φ w * (d w * g w)
    rw [this]; exact mul_nonneg (hφ0 w) (mul_nonneg hd hg)
  have hy : ∫⁻ w in S \ T, Fb w = ENNReal.ofReal (∫ w in S \ T, φ w * d w) := by
    rw [setLIntegral_congr_fun hSTm (fun w _ => show Fb w = ENNReal.ofReal (φ w * d w) by
      simp only [hFb]; rw [mul_comm])]
    refine (ofReal_integral_eq_lintegral_ofReal hi1 ?_).symm
    refine (ae_restrict_iff' hSTm).2 (ae_of_all _ fun w hw => ?_)
    exact mul_nonneg (hφ0 w) (hid w hw.1).1
  have hsum : ∫ w in S \ T, (φ w * d w + φ w * (d w * g w))
      = (∫ w in S \ T, φ w * d w) + ∫ w in S \ T, φ w * (d w * g w) := integral_add hi1 hi2
  -- near parts
  have hM0 : ∀ w ∈ S, 0 ≤ d w * (2 + g w) := fun w hw =>
    mul_nonneg (hid w hw).1 (by linarith [(hid w hw).2.1])
  have hnA : ∫⁻ w in S ∩ T, F w ≤ n := by
    rw [hn, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono_ae' (hS.inter hT) (ae_of_all _ fun w hw => ?_)
    rw [hFS w hw.1, ← ENNReal.ofReal_mul ((hφ0 w).trans (hφM w))]
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨hd, hg, -⟩ := hid w hw.1
    have h1 : φ w * d w + φ w * (d w * g w) = φ w * (d w * (1 + g w)) := by ring
    rw [h1]
    have h2 : d w * (1 + g w) ≤ d w * (2 + g w) := mul_le_mul_of_nonneg_left (by linarith) hd
    exact mul_le_mul (hφM w) h2 (mul_nonneg hd hg) ((hφ0 w).trans (hφM w))
  have hnB : ∫⁻ w in S ∩ T, Fb w ≤ n := by
    rw [hn, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono_ae' (hS.inter hT) (ae_of_all _ fun w hw => ?_)
    simp only [hFb]
    rw [← ENNReal.ofReal_mul ((hφ0 w).trans (hφM w))]
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨hd, hg, -⟩ := hid w hw.1
    have h2 : d w ≤ d w * (2 + g w) := le_mul_of_one_le_right hd (by linarith)
    calc d w * φ w = φ w * d w := mul_comm _ _
      _ ≤ M * (d w * (2 + g w)) := mul_le_mul (hφM w) h2 hd ((hφ0 w).trans (hφM w))
  have hsplitA := lintegral_inter_add_sdiff (μ := volume) F S hT
  have hsplitB := lintegral_inter_add_sdiff (μ := volume) Fb S hT
  set a := ∫ w in S \ T, φ w * d w
  set b := ∫ w in S \ T, φ w * (d w * g w)
  have hab1 : ENNReal.ofReal (a + b) ≤ ENNReal.ofReal a + e :=
    (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self b])).trans
      (ENNReal.ofReal_add_le)
  have hab2 : ENNReal.ofReal a ≤ ENNReal.ofReal (a + b) + e :=
    (ENNReal.ofReal_le_ofReal (by linarith [neg_abs_le b])).trans
      (ENNReal.ofReal_add_le)
  have key1 : (∫⁻ w in S ∩ T, F w) + ENNReal.ofReal (a + b)
      ≤ ((∫⁻ w in S ∩ T, Fb w) + ENNReal.ofReal a) + (e + n) :=
    calc (∫⁻ w in S ∩ T, F w) + ENNReal.ofReal (a + b)
        ≤ n + (ENNReal.ofReal a + e) := add_le_add hnA hab1
      _ = ENNReal.ofReal a + (e + n) := by ring
      _ ≤ _ := add_le_add le_add_self le_rfl
  have key2 : (∫⁻ w in S ∩ T, Fb w) + ENNReal.ofReal a
      ≤ ((∫⁻ w in S ∩ T, F w) + ENNReal.ofReal (a + b)) + (e + n) :=
    calc (∫⁻ w in S ∩ T, Fb w) + ENNReal.ofReal a
        ≤ n + (ENNReal.ofReal (a + b) + e) := add_le_add hnB hab2
      _ = ENNReal.ofReal (a + b) + (e + n) := by ring
      _ ≤ _ := add_le_add le_add_self le_rfl
  have eA : ENNReal.ofReal c * ∫⁻ w in Hs, W w * ENNReal.ofReal (φ w)
      = (∫⁻ w in S ∩ T, F w) + ENNReal.ofReal (a + b) := by
    rw [hA, ← hsplitA, hx, hsum]
  have eB : ∫⁻ w in Hs, ENNReal.ofReal (d w * φ w)
      = (∫⁻ w in S ∩ T, Fb w) + ENNReal.ofReal a := by
    rw [hB, ← hsplitB, hy]
  exact ⟨(le_of_eq eA).trans (key1.trans (le_of_eq (congrArg (· + (e + n)) eB.symm))),
    (le_of_eq eB).trans (key2.trans (le_of_eq (congrArg (· + (e + n)) eA.symm)))⟩

/-- Geometric series in `ℝ≥0∞`. -/
theorem tsum_ofReal_geom_ne_top {C q : ℝ} (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' j : ℕ, ENNReal.ofReal (C * q ^ j)) ≠ ∞ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg hC (pow_nonneg hq0 j))
    ((summable_geometric_of_lt_one hq0 hq1).mul_left C)]
  exact ENNReal.ofReal_ne_top

/-- `exp (-a · (j κ)) = (exp (-a κ))^j`. -/
theorem exp_neg_mul_nat (a κ : ℝ) (j : ℕ) :
    exp (-a * ((j : ℝ) * κ)) = exp (-a * κ) ^ j := by
  rw [← Real.exp_nat_mul]; congr 1; ring

/-- Geometric decay in the window index: `Σ_j C e^{-a j κ} < ∞` for `a, κ > 0`. -/
theorem tsum_ofReal_exp_ne_top {C a κ : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hκ : 0 < κ) :
    (∑' j : ℕ, ENNReal.ofReal (C * exp (-a * ((j : ℝ) * κ)))) ≠ ∞ := by
  simp_rw [exp_neg_mul_nat]
  exact tsum_ofReal_geom_ne_top hC (exp_pos _).le
    (Real.exp_lt_one_iff.2 (by nlinarith))

end QuantumZipper.E6
