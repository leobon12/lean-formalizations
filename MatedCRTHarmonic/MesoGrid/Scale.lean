import Mathlib

/-!
# Scale estimates for the mesoscopic-control construction

Elementary estimates for the dyadic index `⌈λ log₂ D⌉`, exponential decay on that index, and
the radius sequence from the cone-radius asymptotic.
-/

set_option autoImplicit false

open Filter Topology

namespace MatedCRTHarmonic.MesoGrid

noncomputable def scaleIndex (lam D : ℝ) : ℕ := ⌈lam * Real.logb 2 D⌉₊

lemma scaleIndex_tendsto_atTop (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun D : ℝ => scaleIndex lam D) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)
    (f := fun D : ℝ => scaleIndex lam D) (l := atTop)).mp
  apply Filter.tendsto_atTop_mono
    (f := fun D : ℝ => lam * Real.logb 2 D)
    (g := fun D : ℝ => (scaleIndex lam D : ℝ))
  · intro D
    exact Nat.le_ceil _
  · have hid : Tendsto (fun D : ℝ => D) atTop atTop :=
      Filter.tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨b, fun D hD => hD⟩
    exact Filter.Tendsto.const_mul_atTop hlam
      (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)) |>.comp hid

lemma scaleIndex_lt_add_one {lam D : ℝ} (hlam : 0 < lam) (hD : 1 ≤ D) :
    (scaleIndex lam D : ℝ) < lam * Real.logb 2 D + 1 := by
  unfold scaleIndex
  exact Nat.ceil_lt_add_one (mul_nonneg hlam.le
    (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hD))

lemma eventual_radius_rpow_bounds {a δ : ℝ} {R : ℕ → ℝ}
    (hR : ∀ k, 0 < R k)
    (hlim : Tendsto (fun k : ℕ => Real.logb 2 (R k) / (k : ℝ)) atTop (𝓝 a))
    (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ k, K ≤ k →
      (2 : ℝ) ^ ((a - δ) * (k : ℝ)) < R k ∧
      R k < (2 : ℝ) ^ ((a + δ) * (k : ℝ)) := by
  have hleft : a - δ < a := by linarith
  have hright : a < a + δ := by linarith
  have hevent : ∀ᶠ k : ℕ in atTop,
      Real.logb 2 (R k) / (k : ℝ) ∈ Set.Ioo (a - δ) (a + δ) :=
    hlim.eventually (Ioo_mem_nhds hleft hright)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max K 1, ?_⟩
  intro k hk
  have hkK : K ≤ k := le_trans (le_max_left K 1) hk
  have hk1 : 1 ≤ k := le_trans (le_max_right K 1) hk
  have hcl := hK k hkK
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hlo : (a - δ) * (k : ℝ) < Real.logb 2 (R k) :=
    (lt_div_iff₀ hkpos).mp hcl.1
  have hhi : Real.logb 2 (R k) < (a + δ) * (k : ℝ) :=
    (div_lt_iff₀ hkpos).mp hcl.2
  have hb : (1 : ℝ) < 2 := by norm_num
  have hpLo : 0 < (2 : ℝ) ^ ((a - δ) * (k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hpHi : 0 < (2 : ℝ) ^ ((a + δ) * (k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · apply (Real.logb_lt_logb_iff hb hpLo (hR k)).mp
    rw [Real.logb_rpow (by norm_num) (by norm_num)]
    exact hlo
  · apply (Real.logb_lt_logb_iff hb (hR k) hpHi).mp
    rw [Real.logb_rpow (by norm_num) (by norm_num)]
    exact hhi

lemma tendsto_two_neg_mul_scaleIndex {lam gap : ℝ} (hlam : 0 < lam) (hgap : 0 < gap) :
    Tendsto (fun D : ℝ => (2 : ℝ) ^ (-gap * (scaleIndex lam D : ℝ))) atTop (𝓝 0) := by
  have hNat : Tendsto (fun D : ℝ => scaleIndex lam D) atTop atTop :=
    scaleIndex_tendsto_atTop lam hlam
  have hCast : Tendsto (fun D : ℝ => (scaleIndex lam D : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_iff (R := ℝ) (f := fun D : ℝ => scaleIndex lam D)
      (l := atTop)).2 hNat
  have hExp : Tendsto (fun D : ℝ => (2 : ℝ) ^ (scaleIndex lam D : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num : (1 : ℝ) < 2)).comp hCast
  have hdec := (tendsto_rpow_neg_atTop hgap).comp hExp
  refine hdec.congr fun D => ?_
  calc
    ((2 : ℝ) ^ (scaleIndex lam D : ℝ)) ^ (-gap) =
        (2 : ℝ) ^ ((scaleIndex lam D : ℝ) * (-gap)) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
    _ = (2 : ℝ) ^ (-gap * (scaleIndex lam D : ℝ)) := by congr 1; ring

end MatedCRTHarmonic.MesoGrid
