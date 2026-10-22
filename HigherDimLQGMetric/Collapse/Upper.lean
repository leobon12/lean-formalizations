import HigherDimLQGMetric.Collapse.LowerCompact

/-! # Scalar upper bound for normalized recovery costs -/

set_option autoImplicit false

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

/-- Converting the three-piece recovery estimate into a real normalized bound. -/
theorem normalized_recovery_real_le {lam eta : ℝ} {d W : ℝ≥0∞}
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hd : d ≠ ⊤)
    (hW : W ≤ ENNReal.ofReal eta + ENNReal.ofReal lam * d + ENNReal.ofReal eta) :
    ((ENNReal.ofReal lam)⁻¹ * W).toReal ≤ eta / lam + d.toReal + eta / lam := by
  have hsumfin : ENNReal.ofReal eta + ENNReal.ofReal lam * d +
      ENNReal.ofReal eta ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd⟩,
      ENNReal.ofReal_ne_top⟩
  have hnormfin : (ENNReal.ofReal lam)⁻¹ *
      (ENNReal.ofReal eta + ENNReal.ofReal lam * d + ENNReal.ofReal eta) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr
      (ne_of_gt (ENNReal.ofReal_pos.mpr hlam))) hsumfin
  have hle : ((ENNReal.ofReal lam)⁻¹ * W).toReal ≤
      ((ENNReal.ofReal lam)⁻¹ *
        (ENNReal.ofReal eta + ENNReal.ofReal lam * d + ENNReal.ofReal eta)).toReal :=
    ENNReal.toReal_mono hnormfin (mul_le_mul_right hW _)
  have hterm : ENNReal.ofReal lam * d ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd
  have hsum1 : ENNReal.ofReal eta + ENNReal.ofReal lam * d ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hterm⟩
  have hle' : ((ENNReal.ofReal lam)⁻¹ * W).toReal ≤
      lam⁻¹ * (eta + lam * d.toReal + eta) := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_add hsum1 ENNReal.ofReal_ne_top,
      ENNReal.toReal_add ENNReal.ofReal_ne_top hterm,
      ENNReal.toReal_ofReal hlam.le, ENNReal.toReal_ofReal heta] using hle
  calc
    ((ENNReal.ofReal lam)⁻¹ * W).toReal
        ≤ lam⁻¹ * (eta + lam * d.toReal + eta) := hle'
    _ = eta / lam + d.toReal + eta / lam := by
      field_simp

/-- An extended-real sequence bounded above by a convergent real sequence and eventually
above every strict real lower bound converges to its finite target. -/
theorem tendsto_ennreal_of_real_bounds {R : ℕ → ℝ≥0∞} {d : ℝ≥0∞}
    (hd : d ≠ ⊤) (hfin : ∀ᶠ n in atTop, R n ≠ ⊤)
    {U : ℕ → ℝ} (hU : Tendsto U atTop (𝓝 d.toReal))
    (hupper : ∀ᶠ n in atTop, (R n).toReal ≤ U n)
    (hlower : ∀ C : ℝ, 0 ≤ C → C < d.toReal →
      ∀ᶠ n in atTop, ENNReal.ofReal C ≤ R n) :
    Tendsto R atTop (𝓝 d) := by
  have hreal : Tendsto (fun n => (R n).toReal) atTop (𝓝 d.toReal) := by
    rw [tendsto_order]
    constructor
    · intro C hCd
      by_cases hC : 0 ≤ C
      · let B := (C + d.toReal) / 2
        have hB0 : 0 ≤ B := by
          dsimp [B]
          have : 0 ≤ d.toReal := ENNReal.toReal_nonneg
          linarith
        have hCB : C < B := by dsimp [B]; linarith
        have hBd : B < d.toReal := by dsimp [B]; linarith
        filter_upwards [hlower B hB0 hBd, hfin] with n hn hnf
        have hb : B ≤ (R n).toReal := by
          have := ENNReal.toReal_mono hnf hn
          simpa only [ENNReal.toReal_ofReal hB0] using this
        exact hCB.trans_le hb
      · have hCneg : C < 0 := lt_of_not_ge hC
        exact Eventually.of_forall fun n => hCneg.trans_le ENNReal.toReal_nonneg
    · intro C hdC
      filter_upwards [hupper, hU.eventually (eventually_lt_nhds hdC)] with n hn hUn
      exact hn.trans_lt hUn
  have hreal' := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_toReal hd] at hreal'
  apply hreal'.congr'
  filter_upwards [hfin] with n hn
  exact ENNReal.ofReal_toReal hn

end HigherDimLQGMetric
