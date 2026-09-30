import QuantumZipper.Proofs.Zipper.BaseFin2Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1 (D75): the unit moment `BaseUnitMomStmt` from the base return and the unit lengths

`baseUnitMom_of_tail_len : SLEBaseTailStmt → BaseUnitLenMomStmt → BaseUnitMomStmt`.

* `lintegral_rpow_neg_le_of_tail`: the quantitative form of
  `WedgeUnzip.lintegral_rpow_neg_ne_top_of_tail` (a polynomial tail `P(m < ε) ≤ C ε^b` gives
  `E[m^{−a}] ≤ 1 + Σ_k C 2^{a} 2^{−k(b−a)}` for `a < b`, a bound not depending on the probability
  space); same dyadic proof.
* `SLEBaseTailStmt` (the SLE input, a single standard estimate): the chordal `SLE_κ` trace
  (`κ < 4`) comes within `ε` of its root during the capacity window `[1/16, 4]` with probability
  `≤ C ε^b` (qualitatively Lawler, *Conformally invariant processes in the plane* (2005),
  Prop. 6.12, p. 128; quantitative route: handoff/TIP-CORE.md §3, domain Markov at a fixed time,
  root deep-pocket cover and the proved boundary-hitting estimate `LWFar.bdryHitStmt_holds`).
  It replaces `WedgeUnzip.SLEBaseSideStmt`, which is false (handoff/TIP-CORE.md §3).
* `sleBaseReturnUnif_of_tail`: the uniform negative moment of `baseDist` (the window minimum of
  `|η|` over `[1/16, 4]`) from the tail.
* the unit term `λ_0^{−κ/2} L^±(1) ≤ baseDist^{−κ/2} L` (the window `[1/4, 1]` of `λ_0` lies in
  `[1/16, 4]`), and `(uv)^q ≤ u^{2q} + v^{2q}`.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace BaseFin2

open WedgeUnzip

section Tail

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Quantitative tail-to-moment bound** (copy of `lintegral_rpow_neg_ne_top_of_tail`). -/
theorem lintegral_rpow_neg_le_of_tail [IsProbabilityMeasure P] {m : Ω → ℝ≥0∞}
    (hm : AEMeasurable m P) {C a b : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hab : a < b)
    (htail : ∀ ε : ℝ, 0 < ε → P {ω | m ω < ENNReal.ofReal ε} ≤ ENNReal.ofReal (C * ε ^ b)) :
    ∫⁻ ω, m ω ^ (-a) ∂P ≤
      1 + ENNReal.ofReal (∑' k : ℕ, C * (1 / 2 : ℝ) ^ (-a) * ((1 / 2 : ℝ) ^ (b - a)) ^ k) := by
  set m' := hm.mk m
  have hm' : Measurable m' := hm.measurable_mk
  have he : ∫⁻ ω, m ω ^ (-a) ∂P = ∫⁻ ω, m' ω ^ (-a) ∂P :=
    lintegral_congr_ae (hm.ae_eq_mk.mono fun ω h => by
      show m ω ^ (-a) = m' ω ^ (-a); rw [h])
  have htail' : ∀ ε : ℝ, 0 < ε →
      P {ω | m' ω < ENNReal.ofReal ε} ≤ ENNReal.ofReal (C * ε ^ b) := fun ε hε =>
    (measure_mono_ae (hm.ae_eq_mk.mono fun ω h (hω : m' ω < _) =>
      show m ω < _ by rw [h]; exact hω)).trans (htail ε hε)
  rw [he]
  set ρ : ℝ := 1 / 2 with hρ
  set S : ℕ → Set Ω := fun k => {ω | m' ω < ENNReal.ofReal (ρ ^ k)} with hS
  have hSm : ∀ k, MeasurableSet (S k) := fun k => measurableSet_lt hm' measurable_const
  set w : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal ((ρ ^ (k + 1)) ^ (-a)) with hw
  have hpt : ∀ ω, m' ω ^ (-a) ≤ 1 + ∑' k, w k * (S k).indicator 1 ω := fun ω =>
    (txsle_rpow_neg_le (m' ω) ha).trans_eq (by congr 1)
  have hρ0 : 0 < ρ := by norm_num [hρ]
  have hρ1 : ρ < 1 := by norm_num [hρ]
  set q : ℝ := ρ ^ (b - a) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hρ0.le _
  have hq1 : q < 1 := Real.rpow_lt_one hρ0.le hρ1 (by linarith)
  have hterm : ∀ k : ℕ, w k * P (S k) ≤ ENNReal.ofReal (C * ρ ^ (-a) * q ^ k) := by
    intro k
    have hk := htail' (ρ ^ k) (pow_pos hρ0 k)
    calc w k * P (S k) ≤ ENNReal.ofReal ((ρ ^ (k + 1)) ^ (-a)) *
          ENNReal.ofReal (C * (ρ ^ k) ^ b) := by gcongr
      _ = ENNReal.ofReal ((ρ ^ (k + 1)) ^ (-a) * (C * (ρ ^ k) ^ b)) :=
          (ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)).symm
      _ = ENNReal.ofReal (C * ρ ^ (-a) * q ^ k) := by
          congr 1
          have e1 : (ρ ^ (k + 1)) ^ (-a) = ρ ^ (-a) * (ρ ^ (-a)) ^ k := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le, ← Real.rpow_natCast,
              ← Real.rpow_mul hρ0.le, ← Real.rpow_add hρ0]
            congr 1; push_cast; ring
          have e2 : (ρ ^ k) ^ b = (ρ ^ b) ^ k := by
            rw [← Real.rpow_natCast ρ k, ← Real.rpow_natCast (ρ ^ b) k,
              ← Real.rpow_mul hρ0.le, ← Real.rpow_mul hρ0.le, mul_comm]
          have e3 : q = ρ ^ (-a) * ρ ^ b := by
            rw [hq, ← Real.rpow_add hρ0]; congr 1; ring
          rw [e1, e2, e3, mul_pow]
          ring
  have hsum : Summable fun k : ℕ => C * ρ ^ (-a) * q ^ k :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hnn : ∀ k : ℕ, 0 ≤ C * ρ ^ (-a) * q ^ k := fun k =>
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hρ0.le _)) (pow_nonneg hq0 k)
  have hI : ∫⁻ ω, (1 + ∑' k, w k * (S k).indicator 1 ω) ∂P =
      P univ + ∑' k, w k * P (S k) := by
    rw [lintegral_add_left measurable_const _]
    rw [lintegral_tsum (f := fun k ω => w k * (S k).indicator 1 ω) fun k => (measurable_const.mul
        (measurable_one.indicator (hSm k))).aemeasurable]
    congr 1
    · simp
    · refine tsum_congr fun k => ?_
      rw [lintegral_const_mul _ (measurable_one.indicator (hSm k)),
        lintegral_indicator_one (hSm k)]
  refine (lintegral_mono hpt).trans (hI.trans_le ?_)
  rw [measure_univ, ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  exact add_le_add le_rfl (ENNReal.tsum_le_tsum hterm)

end Tail

/-- **Uniform negative moment of the base distance.** -/
def SLEBaseReturnUnifStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ a : ℝ, 0 < a ∧ ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    AEMeasurable (baseDist κ B) P ∧ ∫⁻ ω, baseDist κ B ω ^ (-a) ∂P ≤ K

/-- **(SLE input) Polynomial tail of the base distance**, with constants not depending on the
probability space. -/
def SLEBaseTailStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ C b : ℝ, 0 ≤ C ∧ 0 < b ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ ε : ℝ, 0 < ε →
      P {ω | baseDist κ B ω < ENNReal.ofReal ε} ≤ ENNReal.ofReal (C * ε ^ b)

/-- The tail gives `SLEBaseReturnStmt`'s uniform form. -/
theorem sleBaseReturnUnif_of_tail (h : SLEBaseTailStmt) : SLEBaseReturnUnifStmt := by
  intro κ hκ hκ4
  obtain ⟨C, b, hC, hb, hT⟩ := h κ hκ hκ4
  refine ⟨b / 2, by positivity, 1 + ENNReal.ofReal (∑' k : ℕ, C *
      (1 / 2 : ℝ) ^ (-(b / 2)) * ((1 / 2 : ℝ) ^ (b - b / 2)) ^ k),
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩, ?_⟩
  intro Ω _ P _ B hB
  have hmeas := aemeasurable_baseDist (P := P) hB hκ (by linarith)
  exact ⟨hmeas, lintegral_rpow_neg_le_of_tail hmeas hC (by positivity) (by linarith)
    (hT P B hB)⟩

/-- `uv ≤ u² + v²` in `ℝ≥0∞`. -/
theorem bf2_mul_le_sq_add_sq (u v : ℝ≥0∞) : u * v ≤ u ^ 2 + v ^ 2 := by
  rcases le_total u v with h | h
  · calc u * v ≤ v * v := mul_le_mul' h le_rfl
      _ = v ^ 2 := (sq v).symm
      _ ≤ u ^ 2 + v ^ 2 := le_add_self
  · calc u * v ≤ u * u := mul_le_mul' le_rfl h
      _ = u ^ 2 := (sq u).symm
      _ ≤ u ^ 2 + v ^ 2 := le_self_add

/-- `(y⁻¹)`-free form of `txsc_rpow_le_one_add` for negative exponents:
`m^{−r} ≤ 1 + m^{−a}` for `0 ≤ r ≤ a`. -/
theorem bf2_rpow_neg_le_one_add {r a : ℝ} (hr : 0 ≤ r) (hra : r ≤ a) (m : ℝ≥0∞) :
    m ^ (-r) ≤ 1 + m ^ (-a) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg, ← ENNReal.inv_rpow, ← ENNReal.inv_rpow]
  exact txsc_rpow_le_one_add hr hra _

/-- The window of `λ_0` lies in the window of `baseDist`: `baseDist ≤ λ_0`. -/
theorem baseDist_le_winLam_zero (κ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    baseDist κ B ω ≤ winLam κ B ω 0 := by
  unfold baseDist winLam
  refine biInf_mono fun r hr => ⟨le_trans (by norm_num [radius]) hr.1,
    le_trans hr.2 (by norm_num [radius])⟩

/-- **`BaseUnitMomStmt` from the base return and the unit lengths.** -/
theorem baseUnitMom_of_tail_len (h1 : SLEBaseTailStmt) (hL : BaseUnitLenMomStmt) :
    BaseUnitMomStmt := by
  intro κ hκ hκ4
  obtain ⟨a, ha, K, hK, hD⟩ := sleBaseReturnUnif_of_tail h1 κ hκ hκ4
  obtain ⟨b, hb, CL, hCL, hLL⟩ := hL κ hκ hκ4
  set q : ℝ := min (a / κ) (b / 2) with hqdef
  have hq : 0 < q := lt_min (div_pos ha hκ) (by linarith)
  have hqa : κ * q ≤ a := by
    have : q ≤ a / κ := min_le_left _ _
    rwa [le_div_iff₀ hκ, mul_comm] at this
  have hqb : 2 * q ≤ b := by have : q ≤ b / 2 := min_le_right _ _; linarith
  refine ⟨q, hq, (1 + K) + (1 + CL),
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hK⟩,
      ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hCL⟩⟩, ?_⟩
  intro Ω _ P _ B X hB hX hind hN
  obtain ⟨hDm, hDi⟩ := hD P B hB
  obtain ⟨L, hLm, hLi, hLd⟩ := hLL P B X hB hX hind hN
  refine ⟨fun ω => baseDist κ B ω ^ (-(κ / 2)) * L ω, (hDm.pow_const _).mul hLm, ?_, ?_⟩
  · have hpt : ∀ ω, (baseDist κ B ω ^ (-(κ / 2)) * L ω) ^ q ≤
        (1 + baseDist κ B ω ^ (-a)) + (1 + L ω ^ b) := by
      intro ω
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
      refine (bf2_mul_le_sq_add_sq _ _).trans (add_le_add ?_ ?_)
      · have e : ((baseDist κ B ω ^ (-(κ / 2))) ^ q) ^ (2 : ℕ) =
            baseDist κ B ω ^ (-(κ * q)) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          congr 1; push_cast; ring
        rw [e]
        exact bf2_rpow_neg_le_one_add (by positivity) hqa _
      · have e : (L ω ^ q) ^ (2 : ℕ) = L ω ^ (2 * q) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          congr 1; push_cast; ring
        rw [e]
        exact txsc_rpow_le_one_add (by positivity) hqb _
    calc ∫⁻ ω, (baseDist κ B ω ^ (-(κ / 2)) * L ω) ^ q ∂P
        ≤ ∫⁻ ω, ((1 + baseDist κ B ω ^ (-a)) + (1 + L ω ^ b)) ∂P := lintegral_mono hpt
      _ = ∫⁻ ω, (1 + baseDist κ B ω ^ (-a)) ∂P + ∫⁻ ω, (1 + L ω ^ b) ∂P :=
          lintegral_add_left' (aemeasurable_const.add (hDm.pow_const _)) _
      _ ≤ (1 + K) + (1 + CL) := by
          refine add_le_add ?_ ?_
          · rw [lintegral_add_left' aemeasurable_const, lintegral_const, measure_univ, mul_one]
            exact add_le_add le_rfl hDi
          · rw [lintegral_add_left' aemeasurable_const, lintegral_const, measure_univ, mul_one]
            exact add_le_add le_rfl hLi
  · filter_upwards [hLd] with ω hω
    have hw : winLam κ B ω 0 ^ (-(κ / 2)) ≤ baseDist κ B ω ^ (-(κ / 2)) :=
      by
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg, ← ENNReal.inv_rpow, ← ENNReal.inv_rpow]
        exact ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.2 (baseDist_le_winLam_zero κ B ω))
          (by linarith)
    have h1 : radius 0 ^ 2 = (1 : ℝ) := by simp [radius]
    refine ⟨?_, ?_⟩
    · unfold termL; rw [h1]; exact mul_le_mul' hw hω.1
    · unfold termR; rw [h1]; exact mul_le_mul' hw hω.2

end BaseFin2
end QuantumZipper
