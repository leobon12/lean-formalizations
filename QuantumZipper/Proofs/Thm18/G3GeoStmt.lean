import QuantumZipper.Proofs.Thm18.G3GeoHonest
import QuantumZipper.Proofs.Thm18.G3G2Scale

/-!
# G3-GEO, part 5: the geometric input `G3GeoStmt`

`G3GeoStmt γ` (`G3G2Scale.lean`): with Palm probability close to `1`, the Palm point `x` stays a
positive margin inside region 1 and its length partner `R(x)` inside region 2, along the
`δ`-then-`η` limits of `g3Filter`.

* `g3GeoStmt_x` (**proved**, `0 < γ < 2`): the `x`-half. With `δ` fixed and `η → 0`,
  `P_Palm(x leaves region 1 by m) ≤ Z⁻¹ E ν_h[−η, 0] → 0` (`G3GeoPalm`, `G3GeoHonest`).
* `g3GeoStmt_R_of_palm`: the `R(x)`-half from the named Palm estimate `G3GeoPalmRStmt γ`.
  `P_Palm(R leaves region 2 by m) ≤ Z⁻¹ E min(ν_h[0,η], ν_h[−δ,0]) + Z⁻¹ E[ν_h[−δ,0];
  ν_h[0,½] < ν_h[−δ,0]]` (`G3GeoRight`); the first term `→ 0` as `η → 0` (proved), the second
  is `G3GeoPalmRStmt`.
* `g3GeoStmt_of_palmR : G3GeoPalmRStmt γ → G3GeoStmt γ`.

`G3GeoPalmRStmt γ` is Sheffield's (arXiv:1012.4797, proof of Theorem 1.8, §5.4, p. 71) "We may
choose δ small enough so that with high probability `R(x) ∈ B₁(0)`", written for the Palm law:
the Palm probability (`x ~ ν_h|[−δ,0]`) that the length `ν_h[x, 0]` exceeds `ν_h[0, ½]` tends to
`0` as `δ → 0`. The paper gives no argument; it is left as an explicit input (it needs a genuine
Palm estimate: under the size-biased law `ν_h[−δ,0] dP / E ν_h[−δ,0]` the variable
`ν_h[0,½]` must not collapse to `0`).

Own elementary arguments (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- **The residual Palm estimate for `R(x)`** (Sheffield p. 71, Palm form): for every `ε > 0`,
for all small `δ > 0`, `E[ν_h[−δ,0]; ν_h[0,½] < ν_h[−δ,0]] ≤ ε · E ν_h[−δ,0]`. -/
def G3GeoPalmRStmt (γ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
    ∫⁻ ω, (if g3Hν γ ω (Icc 0 (1 / 2)) < g3Hν γ ω (Icc (-δ) 0) then g3Hν γ ω (Icc (-δ) 0)
      else 0) ∂gffBase.P ≤ ENNReal.ofReal ε * ∫⁻ ω, g3Hν γ ω (Icc (-δ) 0) ∂gffBase.P

theorem real_le_of_palm_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    {Z J : ℝ≥0∞} {e : ℝ} (hZ : 0 < Z ∧ Z < ⊤) (h : μ S ≤ Z⁻¹ * J)
    (hJ : J ≤ ENNReal.ofReal e * Z) (he : 0 ≤ e) : μ.real S ≤ e := by
  have h1 : μ S ≤ ENNReal.ofReal e := by
    refine h.trans ((mul_le_mul_of_nonneg_left hJ bot_le).trans (le_of_eq ?_))
    rw [mul_comm (ENNReal.ofReal e) Z, ← mul_assoc, ENNReal.inv_mul_cancel hZ.1.ne' hZ.2.ne,
      one_mul]
  rw [measureReal_def]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans (le_of_eq (ENNReal.toReal_ofReal he))

/-- **The `x`-half of `G3GeoStmt`**, proved. -/
theorem g3GeoStmt_x {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ m : ℚ, 0 < (m : ℝ) ∧
      ∀ i : G3Idx, i.1.1 = δ → i.1.2.1 = η →
        (g3PalmLaw γ i).real {p | i.r₁ ≤ |g3X γ i p - i.t₁| + m} < ε := by
  intro ε hε
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with δ hδ
  have hZpos : 0 < ∫⁻ ω, g3Hν γ ω (Icc (-δ) 0) ∂gffBase.P :=
    lintegral_qBoundaryMeasure_normField_Icc_pos gffBase.gff hγ hγ2 hδ.1
  have hev := (tendsto_order.1 (tendsto_lintegral_hν_left hγ hγ2 hδ.1 hδ.2)).2 _
    (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (half_pos hε)).ne' hZpos.ne')
  filter_upwards [hev, self_mem_nhdsWithin] with η hη hηpos
  have hηpos' : (0 : ℝ) < η := hηpos
  obtain ⟨mq, hmq0, hmq⟩ := exists_rat_btwn (show (0 : ℝ) < η / 4 by linarith)
  refine ⟨mq, hmq0, fun i hiδ hiη => ?_⟩
  have hiδ' : i.δ = δ := hiδ
  have hiη' : i.η = η := hiη
  have hZi := g3Z_pos_lt_top hγ hγ2 i
  have hmη : (mq : ℝ) < i.η / 4 := by rw [hiη']; exact hmq
  refine lt_of_le_of_lt (real_le_of_palm_bound hZi (g3PalmLaw_bad_le γ i hmη hZi) ?_
    (half_pos hε).le) (half_lt_self hε)
  rw [g3Z_eq_honest hγ hγ2 i, hiδ']
  have hsub := Icc_neg_subset_win i (a := 3 * i.η / 4 + (mq : ℝ)) (by linarith [i.hηδ])
  calc ∫⁻ ω, (g3ν₁ γ i ω + g3ν₀ γ i ω) (Icc (-(3 * i.η / 4 + (mq : ℝ))) 0) ∂gffBase.P
      = ∫⁻ ω, g3Hν γ ω (Icc (-(3 * i.η / 4 + (mq : ℝ))) 0) ∂gffBase.P :=
        lintegral_congr_ae ((ae_g3Fid_sets hγ hγ2).mono fun ω hω => (hω i).1 _ hsub)
    _ ≤ ∫⁻ ω, g3Hν γ ω (Icc (-η) 0) ∂gffBase.P :=
        lintegral_mono fun ω => measure_mono (Icc_subset_Icc_left (by linarith))
    _ ≤ ENNReal.ofReal (ε / 2) * ∫⁻ ω, g3Hν γ ω (Icc (-δ) 0) ∂gffBase.P := hη.le

/-- **The `R(x)`-half of `G3GeoStmt`** from the Palm estimate `G3GeoPalmRStmt`. -/
theorem g3GeoStmt_R_of_palm {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hP : G3GeoPalmRStmt γ) :
    ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ m : ℚ, 0 < (m : ℝ) ∧
      ∀ i : G3Idx, i.1.1 = δ → i.1.2.1 = η →
        (g3PalmLaw γ i).real {p | i.r₂ ≤ |g3R γ i p - i.t₂| + m} < ε := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  filter_upwards [hP (ε / 4) hε4, Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)]
    with δ hδP hδ
  have hZpos : 0 < ∫⁻ ω, g3Hν γ ω (Icc (-δ) 0) ∂gffBase.P :=
    lintegral_qBoundaryMeasure_normField_Icc_pos gffBase.gff hγ hγ2 hδ.1
  have hev := (tendsto_order.1 (tendsto_lintegral_hν_right hγ hγ2 hδ.1 hδ.2)).2 _
    (ENNReal.mul_pos (ENNReal.ofReal_pos.2 hε4).ne' hZpos.ne')
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with η hη hη2
  obtain ⟨mq, hmq0, hmq⟩ := exists_rat_btwn (show (0 : ℝ) < η / 4 by linarith [hη2.1])
  refine ⟨mq, hmq0, fun i hiδ hiη => ?_⟩
  have hiδ' : i.δ = δ := hiδ
  have hiη' : i.η = η := hiη
  have hZi := g3Z_pos_lt_top hγ hγ2 i
  have hmη : (mq : ℝ) < i.η / 4 := by rw [hiη']; exact hmq
  -- the measurable pieces
  have h₂ : Measurable fun ω => g3ν₀ γ i ω + g3ν₂ γ i ω := (measurable_g3sum₂ γ i).mono
    (sup_le (localSigma_le gffBase.gff i.t₂ i.r₂)
      (outsideSigma2_le gffBase.gff i.t₁ i.r₁ i.t₂ i.r₂)) le_rfl
  set cA : Ω₀ → ℝ≥0∞ := fun ω => (g3ν₀ γ i ω + g3ν₂ γ i ω) (Icc 0 i.η) with hcA
  set b : Ω₀ → ℝ≥0∞ := fun ω => (g3ν₀ γ i ω + g3ν₂ γ i ω) (Icc 0 (1 / 2)) with hb
  have hcAm : Measurable cA := (Measure.measurable_coe measurableSet_Icc).comp h₂
  have hbm : Measurable b := (Measure.measurable_coe measurableSet_Icc).comp h₂
  set cB : Ω₀ → ℝ≥0∞ := fun ω => if b ω < g3Mass γ i ω then ⊤ else 0 with hcB
  have hcBm : Measurable cB :=
    Measurable.ite (measurableSet_lt hbm (measurable_g3Mass γ i)) measurable_const
      measurable_const
  set A : Set (Ω₀ × ℝ) := {p | ENNReal.ofReal p.2 ≤ cA p.1} with hA
  set B : Set (Ω₀ × ℝ) := {p | b p.1 < ENNReal.ofReal p.2} with hB
  have hAm : MeasurableSet A :=
    measurableSet_le (ENNReal.measurable_ofReal.comp measurable_snd) (hcAm.comp measurable_fst)
  have hBm : MeasurableSet B :=
    measurableSet_lt (hbm.comp measurable_fst) (ENNReal.measurable_ofReal.comp measurable_snd)
  have hPA := g3PalmLaw_le_of_len γ i hZi hAm hcAm fun p hp _ _ => hp
  have hPB := g3PalmLaw_le_of_len γ i hZi hBm hcBm fun p hp _ hM => by
    have : b p.1 < g3Mass γ i p.1 := lt_of_lt_of_le hp hM
    simp only [hcB, if_pos this, le_top]
  -- the honest forms of the two integrals
  have hfid := ae_g3Fid_sets hγ hγ2
  have hM := g3Mass_ae_eq_honest hγ hγ2 i
  have hJA : ∫⁻ ω, min (cA ω) (g3Mass γ i ω) ∂gffBase.P ≤
      ENNReal.ofReal (ε / 4) * ∫⁻ ω, g3Hν γ ω (Icc (-δ) 0) ∂gffBase.P := by
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hη.le
    filter_upwards [hfid, hM] with ω hω hMω
    rw [hMω, hiδ', hcA]; dsimp only
    rw [(hω i).2 _ (Icc_pos_subset_win i (by linarith [i.hη, i.hηδ, i.hδ])), hiη']
  have hJB : ∫⁻ ω, min (cB ω) (g3Mass γ i ω) ∂gffBase.P ≤
      ENNReal.ofReal (ε / 4) * ∫⁻ ω, g3Hν γ ω (Icc (-δ) 0) ∂gffBase.P := by
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hδP
    filter_upwards [hfid, hM] with ω hω hMω
    have hbω : b ω = g3Hν γ ω (Icc 0 (1 / 2)) :=
      (hω i).2 _ (Icc_pos_subset_win i (by linarith [i.hη]))
    rw [hMω, hiδ', hcB]; dsimp only
    rw [hbω, hMω, hiδ']
    split_ifs <;> simp
  have hbad : g3PalmLaw γ i {p | i.r₂ ≤ |g3R γ i p - i.t₂| + mq} ≤ (g3Z γ i)⁻¹ *
      (∫⁻ ω, min (cA ω) (g3Mass γ i ω) ∂gffBase.P +
        ∫⁻ ω, min (cB ω) (g3Mass γ i ω) ∂gffBase.P) := by
    rw [mul_add]
    exact (measure_mono (g3BadR_subset γ i hmη)).trans
      ((measure_union_le A B).trans (add_le_add hPA hPB))
  refine lt_of_le_of_lt (real_le_of_palm_bound hZi hbad ?_ (half_pos hε).le) (half_lt_self hε)
  rw [g3Z_eq_honest hγ hγ2 i, hiδ']
  refine (add_le_add hJA hJB).trans (le_of_eq ?_)
  rw [← add_mul, ← ENNReal.ofReal_add hε4.le hε4.le]
  ring_nf

/-- **`G3GeoStmt` from the Palm estimate for `R(x)`.** -/
theorem g3GeoStmt_of_palmR {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hP : G3GeoPalmRStmt γ) :
    G3GeoStmt γ :=
  ⟨g3GeoStmt_x hγ hγ2, g3GeoStmt_R_of_palm hγ hγ2 hP⟩

end Thm18Asm
end QuantumZipper
