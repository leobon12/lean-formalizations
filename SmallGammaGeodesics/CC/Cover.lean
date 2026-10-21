import SmallGammaGeodesics.Core.Interfaces
import LQGMetric.Papers.LM.L3_4M6
import LQGMetric.Papers.GM.S3.DeterministicScale
import LQGMetric.Papers.GM.S2.TightLaw
import LQGMetric.Field.CircleAvgRate

/-!
# The generic good-annulus covering lemma (track CC, packet CC7)

Source: Gwynne–Miller arXiv:1905.00384 ([3]) Lemmas 3.7 and 3.11, and LM = arXiv:1905.00379
Lemmas 4.1–4.2 (`N = 0`), as planned in `planning/audits/CC0-conformal-covariance-plan.md`,
Details (a) **D12**. The statement `CC.CoverLemma` is fixed in `Core/Interfaces.lean`.

* `centreField h w = h(· + w) − (h(· + w))_1(0)`, a normalized whole-plane GFF
  (`isNormalizedWPGFF_centreField`).
* `exists_centre_event`: an event that is a.s. determined by `(h − h_R(w))|_{A_{s₁R, s₂R}(w)}` is
  a.s. equal to an event of `σ((h^w − h^w_R(0))|_{A_{s₁R, s₂R}(0)})`, `h^w = centreField h w`
  (translation by `GM.fieldSigma_le_affineComp`; pattern `GM.aeEventIn_goodAnnulus_translate`).
* `annulusLocal_tail`: **one centre** (LM Lemma 4.1 pattern for generic annulus-local events):
  if `P[E(w, N^{-k}ε)] ≥ p` for all `k`, then
  `P[E(w, N^{-j}ε)` fails for all `j ∈ [1, M]] ≤ c e^{-aM}`, from LM Lemma 3.1 (1)
  (`LQGMetric.LM.lmLem3_1a`) at the radii `c₀ N^{-k} ε`.
* `coverLemma_uniform`: the covering bound with explicit constants, uniform in the probability
  space, the field, the events and `r₀`: `P[some z ∈ K is not covered] ≤ c (8R₀ + 5)² ε^q` for
  `K ⊆ B̄_{R₀}(0)` and `ε < min(r₀, 1/N)`. Proof: `a = (4 + q) log N`, the scale `M` with
  `ε ≤ N^{-M} < Nε`, and a union bound over the `O(ε^{-4})` grid points of `(ε²/4)ℤ²` near `K`
  (pattern `LQGMetric.LM.lmLem4_2_of_tail`).
* `coverLemma : CoverLemma` (**T1**), from `coverLemma_uniform` with `R₀` from compactness.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-! ## 1. Translation to the centre -/

section Centre

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- the translated normalized field `h(· + w) − (h(· + w))_1(0)` -/
def centreField (h : Ω → DistC) (w : ℂ) : Ω → DistC := fun ω =>
  addConst (affineComp 1 w (h ω)) (-circleAvg (affineComp 1 w (h ω)) 1 0)

/-- `h(· + w) − (h(· + w))_1(0)` is a normalized whole-plane GFF -/
theorem isNormalizedWPGFF_centreField {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (w : ℂ) :
    IsNormalizedWPGFF (centreField h w) P := by
  have hz := hh.affineComp one_pos w
  have hm1 := measurable_circleAvg_left 1 0
  refine ⟨hz.addConst (hm1.comp hz.measurable).neg, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hz] with ω hω
  simp only [centreField]
  rw [hω]; ring

/-- the recentred translated field is a.s. the translate of the recentred field:
`h^w − h^w_R(0) = (h − h_R(w))(· + w)` -/
theorem ae_centreField_recentre {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (w : ℂ) {R : ℝ}
    (hR : 0 < R) :
    ∀ᵐ ω ∂P, addConst (centreField h w ω) (-circleAvg (centreField h w ω) R 0) =
      affineComp 1 w (addConst (h ω) (-circleAvg (h ω) R w)) := by
  have hz := hh.affineComp one_pos w
  filter_upwards [CircleAvg.ae_circleAvg_addConst hz 0 hR] with ω hω
  simp only [centreField]
  rw [hω, GM.affineComp_addConst one_pos, GM.Tight.circleAvg_affineComp_one,
    GM.Tight.circleAvg_affineComp_one, GFFLaw.addConst_addConst]
  congr 1
  ring

/-- **translation of an annulus-local event to the centre**: an event a.s. determined by
`(h − h_R(w))|_{A_{s₁R, s₂R}(w)}` is a.s. equal to an event determined by
`(h^w − h^w_R(0))|_{A_{s₁R, s₂R}(0)}`, `h^w = centreField h w`. -/
theorem exists_centre_event {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (w : ℂ) {R s₁ s₂ : ℝ}
    (hR : 0 < R) {E : Set Ω}
    (hE : AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) R w))
      (annulus w (s₁ * R) (s₂ * R))) E) :
    ∃ F : Set Ω, MeasurableSet[fieldSigma (fun ω =>
        addConst (centreField h w ω) (-circleAvg (centreField h w ω) R 0))
          (annulus 0 (s₁ * R) (s₂ * R))] F ∧ F =ᵐ[P] E := by
  obtain ⟨F, hF, hFae⟩ := hE
  have hUV : ∀ y : ℂ, y ∈ annulus 0 (s₁ * R) (s₂ * R) ↔
      (1 : ℝ) • y + w ∈ annulus w (s₁ * R) (s₂ * R) := fun y => by
    show s₁ * R < ‖y - 0‖ ∧ ‖y - 0‖ < s₂ * R ↔
      s₁ * R < ‖(1 : ℝ) • y + w - w‖ ∧ ‖(1 : ℝ) • y + w - w‖ < s₂ * R
    simp only [sub_zero, one_smul, add_sub_cancel_right]
  obtain ⟨B, hB, hBF⟩ := GM.fieldSigma_le_affineComp one_pos hUV _ F hF
  refine ⟨_, ⟨B, hB, rfl⟩, ?_⟩
  refine EventuallyEq.trans ?_ hFae.symm
  rw [← hBF]
  filter_upwards [ae_centreField_recentre hh w hR] with ω hω
  simp only [mem_preimage]
  rw [hω]

end Centre

/-! ## 2. One centre: LM Lemma 4.1 for generic annulus-local events -/

/-- **one centre** (LM Lemma 4.1 pattern, generic annulus-local events; from LM Lemma 3.1 (1),
`LQGMetric.LM.lmLem3_1a`, at the radii `c₀ N^{-k} ε`): if `P[E(w, N^{-k}ε)] ≥ p` for every `k`,
then the probability that `E(w, N^{-j}ε)` fails for every `j ∈ [1, M]` is at most `c e^{-aM}`.
The constants `p`, `c` depend only on `(s₁, s₂, a)`. -/
theorem annulusLocal_tail (c₀ s₁ s₂ : ℝ) (N : ℕ) (hc₀ : 0 < c₀) (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂)
    (hs₂ : s₂ < 1) (hN : 2 ≤ N) (hNs : (N : ℝ)⁻¹ ≤ s₁) (a : ℝ) (ha : 0 < a) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ E : ℂ → ℝ → Set Ω, IsAnnulusLocal P h E c₀ s₁ s₂ →
      ∀ (w : ℂ) (ε : ℝ), 0 < ε → (∀ k : ℕ, ENNReal.ofReal p ≤ P (E w ((N : ℝ)⁻¹ ^ k * ε))) →
      ∀ M : ℕ, P {ω | ∀ j ∈ Finset.Icc 1 M, ω ∉ E w ((N : ℝ)⁻¹ ^ j * ε)} ≤
        ENNReal.ofReal (c * Real.exp (-a * M)) := by
  obtain ⟨p, c, hp0, hp1, hc, H⟩ := LM.lmLem3_1a s₁ s₂ hs₁ hs₁₂ hs₂ a ha (1 / 2) (by norm_num)
    (by norm_num)
  refine ⟨p, max c 1, hp0, hp1, by positivity, ?_⟩
  intro Ω _ P _ h hh E hE w ε hε hp M
  have hNpos : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hNinv0 : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.2 hNpos
  have hNinv1 : (N : ℝ)⁻¹ ≤ 1 := hNs.trans (hs₁₂.trans hs₂).le
  set ρ : ℕ → ℝ := fun k => (N : ℝ)⁻¹ ^ k * ε with hρ
  have hρ0 : ∀ k, 0 < ρ k := fun k => mul_pos (pow_pos hNinv0 k) hε
  set R : ℕ → ℝ := fun k => c₀ * ρ k with hR
  have hR0 : ∀ k, 0 < R k := fun k => mul_pos hc₀ (hρ0 k)
  choose F hFm hFae using fun k => exists_centre_event hh w (hR0 k) (hE w (ρ k) (hρ0 k))
  have hAI : AnnulusIterHyp (centreField h w) s₁ s₂ R F := by
    refine ⟨hR0, fun i j hij => ?_, fun k => ?_, hFm⟩
    · have hpow : (N : ℝ)⁻¹ ^ j ≤ (N : ℝ)⁻¹ ^ i := pow_le_pow_of_le_one hNinv0.le hNinv1 hij
      show c₀ * ((N : ℝ)⁻¹ ^ j * ε) ≤ c₀ * ((N : ℝ)⁻¹ ^ i * ε)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hε.le) hc₀.le
    · have e : R (k + 1) = (N : ℝ)⁻¹ * R k := by
        show c₀ * ((N : ℝ)⁻¹ ^ (k + 1) * ε) = (N : ℝ)⁻¹ * (c₀ * ((N : ℝ)⁻¹ ^ k * ε))
        rw [pow_succ]; ring
      rw [e, mul_div_assoc, div_self (hR0 k).ne', mul_one]
      exact hNs
  have hPF : ∀ k, ENNReal.ofReal p ≤ P (F k) := fun k => by
    rw [measure_congr (hFae k)]; exact hp k
  have HB := H P (centreField h w) (isNormalizedWPGFF_centreField hh w) R F hAI hPF M
  have hae : ∀ᵐ ω ∂P, ∀ k, (ω ∈ F k ↔ ω ∈ E w (ρ k)) := by
    rw [ae_all_iff]; intro k
    filter_upwards [hFae k] with ω hω
    exact Iff.of_eq hω
  rcases Nat.eq_zero_or_pos M with hM0 | hM0
  · subst hM0
    calc P _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (max c 1 * Real.exp (-a * ((0 : ℕ) : ℝ))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
          exact le_max_right _ _
  calc P {ω | ∀ j ∈ Finset.Icc 1 M, ω ∉ E w ((N : ℝ)⁻¹ ^ j * ε)}
        ≤ P {ω | (countOcc F M ω : ℝ) < 1 / 2 * M} := by
        refine measure_mono_ae ?_
        filter_upwards [hae] with ω hω hbad
        have h0 : countOcc F M ω = 0 := by
          classical
          unfold countOcc
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro k hk hkF
          exact hbad k hk ((hω k).1 hkF)
        show (countOcc F M ω : ℝ) < 1 / 2 * M
        rw [h0]
        have : (0 : ℝ) < M := by exact_mod_cast hM0
        push_cast; linarith
    _ ≤ ENNReal.ofReal (c * Real.exp (-a * M)) := HB
    _ ≤ ENNReal.ofReal (max c 1 * Real.exp (-a * M)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.exp_pos _).le)

/-! ## 3. Arithmetic of the scales and of the union bound -/

/-- the scale `M` with `ε ≤ N^{-M} < Nε` -/
lemma exists_scale_inv_pow {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ M : ℕ, ε ≤ (N : ℝ)⁻¹ ^ M ∧ (N : ℝ)⁻¹ ^ M < N * ε := by
  classical
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNinv1 : (N : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hex : ∃ n : ℕ, (N : ℝ)⁻¹ ^ n < ε := exists_pow_lt_of_lt_one hε0 hNinv1
  set n₀ := Nat.find hex with hn₀
  have hn₀0 : n₀ ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hn₀, h0, pow_zero] at this
    linarith
  refine ⟨n₀ - 1, not_lt.1 (Nat.find_min hex (by omega)), ?_⟩
  have h1 := Nat.find_spec hex
  rw [← hn₀, show n₀ = (n₀ - 1) + 1 by omega, pow_succ] at h1
  have hNpos : (0 : ℝ) < N := by linarith
  have := mul_lt_mul_of_pos_left h1 hNpos
  rwa [mul_comm (N : ℝ) ((N : ℝ)⁻¹ ^ (n₀ - 1) * (N : ℝ)⁻¹), mul_assoc,
    inv_mul_cancel₀ hNpos.ne', mul_one] at this

/-- `e^{-(4+q) log N · M} ≤ N⁴ N^q ε⁴ ε^q` when `N^{-M} < Nε` -/
lemma exp_neg_scale_le {N : ℕ} (hN : 2 ≤ N) {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) {M : ℕ}
    (hM : (N : ℝ)⁻¹ ^ M < N * ε) :
    Real.exp (-((4 + q) * Real.log N) * M) ≤ (N : ℝ) ^ 4 * (N : ℝ) ^ q * ε ^ 4 * ε ^ q := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set x : ℝ := (N : ℝ)⁻¹ ^ M with hx
  have hx0 : 0 < x := pow_pos (inv_pos.2 hNpos) M
  have e1 : Real.exp (-((4 + q) * Real.log N) * M) = x ^ (4 + q) := by
    rw [Real.rpow_def_of_pos hx0, hx, Real.log_pow, Real.log_inv]
    congr 1; ring
  have h4q : (0 : ℝ) ≤ 4 + q := by linarith
  rw [e1]
  calc x ^ (4 + q) ≤ ((N : ℝ) * ε) ^ (4 + q) := Real.rpow_le_rpow hx0.le hM.le h4q
    _ = (N : ℝ) ^ 4 * (N : ℝ) ^ q * ε ^ 4 * ε ^ q := by
        rw [Real.rpow_add (by positivity), Real.mul_rpow hNpos.le hε0.le,
          Real.mul_rpow hNpos.le hε0.le, Real.rpow_ofNat, Real.rpow_ofNat]
        ring

/-- the count of the grid box: `(2M + 1)² ε⁴ ≤ (8R₀ + 5)²` when `M ε²/4 ≤ R₀ + ε²/2` -/
lemma box_card_arith {ε R₀ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {M : ℕ}
    (hM : (M : ℝ) * (ε ^ 2 / 4) ≤ R₀ + 2 * (ε ^ 2 / 4)) :
    (2 * M + 1 : ℝ) ^ 2 * ε ^ 4 ≤ (8 * R₀ + 5) ^ 2 := by
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1.le
  have hb : (2 * M + 1 : ℝ) * ε ^ 2 ≤ 8 * R₀ + 5 := by
    have e : (2 * M + 1 : ℝ) * ε ^ 2 = 8 * ((M : ℝ) * (ε ^ 2 / 4)) + ε ^ 2 := by ring
    rw [e]; linarith only [hM, hε2]
  have hb0 : 0 ≤ (2 * M + 1 : ℝ) * ε ^ 2 := by positivity
  have e : (2 * M + 1 : ℝ) ^ 2 * ε ^ 4 = ((2 * M + 1 : ℝ) * ε ^ 2) ^ 2 := by ring
  rw [e]
  exact pow_le_pow_left₀ hb0 hb 2

/-! ## 4. The covering lemma -/

/-- **the covering lemma with explicit, uniform constants**: `p ∈ (0,1)` and `c > 0` depend only on
`(s₁, s₂, N, q)`; for every whole-plane GFF `h`, annulus-local events `E` with `P[E(w, r)] ≥ p` for
`dist(w, K) ≤ 1`, `r ≤ r₀`, and every set `K ⊆ B̄_{R₀}(0)`, the probability that some `z ∈ K` is not
covered by a ball `B_{N^{-k}ε/2}(w)`, `w ∈ (ε²/4)ℤ²`, `ε² ≤ N^{-k}ε`, with `E(w, N^{-k}ε)`, is at
most `c (8R₀ + 5)² ε^q` for every `ε ∈ (0, min(r₀, 1/N))`. -/
theorem coverLemma_uniform (c₀ s₁ s₂ : ℝ) (N : ℕ) (hc₀ : 0 < c₀) (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂)
    (hs₂ : s₂ < 1) (hN : 2 ≤ N) (hNs : (N : ℝ)⁻¹ ≤ s₁) (q : ℝ) (hq : 0 < q) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ E : ℂ → ℝ → Set Ω, IsAnnulusLocal P h E c₀ s₁ s₂ →
      ∀ (K : Set ℂ) (R₀ : ℝ), 0 ≤ R₀ → K ⊆ closedBall 0 R₀ → ∀ r₀ : ℝ,
      (∀ w : ℂ, infDist w K ≤ 1 → ∀ r ∈ Ioc (0 : ℝ) r₀, ENNReal.ofReal p ≤ P (E w r)) →
      ∀ ε ∈ Ioo (0 : ℝ) (min r₀ (N : ℝ)⁻¹),
        P {ω | ¬ ∀ z ∈ K, ∃ k : ℕ, ∃ m : ℤ × ℤ, ε ^ 2 ≤ (N : ℝ)⁻¹ ^ k * ε ∧
          ‖z - GM.gridPt (ε ^ 2 / 4) m‖ < (N : ℝ)⁻¹ ^ k * ε / 2 ∧
          ω ∈ E (GM.gridPt (ε ^ 2 / 4) m) ((N : ℝ)⁻¹ ^ k * ε)} ≤
          ENNReal.ofReal (c * (8 * R₀ + 5) ^ 2 * ε ^ q) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNinv0 : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.2 hNpos
  have hNinv1 : (N : ℝ)⁻¹ ≤ 1 := hNs.trans (hs₁₂.trans hs₂).le
  have ha : 0 < (4 + q) * Real.log N := mul_pos (by linarith) (Real.log_pos (by linarith))
  obtain ⟨p, c, hp0, hp1, hc, H⟩ := annulusLocal_tail c₀ s₁ s₂ N hc₀ hs₁ hs₁₂ hs₂ hN hNs _ ha
  refine ⟨p, c * (N : ℝ) ^ 4 * (N : ℝ) ^ q, hp0, hp1, by positivity, ?_⟩
  intro Ω _ P _ h hh E hE K R₀ hR₀ hKR r₀ hpK ε ⟨hε0, hεm⟩
  have hεr : ε ≤ r₀ := (hεm.trans_le (min_le_left _ _)).le
  have hεN : ε < (N : ℝ)⁻¹ := hεm.trans_le (min_le_right _ _)
  have hε1 : ε < 1 := hεN.trans_le hNinv1
  obtain ⟨M, hM1, hM2⟩ := exists_scale_inv_pow hN hε0 hε1
  set δ : ℝ := ε ^ 2 / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    have : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1.le
    rw [hδ]; linarith
  set Mb : ℕ := ⌈R₀ / δ⌉₊ + 1 with hMbdef
  have hMlt : (Mb : ℝ) < R₀ / δ + 2 := by
    rw [hMbdef]; push_cast
    linarith [Nat.ceil_lt_add_one (show 0 ≤ R₀ / δ by positivity)]
  have hMge : R₀ / δ + 1 ≤ (Mb : ℝ) := by
    rw [hMbdef]; push_cast
    linarith [Nat.le_ceil (R₀ / δ)]
  have hMx : (Mb : ℝ) * δ ≤ R₀ + 2 * δ := by
    have := mul_le_mul_of_nonneg_right hMlt.le hδ0.le
    rwa [add_mul, div_mul_cancel₀ _ hδ0.ne'] at this
  set Box : Finset (ℤ × ℤ) := Finset.Icc (-(Mb : ℤ)) Mb ×ˢ Finset.Icc (-(Mb : ℤ)) Mb with hBox
  classical
  -- the bad event at the grid point `δ m` (empty unless `δ m` is within distance `1` of `K`)
  set F : ℤ × ℤ → Set Ω := fun m => if infDist (GM.gridPt δ m) K ≤ 1 then
    {ω | ∀ j ∈ Finset.Icc 1 M, ω ∉ E (GM.gridPt δ m) ((N : ℝ)⁻¹ ^ j * ε)} else ∅ with hF
  have hsub : {ω | ¬ ∀ z ∈ K, ∃ k : ℕ, ∃ m : ℤ × ℤ, ε ^ 2 ≤ (N : ℝ)⁻¹ ^ k * ε ∧
      ‖z - GM.gridPt δ m‖ < (N : ℝ)⁻¹ ^ k * ε / 2 ∧
      ω ∈ E (GM.gridPt δ m) ((N : ℝ)⁻¹ ^ k * ε)} ⊆ ⋃ m ∈ Box, F m := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, not_exists, not_and] at hω
    obtain ⟨z, hz, hy⟩ := hω
    have hzn : ‖z‖ ≤ R₀ := by simpa using hKR hz
    have hbd : ∀ t : ℝ, |t| ≤ ‖z‖ → |t| / δ + 1 ≤ Mb := by
      intro t ht
      have : |t| / δ ≤ R₀ / δ := div_le_div_of_nonneg_right (ht.trans hzn) hδ0.le
      linarith
    obtain ⟨hre1, hre2⟩ := GM.round_grid hδ0 (hbd _ (Complex.abs_re_le_norm _))
    obtain ⟨him1, him2⟩ := GM.round_grid hδ0 (hbd _ (Complex.abs_im_le_norm _))
    set m : ℤ × ℤ := (round (z.re / δ), round (z.im / δ)) with hm
    have hdist : ‖z - GM.gridPt δ m‖ ≤ δ := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [Complex.sub_re, Complex.sub_im, GM.gridPt_re, GM.gridPt_im]
      linarith
    have hinf : infDist (GM.gridPt δ m) K ≤ 1 := by
      refine (infDist_le_dist_of_mem hz).trans ?_
      rw [dist_comm, dist_eq_norm]; linarith
    refine mem_biUnion (x := m) (Finset.mem_coe.2 (Finset.mem_product.2 ⟨hre2, him2⟩)) ?_
    simp only [hF, ite_eq_left hinf, mem_ofPred_eq]
    intro j hj hjE
    have hjM := (Finset.mem_Icc.1 hj).2
    have hpow : (N : ℝ)⁻¹ ^ M ≤ (N : ℝ)⁻¹ ^ j := pow_le_pow_of_le_one hNinv0.le hNinv1 hjM
    have hεj : ε ≤ (N : ℝ)⁻¹ ^ j := hM1.trans hpow
    have hr1 : ε ^ 2 ≤ (N : ℝ)⁻¹ ^ j * ε := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hεj hε0.le
    have hr2 : ‖z - GM.gridPt δ m‖ < (N : ℝ)⁻¹ ^ j * ε / 2 := by
      have : δ < ε ^ 2 / 2 := by
        have := pow_pos hε0 2
        rw [hδ]; linarith
      linarith
    exact hy j m hr1 hr2 hjE
  have hFm : ∀ m ∈ Box, P (F m) ≤
      ENNReal.ofReal (c * ((N : ℝ) ^ 4 * (N : ℝ) ^ q * ε ^ 4 * ε ^ q)) := by
    intro m _
    simp only [hF]
    split_ifs with hm
    · refine (H P h hh E hE (GM.gridPt δ m) ε hε0 (fun k => ?_) M).trans ?_
      · refine hpK _ hm _ ⟨mul_pos (pow_pos hNinv0 k) hε0, ?_⟩
        have : (N : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ hNinv0.le hNinv1
        calc (N : ℝ)⁻¹ ^ k * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right this hε0.le
          _ = ε := one_mul ε
          _ ≤ r₀ := hεr
      · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (exp_neg_scale_le hN hq hε0 hM2) hc.le)
    · simp
  have hcard : (Box.card : ℝ) = (2 * Mb + 1 : ℝ) ^ 2 := by
    rw [hBox, Finset.card_product, Int.card_Icc]
    have : ((Mb : ℤ) + 1 - -(Mb : ℤ)).toNat = 2 * Mb + 1 := by omega
    rw [this]; push_cast; ring
  calc P _ ≤ P (⋃ m ∈ Box, F m) := measure_mono hsub
    _ ≤ ∑ m ∈ Box, P (F m) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _m ∈ Box, ENNReal.ofReal (c * ((N : ℝ) ^ 4 * (N : ℝ) ^ q * ε ^ 4 * ε ^ q)) :=
        Finset.sum_le_sum hFm
    _ = ENNReal.ofReal ((Box.card : ℝ) *
          (c * ((N : ℝ) ^ 4 * (N : ℝ) ^ q * ε ^ 4 * ε ^ q))) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := (Box.card : ℝ)) (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (c * (N : ℝ) ^ 4 * (N : ℝ) ^ q * (8 * R₀ + 5) ^ 2 * ε ^ q) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hcard]
        have hbox := box_card_arith hε0 hε1 hMx
        have hk : 0 ≤ c * (N : ℝ) ^ 4 * (N : ℝ) ^ q * ε ^ q := by positivity
        calc (2 * Mb + 1 : ℝ) ^ 2 * (c * ((N : ℝ) ^ 4 * (N : ℝ) ^ q * ε ^ 4 * ε ^ q))
            = c * (N : ℝ) ^ 4 * (N : ℝ) ^ q * ε ^ q * ((2 * Mb + 1 : ℝ) ^ 2 * ε ^ 4) := by ring
          _ ≤ c * (N : ℝ) ^ 4 * (N : ℝ) ^ q * ε ^ q * (8 * R₀ + 5) ^ 2 :=
              mul_le_mul_of_nonneg_left hbox hk
          _ = c * (N : ℝ) ^ 4 * (N : ℝ) ^ q * (8 * R₀ + 5) ^ 2 * ε ^ q := by ring

/-- **T1: the generic good-annulus covering lemma** (`CoverLemma`; [3] Lemmas 3.7, 3.11,
LM Lemma 4.2, CC0 D12), with `C = c (8R₀ + 5)²` (`K ⊆ B̄_{R₀}(0)`) and `ε₁ = min(r₀, 1/N)` from
`coverLemma_uniform`. -/
theorem coverLemma : CoverLemma := by
  intro c₀ s₁ s₂ N hc₀ hs₁ hs₁₂ hs₂ hN hNs q hq
  obtain ⟨p, c, hp0, hp1, -, H⟩ := coverLemma_uniform c₀ s₁ s₂ N hc₀ hs₁ hs₁₂ hs₂ hN hNs q hq
  refine ⟨p, hp0, hp1, ?_⟩
  intro Ω _ P _ h hh E hE K hK r₀ hr₀ hpK
  obtain ⟨R₀, hR₀, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  have hNinv0 : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (by omega : 0 < N))
  exact ⟨c * (8 * R₀ + 5) ^ 2, min r₀ (N : ℝ)⁻¹, lt_min hr₀ hNinv0,
    H P h hh E hE K R₀ hR₀.le hKR r₀ hpK⟩

end SmallGammaGeodesics.CC
