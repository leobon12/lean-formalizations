import HigherDimLQGMetric.DGZ.BadBoxCEvent

/-!
# DGZ Lemmas 5.7 and 5.8: the recursion for the bad-box probabilities (packet L4a2)

Source: [2] Lemma 5.7 (TeX l. 2264–2323, p. 44) and Lemma 5.8 (TeX l. 2327–2351, p. 45); planning
audit MA7 D-5.5–5.9 (Lemma 5.7: "case (a′) fails `≤ Ce^{-Ka_j}` (D-OSC); `ℬ₁` … and `ℬ₂` as in [2]
with Remark 5.4′"; Lemma 5.8: "with `β ∈ (d+α, Q²/2)` …"), G24; blueprint Lemmas `r2:lem:57`,
`r2:lem:58`.

* `BadBox.prob_bad_add_two_le` (the union bound of Lemma 5.7): by L4a1's case split
  `not_niceBox_add_two_cases`, a bad `a_j`-box (`j = j' + 2`) fails (a′), or contains two bad
  `a_{j-1}`-boxes with centres `≥ R s_{j-1}` apart (`ℬ₁`: L4a1's `measure_bad_inter_bad_eq`, at most
  `S²` pairs, `S = (2N-1)^d`, `N = 2^{a_j - a_{j-1}}`), or `𝒞(x,z)` fails for some `z = s_{j-1} w ∈
  B_{s_j}(x)` while some `a_{j-1}`-box in `B_{R s_{j-1}}(z)` is bad (`ℬ₂`: L4a1's
  `measure_not_niceCEvent_inter_exists_bad_eq`, at most `S` centres and `(2R-1)^d` boxes each);
  all `a_{j-1}`-boxes have the same bad probability (`prob_bad_eq`).
* `lemma57` (**target**):
  `q_j ≤ C (e^{-K a_j} + 2^{2dλa_{j-1}} q_{j-1}² + 2^{(d-β)λa_{j-1}} q_{j-1})` with
  `C = 1 + 16^d + 4^d (2R)^d`, using `S ≤ 4^d 2^{dλa_{j-1}}` (`a_j - a_{j-1} ≤ λa_{j-1} + 1`).
* `q_le` (**target**, Lemma 5.8): `q_j ≤ 2^{-α a_j}` for `1 ≤ j` with `a_j ≤ n`, by induction from
  Lemma 5.5 (`j = 1`, `η = 2^{-αK⁴}`) and Lemma 5.7 with `β = d + 3α/2 ∈ (d + α, Q²/2)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## The union bound of Lemma 5.7 -/

namespace BadBox

/-- **The union bound of DGZ Lemma 5.7** (deterministic case split + independence): for a dyadic
realization, a monotone exponent sequence, `R ≥ 2ρ + 10` (`ρ` a support radius of `κ`), level
`j + 2` with `a_{j+2} ≤ n`, `m(a_{j+1}) ≤ a_{j+1}`, the gaps `(2ρ + R + 4) s_{i-1} ≤ s_i`
(`2 ≤ i ≤ j + 2`), and bounds `eA` for the failure of (a′) and `y` for the failure of every
`𝒞(x, z)`: with `N = 2^{a_{j+2} - a_{j+1}}`, `S = (2N - 1)^d` and `q = P[the a_{j+1}-box at u' is
bad]`, `P[B_{s_{j+2}}(s_{j+2} u) is bad] ≤ eA + S² q² + S · y · (2R - 1)^d q`. -/
theorem prob_bad_add_two_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H)
    {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (p : NiceParams) (hmono : Monotone p.a)
    (hR : 2 * ρ + 10 ≤ (p.R : ℝ)) {j : ℕ} (hjn : p.a (j + 2) ≤ p.n)
    (hsS : superScale (p.a (j + 1)) ≤ p.a (j + 1))
    (hgap : ∀ i, 2 ≤ i → i ≤ j + 2 → (2 * ρ + p.R + 4) * p.s (i - 1) ≤ p.s i)
    (u u' : Zd d) {eA y : ℝ≥0∞}
    (hA : P {ω | ¬ NiceOscCond p (fun q z => H q z ω) (j + 2) u} ≤ eA)
    (hC : ∀ w : Zd d, P {ω | ¬ NiceCEvent p (fun q z => H q z ω) (j + 2) u w} ≤ y) :
    P {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 2) u} ≤
      eA + (((2 * 2 ^ (p.a (j + 2) - p.a (j + 1)) - 1) ^ d *
          (2 * 2 ^ (p.a (j + 2) - p.a (j + 1)) - 1) ^ d : ℕ) : ℝ≥0∞) *
          P {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 1) u'} ^ 2 +
        (((2 * 2 ^ (p.a (j + 2) - p.a (j + 1)) - 1) ^ d : ℕ) : ℝ≥0∞) *
          (y * ((((2 * p.R - 1) ^ d : ℕ) : ℝ≥0∞) *
            P {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 1) u'})) := by
  classical
  have hρ0 : 0 < ρ := hκ.radius_pos hρ
  have hR4 : (4 : ℝ) ≤ p.R := by linarith
  have hR1 : 1 ≤ p.R := by exact_mod_cast (show (1 : ℝ) ≤ p.R by linarith)
  have hc : ∀ q ω, Continuous fun z => H q z ω := fun q => (hH.band q).continuous
  have hs' := p.s_pos (j + 1)
  -- the gap conditions in L4a1's forms
  have hgap8 : ∀ i, 2 ≤ i → i ≤ j + 1 → 8 * p.s (i - 1) ≤ p.s i ∧
      (p.R : ℝ) * p.s (i - 1) ≤ p.s i := by
    intro i hi hij
    have h1 := hgap i hi (by omega)
    have h2 := p.s_pos (i - 1)
    constructor <;> nlinarith
  have hgapj : (2 * ρ + p.R + 4) * p.s (j + 2 - 1) ≤ p.s (j + 2) := hgap (j + 2) le_add_self le_rfl
  -- `s_{j+2} = N s_{j+1}`
  have haj : p.a (j + 1) ≤ p.a (j + 2) := hmono (Nat.le_succ _)
  set N : ℕ := 2 ^ (p.a (j + 2) - p.a (j + 1)) with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hsN : p.s (j + 2) = (N : ℝ) * p.s (j + 1) := by
    have h := BadBox.s_eq_pow_mul p (i := j + 1) (j := j + 2) (Nat.sub_le_sub_left haj _)
    have e : (p.n - p.a (j + 1)) - (p.n - p.a (j + 2)) = p.a (j + 2) - p.a (j + 1) := by omega
    rw [e] at h
    exact h
  set S : Finset (Zd d) := BadBox.cube ((N : ℤ) • u) (N - 1) with hS
  have hScard : S.card = (2 * N - 1) ^ d := by
    rw [hS, BadBox.card_cube]
    congr 1
    omega
  set q := P {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 1) u'} with hq
  have hqeq : ∀ v : Zd d, P {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 1) v} = q := fun v =>
    prob_bad_eq hκ hH p hmono (j + 1) v u'
  -- the three events
  set EB₁ : Set Ω := {ω | ∃ vv : Zd d × Zd d,
    (vv.1 ∈ S ∧ vv.2 ∈ S) ∧ (¬ NiceBox p (fun q z => H q z ω) (j + 1) vv.1 ∧
      ¬ NiceBox p (fun q z => H q z ω) (j + 1) vv.2 ∧ ∃ i, (p.R : ℤ) ≤ |vv.1 i - vv.2 i|)}
    with hEB₁
  set EB₂ : Set Ω := {ω | ∃ w : Zd d, w ∈ S ∧
    (¬ NiceCEvent p (fun q z => H q z ω) (j + 2) u w ∧
      ∃ v : Zd d, obox (latPt (p.s (j + 1)) v) (p.s (j + 1)) ⊆
        obox (latPt (p.s (j + 1)) w) (p.R * p.s (j + 1)) ∧
        ¬ NiceBox p (fun q z => H q z ω) (j + 1) v)} with hEB₂
  have hsplit : {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 2) u} ⊆
      ({ω | ¬ NiceOscCond p (fun q z => H q z ω) (j + 2) u} ∪ EB₁) ∪ EB₂ := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    rcases not_niceBox_add_two_cases p (fun q z => H q z ω) hR1 hω with h1 | h2 | h3
    · exact Or.inl (Or.inl h1)
    · obtain ⟨v₁, v₂, hv₁, hv₂, hb₁, hb₂, hfar⟩ := h2
      refine Or.inl (Or.inr ⟨(v₁, v₂), ⟨?_, ?_⟩, hb₁, hb₂, hfar⟩)
      · rw [hsN] at hv₁
        exact (BadBox.obox_subset_iff_mem_cube hs' N hN1 u v₁).1 hv₁
      · rw [hsN] at hv₂
        exact (BadBox.obox_subset_iff_mem_cube hs' N hN1 u v₂).1 hv₂
    · obtain ⟨w, hw, hbad, hnC⟩ := h3
      refine Or.inr ⟨w, ?_, hnC, hbad⟩
      rw [hsN] at hw
      exact (BadBox.latPt_mem_obox_iff_mem_cube hs' N hN1 u w).1 hw
  -- `ℬ₁`
  have hB₁ : P EB₁ ≤ ((S.card * S.card : ℕ) : ℝ≥0∞) * q ^ 2 := by
    refine (BadBox.measure_exists_le_card_mul P (S ×ˢ S) (fun vv => vv.1 ∈ S ∧ vv.2 ∈ S) _
      (fun vv hvv => Finset.mem_product.2 hvv) (b := q ^ 2) fun vv _ => ?_).trans ?_
    · by_cases hfar : ∃ i, (p.R : ℤ) ≤ |vv.1 i - vv.2 i|
      · have e : {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 1) vv.1 ∧
            ¬ NiceBox p (fun q z => H q z ω) (j + 1) vv.2 ∧ ∃ i, (p.R : ℤ) ≤ |vv.1 i - vv.2 i|} =
            {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 1) vv.1} ∩
              {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 1) vv.2} := by
          ext ω
          simp only [mem_ofPred_eq, mem_inter_iff]
          exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hfar⟩⟩
        rw [e, measure_bad_inter_bad_eq hκ hH hρ p hmono hR4 hR hgap8 hfar, hqeq, hqeq, sq]
      · have e : {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 1) vv.1 ∧
            ¬ NiceBox p (fun q z => H q z ω) (j + 1) vv.2 ∧ ∃ i, (p.R : ℤ) ≤ |vv.1 i - vv.2 i|} =
            ∅ := by
          ext ω
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact fun h => hfar h.2.2
        rw [e, measure_empty]
        exact zero_le
    · rw [Finset.card_product]
  -- `ℬ₂`
  have hB₂ : P EB₂ ≤ (S.card : ℝ≥0∞) * (y * ((((2 * p.R - 1) ^ d : ℕ) : ℝ≥0∞) * q)) := by
    refine BadBox.measure_exists_le_card_mul P S (fun w => w ∈ S) _ (fun w hw => hw) fun w hw => ?_
    have hw' : latPt (p.s (j + 1)) w ∈ obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) := by
      rw [hsN]
      exact (BadBox.latPt_mem_obox_iff_mem_cube hs' N hN1 u w).2 hw
    have key := measure_not_niceCEvent_inter_exists_bad_eq hκ hH hρ p hmono hR4 (j := j + 2) hjn
      hsS (by linarith) hgapj hgap8 hw'
    rw [show j + 2 - 1 = j + 1 from rfl] at key
    have e : {ω | ¬ NiceCEvent p (fun q z => H q z ω) (j + 2) u w ∧
        ∃ v : Zd d, obox (latPt (p.s (j + 1)) v) (p.s (j + 1)) ⊆
          obox (latPt (p.s (j + 1)) w) (p.R * p.s (j + 1)) ∧
          ¬ NiceBox p (fun q z => H q z ω) (j + 1) v} =
        {ω | ¬ NiceCEvent p (fun q z => H q z ω) (j + 2) u w} ∩
          {ω | ∃ v : Zd d, obox (latPt (p.s (j + 1)) v) (p.s (j + 1)) ⊆
            obox (latPt (p.s (j + 1)) w) (p.R * p.s (j + 1)) ∧
            ¬ NiceBox p (fun q z => H q z ω) (j + 1) v} := rfl
    rw [e, key]
    refine mul_le_mul' (hC w) ?_
    -- at most `(2R-1)^d` boxes near `z`
    have hcube : (BadBox.cube w (p.R - 1)).card = (2 * p.R - 1) ^ d := by
      rw [BadBox.card_cube]
      congr 1
      omega
    rw [← hcube]
    refine BadBox.measure_exists_le_card_mul P (BadBox.cube w (p.R - 1)) _ _
      (fun v hv => (BadBox.obox_subset_R_iff_mem_cube hs' hR1 v w).1 hv) fun v _ => ?_
    rw [hqeq]
  -- combine
  calc P {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 2) u}
      ≤ P (({ω | ¬ NiceOscCond p (fun q z => H q z ω) (j + 2) u} ∪ EB₁) ∪ EB₂) :=
        measure_mono hsplit
    _ ≤ eA + ((S.card * S.card : ℕ) : ℝ≥0∞) * q ^ 2 +
        (S.card : ℝ≥0∞) * (y * ((((2 * p.R - 1) ^ d : ℕ) : ℝ≥0∞) * q)) :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add hA hB₁)) hB₂)
    _ = _ := by rw [hScard]

end BadBox

/-! ## Lemma 5.7 -/

namespace BadBox

/-- The number of `a_{j-1}`-boxes in an `a_j`-box: `(2·2^{a_j - a_{j-1}} - 1)^d ≤ 4^d 2^{dλa_{j-1}}`
when `a_j ≤ (1+λ) a_{j-1} + 1`. -/
theorem card_subBoxes_le {lam : ℝ} {N A : ℕ} (hNA : N ≤ A) (h : (A : ℝ) ≤ (1 + lam) * N + 1) :
    (((2 * 2 ^ (A - N) - 1) ^ d : ℕ) : ℝ) ≤ 4 ^ d * (2 : ℝ) ^ ((d : ℝ) * lam * N) := by
  have h1 : (((2 * 2 ^ (A - N) - 1) ^ d : ℕ) : ℝ) ≤ ((2 : ℝ) * 2 ^ (A - N)) ^ d := by
    have : (2 * 2 ^ (A - N) - 1) ^ d ≤ (2 * 2 ^ (A - N)) ^ d :=
      Nat.pow_le_pow_left (Nat.sub_le _ _) d
    exact_mod_cast this
  have h2 : (2 : ℝ) ^ (A - N) ≤ (2 : ℝ) ^ (lam * N + 1) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    rw [Nat.cast_sub hNA]
    linarith
  have h3 : ((2 : ℝ) * (2 : ℝ) ^ (lam * N + 1)) ^ d = 4 ^ d * (2 : ℝ) ^ ((d : ℝ) * lam * N) := by
    rw [Real.rpow_add two_pos, Real.rpow_one,
      show (2 : ℝ) * (2 ^ (lam * N) * 2) = 4 * 2 ^ (lam * N) by ring, mul_pow,
      BadBox.two_rpow_pow]
    congr 2
    ring
  calc (((2 * 2 ^ (A - N) - 1) ^ d : ℕ) : ℝ) ≤ ((2 : ℝ) * 2 ^ (A - N)) ^ d := h1
    _ ≤ ((2 : ℝ) * (2 : ℝ) ^ (lam * N + 1)) ^ d := by gcongr
    _ = _ := h3

end BadBox

/-- **DGZ Lemma 5.7** (target `lemma57`; MA7 D-5.5–5.9, G24; blueprint `r2:lem:57`): for
`β ∈ (d, Q²/2)` and `R ≥ 2ρ + 10` (`ρ` a support radius of `κ`) there are `C > 0` and `θ₀ > 0` such
that for every `θ ∈ (0, θ₀]` there is `K₀` with
`q_j ≤ C (e^{-K a_j} + 2^{2dλa_{j-1}} q_{j-1}² + 2^{(d-β)λa_{j-1}} q_{j-1})` for every dyadic
realization, DGZ's sequence with `K ≥ K₀`, all `n, k`, `2 ≤ j` with `a_j ≤ n` and all boxes, where
`q_j = P[B_{s_j}(s_j u) is bad]` and `q_{j-1} = P[B_{s_{j-1}}(s_{j-1} u') is bad]` (by
`prob_bad_eq` neither depends on the box). `C = 1 + 16^d + 4^d (2R)^d` depends only on `d, R`. -/
theorem lemma57 {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {R : ℕ} (hR : 2 * ρ + 10 ≤ (R : ℝ)) {β : ℝ}
    (hβd : (d : ℝ) < β) (hβQ : β < Q ^ 2 / 2) :
    ∃ C > 0, ∃ θ₀ > 0, ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ K₀ : ℕ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.R = R → K₀ ≤ p.K →
          p.a = dgzSeq (dgzLambda d Q) p.K → ∀ j : ℕ, 2 ≤ j → p.a j ≤ p.n → ∀ u u' : Zd d,
            P {ω | ¬ NiceBox p (fun q z => H q z ω) j u} ≤
              ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (-(p.K * p.a j : ℝ))) +
                ENNReal.ofReal ((2 : ℝ) ^ (2 * d * dgzLambda d Q * p.a (j - 1))) *
                  P {ω | ¬ NiceBox p (fun q z => H q z ω) (j - 1) u'} ^ 2 +
                ENNReal.ofReal ((2 : ℝ) ^ ((d - β) * dgzLambda d Q * p.a (j - 1))) *
                  P {ω | ¬ NiceBox p (fun q z => H q z ω) (j - 1) u'}) := by
  have hκ := h.kernel
  have hρ0 : 0 < ρ := hκ.radius_pos hρ
  have hα := dgzAlpha_pos h.subcritical
  have hlam : 0 < dgzLambda d Q := dgzLambda_pos hα
  have hlam4 : dgzLambda d Q ≤ 1 / 4 := dgzLambda_le_quarter hα
  have hR1 : 1 ≤ R := by exact_mod_cast (show (1 : ℝ) ≤ R by linarith)
  set lam := dgzLambda d Q with hlamdef
  set C : ℝ := 1 + 16 ^ d + 4 ^ d * (2 * R) ^ d with hC
  have hC1 : 1 ≤ C := by rw [hC]; have : (0 : ℝ) ≤ 16 ^ d + 4 ^ d * (2 * R) ^ d := by positivity
                         linarith
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨θ₀, hθ₀, h56⟩ := lemma56 h hβd hβQ hR1
  refine ⟨C, by linarith, θ₀, hθ₀, fun θ hθ hθθ₀ => ?_⟩
  obtain ⟨K₁, hK₁⟩ := h56 θ hθ hθθ₀
  obtain ⟨K₂, hK₂⟩ := prob_not_niceOscCond_le (d := d) hκ hlam.le hlam4
  obtain ⟨K₃, hK₃⟩ := BadBox.exists_le_two_rpow (2 * ρ + R + 4) hlam
  refine ⟨max (max K₁ K₂) (max K₃ 2),
    fun Ω _ P W H hH p hpξ hpQ hpθ hpR hK ha j hj hjn u u' => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
  rw [show j + 2 - 1 = j + 1 from rfl]
  have hK1' : K₁ ≤ p.K := (le_max_left _ _).trans ((le_max_left _ _).trans hK)
  have hK2' : K₂ ≤ p.K := (le_max_right _ _).trans ((le_max_left _ _).trans hK)
  have hK3' : K₃ ≤ p.K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have hK2 : 2 ≤ p.K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  have hK1 : 1 ≤ p.K := by omega
  have hmono : Monotone p.a := by rw [ha]; exact dgzSeq_monotone hlam.le hK1
  have hRp : 2 * ρ + 10 ≤ (p.R : ℝ) := by rw [hpR]; exact hR
  have hN4 : p.K ^ 4 ≤ p.a (j + 1) := by rw [ha]; exact pow_le_dgzSeq hlam.le hK1 (by omega)
  have hsS : superScale (p.a (j + 1)) ≤ p.a (j + 1) := by
    refine superScale_le_self ?_
    have : 2 ^ 4 ≤ p.K ^ 4 := Nat.pow_le_pow_left hK2 4
    omega
  have hgap : ∀ i, 2 ≤ i → i ≤ j + 2 → (2 * ρ + p.R + 4) * p.s (i - 1) ≤ p.s i :=
    dgz_gap_of_le p hlam.le hK1 ha (by rw [hpR]; exact hK₃ p.K hK3') hjn
  have hA := hK₂ Ω P W H hH p hK2' ha (j + 2) le_add_self hjn u
  have hCw : ∀ w : Zd d, P {ω | ¬ NiceCEvent p (fun q z => H q z ω) (j + 2) u w} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(β * lam * p.a (j + 1)))) := fun w =>
    hK₁ Ω P W H hH p hpξ hpQ hpθ hpR hK1' ha (j + 2) le_add_self hjn u w
  have key := BadBox.prob_bad_add_two_le hκ hH hρ p hmono hRp hjn hsS hgap u u' hA hCw
  refine key.trans ?_
  -- the coefficients
  set N : ℕ := p.a (j + 1) with hNdef
  set A : ℕ := p.a (j + 2) with hAdef
  have hNA : N ≤ A := hmono (Nat.le_succ _)
  have hup : (A : ℝ) ≤ (1 + lam) * N + 1 := by
    have h1 := dgzSeq_succ_le (K := p.K) hlam.le (i := j + 1) (by omega)
    rw [← ha] at h1
    exact h1
  have hS := BadBox.card_subBoxes_le (d := d) hNA hup
  set S : ℕ := (2 * 2 ^ (A - N) - 1) ^ d with hSdef
  set x : ℝ := (2 : ℝ) ^ ((d : ℝ) * lam * N) with hx
  have hx0 : 0 ≤ x := by positivity
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hcR : ((((2 * p.R - 1) ^ d : ℕ)) : ℝ) ≤ (2 * R) ^ d := by
    rw [hpR]
    have : (2 * R - 1) ^ d ≤ (2 * R) ^ d := Nat.pow_le_pow_left (Nat.sub_le _ _) d
    exact_mod_cast this
  rw [mul_add, mul_add]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- (a′)
    calc ENNReal.ofReal (Real.exp (-(p.K * A : ℝ))) =
          1 * ENNReal.ofReal (Real.exp (-(p.K * A : ℝ))) := (one_mul _).symm
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (Real.exp (-(p.K * A : ℝ))) := by
          refine mul_le_mul' ?_ le_rfl
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hC1
  · -- `ℬ₁`
    rw [← mul_assoc, ← ENNReal.ofReal_mul hC0]
    refine mul_le_mul' ?_ le_rfl
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : (2 : ℝ) ^ (2 * d * lam * N) = x * x := by
      rw [hx, ← Real.rpow_add two_pos]
      congr 1
      ring
    rw [e]
    push_cast
    have h16 : (4 : ℝ) ^ d * 4 ^ d ≤ C := by
      rw [hC, ← mul_pow]
      norm_num
      have : (0 : ℝ) ≤ 4 ^ d * (2 * R) ^ d := by positivity
      linarith
    calc (S : ℝ) * S ≤ (4 ^ d * x) * (4 ^ d * x) := mul_le_mul hS hS hS0 (by positivity)
      _ = (4 ^ d * 4 ^ d) * (x * x) := by ring
      _ ≤ C * (x * x) := mul_le_mul_of_nonneg_right h16 (by positivity)
  · -- `ℬ₂`
    have e : (S : ℝ≥0∞) * (ENNReal.ofReal ((2 : ℝ) ^ (-(β * lam * N))) *
        ((((2 * p.R - 1) ^ d : ℕ) : ℝ≥0∞) * P {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 1) u'})) =
        ENNReal.ofReal ((S : ℝ) * (((2 * p.R - 1) ^ d : ℕ) : ℝ) * (2 : ℝ) ^ (-(β * lam * N))) *
          P {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 1) u'} := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
      ring
    rw [e, ← mul_assoc, ← ENNReal.ofReal_mul hC0]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have e2 : (2 : ℝ) ^ (((d : ℝ) - β) * lam * N) = x * (2 : ℝ) ^ (-(β * lam * N)) := by
      rw [hx, ← Real.rpow_add two_pos]
      congr 1
      ring
    rw [e2]
    have hy0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(β * lam * N)) := by positivity
    have h4 : (4 : ℝ) ^ d * (2 * R) ^ d ≤ C := by
      rw [hC]
      have : (0 : ℝ) ≤ 16 ^ d := by positivity
      linarith
    calc (S : ℝ) * (((2 * p.R - 1) ^ d : ℕ) : ℝ) * (2 : ℝ) ^ (-(β * lam * N))
        ≤ (4 ^ d * x) * (2 * R) ^ d * (2 : ℝ) ^ (-(β * lam * N)) := by gcongr
      _ = (4 ^ d * (2 * R) ^ d) * (x * (2 : ℝ) ^ (-(β * lam * N))) := by ring
      _ ≤ C * (x * (2 : ℝ) ^ (-(β * lam * N))) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)

/-! ## Lemma 5.8 -/

/-- **DGZ Lemma 5.8** (target `q_le`; MA7 D-5.5–5.9; blueprint `r2:lem:58`): for `R ≥ 2ρ + 10`
(`ρ` a support radius of `κ`) there is `θ₀ > 0` such that for every `θ ∈ (0, θ₀]` there is `K₀` such
that for every `K ≥ K₀` and `ε > 0` there is `L₀` with `q_j ≤ 2^{-α a_j}` for every dyadic
realization, DGZ's parameters with these `θ, K, ε, R` and `L ≥ L₀`, all `n, k`, `1 ≤ j` with
`a_j ≤ n` and all boxes. -/
theorem q_le {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {R : ℕ} (hR : 2 * ρ + 10 ≤ (R : ℝ)) :
    ∃ θ₀ > 0, ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ ε : ℝ, 0 < ε →
      ∃ L₀ : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.ε = ε → p.R = R → p.K = K →
          L₀ ≤ p.L → p.a = dgzSeq (dgzLambda d Q) K → ∀ j : ℕ, 1 ≤ j → p.a j ≤ p.n →
            ∀ u : Zd d, P {ω | ¬ NiceBox p (fun q z => H q z ω) j u} ≤
              ENNReal.ofReal ((2 : ℝ) ^ (-(dgzAlpha d Q * p.a j))) := by
  have hα := dgzAlpha_pos h.subcritical
  have hlam : 0 < dgzLambda d Q := dgzLambda_pos hα
  have hg : (2 * d + dgzAlpha d Q) * dgzLambda d Q < dgzAlpha d Q := by
    have h1 := dgzLambda_lt_alpha_div hα
    rw [lt_div_iff₀ (by positivity)] at h1
    linarith
  set α := dgzAlpha d Q with hαdef
  set lam := dgzLambda d Q with hlamdef
  set β : ℝ := d + 3 * α / 2 with hβ
  have hβd : (d : ℝ) < β := by rw [hβ]; linarith
  have hβQ : β < Q ^ 2 / 2 := by
    have e : α = Q ^ 2 / 4 - d / 2 := rfl
    rw [hβ]
    linarith
  obtain ⟨C, hC, θ₀, hθ₀, h57⟩ := lemma57 h hρ hR hβd hβQ
  refine ⟨θ₀, hθ₀, fun θ hθ hθθ₀ => ?_⟩
  obtain ⟨K₁, hK₁⟩ := h57 θ hθ hθθ₀
  obtain ⟨K₂, hK₂⟩ := BadBox.q_step_arith d hα hlam hg hβ hC
  refine ⟨max K₁ (max K₂ 1), fun K hK ε hε => ?_⟩
  obtain ⟨L₀, hL₀⟩ := q1_le h hε (K ^ 4) (η := (2 : ℝ) ^ (-(α * ((K ^ 4 : ℕ) : ℝ))))
    (by positivity)
  refine ⟨L₀, fun Ω _ P W H hH p hpξ hpQ hpθ hpε hpR hpK hL ha j hj hjn u => ?_⟩
  have hK1 : 1 ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  have hK₁' : K₁ ≤ p.K := by rw [hpK]; exact (le_max_left _ _).trans hK
  have hK₂' : K₂ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have ha' : p.a = dgzSeq (dgzLambda d Q) p.K := by rw [hpK]; exact ha
  have hmono : Monotone p.a := by rw [ha]; exact dgzSeq_monotone hlam.le hK1
  induction j, hj using Nat.le_induction generalizing u with
  | base =>
      have ha0 : p.a 0 = 0 := by rw [ha]; rfl
      have ha1 : p.a 1 = K ^ 4 := by rw [ha]; rfl
      refine (hL₀ Ω P W H hH p hpξ hpQ hpε ha0 ha1.le hL u).trans (le_of_eq ?_)
      rw [ha1]
  | succ j hj ih =>
      have hjn' : p.a j ≤ p.n := (hmono (Nat.le_succ j)).trans hjn
      have hstep := hK₁ Ω P W H hH p hpξ hpQ hpθ hpR hK₁' ha' (j + 1) (by omega) hjn u 0
      rw [Nat.add_sub_cancel, hpK] at hstep
      have hq := ih hjn' 0
      refine hstep.trans ?_
      have hN4 : K ^ 4 ≤ p.a j := by rw [ha]; exact pow_le_dgzSeq hlam.le hK1 hj
      have hNA : p.a j ≤ p.a (j + 1) := hmono (Nat.le_succ j)
      have hA : (p.a (j + 1) : ℝ) ≤ (1 + lam) * p.a j + 1 := by
        rw [ha]
        exact dgzSeq_succ_le hlam.le hj
      have harith := hK₂ K (p.a j) (p.a (j + 1)) hK₂' hN4 hNA hA
      set y : ℝ := (2 : ℝ) ^ (-(α * p.a j)) with hy
      have hy0 : 0 ≤ y := by positivity
      have hC0 : 0 ≤ C := hC.le
      have he0 : 0 ≤ Real.exp (-(K * p.a (j + 1) : ℝ)) := (Real.exp_pos _).le
      have hx₂0 : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * d * lam * p.a j) := by positivity
      have hx₃0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((d - β) * lam * p.a j) := by positivity
      calc ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (-(K * p.a (j + 1) : ℝ))) +
            ENNReal.ofReal ((2 : ℝ) ^ (2 * d * lam * p.a j)) *
              P {ω | ¬ NiceBox p (fun q z => H q z ω) j 0} ^ 2 +
            ENNReal.ofReal ((2 : ℝ) ^ ((d - β) * lam * p.a j)) *
              P {ω | ¬ NiceBox p (fun q z => H q z ω) j 0})
          ≤ ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (-(K * p.a (j + 1) : ℝ))) +
            ENNReal.ofReal ((2 : ℝ) ^ (2 * d * lam * p.a j)) * ENNReal.ofReal y ^ 2 +
            ENNReal.ofReal ((2 : ℝ) ^ ((d - β) * lam * p.a j)) * ENNReal.ofReal y) := by
            gcongr
        _ = ENNReal.ofReal (C * (Real.exp (-(K * p.a (j + 1) : ℝ)) +
            (2 : ℝ) ^ (2 * d * lam * p.a j) * y ^ 2 +
            (2 : ℝ) ^ ((d - β) * lam * p.a j) * y)) := by
            rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add he0 (by positivity), ENNReal.ofReal_mul hx₂0,
              ENNReal.ofReal_mul hx₃0, ENNReal.ofReal_pow hy0]
        _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(α * p.a (j + 1)))) := ENNReal.ofReal_le_ofReal harith

end DGZ

end HigherDimLQGMetric
