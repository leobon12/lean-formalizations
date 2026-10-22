import HigherDimLQGMetric.DGZ.FieldTails

/-!
# Field tails II: sub-scale oscillations and small boxes (packet L3b2; MA7 D-OSC, Lemma 2.3(5))

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 2.3 (2) (gradient tails) and (5)
(supremum on a small box); planning audit `planning/audits/MA7-ref2-sections-4-6.md`, gaps G9 and
G19, §2.4, Details (a) D-OSC ("Sub-scale oscillation"; the conditions (1′), (a′), `𝒥₂′`) and the
§5 row L3b2.

**Multi-scale oscillations (D-OSC, replacing gradients, G9).** For a continuous version `X` of
`H_{a,b}` (`0 < a`) with `‖k_z - k_w‖² ≤ L ‖z - w‖² / a²`, a point `g`, `r ≥ 0` and `v ≥ 0`:
`osc_{B̄_{ra}(g)} X ≤ r (2 c + 2v)` outside probability `2 exp(-v²/(2 d L))`, with
`c = blockConst d L √d` (`measure_osc_cbox_gt_le`; HigherDimLFPP's `Osc.box_osc_tail` with
`ρ = r`, `u = r v`, using that `blockConst d L (√d r) = r · blockConst d L √d` is linear in `r`).
Every condition (1′), (a′), `𝒥₂′` of D-OSC bounds the oscillation of a band on finitely many boxes
`B̄_{r_k a}(y_k)` (`a` the smallest scale of the band) by `r_k T` with one slope `T` per condition
(`T = L/3` for (1′), `T = K√(a_{j-1})/8` for (a′), `T = K√(a_m)/8` for `𝒥₂′`). Hence the target
**`prob_multiscaleOsc_compl_le`**: there is `C > 0` (depending on `d`, `κ`) such that for every
finite family of boxes and every `T ≥ C`,
`P[∃ k, osc_{B̄_{r_k a}(y_k)} X > r_k T] ≤ #family · 2 exp(-(T - C)²/C)`.

**Small boxes (DGZ Lemma 2.3 (5), with G19).** On `B̄_{Ra}(g)` the field is its value at `g` plus
the block oscillation (HigherDimLFPP `Osc.block_tail` on the ball of radius `(√d R + 1) a`), so
(`exists_smallBox_gaussian_tail`) for `u, w ≥ 0`
`P[∃ z ∈ B̄_{Ra}(g), u + C + w < |X z|] ≤ 2 exp(-u²/(2 log(b/a))) + 2 exp(-w²/C)`, and with
`u ↦ u - u^{2/3}`, `w = u^{2/3} - C` the form of [2]: the target **`prob_smallBox_sup_le`**,
`P[sup_{B̄_{Ra}(g)} X > u] ≤ C exp(-(u - u^{2/3})²/(2 log(b/a))) + C exp(-u^{4/3}/C)` for all
`u ≥ 0` (and the same for `|X|` and for `inf X < -u`). G19 (boxes of radius `4R·2^{-n}` instead
of `2^{-n}`) is covered by the radius parameter `R`: no covering argument is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ### Deterministic helpers -/

/-- `blockConst d L (√d r) = r · blockConst d L √d` (the block constant is linear in the radius). -/
theorem blockConst_sqrt_mul (d : ℕ) (L r : ℝ) :
    Osc.blockConst d L (√(d : ℝ) * r) = r * Osc.blockConst d L √(d : ℝ) := by
  unfold Osc.blockConst
  ring

/-- The closed box of radius `0` is a point. -/
theorem eq_of_mem_cbox_zero {c z : Rd d} (hz : z ∈ cbox c 0) : z = c := by
  ext i
  have h : |z i - c i| ≤ 0 := hz i
  have h2 : z i - c i = 0 := abs_nonpos_iff.1 h
  linarith

/-- In dimension `0` all points are equal. -/
theorem eq_of_dim_eq_zero (hd : d = 0) (z w : Rd d) : z = w := by
  ext i
  exact absurd i.2 (by omega)

/-! ### Sub-scale oscillation of a band (MA7 D-OSC) -/

section Osc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}
  {a b : ℝ} {X : Rd d → Ω → ℝ}

/-- **Sub-scale oscillation** (MA7 D-OSC, first paragraph): for a continuous version `X` of
`H_{a,b}` (`0 < a`) with `‖k_z - k_w‖² ≤ L ‖z - w‖² / a²` (`L ≥ 0`), a point `g`, `r ≥ 0` and
`v ≥ 0`, `osc_{B̄_{r a}(g)} X ≤ r (2 c + 2 v)` with `c = blockConst d L √d`, outside an event of
probability at most `2 exp(-v² / (2 d L))`. -/
theorem measure_osc_cbox_gt_le (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hX : IsBandVersion P W κ a b X) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z w : Rd d, ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    (g : Rd d) {r : ℝ} (hr : 0 ≤ r) {v : ℝ} (hv : 0 ≤ v) :
    P {ω | ∃ z ∈ cbox g (r * a), ∃ w ∈ cbox g (r * a),
        r * (2 * Osc.blockConst d L √(d : ℝ) + 2 * v) < |X z ω - X w ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-v ^ 2 / (2 * d * L))) := by
  rcases hr.eq_or_lt with hr0 | hr0
  · -- radius `0`: the box is a point and the event is empty
    subst hr0
    have hempty : {ω | ∃ z ∈ cbox g (0 * a), ∃ w ∈ cbox g (0 * a),
        0 * (2 * Osc.blockConst d L √(d : ℝ) + 2 * v) < |X z ω - X w ω|} = ∅ := by
      refine eq_empty_of_forall_notMem fun ω hω => ?_
      obtain ⟨z, hz, w, hw, hlt⟩ := hω
      rw [zero_mul] at hz hw
      rw [eq_of_mem_cbox_zero hz, eq_of_mem_cbox_zero hw, sub_self, abs_zero, zero_mul] at hlt
      exact lt_irrefl 0 hlt
    rw [hempty, measure_empty]
    exact zero_le
  · have h := Osc.box_osc_tail hW ha hX hL0 hL g (ρ := r) hr (u := r * v) (by positivity)
    have hthr : 2 * (Osc.blockConst d L (√(d : ℝ) * r) + r * v) =
        r * (2 * Osc.blockConst d L √(d : ℝ) + 2 * v) := by
      rw [blockConst_sqrt_mul]
      ring
    have hexp : -(r * v) ^ 2 / (2 * ((√(d : ℝ) * r) ^ 2 * L)) = -v ^ 2 / (2 * d * L) := by
      have e1 : (√(d : ℝ) * r) ^ 2 = d * r ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      have e2 : -(r * v) ^ 2 = r ^ 2 * -v ^ 2 := by ring
      have e3 : 2 * (d * r ^ 2 * L) = r ^ 2 * (2 * d * L) := by ring
      rw [e1, e2, e3, mul_div_mul_left _ _ (pow_ne_zero 2 hr0.ne')]
    rw [hthr, hexp] at h
    exact h

/-- **Sub-scale oscillation with one constant** (MA7 D-OSC): there is `C > 0`, depending only on
`d` and `κ`, such that for every continuous version `X` of a band `H_{a,b}` (`0 < a`), every box
`B̄_{r a}(g)` (`r ≥ 0`) and every slope `T ≥ C`,
`P[osc_{B̄_{r a}(g)} X > r T] ≤ 2 exp(-(T - C)²/C)`. -/
theorem exists_osc_cbox_tail {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {a b : ℝ}, 0 < a → ∀ {X : Rd d → Ω → ℝ},
      IsBandVersion P W κ a b X → ∀ (g : Rd d) {r : ℝ}, 0 ≤ r → ∀ {T : ℝ}, C ≤ T →
        P {ω | ∃ z ∈ cbox g (r * a), ∃ w ∈ cbox g (r * a), r * T < |X z ω - X w ω|} ≤
          ENNReal.ofReal (2 * Real.exp (-(T - C) ^ 2 / C)) := by
  obtain ⟨L₀, hL₀0, hL₀⟩ := exists_norm_bandVec_sub_sq_le hκ
  set L : ℝ := L₀ + 1 with hLdef
  have hL0 : 0 < L := by rw [hLdef]; linarith
  have hL : ∀ a : ℝ, 0 < a → ∀ (b : ℝ) (z w : Rd d),
      ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2 :=
    fun a ha b z w => (hL₀ a ha b z w).trans (by gcongr; linarith)
  set B₁ : ℝ := Osc.blockConst d L √(d : ℝ) with hB₁
  have hB₁0 : 0 ≤ B₁ := Osc.blockConst_nonneg d (Real.sqrt_nonneg _)
  set C : ℝ := max (2 * B₁) (8 * d * L) + 1 with hCdef
  have hC1 : 2 * B₁ ≤ C - 1 := by
    have := le_max_left (2 * B₁) (8 * d * L)
    linarith
  have hC2 : 8 * d * L ≤ C - 1 := by
    have := le_max_right (2 * B₁) (8 * d * L)
    linarith
  have hC0 : 0 < C := by
    have : (0 : ℝ) ≤ 8 * d * L := by positivity
    linarith
  refine ⟨C, hC0, fun {Ω} _ {P} {W} hW {a b} ha {X} hX g {r} hr {T} hT => ?_⟩
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- dimension `0`: the event is empty
    have hempty : {ω | ∃ z ∈ cbox g (r * a), ∃ w ∈ cbox g (r * a),
        r * T < |X z ω - X w ω|} = ∅ := by
      refine eq_empty_of_forall_notMem fun ω hω => ?_
      obtain ⟨z, -, w, -, hlt⟩ := hω
      rw [eq_of_dim_eq_zero hd z w, sub_self, abs_zero] at hlt
      have : 0 ≤ r * T := mul_nonneg hr (by linarith)
      linarith
    rw [hempty, measure_empty]
    exact zero_le
  · set v : ℝ := (T - 2 * B₁) / 2 with hv
    have hv0 : 0 ≤ v := by rw [hv]; linarith
    have h := measure_osc_cbox_gt_le hW ha hX hL0.le (hL a ha b) g hr hv0
    have hT' : 2 * B₁ + 2 * v = T := by rw [hv]; ring
    rw [← hB₁, hT'] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hTC : 0 ≤ T - C := by linarith
    have hvT : (T - C) / 2 ≤ v := by rw [hv]; linarith
    have hsq : ((T - C) / 2) ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ (by linarith) hvT 2
    -- `(T - C)²/C ≤ v²/(2 d L)`
    have hden : 0 < 2 * (d : ℝ) * L := by positivity
    have key : (T - C) ^ 2 / C ≤ v ^ 2 / (2 * d * L) := by
      rw [div_le_div_iff₀ hC0 hden]
      have h8 : 2 * (d : ℝ) * L * 4 ≤ C := by linarith
      have hsq' : (T - C) ^ 2 ≤ 4 * v ^ 2 := by nlinarith
      nlinarith [sq_nonneg (T - C), sq_nonneg v]
    have e1 : -(T - C) ^ 2 / C = -((T - C) ^ 2 / C) := by ring
    have e2 : -v ^ 2 / (2 * d * L) = -(v ^ 2 / (2 * d * L)) := by ring
    rw [e1, e2]
    linarith

/-- **Multi-scale oscillation conditions** (MA7 D-OSC: the events (1′), (a′) and `𝒥₂′` replacing
the gradient conditions of DGZ Definition 5.3 (1), (a), (5.22), Prop 5.10 (A) and Lemma 5.12; §5 row
L3b2): there is `C > 0`, depending only on `d` and `κ`, such that for every continuous version `X`
of a band `H_{a,b}` (`0 < a`, `a` its smallest scale), every finite family of boxes
`B̄_{r_k a}(y_k)` (`r_k ≥ 0`) and every slope `T ≥ C`, the probability that some box has
`osc_{B̄_{r_k a}(y_k)} X > r_k T` is at most `#family · 2 exp(-(T - C)²/C)`. -/
theorem prob_multiscaleOsc_compl_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {a b : ℝ}, 0 < a → ∀ {X : Rd d → Ω → ℝ},
      IsBandVersion P W κ a b X → ∀ {ι : Type*} (s : Finset ι) (y : ι → Rd d) (r : ι → ℝ),
      (∀ k ∈ s, 0 ≤ r k) → ∀ {T : ℝ}, C ≤ T →
        P {ω | ∃ k ∈ s, ∃ z ∈ cbox (y k) (r k * a), ∃ w ∈ cbox (y k) (r k * a),
            r k * T < |X z ω - X w ω|} ≤
          ENNReal.ofReal (s.card * (2 * Real.exp (-(T - C) ^ 2 / C))) := by
  obtain ⟨C, hC0, h1⟩ := exists_osc_cbox_tail (d := d) hκ
  refine ⟨C, hC0, fun {Ω} _ {P} {W} hW {a b} ha {X} hX {ι} s y r hr {T} hT => ?_⟩
  set q : ℝ := 2 * Real.exp (-(T - C) ^ 2 / C) with hq
  have hq0 : 0 ≤ q := by positivity
  have hset : {ω | ∃ k ∈ s, ∃ z ∈ cbox (y k) (r k * a), ∃ w ∈ cbox (y k) (r k * a),
      r k * T < |X z ω - X w ω|} = ⋃ k ∈ s, {ω | ∃ z ∈ cbox (y k) (r k * a),
        ∃ w ∈ cbox (y k) (r k * a), r k * T < |X z ω - X w ω|} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [hset]
  calc P (⋃ k ∈ s, {ω | ∃ z ∈ cbox (y k) (r k * a), ∃ w ∈ cbox (y k) (r k * a),
        r k * T < |X z ω - X w ω|})
      ≤ ∑ k ∈ s, P {ω | ∃ z ∈ cbox (y k) (r k * a), ∃ w ∈ cbox (y k) (r k * a),
          r k * T < |X z ω - X w ω|} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ s, ENNReal.ofReal q :=
        Finset.sum_le_sum fun k hk => h1 hW ha hX (y k) (hr k hk) hT
    _ = ENNReal.ofReal (s.card * q) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

end Osc

/-! ### Small boxes (DGZ Lemma 2.3 (5)) -/

section SmallBox

/-- **Small-box supremum, Gaussian form** (DGZ Lemma 2.3 (5), proof; MA7 §2.4 "point variance +
`block_tail`", G19): for every `R ≥ 0` there is `C > 0`, depending only on `d`, `κ` and `R`, such
that for every continuous version `X` of `H_{a,b}` (`0 < a ≤ b`), every point `g` and `u, w ≥ 0`,
`P[∃ z ∈ B̄_{R a}(g), u + C + w < |X z|] ≤ 2 exp(-u²/(2 log(b/a))) + 2 exp(-w²/C)`. -/
theorem exists_smallBox_gaussian_tail {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {R : ℝ}
    (hR : 0 ≤ R) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ {X : Rd d → Ω → ℝ},
      IsBandVersion P W κ a b X → ∀ (g : Rd d) {u w : ℝ}, 0 ≤ u → 0 ≤ w →
        P {ω | ∃ z ∈ cbox g (R * a), u + C + w < |X z ω|} ≤
          ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * Real.log (b / a))) +
            2 * Real.exp (-w ^ 2 / C)) := by
  obtain ⟨L₀, hL₀0, hL₀⟩ := exists_norm_bandVec_sub_sq_le hκ
  set L : ℝ := L₀ + 1 with hLdef
  have hL0 : 0 < L := by rw [hLdef]; linarith
  have hL : ∀ a : ℝ, 0 < a → ∀ (b : ℝ) (z w : Rd d),
      ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2 :=
    fun a ha b z w => (hL₀ a ha b z w).trans (by gcongr; linarith)
  set ρ : ℝ := √(d : ℝ) * R + 1 with hρ
  have hρ0 : 0 < ρ := by positivity
  set B : ℝ := Osc.blockConst d L ρ with hB
  have hB0 : 0 ≤ B := Osc.blockConst_nonneg d hρ0.le
  set C : ℝ := max B (2 * (ρ ^ 2 * L)) + 1 with hCdef
  have hCB : B ≤ C := by have := le_max_left B (2 * (ρ ^ 2 * L)); linarith
  have hCρ : 2 * (ρ ^ 2 * L) ≤ C := by have := le_max_right B (2 * (ρ ^ 2 * L)); linarith
  have hC0 : 0 < C := by
    have := le_max_left B (2 * (ρ ^ 2 * L))
    linarith
  refine ⟨C, hC0, fun {Ω} _ {P} {W} hW {a b} ha hab {X} hX g {u w} hu hw => ?_⟩
  have hsub : {ω | ∃ z ∈ cbox g (R * a), u + C + w < |X z ω|} ⊆
      {ω | u ≤ |X g ω|} ∪ {ω | ∃ z ∈ closedBall g (ρ * a), B + w < |X z ω - X g ω|} := by
    intro ω hω
    obtain ⟨z, hz, hlt⟩ := hω
    by_cases h1 : u ≤ |X g ω|
    · exact Or.inl h1
    · refine Or.inr ⟨z, ?_, ?_⟩
      · rw [mem_closedBall, dist_eq_norm]
        have h := Osc.norm_sub_le_of_mem_box (mul_nonneg hR ha.le) hz
        have h2 : √(d : ℝ) * (R * a) ≤ ρ * a := by
          rw [hρ]
          nlinarith
        linarith
      · have htri : |X z ω| ≤ |X g ω| + |X z ω - X g ω| := by
          have := abs_add_le (X g ω) (X z ω - X g ω)
          rwa [add_sub_cancel] at this
        push Not at h1
        linarith
  have hp1 := measure_abs_ge_le_of_isBandVersion hκ hW ha hab hX g hu
  have hp2 := Osc.block_tail hW ha hX hL0.le (hL a ha b) g hρ0.le hw
  have hp2' : P {ω | ∃ z ∈ closedBall g (ρ * a), B + w < |X z ω - X g ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-w ^ 2 / C)) := by
    refine hp2.trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have hden : 0 < 2 * (ρ ^ 2 * L) := by positivity
    have : w ^ 2 / C ≤ w ^ 2 / (2 * (ρ ^ 2 * L)) :=
      div_le_div_of_nonneg_left (sq_nonneg w) hden hCρ
    have e1 : -w ^ 2 / (2 * (ρ ^ 2 * L)) = -(w ^ 2 / (2 * (ρ ^ 2 * L))) := by ring
    have e2 : -w ^ 2 / C = -(w ^ 2 / C) := by ring
    rw [e1, e2]
    linarith
  calc P {ω | ∃ z ∈ cbox g (R * a), u + C + w < |X z ω|}
      ≤ P ({ω | u ≤ |X g ω|} ∪ {ω | ∃ z ∈ closedBall g (ρ * a), B + w < |X z ω - X g ω|}) :=
        measure_mono hsub
    _ ≤ P {ω | u ≤ |X g ω|} + P {ω | ∃ z ∈ closedBall g (ρ * a), B + w < |X z ω - X g ω|} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * Real.log (b / a)))) +
          ENNReal.ofReal (2 * Real.exp (-w ^ 2 / C)) := add_le_add hp1 hp2'
    _ = ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * Real.log (b / a))) +
          2 * Real.exp (-w ^ 2 / C)) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

/-- `C e^{-x/C} ≥ 1` for `0 ≤ x` and `x + 1 ≤ C`. -/
theorem one_le_mul_exp_neg_div {C x : ℝ} (hx0 : 0 ≤ x) (hx : x + 1 ≤ C) :
    1 ≤ C * Real.exp (-x / C) := by
  have hC0 : 0 < C := by linarith
  have h1 := Real.add_one_le_exp (-x / C)
  have h2 : C * (-x / C + 1) = C - x := by field_simp; ring
  have h3 := mul_le_mul_of_nonneg_left h1 hC0.le
  linarith

/-- **DGZ Lemma 2.3 (5), two-sided form**, for boxes of radius `R a` (G19): for every `R ≥ 0`
there is `C > 0`, depending only on `d`, `κ` and `R`, such that for every continuous version `X` of
`H_{a,b}` (`0 < a ≤ b`), every point `g` and every `u ≥ 0`,
`P[∃ z ∈ B̄_{R a}(g), u < |X z|] ≤ C exp(-(u - u^{2/3})²/(2 log(b/a))) + C exp(-u^{4/3}/C)`. -/
theorem prob_smallBox_abs_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ {X : Rd d → Ω → ℝ},
      IsBandVersion P W κ a b X → ∀ (g : Rd d) {u : ℝ}, 0 ≤ u →
        P {ω | ∃ z ∈ cbox g (R * a), u < |X z ω|} ≤
          ENNReal.ofReal (C * Real.exp (-(u - u ^ ((2 : ℝ) / 3)) ^ 2 / (2 * Real.log (b / a))) +
            C * Real.exp (-u ^ ((4 : ℝ) / 3) / C)) := by
  obtain ⟨C₀, hC₀, htail⟩ := exists_smallBox_gaussian_tail (d := d) hκ hR
  set x₀ : ℝ := max 1 (4 * C₀ ^ 2) with hx₀
  set C : ℝ := max (max 2 (4 * C₀)) (x₀ + 1) with hCdef
  have hC2 : 2 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC4 : 4 * C₀ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCx : x₀ + 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC0, fun {Ω} _ {P} {W} hW {a b} ha hab {X} hX g {u} hu => ?_⟩
  have := hW.isProbabilityMeasure
  set p : ℝ := u ^ ((2 : ℝ) / 3) with hp
  have hp0 : 0 ≤ p := Real.rpow_nonneg hu _
  have hp43 : u ^ ((4 : ℝ) / 3) = p ^ 2 := by
    rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul hu]
    norm_num
  have hT1 : 0 ≤ C * Real.exp (-(u - p) ^ 2 / (2 * Real.log (b / a))) := by positivity
  by_cases hbig : 1 ≤ u ∧ 2 * C₀ ≤ p
  · obtain ⟨hu1, hpC⟩ := hbig
    have hpu : p ≤ u := by
      have h := Real.rpow_le_rpow_of_exponent_le hu1 (show (2 : ℝ) / 3 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    have hu' : 0 ≤ u - p := by linarith
    have hw : 0 ≤ p - C₀ := by linarith
    have h := htail hW ha hab hX g hu' hw
    have hthr : u - p + C₀ + (p - C₀) = u := by ring
    rw [hthr] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hp43]
    have hA : 2 * Real.exp (-(u - p) ^ 2 / (2 * Real.log (b / a))) ≤
        C * Real.exp (-(u - p) ^ 2 / (2 * Real.log (b / a))) :=
      mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le
    have hB : 2 * Real.exp (-(p - C₀) ^ 2 / C₀) ≤ C * Real.exp (-p ^ 2 / C) := by
      refine mul_le_mul hC2 (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hC0.le
      have hsq : p ^ 2 / 4 ≤ (p - C₀) ^ 2 := by nlinarith
      -- `p²/C ≤ p²/(4 C₀) ≤ (p - C₀)²/C₀`
      have h1 : p ^ 2 / C ≤ p ^ 2 / (4 * C₀) :=
        div_le_div_of_nonneg_left (sq_nonneg p) (by positivity) hC4
      have h2 : p ^ 2 / (4 * C₀) ≤ (p - C₀) ^ 2 / C₀ := by
        rw [div_le_div_iff₀ (by positivity) hC₀]
        nlinarith
      have e1 : -(p - C₀) ^ 2 / C₀ = -((p - C₀) ^ 2 / C₀) := by ring
      have e2 : -p ^ 2 / C = -(p ^ 2 / C) := by ring
      rw [e1, e2]
      linarith
    linarith
  · -- the second term is at least `1`
    have hx : u ^ ((4 : ℝ) / 3) ≤ x₀ := by
      rw [not_and_or] at hbig
      rcases hbig with h | h
      · push Not at h
        exact (Real.rpow_le_one hu h.le (by norm_num)).trans (le_max_left _ _)
      · push Not at h
        rw [hp43]
        have : p ^ 2 ≤ 4 * C₀ ^ 2 := by nlinarith
        exact this.trans (le_max_right _ _)
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 ≤ C * Real.exp (-x₀ / C) :=
      one_le_mul_exp_neg_div (zero_le_one.trans (le_max_left _ _)) hCx
    have h2 : C * Real.exp (-x₀ / C) ≤ C * Real.exp (-u ^ ((4 : ℝ) / 3) / C) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0.le
      exact div_le_div_of_nonneg_right (by linarith) hC0.le
    linarith

/-- **DGZ Lemma 2.3 (5)** (`prob_smallBox_sup_le`, MA7 §5 row L3b2), for boxes of radius `R a`
(G19): for every `R ≥ 0` there is `C > 0`, depending only on `d`, `κ` and `R`, such that for every
continuous version `X` of `H_{a,b}` (`0 < a ≤ b`; for `h_n`, `a = 2^{-n}`, `b = 1`), every point `g`
and every `u ≥ 0`,
`P[sup_{z ∈ B̄_{R a}(g)} X z > u] ≤ C exp(-(u - u^{2/3})²/(2 log(b/a))) + C exp(-u^{4/3}/C)`. -/
theorem prob_smallBox_sup_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ {X : Rd d → Ω → ℝ},
      IsBandVersion P W κ a b X → ∀ (g : Rd d) {u : ℝ}, 0 ≤ u →
        P {ω | ∃ z ∈ cbox g (R * a), u < X z ω} ≤
          ENNReal.ofReal (C * Real.exp (-(u - u ^ ((2 : ℝ) / 3)) ^ 2 / (2 * Real.log (b / a))) +
            C * Real.exp (-u ^ ((4 : ℝ) / 3) / C)) := by
  obtain ⟨C, hC0, h⟩ := prob_smallBox_abs_le (d := d) hκ hR
  refine ⟨C, hC0, fun {Ω} _ {P} {W} hW {a b} ha hab {X} hX g {u} hu => ?_⟩
  refine (measure_mono fun ω hω => ?_).trans (h hW ha hab hX g hu)
  obtain ⟨z, hz, hlt⟩ := hω
  exact ⟨z, hz, hlt.trans_le (le_abs_self _)⟩

/-- **DGZ Lemma 2.3 (5) for the infimum** (used in DGZ Lemma 5.14, MA7 D-5.14): same constant
as `prob_smallBox_abs_le`, for the event `inf_{B̄_{R a}(g)} X < -u`. -/
theorem prob_smallBox_inf_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ {X : Rd d → Ω → ℝ},
      IsBandVersion P W κ a b X → ∀ (g : Rd d) {u : ℝ}, 0 ≤ u →
        P {ω | ∃ z ∈ cbox g (R * a), X z ω < -u} ≤
          ENNReal.ofReal (C * Real.exp (-(u - u ^ ((2 : ℝ) / 3)) ^ 2 / (2 * Real.log (b / a))) +
            C * Real.exp (-u ^ ((4 : ℝ) / 3) / C)) := by
  obtain ⟨C, hC0, h⟩ := prob_smallBox_abs_le (d := d) hκ hR
  refine ⟨C, hC0, fun {Ω} _ {P} {W} hW {a b} ha hab {X} hX g {u} hu => ?_⟩
  refine (measure_mono fun ω hω => ?_).trans (h hW ha hab hX g hu)
  obtain ⟨z, hz, hlt⟩ := hω
  exact ⟨z, hz, (lt_neg.1 hlt).trans_le (neg_le_abs _)⟩

end SmallBox

end HigherDimLQGMetric.DGZ
