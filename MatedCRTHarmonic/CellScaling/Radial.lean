import Mathlib
import QuantumZipper.Proofs.Probability.BMLLN
import MatedCRTHarmonic.CellScaling.ConeDefs

/-!
# the cone-radius asymptotic: `log R_{2^k} / (k log 2) → a_γ` almost surely (pathwise proof)

Paper: the cone-radius asymptotic, (`a_γ = 1/(γ(Q − γ)) = 1/(2 − γ²/2)`). We follow the
pathwise proof of the cone's radial last-passage estimates, which needs
neither [17, Lemma 2.6] nor Borel–Cantelli: for `s > 0` the cone's radial path is `X(s) = c(ℓ + s)`, where
`c(u) = B'_u + (Q − γ)u` and `ℓ` is the last zero of `c` (DMS Rem 4.4); `log R_b` is the last passage time of `X` at
`γ⁻¹ log b`; the Brownian law of large numbers `B'_u / u → 0` (QuantumZipper `BMLLN.ae_tendsto_div_atTop`, Le Gall
Ex. 2.25) gives `c(u)/u → Q − γ`, hence `log R_b / log b → 1/(γ(Q − γ))`.

Main results:
* `CellScaling.tendsto_lastLevel_div` (deterministic): if `c` is continuous, `c 0 = 0`, `c u / u → μ > 0`, and
  `X s = c(ℓ + s)` for `s > 0`, then `sup {s | X s = y} / y → μ⁻¹` as `y → ∞`.
* `CellScaling.tendsto_logb_coneScale` (deterministic, the cone).
* `CellScaling.ae_tendsto_logb_coneScale` (**the cone-radius asymptotic**) and `CellScaling.ae_coneScale_one` (`R_1 = 1`, the
  circle-average normalization).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

/-! ### Deterministic last-passage asymptotics -/

/-- Standing hypotheses on the drifted path `c(u) = B'_u + μu` used for the last-passage asymptotics. -/
structure GoodDrift (c : ℝ → ℝ) (μ : ℝ) : Prop where
  cont : Continuous c
  zero : c 0 = 0
  pos : 0 < μ
  lim : Tendsto (fun u => c u / u) atTop (𝓝 μ)

namespace GoodDrift

variable {c : ℝ → ℝ} {μ : ℝ}

theorem tendsto_atTop (h : GoodDrift c μ) : Tendsto c atTop atTop := by
  have hmul : Tendsto (fun u => c u / u * u) atTop atTop :=
    Filter.Tendsto.pos_mul_atTop h.pos h.lim tendsto_id
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  field_simp

/-- The zero set `{s ≥ 0 | c s = 0}` is bounded above. -/
theorem bddAbove_zeroSet (h : GoodDrift c μ) : BddAbove {s : ℝ | 0 ≤ s ∧ c s = 0} := by
  obtain ⟨U, hU⟩ := (tendsto_atTop_atTop.1 h.tendsto_atTop) 1
  refine ⟨U, fun s hs => ?_⟩
  by_contra hlt
  have := hU s (le_of_lt (not_le.1 hlt))
  rw [hs.2] at this
  norm_num at this

theorem lastZeroR_mem (h : GoodDrift c μ) :
    0 ≤ lastZeroR c ∧ c (lastZeroR c) = 0 := by
  have hne : ({s : ℝ | 0 ≤ s ∧ c s = 0}).Nonempty := ⟨0, le_rfl, h.zero⟩
  have hcl : IsClosed {s : ℝ | 0 ≤ s ∧ c s = 0} :=
    isClosed_Ici.inter (isClosed_singleton.preimage h.cont)
  exact hcl.csSup_mem hne h.bddAbove_zeroSet

theorem lastZeroR_nonneg (h : GoodDrift c μ) : 0 ≤ lastZeroR c := h.lastZeroR_mem.1

/-- Intermediate values: if `c a ≤ y` and `a ≤ b` with `y ≤ c b`, then `c` takes the value `y` on `[a, b]`. -/
theorem exists_eq_of_le (h : GoodDrift c μ) {a b y : ℝ} (hab : a ≤ b) (ha : c a ≤ y) (hb : y ≤ c b) :
    ∃ w ∈ Icc a b, c w = y :=
  intermediate_value_Icc hab h.cont.continuousOn ⟨ha, hb⟩

/-- After its last zero, `c` is positive. -/
theorem pos_of_lastZeroR_lt (h : GoodDrift c μ) {u : ℝ} (hu : lastZeroR c < u) : 0 < c u := by
  by_contra hle
  push Not at hle
  obtain ⟨V, hV⟩ := (tendsto_atTop_atTop.1 h.tendsto_atTop) 1
  obtain ⟨w, hw, hcw⟩ := h.exists_eq_of_le (le_max_left u V) hle
    (le_trans zero_le_one (hV _ (le_max_right u V)))
  have hwZ : w ∈ {s : ℝ | 0 ≤ s ∧ c s = 0} :=
    ⟨le_trans h.lastZeroR_nonneg (le_trans (le_of_lt hu) hw.1), hcw⟩
  have := le_csSup h.bddAbove_zeroSet hwZ
  change w ≤ lastZeroR c at this
  linarith [hw.1]

variable {X : ℝ → ℝ}

/-- The level set of `X` at a positive level is bounded above, when `X s = c(ℓ + s)` for `s > 0`. -/
theorem bddAbove_levelSet (h : GoodDrift c μ) (hX : ∀ s, 0 < s → X s = c (lastZeroR c + s)) (y : ℝ) :
    BddAbove {s : ℝ | X s = y} := by
  obtain ⟨U, hU⟩ := (tendsto_atTop_atTop.1 h.tendsto_atTop) (y + 1)
  refine ⟨max 0 (U - lastZeroR c), fun s hs => ?_⟩
  rcases le_or_gt s 0 with hs0 | hs0
  · exact le_trans hs0 (le_max_left _ _)
  · have hcs : c (lastZeroR c + s) = y := by rw [← hX s hs0]; exact hs
    by_contra hlt
    have hge : U ≤ lastZeroR c + s := by
      have := lt_of_le_of_lt (le_max_right 0 (U - lastZeroR c)) (not_le.1 hlt)
      linarith
    have := hU _ hge
    rw [hcs] at this
    linarith

/-- **Last passage at a positive level.** For `y > 0`, the supremum of `{s | X s = y}` is positive, attained, and
satisfies `c(ℓ + sup) = y`. -/
theorem lastLevel_spec (h : GoodDrift c μ) (hX : ∀ s, 0 < s → X s = c (lastZeroR c + s)) {y : ℝ}
    (hy : 0 < y) :
    0 < sSup {s : ℝ | X s = y} ∧ c (lastZeroR c + sSup {s : ℝ | X s = y}) = y := by
  set ℓ := lastZeroR c with hℓ
  obtain ⟨V, hV⟩ := (tendsto_atTop_atTop.1 h.tendsto_atTop) y
  -- a first passage after `ℓ`
  obtain ⟨w, hw, hcw⟩ := h.exists_eq_of_le (le_max_left ℓ V)
    (by rw [h.lastZeroR_mem.2]; exact le_of_lt hy) (hV _ (le_max_right ℓ V))
  have hwℓ : ℓ < w := by
    rcases eq_or_lt_of_le hw.1 with heq | hlt
    · rw [← heq, h.lastZeroR_mem.2] at hcw
      exact absurd hcw (ne_of_lt hy)
    · exact hlt
  set s₀ := w - ℓ with hs₀
  have hs₀pos : 0 < s₀ := by rw [hs₀]; linarith
  have hs₀S : X s₀ = y := by rw [hX s₀ hs₀pos, hs₀]; simpa using hcw
  set S := {s : ℝ | X s = y} with hS
  set T := {s : ℝ | s₀ ≤ s ∧ c (ℓ + s) = y} with hT
  have hbdd : BddAbove S := h.bddAbove_levelSet hX y
  have hTS : T ⊆ S := fun s hs => by
    change X s = y
    rw [hX s (lt_of_lt_of_le hs₀pos hs.1)]
    exact hs.2
  have hTne : T.Nonempty := ⟨s₀, le_rfl, by rw [hs₀]; simpa using hcw⟩
  have hTcl : IsClosed T :=
    isClosed_Ici.inter (isClosed_singleton.preimage (h.cont.comp (continuous_const.add continuous_id)))
  have hTbdd : BddAbove T := hbdd.mono hTS
  have hTmem := hTcl.csSup_mem hTne hTbdd
  have hsup : sSup S = sSup T := by
    apply le_antisymm
    · refine csSup_le ⟨s₀, hs₀S⟩ (fun s hs => ?_)
      rcases le_or_gt s₀ s with hle | hlt
      · have hsT : s ∈ T := ⟨hle, by
          have := hX s (lt_of_lt_of_le hs₀pos hle)
          rw [← this]; exact hs⟩
        exact le_csSup hTbdd hsT
      · exact le_trans (le_of_lt hlt) (le_csSup hTbdd ⟨le_rfl, by rw [hs₀]; simpa using hcw⟩)
    · exact csSup_le_csSup hbdd hTne hTS
  rw [hsup]
  exact ⟨lt_of_lt_of_le hs₀pos hTmem.1, hTmem.2⟩

/-- **Deterministic last-passage asymptotics** (the radial argument): `sup {s | X s = y} / y → μ⁻¹` as `y → ∞`. -/
theorem tendsto_lastLevel_div (h : GoodDrift c μ) (hX : ∀ s, 0 < s → X s = c (lastZeroR c + s)) :
    Tendsto (fun y => sSup {s : ℝ | X s = y} / y) atTop (𝓝 μ⁻¹) := by
  set ℓ := lastZeroR c with hℓ
  set u : ℝ → ℝ := fun y => ℓ + sSup {s : ℝ | X s = y} with hu
  have hspec : ∀ y, 0 < y → 0 < sSup {s : ℝ | X s = y} ∧ c (u y) = y := fun y hy =>
    h.lastLevel_spec hX hy
  -- `u y → ∞`
  have hu_top : Tendsto u atTop atTop := by
    refine tendsto_atTop_atTop.2 (fun T => ?_)
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).bddAbove_image h.cont.continuousOn
    refine ⟨max M 0 + 1, fun y hy => ?_⟩
    have hy0 : 0 < y := by linarith [le_max_right M 0]
    obtain ⟨hpos, hcu⟩ := hspec y hy0
    by_contra hlt
    push Not at hlt
    have hmem : u y ∈ Icc (0 : ℝ) T :=
      ⟨by simp only [hu]; linarith [h.lastZeroR_nonneg], le_of_lt hlt⟩
    have := hM (mem_image_of_mem c hmem)
    rw [hcu] at this
    linarith [le_max_left M 0]
  have hratio : Tendsto (fun y => y / u y) atTop (𝓝 μ) := by
    refine (h.lim.comp hu_top).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    simp only [Function.comp_apply]
    rw [(hspec y hy).2]
  have hinv : Tendsto (fun y => u y / y) atTop (𝓝 μ⁻¹) := by
    refine (hratio.inv₀ (ne_of_gt h.pos)).congr' ?_
    filter_upwards with y
    rw [inv_div]
  have hℓy : Tendsto (fun y : ℝ => ℓ / y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsub := hinv.sub hℓy
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  simp only [hu]
  field_simp
  ring

end GoodDrift

/-! ### The cone radial path -/

/-- The drifted Brownian path `c(u) = B'_u + (Q − α)u` whose post-last-zero part is the cone's radial path. -/
def coneDrift (γ α : ℝ) (b' : ℝ≥0 → ℝ) : ℝ → ℝ := fun u => b' u.toNNReal + (lqgQ γ - α) * u

theorem coneLogRadial_of_pos (γ α : ℝ) (b b' : ℝ≥0 → ℝ) {s : ℝ} (hs : 0 < s) :
    coneLogRadial γ α b b' s = coneDrift γ α b' (lastZeroR (coneDrift γ α b') + s) := by
  have hns : ¬ (0 ≤ -s) := by linarith
  unfold coneLogRadial coneRadial
  rw [ite_eq_right hns]
  show coneDrift γ α b' (lastZeroR (coneDrift γ α b') - -s) + lqgQ γ * -s + lqgQ γ * s = _
  rw [sub_neg_eq_add]
  ring

theorem coneLogRadial_of_nonpos (γ α : ℝ) (b b' : ℝ≥0 → ℝ) {s : ℝ} (hs : s ≤ 0) :
    coneLogRadial γ α b b' s = b (-s).toNNReal + α * (-s) + lqgQ γ * s := by
  have hns : 0 ≤ -s := by linarith
  unfold coneLogRadial coneRadial
  rw [ite_eq_left hns]

/-- `Q − γ > 0` for `γ ∈ (0, 2)`. -/
theorem lqgQ_sub_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 < lqgQ γ - γ := by
  unfold lqgQ
  have h1 : 2 / γ - γ / 2 = (4 - γ ^ 2) / (2 * γ) := by field_simp; ring
  have h2 : 0 < (4 - γ ^ 2) / (2 * γ) := div_pos (by nlinarith) (by linarith)
  linarith

/-- `(Q − γ)⁻¹ γ⁻¹ = a_γ`. -/
theorem inv_lqgQ_sub_mul_inv {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    (lqgQ γ - γ)⁻¹ * γ⁻¹ = radiusExponent γ := by
  unfold lqgQ radiusExponent
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hden : (2 : ℝ) - γ ^ 2 / 2 ≠ 0 := by nlinarith
  have hmu : 2 / γ + γ / 2 - γ = (2 - γ ^ 2 / 2) / γ := by field_simp; ring
  rw [hmu, inv_div]
  field_simp

/-- **the cone-radius asymptotic, deterministic form.** If the drifted path `c(u) = b'_u + (Q − γ)u` satisfies `GoodDrift`,
then `log₂ R_{2^k} / k → a_γ`. (The path `b` of the negative side plays no role.) -/
theorem tendsto_logb_coneScale {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (b b' : ℝ≥0 → ℝ)
    (h : GoodDrift (coneDrift γ γ b') (lqgQ γ - γ)) :
    Tendsto (fun k : ℕ => Real.logb 2 (coneScale γ γ b b' (2 ^ k)) / k) atTop
      (𝓝 (radiusExponent γ)) := by
  set X := coneLogRadial γ γ b b' with hXdef
  have hX : ∀ s, 0 < s → X s = coneDrift γ γ b' (lastZeroR (coneDrift γ γ b') + s) :=
    fun s hs => coneLogRadial_of_pos γ γ b b' hs
  have hlim := h.tendsto_lastLevel_div hX
  set y : ℕ → ℝ := fun k => γ⁻¹ * Real.log ((2 : ℝ) ^ k) with hy
  have hy_eq : ∀ k : ℕ, y k = (γ⁻¹ * Real.log 2) * k := by
    intro k
    simp only [hy, Real.log_pow]
    ring
  have hcoef : 0 < γ⁻¹ * Real.log 2 := mul_pos (inv_pos.2 hγ) (Real.log_pos (by norm_num))
  have hy_top : Tendsto y atTop atTop := by
    have : Tendsto (fun k : ℕ => (γ⁻¹ * Real.log 2) * (k : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop hcoef tendsto_natCast_atTop_atTop
    exact this.congr (fun k => (hy_eq k).symm)
  have hcomp := (hlim.comp hy_top).mul_const γ⁻¹
  rw [inv_lqgQ_sub_mul_inv hγ hγ2] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  simp only [Function.comp_apply, coneScale, Real.logb, Real.log_exp]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hyk : y k ≠ 0 := by rw [hy_eq k]; exact mul_ne_zero (ne_of_gt hcoef) hk0
  rw [hy_eq k] at hyk ⊢
  change sSup {s : ℝ | X s = (γ⁻¹ * Real.log 2) * k} / ((γ⁻¹ * Real.log 2) * k) * γ⁻¹ =
    sSup {s : ℝ | X s = γ⁻¹ * Real.log ((2 : ℝ) ^ k)} / Real.log 2 / k
  have hset : {s : ℝ | X s = γ⁻¹ * Real.log ((2 : ℝ) ^ k)} = {s : ℝ | X s = (γ⁻¹ * Real.log 2) * k} := by
    rw [Real.log_pow]; ring_nf
  rw [hset]
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  generalize sSup {s : ℝ | X s = (γ⁻¹ * Real.log 2) * k} = A
  field_simp

/-- `R_1 = 1` (the circle-average normalization; the cone normalization): if `b 0 = 0` and the drift is good. -/
theorem coneScale_one {γ : ℝ} (b b' : ℝ≥0 → ℝ) (hb0 : b 0 = 0) {μ : ℝ}
    (h : GoodDrift (coneDrift γ γ b') μ) : coneScale γ γ b b' 1 = 1 := by
  have hset : {s : ℝ | coneLogRadial γ γ b b' s = γ⁻¹ * Real.log 1} ⊆ Iic 0 := by
    intro s hs
    simp only [Real.log_one, mul_zero, mem_ofPred_eq] at hs
    by_contra hpos
    rw [Set.mem_Iic, not_le] at hpos
    rw [coneLogRadial_of_pos γ γ b b' hpos] at hs
    have := h.pos_of_lastZeroR_lt (u := lastZeroR (coneDrift γ γ b') + s) (by linarith)
    linarith
  have h0mem : (0 : ℝ) ∈ {s : ℝ | coneLogRadial γ γ b b' s = γ⁻¹ * Real.log 1} := by
    simp only [mem_ofPred_eq, Real.log_one, mul_zero]
    rw [coneLogRadial_of_nonpos γ γ b b' le_rfl]
    simp [hb0]
  have hsup : sSup {s : ℝ | coneLogRadial γ γ b b' s = γ⁻¹ * Real.log 1} = 0 :=
    le_antisymm (csSup_le ⟨0, h0mem⟩ hset) (le_csSup ⟨0, hset⟩ h0mem)
  simp only [coneScale, hsup, Real.exp_zero]

/-- **`R_b` is a genuine last-passage radius** (non-junk characterization of `coneScale`): for `b > 1`,
`log R_b > 0`, the radial path takes the value `γ⁻¹ log b` at `log R_b`, and never after it. -/
theorem coneScale_lastPassage {γ : ℝ} (hγ : 0 < γ) (b b' : ℝ≥0 → ℝ)
    (h : GoodDrift (coneDrift γ γ b') (lqgQ γ - γ)) {b₀ : ℝ} (hb₀ : 1 < b₀) :
    0 < Real.log (coneScale γ γ b b' b₀) ∧
      coneLogRadial γ γ b b' (Real.log (coneScale γ γ b b' b₀)) = γ⁻¹ * Real.log b₀ ∧
      ∀ s, coneLogRadial γ γ b b' s = γ⁻¹ * Real.log b₀ → s ≤ Real.log (coneScale γ γ b b' b₀) := by
  have hX : ∀ s, 0 < s → coneLogRadial γ γ b b' s =
      coneDrift γ γ b' (lastZeroR (coneDrift γ γ b') + s) := fun s hs => coneLogRadial_of_pos γ γ b b' hs
  have hy : 0 < γ⁻¹ * Real.log b₀ := mul_pos (inv_pos.2 hγ) (Real.log_pos hb₀)
  obtain ⟨hpos, hval⟩ := h.lastLevel_spec hX hy
  simp only [coneScale, Real.log_exp]
  refine ⟨hpos, ?_, fun s hs => le_csSup (h.bddAbove_levelSet hX _) hs⟩
  rw [hX _ hpos]
  exact hval

/-! ### The Brownian input -/

/-- For a Brownian motion `B'`, almost surely the drifted path `c(u) = B'_u + μ u` is a good drift. -/
theorem ae_goodDrift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B' : ℝ≥0 → Ω → ℝ}
    (hB' : IsBrownianReal B' P) {γ α : ℝ} (hμ : 0 < lqgQ γ - α) :
    ∀ᵐ ω ∂P, GoodDrift (coneDrift γ α (fun t => B' t ω)) (lqgQ γ - α) := by
  filter_upwards [hB'.cont, hB'.eval_zero_ae_eq_zero, QuantumZipper.BMLLN.ae_tendsto_div_atTop hB']
    with ω hcont hzero hlln
  refine ⟨?_, ?_, hμ, ?_⟩
  · exact (hcont.comp continuous_real_toNNReal).add (continuous_const.mul continuous_id)
  · simp [coneDrift, hzero]
  · have hcomp : Tendsto (fun u : ℝ => ((u.toNNReal : ℝ≥0) : ℝ)⁻¹ * B' u.toNNReal ω) atTop (𝓝 0) :=
      hlln.comp tendsto_real_toNNReal_atTop
    have hsum := hcomp.add (tendsto_const_nhds (x := lqgQ γ - α))
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    simp only [coneDrift, Real.coe_toNNReal _ (le_of_lt hu)]
    field_simp

/-- **the cone-radius asymptotic** : for the radial Brownian motions `B, B'` of the γ-quantum cone (any `B`;
`B'` a standard Brownian motion), almost surely `log₂ R_{2^k} / k → a_γ = 1/(2 − γ²/2)`. -/
theorem ae_tendsto_logb_coneScale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (B : ℝ≥0 → Ω → ℝ) {B' : ℝ≥0 → Ω → ℝ} (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ => Real.logb 2 (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) (2 ^ k)) / k)
      atTop (𝓝 (radiusExponent γ)) := by
  filter_upwards [ae_goodDrift hB' (lqgQ_sub_pos hγ hγ2)] with ω hω
  exact tendsto_logb_coneScale hγ hγ2 _ _ hω

/-- **`R_1 = 1` almost surely** : the non-junk normalization of `coneScale`. -/
theorem ae_coneScale_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, coneScale γ γ (fun t => B t ω) (fun t => B' t ω) 1 = 1 := by
  filter_upwards [hB.eval_zero_ae_eq_zero, ae_goodDrift hB' (lqgQ_sub_pos hγ hγ2)] with ω h0 hω
  exact coneScale_one _ _ h0 hω

/-- **`R_b` is a.s. a genuine last-passage radius for every `b > 1`** (non-junk anchor for `coneScale`). -/
theorem ae_coneScale_lastPassage {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (B : ℝ≥0 → Ω → ℝ) {B' : ℝ≥0 → Ω → ℝ} (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, ∀ b₀ : ℝ, 1 < b₀ →
      0 < Real.log (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b₀) ∧
      coneLogRadial γ γ (fun t => B t ω) (fun t => B' t ω)
          (Real.log (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b₀)) = γ⁻¹ * Real.log b₀ ∧
      ∀ s, coneLogRadial γ γ (fun t => B t ω) (fun t => B' t ω) s = γ⁻¹ * Real.log b₀ →
        s ≤ Real.log (coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b₀) := by
  filter_upwards [ae_goodDrift hB' (lqgQ_sub_pos hγ hγ2)] with ω hω b₀ hb₀
  exact coneScale_lastPassage hγ _ _ hω hb₀

end MatedCRTHarmonic.CellScaling
