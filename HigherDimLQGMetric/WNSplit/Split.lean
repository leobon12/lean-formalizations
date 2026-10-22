import HigherDimLQGMetric.WNSplit.Statement
import HigherDimLQGMetric.WNSplit.Vectors
import HigherDimLQGMetric.WNSplit.Generic
import HigherDimLQGMetric.WNSplit.Sigma

/-!
# D-WN′: the white-noise split of the LGF (packet S5a, target 1)

Source: MA3 §1.11 (E8–E9) and Details (a) **D-WN′** (`planning/audits/MA3-sections-5-6.md`);
statement `WhiteNoiseSplit` (MA3 Details (c), verbatim in `WNSplit/Statement.lean`); blueprint
`prop:wn-split`.

**Construction.** Start from F2's white-noise realization (`exists_wn_realization`): a white noise
`W` on `(ℕ → ℝ, stdP)` and an LGF `h` (a random distribution for every `ω`) with
`⟨h, φ⟩ = W(gramVec (φ − (∫ φ) θ))` a.s. For a cutoff `b > 0`:

* the **coarse field** `g_b` is a continuous version (`wns_exists_version`) of `x ↦ W(wnsPt b x)`,
  `wnsPt b x = coarse(δ_x − θ) − fine(θ)` (increments `‖·‖² ≤ L ‖x − x'‖² / b²`);
* the **fine field** is `F_b = h − g_b`, a random distribution for every `ω`.

Then (1) `F_b + g_b = h` is an LGF. Stochastic Fubini (`wns_ae_integral_mul_eq`, with the
deterministic identity `coeFn_wnsCoarse`) gives `∫ φ g_b = W(gramVec (φ − (∫ φ) θ) − k^φ_{(0,b)})`
a.s., hence `⟨F_b, φ⟩ = W(k^φ_{(0,b)})` a.s. (`ae_wnsFine_apply`); as `k^φ_{(0,b)}` vanishes outside
`(0, b) × B(w, ρ + ρ₀ b)` when `tsupport φ ⊆ B(w, ρ)`, (2) holds with `R_𝔎 = ρ₀` and the completed
noise σ-algebras `𝒢(S, b)` (`wnsSigma`); (3) is `iIndep_wnsSigma`; (4) is the chaining/Borell–TIS
bound `wns_block_tail` on `B̄(w, 5s)` with `a = b = Ls`, `r = 5/L`, `L₁ = max(L_κ, 1)`:
`P(osc_{B(w,5s)} g_{Ls} > δ) ≤ 2 exp(−δ² L² / (800 L₁))` once `blockConst(5/L) ≤ δ/4`, uniformly
in `s` and `w`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN)

variable {d : ℕ}

/-- Local boundedness of the coarse point vectors. -/
theorem exists_norm_wnsPt_sq_le {b : ℝ} (hb : 0 < b) :
    ∀ R : ℝ, ∃ C : ℝ, ∀ x : Rd d, ‖x‖ ≤ R → ‖wnsPt b x‖ ^ 2 ≤ C := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_wnsPt_sub_sq_le (d := d)
  intro R
  refine ⟨2 * ‖wnsPt b (0 : Rd d)‖ ^ 2 + 2 * (L * R ^ 2 / b ^ 2), fun x hx => ?_⟩
  have h1 : ‖wnsPt b x‖ ≤ ‖wnsPt b (0 : Rd d)‖ + ‖wnsPt b x - wnsPt b (0 : Rd d)‖ := by
    have := norm_sub_norm_le (wnsPt b x) (wnsPt b (0 : Rd d))
    linarith
  have h2 : ‖wnsPt b x - wnsPt b (0 : Rd d)‖ ^ 2 ≤ L * R ^ 2 / b ^ 2 := by
    refine (hL b hb x 0).trans ?_
    rw [sub_zero]
    have : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    gcongr
  have h3 : ‖wnsPt b x‖ ^ 2 ≤ (‖wnsPt b (0 : Rd d)‖ + ‖wnsPt b x - wnsPt b (0 : Rd d)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖wnsPt b (0 : Rd d)‖ - ‖wnsPt b x - wnsPt b (0 : Rd d)‖)]

section Pairing

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

/-- **The pairings of the fine field** (`d ≥ 1`, `b > 0`): if `h` is a white-noise realization
(`⟨h, φ⟩ = W(gramVec (φ − (∫ φ) θ))` a.s.) and `Y` a continuous version of `x ↦ W(wnsPt b x)`, then
`⟨h − Y, φ⟩ = W(k^φ_{(0,b)})` a.s. for every test function `φ`. -/
theorem ae_wnsFine_apply [NeZero d] (hW : HigherDimLFPP.IsWhiteNoise P W)
    {h : Ω → DistRd d}
    (hpair : ∀ φ : TestRd d, (fun ω => h ω φ) =ᵐ[P] W (gramVec (subTheta φ)))
    {b : ℝ} (hb : 0 < b) {Y : Rd d → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) (hYW : ∀ x, (fun ω => Y x ω) =ᵐ[P] W (wnsPt b x))
    (φ : TestRd d) :
    (fun ω => (h ω - ofCont ⟨fun x => Y x ω, hYc ω⟩) φ) =ᵐ[P] W (wnsFine b φ) := by
  have hint : (fun ω => ∫ x, φ x * Y x ω) =ᵐ[P] W (wnsCoarse b φ) :=
    wns_ae_integral_mul_eq hW hYc hYm hYW (exists_norm_wnsPt_sq_le hb) φ.continuous
      φ.hasCompactSupport fun g => wns_integral_mul_inner (measurable_wnsPtRep b)
        (coeFn_wnsPt hb) (exists_norm_wnsPt_sq_le hb) φ.continuous φ.hasCompactSupport
        (coeFn_wnsCoarse hb φ) g
  have e : wnsFine b φ = gramVec (subTheta φ) - wnsCoarse b φ := by
    rw [wnsCoarse, sub_sub_cancel]
  filter_upwards [hpair φ, hint, hW.sub_ae (gramVec (subTheta φ)) (wnsCoarse b φ)]
    with ω h1 h2 h3
  rw [e, h3, ← h1, ← h2, sub_apply, ofCont_apply]
  rfl

end Pairing

/-- Measurability of `ω ↦ h(ω) − Y(·, ω)` for a measurable random distribution `h` and a field `Y`
continuous in `x` and measurable in `ω`. -/
theorem wns_measurable_sub_ofCont {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistRd d}
    (hh : Measurable h) {Y : Rd d → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) :
    Measurable fun ω => h ω - ofCont ⟨fun x => Y x ω, hYc ω⟩ := by
  have hg : Measurable fun ω => (⟨fun x => Y x ω, hYc ω⟩ : C(Rd d, ℝ)) :=
    ContinuousMap.measurable_iff_eval.2 hYm
  exact hh.sub (Measurable.ofCont hg)

/-- **D-WN′, the white-noise split** (`WhiteNoiseSplit d`, MA3 Details (c), verbatim), for every
`d ≥ 2`. -/
theorem whiteNoiseSplit (hd : 2 ≤ d) : WhiteNoiseSplit d := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨W, h, hW, hh, hpair⟩ := exists_wn_realization (d := d) (by omega)
  obtain ⟨ρ₀, hρ₀, hρ⟩ := (wns_isLFPPKernel (d := d)).exists_radius
  obtain ⟨Lκ, hLκ0, hLκ⟩ := exists_norm_wnsPt_sub_sq_le (d := d)
  have hYex : ∀ b : ℝ, ∃ Y : Rd d → (ℕ → ℝ) → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧
      (∀ x, Measurable (Y x)) ∧
      (0 < b → ∀ x, (fun ω => Y x ω) =ᵐ[LQGDimension.ExistAsm.stdP] W (wnsPt b x)) := by
    intro b
    by_cases hb : 0 < b
    · obtain ⟨Y, hYc, hYm, hYW⟩ := wns_exists_version hW (u := wnsPt b) (c := Lκ / b ^ 2)
        (by positivity) fun z w => by
          rw [← mul_div_right_comm]
          exact hLκ b hb z w
      exact ⟨Y, hYc, hYm, fun _ => hYW⟩
    · exact ⟨fun _ _ => 0, fun _ => continuous_const, fun _ => measurable_const,
        fun h' => absurd h' hb⟩
  choose Y hYc hYm hYW using hYex
  set g : ℝ → (ℕ → ℝ) → C(Rd d, ℝ) := fun b ω => ⟨fun x => Y b x ω, hYc b ω⟩ with hg
  set F : ℝ → (ℕ → ℝ) → DistRd d := fun b ω => h ω - ofCont (g b ω) with hF
  refine ⟨ℕ → ℝ, inferInstance, LQGDimension.ExistAsm.stdP, hW.isProbabilityMeasure,
    fun S b => wnsSigma LQGDimension.ExistAsm.stdP W S b, ρ₀, F, g, hρ₀, ?_, ?_, ?_, ?_⟩
  · -- (1) measurability and `F_b + g_b = h`
    intro b hb
    refine ⟨wns_measurable_sub_ofCont hh.measurable (hYc b) (hYm b),
      ContinuousMap.measurable_iff_eval.2 (hYm b), ?_⟩
    have e : (fun ω => F b ω + ofCont (g b ω)) = h := by
      funext ω
      simp only [hF, sub_add_cancel]
    rw [e]
    exact hh
  · -- (2) finite range of the fine field
    intro b hb w r hr
    rw [fieldSigmaOn, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun ψ => ?_
    rw [MeasurableSpace.comap_comp]
    refine Measurable.comap_le ?_
    have hψ : tsupport (ψ.1 : Rd d → ℝ) ⊆ ball w r := ψ.2
    exact measurable_wnsSigma_of_ae_eq
      ((measurable_distOn_apply ψ.1).comp (wns_measurable_sub_ofCont hh.measurable (hYc b) (hYm b)))
      (ae_wnsFine_eq_zero hb hρ₀ hρ ψ.1 hψ)
      (ae_wnsFine_apply hW hpair hb (hYc b) (hYm b) (hYW b hb) ψ.1)
  · -- (3) independence over disjoint regions
    intro b hb n S hS
    exact iIndep_wnsSigma hW hS b
  · -- (4) the coarse oscillation
    intro η δ hη hδ
    set L₁ : ℝ := max Lκ 1 with hL₁
    have hL₁0 : 0 < L₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
    set K₀ : ℝ := 20 * √5 * (2 * 5 * √(L₁ * √(d : ℝ) * (d + 1))) with hK₀
    have hK₀0 : 0 ≤ K₀ := by positivity
    have hA : 0 ≤ 4 * K₀ / δ := by positivity
    have hB : 0 ≤ 1600 * L₁ / (δ ^ 2 * η) := by positivity
    refine ⟨1 + 4 * K₀ / δ + 1600 * L₁ / (δ ^ 2 * η), by positivity, fun L hL s hs w => ?_⟩
    have hL1 : 1 ≤ L := by linarith
    have hL0 : 0 < L := by linarith
    have hLK : 4 * K₀ / δ ≤ L := by linarith
    have hLη : 1600 * L₁ / (δ ^ 2 * η) ≤ L := by linarith
    have hb : 0 < L * s := mul_pos hL0 hs
    set r : ℝ := 5 / L with hr
    have hr0 : 0 < r := div_pos (by norm_num) hL0
    have hrb : r * (L * s) = 5 * s := by
      rw [hr]
      field_simp
    have hblock : HigherDimLFPP.Osc.blockConst d L₁ r = K₀ / L := by
      simp only [HigherDimLFPP.Osc.blockConst]
      rw [hr, hK₀]
      ring
    have hbc : HigherDimLFPP.Osc.blockConst d L₁ r ≤ δ / 4 := by
      rw [hblock, div_le_iff₀ hL0]
      have := (div_le_iff₀ hδ).1 hLK
      linarith
    have hincr : ∀ z z' : Rd d,
        ‖wnsPt (L * s) z - wnsPt (L * s) z'‖ ^ 2 ≤ L₁ * ‖z - z'‖ ^ 2 / (L * s) ^ 2 :=
      fun z z' => (hLκ (L * s) hb z z').trans (by gcongr; exact le_max_left _ _)
    have htail := wns_block_tail hW (hYc (L * s)) (hYW (L * s) hb) hb hL₁0.le hincr w hr0.le
      (t := δ / 4) (by positivity)
    rw [hrb] at htail
    have hsub : {ω | ∃ x ∈ ball w (5 * s), ∃ y ∈ ball w (5 * s),
        δ < |g (L * s) ω x - g (L * s) ω y|} ⊆
        {ω | ∃ z ∈ closedBall w (5 * s), HigherDimLFPP.Osc.blockConst d L₁ r + δ / 4 <
          |Y (L * s) z ω - Y (L * s) w ω|} := by
      rintro ω ⟨x, hx, y, hy, hxy⟩
      have hxy' : δ < |Y (L * s) x ω - Y (L * s) y ω| := hxy
      have htri : |Y (L * s) x ω - Y (L * s) y ω| ≤
          |Y (L * s) x ω - Y (L * s) w ω| + |Y (L * s) y ω - Y (L * s) w ω| := by
        have := abs_sub_le (Y (L * s) x ω) (Y (L * s) w ω) (Y (L * s) y ω)
        rwa [abs_sub_comm (Y (L * s) w ω) (Y (L * s) y ω)] at this
      by_cases h1 : δ / 2 < |Y (L * s) x ω - Y (L * s) w ω|
      · exact ⟨x, ball_subset_closedBall hx, by linarith⟩
      · exact ⟨y, ball_subset_closedBall hy, by linarith⟩
    refine (measure_mono hsub).trans (htail.trans (ENNReal.ofReal_le_ofReal ?_))
    set x : ℝ := (δ / 4) ^ 2 / (2 * (r ^ 2 * L₁)) with hx
    have hx0 : 0 < x := by positivity
    have hexp : Real.exp (-x) ≤ x⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ hx0 (by linarith [Real.add_one_le_exp x])
    have hxval : x = δ ^ 2 * L ^ 2 / (800 * L₁) := by
      rw [hx, hr]
      field_simp
      ring
    have key : 2 * x⁻¹ ≤ η := by
      rw [hxval, inv_div, mul_div_assoc', div_le_iff₀ (by positivity)]
      have h1 := (div_le_iff₀ (by positivity)).1 hLη
      have h2 : L ≤ L ^ 2 := by nlinarith
      have h3 : 0 ≤ δ ^ 2 * η := by positivity
      nlinarith
    calc 2 * Real.exp (-(δ / 4) ^ 2 / (2 * (r ^ 2 * L₁))) = 2 * Real.exp (-x) := by
          rw [hx, neg_div]
      _ ≤ 2 * x⁻¹ := by gcongr
      _ ≤ η := key

end HigherDimLQGMetric
