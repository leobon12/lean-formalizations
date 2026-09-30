import QuantumZipper.Proofs.RS.BasePointHit
import QuantumZipper.Proofs.Thm12.CharFun

/-!
# RS BP1: real points are not approached (`κ ≤ 4`)

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §4, node BP1 (BP1-a for `κ < 4`, BP1-4 for `κ = 4`).

`RS.ae_bp1`: for a Brownian motion `B`, `κ ∈ (0,4]` and `0 < y < x`, almost surely there is
`ε > 0` such that for every `T ≥ 0` and all forward solutions `u` (from `x`) and `v` (from `y`)
on `[0,T]`, `ε ≤ Υ_T = (X_T − O_T) exp(∫₀ᵀ 2/X²) = (g_T(x) − g_T(y))/g_T'(x)` (`bpUpsPath`).
Combined with Koebe 1/4 (node KR: `dist(x, K_t) ≥ c₀ Υ_t`) this gives
`x ∉ closure (η [0,∞))` (Rohde–Schramm, Lemma 7.2).

Proof. The hitting estimate `bp_hit_bound` (optional stopping for a supersolution, RS P1),
applied to
* `κ < 4` (BP1-a, **own argument**, EXT_RS §9): `F = Υ^{−p}(2 − ρ)`, `ρ = O/X`,
  `p = min(1/2, (4−κ)/2)` (`dynkinGen_bp1_le`); gives `ε^{−p} P(Υ hits ε) ≤ 2 (x−y)^{−p}`.
  The published κ < 4 proofs (RS Lemma 7.2, p. 32; Kemppainen, *SLE*, Prop. 5.4, pp. 81–82;
  Lawler, *Conformally invariant processes*, Prop. 6.12, p. 128) use a harmonic-measure
  comparison, which the project does not have; we use RS's κ = 4 Koebe mechanism with a power
  supersolution instead.
* `κ = 4` (BP1-4, RS Lemma 7.2, pp. 32–33): `F = −(log Υ + G(s)) = Q − G_t`, RS's local
  martingale (`dynkinGen_bp14_eq`), with `−1 ≤ G ≤ 2`; gives
  `log(R/ε) P(Υ hits ε) ≤ log(R/(x−y)) + 3`, `R = x − y + 1`. RS use monotone convergence of
  `E Q(t_n)`; we use the equivalent Markov bound at the hitting time of `{Υ = ε}`.

Then `ε → 0`, over an exhausting sequence of horizons `T = n` and lower barriers `c = y/(n+1)`
(continuity from below, for not necessarily measurable sets).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace RS

section Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **BP1-a bound (κ < 4).** `ε^{−p} P(Υ hits ε before T, X, O > c) ≤ 2 (x − y)^{−p}`. -/
theorem bp1_event_bound (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {x y c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hcy : c ≤ y) (hεxy : ε ≤ x - y) (T : ℝ≥0) :
    ε ^ (-bp1Exp κ) * P.real (bpEvent (√κ) c ε x y B T) ≤ 2 * (x - y) ^ (-bp1Exp κ) := by
  set p := bp1Exp κ with hp
  have hp0 : 0 ≤ p := le_min (by norm_num) (by linarith)
  have hxy : 0 < x - y := hε.trans_le hεxy
  have hK : ∀ v ∈ bpK c ε (x - y + 1), 0 < v.2.1 / v.1 ∧ v.2.1 / v.1 < 1 := fun v hv => by
    have h := bpK_subset hc hε hv
    exact ⟨div_pos h.1 (h.1.trans h.2), (div_lt_one (h.1.trans h.2)).2 h.2⟩
  have hUp : ∀ v ∈ bpK c ε (x - y + 1), bpUps v ^ (-p) ≤ ε ^ (-p) := fun v hv =>
    Real.rpow_le_rpow_of_nonpos hε hv.2.1 (neg_nonpos.2 hp0)
  have hUpos : ∀ v ∈ bpK c ε (x - y + 1), 0 < bpUps v ^ (-p) := fun v hv =>
    Real.rpow_pos_of_pos (hε.trans_le hv.2.1) _
  have h := bp_hit_bound (P := P) hB hBm hBc hB0 (κ := κ) (R := x - y + 1) hc hε hcy hεxy
    (by linarith) T (contDiffOn_bp1Test κ)
    (fun v h1 h2 => dynkinGen_bp1_le hκ hκ4 hc ⟨h1, h2⟩)
    (M := 2 * ε ^ (-p)) (m := 0) (a := ε ^ (-p))
    (fun v hv => by
      unfold bp1Test
      rw [abs_of_nonneg (mul_nonneg (hUpos v hv).le (by linarith [(hK v hv).2]))]
      have := hUp v hv
      nlinarith [(hK v hv).1, (hUpos v hv)])
    (fun v hv => mul_nonneg (hUpos v hv).le (by linarith [(hK v hv).2]))
    (fun v hv he => by
      unfold bp1Test
      rw [he]
      have := Real.rpow_pos_of_pos hε (-p)
      nlinarith [(hK v hv).2])
    (Real.rpow_pos_of_pos hε _).le
  simp only [sub_zero] at h
  refine h.trans ?_
  have hu0 : bpUps (x, y, 0) = x - y := by simp [bpUps]
  simp only [bp1Test, hu0]
  have h1 : 0 < (x - y) ^ (-p) := Real.rpow_pos_of_pos hxy _
  have h2 : 0 ≤ y / x := div_nonneg (hc.le.trans hcy) (by linarith)
  nlinarith

/-- **BP1-4 bound (κ = 4).** `log(R/ε) P(Υ hits ε before T, X, O > c) ≤ log(R/(x−y)) + 3`,
`R = x − y + 1` (RS Lemma 7.2, pp. 32–33). -/
theorem bp4_event_bound (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {x y c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hcy : c ≤ y) (hεxy : ε ≤ x - y) (T : ℝ≥0) :
    (Real.log (x - y + 1) - Real.log ε) * P.real (bpEvent (√4) c ε x y B T) ≤
      Real.log (x - y + 1) - Real.log (x - y) + 3 := by
  set R := x - y + 1 with hR_def
  have hxy : 0 < x - y := hε.trans_le hεxy
  have hs : ∀ v ∈ bpK c ε R, 0 < (v.1 - v.2.1) / v.2.1 := fun v hv => by
    have h := bpK_subset hc hε hv
    exact div_pos (sub_pos.2 h.2) h.1
  have hF : ∀ v ∈ bpK c ε R, -bp4Test v =
      -Real.log (bpUps v) - bp4G ((v.1 - v.2.1) / v.2.1) := fun v hv => by
    rw [bp4Test_eq_log_bpUps (bpK_subset hc hε hv)]; ring
  have hlog : ∀ v ∈ bpK c ε R, Real.log ε ≤ Real.log (bpUps v) ∧
      Real.log (bpUps v) ≤ Real.log R := fun v hv =>
    ⟨Real.log_le_log hε hv.2.1, Real.log_le_log (hε.trans_le hv.2.1) hv.2.2⟩
  have hG : ∀ v ∈ bpK c ε R, -1 ≤ bp4G ((v.1 - v.2.1) / v.2.1) ∧
      bp4G ((v.1 - v.2.1) / v.2.1) ≤ 2 := fun v hv =>
    ⟨neg_one_le_bp4G (hs v hv), bp4G_le_two (hs v hv)⟩
  have h := bp_hit_bound (P := P) hB hBm hBc hB0 (κ := 4) (R := R) hc hε hcy hεxy
    (by linarith) T contDiffOn_bp4Test.neg
    (fun v h1 h2 => by
      show dynkinGen (bpDrift c) (bpNoise 4) (-bp4Test) v ≤ 0
      rw [dynkinGen_neg_bp, dynkinGen_bp14_eq hc ⟨h1, h2⟩, neg_zero])
    (M := |Real.log ε| + |Real.log R| + 2) (m := -Real.log R - 2) (a := -Real.log ε - 2)
    (fun v hv => by
      rw [hF v hv, abs_le]
      have := hlog v hv; have := hG v hv
      constructor <;> linarith [neg_abs_le (Real.log ε), le_abs_self (Real.log R),
        neg_abs_le (Real.log R), le_abs_self (Real.log ε), neg_le_abs (Real.log ε)])
    (fun v hv => by rw [hF v hv]; linarith [(hlog v hv).2, (hG v hv).2])
    (fun v hv he => by rw [hF v hv, he]; linarith [(hG v hv).2])
    (by linarith [Real.log_le_log hε (show ε ≤ R by linarith)])
  have hu0 : bpUps (x, y, 0) = x - y := by simp [bpUps]
  have hmem : ((x, y, 0) : ℝ × ℝ × ℝ) ∈ bpDom := ⟨hc.trans_le hcy, by simp; linarith⟩
  have hFu : bp4Test (x, y, 0) = Real.log (x - y) + bp4G ((x - y) / y) := by
    rw [bp4Test_eq_log_bpUps hmem, hu0]
  have hG0 := neg_one_le_bp4G (show 0 < (x - y) / y from div_pos hxy (hc.trans_le hcy))
  simp only [hFu] at h
  have e : -Real.log ε - 2 - (-Real.log R - 2) = Real.log R - Real.log ε := by ring
  rw [e] at h
  linarith

/-- **From the hitting bounds to the a.s. statement.** If `h ε · P(E_{ε,n}) ≤ A` with
`h → ∞` as `ε → 0+`, then a.s. `Υ` stays above some `ε > 0`. -/
theorem ae_bp_of_bound (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) [IsFiniteMeasure P]
    {κ x y : ℝ} (hy : 0 < y) (hyx : y < x) {h : ℝ → ℝ} {A : ℝ}
    (hh : Tendsto h (𝓝[>] 0) atTop)
    (hbd : ∀ ε ∈ Ioo 0 (x - y), ∀ n : ℕ,
      h ε * P.real (bpEvent (√κ) (y / (n + 1)) ε x y B n) ≤ A) :
    ∀ᵐ ω ∂P, ∃ ε > 0, ∀ T : ℝ, 0 ≤ T → ∀ u v : ℝ → ℂ,
      IsForwardSol (sDrive (√κ) B ω) (x : ℂ) T u →
      IsForwardSol (sDrive (√κ) B ω) (y : ℂ) T v → ε ≤ bpUpsPath u v T := by
  rw [ae_iff]
  set Bad := {ω | ¬ ∃ ε > 0, ∀ T : ℝ, 0 ≤ T → ∀ u v : ℝ → ℂ,
      IsForwardSol (sDrive (√κ) B ω) (x : ℂ) T u →
      IsForwardSol (sDrive (√κ) B ω) (y : ℂ) T v → ε ≤ bpUpsPath u v T} with hBad
  set E : ℝ → ℕ → Set Ω := fun ε n => bpEvent (√κ) (y / (n + 1)) ε x y B n with hE
  have hmono : ∀ ε, Monotone (E ε) := by
    intro ε n k hnk ω ⟨t, ht, u, v, hu, hv, hgt, hle⟩
    have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk
    have hc : y / ((k : ℝ) + 1) ≤ y / ((n : ℝ) + 1) :=
      div_le_div_of_nonneg_left hy.le (by positivity) (by linarith)
    exact ⟨t, ⟨ht.1, ht.2.trans (by exact_mod_cast hnk)⟩, u, v, hu, hv,
      fun r hr => ⟨hc.trans_lt (hgt r hr).1, hc.trans_lt (hgt r hr).2⟩, hle⟩
  have hsub : ∀ ε > 0, Bad ⊆ ⋃ n, E ε n := by
    intro ε hε ω hω
    simp only [hBad, mem_ofPred_eq] at hω
    push Not at hω
    obtain ⟨T, hT, u, v, hu, hv, hlt⟩ := hω ε hε
    set W := sDrive (√κ) B ω
    have hW : Continuous W := continuous_sDrive hBc _ ω
    have hW0 : W 0 = 0 := by simp [W, sDrive, hB0]
    have hpu := re_pos_isForwardSol_real hW hT hu (by rw [hW0]; linarith)
    have hpv := re_pos_isForwardSol_real hW hT hv (by rw [hW0]; linarith)
    have hcont : ContinuousOn (fun r => min (u r).re (v r).re) (Icc 0 T) :=
      continuous_min.comp_continuousOn ((Complex.continuous_re.comp_continuousOn hu.1).prodMk
        (Complex.continuous_re.comp_continuousOn hv.1))
    obtain ⟨r0, hr0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hcont
    set m0 := min (u r0).re (v r0).re
    have hm0 : 0 < m0 := lt_min (hpu r0 hr0) (hpv r0 hr0)
    set n := max ⌈T⌉₊ ⌈y / m0⌉₊
    have hTn : T ≤ n := (Nat.le_ceil T).trans (by exact_mod_cast le_max_left _ _)
    have hyn : y / m0 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    have hcm : y / ((n : ℝ) + 1) < m0 := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_le_iff₀ hm0] at hyn
      nlinarith
    refine mem_iUnion.2 ⟨n, T, ⟨hT, by exact_mod_cast hTn⟩, u, v, hu, hv, fun r hr => ?_,
      hlt.le⟩
    have := hmin hr
    simp only [mem_ofPred_eq] at this
    exact ⟨hcm.trans_le (this.trans (min_le_left _ _)),
      hcm.trans_le (this.trans (min_le_right _ _))⟩
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P Bad ≤ ENNReal.ofReal (A / h ε) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < x - y by linarith),
      hh.eventually_gt_atTop 0] with ε hε hhε
    refine (measure_mono (hsub ε hε.1)).trans ?_
    rw [(hmono ε).measure_iUnion]
    refine iSup_le fun n => ?_
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hhε, mul_comm]
    exact hbd ε hε n
  have hlim : Tendsto (fun ε => ENNReal.ofReal (A / h ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_const_nhds (x := A).div_atTop hh)
    simpa using this
  exact le_antisymm (ge_of_tendsto hlim hbound) bot_le

end Prob

/-- **RS BP1 (BP1-a and BP1-4). Real points are not approached, `κ ≤ 4`.** For `0 < y < x`,
almost surely `Υ_T = (g_T(x) − g_T(y))/g_T'(x)` (`bpUpsPath`, computed from the centered
forward solutions from `x` and `y`) stays above a random `ε > 0` for all times at which `x`
and `y` are alive.

Sources: Rohde–Schramm, *Basic properties of SLE*, Lemma 7.2 and proof, pp. 32–33 (κ = 4
literally; κ < 4 by the same Koebe mechanism with an own power supersolution, EXT_RS §9);
Kemppainen, *SLE*, Prop. 5.4, pp. 81–82; Lawler, Prop. 6.12, pp. 128–129. -/
theorem ae_bp1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    ∀ᵐ ω ∂P, ∃ ε > 0, ∀ T : ℝ, 0 ≤ T → ∀ u v : ℝ → ℂ,
      IsForwardSol (drive κ B ω) (x : ℂ) T u → IsForwardSol (drive κ B ω) (y : ℂ) T v →
      ε ≤ bpUpsPath u v T := by
  have hBpre := hB.toIsPreBrownianReal
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  set B'' : ℝ≥0 → Ω → ℝ := fun t ω => B' t ω - B' 0 ω with hB''_def
  have hB''m : ∀ t, Measurable (B'' t) := fun t => (hB'm t).sub (hB'm 0)
  have hB''c : ∀ ω, Continuous (B'' · ω) := fun ω => (hB'c ω).sub continuous_const
  have hB''0 : ∀ ω, B'' 0 ω = 0 := fun ω => sub_self _
  have hBB : ∀ᵐ ω ∂P, ∀ t, B'' t ω = B t ω := by
    filter_upwards [hB'eq, hBpre.eval_zero_ae_eq_zero] with ω h h0 t
    simp only [hB''_def, h t, h 0, h0, sub_zero]
  have hB'' : IsPreBrownianReal B'' P := hBpre.congr fun t => hBB.mono fun ω h => (h t).symm
  have hy' : ∀ n : ℕ, y / ((n : ℝ) + 1) ≤ y := fun n =>
    div_le_self hy.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hmain : ∀ᵐ ω ∂P, ∃ ε > 0, ∀ T : ℝ, 0 ≤ T → ∀ u v : ℝ → ℂ,
      IsForwardSol (sDrive (√κ) B'' ω) (x : ℂ) T u →
      IsForwardSol (sDrive (√κ) B'' ω) (y : ℂ) T v → ε ≤ bpUpsPath u v T := by
    rcases hκ4.lt_or_eq with hlt | h4
    · have hp : 0 < bp1Exp κ := lt_min (by norm_num) (by linarith)
      refine ae_bp_of_bound hB''c hB''0 hy hyx (h := fun ε => ε ^ (-bp1Exp κ))
        (A := 2 * (x - y) ^ (-bp1Exp κ)) (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hp))
        fun ε hε n => ?_
      have := bp1_event_bound hB'' hB''m hB''c hB''0 hκ hlt (c := y / ((n : ℝ) + 1))
        (by positivity) hε.1 (hy' n) hε.2.le (n : ℝ≥0)
      rwa [NNReal.coe_natCast] at this
    · subst h4
      refine ae_bp_of_bound hB''c hB''0 hy hyx
        (h := fun ε => Real.log (x - y + 1) - Real.log ε)
        (A := Real.log (x - y + 1) - Real.log (x - y) + 3) ?_ fun ε hε n => ?_
      · have h := tendsto_atTop_add_const_left _ (Real.log (x - y + 1))
          (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
        refine h.congr fun ε => ?_
        simp [sub_eq_add_neg]
      · have := bp4_event_bound hB'' hB''m hB''c hB''0 (c := y / ((n : ℝ) + 1))
          (by positivity) hε.1 (hy' n) hε.2.le (n : ℝ≥0)
        rwa [NNReal.coe_natCast] at this
  filter_upwards [hmain, hBB] with ω hω hBω
  have hdrive : drive κ B ω = sDrive (√κ) B'' ω := funext fun t => by
    simp [drive, sDrive, hBω]
  rw [hdrive]
  exact hω

end RS
end QuantumZipper
