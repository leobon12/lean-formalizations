import InteractingSLE.SLE8.ChangeOfMeasure.Tilt
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.Zipper.UnzipInvariance

/-!
# SLE₈ note, Lemma 3.1: the critical change of measure

SLE₈ note `source/sle8-continuity.pdf`, §3.1, pp. 4–5 (transcription `source/sle8/sle8-continuity.md`,
anchors `lem-3.1`, `lem-3.1-proof`).

> **Lemma 3.1** (Critical change of measure). *For each `T ∈ [0, 1]` and `y ∈ (0, 1]`, the
> height-parameter process has a construction on the deterministic interval `[u₀, U]` for which `τ_T`
> is a bounded stopping time. There is a probability measure `ℚ` on this interval under which
> `(J_{u₀+v})_{0 ≤ v ≤ U − u₀}` is a Brownian motion of variance rate `4`, started at `0`. For every
> `a ∈ (0, 1)` and `E ∈ 𝓕_{τ_T}` with `E ⊂ {y Φ_T ≥ a}`, `P(E) ≤ y² a⁻² ℚ(E)` (3.2). On
> `{y Φ_T ≥ a}`, `τ_T ≥ log a` and `∫_{u₀}^{τ_T} 1{|J_u| ≤ 1} du ≤ C_occ (1 + log(1/a))` (3.3), where
> `C_occ` is a universal deterministic constant.*

Here `u₀ = log y`, `U = log √5`, `J_u = arsinh (X_s / Y_s)`, `Φ̂_u = Φ_s` at `u = log Y_s`, and
`τ_T = log Y_T`, for the reverse flow `Z_s = X_s + i Y_s` of (2.5)–(2.6) from `iy` driven by
`V_s = W_{T−s} − W_T`, `W = √8 B` (`revMap (revDriver (drive 8 B ω) T) s (iy)`), and
`Φ_T = |F_T'(iy)|`, `F_T = fwdMapInv (drive 8 B ω) T` (the carriers of the frozen SLE₈ anchor).

## The construction

The given Brownian motion `B` is replaced by a continuous version `B'`, reversed at `T`
(`UnzipInvariance.revBM B' T`, a Brownian motion on `ℝ≥0` that drives the note's reverse flow on `[0, T]`
and continues it afterwards), and modified on the null set where the continued flow never reaches
height `√5` (`measure_not_reachesTop`). The resulting `B₃` (`goodBM`) has every path continuous and its
flow reaches `√5` along every path; on a set of full measure its flow is the note's flow on `[0, T]`.
Then `InteractingSLE.SLE8.ChangeOfMeasure.Tilt` gives the filtration `𝓖_v = 𝓕_{𝔰⁻¹(u₀ + v)}`, the
processes, `ℚ = 𝓜_U · P` and the Brownian motion `β` with `J_{u₀+v} = 2 β_v` on `[0, U − u₀]`.

## Fidelity notes

* The filtration is the natural filtration of the driving Brownian motion read at the height clock; the
  height-parameter process is adapted to it, so every event of the natural filtration of `(J, Φ̂)` up to
  `τ_T` is admissible in (3.2). (The note's usual augmentation adds null sets only.)
* (3.2) is proved for every `a > 0` (the note: `a ∈ (0, 1)`) and for `E` contained in `{y Φ_T ≥ a}` up to
  a `P`-null set.
* `β` is a Brownian motion on all of `ℝ≥0` under `ℚ` (continued after `U − u₀` by independent increments),
  which contains the note's statement on `[0, U − u₀]` and is the form used in Step 4 of Proposition 4.1.
* `C_occ = cosh² 1 / 2` (`ChangeOfMeasure.occConst`).
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal

namespace InteractingSLE.SLE8

open QuantumZipper ChangeOfMeasure

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

namespace ChangeOfMeasure

/-! ### The modified Brownian motion -/

/-- The set where the height of the flow driven by `√8 B` never reaches `√5`. -/
def notReach (B : ℝ≥0 → Ω → ℝ) (y : ℝ) : Set Ω :=
  {ω | ∀ s : ℝ≥0, (htZ (drive 8 B ω) y s).im < √5}

open Classical in
/-- `B` modified to vanish on `notReach B y`. -/
def goodBM (B : ℝ≥0 → Ω → ℝ) (y : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ notReach B y then 0 else B t ω

theorem measurableSet_notReach {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t)) {y : ℝ} (hy : 0 < y) : MeasurableSet (notReach B y) := by
  have : notReach B y = ⋂ n : ℕ, {ω | (stProc B y (n : ℝ≥0) ω).1.im < √5} := by
    ext ω
    simp only [notReach, mem_ofPred_eq, mem_iInter, stProc_fst]
    refine ⟨fun h n => h n, fun h s => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (s : ℝ)
    have hsn : s ≤ (n : ℝ≥0) := by exact_mod_cast hn
    exact lt_of_le_of_lt (monotone_im_htZ_nnreal (continuous_drive8 hBc ω) hy hsn) (h n)
  rw [this]
  refine MeasurableSet.iInter fun n => measurableSet_lt ?_ measurable_const
  exact Complex.measurable_im.comp (measurable_fst.comp
    ((measurable_stProc hBc hBm hy _).mono ((NonSwallow.bmFilt hBm).le _) le_rfl))

section Good

variable {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
  {y : ℝ} (hy : 0 < y)
include hBc hBm hy

omit mΩ hBm hy in
theorem continuous_goodBM (ω : Ω) : Continuous (goodBM B y · ω) := by
  unfold goodBM
  split_ifs
  · exact continuous_const
  · exact hBc ω

theorem measurable_goodBM (t : ℝ≥0) : Measurable (goodBM B y t) :=
  Measurable.ite (measurableSet_notReach hBc hBm hy) measurable_const (hBm t)

omit mΩ hBc hBm hy in
theorem goodBM_eq_of_not_mem {ω : Ω} (hω : ω ∉ notReach B y) (t : ℝ≥0) :
    goodBM B y t ω = B t ω := by
  simp [goodBM, hω]

omit mΩ hBc hBm hy in
theorem drive_goodBM_of_not_mem {ω : Ω} (hω : ω ∉ notReach B y) :
    drive 8 (goodBM B y) ω = drive 8 B ω := by
  funext t
  simp only [drive, goodBM_eq_of_not_mem hω]

omit mΩ hBc hBm in
theorem reachesTop_goodBM (hy1 : y ≤ 1) : ReachesTop (goodBM B y) y := by
  intro ω
  by_cases hω : ω ∈ notReach B y
  · -- the zero driver: `X ≡ 0` and the height grows
    have hW : drive 8 (goodBM B y) ω = fun _ => 0 := by
      funext t
      simp [drive, goodBM, hω]
    by_contra hne
    push Not at hne
    have hc0 : Continuous (drive 8 (goodBM B y) ω) := by rw [hW]; exact continuous_const
    set s : ℝ := 5 / 2 * Real.log (√5 / y) + 1 with hs
    have hlog : 0 ≤ Real.log (√5 / y) := Real.log_nonneg (by
      rw [le_div_iff₀ hy, one_mul]; exact hy1.trans one_lt_sqrt_five.le)
    have hs0 : 0 ≤ s := by positivity
    have hcone : ∀ r ∈ Icc 0 s, |(htZ (drive 8 (goodBM B y) ω) y r).re| ≤
        0 * (htZ (drive 8 (goodBM B y) ω) y r).im ∧ (htZ (drive 8 (goodBM B y) ω) y r).im ≤ √5 := by
      intro r hr
      refine ⟨?_, ?_⟩
      · have := abs_re_revMap_mul_I_le hc0 hy hr.1 (m := 0) fun v _ => by rw [hW]; simp
        simp only [htZ] at this ⊢
        linarith
      · have := hne r.toNNReal
        rw [Real.coe_toNNReal r hr.1] at this
        exact this.le
    have h1 := im_ge_of_cone hc0 hy hs0 hcone
    have h2 := hne s.toNNReal
    rw [Real.coe_toNNReal s hs0] at h2
    have h3 : √5 ≤ y * Real.exp (2 * s / (5 * (1 + 0 ^ 2))) := by
      have : Real.log (√5 / y) ≤ 2 * s / (5 * (1 + 0 ^ 2)) := by
        simp only [hs]; norm_num; nlinarith
      calc √5 = y * Real.exp (Real.log (√5 / y)) := by
            rw [Real.exp_log (div_pos (by positivity) hy)]; field_simp
        _ ≤ _ := by gcongr
    linarith
  · simp only [notReach, mem_ofPred_eq, not_forall, not_lt] at hω
    obtain ⟨s, hs⟩ := hω
    refine ⟨s, ?_⟩
    rw [drive_goodBM_of_not_mem (by simp [notReach]; exact ⟨s, hs⟩)]
    exact hs

end Good

theorem isBrownianReal_goodBM {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t)) (hB0 : ∀ ω, B 0 ω = 0)
    {y : ℝ} (hy : 0 < y) (hy5 : y ≤ √5) : IsBrownianReal (goodBM B y) P where
  toIsPreBrownianReal := by
    refine hB.toIsPreBrownianReal.congr fun t => ?_
    have h0 := measure_not_reachesTop hB.toIsPreBrownianReal hBc hBm hB0 hy hy5
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
    exact (goodBM_eq_of_not_mem (by exact hω) t).symm
  cont := ae_of_all _ fun ω => continuous_goodBM hBc ω

/-! ### Transfer to the note's reverse flow -/

omit mΩ in
/-- On `[0, T]`, the reversed Brownian motion drives the note's reverse flow. -/
theorem revMap_drive_revBM {B : ℝ≥0 → Ω → ℝ} {T s : ℝ} (hT : 0 ≤ T) (hs : s ∈ Icc 0 T) (ω : Ω) :
    revMap (drive 8 (UnzipInvariance.revBM B T.toNNReal) ω) s =
      revMap (revDriver (drive 8 B ω) T) s := by
  funext z
  refine (ReverseFlow.revMap_congr_drive z fun r hr => ?_)
  have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans hs.2⟩
  have hle : r.toNNReal ≤ T.toNNReal := Real.toNNReal_le_toNNReal hr'.2
  have h1 : (T - r).toNNReal = T.toNNReal - r.toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (sub_nonneg.2 hr'.2), NNReal.coe_sub hle, Real.coe_toNNReal _ hr'.1,
      Real.coe_toNNReal _ hT]
  have h2 : max r.toNNReal T.toNNReal = T.toNNReal := max_eq_right hle
  simp only [drive, UnzipInvariance.revBM_apply, revDriver_apply, h1, h2]
  ring

/-- The height clock at `log (Y_s / y)` is `s`, and the state there is the state at `s`. -/
theorem stProc_vClock_termLevel {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω)) {y : ℝ}
    (hy : 0 < y) (hy1 : y ≤ 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ω : Ω) :
    stProc B y (vClock B y (min (termLevel B y s ω) (vTop y)) ω) ω = stProc B y s.toNNReal ω := by
  rw [min_eq_left (termLevel_le hBc hy hy1 hs ω)]
  congr 1
  apply NNReal.eq
  rw [vClock_termLevel hBc hy hy1 hs ω, Real.coe_toNNReal s hs.1]

theorem log_im_eq_termLevel {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω)) {y : ℝ}
    (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    Real.log (htZ (drive 8 B ω) y s).im = Real.log y + termLevel B y s ω := by
  have hW := continuous_drive8 hBc ω
  have hY := im_htZ_pos hW hy hs
  rw [termLevel, Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hy).2 (le_im_htZ hW hy hs))),
    Real.log_div hY.ne' hy.ne']
  ring

/-- The height level of the clock above `u₀`: `y e^{min (u − u₀) (U − u₀)} = e^{min u U}`. -/
theorem level_eq_exp_min {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) {u : ℝ} (hu : Real.log y ≤ u) :
    y * Real.exp ((min (u - Real.log y).toNNReal (vTop y) : ℝ≥0) : ℝ) =
      Real.exp (min u (Real.log √5)) := by
  have hv : ((u - Real.log y).toNNReal : ℝ) = u - Real.log y := Real.coe_toNNReal _ (sub_nonneg.2 hu)
  rw [NNReal.coe_min, hv, coe_vTop hy hy1, Real.log_div (by positivity) hy.ne', min_sub_sub_right]
  calc y * Real.exp (min u (Real.log √5) - Real.log y)
      = Real.exp (Real.log y) * Real.exp (min u (Real.log √5) - Real.log y) := by
        rw [Real.exp_log hy]
    _ = Real.exp (min u (Real.log √5)) := by rw [← Real.exp_add]; ring_nf

omit mΩ in
/-- The height-parameter path agrees with `htJ` above `u₀`. -/
theorem vJ_eq_htJ {B : ℝ≥0 → Ω → ℝ} {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) {u : ℝ}
    (hu : Real.log y ≤ u) (ω : Ω) :
    vJ B y (u - Real.log y).toNNReal ω = htJ (drive 8 B ω) y (Real.log √5) u := by
  rw [vJ, htJ, vClock_of_le _ (min_le_right _ _), stProc_fst, level_eq_exp_min hy hy1 hu]

end ChangeOfMeasure

/-! ### Lemma 3.1 -/

/-- **Lemma 3.1 of the SLE₈ note** (critical change of measure, p. 4). For each `T ∈ [0, 1]` and
`y ∈ (0, 1]`, with `u₀ = log y`, `U = log √5`, the reverse flow `Z_s = X_s + i Y_s` from `iy` driven by
`V_s = W_{T−s} − W_T`, `W = √8 B`, and `Φ_T = |F_T'(iy)|`:

* (*construction*) there are a filtration `𝓖` (indexed by the shifted height parameter `v = u − u₀`),
  continuous processes `J, Φ̂` adapted to it with `J_u = arsinh (X_s / Y_s)` and `Φ̂_u = Φ_s` at
  `u = log Y_s` for `s ∈ [0, T]` (a.s.), and `τ_T = log Y_T ∈ [u₀, U]` with `τ_T − u₀` a `𝓖`-stopping
  time and `Φ̂_{τ_T} = Φ_T` (a.s.);
* (*the measure `ℚ`*) a probability measure `ℚ` and a `ℚ`-Brownian motion `β` (continuous paths,
  `𝓖`-adapted) with `J_{u₀} = 0` and `J_{u₀+v} = 2 β_v` for `0 ≤ v ≤ U − u₀`, i.e. `(J_{u₀+v})` is a
  Brownian motion of variance rate `4` started at `0` under `ℚ`;
* (**3.2**) for `a > 0` and `E ∈ 𝓖_{τ_T}` with `y Φ_T ≥ a` (a.s.) on `E`: `P(E) ≤ y² a⁻² ℚ(E)`;
* (**3.3**) for `a ∈ (0, 1)`, a.s. on `{y Φ_T ≥ a}`: `τ_T ≥ log a` and
  `∫_{u₀}^{τ_T} 1{|J_u| ≤ 1} du ≤ C_occ (1 + log (1/a))` with `C_occ = cosh² 1 / 2`. -/
theorem exists_criticalChangeOfMeasure {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {T : ℝ}
    (hT : T ∈ Icc (0 : ℝ) 1) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) :
    ∃ (𝓖 : Filtration ℝ≥0 mΩ) (J Φ : ℝ → Ω → ℝ) (τ : Ω → ℝ)
      (hτ : IsStoppingTime 𝓖 fun ω => ((τ ω - Real.log y).toNNReal : WithTop ℝ≥0))
      (Q : Measure Ω) (β : ℝ≥0 → Ω → ℝ),
      -- the height-parameter process on `[u₀, U]` and the bounded stopping time `τ_T`
      (∀ ω, Continuous fun u => J u ω) ∧ (∀ ω, Continuous fun u => Φ u ω) ∧
      (∀ v : ℝ≥0, Measurable[𝓖 v] (J (Real.log y + v))) ∧
      (∀ v : ℝ≥0, Measurable[𝓖 v] (Φ (Real.log y + v))) ∧
      (∀ ω, τ ω ∈ Icc (Real.log y) (Real.log √5)) ∧
      (∀ᵐ ω ∂P, ∀ s ∈ Icc (0 : ℝ) T,
        J (Real.log (revMap (revDriver (drive 8 B ω) T) s ((y : ℂ) * I)).im) ω =
          Real.arsinh ((revMap (revDriver (drive 8 B ω) T) s ((y : ℂ) * I)).re /
            (revMap (revDriver (drive 8 B ω) T) s ((y : ℂ) * I)).im) ∧
        Φ (Real.log (revMap (revDriver (drive 8 B ω) T) s ((y : ℂ) * I)).im) ω =
          ‖deriv (revMap (revDriver (drive 8 B ω) T) s) ((y : ℂ) * I)‖) ∧
      (∀ᵐ ω ∂P, τ ω = Real.log (revMap (revDriver (drive 8 B ω) T) T ((y : ℂ) * I)).im ∧
        Φ (τ ω) ω = ‖deriv (fwdMapInv (drive 8 B ω) T) ((y : ℂ) * I)‖) ∧
      -- the measure `ℚ`
      IsProbabilityMeasure Q ∧ IsBrownianReal β Q ∧ (∀ ω, Continuous fun v => β v ω) ∧
      (∀ v : ℝ≥0, Measurable[𝓖 v] (β v)) ∧ (∀ ω, J (Real.log y) ω = 0) ∧
      (∀ ω, ∀ v : ℝ≥0, (v : ℝ) ≤ Real.log √5 - Real.log y → J (Real.log y + v) ω = 2 * β v ω) ∧
      -- (3.2)
      (∀ a : ℝ, 0 < a → ∀ E : Set Ω, MeasurableSet[hτ.measurableSpace] E →
        (∀ᵐ ω ∂P, ω ∈ E → a ≤ y * ‖deriv (fwdMapInv (drive 8 B ω) T) ((y : ℂ) * I)‖) →
        P E ≤ ENNReal.ofReal (y ^ 2 * a ^ (-2 : ℝ)) * Q E) ∧
      -- (3.3)
      (∀ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P,
        a ≤ y * ‖deriv (fwdMapInv (drive 8 B ω) T) ((y : ℂ) * I)‖ →
        Real.log a ≤ τ ω ∧
        volume {u | u ∈ Icc (Real.log y) (τ ω) ∧ |J u ω| ≤ 1} ≤
          ENNReal.ofReal (occConst * (1 + Real.log (1 / a)))) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hy5 : y ≤ √5 := y_le_sqrt5 hy1
  -- a continuous version, reversed at `T`
  obtain ⟨B', hB'm, hB'c, hB'0, hB'B, hB'eq⟩ := RS.exists_good_version0 hB
  set B₂ := UnzipInvariance.revBM B' T.toNNReal with hB₂def
  have hB₂ : IsBrownianReal B₂ P :=
    UnzipInvariance.isBrownianReal_revBM hB'B.toIsPreBrownianReal hB'c _
  have hB₂c : ∀ ω, Continuous (B₂ · ω) := fun ω => by
    simp only [hB₂def, UnzipInvariance.revBM_apply]
    exact (((hB'c ω).comp (continuous_const.sub continuous_id)).add
      ((hB'c ω).comp (continuous_id.max continuous_const))).sub continuous_const
  have hB₂m : ∀ t, Measurable (B₂ t) := fun t => by
    simp only [hB₂def, UnzipInvariance.revBM]
    exact ((hB'm _).add (hB'm _)).sub ((hB'm _).const_smul _)
  have hB₂0 : ∀ ω, B₂ 0 ω = 0 := fun ω => by
    simp only [hB₂def, UnzipInvariance.revBM_apply, tsub_zero,
      max_eq_right (zero_le : (0 : ℝ≥0) ≤ T.toNNReal)]
    ring
  -- the modification that always reaches height `√5`
  set B₃ := ChangeOfMeasure.goodBM B₂ y with hB₃def
  have hB₃ : IsBrownianReal B₃ P :=
    ChangeOfMeasure.isBrownianReal_goodBM hB₂ hB₂c hB₂m hB₂0 hy0 hy5
  have hB₃c : ∀ ω, Continuous (B₃ · ω) := ChangeOfMeasure.continuous_goodBM hB₂c
  have hB₃m : ∀ t, Measurable (B₃ t) := ChangeOfMeasure.measurable_goodBM hB₂c hB₂m hy0
  have hB₃0 : ∀ ω, B₃ 0 ω = 0 := fun ω => by
    simp only [hB₃def, ChangeOfMeasure.goodBM]; split_ifs <;> simp [hB₂0]
  have hreach : ReachesTop B₃ y := ChangeOfMeasure.reachesTop_goodBM hy0 hy1
  have hBpre := hB₃.toIsPreBrownianReal
  -- the good set
  have hgood : ∀ᵐ ω ∂P, (∀ t, B' t ω = B t ω) ∧ ω ∉ ChangeOfMeasure.notReach B₂ y := by
    have h0 := measure_not_reachesTop hB₂.toIsPreBrownianReal hB₂c hB₂m hB₂0 hy0 hy5
    filter_upwards [hB'eq, measure_eq_zero_iff_ae_notMem.1 h0] with ω h1 h2
    exact ⟨h1, h2⟩
  -- on the good set the flow of `B₃` is the note's flow on `[0, T]`
  have hflow : ∀ ω, (∀ t, B' t ω = B t ω) → ω ∉ ChangeOfMeasure.notReach B₂ y →
      ∀ s ∈ Icc (0 : ℝ) T, revMap (drive 8 B₃ ω) s = revMap (revDriver (drive 8 B ω) T) s := by
    intro ω h1 h2 s hs
    have hd : drive 8 B' ω = drive 8 B ω := by funext t; simp only [drive, h1]
    rw [hB₃def, ChangeOfMeasure.drive_goodBM_of_not_mem h2, hB₂def,
      ChangeOfMeasure.revMap_drive_revBM hT.1 hs, hd]
  have hWc : ∀ ω, (∀ t, B' t ω = B t ω) → Continuous (drive 8 B ω) := fun ω h1 => by
    have hd : drive 8 B' ω = drive 8 B ω := by funext t; simp only [drive, h1]
    rw [← hd]; exact continuous_drive8 hB'c ω
  have hW0 : ∀ ω, (∀ t, B' t ω = B t ω) → drive 8 B ω 0 = 0 := fun ω h1 => by
    simp only [drive, Real.toNNReal_zero, ← h1, hB'0, mul_zero]
  -- the objects
  set 𝓖 := vFilt hB₃c hB₃m hy0 hy1 hreach
  set J : ℝ → Ω → ℝ := fun u ω => vJ B₃ y (u - Real.log y).toNNReal ω with hJ
  set Φ : ℝ → Ω → ℝ := fun u ω => vPhi B₃ y (u - Real.log y).toNNReal ω with hΦ
  set τ : Ω → ℝ := fun ω => Real.log y + termLevel B₃ y T ω with hτdef
  have hτfun : (fun ω => ((τ ω - Real.log y).toNNReal : WithTop ℝ≥0)) =
      fun ω => ((termLevel B₃ y T ω : ℝ≥0) : WithTop ℝ≥0) := by
    funext ω; simp only [hτdef, add_sub_cancel_left, Real.toNNReal_coe]
  have hτst₀ := isStoppingTime_termLevel hB₃c hB₃m hy0 hy1 hreach hT
  have hτst : IsStoppingTime 𝓖 fun ω => ((τ ω - Real.log y).toNNReal : WithTop ℝ≥0) := by
    rw [hτfun]; exact hτst₀
  have hshift : ∀ v : ℝ≥0, (Real.log y + v - Real.log y).toNNReal = v := fun v => by
    rw [add_sub_cancel_left, Real.toNNReal_coe]
  refine ⟨𝓖, J, Φ, τ, hτst, tiltMeasure P B₃ y, tiltBM B₃ y, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    isProbabilityMeasure_tiltMeasure hBpre hB₃c hB₃m hB₃0 hy0 hy1 hreach,
    isBrownianReal_tiltBM hBpre hB₃c hB₃m hB₃0 hy0 hy1 hreach,
    continuous_tiltBM hB₃c hy0 hy1 hreach, measurable_tiltBM hB₃c hB₃m hy0 hy1 hreach, ?_, ?_, ?_,
    ?_⟩
  · -- continuity of `J`
    intro ω
    exact (continuous_vJ hB₃c hy0 hy1 hreach ω).comp
      (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  · intro ω
    exact (continuous_vPhi hB₃c hy0 hy1 hreach ω).comp
      (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  · intro v
    simp only [hJ, hshift]
    exact measurable_vJ hB₃c hB₃m hy0 hy1 hreach v
  · intro v
    simp only [hΦ, hshift]
    exact measurable_vPhi hB₃c hB₃m hy0 hy1 hreach v
  · intro ω
    refine ⟨le_add_of_nonneg_right (termLevel B₃ y T ω).coe_nonneg, ?_⟩
    have h := termLevel_le hB₃c hy0 hy1 hT ω
    have h' : ((termLevel B₃ y T ω : ℝ≥0) : ℝ) ≤ vTop y := by exact_mod_cast h
    rw [coe_vTop hy0 hy1, Real.log_div (by positivity) hy0.ne'] at h'
    simp only [hτdef]
    linarith
  · -- identification with the note's flow
    filter_upwards [hgood] with ω ⟨h1, h2⟩ s hs
    have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans hT.2⟩
    have hfl := hflow ω h1 h2 s hs
    have hZ : htZ (drive 8 B₃ ω) y s = revMap (revDriver (drive 8 B ω) T) s ((y : ℂ) * I) := by
      rw [htZ, hfl]
    have hlev := log_im_eq_termLevel hB₃c hy0 hs.1 ω
    rw [hZ] at hlev
    have hsv := ChangeOfMeasure.stProc_vClock_termLevel hB₃c hy0 hy1 hs1 ω
    have hTT : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs.1
    refine ⟨?_, ?_⟩
    · simp only [hJ, hlev, hshift, vJ]
      rw [hsv, stProc_fst, hTT, hZ]
      rfl
    · simp only [hΦ, hlev, hshift, vPhi, hsv]
      rw [snd_stProc_eq hB₃c hy0, hTT, hfl,
        Real.exp_log (norm_pos_iff.2 (deriv_revMap_ne_zero _
          (continuous_revDriver (hWc ω h1) T) hs.1 (mem_H_mul_I hy0)))]
  · -- `τ_T = log Y_T` and `Φ̂_{τ_T} = Φ_T`
    filter_upwards [hgood] with ω ⟨h1, h2⟩
    have hfl := hflow ω h1 h2 T ⟨hT.1, le_rfl⟩
    have hlev := log_im_eq_termLevel hB₃c hy0 hT.1 ω
    have hZ : htZ (drive 8 B₃ ω) y T = revMap (revDriver (drive 8 B ω) T) T ((y : ℂ) * I) := by
      rw [htZ, hfl]
    have hsv := ChangeOfMeasure.stProc_vClock_termLevel hB₃c hy0 hy1 hT ω
    have hTT : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT.1
    refine ⟨?_, ?_⟩
    · simp only [hτdef]; rw [hlev.symm.trans (by rw [hZ])]
    · simp only [hΦ, hτdef, hshift, vPhi, hsv]
      rw [snd_stProc_eq hB₃c hy0, hTT, hfl,
        Real.exp_log (norm_pos_iff.2 (deriv_revMap_ne_zero _
          (continuous_revDriver (hWc ω h1) T) hT.1 (mem_H_mul_I hy0))),
        norm_deriv_fwdMapInv_eq_norm_deriv_revFlow (hWc ω h1) (hW0 ω h1) hT.1 (mem_H_mul_I hy0),
        deriv_revFlow]
  · -- `J_{u₀} = 0`
    intro ω
    have h := tiltBM_zero hB₃c hy0 hy1 hB₃0 ω
    rw [tiltBM_of_le hy0 hy1 (zero_le : (0 : ℝ≥0) ≤ vTop y)] at h
    simp only [hJ, sub_self, Real.toNNReal_zero, vJ, min_eq_left (zero_le : (0 : ℝ≥0) ≤ vTop y)]
    linarith
  · -- `J = 2 β` below the horizon
    intro ω v hv
    have hv' : v ≤ vTop y := by
      rw [← NNReal.coe_le_coe, coe_vTop hy0 hy1, Real.log_div (by positivity) hy0.ne']
      exact hv
    simp only [hJ, hshift]
    rw [tiltBM_of_le hy0 hy1 hv', vJ, min_eq_left hv']
    ring
  · -- (3.2)
    intro a ha E hE hEa
    have hE' : MeasurableSet[hτst₀.measurableSpace] E :=
      IsStoppingTime.measurableSpace_mono hτst hτst₀ (fun ω => by rw [hτfun]) E hE
    refine measure_le_tilt hBpre hB₃c hB₃m hB₃0 hy0 hy1 hreach hT ha hE' ?_
    filter_upwards [hEa, hgood] with ω hω ⟨h1, h2⟩ hωE
    have hfl := hflow ω h1 h2 T ⟨hT.1, le_rfl⟩
    rw [hfl, ← deriv_revFlow, ← norm_deriv_fwdMapInv_eq_norm_deriv_revFlow (hWc ω h1) (hW0 ω h1)
      hT.1 (mem_H_mul_I hy0)]
    exact hω hωE
  · -- (3.3)
    intro a ha
    filter_upwards [hgood] with ω ⟨h1, h2⟩ hphi
    have hW3 := continuous_drive8 hB₃c ω
    have hfl := hflow ω h1 h2 T ⟨hT.1, le_rfl⟩
    have hphi' : a ≤ y * ‖deriv (revMap (drive 8 B₃ ω) T) ((y : ℂ) * I)‖ := by
      rw [hfl, ← deriv_revFlow, ← norm_deriv_fwdMapInv_eq_norm_deriv_revFlow (hWc ω h1)
        (hW0 ω h1) hT.1 (mem_H_mul_I hy0)]
      exact hphi
    have hYT := im_htZ_pos hW3 hy0 hT.1
    have hY5 : (htZ (drive 8 B₃ ω) y T).im ≤ √5 := by
      have h := im_htZ_sq_le hW3 hy0 hT.1
      rw [← Real.sqrt_sq hYT.le]
      exact Real.sqrt_le_sqrt (by nlinarith [hT.2])
    have hτeq : τ ω = Real.log (htZ (drive 8 B₃ ω) y T).im :=
      (log_im_eq_termLevel hB₃c hy0 hT.1 ω).symm
    refine ⟨?_, ?_⟩
    · rw [hτeq]
      have := phi_le_im_div hW3 hy0 hT.1
      have h3 : a ≤ (htZ (drive 8 B₃ ω) y T).im := by
        calc a ≤ y * ‖deriv (revMap (drive 8 B₃ ω) T) ((y : ℂ) * I)‖ := hphi'
          _ ≤ y * ((htZ (drive 8 B₃ ω) y T).im / y) := by gcongr
          _ = (htZ (drive 8 B₃ ω) y T).im := by field_simp
      exact Real.log_le_log ha.1 h3
    · have hocc := volume_occupation_le hW3 hy0 hT.1 (U := Real.log √5)
        (Real.log_le_log hYT hY5) hY5 ha.1 hphi'
      have hset : {u | u ∈ Icc (Real.log y) (τ ω) ∧ |J u ω| ≤ 1} =
          {u | u ∈ Icc (Real.log y) (Real.log (htZ (drive 8 B₃ ω) y T).im) ∧
            |htJ (drive 8 B₃ ω) y (Real.log √5) u| ≤ 1} := by
        ext u
        simp only [mem_ofPred_eq, mem_Icc, hτeq]
        constructor
        · rintro ⟨⟨hu1, hu2⟩, hu3⟩
          refine ⟨⟨hu1, hu2⟩, ?_⟩
          rwa [← ChangeOfMeasure.vJ_eq_htJ hy0 hy1 hu1]
        · rintro ⟨⟨hu1, hu2⟩, hu3⟩
          refine ⟨⟨hu1, hu2⟩, ?_⟩
          simp only [hJ]
          rwa [ChangeOfMeasure.vJ_eq_htJ hy0 hy1 hu1]
      rw [hset]
      refine hocc.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ occConst_pos.le))
      have h5 : Real.log √5 ≤ 1 := by
        rw [Real.log_sqrt (by norm_num)]
        have : Real.log 5 ≤ 2 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]
          have := Real.exp_one_gt_d9
          have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith [Real.exp_pos 1]
        linarith
      rw [one_div, Real.log_inv]
      linarith

end InteractingSLE.SLE8
