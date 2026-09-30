import QuantumZipper.Proofs.RS.BasePointPath
import QuantumZipper.Proofs.RS.LocalDynkinSuper

/-!
# RS BP1: the hitting estimate from the super-Dynkin formula

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §4, node BP1 (with §2, node P1).

`bp_hit_bound`: let `F` be `C³` on `bpDom = {0 < O < X}` with `dynkinGen (bpDrift c)
(bpNoise κ) F ≤ 0` where `c ≤ O < X` (a supersolution for the three-point state
`(X, O, L) = (f_t x, f_t y, log f_t' x)`), and on `K = {c ≤ O, ε ≤ Υ ≤ R}` let
`m ≤ F ≤ M` in absolute value, with `F ≥ a` on `K ∩ {Υ = ε}`. If `0 < c ≤ y`,
`ε ≤ x − y < R`, then the probability that `Υ_t ≤ ε` at some `t ≤ T` while `X, O > c` on
`[0,t]` is at most `(F(x,y,0) − m)/(a − m)`.

Proof: optional stopping for `F` (RS P1, `integral_localDynkin_stopped_le`) at the exit time
`τ` of the tamed state from `K`; on the event, the tamed state is the Loewner flow up to `t`
(`bpUpsPath_eq_bpUps`), `Υ ≤ x − y < R` (`bpUps_bpTamed_le`), `O > c`, so the exit is through
`{Υ = ε}` and `F(U_τ) ≥ a`; then Markov's inequality.

This is the optional-stopping step of Rohde–Schramm, *Basic properties of SLE*,
Ann. Math. 161 (2005), Lemma 7.2 proof, p. 33 ("there is an increasing sequence of stopping
times `t_n` … `E[Q(t_n)] = E[G_{t_n}] + Q(0) − G_0`"), in the Itô-free form of the project.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace RS

/-- The stopping region `K = {c ≤ O, ε ≤ Υ ≤ R}`. -/
def bpK (c ε R : ℝ) : Set (ℝ × ℝ × ℝ) := {v | c ≤ v.2.1 ∧ ε ≤ bpUps v ∧ bpUps v ≤ R}

/-- The exit set `{O ≤ c} ∪ {Υ ≤ ε} ∪ {Υ ≥ R}`. -/
def bpCl (c ε R : ℝ) : Set (ℝ × ℝ × ℝ) := {v | v.2.1 ≤ c ∨ bpUps v ≤ ε ∨ R ≤ bpUps v}

theorem isClosed_bpK (c ε R : ℝ) : IsClosed (bpK c ε R) := by
  have h := contDiff_bpUps.continuous
  exact (isClosed_le continuous_const (continuous_fst.comp continuous_snd)).inter
    ((isClosed_le continuous_const h).inter (isClosed_le h continuous_const))

theorem isClosed_bpCl (c ε R : ℝ) : IsClosed (bpCl c ε R) := by
  have h := contDiff_bpUps.continuous
  exact (isClosed_le (continuous_fst.comp continuous_snd) continuous_const).union
    ((isClosed_le h continuous_const).union (isClosed_le continuous_const h))

theorem bpK_subset {c ε R : ℝ} (hc : 0 < c) (hε : 0 < ε) : bpK c ε R ⊆ bpDom := by
  intro v hv
  refine ⟨hc.trans_le hv.1, ?_⟩
  have h : 0 < (v.1 - v.2.1) * Real.exp (-v.2.2) := hε.trans_le hv.2.1
  have := (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 h
  linarith

theorem hittingBtwn_mem_bp {X : ℝ≥0 → Ω → ℝ × ℝ × ℝ} {S : Set (ℝ × ℝ × ℝ)} (hS : IsClosed S)
    {ω : Ω} (hc : Continuous (X · ω)) {T : ℝ≥0} (hex : ∃ j ∈ Icc 0 T, X j ω ∈ S) :
    X (hittingBtwn X S 0 T ω) ω ∈ S := by
  classical
  rw [hittingBtwn_def]
  simp only [if_pos hex]
  obtain ⟨j, hj, hjS⟩ := hex
  have hcl : IsClosed (Icc 0 T ∩ {i : ℝ≥0 | X i ω ∈ S}) :=
    isClosed_Icc.inter (hS.preimage hc)
  exact (hcl.csInf_mem ⟨j, hj, hjS⟩ ⟨0, fun _ h => h.1.1⟩).2

section Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit mΩ in
/-- The event: `Υ_t ≤ ε` for some `t ≤ T`, while `X, O > c` on `[0,t]` (flow driven by
`s B`). -/
def bpEvent (s c ε x y : ℝ) (B : ℝ≥0 → Ω → ℝ) (T : ℝ) : Set Ω :=
  {ω | ∃ t ∈ Icc (0 : ℝ) T, ∃ u v : ℝ → ℂ, IsForwardSol (sDrive s B ω) (x : ℂ) t u ∧
    IsForwardSol (sDrive s B ω) (y : ℂ) t v ∧
    (∀ r ∈ Icc (0 : ℝ) t, c < (u r).re ∧ c < (v r).re) ∧ bpUpsPath u v t ≤ ε}

omit mΩ in
/-- The tamed state driven by `√κ B` solves `U = (x,y,0) + ∫ bpDrift c (U) + B • bpNoise κ`. -/
theorem bpTamed_integralEq (hBc : ∀ ω, Continuous (B · ω)) (κ : ℝ) {c : ℝ} (hc : 0 < c)
    (x y : ℝ) (ω : Ω) (t : ℝ≥0) :
    bpTamed (sDrive (√κ) B ω) c x y t = (x, y, 0) +
      (∫ r in (0 : ℝ)..t, bpDrift c (bpTamed (sDrive (√κ) B ω) c x y (r.toNNReal : ℝ))) +
      B t ω • bpNoise κ := by
  set W := sDrive (√κ) B ω with hW_def
  have hW : Continuous W := continuous_sDrive hBc _ ω
  have hX := continuous_realTamed_toNNReal hW hc x
  have hO := continuous_realTamed_toNNReal hW hc y
  have hpos : ∀ z : ℝ, max z c ≠ 0 := fun z => (hc.trans_le (le_max_right _ _)).ne'
  have hgc : Continuous fun r : ℝ => bpDrift c (bpTamed W c x y (r.toNNReal : ℝ)) := by
    show Continuous fun r : ℝ => (2 / max (realTamed W c x (r.toNNReal : ℝ)) c,
      2 / max (realTamed W c y (r.toNNReal : ℝ)) c,
      -2 / max (realTamed W c x (r.toNNReal : ℝ)) c ^ 2)
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
    · exact continuous_const.div (hX.max continuous_const) fun r => hpos _
    · exact continuous_const.div (hO.max continuous_const) fun r => hpos _
    · exact continuous_const.div ((hX.max continuous_const).pow 2) fun r => pow_ne_zero 2 (hpos _)
  have hint := hgc.intervalIntegrable (μ := volume) 0 t
  have hcongr : ∀ (φ : ℝ → ℝ), (∫ r in (0 : ℝ)..t, φ (realTamed W c x (r.toNNReal : ℝ))) =
      ∫ r in (0 : ℝ)..t, φ (realTamed W c x r) := fun φ => by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le t.coe_nonneg] at hr
    simp only [Real.coe_toNNReal r hr.1]
  have h1 : (∫ r in (0 : ℝ)..t, bpDrift c (bpTamed W c x y (r.toNNReal : ℝ))).1 =
      ∫ r in (0 : ℝ)..t, realDrift c (realTamed W c x r) := by
    have := ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).intervalIntegral_comp_comm hint).symm
    simp only [ContinuousLinearMap.coe_fst'] at this
    rw [this]
    exact hcongr (realDrift c)
  have h2 : (∫ r in (0 : ℝ)..t, bpDrift c (bpTamed W c x y (r.toNNReal : ℝ))).2.1 =
      ∫ r in (0 : ℝ)..t, realDrift c (realTamed W c y r) := by
    have := (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).intervalIntegral_comp_comm hint).symm
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Function.comp_apply] at this
    rw [this]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le t.coe_nonneg] at hr
    simp only [bpDrift, bpTamed, Real.coe_toNNReal r hr.1, realDrift]
  have h3 : (∫ r in (0 : ℝ)..t, bpDrift c (bpTamed W c x y (r.toNNReal : ℝ))).2.2 =
      bpTamedL W c x t := by
    have := (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).intervalIntegral_comp_comm hint).symm
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_snd',
      Function.comp_apply] at this
    rw [this, bpTamedL, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le t.coe_nonneg] at hr
    simp only [bpDrift, bpTamed, Real.coe_toNNReal r hr.1, neg_div]
  have hWt : W t = √κ * B t ω := by simp [hW_def, sDrive]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.fst_add, Prod.smul_fst, bpNoise, h1, smul_eq_mul]
    show realTamed W c x t = _
    rw [realTamed_eq hW hc x t.coe_nonneg, hWt]
    unfold realDrift; ring
  · simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, bpNoise, h2,
      smul_eq_mul]
    show realTamed W c y t = _
    rw [realTamed_eq hW hc y t.coe_nonneg, hWt]
    unfold realDrift; ring
  · simp only [Prod.snd_add, Prod.smul_snd, bpNoise, h3, smul_zero, add_zero, zero_add]
    rfl

/-- **The hitting estimate** (optional stopping for a supersolution of the three-point state;
RS Lemma 7.2 proof, p. 33, in the Itô-free form of RS P1). -/
theorem bp_hit_bound (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} {x y c ε R : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hcy : c ≤ y) (hεxy : ε ≤ x - y) (hR : x - y < R) (T : ℝ≥0)
    {F : ℝ × ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ 3 F bpDom)
    (hLF : ∀ v : ℝ × ℝ × ℝ, c ≤ v.2.1 → v.2.1 < v.1 → dynkinGen (bpDrift c) (bpNoise κ) F v ≤ 0)
    {M m a : ℝ} (hFM : ∀ v ∈ bpK c ε R, |F v| ≤ M) (hFm : ∀ v ∈ bpK c ε R, m ≤ F v)
    (hFa : ∀ v ∈ bpK c ε R, bpUps v = ε → a ≤ F v) (hma : m ≤ a) :
    (a - m) * P.real (bpEvent (√κ) c ε x y B T) ≤ F (x, y, 0) - m := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set U : ℝ≥0 → Ω → ℝ × ℝ × ℝ := fun t ω => bpTamed (sDrive (√κ) B ω) c x y t with hU_def
  have hU : ∀ ω (t : ℝ≥0), U t ω = (x, y, 0) + (∫ r in (0 : ℝ)..t, bpDrift c (U r.toNNReal ω))
      + B t ω • bpNoise κ := fun ω t => bpTamed_integralEq hBc κ hc x y ω t
  have hb := lipschitz_bpDrift hc
  have hbM := norm_bpDrift_le hc
  have hUc : ∀ ω, Continuous (U · ω) :=
    Dynkin.continuous_of_integralEq hBc hb.continuous hbM hU
  set 𝓕 := NonSwallow.bmFilt hBm
  have hUad : Adapted 𝓕 U := Dynkin.measurable_of_integralEq 𝓕 (NonSwallow.bmFilt_adapted hBm)
    hBc hb hbM hU hUc
  have hU0 : ∀ ω, U 0 ω = (x, y, 0) := fun ω => by rw [hU ω 0]; simp [hB0 ω]
  have hK := isClosed_bpK c ε R
  have hCl := isClosed_bpCl c ε R
  have hKO := bpK_subset (R := R) hc hε
  have hu0 : bpUps (x, y, 0) = x - y := by simp [bpUps]
  have hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ bpCl c ε R) → U t ω ∈ bpK c ε R := by
    intro ω t _ ht
    have hsub : Iio t ⊆ (fun s => U s ω) ⁻¹' bpK c ε R := by
      intro s hs
      have := ht s hs
      simp only [bpCl, mem_ofPred_eq, not_or, not_le] at this
      exact ⟨this.1.le, this.2.1.le, this.2.2.le⟩
    rcases eq_or_ne t 0 with h0 | hne
    · rw [h0, hU0]; exact ⟨hcy, by rw [hu0]; exact hεxy, by rw [hu0]; exact hR.le⟩
    have hcl := closure_minimal hsub (hK.preimage (hUc ω))
    have hne' : (Iio t).Nonempty := ⟨0, show (0 : ℝ≥0) < t from pos_iff_ne_zero.2 hne⟩
    exact hcl (by rw [closure_Iio' hne']; exact mem_Iic.2 le_rfl)
  have hsup := integral_localDynkin_stopped_le hB hBc 𝓕 (NonSwallow.bmFilt_adapted hBm)
    (NonSwallow.bmFilt_le_past hBm) hb hbM hU isOpen_bpDom hCl hK hKO hF
    (fun v hv _ => hLF v hv.1 (bpK_subset hc hε hv).2) T hUK hFM
  set τ := hittingBtwn U (bpCl c ε R) 0 T with hτ_def
  have hτT : ∀ ω, τ ω ≤ T := fun ω => hittingBtwn_le ω
  have hfK : ∀ ω, U (min T (τ ω)) ω ∈ bpK c ε R := fun ω => by
    rw [min_eq_right (hτT ω)]
    exact hUK ω _ (hτT ω) fun q hq => notMem_of_lt_hittingBtwn hq (zero_le)
  -- integrability of the stopped value
  have hτst : IsStoppingTime 𝓕 (fun ω => ((τ ω : ℝ≥0) : WithTop ℝ≥0)) :=
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUad hUc hCl T
  have hprog : IsStronglyProgressive 𝓕 U :=
    (hUad.stronglyAdapted).isStronglyProgressive_of_continuous hUc
  have hgm : StronglyMeasurable fun ω => U (min T (τ ω)) ω := by
    have h := hprog.stronglyMeasurable_stoppedProcess hτst T
    have heq : stoppedProcess U (fun ω => ((τ ω : ℝ≥0) : WithTop ℝ≥0)) T =
        fun ω => U (min T (τ ω)) ω := by
      funext ω
      simp only [stoppedProcess, ← WithTop.coe_min]
      rfl
    rw [heq] at h
    exact h
  classical
  have hF'm : Measurable (bpDom.piecewise F 0) :=
    ContinuousOn.measurable_piecewise hF.continuousOn continuousOn_const
      isOpen_bpDom.measurableSet
  have hfeq : (fun ω => F (U (min T (τ ω)) ω)) =
      fun ω => bpDom.piecewise F 0 (U (min T (τ ω)) ω) := by
    funext ω; rw [piecewise_eq_of_mem _ _ _ (hKO (hfK ω))]
  have hfsm : StronglyMeasurable fun ω => F (U (min T (τ ω)) ω) := by
    rw [hfeq]; exact (hF'm.comp hgm.measurable).stronglyMeasurable
  have hfi : Integrable (fun ω => F (U (min T (τ ω)) ω)) P :=
    ItoLite.integrable_of_bound_abs hfsm fun ω => hFM _ (hfK ω)
  -- Markov
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun ω => F (U (min T (τ ω)) ω) - m)
    (ae_of_all _ fun ω => sub_nonneg.2 (hFm _ (hfK ω))) (hfi.sub (integrable_const m)) (a - m)
  rw [integral_sub hfi (integrable_const m), integral_const, probReal_univ, one_smul] at hmk
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono ?_) (sub_nonneg.2 hma))
    (hmk.trans (by linarith))
  -- on the event, the stopped value lies on `{Υ = ε}`
  intro ω ⟨t, ht, u, v, hu, hv, hgt, hle⟩
  show a - m ≤ F (U (min T (τ ω)) ω) - m
  set W := sDrive (√κ) B ω
  have hW : Continuous W := continuous_sDrive hBc _ ω
  have hge : ∀ r ∈ Icc (0 : ℝ) t, c ≤ (u r).re ∧ c ≤ (v r).re := fun r hr =>
    ⟨(hgt r hr).1.le, (hgt r hr).2.le⟩
  obtain ⟨hpath, htame⟩ := bpUpsPath_eq_bpUps hW hc ht.1 hu hv hge
  have hmono := bpUps_bpTamed_le hW hc ht.1 x y htame
  have ev := realTamed_eq_of_isForwardSol hW hc ht.1 hv fun r hr => (hge r hr).2
  set t' : ℝ≥0 := t.toNNReal
  have ht' : (t' : ℝ) = t := Real.coe_toNNReal t ht.1
  have ht'T : t' ≤ T := by
    rw [← NNReal.coe_le_coe, ht']; exact ht.2
  have hmemt : U t' ω ∈ bpCl c ε R := by
    right; left
    show bpUps (bpTamed W c x y t') ≤ ε
    rw [ht', ← hpath]; exact hle
  have hτt : τ ω ≤ t' := hittingBtwn_le_of_mem zero_le ht'T hmemt
  have hτr : ((τ ω : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) t :=
    ⟨(τ ω).coe_nonneg, by rw [← ht']; exact_mod_cast hτt⟩
  have hmemCl := hittingBtwn_mem_bp hCl (hUc ω) ⟨t', ⟨zero_le, ht'T⟩, hmemt⟩
  have hmemK := hfK ω
  rw [min_eq_right (hτT ω)] at hmemK ⊢
  have hOgt : c < (U (τ ω) ω).2.1 := by
    show c < realTamed W c y (τ ω)
    have := (hgt _ hτr).2
    rw [ev _ hτr] at this
    simpa using this
  have hUle : bpUps (U (τ ω) ω) ≤ x - y := hmono _ hτr
  have hUeq : bpUps (U (τ ω) ω) = ε := by
    rcases hmemCl with h | h | h
    · exact absurd h (not_le.2 hOgt)
    · exact le_antisymm h hmemK.2.1
    · exact absurd (h.trans hUle) (not_le.2 hR)
  linarith [hFa _ hmemK hUeq]

end Prob

end RS
end QuantumZipper
