import QuantumZipper.Proofs.Section5.Prop16MarkovMask2
import QuantumZipper.Proofs.Section5.Prop17PalmCLog
import QuantumZipper.Proofs.Section5.Prop17PalmCReg
import QuantumZipper.Proofs.Zipper.D3PlusN1Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node C′ (masked): the Palm-Markov node from the harmonic Palm representative

Task P16-MARKOVMASK2. `prop16PalmMarkovCoupling_of_harm`: the Palm-Markov node
`Prop16PalmMarkovCouplingStmt` (pieces (b)–(d) of `Prop16NodeCMarkovMaskStmt`,
`Prop16MarkovMask2.lean`) follows from the domain Markov coupling `Prop16MixedFreeLocCouplingStmt`
(only for the local area limit, via local niceness) and the single analytic input
`Prop16PalmShiftHarmStmt` (near the free-arc point `x`, the Palm shift `(γ/2) G_D(x, ·)` is
`γ(−log‖· − x‖) + ψ(· − x)` with `ψ ∘ foldH` harmonic).

* **(d)** `aemeasurable_scaleParamOn_zoomModel_mm`: for *any* D3⁺ `Setup`, the local scale of the
  model field is a.e.-measurable: it equals a.s. the measurable surrogate `D3Plus.scaleSur` of the
  local data `(localZ, macroF)` (the argument of `D3Plus.nullMeasurableSet_badScale`).
* **RC1, uniformly in the mean**: `palmC_ae_evalReg_logAdd_unif_mm` is
  `S5.FieldLaw.Raw.palmC_ae_evalReg_logAdd` with the null set chosen independently of the pole,
  the coefficient and the continuous part (the proof there never uses them to choose the null
  set), so that it applies to the random correction `g ω` of the M7 coupling.
* **(b)** the `AgreeNear`: at the M7 data (`prop16_markovSetup_at`, radii `r = rH`, `r' = rH/2`,
  normalizing measure `ρ₀ = fc(x, 2 rH)`), on the dyadic circles inside `ball x (rH/4)` the
  Palm-shifted field `Y + (γ/2) G_D(x,·)` agrees (M7 identity + `Prop16PalmShiftHarmStmt`) with
  the split field `ofFun (−γ log‖· − x‖ + G̃) + X` where `G̃` is a Tietze extension of the
  continuous correction `ψ(· − x) + g − X ρ₀` from `closedBall x (rH/4) ∩ Hbar`; by locality of
  `evalReg` (`evalReg_eq_of_circAgree`) and RC1 the zoomed Palm field is regular at the dyadic
  circles of `ball 0 (rH/8)`, where it then equals the model field with `g' = g(· + x) + ψ + 𝔥₀(x)`
  (`D3Plus.Setup.mono_absorb`).

Sources: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25) (the conditional law given `x`
is the field plus `(γ/2) G_D(x, ·)`, and zooming in at `x`); Sheffield, *Gaussian free fields for
mathematicians*, PTRF 139 (2007), Thm 2.17 (domain Markov property, via M7). The bookkeeping
(countable a.s. assembly, Tietze extension, locality of `evalReg`) is an own argument, following
the Prop. 1.7 analogue `Prop17PalmCAgree.lean` / `Prop17PalmCReg.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Prop16Area.G TV Factorization

/-! ## (d) Measurability of the local scale of the D3⁺ model field -/

/-- **(d)** For any D3⁺ setup, the local scale of the model field is a.e.-measurable. -/
theorem aemeasurable_scaleParamOn_zoomModel_mm {γ α r : ℝ} {ρ₀ : Measure ℂ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    {E' : Type*} [MeasurableSpace E'] {Ξ : Ω → E'} {g : Ω → ℂ → ℝ}
    (hS : D3Plus.Setup γ α r ρ₀ P X Ξ g) (L : ℝ) :
    AEMeasurable (fun ω => scaleParamOn γ (D3Plus.zoomModel γ α L ρ₀ (X ω) (g ω))
      (D3Plus.halfDisc r)) P := by
  refine ⟨fun ω => D3Plus.scaleSur γ L r (D3Plus.localZ X r ω, D3Plus.macroF α r ρ₀ X g ω),
    (D3Plus.measurable_scaleSur γ L r).comp (D3Plus.measurable_localZ_macroF hS), ?_⟩
  filter_upwards [D3Plus.ae_exists_isVagueLimitOn_zoomModel hS] with ω hω
  have hag := D3Plus.agreeNear_zoomModel_locModel hS L ω
  have hgood := (D3Plus.exists_isVagueLimitOn_halfDisc_iff hag).1 (hω L)
  exact ((D3Plus.scaleSur_eq hgood).trans (D3Plus.scaleParamOn_halfDisc_congr hag).symm).symm

/-! ## RC1 with a logarithmic singularity, uniformly in the mean -/

open S5.FieldLaw.Raw FrostmanReg in
/-- `palmC_ae_evalReg_logAdd` with the null set independent of `a`, `t` and `g₁` (same proof). -/
theorem palmC_ae_evalReg_logAdd_unif_mm {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {ν : Measure ℂ}
    [IsFiniteMeasure ν] {α C R : ℝ} (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0)
    (h : IsFrostman ν α C) (hα : 0 < α) :
    ∀ᵐ ω ∂P, ∀ (a t : ℝ) (g₁ : ℂ → ℝ), ContinuousOn g₁ Hbar →
      evalReg (ofFun (fun v => a * Real.log ‖v - (t : ℂ)‖ + g₁ v) + X ω) ν =
        (∫ z, (a * Real.log ‖z - (t : ℂ)‖ + g₁ z) ∂ν) + X ω ν := by
  set K := Metric.closedBall (0 : ℂ) R ∩ Hbar
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right isClosed_Hbar
  have hKH : K ⊆ Hbar := Set.inter_subset_right
  have hae : ∀ᵐ z ∂ν, z ∈ K := ae_mem_of_compl_null_frostman hsupp
  filter_upwards [ae_all_iff.2 fun k => ae_circleAvg_tendsto_frostman hX k,
    ae_tendsto_integral_avgReg_frostman hX hsupp h hα] with ω hc ht a t g₁ hg₁
  have hlog := palmC_integrable_log_sub_frostman hsupp h hα t
  have hg₁i : Integrable g₁ ν := integrable_of_continuousOn_frostman hK hKH hsupp hg₁
  have heq : ∀ k, ∫ z, avgReg (ofFun (fun v => a * Real.log ‖v - (t : ℂ)‖ + g₁ v) + X ω) k z ∂ν =
      a * ∫ z, Real.log (max (radius k) ‖z - (t : ℂ)‖) ∂ν +
        ∫ z, GoodSample.smoothFun g₁ z (radius k) ∂ν + ∫ z, avgReg (X ω) k z ∂ν := by
    intro k
    have i1 : Integrable (fun z => Real.log (max (radius k) ‖z - (t : ℂ)‖)) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp
        (palmC_continuous_log_max_sub (radius_pos k) t).continuousOn
    have i2 : Integrable (fun z => GoodSample.smoothFun g₁ z (radius k)) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp
        (GoodSample.continuous_smoothFun hg₁ _).continuousOn
    have i3 : Integrable (fun z => avgReg (X ω) k z) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp (hc k).1
    have i12 : Integrable (fun z => a * Real.log (max (radius k) ‖z - (t : ℂ)‖) +
        GoodSample.smoothFun g₁ z (radius k)) ν := (i1.const_mul a).add i2
    rw [← integral_const_mul, ← integral_add (i1.const_mul a) i2, ← integral_add i12 i3]
    exact integral_congr_ae (hae.mono fun z hz =>
      palmC_avgReg_logAdd a t hg₁ ((hc k).2 z (hKH hz)))
  have hval : (∫ z, (a * Real.log ‖z - (t : ℂ)‖ + g₁ z) ∂ν) + X ω ν =
      a * ∫ z, Real.log ‖z - (t : ℂ)‖ ∂ν + ∫ z, g₁ z ∂ν + X ω ν := by
    rw [integral_add (hlog.const_mul a) hg₁i, integral_const_mul]
  rw [hval]
  refine Tendsto.limUnder_eq ?_
  simp only [heq]
  exact (((palmC_tendsto_integral_log_max_sub hsupp h hα t).const_mul a).add
    (tendsto_integral_smoothFun_frostman hg₁ hK hKH hsupp)).add ht

/-! ## Small geometric helpers -/

/-- Tietze extension of a function continuous on a closed subset of `ℂ`. -/
theorem exists_continuous_eqOn_mm {s : Set ℂ} (hs : IsClosed s) {f : ℂ → ℝ}
    (hf : ContinuousOn f s) : ∃ F : ℂ → ℝ, Continuous F ∧ EqOn F f s := by
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hs ⟨s.domRestrict f, hf.domRestrict⟩
  refine ⟨F, F.continuous, fun z hz => ?_⟩
  have := congrArg (fun φ : C(s, ℝ) => φ ⟨z, hz⟩) hF
  exact this

theorem mem_Hbar_add_real_mm {u : ℂ} (x : ℝ) : u + (x : ℂ) ∈ Hbar ↔ u ∈ Hbar := by
  simp [Hbar]

theorem mem_Hbar_sub_real_mm {u : ℂ} (x : ℝ) : u - (x : ℂ) ∈ Hbar ↔ u ∈ Hbar := by
  simp [Hbar]

/-- A point of the translated closed ball `closedBall (e − x) ρ ∩ Hbar` lies, after translation,
in `closedBall e ρ ∩ Hbar`. -/
theorem add_mem_of_mem_sub_mm {e u : ℂ} {x ρ : ℝ} (hu : u ∈ closedBall (e - x) ρ ∩ Hbar) :
    u + (x : ℂ) ∈ closedBall e ρ ∩ Hbar := by
  refine ⟨?_, (mem_Hbar_add_real_mm x).2 hu.2⟩
  have h := hu.1
  rw [mem_closedBall, dist_eq_norm] at h ⊢
  convert h using 2
  ring

/-! ## (b) The `AgreeNear` and the assembly of the Palm-Markov node -/

open S5.FieldLaw.Raw K3 in
/-- **The Palm-Markov node from the harmonic Palm representative** (own bookkeeping on top of
M7, `Prop16PalmShiftHarmStmt` and RC1; see the module docstring). -/
theorem prop16PalmMarkovCoupling_of_harm (hA : Prop16MixedFreeLocCouplingStmt)
    (hH : Prop16PalmShiftHarmStmt) : Prop16PalmMarkovCouplingStmt := by
  intro γ D c d a b h0 hγ hγ2 hgeo hab hca hbd x hx
  have hxcd : x ∈ Ioo c d := ⟨lt_of_le_of_lt hca hx.1, lt_of_lt_of_le hx.2 hbd⟩
  obtain ⟨rH, hrH, hballD, ψ, hψh, hψ⟩ := hH γ D c d x hγ hγ2 hgeo hxcd
  set ρ₀ : Measure ℂ := (foldedCircle 0 (2 * rH)).map (· + (x : ℂ)) with hρ₀def
  have hρ₀ : IsAdmissibleH ρ₀ := isAdmissibleH_map_add_real
    (isAdmissibleH_foldedCircle (by simp [Hbar]) (by linarith)) x
  have hρ₀1 : ρ₀ Set.univ = 1 := by rw [hρ₀def, map_add_real_univ, measure_univ]
  have hρ₀B : ρ₀ (ball (x : ℂ) rH) = 0 := by
    rw [hρ₀def, map_add_real_apply_mm _ _ measurableSet_ball, preimage_ball_add_mm]
    exact LateralGerm.foldedCircle_ball_eq_zero hrH (by linarith)
  obtain ⟨Ω₀, _, P₀, Y, X, g, E', _, Ξ, hP₀, hY, hS, hid⟩ :=
    prop16_markovSetup_at hγ hγ2 hgeo hxcd (r := rH) (r' := rH / 2) (by linarith)
      (by linarith) hballD hρ₀ hρ₀1 hρ₀B
  have := hP₀
  have hr1 : (0 : ℝ) < rH / 8 := by linarith
  have hψh1 : InnerProductSpace.HarmonicOnNhd (fun z => ψ (foldH z)) (ball 0 (rH / 8)) :=
    fun z hz => hψh z (ball_subset_ball (by linarith) hz)
  have hS1 := QuantumZipper.Prop16Asm.D3Plus.Setup.mono_absorb hS hr1 (by linarith) hψh1 (h0 x)
  -- the untranslated free field
  have hXf : IsFreeGFFModConstH X P₀ := by
    convert isFreeGFFModConstH_translate hS.hX (-x) using 1
    funext ω μ
    simp only [palmCField]
    rw [Measure.map_map (measurable_add_const _) (measurable_add_const _)]
    have e2 : ((· + (x : ℂ)) ∘ (· + ((-x : ℝ) : ℂ))) = id := by funext z; simp
    rw [e2, Measure.map_id]
  have hXρ : ∀ ω, palmCField X x ω (palmCRho ρ₀ x) = X ω ρ₀ := fun ω => by
    simp only [palmCField, map_map_add_neg_mm]
  -- the M7 identity at the translated dyadic circles of `ball x (rH/4)`
  have hM0 : ∀ᵐ ω ∂P₀, ∀ p : ℕ × ℕ × ℤ × ℤ,
      CircleCont.lpt p.1 p.2.2.1 p.2.2.2 ∈ Hbar →
      closedBall (CircleCont.lpt p.1 p.2.2.1 p.2.2.2) (radius p.2.1) ∩ Hbar ⊆
        ball (x : ℂ) (rH / 4) →
      Y ω ((foldedCircle (CircleCont.lpt p.1 p.2.2.1 p.2.2.2 - x) (radius p.2.1)).map
          (· + (x : ℂ))) =
        palmCField X x ω (foldedCircle (CircleCont.lpt p.1 p.2.2.1 p.2.2.2 - x) (radius p.2.1)) -
          ((foldedCircle (CircleCont.lpt p.1 p.2.2.1 p.2.2.2 - x) (radius p.2.1))
            Set.univ).toReal * palmCField X x ω (palmCRho ρ₀ x) +
          ∫ z, g ω (z + x) ∂(foldedCircle (CircleCont.lpt p.1 p.2.2.1 p.2.2.2 - x)
            (radius p.2.1)) := by
    rw [ae_all_iff]
    intro p
    set e := CircleCont.lpt p.1 p.2.2.1 p.2.2.2
    by_cases hc : e ∈ Hbar ∧ closedBall e (radius p.2.1) ∩ Hbar ⊆ ball (x : ℂ) (rH / 4)
    · have hex : e - x ∈ Hbar := (mem_Hbar_sub_real_mm x).2 hc.1
      have hadm := isAdmissibleH_foldedCircle hex (radius_pos p.2.1)
      have hsupp : foldedCircle (e - x) (radius p.2.1) (closedBall (0 : ℂ) (rH / 2))ᶜ = 0 := by
        refine mem_ae_iff.1 ?_
        filter_upwards [ae_fc_mem_ball_inter hex (radius_pos p.2.1)] with u hu
        have h1 := hc.2 (add_mem_of_mem_sub_mm hu)
        rw [mem_ball, dist_eq_norm, add_sub_cancel_right] at h1
        rw [mem_closedBall, dist_zero_right]
        linarith
      filter_upwards [hid _ hadm hsupp] with ω hω
      exact fun _ _ => hω
    · exact Filter.Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hc
  have hM : ∀ᵐ ω ∂P₀, ∀ (n k : ℕ) (z : ℂ), dyadicRoundC n z ∈ Hbar →
      closedBall (dyadicRoundC n z) (radius k) ∩ Hbar ⊆ ball (x : ℂ) (rH / 4) →
      Y ω ((foldedCircle (dyadicRoundC n z - x) (radius k)).map (· + (x : ℂ))) =
        palmCField X x ω (foldedCircle (dyadicRoundC n z - x) (radius k)) -
          ((foldedCircle (dyadicRoundC n z - x) (radius k)) Set.univ).toReal *
            palmCField X x ω (palmCRho ρ₀ x) +
          ∫ z', g ω (z' + x) ∂(foldedCircle (dyadicRoundC n z - x) (radius k)) := by
    filter_upwards [hM0] with ω hω n k z
    have := hω (n, k, ⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋)
    simpa only [CircleCont.dyadicRoundC_eq_lpt] using this
  -- RC1 at the translated zoom circles
  have hR0 : ∀ᵐ ω ∂P₀, ∀ p : ℕ × ℕ × ℤ × ℤ, ∀ (a' t : ℝ) (g₁ : ℂ → ℝ),
      ContinuousOn g₁ Hbar →
      evalReg (ofFun (fun v => a' * Real.log ‖v - (t : ℂ)‖ + g₁ v) + X ω)
          ((foldedCircle (foldH (CircleCont.lpt p.1 p.2.2.1 p.2.2.2)) (radius p.2.1)).map
            (· + (x : ℂ))) =
        (∫ z, (a' * Real.log ‖z - (t : ℂ)‖ + g₁ z) ∂((foldedCircle
          (foldH (CircleCont.lpt p.1 p.2.2.1 p.2.2.2)) (radius p.2.1)).map (· + (x : ℂ)))) +
          X ω ((foldedCircle (foldH (CircleCont.lpt p.1 p.2.2.1 p.2.2.2)) (radius p.2.1)).map
            (· + (x : ℂ))) := by
    rw [ae_all_iff]
    intro p
    rw [S5.FieldLaw.Raw.palmC_fc_map_add_real]
    exact palmC_ae_evalReg_logAdd_unif_mm hXf
      (CircleFubini.foldedCircle_support (radius_pos p.2.1).le le_rfl)
      (Cor15Group.isFrostman_fc _ (radius_pos p.2.1)) one_pos
  have hR : ∀ᵐ ω ∂P₀, ∀ (n k : ℕ) (z : ℂ) (a' t : ℝ) (g₁ : ℂ → ℝ),
      ContinuousOn g₁ Hbar →
      evalReg (ofFun (fun v => a' * Real.log ‖v - (t : ℂ)‖ + g₁ v) + X ω)
          ((foldedCircle (foldH (dyadicRoundC n z)) (radius k)).map (· + (x : ℂ))) =
        (∫ z, (a' * Real.log ‖z - (t : ℂ)‖ + g₁ z) ∂((foldedCircle
          (foldH (dyadicRoundC n z)) (radius k)).map (· + (x : ℂ)))) +
          X ω ((foldedCircle (foldH (dyadicRoundC n z)) (radius k)).map (· + (x : ℂ))) := by
    filter_upwards [hR0] with ω hω n k z
    have := hω (n, k, ⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋)
    simpa only [CircleCont.dyadicRoundC_eq_lpt] using this
  refine ⟨Ω₀, _, P₀, Y, rH / 8, palmCRho ρ₀ x, palmCField X x, E', _, Ξ,
    fun ω z => g ω (z + x) + ψ z + h0 x, hP₀, hY, hS1, ?_, ?_,
    fun C => aemeasurable_scaleParamOn_zoomModel_mm hS1 C⟩
  · rintro z ⟨hz1, hz2⟩
    show z + (x : ℂ) ∈ D
    refine hballD ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
      rw [mem_ball, dist_zero_right] at hz1
      linarith
    · show 0 < (z + (x : ℂ)).im
      simpa using (show 0 < z.im from hz2)
  filter_upwards [hM, hR, prop16LocNice_of_mixedGFF hA hγ hγ2 hgeo hab hca hbd P₀ Y hP₀ hY]
    with ω hMω hRω hn
  intro C
  refine ⟨?_, exists_vagueLimit_zoomFree_palmMixedField hgeo hxcd Y ω hn C⟩
  -- the continuous correction and its Tietze extension
  have hψc : ContinuousOn ψ (ball 0 rH ∩ Hbar) := D3Plus.continuousOn_g_of_harm hψh
  have hgc : ContinuousOn (fun z => g ω (z + x)) (ball 0 (rH / 2) ∩ Hbar) :=
    D3Plus.continuousOn_g_of_harm (hS.harm ω)
  set s : Set ℂ := closedBall (x : ℂ) (rH / 4) ∩ Hbar with hsdef
  have hsub : ∀ v ∈ s, ∀ R : ℝ, rH / 4 < R → v - x ∈ ball (0 : ℂ) R ∩ Hbar := by
    intro v hv R hR
    refine ⟨?_, (mem_Hbar_sub_real_mm x).2 hv.2⟩
    have h1 := hv.1
    rw [mem_closedBall, dist_eq_norm] at h1
    rw [mem_ball, dist_zero_right]
    linarith
  have hGc : ContinuousOn (fun v => ψ (v - x) + g ω v - X ω ρ₀) s := by
    have h1 : ContinuousOn (fun v : ℂ => ψ (v - x)) s :=
      hψc.comp (continuous_id.sub continuous_const).continuousOn
        fun v hv => hsub v hv rH (by linarith)
    have h2 : ContinuousOn (fun v : ℂ => g ω (v - x + x)) s :=
      hgc.comp (continuous_id.sub continuous_const).continuousOn
        fun v hv => hsub v hv (rH / 2) (by linarith)
    simp only [sub_add_cancel] at h2
    exact (h1.add h2).sub continuousOn_const
  obtain ⟨G, hGcont, hGeq⟩ := exists_continuous_eqOn_mm
    (isClosed_closedBall.inter isClosed_Hbar) hGc
  set Z'' : FieldSample := ofFun (fun v => -γ * Real.log ‖v - (x : ℂ)‖ + G v) + X ω
    with hZdef
  have hFm : Measurable (fun v : ℂ => -γ * Real.log ‖v - (x : ℂ)‖ + G v) :=
    ((palmC_measurable_log_sub (x : ℂ)).const_mul (-γ)).add hGcont.measurable
  -- (b1) locality: the Palm-shifted field agrees with `Z''` on the dyadic circles near `x`
  have hB : CircAgree (ball (x : ℂ) (rH / 4)) (palmMixedField γ D (realSet (Icc c d)) Y x ω)
      Z'' := by
    intro n k z hz hW
    have he : dyadicRoundC n z ∈ Hbar := CircleCont.dyadicRoundC_mem_Hbar hz n
    have hex : dyadicRoundC n z - x ∈ Hbar := (mem_Hbar_sub_real_mm x).2 he
    have hρ := radius_pos k
    have hpt : ∀ u ∈ closedBall (dyadicRoundC n z - x) (radius k) ∩ Hbar,
        u + (x : ℂ) ∈ s ∧ u ∈ ball (0 : ℂ) (rH / 4) ∩ Hbar := by
      intro u hu
      have h1 := add_mem_of_mem_sub_mm hu
      have h2 := hW h1
      refine ⟨⟨mem_closedBall.2 (mem_ball.1 h2).le, h1.2⟩, ?_, hu.2⟩
      rw [mem_ball, dist_eq_norm, add_sub_cancel_right] at h2
      rw [mem_ball, dist_zero_right]
      exact h2
    have hin : ∀ᵐ u ∂foldedCircle (dyadicRoundC n z - x) (radius k),
        u + (x : ℂ) ∈ s ∧ u ∈ ball (0 : ℂ) (rH / 4) ∩ Hbar := by
      filter_upwards [ae_fc_mem_ball_inter hex hρ] with u hu
      exact hpt u hu
    have hsuppμ : foldedCircle (dyadicRoundC n z - x) (radius k) (closedBall (0 : ℂ) rH)ᶜ = 0 := by
      refine mem_ae_iff.1 ?_
      filter_upwards [hin] with u hu
      have h3 := hu.2.1
      rw [mem_ball, dist_zero_right] at h3
      rw [mem_closedBall, dist_zero_right]
      linarith
    have hHe := hψ _ (isAdmissibleH_foldedCircle hex hρ) hsuppμ
    have Iψ : Integrable ψ (foldedCircle (dyadicRoundC n z - x) (radius k)) :=
      integrable_fc_of_continuousOn hex hρ (hψc.mono fun u hu =>
        ⟨ball_subset_ball (by linarith) (hpt u hu).2.1, hu.2⟩)
    have Ig : Integrable (fun u => g ω (u + x)) (foldedCircle (dyadicRoundC n z - x) (radius k)) :=
      integrable_fc_of_continuousOn hex hρ (hgc.mono fun u hu =>
        ⟨ball_subset_ball (by linarith) (hpt u hu).2.1, hu.2⟩)
    have Ilog : Integrable (fun u : ℂ => Real.log ‖u‖)
        (foldedCircle (dyadicRoundC n z - x) (radius k)) := by
      simpa using palmC_integrable_log_sub_fc (dyadicRoundC n z - x) 0 (radius k)
    have I1 : Integrable (fun u : ℂ => γ * -Real.log ‖u‖ + ψ u)
        (foldedCircle (dyadicRoundC n z - x) (radius k)) := (Ilog.neg.const_mul γ).add Iψ
    have hmap : (foldedCircle (dyadicRoundC n z - x) (radius k)).map (· + (x : ℂ)) =
        foldedCircle (dyadicRoundC n z) (radius k) := by
      rw [palmC_fc_map_add_real, sub_add_cancel]
    rw [← hmap]
    simp only [palmMixedField, hZdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofFun]
    rw [hMω n k z he hW, hHe, hXρ ω, measure_univ, ENNReal.toReal_one,
      integral_map (measurable_add_const _).aemeasurable hFm.aestronglyMeasurable]
    have hint : ∫ u, (-γ * Real.log ‖u + (x : ℂ) - (x : ℂ)‖ + G (u + (x : ℂ)))
        ∂foldedCircle (dyadicRoundC n z - x) (radius k) =
        ∫ u, ((γ * -Real.log ‖u‖ + ψ u) + g ω (u + x) - X ω ρ₀)
          ∂foldedCircle (dyadicRoundC n z - x) (radius k) := by
      refine integral_congr_ae (hin.mono fun u hu => ?_)
      have h4 := hGeq hu.1
      simp only [add_sub_cancel_right] at h4 ⊢
      rw [h4]
      ring
    have hc : ∫ _u, X ω ρ₀ ∂foldedCircle (dyadicRoundC n z - x) (radius k) = X ω ρ₀ := by
      simp
    rw [hint, integral_sub (f := fun u => (γ * -Real.log ‖u‖ + ψ u) + g ω (u + x))
      (I1.add Ig) (integrable_const _),
      integral_add (f := fun u => γ * -Real.log ‖u‖ + ψ u) (g := fun u => g ω (u + x)) I1 Ig, hc]
    show X ω _ - 1 * X ω ρ₀ + _ + _ = _
    ring
  -- (b2) the `AgreeNear` at the dyadic circles of `ball 0 (rH/8)`
  intro n k z hz
  have hρ := radius_pos k
  have hd : foldH (dyadicRoundC n z) ∈ Hbar := CircleFubini.foldH_mem_Hbar' _
  have hnd : ‖foldH (dyadicRoundC n z)‖ = ‖dyadicRoundC n z‖ := palmC_norm_foldH _
  have hfc : foldedCircle (foldH (dyadicRoundC n z)) (radius k) =
      foldedCircle (dyadicRoundC n z) (radius k) :=
    ext_of_forall_integral_eq_of_IsFiniteMeasure fun f =>
      RegClosure.integral_fc_foldH f.continuous.continuousOn _ _
  rw [← hfc]
  have hzf : zoomFree γ C h0 (palmMixedField γ D (realSet (Icc c d)) Y x) (ω, x) =
      addConst (translate (palmMixedField γ D (realSet (Icc c d)) Y x ω) (x : ℂ))
        (C / γ + h0 x) := by
    simp only [zoomFree, zoomField, addConst_addConst]
  have hK : closedBall (foldH (dyadicRoundC n z) + x) (radius k) ∩ Hbar ⊆
      ball (x : ℂ) (rH / 4) := by
    intro v hv
    have h1 := hv.1
    rw [mem_closedBall, dist_eq_norm] at h1
    rw [mem_ball, dist_eq_norm]
    have h2 := norm_add_le (v - (foldH (dyadicRoundC n z) + x)) (foldH (dyadicRoundC n z))
    rw [show v - (foldH (dyadicRoundC n z) + x) + foldH (dyadicRoundC n z) = v - x by ring]
      at h2
    linarith
  have hloc := evalReg_eq_of_circAgree isOpen_ball hB (isCompact_closedBall_inter_Hbar _ _) hK
    (ν := (foldedCircle (foldH (dyadicRoundC n z)) (radius k)).map (· + (x : ℂ))) (by
      rw [palmC_fc_map_add_real]
      filter_upwards [ae_fc_mem_ball_inter ((mem_Hbar_add_real_mm x).2 hd) hρ] with u hu
      exact ⟨hu, hu.2⟩)
  rw [hzf]
  simp only [addConst, translate, D3Plus.zoomModel, Pi.add_apply, ofFun, measure_univ,
    ENNReal.toReal_one, mul_one]
  rw [hloc, hRω n k z (-γ) x G hGcont.continuousOn, hXρ ω,
    integral_map (measurable_add_const _).aemeasurable hFm.aestronglyMeasurable]
  have Ilog : Integrable (fun u : ℂ => Real.log ‖u‖)
      (foldedCircle (foldH (dyadicRoundC n z)) (radius k)) := by
    simpa using palmC_integrable_log_sub_fc (foldH (dyadicRoundC n z)) 0 (radius k)
  have IF : Integrable (fun u : ℂ => -γ * Real.log ‖u‖ + G (u + x))
      (foldedCircle (foldH (dyadicRoundC n z)) (radius k)) :=
    (Ilog.const_mul (-γ)).add (RegClosure.integrable_fc
      (by fun_prop : Continuous fun u : ℂ => G (u + x)).continuousOn _ hρ.le)
  have hint : ∫ u, (γ * -Real.log ‖u‖ + (g ω (u + x) + ψ u + h0 x) + (C / γ - X ω ρ₀))
      ∂foldedCircle (foldH (dyadicRoundC n z)) (radius k) =
      ∫ u, ((-γ * Real.log ‖u‖ + G (u + x)) + (C / γ + h0 x))
        ∂foldedCircle (foldH (dyadicRoundC n z)) (radius k) := by
    refine integral_congr_ae ((ae_fc_mem_ball_inter hd hρ).mono fun u hu => ?_)
    have hus : u + (x : ℂ) ∈ s := by
      refine ⟨?_, (mem_Hbar_add_real_mm x).2 hu.2⟩
      have h1 := hu.1
      rw [mem_closedBall, dist_eq_norm] at h1
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
      have h2 := norm_add_le (u - foldH (dyadicRoundC n z)) (foldH (dyadicRoundC n z))
      rw [sub_add_cancel] at h2
      linarith
    have h4 := hGeq hus
    simp only [add_sub_cancel_right] at h4
    dsimp only
    rw [h4]
    ring
  have hc : ∫ _u, (C / γ + h0 x) ∂foldedCircle (foldH (dyadicRoundC n z)) (radius k) =
      C / γ + h0 x := by simp
  simp only [add_sub_cancel_right]
  rw [hint, integral_add IF (integrable_const _), hc]
  show _ = X ω _ + _
  ring

end Prop16Asm

end QuantumZipper
