import InteractingSLE.SLE8.Counting.Height
import QuantumZipper.Proofs.RS.TransienceCanon

/-!
# The trial event at a deterministic pair and its probability ((4.22)–(4.24))

SLE₈ note `source/sle8-continuity.pdf`, §4, Step 4, pp. 9–10 (transcription
`source/sle8/sle8-continuity.md`, anchor `prop-4.1-proof`).

For a deterministic pair `(k_*, T)` the note's event `E_{k_*,T}` (4.22) concerns the reverse flow from
`(T, iy_*)` in the height parameter (3.1). Here it is `trialEventAt V y T a r m`, for the reverse flow
driven by `V` from `iy`: `y Φ_T ≥ a`, and the first `m` trial intervals of the height-parameter process
`v ↦ J_{u₀ + v}` (level `2r`, length `2L = 2r⁵`, searched up to `U - u₀`, `U = log √5`) end by
`τ_T - u₀` (the completion condition), each with occupation of `[-1, 1]` at most `r`. The condition
`σ_{m_r} ≤ u_end` of (4.22) is not needed for the bound and is not included.

## Main results

* `measurableSet_trialEventAt`: the trial event is measurable with respect to `τ_T`, `Φ_T` and the
  stopped height-parameter process ("the completion condition makes this an `𝓕_{τ_T}`-measurable event");
* `measure_trialEventAt_le`: (4.23)–(4.24), `ℙ(E) ≤ y² a⁻² (C_tr/r)^m`, from Lemma 3.1 ((3.2) and the
  law of `J` under `ℚ`), Lemma 3.3 and the strong Markov property (`measure_trialFound_le`).
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology ENNReal NNReal

namespace InteractingSLE.SLE8

open QuantumZipper

/-- The height-parameter process from `u₀ = log y`, stopped at `τ_T`: `v ↦ J_{min(u₀ + v, τ_T)}`. -/
def jPath (V : ℝ → ℝ) (y T : ℝ) : ℝ → ℝ :=
  fun v => heightJ V y (min (Real.log y + v) (heightTau V y T))

/-- The search horizon `U - u₀ = log √5 - log y` of the trial intervals. -/
def trialHorizon (y : ℝ) : ℝ := Real.log (Real.sqrt 5) - Real.log y

/-- The trial event `E_{k_*,T}` of (4.22) (without the condition `σ_{m_r} ≤ u_end`), for the reverse
flow driven by `V` from `iy` at terminal time `T`, with `m` trials, level `2r` and length `2r⁵`. -/
def trialEventAt (V : ℝ → ℝ) (y T a r : ℝ) (m : ℕ) : Prop :=
  a ≤ y * rfPhi V y T ∧ TrialEvent (jPath V y T) (2 * r) (r ^ 5) (trialHorizon y) r m ∧
    ∀ j < m, entrance (jPath V y T) (2 * r) (r ^ 5) (trialHorizon y) j + 2 * r ^ 5 ≤
      heightTau V y T - Real.log y

variable {V : ℝ → ℝ} {y T : ℝ}

theorem continuous_jPath (hV : Continuous V) (hy : 0 < y) (hT : 0 ≤ T) : Continuous (jPath V y T) :=
  (continuous_heightJ_stopped hV hy hT).comp (continuous_const.add continuous_id)

/-- `log y ≤ τ_T ≤ log √5` for `y ∈ (0, 1]`, `T ∈ [0, 1]` (Lemma 2.2). -/
theorem heightTau_mem (hV : Continuous V) (hy : y ∈ Ioc (0 : ℝ) 1) (hT : T ∈ Icc (0 : ℝ) 1) :
    heightTau V y T ∈ Icc (Real.log y) (Real.log (Real.sqrt 5)) := by
  have hz : (y : ℂ) * I ∈ H := mul_I_mem_H hy.1
  have h := im_revMap_mem_Icc hV hz hT.1
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at h
  have hpos : 0 < rfY V y T := rfY_pos hV hy.1 hT.1
  refine ⟨Real.log_le_log hy.1 h.1, Real.log_le_log hpos (h.2.trans ?_)⟩
  refine Real.sqrt_le_sqrt ?_
  nlinarith [hy.2, hT.2, hy.1]

theorem jPath_eq {v : ℝ} (hv : v ≤ heightTau V y T - Real.log y) :
    jPath V y T v = heightJ V y (Real.log y + v) := by
  unfold jPath; rw [min_eq_left (by linarith)]

section Measurability

variable {Ω : Type*} {β : ℝ≥0 → Ω → ℝ}

theorem measurable_heightStoppedSigma_tau :
    Measurable[heightStoppedSigma (fun ω => drive 8 β ω) y T] fun ω => heightTau (drive 8 β ω) y T :=
  measurable_fst.comp (comap_measurable _)

theorem measurable_heightStoppedSigma_phi :
    Measurable[heightStoppedSigma (fun ω => drive 8 β ω) y T] fun ω => rfPhi (drive 8 β ω) y T :=
  (measurable_fst.comp measurable_snd).comp (comap_measurable _)

theorem measurable_heightStoppedSigma_jPath (v : ℝ) :
    Measurable[heightStoppedSigma (fun ω => drive 8 β ω) y T] fun ω => jPath (drive 8 β ω) y T v :=
  ((measurable_pi_apply (Real.log y + v)).comp (measurable_snd.comp measurable_snd)).comp
    (comap_measurable (fun ω => (heightTau (drive 8 β ω) y T, rfPhi (drive 8 β ω) y T,
      fun u : ℝ => heightJ (drive 8 β ω) y (min u (heightTau (drive 8 β ω) y T)))))

/-- **The trial event is `𝓕_{τ_T}`-measurable** (p. 10: "The completion condition makes this an
`𝓕_{τ_T}`-measurable event"): it is measurable with respect to `τ_T`, `Φ_T` and the stopped
height-parameter process. -/
theorem measurableSet_trialEventAt (hβc : ∀ ω, Continuous fun t => β t ω) (hy : 0 < y)
    (hT : 0 ≤ T) (a r : ℝ) (m : ℕ) :
    MeasurableSet[heightStoppedSigma (fun ω => drive 8 β ω) y T]
      {ω | trialEventAt (drive 8 β ω) y T a r m} := by
  have hc : ∀ ω, Continuous (jPath (drive 8 β ω) y T) := fun ω =>
    continuous_jPath (drive_continuous (hβc ω)) hy hT
  have hm := measurable_heightStoppedSigma_jPath (β := β) (y := y) (T := T)
  have heq : {ω | trialEventAt (drive 8 β ω) y T a r m} =
      {ω | a ≤ y * rfPhi (drive 8 β ω) y T} ∩
        {ω | TrialEvent (jPath (drive 8 β ω) y T) (2 * r) (r ^ 5) (trialHorizon y) r m} ∩
        ⋂ j ∈ Finset.range m, {ω | entrance (jPath (drive 8 β ω) y T) (2 * r) (r ^ 5)
          (trialHorizon y) j + 2 * r ^ 5 ≤ heightTau (drive 8 β ω) y T - Real.log y} := by
    ext ω; simp [trialEventAt, and_assoc]
  rw [heq]
  refine ((measurableSet_le measurable_const
    (measurable_const.mul measurable_heightStoppedSigma_phi)).inter
    (measurableSet_trialEvent hc hm _ _ _ _ _)).inter
    (Finset.measurableSet_biInter _ fun j _ => measurableSet_le
      ((measurable_entrance hc hm _ _ _ j).add_const _)
      (measurable_heightStoppedSigma_tau.sub_const _))

end Measurability

/-! ## The probability of the trial event -/

/-- **(4.23)–(4.24).** Let `β` be a Brownian motion (all paths continuous, `β₀ = 0`) driving the
reverse flow `V = √8 β`, `T ∈ [0, 1]`, `y ∈ (0, 1]`, and let `ℚ`, `β'` be as in Lemma 3.1 (`J = 2β'` on
`[u₀, τ_T]` `ℚ`-a.s., and the change of measure (3.2)). If Lemma 3.3 holds with constant `C` at `r ≥ 2`,
then `ℙ(E) ≤ y² a⁻² (C/r)^m` for the trial event `E` with `m` trials. -/
theorem measure_trialEventAt_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {β : ℝ≥0 → Ω → ℝ} (hβc : ∀ ω, Continuous fun t => β t ω)
    (hT : T ∈ Icc (0 : ℝ) 1) (hy : y ∈ Ioc (0 : ℝ) 1)
    {Q : Measure Ω} [IsProbabilityMeasure Q] {β' : ℝ≥0 → Ω → ℝ} (hβ' : IsBrownianReal β' Q)
    (hJ : ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, (v : ℝ) ≤ heightTau (drive 8 β ω) y T - Real.log y →
      heightJ (drive 8 β ω) y (Real.log y + v) = 2 * β' v ω)
    (hPQ : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ E : Set Ω,
      MeasurableSet[heightStoppedSigma (fun ω => drive 8 β ω) y T] E →
      E ⊆ {ω | a ≤ y * rfPhi (drive 8 β ω) y T} → P E ≤ ENNReal.ofReal (y ^ 2 / a ^ 2) * Q E)
    {C r a : ℝ}
    (hC : ∀ β'' : ℝ≥0 → Ω → ℝ, IsBrownianReal β'' Q → (∀ ω, Continuous fun t => β'' t ω) →
      (∀ t, Measurable (β'' t)) → ∀ x : ℝ, |x| ≤ 2 * r →
        Q {ω | occRestart r x (fun t => β'' t ω) ≤ ENNReal.ofReal r} ≤ ENNReal.ofReal (C / r))
    (ha : a ∈ Ioo (0 : ℝ) 1) (hr : 2 ≤ r) (m : ℕ) :
    P {ω | trialEventAt (drive 8 β ω) y T a r m} ≤
      ENNReal.ofReal (y ^ 2 / a ^ 2) * ENNReal.ofReal (C / r) ^ m := by
  have hVc : ∀ ω, Continuous (drive 8 β ω) := fun ω => drive_continuous (hβc ω)
  obtain ⟨β'', hm'', hc'', h0'', hβ'', hae''⟩ := RS.exists_good_version0 hβ'
  have hK : 0 ≤ trialHorizon y := by
    unfold trialHorizon
    have : Real.log y ≤ Real.log (Real.sqrt 5) := Real.log_le_log hy.1 (hy.2.trans
      (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num))
    linarith
  have hsub : {ω | trialEventAt (drive 8 β ω) y T a r m} ≤ᵐ[Q]
      {ω | TrialFound (bmPath β'' ω) (2 * r) (r ^ 5) (trialHorizon y) r m} := by
    filter_upwards [hJ, hae''] with ω hJω hgood hE
    obtain ⟨-, hTE, hcomp⟩ := hE
    have hτ := heightTau_mem (hVc ω) hy hT
    have hK'0 : 0 ≤ heightTau (drive 8 β ω) y T - Real.log y := by linarith [hτ.1]
    have hK'K : heightTau (drive 8 β ω) y T - Real.log y ≤ trialHorizon y := by
      unfold trialHorizon; linarith [hτ.2]
    refine trialFound_of_congr (continuous_jPath (hVc ω) hy.1 hT.1)
      (continuous_bmPath hc'' ω) (by positivity) hK'0 hK'K (fun v hv => ?_)
      fun j hj => ⟨hcomp j hj, (hTE j hj).2⟩
    rw [jPath_eq hv.2]
    have h1 := hJω v.toNNReal (by rw [Real.coe_toNNReal _ hv.1]; exact hv.2)
    rw [Real.coe_toNNReal _ hv.1] at h1
    rw [h1, bmPath, hgood]
  have hEm := measurableSet_trialEventAt hβc hy.1 hT.1 a r m
  calc P {ω | trialEventAt (drive 8 β ω) y T a r m}
      ≤ ENNReal.ofReal (y ^ 2 / a ^ 2) * Q {ω | trialEventAt (drive 8 β ω) y T a r m} :=
        hPQ a ha _ hEm fun ω hω => hω.1
    _ ≤ ENNReal.ofReal (y ^ 2 / a ^ 2) *
          Q {ω | TrialFound (bmPath β'' ω) (2 * r) (r ^ 5) (trialHorizon y) r m} := by
        gcongr 1; exact measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (y ^ 2 / a ^ 2) * ENNReal.ofReal (C / r) ^ m := by
        gcongr 1; exact measure_trialFound_le hC hβ'' hc'' hm'' h0'' hr hK m

end InteractingSLE.SLE8
