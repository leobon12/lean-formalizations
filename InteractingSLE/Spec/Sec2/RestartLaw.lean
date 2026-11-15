/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.RestartEvolution
import InteractingSLE.Spec.Sec2.RestartLawCode
import InteractingSLE.Spec.Sec2.OneForceLaw
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# The law of a restarted evolution is the canonical law from the state at the stopping time

Packet PROVE-RESTART (Theorem 2.2's Markov property in the form used inside proofs: "conditionally on
`𝓕_τ`, the process after `τ` is the canonical integrated evolution from the state at `τ`").

* `wienerPath`: the Wiener measure on `ℝ≥0 → ℝ` (product σ-algebra), the law of every pre-Brownian motion
  with measurable coordinates (`map_path_eq_wienerPath`);
* `restartLaw a ρL ρR ts K s`: the measurable kernel (`measurable_restartLaw`) giving, for a start `s`, the
  probability that the solution driven by a Brownian path has its killed state at the times `ts` in `K`
  (built from the Borel set `Assembly.lawSetF`);
* `measure_killedState_eq_restartLaw`: **canonical law.** For a separated start `s = (xL, xR)` this is the
  killed-state law of *every* integrated evolution from `s`, on any filtered probability space;
* `measure_restart_killedState`: **the conditional law at a stopping time.** For an integrated evolution,
  a finite stopping time `T`, and `A ∈ 𝓕_T` with `T < ζ` on `A` and, on `A`, `0 < T` or a separated word,

    `ℙ[A ∩ {(W, V, B)_{T+t_j} − (W_T, W_T, B_T) ∈ K_j, t_j < ζ − T for all j}]
      = ∫_A restartLaw(V_T − W_T) dℙ`,

  so the conditional law of the restarted killed state given `𝓕_T` is the canonical law from the state
  `V_T − W_T`. The condition makes the restart state separated (`sepStart_restart`: after a positive time
  a left mark is strictly left of its start and a right mark strictly right; `sepStart_restart_of_sep`: a
  separated word stays separated), the class in which Theorem 2.2's uniqueness is landed; no hypothesis
  about the general entrance laws is needed. The excluded case, an entrance word restarted at `T = 0`, is
  the evolution itself given `𝓕_0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Interval

namespace InteractingSLE

namespace Sec2

namespace Restart

open Assembly QuantumZipper.StrongMarkov

/-! ### The Wiener measure on paths -/

theorem exists_isProjectiveLimit_brownian :
    ∃ μ : Measure (ℝ≥0 → ℝ), IsProjectiveLimit μ BrownianReal.projectiveFamily := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, B, hB, -, -⟩ := OneForce.exists_filteredBrownian
  have hm : Measurable fun ω (s : ℝ≥0) => B s ω := measurable_pi_iff.2 hB.measurable'
  have h := isProjectiveLimit_map (P := P) (X := B) hm.aemeasurable
  have e : (fun I : Finset ℝ≥0 => P.map fun ω => I.restrict fun s => B s ω) =
      BrownianReal.projectiveFamily := funext fun I => (hB.1.toIsPreBrownianReal.hasLaw I).map_eq
  rw [e] at h
  exact ⟨_, h⟩

/-- The Wiener measure on `ℝ≥0 → ℝ`: the projective limit of the Brownian finite-dimensional laws. -/
def wienerPath : Measure (ℝ≥0 → ℝ) := Classical.choose exists_isProjectiveLimit_brownian

/-- Every pre-Brownian motion with measurable coordinates has path law `wienerPath`. -/
theorem map_path_eq_wienerPath {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : Measurable fun ω (s : ℝ≥0) => B s ω) : P.map (fun ω s => B s ω) = wienerPath := by
  have h := isProjectiveLimit_map (P := P) (X := B) hm.aemeasurable
  have e : (fun I : Finset ℝ≥0 => P.map fun ω => I.restrict fun s => B s ω) =
      BrownianReal.projectiveFamily := funext fun I => (hB.hasLaw I).map_eq
  rw [e] at h
  exact h.unique (Classical.choose_spec exists_isProjectiveLimit_brownian)

instance isProbabilityMeasure_wienerPath : IsProbabilityMeasure wienerPath := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, B, hB, -, -⟩ := OneForce.exists_filteredBrownian
  have hm : Measurable fun ω (s : ℝ≥0) => B s ω := measurable_pi_iff.2 hB.measurable'
  rw [← map_path_eq_wienerPath hB.1.toIsPreBrownianReal hm]
  exact ⟨by rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ, measure_univ]⟩

/-! ### The kernel -/

variable {nL nR : ℕ}

theorem measurable_enc : Measurable (enc : (ℝ≥0 → ℝ) → PCode) :=
  measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- Pairs (start, Brownian path) whose solution from the start has its killed state in `K` at `ts`. -/
def restartSet (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) :
    Set (((Fin nL → ℝ) × (Fin nR → ℝ)) × (ℝ≥0 → ℝ)) :=
  {p | (p.1, enc p.2) ∈ lawSetF a ρL ρR ts K}

theorem measurableSet_restartSet {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {n : ℕ}
    (ts : Fin n → ℝ≥0) {K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)}
    (hK : ∀ j, MeasurableSet (K j)) : MeasurableSet (restartSet a ρL ρR ts K) :=
  (measurable_fst.prodMk (measurable_enc.comp measurable_snd)) (measurableSet_lawSetF ts hK)

/-- **The canonical killed-state law from a start** `s`: the Wiener probability of the driving paths
whose solution from `s` (with weights `ρ`) has its killed state `(W, V^L, V^R, B)` at the times `ts` in the
sets `K`. For a separated start this is the law of every integrated evolution from `s`
(`measure_killedState_eq_restartLaw`). -/
def restartLaw (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) (s : (Fin nL → ℝ) × (Fin nR → ℝ)) :
    ℝ≥0∞ :=
  wienerPath (Prod.mk s ⁻¹' restartSet a ρL ρR ts K)

/-- The canonical law is a measurable kernel in the start. -/
theorem measurable_restartLaw {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {n : ℕ}
    (ts : Fin n → ℝ≥0) {K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)}
    (hK : ∀ j, MeasurableSet (K j)) : Measurable (restartLaw a ρL ρR ts K) :=
  measurable_measure_prodMk_left (measurableSet_restartSet ts hK)

/-- **The canonical law.** For a separated start `(xL, xR)`, every integrated evolution from it (on any
filtered probability space) has killed-state law `restartLaw · (xL, xR)`. -/
theorem measure_killedState_eq_restartLaw {a : ℝ} (ha : 0 < a) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {n : ℕ} (ts : Fin n → ℝ≥0)
    {K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)} (hK : ∀ j, MeasurableSet (K j)) :
    P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
        (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ K j} =
      restartLaw a ρL ρR ts K (xL, xR) := by
  obtain ⟨B', hm, hc, -, hbm, hae⟩ := QuantumZipper.RS.exists_good_version0 h.1.1
  have hpm : Measurable fun ω (s : ℝ≥0) => B' s ω := measurable_pi_iff.2 hm
  rw [measure_killedState_eq_map ha hsep h hm hc hae ts K hK,
    Measure.map_apply (QuantumZipper.RS.measurable_toCPath hm hc)
      ((measurableSet_lawSet hsep ts hK).preimage measurable_encC),
    restartLaw, ← map_path_eq_wienerPath hbm.toIsPreBrownianReal hpm,
    Measure.map_apply hpm ((measurableSet_restartSet ts hK).preimage measurable_prodMk_left)]
  congr 1
  ext ω
  simp only [mem_preimage, restartSet, mem_ofPred_eq]
  rw [mem_lawSetF_iff hsep]
  rfl

/-! ### Pointwise facts about a restarted path -/

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The pointwise content of `Assembly.ae_codeOf_mem`: a path satisfying the frozen predicate, with a
continuous driving path and a threshold limit at a finite positive lifetime, has a canonical solution code
that decodes to it before `ζ`. -/
theorem codeOf_mem_cRel_of_path {Ω : Type*} {B' : ℝ≥0 → Ω → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hpath : IsIntegratedSLEPath a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ ω))
    (hB'c : Continuous (B' · ω)) (hB : ∀ t, B' t ω = B t ω)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T)
          (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) :
    codeOf xL xR B' W VL VR ζ ω ∈ CRel a xL xR ρL ρR ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
        cw (codeOf xL xR B' W VL VR ζ ω) t = W t ω ∧
        (∀ i, cvL (codeOf xL xR B' W VL VR ζ ω) i t = VL i t ω) ∧
        (∀ j, cvR (codeOf xL xR B' W VL VR ζ ω) j t = VR j t ω) ∧
        cb (codeOf xL xR B' W VL VR ζ ω) t = B t ω := by
  set x := codeOf xL xR B' W VL VR ζ ω with hxdef
  have hp := hpath.isForcePath
  have hbdec : ∀ t, cb x t = B t ω := fun t => by
    show dec (enc (B' · ω)) t = B t ω
    rw [dec_enc hB'c.continuousWithinAt, hB t]
  have hwdec : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → cw x t = W t ω := fun t ht =>
    dec_killedCode hp.w_zero hp.continuousOn_w ht
  have hLdec : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ i, cvL x i t = VL i t ω := fun t ht i =>
    dec_killedCode (hp.vL_zero i) (hp.continuousOn_vL i) ht
  have hRdec : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ j, cvR x j t = VR j t ω := fun t ht j =>
    dec_killedCode (hp.vR_zero j) (hp.continuousOn_vR j) ht
  have hgood : Good x := by
    refine ⟨fun T => uc_enc hB'c.continuousOn, fun n k hd => ⟨?_, fun i => ?_, fun j => ?_⟩⟩
    · exact uc_killedCode hp.w_zero hp.continuousOn_w hd
    · exact uc_killedCode (hp.vL_zero i) (hp.continuousOn_vL i) hd
    · exact uc_killedCode (hp.vR_zero j) (hp.continuousOn_vR j) hd
  have hpred : IsIntegratedSLEPath a xL xR ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) := by
    refine isIntegratedSLEPath_congr hpath ?_ (fun i => ?_) (fun j => ?_) hwdec hLdec hRdec
      fun t _ => hbdec t
    · show dec (killedCode W 0 ζ ω) 0 = W 0 ω
      rw [dec_zero_of_const (killedCode_zero W 0 ζ ω), hp.w_zero]
    · show dec (killedCode (VL i) (xL i) ζ ω) 0 = VL i 0 ω
      rw [dec_zero_of_const (killedCode_zero (VL i) (xL i) ζ ω), hp.vL_zero i]
    · show dec (killedCode (VR j) (xR j) ζ ω) 0 = VR j 0 ω
      rw [dec_zero_of_const (killedCode_zero (VR j) (xR j) ζ ω), hp.vR_zero j]
  have hlimthr : LimThr ρL ρR x := by
    intro h0 hfin
    set T := (ζ ω).toNNReal
    have hTζ : (T : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hfin.ne
    have hT : 0 < T := by
      have : (0 : ℝ≥0∞) < T := by rw [hTζ]; exact h0
      exact_mod_cast this
    obtain ⟨w₀, vL₀, vR₀, htend, hthr⟩ := hlim T hT hTζ
    have htend' : Tendsto (fun t => (cw x t, fun i => cvL x i t, fun j => cvR x j t)) (𝓝[<] T)
        (𝓝 (w₀, vL₀, vR₀)) := by
      refine htend.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (t : ℝ≥0∞) < ζ ω := by rw [← hTζ]; exact_mod_cast ht
      rw [hwdec t ht', funext (hLdec t ht'), funext (hRdec t ht')]
    have hq := lim_eq_of_tendsto (x := x) hT (show (T : ℝ≥0∞) = cζ x from hTζ) htend'
    simp only [Prod.mk.injEq] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    rw [h1, h2, h3]
    exact hthr
  have hcanon : Canon xL xR x := by
    intro n k
    constructor
    · intro h0
      simp only [x, codeOf, killedCode, h0, ↓reduceIte]
      exact ⟨trivial, fun i => trivial, fun j => trivial⟩
    · intro h0 hlt
      have hlt' : ¬ (dyad n k : ℝ≥0∞) < ζ ω := hlt
      simp only [x, codeOf, killedCode, h0, hlt', ↓reduceIte]
      exact ⟨trivial, fun i => trivial, fun j => trivial⟩
  exact ⟨⟨⟨hgood, hlimthr, hpred⟩, hcanon⟩, fun t ht =>
    ⟨hwdec t ht, hLdec t ht, hRdec t ht, hbdec t⟩⟩

/-- The threshold limit at the lifetime passes to the restarted path. -/
theorem restart_tendsto {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) :
    ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ - σ →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (w (σ + t) - w σ, fun i => vL i (σ + t) - w σ,
          fun i => vR i (σ + t) - w σ)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := by
  intro T hT hTζ
  have hζtop : ζ ≠ ⊤ := fun h => by
    rw [h, ENNReal.top_sub_coe] at hTζ
    exact ENNReal.coe_ne_top hTζ
  have hζ : ((σ + T : ℝ≥0) : ℝ≥0∞) = ζ := by
    rw [ENNReal.coe_add, hTζ, add_tsub_cancel_of_le hσ.le]
  obtain ⟨w₀, vL₀, vR₀, ht, hthr⟩ := hlim (σ + T) (lt_of_lt_of_le hT le_add_self) hζ
  set c := w σ
  refine ⟨w₀ - c, fun i => vL₀ i - c, fun j => vR₀ j - c, ?_,
    (ForceWord.thresholdCondition_sub_iff ρL ρR w₀ c vL₀ vR₀).2 hthr⟩
  have hφ : Tendsto (fun u : ℝ≥0 => σ + u) (𝓝[<] T) (𝓝[<] (σ + T)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_const.add continuous_id).tendsto T).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact add_lt_add_right hu σ
  have hΨ : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
      (p.1 - c, fun i => p.2.1 i - c, fun j => p.2.2 j - c) :=
    (continuous_fst.sub continuous_const).prodMk
      ((continuous_pi fun i => ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).sub
        continuous_const).prodMk
      (continuous_pi fun j => ((continuous_apply j).comp (continuous_snd.comp continuous_snd)).sub
        continuous_const))
  exact ((hΨ.tendsto _).comp ht).comp hφ

/-- The integral of `2/d` over `[0, σ]` is positive when `d ≥ 0` there and `d` vanishes only on a null
set. -/
theorem integral_two_div_pos {d : ℝ≥0 → ℝ} {σ : ℝ≥0} (hσ : 0 < σ) (hd : ∀ s ≤ σ, 0 ≤ d s)
    (hint : IntervalIntegrable (fun s : ℝ => 2 / d s.toNNReal) volume 0 σ)
    (hnull : volume {s : ℝ | 0 ≤ s ∧ s.toNNReal ≤ σ ∧ d s.toNNReal = 0} = 0) :
    0 < ∫ s in (0 : ℝ)..σ, 2 / d s.toNNReal := by
  have hσr : (0 : ℝ) < σ := hσ
  have hle : ∀ s ∈ Ioc (0 : ℝ) σ, s.toNNReal ≤ σ := fun s hs =>
    Real.toNNReal_le_iff_le_coe.2 hs.2
  have hnn : 0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) σ)] fun s : ℝ => 2 / d s.toNNReal := by
    rw [uIoc_of_le hσr.le]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    exact div_nonneg zero_le_two (hd _ (hle s hs))
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnn hint]
  refine ⟨hσr, ?_⟩
  set N : Set ℝ := {s : ℝ | 0 ≤ s ∧ s.toNNReal ≤ σ ∧ d s.toNNReal = 0}
  have hsub : Ioc (0 : ℝ) σ \ N ⊆ Function.support (fun s : ℝ => 2 / d s.toNNReal) ∩ Ioc 0 σ := by
    rintro s ⟨hs, hsN⟩
    refine ⟨?_, hs⟩
    have hd0 : d s.toNNReal ≠ 0 := fun h0 => hsN ⟨hs.1.le, hle s hs, h0⟩
    exact div_ne_zero two_ne_zero hd0
  calc (0 : ℝ≥0∞) < volume (Ioc (0 : ℝ) σ) := by
        rw [Real.volume_Ioc]; exact ENNReal.ofReal_pos.2 (by linarith)
    _ = volume (Ioc (0 : ℝ) σ \ N) := (measure_sdiff_null hnull).symm
    _ ≤ _ := measure_mono hsub

/-- **After a positive time the state is separated**: every left mark is strictly to the left of every
right mark (`V^{i,L}_σ < x_{i,L} ≤ 0 ≤ x_{j,R} < V^{j,R}_σ`, since the force drifts are of one sign and
vanish only on the null collision sets). -/
theorem sepStart_restart {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {σ : ℝ≥0}
    (hσ0 : 0 < σ) (hσ : (σ : ℝ≥0∞) < ζ) :
    SepStart ((fun i => vL i σ - w σ), fun j => vR j σ - w σ) := by
  have hfp := hp.isForcePath
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 bot_le) hσ
  have hs : ∀ s : ℝ≥0, s ≤ σ → (s : ℝ≥0∞) < ζ := fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) hσ
  intro i j
  show vL i σ - w σ < vR j σ - w σ
  have hxL : xL i ≤ 0 := by
    have := hfp.vL_le_w h0 i
    rwa [hfp.vL_zero i, hfp.w_zero] at this
  have hxR : 0 ≤ xR j := by
    have := hfp.w_le_vR h0 j
    rwa [hfp.vR_zero j, hfp.w_zero] at this
  -- the right mark has moved strictly right
  have hR : 0 < ∫ s in (0 : ℝ)..σ, 2 / (vR j s.toNNReal - w s.toNNReal) := by
    refine integral_two_div_pos (d := fun u => vR j u - w u) hσ0
      (fun s hsσ => sub_nonneg.2 (hfp.w_le_vR (hs s hsσ) j))
      (Restart.intervalIntegrable_two_div_gap (hfp.integrable_gapR hσ j)) ?_
    refine measure_mono_null ?_ (hfp.volume_collisionR j)
    rintro s ⟨h1, h2, h3⟩
    exact ⟨h1, hs _ h2, (sub_eq_zero.1 h3).symm⟩
  -- the left mark has moved strictly left
  have hL : 0 < ∫ s in (0 : ℝ)..σ, 2 / (w s.toNNReal - vL i s.toNNReal) := by
    refine integral_two_div_pos (d := fun u => w u - vL i u) hσ0
      (fun s hsσ => sub_nonneg.2 (hfp.vL_le_w (hs s hsσ) i)) ?_ ?_
    · simpa only [div_eq_mul_inv] using (hfp.integrable_gapL hσ i).const_mul 2
    · refine measure_mono_null ?_ (hfp.volume_collisionL i)
      rintro s ⟨h1, h2, h3⟩
      exact ⟨h1, hs _ h2, sub_eq_zero.1 h3⟩
  have eL : (∫ s in (0 : ℝ)..σ, 2 / (vL i s.toNNReal - w s.toNNReal)) =
      -∫ s in (0 : ℝ)..σ, 2 / (w s.toNNReal - vL i s.toNNReal) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show 2 / (vL i s.toNNReal - w s.toNNReal) = -(2 / (w s.toNNReal - vL i s.toNNReal))
    rw [← neg_sub (w s.toNNReal), div_neg]
  have hvL := hfp.vL_eq hσ i
  have hvR := hfp.vR_eq hσ j
  rw [eL] at hvL
  linarith

/-- For a separated force word the state stays separated at every time before the lifetime. -/
theorem sepStart_restart_of_sep {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hsep : ∀ i j, xL i < xR j) {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) :
    SepStart ((fun i => vL i σ - w σ), fun j => vR j σ - w σ) := by
  intro i j
  show vL i σ - w σ < vR j σ - w σ
  have h1 := hp.isForcePath.vL_le_xL hσ i
  have h2 := hp.isForcePath.xR_le_vR hσ j
  have := hsep i j
  linarith

/-! ### The conditional law at a stopping time -/

/-- Measurability of a start built from values at a time (stated over a general measurable space, to be
used with a stopping-time σ-algebra). -/
theorem measurable_start_aux {Ω' : Type*} [MeasurableSpace Ω'] {f : Ω' → ℝ} {gL : Fin nL → Ω' → ℝ}
    {gR : Fin nR → Ω' → ℝ} (hf : Measurable f) (hL : ∀ i, Measurable (gL i))
    (hR : ∀ j, Measurable (gR j)) :
    Measurable fun ω => ((fun i => gL i ω - f ω), fun j => gR j ω - f ω) :=
  (measurable_pi_iff.2 fun i => (hL i).sub hf).prodMk (measurable_pi_iff.2 fun j => (hR j).sub hf)

theorem measurable_eval_stop {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {T : Ω → ℝ≥0} {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyProgressive 𝓕 X)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) :
    Measurable[hT.measurableSpace] fun ω => X (T ω) ω := by
  have h := measurable_restart_eval_zero hX hT 0
  rwa [restartFiltration_zero] at h

/-- **The conditional law of a restarted evolution is the canonical law from the state at the stopping
time.** Let `(W, V, B)` be an integrated `SLE_a(ρ)` evolution (`a > 0`), `T` a finite stopping time of its
filtration and `A ∈ 𝓕_T` with `T < ζ` on `A`, and on `A` either `0 < T` or the force word separated (then
the state at `T` is separated, `sepStart_restart`, `sepStart_restart_of_sep`). For times `t_1, …, t_n` and
Borel sets `K_j`,

  `ℙ[A ∩ {t_j < ζ − T, (W_{T+t_j} − W_T, V_{T+t_j} − W_T, B_{T+t_j} − B_T) ∈ K_j for all j}]
    = ∫_A restartLaw(V_T − W_T) dℙ`,

where `restartLaw · s` is the killed-state law of every integrated evolution from the separated state `s`
(`measure_killedState_eq_restartLaw`) and is measurable in `s` (`measurable_restartLaw`). -/
theorem measure_restart_killedState {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (ha : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j))
    {n : ℕ} (ts : Fin n → ℝ≥0) {K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)}
    (hK : ∀ j, MeasurableSet (K j)) :
    P (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
        (W (T ω + ts j) ω - W (T ω) ω, (fun i => VL i (T ω + ts j) ω - W (T ω) ω),
          (fun i => VR i (T ω + ts j) ω - W (T ω) ω), B (T ω + ts j) ω - B (T ω) ω) ∈ K j}) =
      ∫⁻ ω in A, restartLaw a ρL ρR ts K
        ((fun i => VL i (T ω) ω - W (T ω) ω), fun j => VR j (T ω) ω - W (T ω) ω) ∂P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hlimE := hE.ae_tendsto_threshold ha
  obtain ⟨hBF, hWad, hVLad, hVRad, hpath⟩ := hE
  obtain ⟨Bv, hBvm, hBvc, hBvF, hBvae⟩ := exists_continuous_version hBF
  have h𝓕𝓖 : 𝓕 ≤ usualAugmentation 𝓕 P := Ito.le_usualAugmentation 𝓕 P
  have hT𝓖 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T ω : WithTop ℝ≥0) :=
    fun u => h𝓕𝓖 u _ (hT u)
  have hle𝓖 : hT.measurableSpace ≤ hT𝓖.measurableSpace :=
    Ito.measurableSpace_le_of_filtration_le h𝓕𝓖 hT hT𝓖
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  -- the state at `T`, through the progressive versions
  set st : Ω → (Fin nL → ℝ) × (Fin nR → ℝ) := fun ω =>
    ((fun i => progVersion ζ (VL i) (T ω) ω - progVersion ζ W (T ω) ω),
      fun j => progVersion ζ (VR j) (T ω) ω - progVersion ζ W (T ω) ω) with hst
  have hstT : Measurable[hT.measurableSpace] st :=
    @measurable_start_aux nL nR Ω hT.measurableSpace _ _ _
      (measurable_eval_stop (isStronglyProgressive_progVersion hWad) hT)
      (fun i => measurable_eval_stop (isStronglyProgressive_progVersion (hVLad i)) hT)
      (fun j => measurable_eval_stop (isStronglyProgressive_progVersion (hVRad j)) hT)
  have hstm : Measurable st := hstT.mono (hT.measurableSpace_le) le_rfl
  -- the restarted Brownian path: Wiener law, independent of `𝓖_T`
  set g : Ω → ℝ≥0 → ℝ := smPath Bv T with hg
  have hgm : Measurable g := measurable_smPath hBvc hBvm (measurable_of_isStoppingTime hT)
  have hind := indep_future hBvF
  have hlaw : P.map g = wienerPath :=
    map_path_eq_wienerPath
      (isBrownianReal_smShift hBvF.1.toIsPreBrownianReal hBvc hBvm hind hT𝓖).toIsPreBrownianReal
      hgm
  have hindT := indep_smPath hBvF.1.toIsPreBrownianReal hBvc hBvm hind hT𝓖
  have hpair : Measurable fun ω => (st ω, g ω) := hstm.prodMk hgm
  have hjoint : (P.restrict A).map (fun ω => (st ω, g ω)) =
      ((P.restrict A).map st).prod wienerPath := by
    refine (Measure.prod_eq fun D F hD hF => ?_).symm
    rw [Measure.map_apply hpair (hD.prod hF), Measure.map_apply hstm hD, ← hlaw,
      Measure.map_apply hgm hF, Measure.restrict_apply (hpair (hD.prod hF)),
      Measure.restrict_apply (hstm hD)]
    have hDA : MeasurableSet[hT𝓖.measurableSpace] (st ⁻¹' D ∩ A) :=
      hle𝓖 _ ((hstT hD).inter hA)
    have e : (fun ω => (st ω, g ω)) ⁻¹' (D ×ˢ F) ∩ A = (st ⁻¹' D ∩ A) ∩ g ⁻¹' F := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_prod]
      tauto
    rw [e]
    exact (Indep_iff _ _ _).1 hindT _ _ hDA ⟨F, hF, rfl⟩
  have hR := measurableSet_restartSet (a := a) (ρL := ρL) (ρR := ρR) ts hK
  have hmainA : P (A ∩ (fun ω => (st ω, g ω)) ⁻¹' restartSet a ρL ρR ts K) =
      ∫⁻ ω in A, restartLaw a ρL ρR ts K (st ω) ∂P := by
    rw [inter_comm, ← Measure.restrict_apply (hpair hR), ← Measure.map_apply hpair hR, hjoint,
      Measure.prod_apply hR]
    change ∫⁻ x, restartLaw a ρL ρR ts K x ∂((P.restrict A).map st) = _
    rw [lintegral_map (measurable_restartLaw ts hK) hstm]
  -- the identification, almost surely on `A`
  have hid : ∀ᵐ ω ∂P, ω ∈ A →
      ((∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
        (W (T ω + ts j) ω - W (T ω) ω, (fun i => VL i (T ω + ts j) ω - W (T ω) ω),
          (fun i => VR i (T ω + ts j) ω - W (T ω) ω), B (T ω + ts j) ω - B (T ω) ω) ∈ K j) ↔
        (st ω, g ω) ∈ restartSet a ρL ρR ts K) ∧
      st ω = ((fun i => VL i (T ω) ω - W (T ω) ω), fun j => VR j (T ω) ω - W (T ω) ω) := by
    filter_upwards [hpath, hBvae, hlimE] with ω hp hb hl hωA
    obtain ⟨hTζ, hT0⟩ := hAT ω hωA
    have h0 := restart_values hp hTζ
    have hst_eq : st ω = ((fun i => VL i (T ω) ω - W (T ω) ω),
        fun j => VR j (T ω) ω - W (T ω) ω) := by
      simp only [hst, h0.1, h0.2.1, h0.2.2]
    refine ⟨?_, hst_eq⟩
    rw [hst_eq]
    have hr := hp.restart hTζ
    have hb' : (fun t => B (T ω + t) ω - B (T ω) ω) = fun t => smShift Bv T t ω := by
      funext t; simp only [smShift, hb]
    rw [hb'] at hr
    have hsep : SepStart ((fun i => VL i (T ω) ω - W (T ω) ω), fun j => VR j (T ω) ω - W (T ω) ω) := by
      rcases hT0 with hT0 | hsx
      · exact sepStart_restart hp hT0 hTζ
      · exact sepStart_restart_of_sep hp hsx hTζ
    have hcode := codeOf_mem_cRel_of_path (Ω := Ω) (ω := ω)
      (xL := fun i => VL i (T ω) ω - W (T ω) ω) (xR := fun j => VR j (T ω) ω - W (T ω) ω)
      (W := fun t ω' => W (T ω' + t) ω' - W (T ω') ω')
      (VL := fun i t ω' => VL i (T ω' + t) ω' - W (T ω') ω')
      (VR := fun j t ω' => VR j (T ω' + t) ω' - W (T ω') ω')
      (B := smShift Bv T) (B' := smShift Bv T) (ζ := fun ω' => ζ ω' - T ω') hr
      (((hBvc ω).comp (continuous_const.add continuous_id)).sub continuous_const) (fun t => rfl)
      (restart_tendsto hTζ hl)
    set c := codeOf (fun i => VL i (T ω) ω - W (T ω) ω) (fun j => VR j (T ω) ω - W (T ω) ω)
      (smShift Bv T) (fun t ω' => W (T ω' + t) ω' - W (T ω') ω')
      (fun i t ω' => VL i (T ω' + t) ω' - W (T ω') ω')
      (fun j t ω' => VR j (T ω' + t) ω' - W (T ω') ω') (fun ω' => ζ ω' - T ω') ω with hc
    have hc1 : c.1 = enc (g ω) := rfl
    have hKc : (∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
        (W (T ω + ts j) ω - W (T ω) ω, (fun i => VL i (T ω + ts j) ω - W (T ω) ω),
          (fun i => VR i (T ω + ts j) ω - W (T ω) ω), B (T ω + ts j) ω - B (T ω) ω) ∈ K j) ↔
        c ∈ KSet ts K := by
      refine forall_congr' fun j => ?_
      refine ⟨fun ⟨hlt, hmem⟩ => ⟨hlt, ?_⟩, fun ⟨hlt, hmem⟩ => ⟨hlt, ?_⟩⟩
      · obtain ⟨e1, e2, e3, e4⟩ := hcode.2 (ts j) hlt
        rw [e1, funext e2, funext e3, e4]
        simpa only [smShift, hb] using hmem
      · obtain ⟨e1, e2, e3, e4⟩ := hcode.2 (ts j) hlt
        rw [e1, funext e2, funext e3, e4] at hmem
        simpa only [smShift, hb] using hmem
    show _ ↔ (_, enc (g ω)) ∈ lawSetF a ρL ρR ts K
    rw [mem_lawSetF_iff hsep, hKc, ← hc1]
    constructor
    · intro hk
      exact ⟨c, ⟨hcode.1, hk⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyK⟩, hy1⟩
      have : y = c := injOn_fst_cRel hsep hy hcode.1 hy1
      rw [← this]
      exact hyK
  -- conclusion
  have hset : (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
        (W (T ω + ts j) ω - W (T ω) ω, (fun i => VL i (T ω + ts j) ω - W (T ω) ω),
          (fun i => VR i (T ω + ts j) ω - W (T ω) ω), B (T ω + ts j) ω - B (T ω) ω) ∈ K j} :
        Set Ω) =ᵐ[P] A ∩ (fun ω => (st ω, g ω)) ⁻¹' restartSet a ρL ρR ts K := by
    filter_upwards [hid] with ω h
    refine propext ⟨fun ⟨h1, h2⟩ => ⟨h1, ((h h1).1).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, ((h h1).1).2 h2⟩⟩
  rw [measure_congr hset, hmainA]
  refine setLIntegral_congr_fun_ae hAm ?_
  filter_upwards [hid] with ω h hωA
  rw [(h hωA).2]

end Restart

end Sec2

end InteractingSLE
