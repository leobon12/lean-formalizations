/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP3Bessel

/-!
# Lemma LP3: one steering-and-swallowing stage

Packet PROVE-LP15. Supplement §6.3, proof of Lemma LP3 (`source/spec/p481-528.md` L25–L33, pp. 481–482): "First
consider swallowing one prescribed inner point `p` while both outer points remain unswallowed. […] if `p > w`,
move the driver monotonically from `w` to `p − ε` in time `T ≤ ε²/16` […] The target characteristic is
nondecreasing and its gap stays at least `ε`, so its total displacement is at most `2T/ε ≤ ε/8`. […] Continuous
dependence of those real characteristics on the driver and Brownian full support give a positive-probability
neighborhood of this final configuration. […] It controls every initial gap in the indicated interval
simultaneously. For `ε` small relative to `δ/K`, the two outer gaps cannot vanish."

Here the "continuous dependence" is replaced by the two-sided bound `x − W_t ≤ u_t(x) ≤ x − W_t + 2t/m` of
`re_le_of_isForwardSol`, and the target's starting point may vary in a window `|p − p₀| ≤ η` (needed to compose
two stages).

* `stage_det`: the deterministic stage. If the driver stays within `ηs` of the steering path
  `f(t) = (p₀ − ε) min(t/T, 1)`, `T = ε²/16`, and after `T` the restarted driver kills `2ε` within time `S`
  while moving by at most `ξ`, then the target `p` is not alive at `T + S`, and the driver stays in
  `(−ηs − ξ, p₀ − ε + ηs + ξ]` with final value within `ηs + ξ` of `p₀ − ε`.
* `exists_stageEvent`: the stage has positive probability (the support theorem and the Bessel step, split by the
  Markov property at `T`), on an event of the past at `T + S`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat
open QuantumZipper QuantumZipper.RS

namespace InteractingSLE.LP.LP3

/-- The steering path: from `0` to `p₀ − ε` linearly on `[0, T]`, then constant. -/
def steer (p₀ ε T : ℝ) (t : ℝ) : ℝ := (p₀ - ε) * min (t / T) 1

theorem continuous_steer (p₀ ε T : ℝ) : Continuous (steer p₀ ε T) :=
  continuous_const.mul ((continuous_id.div_const T).min continuous_const)

theorem steer_zero (p₀ ε T : ℝ) : steer p₀ ε T 0 = 0 := by simp [steer]

theorem steer_mem {p₀ ε T t : ℝ} (hpε : ε ≤ p₀) (hT : 0 < T) (ht : 0 ≤ t) :
    0 ≤ steer p₀ ε T t ∧ steer p₀ ε T t ≤ p₀ - ε := by
  have h0 : 0 ≤ min (t / T) 1 := le_min (div_nonneg ht hT.le) zero_le_one
  have h1 : min (t / T) 1 ≤ 1 := min_le_right _ _
  have hp : 0 ≤ p₀ - ε := by linarith
  exact ⟨mul_nonneg hp h0, by unfold steer; nlinarith⟩

theorem steer_self {p₀ ε T : ℝ} (hT : 0 < T) : steer p₀ ε T T = p₀ - ε := by
  simp [steer, div_self hT.ne']

/-! ### The deterministic stage -/

section Det

variable {W : ℝ → ℝ}

/-- **The deterministic stage.** -/
theorem stage_det (hW : Continuous W) (hW0 : W 0 = 0) {ε p₀ p η ηs ξ S : ℝ} (hε : 0 < ε)
    (hp₀ : 2 * ε ≤ p₀) (hpη : |p - p₀| ≤ η) (hη : 0 ≤ η) (hηs : 0 ≤ ηs) (hsmall : η + ηs ≤ ε / 4)
    (hS : 0 ≤ S)
    (htube : ∀ t ∈ Icc (0 : ℝ) (ε ^ 2 / 16), |W t - steer p₀ ε (ε ^ 2 / 16) t| < ηs)
    (hdead : ¬ Alive (fun r => W (ε ^ 2 / 16 + r) - W (ε ^ 2 / 16)) (2 * ε) S)
    (hmove : ∀ r ∈ Icc (0 : ℝ) S, |W (ε ^ 2 / 16 + r) - W (ε ^ 2 / 16)| ≤ ξ) :
    ¬ Alive W p (ε ^ 2 / 16 + S) ∧
      (∀ t ∈ Icc (0 : ℝ) (ε ^ 2 / 16 + S), -(ηs + ξ) < W t ∧ W t < p₀ - ε + ηs + ξ) ∧
      |W (ε ^ 2 / 16 + S) - (p₀ - ε)| < ηs + ξ := by
  set T : ℝ := ε ^ 2 / 16 with hTdef
  have hT : 0 < T := by positivity
  have hpε : ε ≤ p₀ := by linarith
  have hξ : 0 ≤ ξ := (abs_nonneg _).trans (hmove 0 ⟨le_rfl, hS⟩)
  have hWT : |W T - (p₀ - ε)| < ηs := by
    have := htube T ⟨hT.le, le_rfl⟩
    rwa [steer_self hT] at this
  have hηle : |p - p₀| ≤ ε / 4 := hpη.trans (by linarith)
  have hp_lo : p₀ - ε / 4 ≤ p := by linarith [(abs_le.1 hηle).1]
  have hp_hi : p ≤ p₀ + η := by linarith [(abs_le.1 hpη).2]
  -- the target is alive on `[0, T]` with gap `≥ 3ε/4`
  have hm : 0 < 3 * ε / 4 := by positivity
  have hgap : ∀ t ∈ Icc (0 : ℝ) T, W t + 3 * ε / 4 ≤ p := by
    intro t ht
    have h1 := (abs_lt.1 (htube t ht)).2
    have h2 := (steer_mem hpε hT ht.1).2
    have h3 : -(p - p₀) ≤ η := (neg_le_abs _).trans hpη
    linarith
  obtain ⟨v, hv, hvlow⟩ := exists_isForwardSol_of_forall_add_le hW hT.le hm hgap
  have hvm : ∀ t ∈ Icc (0 : ℝ) T, 3 * ε / 4 ≤ (v t).re := fun t ht => by
    have := hvlow t ht; have := hgap t ht; linarith
  have hppos : 0 < p := by linarith
  have hvT := (re_le_of_isForwardSol hW hW0 hm hv hvm T ⟨hT.le, le_rfl⟩).2
  have hdisp : 2 * T / (3 * ε / 4) = ε / 6 := by rw [hTdef]; field_simp; ring
  have hvT' : (v T).re ≤ 2 * ε := by
    have h1 := (abs_lt.1 hWT).1
    rw [hdisp] at hvT
    linarith
  refine ⟨not_alive_of_restart hW hW0 hppos hT.le hS hv hvT' hdead, fun t ht => ?_, ?_⟩
  · rcases le_or_gt t T with htT | htT
    · have h1 := abs_lt.1 (htube t ⟨ht.1, htT⟩)
      have h2 := steer_mem hpε hT ht.1
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have hr : t - T ∈ Icc (0 : ℝ) S := ⟨by linarith, by linarith [ht.2]⟩
      have h1 := abs_le.1 (hmove (t - T) hr)
      have e : T + (t - T) = t := by ring
      rw [e] at h1
      have h2 := abs_lt.1 hWT
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · have h1 := abs_le.1 (hmove S ⟨hS, le_rfl⟩)
    have h2 := abs_lt.1 hWT
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end Det

/-! ### The probabilistic stage -/

/-- A set measurable for `comap f` is measurable for `comap g` when `f` factors measurably through `g`. -/
theorem measurableSet_comap_of_factor {α β γ : Type*} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    {f : α → β} {g : α → γ} {Φ : γ → β} (hΦ : Measurable Φ) (hfg : ∀ a, f a = Φ (g a)) {A : Set α}
    (hA : MeasurableSet[MeasurableSpace.comap f mβ] A) : MeasurableSet[MeasurableSpace.comap g mγ] A := by
  obtain ⟨s, hs, rfl⟩ := hA
  refine ⟨Φ ⁻¹' s, hΦ hs, ?_⟩
  ext a; simp [hfg]

section Prob

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℝ≥0 → Ω → ℝ}

/-- **The stage has positive probability.** For a Brownian motion `X` with continuous paths vanishing at `0`, Bessel
constants `K, M` (`exists_bessel_constants`), a scale `ε`, a centre `p₀` and a tube width `ηs > 0`, there is an
event of the past at `T + S` (`T = ε²/16`, `S = ε² K`) of positive probability on which the driver `√κ X` stays
within `ηs` of the steering path on `[0, T]`, and after `T` kills `2ε` within `S` while moving by at most `Mε`. -/
theorem exists_stageEvent (hX : IsBrownianReal X P) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ ω, Continuous (X · ω)) {κ : ℝ} (hκ : 0 < κ) {K M : ℝ≥0}
    (hKM : ∀ {X' : ℝ≥0 → Ω → ℝ}, IsPreBrownianReal X' P → (∀ t, Measurable (X' t)) →
      1 / 2 ≤ P.real {ω | stopPath K (fun t => X' t ω) ∈ besselSet κ K M})
    {ε : ℝ≥0} (hε : ε ≠ 0) (p₀ : ℝ) {ηs : ℝ} (hηs : 0 < ηs) :
    ∃ E : Set Ω, MeasurableSet[MeasurableSpace.comap
        (fun ω (r : Iic (ε ^ 2 / 16 + ε ^ 2 * K)) => X r ω) MeasurableSpace.pi] E ∧ 0 < P E ∧
      ∀ ω ∈ E,
        (∀ t ∈ Icc (0 : ℝ) ((ε : ℝ) ^ 2 / 16),
          |pathDrive (√κ) (fun s => X s ω) t - steer p₀ ε ((ε : ℝ) ^ 2 / 16) t| < ηs) ∧
        ¬ Alive (fun r => pathDrive (√κ) (fun s => X s ω) ((ε : ℝ) ^ 2 / 16 + r) -
          pathDrive (√κ) (fun s => X s ω) ((ε : ℝ) ^ 2 / 16)) (2 * ε) ((ε : ℝ) ^ 2 * K) ∧
        ∀ r ∈ Icc (0 : ℝ) ((ε : ℝ) ^ 2 * K),
          |pathDrive (√κ) (fun s => X s ω) ((ε : ℝ) ^ 2 / 16 + r) -
            pathDrive (√κ) (fun s => X s ω) ((ε : ℝ) ^ 2 / 16)| ≤ M * ε := by
  set T : ℝ≥0 := ε ^ 2 / 16 with hTdef
  set S : ℝ≥0 := ε ^ 2 * K with hSdef
  have hTr : (T : ℝ) = (ε : ℝ) ^ 2 / 16 := by rw [hTdef]; push_cast; ring
  have hSr : (S : ℝ) = (ε : ℝ) ^ 2 * K := by rw [hSdef]; push_cast; ring
  have hsκ : 0 < √κ := Real.sqrt_pos.2 hκ
  -- the tube event
  set g : ℝ≥0 → ℝ := fun t => steer p₀ ε ((ε : ℝ) ^ 2 / 16) t / √κ with hg
  have hgc : Continuous g := ((continuous_steer _ _ _).comp NNReal.continuous_coe).div_const _
  have hg0 : g 0 = 0 := by simp [hg, steer_zero]
  set δ : ℝ := ηs / (2 * √κ) with hδ
  have hδpos : 0 < δ := by positivity
  set tube : Set Ω := {ω | ∀ q : ℚ≥0, (q : ℝ≥0) ≤ T → |X q ω - g q| < δ} with htube
  have htubeP : 0 < P tube := BrownianSupport.measure_ratTube_pos hX hXm hgc hg0 T hδpos
  have htube_past : MeasurableSet[MeasurableSpace.comap (fun ω (r : Iic T) => X r ω) MeasurableSpace.pi]
      tube := ⟨BrownianSupport.pastTube g δ T, BrownianSupport.measurableSet_pastTube g δ T, rfl⟩
  -- the Bessel event
  set Y : ℝ≥0 → Ω → ℝ := fun r ω => X (T + r) ω - X T ω with hY
  have hYB : IsPreBrownianReal Y P := hX.toIsPreBrownianReal.shift T
  have hYm : ∀ t, Measurable (Y t) := fun t => (hXm _).sub (hXm _)
  set Bev : Set Ω := scaledBesselEvent κ K M ε Y with hBev
  have hBevP : 1 / 2 ≤ P.real Bev :=
    hKM (isPreBrownianReal_scaledPath hYB hε) fun t => (hYm _).const_mul _
  have hBev_pastY := measurableSet_scaledBesselEvent (Y := Y) κ K M ε
  have hBev_path : MeasurableSet[MeasurableSpace.comap (fun ω r => X (T + r) ω - X T ω)
      MeasurableSpace.pi] Bev :=
    measurableSet_comap_of_factor (Φ := fun y (r : Iic (ε ^ 2 * K)) => y r)
      (measurable_pi_iff.2 fun r => measurable_pi_apply _) (fun _ => rfl) hBev_pastY
  have hEP : P (tube ∩ Bev) = P tube * P Bev :=
    measure_inter_eq_mul_of_past hX.toIsPreBrownianReal T htube_past hBev_path
  have hBevpos : 0 < P Bev := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [measureReal_def, h0, ENNReal.toReal_zero] at hBevP
    norm_num at hBevP
  refine ⟨tube ∩ Bev, ?_, ?_, ?_⟩
  · refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_comap_of_factor
        (Φ := fun x (r : Iic T) => x ⟨r, mem_Iic.2 ((mem_Iic.1 r.2).trans le_self_add)⟩)
        (measurable_pi_iff.2 fun r => measurable_pi_apply _) (fun _ => rfl) htube_past
    · exact measurableSet_comap_of_factor
        (Φ := fun x (r : Iic (ε ^ 2 * K)) => x ⟨T + r, mem_Iic.2 (add_le_add (le_refl T) (mem_Iic.1 r.2))⟩ -
          x ⟨T, mem_Iic.2 le_self_add⟩)
        (measurable_pi_iff.2 fun r => Measurable.sub (measurable_pi_apply (X := fun _ : Iic (T + S) => ℝ) _)
          (measurable_pi_apply _)) (fun _ => rfl)
        hBev_pastY
  · rw [hEP]; exact ENNReal.mul_pos htubeP.ne' hBevpos.ne'
  · rintro ω ⟨hωt, hωB⟩
    have hYc : Continuous fun t => Y t ω :=
      ((hXc ω).comp (continuous_const.add continuous_id)).sub continuous_const
    have hY0 : Y 0 ω = 0 := by simp [hY]
    obtain ⟨hdead, hmov⟩ := scaledBesselEvent_spec hε hYc hY0 hωB
    have hT0 : ((ε : ℝ) ^ 2 / 16).toNNReal = T := by rw [← hTr, Real.toNNReal_coe]
    have hkey : ∀ r : ℝ, 0 ≤ r →
        pathDrive (√κ) (fun s => X s ω) ((ε : ℝ) ^ 2 / 16 + r) -
          pathDrive (√κ) (fun s => X s ω) ((ε : ℝ) ^ 2 / 16) =
        pathDrive (√κ) (fun t => Y t ω) r := by
      intro r hr
      simp only [pathDrive, hY]
      rw [Real.toNNReal_add (by positivity) hr, hT0]
      ring
    refine ⟨fun t ht => ?_, fun ha => hdead ?_, fun r hr => ?_⟩
    · have hφ : Continuous fun s : ℝ≥0 => |X s ω - g s| := ((hXc ω).sub hgc).abs
      have htT : t.toNNReal ≤ T := by
        rw [Real.toNNReal_le_iff_le_coe, hTr]; exact ht.2
      have h1 := BrownianSupport.le_of_forall_nnrat_lt hφ (fun q hq => hωt q hq) _ htT
      have e1 : pathDrive (√κ) (fun s => X s ω) t - steer p₀ ε ((ε : ℝ) ^ 2 / 16) t =
          √κ * (X t.toNNReal ω - g t.toNNReal) := by
        simp only [pathDrive, hg, Real.coe_toNNReal _ ht.1]
        field_simp
      rw [e1, abs_mul, abs_of_pos hsκ]
      calc √κ * |X t.toNNReal ω - g t.toNNReal| ≤ √κ * δ := mul_le_mul_of_nonneg_left h1 hsκ.le
        _ = ηs / 2 := by rw [hδ]; field_simp
        _ < ηs := half_lt_self hηs
    · obtain ⟨u, hu⟩ := ha
      exact ⟨u, QuantumZipper.isForwardSol_congr_drive (fun r hr => hkey r hr.1) hu⟩
    · rw [hkey r hr.1]
      have hr' : r.toNNReal ≤ ε ^ 2 * K := by
        rw [Real.toNNReal_le_iff_le_coe]; push_cast; exact hr.2
      exact hmov _ hr'

end Prob

end InteractingSLE.LP.LP3
