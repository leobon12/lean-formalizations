import HigherDimLQGContinuity.SiteEvents.TrialBase
import HigherDimLQGContinuity.Events.Local
import HigherDimLQGContinuity.Caps.Locality
import HigherDimLQGMetric.Sec6.Geometry

/-! Concentric seed trials and finite-edge amplification. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Trial radii `L·8^{-(j+1)}/4`, with zero-based Lean indices. -/
def seedTrialRadius (L : ℝ) (j : ℕ) : ℝ := L / 4 * (1 / 8 : ℝ) ^ (j + 1)

theorem seedTrialRadius_pos {L : ℝ} (hL : 0 < L) (j : ℕ) :
    0 < seedTrialRadius L j := by
  unfold seedTrialRadius
  positivity

theorem seedTrialRadius_step (L : ℝ) (j : ℕ) :
    seedTrialRadius L (j + 1) = (1 / 8 : ℝ) * seedTrialRadius L j := by
  unfold seedTrialRadius
  rw [show j + 1 + 1 = j + 1 + 1 by rfl, pow_succ]
  ring

theorem seedTrialRadius_le {L : ℝ} (hL : 0 ≤ L) (j : ℕ) :
    seedTrialRadius L j ≤ L / 32 := by
  unfold seedTrialRadius
  have hp : (1 / 8 : ℝ) ^ (j + 1) ≤ 1 / 8 := by
    rw [pow_succ]
    have hpow : (1 / 8 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  nlinarith

/-- Shell-decoupling bound for failures of a fixed base event around one centre. -/
theorem seedTrials_one_center (hd : 2 ≤ d) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (T : Set (DistRd d))
        (_hT : AEEventIn (pinLaw d 1) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4)) T)
        {q L : ℝ} (_hq : 0 ≤ q) (_hL : 0 < L)
        (_hfail : pinLaw d 1 Tᶜ ≤ ENNReal.ofReal q)
        (c : Rd d) (N : ℕ),
        pinLaw d 1 {g | ∀ j ∈ Finset.range N,
          recentre 1 (seedTrialRadius L j) c g ∉ T} ≤
            ENNReal.ofReal (q ^ ((N : ℝ) / K)) := by
  obtain ⟨K, hK, hdec⟩ := p4_shell_event_bound (by omega : 1 ≤ d)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 4) (by norm_num : (0 : ℝ) < 1 / 8)
    (by norm_num : (1 / 8 : ℝ) < 1)
  refine ⟨K, hK, ?_⟩
  intro T hT q L hq hL hfail c N
  let B (j : ℕ) : Set (DistRd d) :=
    {g | recentre 1 (seedTrialRadius L j) c g ∈ Tᶜ}
  have hlocal (j : ℕ) :
      AEEventIn (pinLaw d 1)
        (fieldSigma0 id (ann c ((1 / 2) * seedTrialRadius L j)
          (4 * seedTrialRadius L j))) (B j) := by
    have hr := seedTrialRadius_pos hL j
    have hgeom : affinePt (seedTrialRadius L j) c ''
        ann (0 : Rd d) (1 / 2) 4 ⊆
        ann c ((1 / 2) * seedTrialRadius L j) (4 * seedTrialRadius L j) := by
      change ((fun x : Rd d => seedTrialRadius L j • x + c) ''
        ann (0 : Rd d) (1 / 2) 4) ⊆ _
      simpa only [mul_comm] using
        (S6a.image_ann_affine_eq hr c (1 / 2) 4).le
    exact p4_aeEventIn_recentre hd one_pos one_pos hr c hgeom
      (p5b_aeEventIn_compl hT)
  have hprob (j : ℕ) : pinLaw d 1 (B j) ≤ ENNReal.ofReal q :=
    (pinLaw_preimage_recentre_le hd one_pos one_pos
      (seedTrialRadius_pos hL j) c Tᶜ).trans hfail
  have hbound := @hdec _ _ (pinLaw d 1) (isProbabilityMeasure_pinLaw hd 1)
    id (isWholeSpaceLGF_pinLaw hd one_pos).1 c (seedTrialRadius L)
    (seedTrialRadius_pos hL)
    (fun j => (seedTrialRadius_step L j).le) B hlocal (Finset.range N) q hq
    (fun j _ => hprob j)
  simpa only [Finset.card_range, B, Set.mem_ofPred_eq, Set.mem_compl_iff] using hbound

/-- A finite union over edge centres after concentric decoupling. -/
theorem seedTrials_finite_bound (hd : 2 ≤ d) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι : Type} (E : Finset ι) (c : ι → Rd d)
        (T : Set (DistRd d))
        (_hT : AEEventIn (pinLaw d 1) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4)) T)
        {q L : ℝ} (_hq : 0 ≤ q) (_hL : 0 < L)
        (_hfail : pinLaw d 1 Tᶜ ≤ ENNReal.ofReal q) (N : ℕ),
        pinLaw d 1 {g | ∃ e ∈ E, ∀ j ∈ Finset.range N,
          recentre 1 (seedTrialRadius L j) (c e) g ∉ T} ≤
            ENNReal.ofReal ((E.card : ℝ) * q ^ ((N : ℝ) / K)) := by
  classical
  obtain ⟨K, hK, hcenter⟩ := seedTrials_one_center hd
  refine ⟨K, hK, ?_⟩
  intro ι E c T hT q L hq hL hfail N
  have hsum : pinLaw d 1 (⋃ e ∈ E, {g | ∀ j ∈ Finset.range N,
      recentre 1 (seedTrialRadius L j) (c e) g ∉ T}) ≤
      ENNReal.ofReal ((E.card : ℝ) * q ^ ((N : ℝ) / K)) := by
    calc
      pinLaw d 1 _ ≤ ∑ e ∈ E, pinLaw d 1 {g | ∀ j ∈ Finset.range N,
          recentre 1 (seedTrialRadius L j) (c e) g ∉ T} := measure_biUnion_finset_le E _
      _ ≤ ∑ _e ∈ E, ENNReal.ofReal (q ^ ((N : ℝ) / K)) :=
        Finset.sum_le_sum (fun e _ => hcenter T hT hq hL hfail (c e) N)
      _ = ENNReal.ofReal ((E.card : ℝ) * q ^ ((N : ℝ) / K)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
        simp
  have heq : {g | ∃ e ∈ E, ∀ j ∈ Finset.range N,
      recentre 1 (seedTrialRadius L j) (c e) g ∉ T} =
      ⋃ e ∈ E, {g | ∀ j ∈ Finset.range N,
        recentre 1 (seedTrialRadius L j) (c e) g ∉ T} := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    tauto
  rw [heq]
  exact hsum

/-- A finite number of trials suffices for any prescribed positive failure budget. -/
theorem seedTrials_choose_N (n : ℕ) {pstar p K : ℝ}
    (hpstar : 0 < pstar) (hpstar1 : pstar < 1) (hp : 0 < p) (hK : 1 ≤ K) :
    ∃ N : ℕ, (n : ℝ) * (1 - pstar / 4) ^ ((N : ℝ) / K) ≤ p := by
  let q : ℝ := 1 - pstar / 4
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hK0 : 0 < K := by linarith
  let b : ℝ := q ^ K⁻¹
  have hb0 : 0 < b := Real.rpow_pos_of_pos hq0 _
  have hb1 : b < 1 := Real.rpow_lt_one hq0.le hq1 (inv_pos.mpr hK0)
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hp hn1) hb1
  refine ⟨N, ?_⟩
  have heq : q ^ ((N : ℝ) / K) = b ^ N := by
    calc
      q ^ ((N : ℝ) / K) = q ^ (K⁻¹ * (N : ℝ)) := by congr 1; ring
      _ = b ^ N := Real.rpow_mul_natCast hq0.le K⁻¹ N
  change (n : ℝ) * q ^ ((N : ℝ) / K) ≤ p
  rw [heq]
  have hbN : 0 ≤ b ^ N := pow_nonneg hb0.le _
  rw [lt_div_iff₀ hn1] at hN
  nlinarith only [hN, hbN]

/-- Lemma `b:lem-trials`: concentric seed trials succeed at every edge with high probability. -/
theorem seedTrials_prob (hd : 2 ≤ d) {ξbar : ℝ}
    (hU : ∀ s ∈ Icc (1 : ℝ) 10, UniformEstimates d ξbar s) :
    ∃ pstar v₀ C₄ c₄ H₀ σ₀ β₀ m M Hsd σsd K : ℝ,
      0 < pstar ∧ pstar < 1 ∧ 0 < v₀ ∧ v₀ ≤ 1 / 2 ∧ 0 < C₄ ∧ 0 < c₄ ∧
      0 < σ₀ ∧ σ₀ < 1 ∧ 1 < β₀ ∧ 0 < m ∧ m < M ∧ 1 ≤ H₀ ∧
      1 ≤ Hsd ∧ 0 < σsd ∧ σsd ≤ 1 ∧ 1 ≤ K ∧
      ∀ {ι : Type} (F : Finset ι) (c : ι → Rd d) {p L : ℝ},
        0 < p → 0 < L →
        ∃ Ntr : ℕ, ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ η ∈ Ioc (0 : ℝ) ξbar,
          ∀ D E : DistRd d → ContMetric d,
          IsStrongExpMetric d ξ (distExp d ξ) D →
          IsStrongExpMetric d η (distExp d η) E →
          ∀ v : ℝ, 0 < v → v < v₀ → |η - ξ| ≤ c₄ * v ^ C₄ →
            pinLaw d 1 {g | ∃ e ∈ F, ∀ j ∈ Finset.range Ntr,
              recentre 1 (seedTrialRadius L j) (c e) g ∉
                seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd} ≤ ENNReal.ofReal p := by
  classical
  obtain ⟨pstar, v₀, C₄, c₄, hpstar, hpstar1, hv₀, hv₀1, hC₄, hc₄,
    H₀, σ₀, β₀, m, M, hσ₀, hσ₀1, hβ₀, hm, hmM, hH₀, _hrefs, hmain⟩ :=
      lemma34 hd hU
  obtain ⟨Hsd, σsd, hHsd, hσsd, hσsd1, hdup⟩ :=
    dupper_prob hd (hU 1 (by norm_num)) (by positivity : 0 < pstar / 16)
  obtain ⟨K, hK, hfinite⟩ := seedTrials_finite_bound hd
  refine ⟨pstar, v₀, C₄, c₄, H₀, σ₀, β₀, m, M, Hsd, σsd, K,
    hpstar, hpstar1, hv₀, hv₀1, hC₄, hc₄, hσ₀, hσ₀1, hβ₀,
    hm, hmM, hH₀, hHsd, hσsd, hσsd1, hK, ?_⟩
  intro ι F c p L hp hL
  obtain ⟨Ntr, hNtr⟩ := seedTrials_choose_N F.card hpstar hpstar1 hp hK
  refine ⟨Ntr, ?_⟩
  intro ξ hξ η hη D E hD hE v hv hvv hτ
  let T := seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd
  have hgood : ENNReal.ofReal (pstar / 4) ≤ pinLaw d 1 T :=
    seedTrial_base_prob hd hpstar
      (fun ξ hξ η hη D E hD hE v hv hvv hτ =>
        (hmain ξ hξ η hη D E hD hE v hv hvv hτ).2)
      (fun ζ hζ A hA => by
        simpa only [siteA] using (hdup ζ hζ A hA).1)
      hξ hη D E hD hE hv hvv hτ
  have hlocal : AEEventIn (pinLaw d 1)
      (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4)) T :=
    seedTrial_base_local hd hξ.1 hη.1 hD hE (by linarith) hσsd.le
  have hfail : pinLaw d 1 Tᶜ ≤ ENNReal.ofReal (1 - pstar / 4) :=
    seedTrial_base_fail_prob hd hD hE (by linarith) hσsd.le hpstar hgood
  have hbound := hfinite F c T hlocal (by linarith : 0 ≤ 1 - pstar / 4)
    hL hfail Ntr
  exact hbound.trans (ENNReal.ofReal_le_ofReal hNtr)

end HigherDimLQGContinuity
