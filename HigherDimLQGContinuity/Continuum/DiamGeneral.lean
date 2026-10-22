import HigherDimLQGContinuity.Continuum.Diam
import HigherDimLQGMetric.DGZ.TightCompact
import HigherDimLQGMetric.Sharp.SphereChainBound

/-! Buffered internal diameters on compact subsets of connected open sets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- A compact connected hull and a uniform collar turn local diameter bounds into an
internal diameter bound, with a deterministic step count. -/
theorem internalDiamRd_le_chain {d : ℕ} {U K : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsConnected U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (N : ℕ) (s R : ℝ), 0 < s ∧ s ≤ 1 ∧ 1 ≤ R ∧
      ∀ (E : ContMetric d) (M : ℝ≥0∞),
        (∀ z ∈ closedBall (0 : Rd d) R,
          internalDiamRd E (ball z s) (ball z (2 * s)) ≤ M) →
        internalDiamRd E K U ≤ (N : ℝ≥0∞) * M := by
  classical
  by_cases hKn : K.Nonempty
  · obtain ⟨T, hTc, hTp, hKT, hTU⟩ :=
      DGZ.exists_isCompact_isPreconnected_superset hU hUc hK hKU
    have hTn : T.Nonempty := hKn.mono hKT
    have hTconn : IsConnected T := ⟨hTn, hTp⟩
    obtain ⟨δ, hδ, hδU⟩ := hTc.exists_thickening_subset_open hU hTU
    obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Rd d)).mp hTc.isBounded
    let s : ℝ := min (δ / 4) 1
    have hs : 0 < s := lt_min (by positivity) (by norm_num)
    have hs1 : s ≤ 1 := min_le_right _ _
    have h2s : 2 * s < δ := by
      have := min_le_left (δ / 4) (1 : ℝ)
      linarith
    have hball : ∀ z ∈ T, ball z (2 * s) ⊆ U := by
      intro z hz w hw
      apply hδU
      exact Metric.ball_subset_thickening hz δ (lt_trans (Metric.mem_ball.mp hw) h2s)
    obtain ⟨N, hN⟩ := compact_connected_chain_bound hTc hTconn hs
    refine ⟨N, s, max 1 R₀, hs, hs1, le_max_left _ _, ?_⟩
    intro E M hloc
    unfold internalDiamRd
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    apply hN x (hKT hx) y (hKT hy) (fun a b => E.internal U a b)
    · intro z hz
      exact E.internal_self (hTU hz)
    · exact E.internal_triangle U
    · intro x y hxy
      have hxT := hxy.1
      have hyball : y ∈ ball x s := Metric.mem_ball.mpr (by simpa [dist_comm] using hxy.2.2)
      have hxball : x ∈ ball x s := mem_ball_self hs
      have hlocx := hloc x (closedBall_subset_closedBall (le_max_right _ _) (hR₀ hxT))
      calc
        E.internal U x y ≤ E.internal (ball x (2 * s)) x y := E.internal_anti (hball x hxT) _ _
        _ ≤ internalDiamRd E (ball x s) (ball x (2 * s)) :=
          le_iSup₂_of_le x hxball (le_iSup₂_of_le y hyball le_rfl)
        _ ≤ M := hlocx
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKn
    refine ⟨0, 1, 1, by norm_num, le_rfl, le_rfl, ?_⟩
    intro E M _
    simp [hKempty, internalDiamRd]

/-- The finite-ball form of the deterministic compact-set diameter estimate. -/
theorem internalDiamRd_le_finite_balls {d : ℕ} {U K : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsConnected U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (N : ℕ) (s : ℝ) (F : Finset (Rd d)), 0 < s ∧ s ≤ 1 ∧ F.card ≤ N ∧
      (∀ z ∈ F, ball z (2 * s) ⊆ U) ∧
      K ⊆ ⋃ z ∈ F, ball z s ∧
      ∀ E : ContMetric d,
        internalDiamRd E K U ≤ (N : ℝ≥0∞) *
          (⨆ z ∈ F, internalDiamRd E (ball z s) (ball z (2 * s))) := by
  classical
  by_cases hKn : K.Nonempty
  · obtain ⟨T, hTc, hTp, hKT, hTU⟩ :=
      DGZ.exists_isCompact_isPreconnected_superset hU hUc hK hKU
    have hTn : T.Nonempty := hKn.mono hKT
    have hTconn : IsConnected T := ⟨hTn, hTp⟩
    obtain ⟨δ, hδ, hδU⟩ := hTc.exists_thickening_subset_open hU hTU
    let s : ℝ := min (δ / 4) 1
    have hs : 0 < s := lt_min (by positivity) (by norm_num)
    have hs1 : s ≤ 1 := min_le_right _ _
    have h2s : 2 * s < δ := by
      have := min_le_left (δ / 4) (1 : ℝ)
      linarith
    have hball : ∀ z ∈ T, ball z (2 * s) ⊆ U := by
      intro z hz w hw
      apply hδU
      exact Metric.ball_subset_thickening hz δ (lt_trans (Metric.mem_ball.mp hw) h2s)
    obtain ⟨F₀, hF₀T, hF₀fin, hcov⟩ :=
      finite_cover_balls_of_compact hTc (by positivity : 0 < s / 4)
    let F : Finset (Rd d) := hF₀fin.toFinset
    have hFT : ∀ z ∈ F, z ∈ T := by
      intro z hz
      exact hF₀T (hF₀fin.mem_toFinset.mp hz)
    have hcov' : T ⊆ ⋃ z ∈ F, ball z (s / 4) := by
      simpa only [F, hF₀fin.mem_toFinset] using hcov
    obtain ⟨N₀, hN₀⟩ := compact_connected_chain_bound hTc hTconn (by positivity : 0 < s / 4)
    refine ⟨max N₀ F.card, s, F, hs, hs1, le_max_right _ _,
      (fun z hz => hball z (hFT z hz)), ?_, ?_⟩
    · intro x hx
      obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (hcov' (hKT hx))
      exact mem_iUnion₂.2 ⟨z, hz, Metric.mem_ball.mpr (by
        have := Metric.mem_ball.mp hxz
        linarith)⟩
    · intro E
      unfold internalDiamRd
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
      have hxy := hN₀ x (hKT hx) y (hKT hy) (fun a b => E.internal U a b)
        (fun z hz => E.internal_self (hTU hz)) (E.internal_triangle U)
        (⨆ z ∈ F, internalDiamRd E (ball z s) (ball z (2 * s))) ?_
      · have hNle : (N₀ : ℝ≥0∞) ≤ ((max N₀ F.card : ℕ) : ℝ≥0∞) := by
          exact_mod_cast (le_max_left N₀ F.card)
        exact hxy.trans (mul_le_mul_of_nonneg_right hNle (by positivity))
      · intro a b hab
        obtain ⟨z, hzF, haz⟩ := mem_iUnion₂.1 (hcov' hab.1)
        have ha : a ∈ ball z s := Metric.mem_ball.mpr (by
          have := Metric.mem_ball.mp haz
          linarith)
        have hb : b ∈ ball z s := Metric.mem_ball.mpr (by
          have hza := Metric.mem_ball.mp haz
          have hab' := hab.2.2
          calc
            dist b z ≤ dist b a + dist a z := dist_triangle _ _ _
            _ < s := by rw [dist_comm b a]; linarith)
        calc
          E.internal U a b ≤ E.internal (ball z (2 * s)) a b :=
            E.internal_anti (hball z (hFT z hzF)) _ _
          _ ≤ internalDiamRd E (ball z s) (ball z (2 * s)) :=
            le_iSup₂_of_le a ha (le_iSup₂_of_le b hb le_rfl)
          _ ≤ ⨆ z ∈ F, internalDiamRd E (ball z s) (ball z (2 * s)) :=
            le_iSup₂_of_le z hzF le_rfl
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKn
    refine ⟨0, 1, ∅, by norm_num, le_rfl, by simp, by simp, ?_, ?_⟩
    · simp [hKempty]
    · intro E
      simp [hKempty, internalDiamRd]

/-- Uniform positive moments of buffered diameters on every compact subset of a
bounded connected open set. -/
theorem continuum_diam {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ σ p : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hσ : 0 < σ) (hσμ : σ < μ) (hp : 0 < p)
    (hpb : 32 * p * b ≤ Real.sqrt (2 * d))
    (U K : Set (Rd d)) (hU : IsOpen U) (_hUb : Bornology.IsBounded U)
    (hUc : IsConnected U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        (∫⁻ g, (internalDiamRd (rho D g) K U) ^ p ∂(normLGFLaw d)) ≤
          ENNReal.ofReal C := by
  obtain ⟨N, s, R, hs, hs1, hR, hchain⟩ := internalDiamRd_le_chain hU hUc hK hKU
  obtain ⟨C₀, A, hfatou⟩ := continuum_fatou hd hκ hC1 hC2 hb hμ hμ1 hσ hσμ hp hpb
  refine ⟨(N : ℝ) ^ p * (C₀ * (1 + R) ^ A), fun ξ hξ D hD => ?_⟩
  obtain ⟨H, hHm, hH1, hHmom, hHpt⟩ := (hfatou ξ hξ D hD).2 R hR
  have hsmall : s ^ σ ≤ 1 := Real.rpow_le_one hs.le hs1 hσ.le
  have hpt : ∀ᵐ g ∂(normLGFLaw d),
      internalDiamRd (rho D g) K U ≤ ENNReal.ofReal ((N : ℝ) * H g) := by
    filter_upwards [hHpt] with g hg
    have hloc : ∀ z ∈ closedBall (0 : Rd d) R,
        internalDiamRd (rho D g) (ball z s) (ball z (2 * s)) ≤
          ENNReal.ofReal (H g) := by
      intro z hz
      have hsI : s ∈ Ioc (0 : ℝ) 1 := ⟨hs, hs1⟩
      have hbound := hg z hz s hsI
      have hm : H g * s ^ σ ≤ H g := by
        have hH0 : 0 ≤ H g := by linarith [hH1 g]
        nlinarith
      exact hbound.trans (ENNReal.ofReal_le_ofReal hm)
    have hh := hchain (rho D g) (ENNReal.ofReal (H g)) hloc
    calc
      internalDiamRd (rho D g) K U ≤ (N : ℝ≥0∞) * ENNReal.ofReal (H g) := hh
      _ = ENNReal.ofReal ((N : ℝ) * H g) := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (N : ℝ)), ENNReal.ofReal_natCast]
  have hpow : ∀ᵐ g ∂(normLGFLaw d),
      (internalDiamRd (rho D g) K U) ^ p ≤
        ENNReal.ofReal ((N : ℝ) ^ p) * ENNReal.ofReal (H g ^ p) := by
    filter_upwards [hpt] with g hg
    calc
      (internalDiamRd (rho D g) K U) ^ p ≤
          ENNReal.ofReal ((N : ℝ) * H g) ^ p := ENNReal.rpow_le_rpow hg hp.le
      _ = ENNReal.ofReal ((N : ℝ) ^ p) * ENNReal.ofReal (H g ^ p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg
            (mul_nonneg (Nat.cast_nonneg _) (by linarith [hH1 g])) hp.le,
          Real.mul_rpow (by positivity : 0 ≤ (N : ℝ)) (by linarith [hH1 g]),
          ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : 0 ≤ (N : ℝ)) _)]
  calc
    (∫⁻ g, (internalDiamRd (rho D g) K U) ^ p ∂(normLGFLaw d)) ≤
        ∫⁻ g, ENNReal.ofReal ((N : ℝ) ^ p) * ENNReal.ofReal (H g ^ p)
          ∂(normLGFLaw d) := lintegral_mono_ae hpow
    _ = ENNReal.ofReal ((N : ℝ) ^ p) *
        (∫⁻ g, ENNReal.ofReal (H g ^ p) ∂(normLGFLaw d)) :=
      lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hHm.pow_const p))
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ p) * ENNReal.ofReal (C₀ * (1 + R) ^ A) := by
      gcongr
    _ = ENNReal.ofReal ((N : ℝ) ^ p * (C₀ * (1 + R) ^ A)) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : 0 ≤ (N : ℝ)) _)]

end HigherDimLQGContinuity
