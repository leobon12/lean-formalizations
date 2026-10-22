import HigherDimLQGContinuity.Amplify.RoughDet
import HigherDimLQGContinuity.Amplify.Conn
import HigherDimLQGContinuity.Amplify.Lemma32Num
import HigherDimLQGContinuity.Events.RefsProb
import HigherDimLQGContinuity.Events.Local

/-!
# Lemma 3.2: rough comparison (packet P7)

Blueprint Part A, Lemma `a:lem32` ([C] Lemma 3.2, p. 7, l. 341–359; NA1 item 23, R8; NA0 §2.3; erratum EA `a:err-32`).

**Statement** (`lemma32`). Let `d ≥ 2` and assume Lemma 2.1 (`UniformEstimates d ξ̄ s`, interface I1) for all pins
`s ∈ [1, 10]`. There is `C_b > 4` (namely `C_b = 4M/m` for the references of `refs_prob` at pin `1` with failure
`p_cov`) such that for every global pin `s₀ ∈ [1, 10]` there are `C₃₂, c₃₂ > 0` with: for all `ξ, η ∈ (0, ξ̄]`, `D, E`
strong at `(ξ, Q(ξ))`, `(η, Q(η))`, `R ≥ 1`, `e, q ∈ (0, 1/8)` and
`n ≥ C₃₂ (1 + log(1 + R) + log e⁻¹ + log q⁻¹)`, `|η - ξ| n ≤ c₃₂`:
`𝐏_{s₀}{g : ¬ (Comp(ρ^E_g, ρ^D_g; C_b, e, R) ∧ Comp(ρ^D_g, ρ^E_g; C_b, e, R))} ≤ q`.

**Proof** (blueprint, with the numerics of `Amplify/Lemma32Num.lean`). Events under `𝐏_{s₀}`: (G1) the escape event
(E5) with `K = 1` at radius `R + 1` and factor `S = e^{κ_S Λ}` for `ρ^D` and `ρ^E`; (G2) the envelopes (E1) of
`ρ^D`, `ρ^E` at radius `W + 1`, `W = S (R + 1)`, below `H̄ = e^{κ_H Λ}` (Markov); (G3) the covering (2.10) in the full
band `V = n/4` with local pin `1` and the local event `PairRefs(D, E)` (`cover210_full`, `local_events_aeEventIn`,
`refs_prob`); (G4) the scale cap of Lemma 2.2 on the grid of depth `⌈n⌉` and radius `W + 1` (`lemma22`). Each fails with
probability `≤ q/8`. Off a null set (E6 geodesics, envelope bounds, `connector_of_good` at all grid balls) and on all
the events, the deterministic step `p7_rough_of_band` (Lemma 3.1(a) + the envelope) gives both comparisons.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open Set Metric MeasureTheory Filter
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)
open HigherDimLQGMetric
open scoped ENNReal

variable {d : ℕ}

/-! ## Small helpers -/

/-- `|log(b/a)| ≤ x` gives `b ≤ e^x a` and `a ≤ e^x b`. -/
theorem p7_ratio_of_abs_log_le {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (h : |Real.log (b / a)| ≤ x) :
    b ≤ Real.exp x * a ∧ a ≤ Real.exp x * b := by
  have h1 : Real.log (b / a) ≤ x := (le_abs_self _).trans h
  have h2 : -Real.log (b / a) ≤ x := (neg_le_abs _).trans h
  constructor
  · have : b / a ≤ Real.exp x := by
      calc b / a = Real.exp (Real.log (b / a)) := (Real.exp_log (div_pos hb ha)).symm
        _ ≤ Real.exp x := Real.exp_le_exp.mpr h1
    rwa [div_le_iff₀ ha] at this
  · have hlog : Real.log (a / b) = -Real.log (b / a) := by
      rw [← Real.log_inv, inv_div]
    have : a / b ≤ Real.exp x := by
      calc a / b = Real.exp (Real.log (a / b)) := (Real.exp_log (div_pos ha hb)).symm
        _ ≤ Real.exp x := Real.exp_le_exp.mpr (by rw [hlog]; exact h2)
    rwa [div_le_iff₀ hb] at this

/-- From the failure of the Markov event to a pointwise bound. -/
theorem p7_le_of_not_ofReal_rpow_le {H Hbar p : ℝ} (hH : 0 ≤ H) (hHbar : 0 < Hbar) (hp : 0 < p)
    (h : ¬ ENNReal.ofReal (Hbar ^ p) ≤ ENNReal.ofReal (H ^ p)) : H ≤ Hbar := by
  rw [not_le, ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hHbar p)] at h
  exact ((Real.rpow_lt_rpow_iff hH hHbar.le hp).mp h).le

/-! ## The deterministic step from band data -/

/-- **Deterministic step of Lemma 3.2 from band data**: on the escape event of the primary metric `Rm`, the envelope
of the secondary metric `Qm` on `B̄_{W+1}` (`W = S (R + 1)`), and the covering of `B̄_W` by good grid balls of the band
`V ≥ log 4` whose members satisfy the crossing/diameter bounds and `S_Q ≤ 2 S_R`, every `Rm`-geodesic pair
`x, y ∈ B̄_R` has `Qm(x, y) ≤ 4 (M/m) Rm(x, y) + 2 H̄ (4 e^{-V})^σ`. -/
theorem p7_rough_of_band (hd : 2 ≤ d) (Rm Qm : ContMetric d) (SR SQ : SewBall d → ℝ)
    {R S Hbar σ m M V : ℝ} (hR : 0 ≤ R) (hS : 4 ≤ S) (hHbar : 0 ≤ Hbar) (hm : 0 < m) (hM : 0 ≤ M)
    (hV : Real.log 4 ≤ V) (good : SewBall d → Prop)
    (hesc : diamIn Rm (ball (0 : Rd d) (2 * (R + 1))) (ball (0 : Rd d) (R + 1)) <
      setDistIn Rm univ (sphere (0 : Rd d) (2 * (R + 1))) (sphere (0 : Rd d) (S * (R + 1))))
    (henv : ∀ z ∈ closedBall (0 : Rd d) (S * (R + 1) + 1), ∀ s ∈ Ioc (0 : ℝ) 1,
      diamIn Qm (ball z (2 * s)) (ball z s) ≤ ENNReal.ofReal (Hbar * s ^ σ))
    (hgood : ∀ B ∈ p7BandSet d V (S * (R + 1)) good, 0 < SR B ∧ 0 < SQ B ∧ SQ B ≤ 2 * SR B ∧
      ENNReal.ofReal (m * SR B) ≤ setDistIn Rm univ (sphere B.1 (3 * B.2 / 4)) (sphere B.1 B.2) ∧
      diamIn Qm (ann B.1 (B.2 / 2) (7 * B.2 / 2)) (sphere B.1 B.2) ≤ ENNReal.ofReal (M * SQ B))
    (hcov : ∀ x ∈ closedBall (0 : Rd d) (S * (R + 1)), ∃ k ∈ p4_fullScales V, ∃ j : Fin d → ℤ,
      ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ < p4_radius k / 10 ∧
        good (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j, p4_radius k))
    {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) R) (hy : y ∈ closedBall (0 : Rd d) R)
    {γ : C(unitInterval, Rd d)} (hγ : IsConstSpeedGeod Rm x y γ) :
    Qm.1 (x, y) ≤ 4 * (M / m) * Rm.1 (x, y) + 2 * (Hbar * (4 * Real.exp (-V)) ^ σ) := by
  have hV0 : 0 ≤ V := le_trans (Real.log_nonneg (by norm_num)) hV
  have hW0 : 0 ≤ S * (R + 1) := by positivity
  have hd1 : 1 ≤ d := by omega
  have hrp : 4 * Real.exp (-V) ≤ 1 := by
    have h : Real.exp (-V) ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by linarith)
    have h4 : Real.exp (-Real.log 4) = 1 / 4 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    linarith
  have hRenv : R ≤ S * (R + 1) + 1 := by nlinarith
  refine p7_rough_det hd Rm Qm (rm := Real.exp (-2 * V)) hR hS hRenv hHbar hm hM (Real.exp_pos _) hrp
    hesc henv (p7BandFinset hd1 hV0 hW0 good) SR SQ ?_ ?_ ?_ ?_ hx hy hγ
  · intro B hB
    rw [p7_mem_bandFinset] at hB
    obtain ⟨h1, h2, h3, -, -⟩ := hgood B hB
    obtain ⟨hr1, hr2⟩ := p7BandSet_radius hV0 hB
    exact ⟨hr1, hr2, h1, h2, h3⟩
  · intro B hB
    rw [p7_mem_bandFinset] at hB
    exact (hgood B hB).2.2.2.1
  · intro B hB
    rw [p7_mem_bandFinset] at hB
    exact (hgood B hB).2.2.2.2
  · intro z hz
    obtain ⟨B, hB, hzB⟩ := p7_band_cover hV0 hcov z hz
    exact ⟨B, (p7_mem_bandFinset hd1 hV0 hW0).mpr hB, hzB⟩

/-! ## Lemma 3.2 -/

/-- **Lemma 3.2** (rough comparison; blueprint `a:lem32`). -/
theorem lemma32 (hd : 2 ≤ d) {ξbar : ℝ} (hU : ∀ s ∈ Icc (1 : ℝ) 10, UniformEstimates d ξbar s) :
    ∃ Cb : ℝ, 4 < Cb ∧ ∀ s₀ : ℝ, 1 ≤ s₀ → s₀ ≤ 10 → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ η ∈ Ioc (0 : ℝ) ξbar, ∀ D E : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
        ∀ R e q n : ℝ, 1 ≤ R → 0 < e → e < 1 / 8 → 0 < q → q < 1 / 8 →
          C * (1 + Real.log (1 + R) + Real.log e⁻¹ + Real.log q⁻¹) ≤ n → |η - ξ| * n ≤ c →
          pinLaw d s₀ {g | ¬ (CompOn (rho E g) (rho D g) Cb e R ∧ CompOn (rho D g) (rho E g) Cb e R)} ≤
            ENNReal.ofReal q := by
  classical
  -- the covering constants and the references at pin `1` with failure `p_cov`
  obtain ⟨Kc, Cc, -, hCc, hcover⟩ := cover210_full hd
  set pcov : ℝ := (2 : ℝ) ^ (-Kc * (2 * (d : ℝ) + 2)) with hpcov
  have hpcov0 : 0 < pcov := Real.rpow_pos_of_pos (by norm_num) _
  have hU1 := hU 1 ⟨le_rfl, by norm_num⟩
  obtain ⟨H₀, σ₀, β₀, m, M, -, -, -, hm, hmM, -, hrefs⟩ := refs_prob hd one_pos hU1 hpcov0
  have hMm : 1 < M / m := (one_lt_div hm).mpr hmM
  refine ⟨4 * (M / m), by linarith, ?_⟩
  intro s₀ hs₀ hs₀'
  have hs₀pos : 0 < s₀ := by linarith
  have hU₀ := hU s₀ ⟨hs₀, hs₀'⟩
  -- Lemma 2.1 at pin `s₀`
  obtain ⟨p, σ, β, C₁, A, hp, hσ, hσ1, -, hC₁, hA, henv⟩ := hU₀.envelope
  obtain ⟨pesc, hpesc, hescK⟩ := hU₀.escape
  obtain ⟨Cesc, hesc⟩ := hescK 1 le_rfl
  -- Lemma 2.2 with `λ = 2`, `κ₀ = 1/(20√d)`, `c₀ = 2`, local pin `1`, global pin `s₀`
  have hκ : 0 < 1 / (20 * Real.sqrt d) := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < d by omega))
    positivity
  obtain ⟨Ccap, Ccp, ccp, hCcap, hCcp, hccp, hcap⟩ :=
    lemma22 hd (lam := 2) (κ := 1 / (20 * Real.sqrt d)) (c₀ := 2) (s := 1) (s₀ := s₀) (by norm_num) hκ
      (by norm_num) le_rfl (by norm_num) hs₀ hs₀'
  -- constants
  set Cesc' : ℝ := max Cesc 1 with hCesc'
  have hCesc'0 : 0 < Cesc' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set κS : ℝ := p7κS pesc Cesc' with hκSdef
  set κH : ℝ := p7κH p C₁ A κS with hκHdef
  have hκS3 : 3 ≤ κS := p7κS_ge pesc Cesc' hpesc
  have hκH0 : 0 ≤ κH := p7κH_nonneg hp hA (by linarith)
  set C32 : ℝ := p7C32 d σ Cc Ccp ccp κS κH with hC32def
  have hC32 : 0 < C32 := p7C32_pos d hσ hccp (by linarith) hκH0
  have hcapc : 0 < Real.sqrt (2 * d) + Ccap := by positivity
  set c32 : ℝ := Real.log 2 / (2 * (Real.sqrt (2 * d) + Ccap)) with hc32def
  have hc32 : 0 < c32 := div_pos (Real.log_pos (by norm_num)) (by positivity)
  refine ⟨C32, c32, hC32, hc32, ?_⟩
  intro ξ hξ η hη D E hD hE R e q n hR he he8 hq hq8 hn hτ
  -- the parameters
  set Λ : ℝ := p7Lam R e q with hΛ
  set S : ℝ := Real.exp (κS * Λ) with hSdef
  set W : ℝ := S * (R + 1) with hWdef
  set Hbar : ℝ := Real.exp (κH * Λ) with hHdef
  have hn' : p7C32 d σ Cc Ccp ccp κS κH * Λ ≤ n := hn
  obtain ⟨hS4, hescq, henvq, hcovq, hcapq, hV4, hV1, hN1, hlogW, hNV, hatt, hHbar1, hn1⟩ :=
    p7_lemma32_numerics_abs d hpesc hCesc'0 hC₁ hA hσ hσ1.le hCc hCcp hccp hκS3
      (p7κS_mul pesc Cesc' hpesc) hκH0 (p7κH_mul p C₁ A κS hp) (by linarith) he (by linarith) hq
      (by linarith) hΛ hSdef hWdef hHdef hn'
  have hR0 : 0 ≤ R := by linarith
  have hW0 : 0 ≤ W := by positivity
  have hHbar0 : 0 < Hbar := Real.exp_pos _
  have hξ0 : 0 < ξ := hξ.1
  have hη0 : 0 < η := hη.1
  -- envelopes at radius `W + 1`
  obtain ⟨HD, hHDm, hHD1, hHDint, hHDae⟩ := henv ξ hξ D hD (W + 1) (by linarith)
  obtain ⟨HE, hHEm, hHE1, hHEint, hHEae⟩ := henv η hη E hE (W + 1) (by linarith)
  -- the drift condition gives the cap `log 2`
  have hcapτ : (Real.sqrt (2 * d) + Ccap) * |η - ξ| * (⌈n⌉₊ : ℝ) ≤ Real.log 2 := by
    have hNle : (⌈n⌉₊ : ℝ) ≤ 2 * n := by
      have := Nat.ceil_lt_add_one (show 0 ≤ n by linarith)
      linarith
    have hτ0 : 0 ≤ |η - ξ| := abs_nonneg _
    calc (Real.sqrt (2 * d) + Ccap) * |η - ξ| * (⌈n⌉₊ : ℝ) ≤
          (Real.sqrt (2 * d) + Ccap) * |η - ξ| * (2 * n) := by gcongr
      _ = 2 * (Real.sqrt (2 * d) + Ccap) * (|η - ξ| * n) := by ring
      _ ≤ 2 * (Real.sqrt (2 * d) + Ccap) * c32 := by gcongr
      _ = Real.log 2 := by rw [hc32def]; field_simp
  -- the six failure events
  set escD : Set (DistRd d) := {g | ¬ (ENNReal.ofReal 1 *
      diamIn (rho D g) (ball (0 : Rd d) (2 * (R + 1))) (ball (0 : Rd d) (R + 1)) <
      setDistIn (rho D g) univ (sphere (0 : Rd d) (2 * (R + 1))) (sphere (0 : Rd d) (S * (R + 1))))}
    with hescDdef
  set escE : Set (DistRd d) := {g | ¬ (ENNReal.ofReal 1 *
      diamIn (rho E g) (ball (0 : Rd d) (2 * (R + 1))) (ball (0 : Rd d) (R + 1)) <
      setDistIn (rho E g) univ (sphere (0 : Rd d) (2 * (R + 1))) (sphere (0 : Rd d) (S * (R + 1))))}
    with hescEdef
  set envD : Set (DistRd d) := {g | ENNReal.ofReal (Hbar ^ p) ≤ ENNReal.ofReal (HD g ^ p)} with henvDdef
  set envE : Set (DistRd d) := {g | ENNReal.ofReal (Hbar ^ p) ≤ ENNReal.ofReal (HE g ^ p)} with henvEdef
  set cov : Set (DistRd d) := {g : DistRd d | ∃ x ∈ closedBall (0 : Rd d) W,
      ∀ k ∈ p4_fullScales (n / 4), ∀ j : Fin d → ℤ,
        ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ < p4_radius k / 10 →
          recentre 1 (p4_radius k) (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) g ∉
            PairRefs D E H₀ σ₀ β₀ m M} with hcovdef
  set cap : Set (DistRd d) := {g | ∃ pr ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) ⌈n⌉₊ (W + 1),
      Ccap * (⌈n⌉₊ : ℝ) < |sphereAvg g (1 * pr.1) pr.2|} with hcapdef
  -- their probabilities
  have hPescD : pinLaw d s₀ escD ≤ ENNReal.ofReal (q / 8) := by
    refine (hesc ξ hξ D hD (R + 1) S (by linarith) hS4).trans (ENNReal.ofReal_le_ofReal ?_)
    have hSp : 0 ≤ S ^ (-pesc) := Real.rpow_nonneg (by linarith) _
    have : Cesc * S ^ (-pesc) ≤ Cesc' * S ^ (-pesc) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hSp
    linarith
  have hPescE : pinLaw d s₀ escE ≤ ENNReal.ofReal (q / 8) := by
    refine (hesc η hη E hE (R + 1) S (by linarith) hS4).trans (ENNReal.ofReal_le_ofReal ?_)
    have hSp : 0 ≤ S ^ (-pesc) := Real.rpow_nonneg (by linarith) _
    have : Cesc * S ^ (-pesc) ≤ Cesc' * S ^ (-pesc) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hSp
    linarith
  have hPenvD : pinLaw d s₀ envD ≤ ENNReal.ofReal (q / 8) := by
    have hf : AEMeasurable (fun g => ENNReal.ofReal (HD g ^ p)) (pinLaw d s₀) :=
      ((hHDm.pow_const p).ennreal_ofReal).aemeasurable
    refine (p5b_markov hf (Real.rpow_pos_of_pos hHbar0 p) hHDint).trans (ENNReal.ofReal_le_ofReal ?_)
    exact henvq
  have hPenvE : pinLaw d s₀ envE ≤ ENNReal.ofReal (q / 8) := by
    have hf : AEMeasurable (fun g => ENNReal.ofReal (HE g ^ p)) (pinLaw d s₀) :=
      ((hHEm.pow_const p).ennreal_ofReal).aemeasurable
    refine (p5b_markov hf (Real.rpow_pos_of_pos hHbar0 p) hHEint).trans (ENNReal.ofReal_le_ofReal ?_)
    exact henvq
  have hEloc := (local_events_aeEventIn hd hξ0 hη0 hD hE (s := 1) (by norm_num) 0 H₀ σ₀ β₀ m M).2.2
  have hPcov : pinLaw d s₀ cov ≤ ENNReal.ofReal (q / 8) :=
    (hcover le_rfl (by norm_num) hs₀ hs₀' hEloc hpcov0.le le_rfl (hrefs ξ hξ η hη D E hD hE) hW0
      hV1).trans (ENNReal.ofReal_le_ofReal hcovq)
  have hcapN := hcap (n := ⌈n⌉₊) (W := W + 1) hN1 (by linarith) hlogW
  have hPcap : pinLaw d s₀ cap ≤ ENNReal.ofReal (q / 8) :=
    hcapN.1.trans (ENNReal.ofReal_le_ofReal hcapq)
  -- almost surely, the bad event lies in the union of the failure events
  have hae : ∀ᵐ g ∂(pinLaw d s₀),
      g ∈ {g | ¬ (CompOn (rho E g) (rho D g) (4 * (M / m)) e R ∧
        CompOn (rho D g) (rho E g) (4 * (M / m)) e R)} →
      g ∈ escD ∪ escE ∪ envD ∪ envE ∪ cov ∪ cap := by
    filter_upwards [hU₀.proper ξ hξ D hD, hU₀.proper η hη E hE, hHDae, hHEae,
      p7_ae_connector_grid hd hξ0 hη0 hD hE (s := 1) hs₀pos (b := 0) le_rfl H₀ σ₀ β₀ m M]
      with g hpD hpE hbD hbE hconn
    intro hbad
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨⟨⟨⟨hnescD, hnescE⟩, hnenvD⟩, hnenvE⟩, hncov⟩, hncap⟩ := hnot
    apply hbad
    -- the good events, unfolded
    have hescD' : diamIn (rho D g) (ball (0 : Rd d) (2 * (R + 1))) (ball (0 : Rd d) (R + 1)) <
        setDistIn (rho D g) univ (sphere (0 : Rd d) (2 * (R + 1))) (sphere (0 : Rd d) (S * (R + 1))) := by
      have h := not_not.mp hnescD
      rwa [ENNReal.ofReal_one, one_mul] at h
    have hescE' : diamIn (rho E g) (ball (0 : Rd d) (2 * (R + 1))) (ball (0 : Rd d) (R + 1)) <
        setDistIn (rho E g) univ (sphere (0 : Rd d) (2 * (R + 1))) (sphere (0 : Rd d) (S * (R + 1))) := by
      have h := not_not.mp hnescE
      rwa [ENNReal.ofReal_one, one_mul] at h
    have hHDle : HD g ≤ Hbar :=
      p7_le_of_not_ofReal_rpow_le (by linarith [hHD1 g]) hHbar0 hp hnenvD
    have hHEle : HE g ≤ Hbar :=
      p7_le_of_not_ofReal_rpow_le (by linarith [hHE1 g]) hHbar0 hp hnenvE
    have henvD' : ∀ z ∈ closedBall (0 : Rd d) (S * (R + 1) + 1), ∀ s ∈ Ioc (0 : ℝ) 1,
        diamIn (rho D g) (ball z (2 * s)) (ball z s) ≤ ENNReal.ofReal (Hbar * s ^ σ) := by
      intro z hz s hs
      refine (hbD.1 z hz s hs).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right hHDle (Real.rpow_nonneg hs.1.le _)
    have henvE' : ∀ z ∈ closedBall (0 : Rd d) (S * (R + 1) + 1), ∀ s ∈ Ioc (0 : ℝ) 1,
        diamIn (rho E g) (ball z (2 * s)) (ball z s) ≤ ENNReal.ofReal (Hbar * s ^ σ) := by
      intro z hz s hs
      refine (hbE.1 z hz s hs).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right hHEle (Real.rpow_nonneg hs.1.le _)
    have hcov' := p7_not_cover_event hncov
    have hcapg : ∀ pr ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) ⌈n⌉₊ (W + 1),
        |sphereAvg g (1 * pr.1) pr.2| ≤ Ccap * (⌈n⌉₊ : ℝ) := by
      intro pr hpr
      by_contra hlt
      exact hncap ⟨pr, hpr, lt_of_not_ge hlt⟩
    have hratio : ∀ B ∈ p7BandSet d (n / 4) W
        (fun B : SewBall d => recentre 1 B.2 B.1 g ∈ PairRefs D E H₀ σ₀ β₀ m M),
        scaleS d η 1 B.2 B.1 g ≤ 2 * scaleS d ξ 1 B.2 B.1 g ∧
          scaleS d ξ 1 B.2 B.1 g ≤ 2 * scaleS d η 1 B.2 B.1 g := by
      intro B hB
      have hgrid := p7BandSet_swap_mem_gridPairs (by linarith) hNV hB
      have hr := p7GridBall_radius_pos (p7BandSet_subset_gridBall hB)
      have hlog := (hcapN.2 g hcapg ξ η hξ0.le hη0.le (B.2, B.1) hgrid).trans hcapτ
      have h2 := p7_ratio_of_abs_log_le (scaleS_pos d ξ 1 hr B.1 g) (scaleS_pos d η 1 hr B.1 g) hlog
      rwa [Real.exp_log (by norm_num)] at h2
    have hgoodA : ∀ B ∈ p7BandSet d (n / 4) W
        (fun B : SewBall d => recentre 1 B.2 B.1 g ∈ PairRefs D E H₀ σ₀ β₀ m M),
        p7ConnA D E ξ η 1 m M g B := fun B hB =>
      (hconn B (p7BandSet_subset_gridBall hB) hB.2.2).1
    constructor
    · intro x hx y hy
      obtain ⟨γ, hγ⟩ := hpD.2 x y
      have h := p7_rough_of_band hd (rho D g) (rho E g) (fun B => scaleS d ξ 1 B.2 B.1 g)
        (fun B => scaleS d η 1 B.2 B.1 g) hR0 hS4 hHbar0.le hm (by linarith) hV4
        (fun B : SewBall d => recentre 1 B.2 B.1 g ∈ PairRefs D E H₀ σ₀ β₀ m M) hescD' henvE'
        (fun B hB => ⟨scaleS_pos d ξ 1 (p7GridBall_radius_pos (p7BandSet_subset_gridBall hB)) B.1 g,
          scaleS_pos d η 1 (p7GridBall_radius_pos (p7BandSet_subset_gridBall hB)) B.1 g,
          (hratio B hB).1, (hgoodA B hB).1.1, (hgoodA B hB).2.2⟩) hcov' hx hy hγ
      linarith
    · intro x hx y hy
      obtain ⟨γ, hγ⟩ := hpE.2 x y
      have h := p7_rough_of_band hd (rho E g) (rho D g) (fun B => scaleS d η 1 B.2 B.1 g)
        (fun B => scaleS d ξ 1 B.2 B.1 g) hR0 hS4 hHbar0.le hm (by linarith) hV4
        (fun B : SewBall d => recentre 1 B.2 B.1 g ∈ PairRefs D E H₀ σ₀ β₀ m M) hescE' henvD'
        (fun B hB => ⟨scaleS_pos d η 1 (p7GridBall_radius_pos (p7BandSet_subset_gridBall hB)) B.1 g,
          scaleS_pos d ξ 1 (p7GridBall_radius_pos (p7BandSet_subset_gridBall hB)) B.1 g,
          (hratio B hB).2, (hgoodA B hB).2.1, (hgoodA B hB).1.2⟩) hcov' hx hy hγ
      linarith
  -- sum up
  calc pinLaw d s₀ {g | ¬ (CompOn (rho E g) (rho D g) (4 * (M / m)) e R ∧
        CompOn (rho D g) (rho E g) (4 * (M / m)) e R)}
      ≤ pinLaw d s₀ (escD ∪ escE ∪ envD ∪ envE ∪ cov ∪ cap) := measure_mono_ae hae
    _ ≤ pinLaw d s₀ escD + pinLaw d s₀ escE + pinLaw d s₀ envD + pinLaw d s₀ envE +
          pinLaw d s₀ cov + pinLaw d s₀ cap := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (q / 8) + ENNReal.ofReal (q / 8) + ENNReal.ofReal (q / 8) +
          ENNReal.ofReal (q / 8) + ENNReal.ofReal (q / 8) + ENNReal.ofReal (q / 8) := by
        gcongr
    _ = ENNReal.ofReal (q / 8 + q / 8 + q / 8 + q / 8 + q / 8 + q / 8) := by
        have hq8 : 0 ≤ q / 8 := by linarith
        rw [ENNReal.ofReal_add (by linarith) hq8, ENNReal.ofReal_add (by linarith) hq8,
          ENNReal.ofReal_add (by linarith) hq8, ENNReal.ofReal_add (by linarith) hq8,
          ENNReal.ofReal_add hq8 hq8]
    _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal (by linarith)

end HigherDimLQGContinuity
