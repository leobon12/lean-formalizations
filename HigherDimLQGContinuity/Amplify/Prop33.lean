import HigherDimLQGContinuity.Amplify.Lemma32
import HigherDimLQGContinuity.Amplify.Prop33Good
import HigherDimLQGContinuity.Amplify.Prop33Params

/-!
# Proposition 3.3: annular amplification (packet P7)

Blueprint Part A, Proposition `a:prop33` ([C] Prop. 3.3, p. 7–8, l. 361–403; NA1 items 24–25, R9, Q6; NA0 §2.3;
erratum EA `a:err-33`).

**Statement** (`prop33`). Let `d ≥ 2` and assume Lemma 2.1 (`UniformEstimates d ξ̄ s`, interface I1) for all pins
`s ∈ [1, 10]`. There is `p₀ > 0` (`p₀ = p_cov = 2^{-K(2d+2)}` of `cover210_full`, depending only on `d`) such that for
every bound `C_b > 0`, all reference constants `(H₀, σ₀, β₀, m, M)` with `0 < m ≤ M` and all pins `s₁, s₂ ∈ [1, 10]`
(local and global) there are `M₃, C₃, c₃ > 0` with: for `ξ, η ∈ (0, ξ̄]`, `D, E` strong, `b ∈ (0, C_b]` with
`𝐏_{s₁}(H↑(D, E; b) ∪ PairRefs(D, E)ᶜ) ≤ p₀`, and `R ≥ 1`, `δ, e ∈ (0, 1/8)`,
`n ≥ C₃ δ^{-M₃} (1 + log(1 + R) + log e⁻¹ + log δ⁻¹)`, `|η - ξ| n ≤ c₃ δ`:
`𝐏_{s₂}{g : ¬ Comp(ρ^E_g, ρ^D_g; b + δ, e, R)} ≤ C₃ R^{M₃} δ^{-M₃} e^{-c₃ δ^{M₃} n}`.

The blueprint states it with `C_b` the constant of Lemma 3.2; the statement here holds for every bound `C_b` on `b`
(the constants depend on `C_b`), which contains the blueprint's form. Only `0 < m ≤ M` of the reference ranges is
used.

**Proof** (blueprint, with the explicit constants of `P7Consts33`): events under `𝐏_{s₂}` (G1) escape of `ρ^D` at radius
`R + 1` with factor `S = e^{w a_N n}`; (G2) envelope of `ρ^D` at radius `W + 1` (`W = S(R + 1)`) below
`H̄ = e^{κ_H Λ + h' a_N n}`; (G3) Lemma 3.2 at radius `W + 2` with `e = q = e^{-c₀ n}`; (G4) the coverings (2.10) of
the `N` bands `V_j = a_{j+1} n`, `a_j = L^{-j}/4`, at the local pin `s₁` with the local event `(H↑ ∪ PairRefsᶜ)ᶜ`;
(G5) the scale cap of Lemma 2.2. Off a null set and on the intersection, `p7_prop33_good` (band recursion through
Lemma 3.1(b) with the closed-form upper solutions `p7X`, `p7E`) gives the comparison; the numerics are
`p7_prop33_num_det` and `p7_prop33_num_fail`.
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

/-- **Proposition 3.3** (annular amplification; blueprint `a:prop33`). -/
theorem prop33 (hd : 2 ≤ d) {ξbar : ℝ} (hU : ∀ s ∈ Icc (1 : ℝ) 10, UniformEstimates d ξbar s) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ Cb H₀ σ₀ β₀ m M : ℝ, 0 < Cb → 0 < m → m ≤ M →
    ∀ s₁ s₂ : ℝ, 1 ≤ s₁ → s₁ ≤ 10 → 1 ≤ s₂ → s₂ ≤ 10 →
    ∃ M₃ C₃ c₃ : ℝ, 0 < M₃ ∧ 0 < C₃ ∧ 0 < c₃ ∧
    ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ η ∈ Ioc (0 : ℝ) ξbar, ∀ D E : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
      ∀ b : ℝ, 0 < b → b ≤ Cb →
      pinLaw d s₁ (Hup D E b ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ) ≤ ENNReal.ofReal p₀ →
      ∀ R δ e n : ℝ, 1 ≤ R → 0 < δ → δ < 1 / 8 → 0 < e → e < 1 / 8 →
        C₃ * δ ^ (-M₃) * (1 + Real.log (1 + R) + Real.log e⁻¹ + Real.log δ⁻¹) ≤ n →
        |η - ξ| * n ≤ c₃ * δ →
        pinLaw d s₂ {g | ¬ CompOn (rho E g) (rho D g) (b + δ) e R} ≤
          ENNReal.ofReal (C₃ * R ^ M₃ * δ ^ (-M₃) * Real.exp (-c₃ * δ ^ M₃ * n)) := by
  classical
  obtain ⟨Kc, Cc, -, hCc, hcover⟩ := cover210_full hd
  set p₀ : ℝ := (2 : ℝ) ^ (-Kc * (2 * (d : ℝ) + 2)) with hp₀def
  have hp₀ : 0 < p₀ := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨C0, hC0, hl32⟩ := lemma32 hd hU
  refine ⟨p₀, hp₀, ?_⟩
  intro Cb H₀ σ₀ β₀ m M hCb hm hmM s₁ s₂ hs₁ hs₁' hs₂ hs₂'
  have hs₂pos : 0 < s₂ := by linarith
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hU₂ := hU s₂ ⟨hs₂, hs₂'⟩
  -- Lemma 2.1 at the global pin `s₂`
  obtain ⟨p, σ, β, C₁, A, hp, hσ, hσ1, hβ, hC₁, hA, henv⟩ := hU₂.envelope
  obtain ⟨pesc, hpesc, hescK⟩ := hU₂.escape
  obtain ⟨Cesc, hesc⟩ := hescK 1 le_rfl
  -- Lemma 3.2 at the global pin `s₂`
  obtain ⟨C32, c32, hC32, hc32, hl32'⟩ := hl32 s₂ hs₂ hs₂'
  -- Lemma 2.2 with local pin `s₁`, global pin `s₂`
  have hκ : 0 < 1 / (20 * Real.sqrt d) := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < d by omega))
    positivity
  obtain ⟨Ccap, Ccp, ccp, hCcap, hCcp, hccp, hcap⟩ :=
    lemma22 hd (lam := 2) (κ := 1 / (20 * Real.sqrt d)) (c₀ := 2) (s := s₁) (s₀ := s₂) (by norm_num) hκ
      (by norm_num) hs₁ hs₁' hs₂ hs₂'
  -- the constants
  obtain ⟨K⟩ := p7_consts33_nonempty d hd (β := β) (C₁ := C₁) (Cesc := Cesc) hp hσ hA hpesc
    (by linarith : (1 : ℝ) ≤ C0) hC32 hc32 hCcap hCcp hccp hCc hCb hm hmM
  refine ⟨K.M₃, K.C₃, K.c₃, by linarith [K.hM₃1], K.hC₃0, K.hc₃0, ?_⟩
  intro ξ hξ η hη D E hD hE b hb hbCb hloc R δ e n hR hδ hδ8 he he8 hn hτ
  have hδ1 : δ ≤ 1 := by linarith only [hδ8]
  have he1 : e ≤ 1 := by linarith only [he8]
  have hξ0 : 0 < ξ := hξ.1
  have hη0 : 0 < η := hη.1
  -- the bracket, the bands and the depth consequences
  obtain ⟨hΛ1, hΛR, hΛe, hΛδ, hqsN, hNΛ, hNδ, haN, hnC, hAC, hn0⟩ :=
    p7_prop33_base (by linarith : (1 : ℝ) ≤ C0) K hR hδ hδ1 he he1 hn
  set Λ : ℝ := p7Lam R e δ with hΛdef
  set N : ℕ := p7Nb C0 K.qs δ with hNdef
  set τ : ℝ := |η - ξ| with hτdef
  have hτ0 : 0 ≤ τ := abs_nonneg _
  -- the parameters
  set As : ℝ := p7a K.L N * n with hAsdef
  set S : ℝ := Real.exp (K.w * As) with hSdef
  set W : ℝ := S * (R + 1) with hWdef
  set Hbar : ℝ := Real.exp (K.κH * Λ + K.h' * As) with hHbardef
  set H : ℝ := 2 * Hbar with hHdef
  set e0 : ℝ := Real.exp (-(K.c₀ * n)) with he0def
  set b' : ℝ := b * Real.exp (2 * K.Ccap' * τ * n) with hb'def
  set Γ : ℝ := b' + C0 + 1 with hΓdef
  set εbar : ℝ := e0 * H * 4 ^ β * Real.exp (2 * β * (p7a K.L 1 * n)) +
    N * (Γ * (4 * H) * H * 4 ^ β) * Real.exp (-(3 / 4 * σ * (p7a K.L N * n))) with hεbardef
  obtain ⟨hS4, hHbar1, hbands, he00, he08, hdepth32, hτ32, hN1, hlogW1, hcapτ, hb'0, hb'le, hεbar0,
      hXN, hΓε, hEN⟩ :=
    p7_prop33_num_det hd hσ (by linarith : (1 : ℝ) ≤ C0) hCb K hR hδ hδ8 he hΛ1 hΛR hΛe hΛδ hqsN hNΛ
      hnC hAC hn0 hτ0 hτ hb hbCb hAsdef hSdef hWdef hHbardef hHdef he0def hb'def hΓdef hεbardef
  obtain ⟨hescF, henvF, hcovF, hcapF, hsumF⟩ :=
    p7_prop33_num_fail hC₁ hA hCc hCcp hccp K hR hδ hδ1 hΛ1 hΛR hNδ haN hn0 hAsdef hSdef hWdef hHbardef
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hW0 : 0 ≤ W := by positivity
  have hHbar0 : 0 < Hbar := Real.exp_pos _
  -- the envelope of `ρ^D` at radius `W + 1`
  obtain ⟨HD, hHDm, hHD1, hHDint, hHDae⟩ := henv ξ hξ D hD (W + 1) (by linarith only [hW0])
  -- the local event
  set Eloc : Set (DistRd d) := (Hup D E b ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ)ᶜ with hElocdef
  have hEloc := (local_good_aeEventIn hd hξ0 hη0 hD hE (s := s₁) (by linarith) b H₀ σ₀ β₀ m M).1
  have hElocc : pinLaw d s₁ Elocᶜ ≤ ENNReal.ofReal p₀ := by rw [hElocdef, compl_compl]; exact hloc
  -- the failure events
  set escD : Set (DistRd d) := {g | ¬ (ENNReal.ofReal 1 *
      diamIn (rho D g) (ball (0 : Rd d) (2 * (R + 1))) (ball (0 : Rd d) (R + 1)) <
      setDistIn (rho D g) univ (sphere (0 : Rd d) (2 * (R + 1))) (sphere (0 : Rd d) (S * (R + 1))))}
    with hescDdef
  set envD : Set (DistRd d) := {g | ENNReal.ofReal (Hbar ^ p) ≤ ENNReal.ofReal (HD g ^ p)} with henvDdef
  set rough : Set (DistRd d) := {g | ¬ (CompOn (rho E g) (rho D g) C0 e0 (W + 2) ∧
      CompOn (rho D g) (rho E g) C0 e0 (W + 2))} with hroughdef
  set cov : ℕ → Set (DistRd d) := fun j => {g : DistRd d | ∃ x ∈ closedBall (0 : Rd d) W,
      ∀ k ∈ p4_fullScales (p7a K.L (j + 1) * n), ∀ i : Fin d → ℤ,
        ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) i‖ < p4_radius k / 10 →
          recentre s₁ (p4_radius k) (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) i) g ∉ Eloc}
    with hcovdef
  set cap : Set (DistRd d) := {g | ∃ pr ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) ⌈n⌉₊ (W + 1),
      Ccap * (⌈n⌉₊ : ℝ) < |sphereAvg g (s₁ * pr.1) pr.2|} with hcapdef
  -- their probabilities
  have hPesc : pinLaw d s₂ escD ≤ ENNReal.ofReal (K.Cesc' * Real.exp (-(pesc * K.w * As))) :=
    (hesc ξ hξ D hD (R + 1) S (by linarith only [hR]) hS4).trans (ENNReal.ofReal_le_ofReal hescF)
  have hPenv : pinLaw d s₂ envD ≤ ENNReal.ofReal (1 * Real.exp (-(p * K.h * As))) := by
    have hf : AEMeasurable (fun g => ENNReal.ofReal (HD g ^ p)) (pinLaw d s₂) :=
      ((hHDm.pow_const p).ennreal_ofReal).aemeasurable
    exact (p5b_markov hf (Real.rpow_pos_of_pos hHbar0 p) hHDint).trans (ENNReal.ofReal_le_ofReal henvF)
  have hPrough : pinLaw d s₂ rough ≤ ENNReal.ofReal (1 * Real.exp (-(K.c₀ * n))) := by
    rw [one_mul]
    exact hl32' ξ hξ η hη D E hD hE (W + 2) e0 e0 n (by linarith only [hW0]) he00 he08 he00 he08
      hdepth32 hτ32
  have hPcov : ∀ j < N, pinLaw d s₂ (cov j) ≤
      ENNReal.ofReal (Cc * 4 ^ d * R ^ d * Real.exp (-(1 * As))) := by
    intro j hj
    obtain ⟨-, hV1, -⟩ := hbands j hj
    exact (hcover hs₁ hs₁' hs₂ hs₂' hEloc hp₀.le le_rfl hElocc hW0 hV1).trans
      (ENNReal.ofReal_le_ofReal (hcovF j hj))
  have hcapN := hcap (n := ⌈n⌉₊) (W := W + 1) hN1 (by linarith only [hW0]) hlogW1
  have hPcap : pinLaw d s₂ cap ≤ ENNReal.ofReal (Ccp * Real.exp (-(ccp * n))) :=
    hcapN.1.trans (ENNReal.ofReal_le_ofReal hcapF)
  -- almost surely, the bad event lies in the union of the failure events
  have hae : ∀ᵐ g ∂(pinLaw d s₂),
      g ∈ {g | ¬ CompOn (rho E g) (rho D g) (b + δ) e R} →
      g ∈ escD ∪ envD ∪ rough ∪ (⋃ j ∈ Finset.range N, cov j) ∪ cap := by
    filter_upwards [hU₂.proper ξ hξ D hD, hHDae, p5b_ae_isLength_rho hd hD hs₂pos,
      p7_ae_connector_grid hd hξ0 hη0 hD hE (s := s₁) hs₂pos (b := b) hb.le H₀ σ₀ β₀ m M]
      with g hpD hbD hlenD hconn
    intro hbad
    by_contra hnot
    simp only [mem_union, mem_iUnion, Finset.mem_range, not_or, not_exists] at hnot
    obtain ⟨⟨⟨⟨hnesc, hnenv⟩, hnrough⟩, hncov⟩, hncap⟩ := hnot
    apply hbad
    have hesc' : diamIn (rho D g) (ball (0 : Rd d) (2 * (R + 1))) (ball (0 : Rd d) (R + 1)) <
        setDistIn (rho D g) univ (sphere (0 : Rd d) (2 * (R + 1))) (sphere (0 : Rd d) (S * (R + 1))) := by
      have h := not_not.mp hnesc
      rwa [ENNReal.ofReal_one, one_mul] at h
    have hHDle : HD g ≤ Hbar :=
      p7_le_of_not_ofReal_rpow_le (by linarith [hHD1 g]) hHbar0 hp hnenv
    have henvU : ∀ z ∈ closedBall (0 : Rd d) (S * (R + 1) + 1), ∀ s ∈ Ioc (0 : ℝ) 1,
        diamIn (rho D g) (ball z (2 * s)) (ball z s) ≤ ENNReal.ofReal (Hbar * s ^ σ) := by
      intro z hz s hs
      refine (hbD.1 z hz s hs).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right hHDle (Real.rpow_nonneg hs.1.le _)
    have henvL : ∀ x ∈ closedBall (0 : Rd d) (S * (R + 1) + 1),
        ∀ y ∈ closedBall (0 : Rd d) (S * (R + 1) + 1), Hbar⁻¹ * ‖x - y‖ ^ β ≤ (rho D g).1 (x, y) := by
      intro x hx y hy
      have h := hbD.2 x hx y hy
      have hinv : Hbar⁻¹ ≤ (HD g)⁻¹ := inv_anti₀ (by linarith [hHD1 g]) hHDle
      have hnn : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
      exact (mul_le_mul_of_nonneg_right hinv hnn).trans h
    have hrough' : CompOn (rho E g) (rho D g) C0 e0 (S * (R + 1) + 2) := (not_not.mp hnrough).1
    have hcov' : ∀ j < N, ∀ x ∈ closedBall (0 : Rd d) (S * (R + 1)),
        ∃ k ∈ p4_fullScales (p7a K.L (j + 1) * n), ∃ i : Fin d → ℤ,
          ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) i‖ < p4_radius k / 10 ∧
          recentre s₁ (p4_radius k) (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) i) g ∈ Eloc :=
      fun j hj => p7_not_cover_event (hncov j hj)
    have hcapg : ∀ pr ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) ⌈n⌉₊ (W + 1),
        |sphereAvg g (s₁ * pr.1) pr.2| ≤ Ccap * (⌈n⌉₊ : ℝ) := by
      intro pr hpr
      by_contra hlt
      exact hncap ⟨pr, hpr, lt_of_not_ge hlt⟩
    have hcoef : ∀ j < N, ∀ B ∈ p7BandSet d (p7a K.L (j + 1) * n) (S * (R + 1))
        (fun B : SewBall d => recentre s₁ B.2 B.1 g ∈ (Hup D E b ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ)ᶜ),
        b * (scaleS d η s₁ B.2 B.1 g / scaleS d ξ s₁ B.2 B.1 g) ≤ b' := by
      intro j hj B hB
      obtain ⟨-, -, hNV⟩ := hbands j hj
      have hV0 : 0 ≤ p7a K.L (j + 1) * n := le_trans (by norm_num) (hbands j hj).2.1
      have hgrid := p7BandSet_swap_mem_gridPairs hV0 hNV hB
      have hr := p7GridBall_radius_pos (p7BandSet_subset_gridBall hB)
      have hlog := (hcapN.2 g hcapg ξ η hξ0.le hη0.le (B.2, B.1) hgrid).trans hcapτ
      have hSD := scaleS_pos d ξ s₁ hr B.1 g
      have hSE := scaleS_pos d η s₁ hr B.1 g
      have hrat := (p7_ratio_of_abs_log_le hSD hSE hlog).1
      have hdiv : scaleS d η s₁ B.2 B.1 g / scaleS d ξ s₁ B.2 B.1 g ≤ Real.exp (2 * K.Ccap' * τ * n) := by
        rw [div_le_iff₀ hSD]; exact hrat
      rw [hb'def]
      exact mul_le_mul_of_nonneg_left hdiv hb.le
    have hL1 : 1 ≤ K.L := le_trans (by norm_num) K.hL5
    have hL0 : 0 < K.L := by linarith only [hL1]
    have hqs0 := K.hqs0
    have hqs1 := K.hqs1
    have hX : ∀ j ≤ N, 0 ≤ p7X K.qs C0 εbar j := fun j _ =>
      p7X_nonneg hqs0.le (by linarith) hεbar0 j
    have hΓ0 : 0 ≤ Γ := by rw [hΓdef]; linarith only [hb'0, hC0]
    have hH0 : 0 < H := by rw [hHdef]; positivity
    have hΕ : ∀ j ≤ N, 0 ≤ p7E e0 Γ H σ n (p7a K.L) j := fun j _ =>
      p7E_nonneg he00.le hΓ0 hH0.le j
    have hstepC := p7_stepC (qs := K.qs) (C0 := C0) (N := N) hqs1.le hεbar0 hH0
      (p7_eps_bound (N := N) he00.le hΓ0 hH0.le (by linarith only [hβ]) hσ.le hn0 hL0
        (fun j => (p7a_pos hL0 j).le) (p7a_succ K.L) (p7a_anti hL1)
        (by have := K.hLσ; linarith only [this]))
    have hstepE := p7_stepE (qs := K.qs) (C0 := C0) (εbar := εbar) (e0 := e0) (N := N) (a := p7a K.L)
      hqs0.le hqs1.le (by linarith) hεbar0 hH0.le hσ.le hσ1.le hn0 hb'0
      (fun j => p7a_anti hL1 (Nat.le_succ j)) hΓε
    have hqsdef : K.qs = 1 - m / (2 * M) := K.hqs
    refine p7_prop33_good hd (ξ := ξ) (η := η) (s₁ := s₁) hlenD hpD.2 hR0 hS4 hHbar1 hσ hσ1.le
      (by linarith only [hβ]) hm hM hmM hb'0 hesc' henvU henvL hrough' (fun j hj => (hbands j hj).1)
      hcov' hconn hcoef hX hΕ (by rw [p7X_zero]) (by rw [p7E_zero]) ?_ ?_ hXN hEN
    · intro j hj
      have h := hstepC j hj
      rw [← hqsdef]
      rw [hHdef] at h
      exact h
    · intro j hj
      have h := hstepE j hj
      rw [hHdef] at h
      exact h
  -- sum up
  calc pinLaw d s₂ {g | ¬ CompOn (rho E g) (rho D g) (b + δ) e R}
      ≤ pinLaw d s₂ (escD ∪ envD ∪ rough ∪ (⋃ j ∈ Finset.range N, cov j) ∪ cap) := measure_mono_ae hae
    _ ≤ pinLaw d s₂ escD + pinLaw d s₂ envD + pinLaw d s₂ rough +
          pinLaw d s₂ (⋃ j ∈ Finset.range N, cov j) + pinLaw d s₂ cap := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (K.Cesc' * Real.exp (-(pesc * K.w * As))) +
          ENNReal.ofReal (1 * Real.exp (-(p * K.h * As))) +
          ENNReal.ofReal (1 * Real.exp (-(K.c₀ * n))) +
          ENNReal.ofReal (N * (Cc * 4 ^ d * R ^ d * Real.exp (-(1 * As)))) +
          ENNReal.ofReal (Ccp * Real.exp (-(ccp * n))) := by
        gcongr
        calc pinLaw d s₂ (⋃ j ∈ Finset.range N, cov j)
            ≤ ∑ j ∈ Finset.range N, pinLaw d s₂ (cov j) := measure_biUnion_finset_le _ _
          _ ≤ ∑ _j ∈ Finset.range N, ENNReal.ofReal (Cc * 4 ^ d * R ^ d * Real.exp (-(1 * As))) :=
              Finset.sum_le_sum fun j hj => hPcov j (Finset.mem_range.mp hj)
          _ = ENNReal.ofReal (N * (Cc * 4 ^ d * R ^ d * Real.exp (-(1 * As)))) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (K.Cesc' * Real.exp (-(pesc * K.w * As)) + 1 * Real.exp (-(p * K.h * As)) +
          1 * Real.exp (-(K.c₀ * n)) + N * (Cc * 4 ^ d * R ^ d * Real.exp (-(1 * As))) +
          Ccp * Real.exp (-(ccp * n))) := by
        have h1 : 0 ≤ K.Cesc' * Real.exp (-(pesc * K.w * As)) := by
          have := K.hCesc'0; positivity
        have h2 : 0 ≤ 1 * Real.exp (-(p * K.h * As)) := by positivity
        have h3 : 0 ≤ 1 * Real.exp (-(K.c₀ * n)) := by positivity
        have h4 : 0 ≤ (N : ℝ) * (Cc * 4 ^ d * R ^ d * Real.exp (-(1 * As))) := by positivity
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) h4,
          ENNReal.ofReal_add (by positivity) h3, ENNReal.ofReal_add h1 h2]
    _ ≤ ENNReal.ofReal (K.C₃ * R ^ K.M₃ * δ ^ (-K.M₃) * Real.exp (-K.c₃ * δ ^ K.M₃ * n)) :=
        ENNReal.ofReal_le_ofReal hsumF

end HigherDimLQGContinuity
