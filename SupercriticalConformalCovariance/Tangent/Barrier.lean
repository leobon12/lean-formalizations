import SupercriticalConformalCovariance.Tangent.BarrierProb
import SupercriticalConformalCovariance.Tangent.Main

/-!
# Lemma 3.3, step 6: the barrier for the transformed fields

Paper l. 224–228: "Lemma 3.2 implies that for each fixed inner disk `B_R` and `δ > 0` one can choose
`S` so that, with probability at least `1 − δ`, all distances between points of `B_R` agree with
those confined to `B_S`. Since `ψ_n(K_n)` eventually contains every fixed target disk, the same
barrier event transfers to the transformed field by the preceding total-variation comparison."

`targetBarrier_holds` discharges `TargetBarrier`. Route:
1. the margin event `around(A) < θ · across(B)` (`exists_margin_prob`, from SupercriticalLQGUniqueness) has
   probability `≥ 1 − δ/2` for `h^a`;
2. it is a pathwise local Borel observable (`isPathwiseLocal_margin`), so the universal local
   functional and the total-variation convergence of the normalized fields (GM (2.6)) transfer it
   to `G_n` up to `TV_n`;
3. on it, the strict barrier holds for the realized field near `B̄_{S₀}` (Weyl stability with the
   clamped correction `Q log |(ψ_n⁻¹)′|`, `around_lt_across_of_weyl`; locality);
4. the deterministic surgery (`internal_eq_of_around_lt_across`) then identifies the target metric
   internal to any compact `Y ⊇ B̄_{S₀}` with the one internal to `B̄_{S₀}` on `B̄_b × B̄_b`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric Function
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open LQGMetric (DistC DistOn TestOn TestC restrictTo addFun addConst ofCont IsGFFPlusCont
  IsWholePlaneGFF CoordJ)
open SupercriticalLQGUniqueness (LSCMetric LSCFun IsStrongLQGMetric aroundDist acrossDist weylScale)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization
  weylScaleOn)
open SupercriticalConformalCovariance.Domain (confined resC cutF exW exWO exW_subset cutF_eq exists_subset_exW
  ae_weylScaleOn_eq_internal isGFFPlusCont_addFun_of_measurable measurable_cutExt)
open SupercriticalConformalCovariance.GM24 (isConformalBijection_invFunOn dilDist)
open QuantumZipper.TV (tvDist)

/-- Two whole-plane fields `x + F`, `x + F'` with `F = F'` on an open `W` agree on `W`. -/
theorem restrictTo_addFun_eq_of_eqOn (W : Opens ℂ) (x : DistC) {F F' : C(ℂ, ℝ)}
    (hFF : ∀ z ∈ (W : Set ℂ), F z = F' z) : restrictTo W (addFun x F) = restrictTo W (addFun x F') := by
  ext g
  show addFun x F _ = addFun x F' _
  simp only [addFun, add_apply, LQGMetric.ofCont_apply]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  by_cases hz : z ∈ (W : Set ℂ)
  · rw [hFF z hz]
  · have : (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := ⊤) g : ℂ → ℝ) z = 0 := by
      rw [SupercriticalConformalCovariance.Domain.coe_monoCLM le_top]
      exact image_eq_zero_of_notMem_tsupport fun h' => hz (g.tsupport_subset h')
    simp only [ContinuousLinearMap.coe_coe] at *
    rw [this, zero_mul, zero_mul]

/-- Clamp a continuous function to `[lo, hi]`. -/
def clampC (lo hi : ℝ) (F : C(ℂ, ℝ)) : C(ℂ, ℝ) :=
  ⟨fun z => max lo (min hi (F z)), continuous_const.max (continuous_const.min F.continuous)⟩

theorem clampC_apply (lo hi : ℝ) (F : C(ℂ, ℝ)) (z : ℂ) : clampC lo hi F z = max lo (min hi (F z)) :=
  rfl

/-- **The barrier for the transformed fields** (paper l. 224–228). -/
theorem targetBarrier_holds {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : 0 < Q) {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (hTV : GMLemma24TV)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ (U n : Set ℂ))
    (hzero : ∀ n, ψ n 0 = 0) {a : ℂ} (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {f : TestC} (hf1 : ∫ x, f x = 1)
    (hrot : ∀ u : ℂ, ‖u‖ = 1 → ∀ z : ℂ, f (u * z) = f z) (hnorm : ∀ᵐ ω ∂P, h ω f = 0)
    (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hreal : ∀ n, IsDomainRealization (V n) P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn (hψ n)) (restrictTo (U n) (h ω)))
      (hbar n) (fr n)) :
    TargetBarrier (ξ : ℝ) D P V hbar fr := by
  classical
  intro b hb δ hδ
  set bb : Set.Ioi (0 : ℝ) := ⟨b, hb⟩ with hbb
  have hα : a⁻¹ ≠ 0 := inv_ne_zero ha0
  have hopen : ∀ n, IsOpen (U n : Set ℂ) := fun n => (U n).isOpen
  have hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n) := fun n => (hψ n).1
  have hinj : ∀ n, InjOn (ψ n) (U n) := fun n => (hψ n).2.injOn
  have hξ : (0 : ℝ) ≤ ξ := le_of_lt ξ.2
  set ℓ : ℝ := -(Q * Real.log ‖a‖) with hℓ
  set Glim : Ω → DistC := fun ω => dilDist hα (h ω) with hGlimdef
  have hGlimW : IsWholePlaneGFF Glim P := SupercriticalConformalCovariance.GM24.isWholePlaneGFF_dilDist hh hα
  have hGlim : IsGFFPlusCont Glim P := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hGlimW
  -- step 1: the margin event for `h^a`
  obtain ⟨J, hJ, θ, hθ0, hθ1, hθprob⟩ :=
    exists_margin_prob hQ hD P hGlimW bb (δ := δ / 2) (by positivity)
  set A := annA bb with hA
  set B := annB J bb with hB
  set S₀ : ℝ := 2 ^ (J + 1) * b + 1 with hS₀
  have h2J : (4 : ℝ) ≤ 2 ^ J := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ J := pow_le_pow_right₀ one_le_two hJ
  have hBout : B.outerRadius = 2 ^ (J + 1) * b := annB_outerRadius J bb
  have hbS₀ : b < S₀ := by
    have : b ≤ 2 ^ (J + 1) * b := le_mul_of_one_le_left hb.le (one_le_pow₀ one_le_two)
    linarith
  have hS₀pos : 0 < S₀ := hb.trans hbS₀
  refine ⟨S₀, hbS₀, ?_⟩
  -- the normalized fields near `B̄_ρ`, `ρ > S₀`
  obtain ⟨ρ, N₀, m, c, G, hSρ, hcm, hc0, hG, hGn, hconv, hTVc⟩ :=
    exists_normField_package hD hTV hψ hzeroU hexhaust hzero ha0 ha P hh hf1 hrot hnorm hbar fr
      hreal hS₀pos
  -- geometry of the annuli
  have hAsub : A.toSet ⊆ ball (0 : ℂ) S₀ := by
    intro z hz
    have h1 := hz.1
    simp only [hA, SupercriticalLQGUniqueness.EuclideanAnnulus.toSet] at h1
    rw [annA_center, annA_outerRadius] at h1
    refine ball_subset_ball ?_ h1
    have : 4 * b ≤ 2 ^ (J + 1) * b := by
      rw [pow_succ]; nlinarith
    change 4 * b ≤ S₀; linarith
  have hBsub : closedBall B.center B.outerRadius ⊆ ball (0 : ℂ) S₀ := by
    rw [annB_center, hBout]
    exact closedBall_subset_ball (by linarith)
  have hS₀ρ : ball (0 : ℂ) S₀ ⊆ ballO ρ := ball_subset_ball hSρ.le
  -- step 2: one Borel functional for the margin event, and the total-variation transfer
  obtain ⟨Φ, hΦm, hΦ⟩ := exists_universal_local_functional (ballO ρ)
    (measurable_marginEvent hD.1 A B θ)
    (isPathwiseLocal_margin hD (ballO ρ) A B (hAsub.trans hS₀ρ) (hBsub.trans hS₀ρ) θ)
    (Option ℕ) (fun _ => Ω) (fun _ => P) (fun i => Option.elim i Glim G)
    (fun i => by cases i with
      | none => exact hGlim
      | some n => exact hG n)
  have hXm : ∀ n, Measurable fun ω => locCoord (ballO ρ) (G n ω) := fun n =>
    (measurable_locCoord _).comp (hG n).1
  have hYm : Measurable fun ω => locCoord (ballO ρ) (Glim ω) :=
    (measurable_locCoord _).comp hGlim.1
  have hTVineq : ∀ n, P {ω | marginEvent D A B θ (G n ω) = false} ≤
      ENNReal.ofReal (δ / 2) + tvDist (P.map fun ω => locCoord (ballO ρ) (G n ω))
        (P.map fun ω => locCoord (ballO ρ) (Glim ω)) := by
    intro n
    have hs : MeasurableSet (Φ ⁻¹' {false}) := hΦm (measurableSet_singleton false)
    have e1 : P {ω | marginEvent D A B θ (G n ω) = false} =
        (P.map fun ω => locCoord (ballO ρ) (G n ω)) (Φ ⁻¹' {false}) := by
      rw [Measure.map_apply (hXm n) hs]
      refine measure_congr ?_
      filter_upwards [hΦ (some n)] with ω hω
      simp only [Option.elim] at hω
      change (marginEvent D A B θ (G n ω) = false) = (Φ (locCoord (ballO ρ) (G n ω)) = false)
      rw [hω]
    have e2 : (P.map fun ω => locCoord (ballO ρ) (Glim ω)) (Φ ⁻¹' {false}) =
        P {ω | marginEvent D A B θ (Glim ω) = false} := by
      rw [Measure.map_apply hYm hs]
      refine measure_congr ?_
      filter_upwards [hΦ none] with ω hω
      simp only [Option.elim] at hω
      change (Φ (locCoord (ballO ρ) (Glim ω)) = false) = (marginEvent D A B θ (Glim ω) = false)
      rw [hω]
    rw [e1]
    have h3 := QuantumZipper.TV.le_tvDist (μ := P.map fun ω => locCoord (ballO ρ) (G n ω))
      (ν := P.map fun ω => locCoord (ballO ρ) (Glim ω)) hs
    rw [tsub_le_iff_right, e2] at h3
    calc _ ≤ tvDist _ _ + P {ω | marginEvent D A B θ (Glim ω) = false} := h3
      _ ≤ tvDist _ _ + ENNReal.ofReal (δ / 2) := by gcongr
      _ = _ := add_comm _ _
  -- the Weyl correction is uniformly small on `B̄_{S₀}`
  obtain ⟨ε, hε0, hεb⟩ := exists_eps_logDerivInv Q hopen hzeroU hexhaust hd hinj hzero ha0 ha S₀
  have hev1 : ∀ᶠ n in atTop, θ * Real.exp ((ξ : ℝ) * (2 * ε n)) ≤ 1 := by
    have ht : Tendsto (fun n => θ * Real.exp ((ξ : ℝ) * (2 * ε n))) atTop (𝓝 θ) := by
      have h0 : Tendsto (fun n => (ξ : ℝ) * (2 * ε n)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (ξ : ℝ))).mul (hε0.const_mul 2)
      have := ((Real.continuous_exp.tendsto 0).comp h0).const_mul θ
      simpa using this
    exact ht.eventually (Iic_mem_nhds hθ1)
  have hev2 : ∀ᶠ n in atTop, tvDist (P.map fun ω => locCoord (ballO ρ) (G n ω))
      (P.map fun ω => locCoord (ballO ρ) (Glim ω)) ≤ ENNReal.ofReal (δ / 2) :=
    hTVc.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 (by positivity)))
  filter_upwards [eventually_ge_atTop N₀, hεb, hev1, hev2] with n hn hεn hθn htvn
  obtain ⟨hVρ, hρm, hGeq⟩ := hGn n hn
  have hεpos : 0 ≤ ε n := (abs_nonneg _).trans (hεn 0 (mem_closedBall_self hS₀pos.le))
  set L := logDerivInv Q (hψ n) with hL
  set gcl : C(ℂ, ℝ) := clampC (ℓ - ε n) (ℓ + ε n) (cutF (V n) (m n) L) with hgcl
  set Gev : Ω → DistC := fun ω => addFun (G n ω) (gcl + ContinuousMap.const ℂ (c n ω)) with hGev
  have hGevm : Measurable fun ω => gcl + ContinuousMap.const ℂ (c n ω) := by
    rw [ContinuousMap.measurable_iff_eval]
    intro z
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    exact measurable_const.add (hcm n)
  have hGevc : IsGFFPlusCont Gev P := isGFFPlusCont_addFun_of_measurable (hG n) hGevm
  set H : ℕ → Ω → DistC := fun m' ω => addFun (hbar n ω) (cutF (V n) m' (fr n ω)) with hH
  have hHc : ∀ m', IsGFFPlusCont (H m') P := fun m' =>
    isGFFPlusCont_addFun_of_measurable (hreal n).2.1 (measurable_cutExt (V n).isOpen _ (hreal n).2.2.1)
  set W : Opens ℂ := ⟨ball 0 S₀, isOpen_ball⟩ with hW
  -- the fields `H m'` and `Gev` agree on `W` whenever `W ⊆ exW (V n) m'`
  have hagree : ∀ m', ball (0 : ℂ) S₀ ⊆ exW (V n) m' → ∀ ω,
      restrictTo W (H m' ω) = restrictTo W (Gev ω) := by
    intro m' hm' ω
    simp only [hH, hGev, hGeq ω, SupercriticalConformalCovariance.Lemma31.addFun_addFun]
    refine restrictTo_addFun_eq_of_eqOn W _ fun z hz => ?_
    have hzρ : z ∈ exW (V n) (m n) := hρm (ball_subset_closedBall (ball_subset_ball hSρ.le hz))
    have hzK : z ∈ closedBall (0 : ℂ) S₀ := ball_subset_closedBall hz
    have hLz := hεn z hzK
    simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply, hgcl,
      clampC_apply]
    rw [cutF_eq (V n) m' (fr n ω) z (hm' hz), cutF_eq (V n) (m n) (fr n ω) z hzρ,
      cutF_eq (V n) (m n) L z hzρ]
    have hL' : L ⟨z, exW_subset (V n) (m n) hzρ⟩ =
        Q * Real.log ‖deriv (invFunOn (ψ n) (U n)) z‖ := rfl
    rw [hL'] at *
    have h1 := (abs_le.1 hLz).1
    have h2 := (abs_le.1 hLz).2
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    have : (fr n ω ⟨z, exW_subset (V n) m' (hm' hz)⟩ : ℝ) =
        fr n ω ⟨z, exW_subset (V n) (m n) hzρ⟩ := rfl
    rw [this]
    ring
  -- the almost sure events
  have hE1 := ae_weylScaleOn_eq_internal hD P (hreal n).2.1
  have hE2 : ∀ᵐ ω ∂P, ∀ m', Continuous (SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.forget
      (D (H m' ω))) ∧ (D (H m' ω)).IsLengthSpace := by
    rw [ae_all_iff]
    intro m'
    filter_upwards [SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P (H m') (hHc m')] with ω hω
    exact ⟨hω.1, hω.2.1⟩
  have hE3 : ∀ᵐ ω ∂P, ∀ m', ball (0 : ℂ) S₀ ⊆ exW (V n) m' →
      (D (H m' ω)).internal (W : Set ℂ) = (D (Gev ω)).internal (W : Set ℂ) := by
    rw [ae_all_iff]
    intro m'
    by_cases hm' : ball (0 : ℂ) S₀ ⊆ exW (V n) m'
    · filter_upwards [SupercriticalConformalCovariance.Domain.ae_internal_eq_of_ae_restrictTo_eq_lsc hD (hHc m') hGevc W
        (Eventually.of_forall (hagree m' hm'))] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω hm'' => absurd hm'' hm'
  have hE4 := SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P (G n) (hG n)
  have hE5 := SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P Gev hGevc
  set Good : Set Ω := {ω | (∀ (K : Set ℂ) (f : C(K, ℝ)) (F : C(ℂ, ℝ)),
      (∀ z (hz : z ∈ K), F z = f ⟨z, hz⟩) → ∀ p : K × K,
        weylScaleOn (ξ : ℝ) f (D (hbar n ω)) p = (D (addFun (hbar n ω) F)).internal K p) ∧
      (∀ m', Continuous (SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.forget
        (D (H m' ω))) ∧ (D (H m' ω)).IsLengthSpace) ∧
      (∀ m', ball (0 : ℂ) S₀ ⊆ exW (V n) m' →
        (D (H m' ω)).internal (W : Set ℂ) = (D (Gev ω)).internal (W : Set ℂ)) ∧
      (Continuous (SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.forget (D (G n ω))) ∧
        (D (G n ω)).IsLengthSpace ∧
        ∀ g : C(ℂ, ℝ), weylScale (ξ : ℝ) g (D (G n ω)) = (D (addFun (G n ω) g)).1) ∧
      (Continuous (SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.forget (D (Gev ω))) ∧
        (D (Gev ω)).IsLengthSpace)} with hGood
  have hGoodae : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [hE1, hE2, hE3, hE4, hE5] with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5.1, h5.2.1⟩
  -- the inclusion
  refine (measure_mono (t := {ω | marginEvent D A B θ (G n ω) = false} ∪ Goodᶜ) ?_).trans
    ((measure_union_le _ _).trans ?_)
  · intro ω hω
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hmarg0, hgood⟩ := hcon
    have hmarg : marginEvent D A B θ (G n ω) = true := by
      cases hm : marginEvent D A B θ (G n ω)
      · exact absurd hm hmarg0
      · rfl
    obtain ⟨g1, g2, g3, ⟨g4f, g4L, g4W⟩, g5f, g5L⟩ := hgood
    apply hω
    intro Y hYc hY hYV x hx y hy
    -- (a) the strict barrier for `Gev`
    have hlt0 := marginEvent_eq_true.1 hmarg
    have hWeyl : ∀ p : ℂ × ℂ, D (Gev ω) p =
        weylScale (ξ : ℝ) (gcl + ContinuousMap.const ℂ (c n ω)) (D (G n ω)) p := fun p => by
      rw [g4W]
    have hbnd : ∀ z : ℂ, c n ω + ℓ - ε n ≤ (gcl + ContinuousMap.const ℂ (c n ω)) z ∧
        (gcl + ContinuousMap.const ℂ (c n ω)) z ≤ c n ω + ℓ + ε n := by
      intro z
      simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, hgcl, clampC_apply]
      constructor
      · have := le_max_left (ℓ - ε n) (min (ℓ + ε n) (cutF (V n) (m n) L z)); linarith
      · have := max_le (by linarith : ℓ - ε n ≤ ℓ + ε n)
          (min_le_left (ℓ + ε n) (cutF (V n) (m n) L z)); linarith
    have hθw : θ * Real.exp ((ξ : ℝ) * ((c n ω + ℓ + ε n) - (c n ω + ℓ - ε n))) ≤ 1 := by
      convert hθn using 3; ring
    have hltev : aroundDist (D (Gev ω)) A < acrossDist (D (Gev ω)) B :=
      around_lt_across_of_weyl (D (G n ω)) (D (Gev ω)) (ξ : ℝ) hξ _ _ _ g4f hWeyl hbnd g4L A B
        hθ0.le hθw hlt0
    -- (b) transfer to `H m'`, `Y ⊆ exW (V n) m'`
    obtain ⟨m', hm'⟩ := exists_subset_exW (V n).isOpen hYc hYV
    have hWm' : ball (0 : ℂ) S₀ ⊆ exW (V n) m' := ball_subset_closedBall.trans (hY.trans hm')
    obtain ⟨hAeq, hBeq⟩ := around_across_eq_of_internal_eq (g2 m').1 g5f (g2 m').2 g5L
      (g3 m' hWm') A B hAsub hBsub
    have hltH : aroundDist (D (H m' ω)) A < acrossDist (D (H m' ω)) B := by
      rw [hAeq, hBeq]; exact hltev
    -- (c) the surgery
    have hxK : x ∈ closedBall (0 : ℂ) S₀ := closedBall_subset_closedBall hbS₀.le hx
    have hyK : y ∈ closedBall (0 : ℂ) S₀ := closedBall_subset_closedBall hbS₀.le hy
    have hsurg := internal_eq_of_around_lt_across (D (H m' ω))
      (fun γ s t hγ => (g2 m').1.comp_continuousOn hγ.2) A B (annA_center bb) (annB_center J bb)
      (by rw [annA_outerRadius, annB_innerRadius]; change 4 * b ≤ 2 ^ J * b; nlinarith)
      (r := b) (by rw [annA_innerRadius]; change b ≤ 2 * b; linarith)
      (by rw [hBout]; linarith) hltH hY hx hy hxK hyK
    -- (d) the confined metrics are internal metrics of `D (H m')`
    have hext : ∀ (K' : Set ℂ) (hK'V : K' ⊆ (V n : Set ℂ)), K' ⊆ exW (V n) m' →
        ∀ z (hz : z ∈ K'), cutF (V n) m' (fr n ω) z = resC hK'V (fr n ω) ⟨z, hz⟩ := by
      intro K' hK'V hK'm z hz
      rw [cutF_eq (V n) m' (fr n ω) z (hK'm hz)]
      rfl
    unfold confined
    rw [dif_pos ⟨hY hxK, hY hyK⟩, dif_pos ⟨hxK, hyK⟩]
    rw [g1 Y (resC hYV (fr n ω)) (cutF (V n) m' (fr n ω)) (hext Y hYV hm'),
      g1 (closedBall 0 S₀) (resC (hY.trans hYV) (fr n ω)) (cutF (V n) m' (fr n ω))
        (hext _ (hY.trans hYV) (hY.trans hm'))]
    exact hsurg
  · rw [show P Goodᶜ = 0 from ae_iff.1 hGoodae, add_zero]
    calc P {ω | marginEvent D A B θ (G n ω) = false}
        ≤ ENNReal.ofReal (δ / 2) + tvDist _ _ := hTVineq n
      _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := by gcongr
      _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end SupercriticalConformalCovariance.Tangent
