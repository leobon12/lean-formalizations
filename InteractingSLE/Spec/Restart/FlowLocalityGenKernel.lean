/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowLocalityGenKernelTilt
import InteractingSLE.Spec.Restart.FlowLocalityGenConverse

/-!
# Flow locality with a general agreement set: the per-stop identification from the pocket mean identity

Packet PROVE-G7A-LOC. `ShiftKernelGenStatement` (the per-stop Cameron–Martin identification with every born pocket
retained) is reduced to ONE deterministic, pathwise statement:

* **`PocketMeanIdentStatement`** (named input, PROVE-G3RESTART §6.6): along a continuous driver whose trace up to `t`
  lies in the chart buffer `N − y` (only the RANGE, not the filled hull), for a test `φ` off the filled hull,
  `∫ M^b_t φ − greenCross_t(φ, 1_{ℍ∖K_t} F_y.src) + T_y(φ) = ∫ M^{bR}_t φ` — the landed interval identity
  `FlowStopIdentCMI.integral_couplingMean_shift_eq` with the source restricted to its alive part;
* `pocketMeanIdent_of_hull`: when the hull closure lies in the buffer the identity is the landed one (the alive
  restriction changes nothing), so the named statement only adds the case of a hull that swallowed source mass;
* **`shiftKernelGenStatement_of_meanIdent`**: the reduction — localization of the stop (`τ ∧ n`, Mathlib's
  `condExp_min_stopping_time_ae_eq_restrict_le_const`), the bounded-stop tilt `GSetting.ae_condExp_chart_tilt_bdd`,
  the transport to the frozen driver, and the named identity;
* **`g7aChartStatement_of_meanIdent`**-style wiring is in `RLCG7aAssembly`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowLocalityGen
open QuantumZipper (H Hbar fwdHull)
open LQGMetric (TestOn DistOn)
open FlowStopIdentCMI StoppedExtend

/-- **Named input (deterministic): the mean identity with pocket mass** (PROVE-G3RESTART §6.6; Corollary G7a's
proof, supplement p. 499, "with every born pocket retained"). For data `b`, `bR` agreeing on an open `O ∋ y`, the
bounded harmonic extension `q` of `bR − b`, a cutoff `F = q` harmonic on an open buffer `N ∋ y` with real points over
`O`, a continuous driver `w'` (`w' 0 = 0`) whose hulls up to `t > 0` are filled by a trace `η` whose RANGE lies in the
chart buffer `N − y`, and the two flow-line words' extensions at the geometric mark images: for every test `φ` off
the filled hull, `∫ M^b_t φ − greenCross_t(φ, 1_{ℍ∖K_t} F_y.src) + T_y(φ) = ∫ M^{bR}_t φ`. -/
def PocketMeanIdentStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ y : ℝ, y ∈ O → ∀ θ : ℝ, ∀ (F : CMCut) (q : ℂ → ℝ),
    IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) → (∀ z ∈ N, z ∈ H → F.f z = q z) →
    (∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) → (y : ℂ) ∈ N →
    ∀ w' : ℝ≥0 → ℝ, Continuous w' → w' 0 = 0 → ∀ t : ℝ≥0, 0 < t →
    ∀ η : ℝ → ℂ, ContinuousOn η (Icc 0 (t : ℝ)) →
    (∀ s ∈ Ioc (0 : ℝ) t, fwdHull (Ito.rpath w') s = fillH (η '' Icc 0 s)) →
    (∀ s ∈ Icc (0 : ℝ) t, η s + y ∈ N) →
    ∀ uR u : ℂ → ℝ,
    IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ)
        (fun i => geomL (Ito.rpath w') t (flowLineXL bR Ĵ y i)) (fun j => geomR (Ito.rpath w') t (flowLineXR bR Ĵ y j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') t (flowLineXL bR Ĵ y i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR bR Ĵ y j))) uR →
    IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ)
        (fun i => geomL (Ito.rpath w') t (flowLineXL b J y i)) (fun j => geomR (Ito.rpath w') t (flowLineXR b J y j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') t (flowLineXL b J y i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR b J y j))) u →
    ∀ φ : TestOn upperHalfPlaneOpens, Disjoint (tsupport φ) (fwdHull (Ito.rpath w') t) →
      (∫ z, couplingMean κ (Ito.rpath w') t u z * φ z) -
          LocalExt.greenCross (Ito.rpath w') t φ ((H \ fwdHull (Ito.rpath w') t).indicator (F.shift y).src) +
        chartShift F q y φ = ∫ z, couplingMean κ (Ito.rpath w') t uR z * φ z

/-- The alive restriction of the chart source is the source itself when the hull lies in the chart buffer. -/
theorem indicator_src_eq_of_hull {F : CMCut} {N : Set ℂ} (hFΔ : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0)
    {y : ℝ} {K : Set ℂ} (hKN : K ⊆ (fun z => z + y) ⁻¹' N) :
    (H \ K).indicator (F.shift y).src = (F.shift y).src := by
  refine indicator_eq_self.2 fun z hz => ?_
  have hz' : (F.shift y).src z ≠ 0 := hz
  by_cases hzH : z ∈ H
  · refine ⟨hzH, fun hzK => hz' ?_⟩
    rw [(F.shift y).src_of_mem hzH, CMCut.greenDensity_shift, hFΔ _ (hKN hzK), neg_zero]
  · exact absurd ((F.shift y).src_of_notMem hzH) hz'

/-- **The named identity holds when the hull closure lies in the buffer** (the landed interval identity
`FlowStopIdentCMI.integral_couplingMean_shift_eq`). -/
theorem pocketMeanIdent_of_hull {κ : ℝ} (hκ : 0 < κ) {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR Ĵ) {O : Set ℝ}
    (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {y : ℝ} (hy : y ∈ O) (θ : ℝ) {F : CMCut} {q : ℂ → ℝ}
    (hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q) {N : Set ℂ}
    (hNo : IsOpen N) (hNO : ∀ z ∈ N, z.im = 0 → z.re ∈ O) (hFq : ∀ z ∈ N, z ∈ H → F.f z = q z)
    (hFΔ : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) (hyN : (y : ℂ) ∈ N) {w' : ℝ≥0 → ℝ}
    (hw' : Continuous w') (hw0 : w' 0 = 0) {t : ℝ≥0} (ht : 0 < t) {η : ℝ → ℂ} (hηc : ContinuousOn η (Icc 0 t))
    (hfill : ∀ s ∈ Ioc (0 : ℝ) t, fwdHull (Ito.rpath w') s = fillH (η '' Icc 0 s))
    (hKN : closure (fwdHull (Ito.rpath w') t) ⊆ (fun z => z + y) ⁻¹' N) {uR u : ℂ → ℝ}
    (huR : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ)
        (fun i => geomL (Ito.rpath w') t (flowLineXL bR Ĵ y i)) (fun j => geomR (Ito.rpath w') t (flowLineXR bR Ĵ y j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') t (flowLineXL bR Ĵ y i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR bR Ĵ y j))) uR)
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ)
        (fun i => geomL (Ito.rpath w') t (flowLineXL b J y i)) (fun j => geomR (Ito.rpath w') t (flowLineXR b J y j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') t (flowLineXL b J y i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR b J y j))) u)
    (φ : TestOn upperHalfPlaneOpens) (hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w') t)) :
    (∫ z, couplingMean κ (Ito.rpath w') t u z * φ z) -
        LocalExt.greenCross (Ito.rpath w') t φ ((H \ fwdHull (Ito.rpath w') t).indicator (F.shift y).src) +
      chartShift F q y φ = ∫ z, couplingMean κ (Ito.rpath w') t uR z * φ z := by
  classical
  rw [indicator_src_eq_of_hull hFΔ (subset_closure.trans hKN)]
  exact integral_couplingMean_shift_eq hκ hb hbR hO hbO hy θ hq hNo hNO hFq hFΔ hyN hw' hw0 ht hηc hfill hKN huR
    hu φ hφ

/-- **The per-stop identification with retained pockets from the pocket mean identity.** -/
theorem shiftKernelGenStatement_of_meanIdent (hM : PocketMeanIdentStatement) : ShiftKernelGenStatement.{u} := by
  classical
  intro S _ D τ hτ hτx W₁ hpath uR huR φ
  let _ := D.Q₀_prob
  let _ : IsProbabilityMeasure D.tilt := D.tilt_prob
  have hQP : D.tilt ≪ D.Q₀ := D.tilt_equivalent.1
  set X : S → ℂ := fun ω' => Complex.exp (Complex.I * (D.chartField ω' φ : ℂ)) with hX
  -- the bounded stops `τ ∧ n`
  set τn : ℕ → S → ℝ≥0 := fun n ω => (min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0)).untopD 0 with hτn
  have hτn_coe : ∀ n ω, ((τn n ω : ℝ≥0) : WithTop ℝ≥0) = min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0) := fun n ω =>
    Coupling.coe_untopD_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _))
  have hfun : ∀ n, (fun ω => ((τn n ω : ℝ≥0) : WithTop ℝ≥0)) = fun ω => min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0) :=
    fun n => funext (hτn_coe n)
  have hτs : ∀ n, IsStoppingTime D.driving fun ω => ((τn n ω : ℝ≥0) : WithTop ℝ≥0) := fun n => by
    rw [hfun n]; exact hτ.min_const _
  have hms : ∀ n, (hτs n).measurableSpace = (hτ.min_const (n : ℝ≥0)).measurableSpace := by
    have key : ∀ {σ σ' : S → WithTop ℝ≥0} (_ : σ = σ') (hσ : IsStoppingTime D.driving σ)
        (hσ' : IsStoppingTime D.driving σ'), hσ.measurableSpace = hσ'.measurableSpace := by
      intro σ σ' h hσ hσ'; subst h; rfl
    exact fun n => key (hfun n) _ _
  have hloc : ∀ n : ℕ, ∀ᵐ ω ∂D.tilt, τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) →
      D.tilt[X | (hτs n).measurableSpace] ω = D.tilt[X | hτ.measurableSpace] ω := fun n => by
    have h := condExp_min_stopping_time_ae_eq_restrict_le_const (μ := D.tilt) (f := X) hτ (n : ℝ≥0)
    rw [← hms n] at h
    exact (ae_restrict_iff' (hτ.measurableSpace_le _ (hτ.measurableSet_le' _))).1 h
  -- finiteness of the stop
  have hfin : ∀ᵐ ω ∂D.Q₀, ∃ t : ℝ≥0, τ ω = (t : WithTop ℝ≥0) := by
    filter_upwards [hτx] with ω hω
    have hne : τ ω ≠ ⊤ := fun h => by
      rw [h] at hω
      exact absurd hω (not_lt.2 le_top)
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
    exact ⟨t, ht.symm⟩
  have hτn_of : ∀ n ω (t : ℝ≥0), τ ω = (t : WithTop ℝ≥0) → τn n ω = min t n := fun n ω t h => by
    simp only [hτn, h, ← WithTop.coe_min]
    rfl
  -- the bounded-stop tilt
  have hb : ∀ n : ℕ, ∀ᵐ ω ∂D.tilt, Disjoint (tsupport φ) (fwdHull (Ito.rpath (W₁ · ω)) (τn n ω)) →
      D.tilt[X | (hτs n).measurableSpace] ω =
        LocalExt.cfVal ((∫ z, couplingMean D.κ (Ito.rpath (D.W₀ · ω)) (τn n ω) (D.ubAt (τn n) ω) z * φ z) -
          LocalExt.greenCross (Ito.rpath (W₁ · ω)) (τn n ω) φ
            ((H \ fwdHull (Ito.rpath (W₁ · ω)) (τn n ω)).indicator (D.F.shift D.y).src) +
          chartShift D.F D.q D.y φ) (loewnerGreenEnergy (Ito.rpath (D.W₀ · ω)) (τn n ω) φ) := by
    intro n
    refine D.ae_condExp_chart_tilt_bdd (τn n) (hτs n) ⟨n, fun ω => ?_⟩ ?_ ?_ φ
    · have h : ((τn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := by
        rw [hτn_coe]; exact min_le_right _ _
      exact WithTop.coe_le_coe.1 h
    · filter_upwards [hτx, hfin] with ω hω ⟨t, ht⟩
      rw [hτn_of n ω t ht]
      rw [ht] at hω
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_left _ _)) hω
    · filter_upwards [hpath, hfin] with ω hp ⟨t, ht⟩
      obtain ⟨hc, -, ⟨t₂, ht₂, hag⟩, -⟩ := hp
      have hut : (τ ω).untopD 0 = t := by rw [ht]; rfl
      rw [hut] at ht₂
      refine ⟨hc, t₂, lt_of_le_of_lt ?_ ht₂, ?_⟩
      · rw [hτn_of n ω t ht]; exact_mod_cast min_le_left _ _
      · exact fun r hr => hag r hr
  -- assembly
  filter_upwards [ae_all_iff.2 hloc, ae_all_iff.2 hb, hQP.ae_le hpath, hQP.ae_le hτx, hQP.ae_le hfin,
    hQP.ae_le D.trace] with ω hl hbω hp hω ⟨t, ht⟩ hg hφ
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
  have htn' : t ≤ (n : ℝ≥0) := by exact_mod_cast hn
  have htn : τn n ω = t := by rw [hτn_of n ω t ht, min_eq_left htn']
  have hut : (τ ω).untopD 0 = t := by rw [ht]; rfl
  have hle : τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := by rw [ht]; exact WithTop.coe_le_coe.2 htn'
  obtain ⟨hc1, hc0, ⟨t₂, ht₂, hag⟩, hL, hR, -, -⟩ := hp
  rw [hut] at hφ ht₂ hL hR ⊢
  have hb' := hbω n
  rw [htn] at hb'
  rw [← hl n hle, hb' hφ]
  have hτe : (t : ℝ≥0∞) < RLC.exitTime D.V (D.Γ ω) (D.U ω) := by rw [ht] at hω; exact hω
  have ht0 : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  have hagt : EqOn (Ito.rpath (D.W₀ · ω)) (Ito.rpath (W₁ · ω)) (Icc 0 (t : ℝ)) := fun r hr =>
    (hag r ⟨hr.1, hr.2.trans ht₂.le⟩).symm
  have hmean : ∀ v : ℂ → ℝ, ∫ z, couplingMean D.κ (Ito.rpath (D.W₀ · ω)) t v z * φ z =
      ∫ z, couplingMean D.κ (Ito.rpath (W₁ · ω)) t v z * φ z := fun v =>
    integral_congr_ae (ae_of_all _ fun z => by
      simp only; rw [StoppedK2.couplingMean_congr_Icc ht0 hagt D.κ v z])
  rw [hmean, StoppedK2.loewnerGreenEnergy_congr_Icc hagt φ]
  congr 1
  -- the source extension at the geometric images
  have hub : IsBoundedHarmonicExtension
      (forceBoundaryData D.κ (flowLineRhoL D.κ D.b D.J D.y D.θ) (flowLineRhoR D.κ D.b D.J D.y D.θ)
        (fun i => geomL (Ito.rpath (W₁ · ω)) t (flowLineXL D.b D.J D.y i))
        (fun j => geomR (Ito.rpath (W₁ · ω)) t (flowLineXR D.b D.J D.y j)))
      (forceJumpSet (fun i => geomL (Ito.rpath (W₁ · ω)) t (flowLineXL D.b D.J D.y i))
        (fun j => geomR (Ito.rpath (W₁ · ω)) t (flowLineXR D.b D.J D.y j))) (D.ubAt (τn n) ω) := by
    have h := MartChar.isBoundedHarmonicExtension_meanExt D.κ (flowLineRhoL D.κ D.b D.J D.y D.θ)
      (flowLineRhoR D.κ D.b D.J D.y D.θ) (D.W₀ (τn n ω) ω) (fun i => D.VL₀ i (τn n ω) ω)
      (fun j => D.VR₀ j (τn n ω) ω)
    have hpL : (fun i => D.VL₀ i t ω - D.W₀ t ω) = fun i => geomL (Ito.rpath (W₁ · ω)) t (flowLineXL D.b D.J D.y i) :=
      funext hL
    have hpR : (fun j => D.VR₀ j t ω - D.W₀ t ω) = fun j => geomR (Ito.rpath (W₁ · ω)) t (flowLineXR D.b D.J D.y j) :=
      funext hR
    rw [htn, hpL, hpR] at h
    simpa only [GSetting.ubAt, htn] using h
  -- the seed lies in the buffer (the exit is positive)
  have hy0 : D.Γ ω 0 = D.y := sub_eq_zero.1 hg.1
  have hyN : (D.y : ℂ) ∈ D.N := by
    have hyV : (D.y : ℂ) ∈ D.V := by
      by_contra hnot
      have hex := RLC.exitTime_eq_zero (V := D.V) (γ := D.Γ ω) (D.U ω) (by rwa [hy0])
      rw [hex] at hτe
      exact absurd hτe (not_lt.2 bot_le)
    exact D.closureV_subset (subset_closure hyV)
  have hyO : D.y ∈ D.O := by simpa using D.N_real _ hyN (by simp)
  rcases eq_zero_or_pos t with h0 | hpos
  · -- time `0`: the hull is empty
    subst h0
    have hW₁c : Continuous (Ito.rpath (W₁ · ω)) := hc1.comp continuous_real_toNNReal
    have hK0 : fwdHull (Ito.rpath (W₁ · ω)) ((0 : ℝ≥0) : ℝ) = ∅ := by
      rw [NNReal.coe_zero]; exact QuantumZipper.RS.fwdHull_zero_eq_empty hW₁c
    have hind : (H \ fwdHull (Ito.rpath (W₁ · ω)) ((0 : ℝ≥0) : ℝ)).indicator (D.F.shift D.y).src =
        (D.F.shift D.y).src := by
      rw [hK0, sdiff_empty]
      refine indicator_eq_self.2 fun z hz => ?_
      by_contra hzH
      exact hz ((D.F.shift D.y).src_of_notMem hzH)
    have huR' := huR ω
    rw [hut] at huR'
    rw [hind]
    simp only [NNReal.coe_zero] at huR' hub ⊢
    exact integral_couplingMean_shift_eq_zero D.κ_pos D.b_pc D.bR_pc D.O_open D.boundary_eq hyO D.θ D.F
      D.q_extension hc1 hc0 huR' hub φ
  · -- positive time: the trace `Γ − y` fills the hulls, its range lies in the buffer
    have hτU : (t : ℝ≥0∞) < D.U ω := hτe.trans_le (min_le_left _ _)
    set η : ℝ → ℂ := fun s => D.Γ ω s.toNNReal - D.y with hηdef
    have hηc : ContinuousOn η (Icc 0 (t : ℝ)) := by
      have h := hg.2.1.comp (s := Icc (0 : ℝ) t) continuous_real_toNNReal.continuousOn
        fun (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) => show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ D.U ω from
          (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)).trans hτU.le
      exact h
    have hKeq : ∀ r : ℝ, 0 ≤ r → r < t₂ →
        fwdHull (Ito.rpath (W₁ · ω)) r = fwdHull (Ito.rpath (D.W₀ · ω)) r := fun r hr hrt =>
      InteractingSLE.fwdHull_eq_of_eqOn hr hrt fun s hs => hag s hs
    have hfill : ∀ r ∈ Ioc (0 : ℝ) t, fwdHull (Ito.rpath (W₁ · ω)) r = fillH (η '' Icc 0 r) := by
      intro r hr
      have hr0 : 0 ≤ r := hr.1.le
      have hrU : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < D.U ω :=
        lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hτU
      have hfil : IsFilling (fwdHull (Ito.rpath (D.W₀ · ω)) (r.toNNReal : ℝ))
          ((fun s => D.Γ ω s - D.y) '' Icc 0 r.toNNReal) := hg.2.2 r.toNNReal hrU
      rw [Real.coe_toNNReal _ hr0] at hfil
      have hcA : IsCompact ((fun s => D.Γ ω s - D.y) '' Icc 0 r.toNNReal) := by
        have h := hg.2.1.mono fun s (hs : s ∈ Icc 0 r.toNNReal) => show (s : ℝ≥0∞) ≤ D.U ω from
          (ENNReal.coe_le_coe.2 hs.2).trans hrU.le
        exact isCompact_Icc.image_of_continuousOn h
      rw [hKeq r hr0 (hr.2.trans_lt ht₂), Sec5.CrossRestart.fwdHull_eq_fillH_of_isFilling hcA hfil,
        InteractingSLE.image_toNNReal_Icc (fun s => D.Γ ω s - D.y) hr0]
    have hηN : ∀ s ∈ Icc (0 : ℝ) t, η s + D.y ∈ D.N := by
      intro s hs
      have hsV : D.Γ ω s.toNNReal ∈ D.V := FlowStopIdentG.mem_of_lt_exitTime
        (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) hτe)
      simp only [hηdef, sub_add_cancel]
      exact D.closureV_subset (subset_closure hsV)
    have huR' := huR ω
    rw [hut] at huR'
    exact hM D.κ D.κ_pos D.b D.bR D.J D.JR D.b_pc D.bR_pc D.O D.O_open D.boundary_eq D.y hyO D.θ D.F D.q
      D.q_extension D.N D.N_open D.N_real D.cutoff_eq D.cutoff_harmonic hyN (W₁ · ω) hc1 hc0 t hpos η hηc
      hfill hηN (uR ω) (D.ubAt (τn n) ω) huR' hub φ hφ

end InteractingSLE.Restart.FlowLocalityGen
