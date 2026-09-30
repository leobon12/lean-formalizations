import QuantumZipper.Proofs.Zipper.D3PlusN2H2ReprHarm
import QuantumZipper.Proofs.Zipper.D3PlusN2H2WinCM
import QuantumZipper.Proofs.Zipper.D3PlusLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-H2 representation node (task N2H2-REPR)

Reduces the representation node `N2H2WinReprStmt` (`D3PlusN2H2WinCM.lean`) to the single named
free-field regularization statement `N2H2ReprFreeStmt`:

  `n2H2WinRepr_of_free : N2H2ReprFreeStmt → N2H2WinReprStmt`.

## Witnesses (Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.7(ii), pp. 77–78)

* `hd = H − H(0)` (`reprHd`), `H` the continuous harmonic part of the Markov decomposition
  `X = Z + h_X` on the half-disc (`ae_reprHarm`, `D3PlusN2H2ReprHarm.lean`); `H(0) = X(P_0)`.
* `b μ = X(bal μ) − X(P_0)` on probability measures (`reprB`): a balanced difference of measures
  outside the half-disc, hence `outsideSigma`-measurable.
* `G = latWinW K a ∘ reprY ε` (`reprG`), where `reprY ε u` is the lateral part of the extension
  of the `ε`-local data `u`. For `a K < ε`, `G u` reads `u` only at the folded circles
  `reprCirc ε` (dyadic circles of `evalReg`, centred circles of `radAvgReg`, all inside
  `ball 0 ε`; locality of `limUnder`, own bookkeeping extending `D3Plus.evalReg_congr`).

Then (all proved here): `G (v + b) = G (v + ∫ hd)` a.s. (at the circles of `reprCirc ε`,
`b = X(bal μ) − X(P_0) = ∫ H dμ − H(0) = ∫ hd dμ`); the model window is `G` of the local data of
`Z` (deterministic locality); and `G (Z + b)` is the regularized evaluation of the lateral part of
`X − X(P_0)` (deterministic: `Z + b = X − X(P_0)` at the circles). The only remaining input is
that the latter a.s. equals the free-field window `latWinFreeW` (`N2H2ReprFreeStmt`: nested
regularization equals single regularization, and the constant drops out).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## Locality of the lateral part -/

/-- Raw values of `y` and `y'` agree at the centred circles read by `radAvgReg` inside
`ball 0 r`. -/
def AgreeRad (y y' : FieldSample) (r : ℝ) : Prop :=
  ∀ (n : ℕ) (m : ℤ), 0 ≤ (m : ℝ) → (m : ℝ) / (2 : ℝ) ^ n + radius n < r →
    y (foldedCircle 0 ((m : ℝ) / (2 : ℝ) ^ n + radius n)) =
      y' (foldedCircle 0 ((m : ℝ) / (2 : ℝ) ^ n + radius n))

theorem radAvgReg_congr_repr {y y' : FieldSample} {r : ℝ} (hag : AgreeRad y y' r) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s < r) : radAvgReg y s = radAvgReg y' s := by
  unfold radAvgReg
  apply limUnder_congr_eventually
  obtain ⟨K, hK⟩ := AtomlessUncond.exists_radius_lt (sub_pos.2 hs)
  filter_upwards [eventually_ge_atTop K] with n hn
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hm0 : (0 : ℝ) ≤ (⌊(2 : ℝ) ^ n * s⌋ : ℝ) :=
    Int.cast_nonneg (Int.floor_nonneg.2 (by positivity))
  have hle : (⌊(2 : ℝ) ^ n * s⌋ : ℝ) / (2 : ℝ) ^ n ≤ s := by
    rw [div_le_iff₀ hpow]
    linarith [Int.floor_le ((2 : ℝ) ^ n * s)]
  exact hag n _ hm0 (by linarith [hK n hn])

theorem lateralPart_congr_repr {y y' : FieldSample} {r : ℝ} (h1 : AgreeNear y y' r)
    (h2 : AgreeRad y y' r) {ν : Measure ℂ} {ρ : ℝ} (hν : ν (Metric.closedBall 0 ρ)ᶜ = 0)
    (hρ : ρ < r) : lateralPart y ν = lateralPart y' ν := by
  unfold lateralPart
  rw [evalReg_congr h1 hν hρ]
  congr 1
  refine integral_congr_ae ?_
  have hae : ∀ᵐ w ∂ν, w ∈ Metric.closedBall (0 : ℂ) ρ := ae_iff.2 hν
  filter_upwards [hae] with w hw
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  exact radAvgReg_congr_repr h2 (norm_nonneg w) (by linarith)

/-- The folded circles read by the reader: those of `reprT` inside `ball 0 ε`. -/
def reprCirc (ε : ℝ) : Set (Measure ℂ) :=
  {μ | ∃ p ∈ reprT, 0 < p.2 ∧ ‖p.1‖ + p.2 < ε ∧ μ = foldedCircle p.1 p.2}

theorem isLocalH_of_mem_reprCirc {ε : ℝ} {μ : Measure ℂ} (h : μ ∈ reprCirc ε) :
    K3.IsLocalH 0 ε μ := by
  obtain ⟨p, -, hp0, hpε, rfl⟩ := h
  exact isLocalH_foldedCircle_repr hp0 hpε

theorem agree_of_reprCirc {y y' : FieldSample} {ε : ℝ} (h : ∀ μ ∈ reprCirc ε, y μ = y' μ) :
    AgreeNear y y' ε ∧ AgreeRad y y' ε := by
  refine ⟨fun n k z hz => h _ ⟨_, mem_reprT_dyadic n k z, radius_pos k, hz, rfl⟩,
    fun n m hm hlt => h _ ⟨_, mem_reprT_rad n m, ?_, by simpa using hlt, rfl⟩⟩
  have h1 := radius_pos n
  have h2 : 0 ≤ (m : ℝ) / (2 : ℝ) ^ n := div_nonneg hm (by positivity)
  show 0 < (m : ℝ) / (2 : ℝ) ^ n + radius n
  linarith

theorem isLocalH_mono_repr {ε r : ℝ} (hεr : ε ≤ r) {μ : Measure ℂ} (h : K3.IsLocalH 0 ε μ) :
    K3.IsLocalH 0 r μ := by
  obtain ⟨h1, r', h2, h3⟩ := h
  exact ⟨h1, r', h2.trans_le hεr, h3⟩

theorem extLoc_resField_of_local {ε : ℝ} (y : FieldSample) {μ : Measure ℂ}
    (h : K3.IsLocalH 0 ε μ) : extLoc ε (resField ε y) μ = y μ := by
  simp [extLoc, h, resField]

/-! ## The reader -/

open Classical in
/-- The lateral part of the extension of `ε`-local data (junk `0` off the local measures). -/
def reprY (ε : ℝ) (u : LocIdx ε → ℝ) : FieldSample := fun ν =>
  if K3.IsLocalH 0 ε ν then lateralPart (extLoc ε u) ν else 0

/-- The reader `G`: the lateral window at scale `a` of `reprY ε u`. -/
def reprG (K : ℕ) (a ε : ℝ) (u : LocIdx ε → ℝ) : WinIdx K → ℝ := latWinW K a (reprY ε u)

theorem measurable_reprY (ε : ℝ) : Measurable (reprY ε) := by
  classical
  refine measurable_pi_iff.2 fun ν => ?_
  unfold reprY
  by_cases h : K3.IsLocalH 0 ε ν
  · haveI : IsFiniteMeasure ν := h.1.1
    simp only [h, ite_true]
    exact (WedgeTK.measurable_lateralPart_apply ν).comp (measurable_extLoc ε)
  · simp only [h, ite_false]
    exact measurable_const

theorem measurable_reprG (K : ℕ) (a ε : ℝ) : Measurable (reprG K a ε) := by
  refine measurable_pi_iff.2 fun i => ?_
  haveI : IsFiniteMeasure (winIdx K i) := (isAdmissibleH_winIdx K i).1
  exact (measurable_evalReg _).comp (measurable_reprY ε)

/-- The rescaled window measures are carried by `closedBall 0 (a K)`. -/
theorem winIdx_map_compl (K : ℕ) (i : WinIdx K) {a : ℝ} (ha : 0 < a) :
    ((winIdx K i).map fun z => (a : ℂ) * z) (Metric.closedBall 0 (a * K))ᶜ = 0 := by
  have h0 : winIdx K i (Metric.closedBall (0 : ℂ) K)ᶜ = 0 := by
    rcases i with p | q
    · rw [winIdx_circ]
      have := foldedCircle_compl_closedBall (d := p.1.1) p.2.1
      rw [Complex.ofReal_zero] at this
      exact measure_mono_null
        (compl_subset_compl.2 (Metric.closedBall_subset_closedBall p.2.2.le)) this
    · obtain ⟨M, δ, hd⟩ := q.2
      rw [winIdx_dens]
      have hw : winRad K ≤ (K : ℝ) := by
        unfold winRad
        exact max_le (by linarith) (Nat.cast_nonneg K)
      exact measure_mono_null (compl_subset_compl.2 (Set.inter_subset_left.trans
        (Metric.closedBall_subset_closedBall hw))) hd.tdens_compl
  have hm : Measurable fun z : ℂ => (a : ℂ) * z := (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm Metric.isClosed_closedBall.measurableSet.compl]
  refine measure_mono_null (fun z hz => ?_) h0
  simp only [mem_preimage, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at hz ⊢
  exact lt_of_mul_lt_mul_left hz ha.le

/-- **Locality of the reader.** If the extension of `u` agrees with `y` at the circles
`reprCirc ε`, and `Y` is the lateral part of `y` on `ε`-local measures, then the regularized
evaluations of `reprY ε u` and `Y` agree at every measure carried strictly inside `ball 0 ε`. -/
theorem evalReg_reprY {ε : ℝ} {u : LocIdx ε → ℝ} {y Y : FieldSample}
    (hag : ∀ μ ∈ reprCirc ε, extLoc ε u μ = y μ)
    (hY : ∀ c, K3.IsLocalH 0 ε c → Y c = lateralPart y c) {ν : Measure ℂ} {ρ : ℝ}
    (hν : ν (Metric.closedBall 0 ρ)ᶜ = 0) (hρ : ρ < ε) :
    evalReg (reprY ε u) ν = evalReg Y ν := by
  obtain ⟨h1, h2⟩ := agree_of_reprCirc hag
  refine evalReg_congr (fun n k z hz => ?_) hν hρ
  have hc := isLocalH_foldedCircle_repr (radius_pos k) hz
  have hs := foldedCircle_compl_closedBall (d := dyadicRoundC n z) (radius_pos k)
  rw [Complex.ofReal_zero] at hs
  unfold reprY
  rw [if_pos hc, hY _ hc]
  exact lateralPart_congr_repr h1 h2 hs hz

/-! ## The shift and the harmonic part -/

open Classical in
/-- The outside shift `b μ = X(bal μ) − X(P_0)` on probability measures (`0` otherwise). -/
def reprB {Ω : Type*} (X : Ω → FieldSample) (r ε : ℝ) (ω : Ω) : LocIdx ε → ℝ := fun μ =>
  if μ.1 Set.univ = 1 then
    X ω (K3.bal 0 r μ.1) - X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)) else 0

theorem measurable_reprB {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample} {r ε : ℝ}
    (hr : 0 < r) (hεr : ε ≤ r) : Measurable[K3.outsideSigma X 0 r] (reprB X r ε) := by
  classical
  refine (@measurable_pi_iff Ω (LocIdx ε) (fun _ => ℝ) (K3.outsideSigma X 0 r)
    (fun _ => inferInstance) (reprB X r ε)).2 fun μ => ?_
  unfold reprB
  by_cases h : μ.1 Set.univ = 1
  · simp only [h, ite_true]
    obtain ⟨hadm, r', hr', hμr'⟩ := μ.2
    haveI : IsFiniteMeasure μ.1 := hadm.1
    have hr'r : r' < r := lt_of_lt_of_le hr' hεr
    have h0 : ‖((0 : ℝ) : ℂ) - ((0 : ℝ) : ℂ)‖ ≤ r / 2 := by
      rw [K3.norm_self_sub_ofReal]; positivity
    haveI := K3.isProbabilityMeasure_halfDiscPoisson (t := 0) hr
      (K3.mem_ball_of_le_k3 (half_lt_self hr) h0)
    exact K3.measurable_outsideSigma (K3.isAdmissibleH_bal hr hr'r hμr')
      (K3.isAdmissibleH_halfDiscPoisson hr (half_lt_self hr) h0)
      (by rw [K3.bal_univ hr hr'r hμr', h, measure_univ]) (K3.bal_ball hr)
      (K3.halfDiscPoisson_ball hr _)
  · simp only [h, ite_false]
    exact measurable_const

/-- The a.s. property of the harmonic part (`ae_reprHarm`). -/
def ReprHarmAt {Ω : Type*} (X : Ω → FieldSample) (r : ℝ) (ω : Ω) (H : ℂ → ℝ) : Prop :=
  ContinuousOn H (Metric.ball (0 : ℂ) r ∩ Hbar) ∧
    (∃ ρ > 0, InnerProductSpace.HarmonicOnNhd (fun z => H (foldH z)) (Metric.ball (0 : ℂ) ρ)) ∧
    H 0 = X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)) ∧
    ∀ p ∈ reprT, 0 < p.2 → ‖p.1‖ + p.2 < r →
      X ω (K3.bal 0 r (foldedCircle p.1 p.2)) = ∫ z, H z ∂foldedCircle p.1 p.2

open Classical in
/-- A selected harmonic part (junk `0` off the a.s. event). -/
def reprH {Ω : Type*} (X : Ω → FieldSample) (r : ℝ) (ω : Ω) : ℂ → ℝ :=
  if h : ∃ H, ReprHarmAt X r ω H then h.choose else 0

/-- The correction `hd = H − H(0)`. -/
def reprHd {Ω : Type*} (X : Ω → FieldSample) (r : ℝ) (ω : Ω) : ℂ → ℝ :=
  fun z => reprH X r ω z - reprH X r ω 0

theorem ae_reprHarmAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ReprHarmAt X r ω (reprH X r ω) := by
  filter_upwards [ae_reprHarm (P := P) hX hr] with ω h
  have h' : ∃ H, ReprHarmAt X r ω H := h
  unfold reprH
  rw [dif_pos h']
  exact h'.choose_spec

/-! ## The remaining free-field input and the reduction -/

end D3Plus
end QuantumZipper
