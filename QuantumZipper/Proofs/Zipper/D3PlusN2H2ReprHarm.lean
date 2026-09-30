import QuantumZipper.Proofs.Zipper.D3PlusN2HarmP1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-H2 representation, part 1: the harmonic part at the circles read by the reader

Task N2H2-REPR. The reader `G` of `N2H2WinReprStmt` (`D3PlusN2H2WinCM.lean`) reads its argument
at two countable families of folded circles inside `ball 0 ε`: the dyadic circles
`foldedCircle (dyadicRoundC n z) (radius k)` (read by `evalReg`) and the centred circles
`foldedCircle 0 (dyadicRound n s + radius n)` (read by `radAvgReg`). `d3PlusN2HarmPart_holds`
gives the harmonic part only at the first family; here the same gluing argument is run on the
union `reprT` of both families, and the value of the harmonic part at `0` is identified
(`X(P_0)`, since the Kolmogorov version of `w ↦ X(P_w) − X(P_0)` vanishes at `w = 0` a.s.).

Route: exactly the proof of `d3PlusN2HarmPart_holds` (`D3PlusN2HarmP1.lean`: Markov decomposition
`K3.markov_decomposition`, Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007),
§2.4, applied on the countable family, and gluing of the continuous versions along `rSeq r`),
with the index family enlarged; own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- Centres and radii of the folded circles read by the regularizations near `0`: the dyadic
circles of `evalReg` and the centred circles of `radAvgReg`. -/
def reprT : Set (ℂ × ℝ) :=
  (⋃ n : ℕ, ⋃ k : ℕ, Set.range (dyadicRoundC n) ×ˢ {radius k}) ∪
    ⋃ n : ℕ, Set.range fun m : ℤ => ((0 : ℂ), (m : ℝ) / (2 : ℝ) ^ n + radius n)

theorem reprT_countable : reprT.Countable := by
  refine Set.Countable.union (Set.countable_iUnion fun n => Set.countable_iUnion fun k =>
    (countable_range_dyadicRoundC n).prod (Set.countable_singleton _))
    (Set.countable_iUnion fun n => Set.countable_range _)

theorem mem_reprT_dyadic (n k : ℕ) (z : ℂ) : (dyadicRoundC n z, radius k) ∈ reprT :=
  Or.inl (Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨k, Set.mk_mem_prod (Set.mem_range_self z) rfl⟩⟩)

theorem mem_reprT_rad (n : ℕ) (m : ℤ) :
    ((0 : ℂ), (m : ℝ) / (2 : ℝ) ^ n + radius n) ∈ reprT :=
  Or.inr (Set.mem_iUnion.2 ⟨n, Set.mem_range_self m⟩)

/-- A folded circle strictly inside `ball 0 r` is a local measure of the half-disc. -/
theorem isLocalH_foldedCircle_repr {d : ℂ} {ρ r : ℝ} (hρ : 0 < ρ) (h : ‖d‖ + ρ < r) :
    K3.IsLocalH 0 r (foldedCircle d ρ) :=
  ⟨isAdmissibleH_foldedCircle' d hρ, _, h, foldedCircle_compl_closedBall hρ⟩

section Harm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The Markov decomposition at every circle of `reprT`, a.s. simultaneously. -/
theorem ae_repr_decomp [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ (N : ℕ), ∀ p ∈ reprT, 0 < p.2 → ‖p.1‖ + p.2 ≤ rSeq r N →
      X ω (K3.bal 0 r (foldedCircle p.1 p.2)) =
        (∫ z, K3.harmH X 0 r (rSeq r N) ω z ∂foldedCircle p.1 p.2) +
          X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)) := by
  rw [ae_all_iff]
  intro N
  rw [ae_ball_iff reprT_countable]
  intro p _
  by_cases hp : 0 < p.2 ∧ ‖p.1‖ + p.2 ≤ rSeq r N
  · have hμadm : IsAdmissibleH (foldedCircle p.1 p.2) := isAdmissibleH_foldedCircle' _ hp.1
    have hsupp : foldedCircle p.1 p.2 (Metric.closedBall ((0 : ℝ) : ℂ) (rSeq r N))ᶜ = 0 :=
      measure_mono_null (Set.compl_subset_compl.2 (Metric.closedBall_subset_closedBall hp.2))
        (foldedCircle_compl_closedBall hp.1)
    filter_upwards [K3.markov_decomposition (P := P) hX hr (rSeq_pos hr N) (rSeq_lt hr N)
      hμadm hsupp] with ω hω
    intro _ _
    have hzu : K3.markovZ X 0 r ω (foldedCircle p.1 p.2) =
        X ω (foldedCircle p.1 p.2) - X ω (K3.bal 0 r (foldedCircle p.1 p.2)) := rfl
    rw [hzu, measure_univ, ENNReal.toReal_one, one_mul] at hω
    linarith only [hω]
  · filter_upwards with ω h1 h2
    exact absurd ⟨h1, h2⟩ hp

/-- The continuous version of the harmonic increments vanishes at `0`, a.s. -/
theorem ae_harmH_zero_repr [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (hr'r : r' < r) :
    ∀ᵐ ω ∂P, K3.harmH X 0 r r' ω 0 = 0 := by
  have h0H : (0 : ℂ) ∈ Hbar := by show (0 : ℝ) ≤ (0 : ℂ).im; simp
  have hf : foldH 0 = 0 := by
    have := CircleFubini.foldH_mem_Hbar' 0
    simp [foldH]
  have hret : K3.retr 0 r' 0 = ((0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero]
    exact K3.retr_eq_self h0H (by simp [hr'.le])
  filter_upwards [(K3.kolY_harmIncr_spec (P := P) (t := 0) hX hr hr' hr'r).2 0 h0H] with ω hω
  show K3.kolY (K3.harmIncr X 0 r r') (foldH 0) ω = 0
  rw [hf, hω]
  simp only [K3.harmIncr, hret, sub_self]

/-- **Harmonic part at the reader's circles.** A.s. there is `H`, continuous on
`ball 0 r ∩ Hbar`, with `H ∘ foldH` harmonic near `0`, `H 0 = X(P_0)`, and
`X(bal μ) = ∫ H dμ` at every folded circle of `reprT` inside `ball 0 r`. -/
theorem ae_reprHarm [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∃ H : ℂ → ℝ, ContinuousOn H (Metric.ball (0 : ℂ) r ∩ Hbar) ∧
      (∃ ρ > 0, InnerProductSpace.HarmonicOnNhd (fun z => H (foldH z)) (Metric.ball (0 : ℂ) ρ)) ∧
      H 0 = X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)) ∧
      ∀ p ∈ reprT, 0 < p.2 → ‖p.1‖ + p.2 < r →
        X ω (K3.bal 0 r (foldedCircle p.1 p.2)) = ∫ z, H z ∂foldedCircle p.1 p.2 := by
  have hcons : ∀ᵐ ω ∂P, ∀ n m : ℕ, n ≤ m → ∀ z ∈ Metric.closedBall (0 : ℂ) (rSeq r n),
      K3.harmH X 0 r (rSeq r n) ω z = K3.harmH X 0 r (rSeq r m) ω z := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    by_cases hnm : n ≤ m
    · filter_upwards [ae_harmH_rSeq_consistent (P := P) hX hr hnm] with ω h
      exact fun _ z hz => h (x := z) hz
    · filter_upwards with ω h
      exact absurd h hnm
  filter_upwards [hcons, ae_repr_decomp (P := P) hX hr,
    K3.ae_harmonicOnNhd_harmH (P := P) (t := 0) hX hr (rSeq_pos hr 0) (rSeq_lt hr 0),
    ae_harmH_zero_repr (P := P) hX hr (rSeq_pos hr 0) (rSeq_lt hr 0)]
    with ω hconsω hdecω hharmω hzeroω
  set cω : ℝ := X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)) with hcω
  have hlim : ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ rSeq r N →
      limUnder atTop (fun m => K3.harmH X 0 r (rSeq r m) ω z) =
        K3.harmH X 0 r (rSeq r N) ω z := by
    intro N z hz
    have hev : (fun _ : ℕ => K3.harmH X 0 r (rSeq r N) ω z) =ᶠ[atTop]
        (fun m => K3.harmH X 0 r (rSeq r m) ω z) := by
      filter_upwards [eventually_ge_atTop N] with m hm
      exact hconsω N m hm z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
    exact (tendsto_const_nhds.congr' hev).limUnder_eq
  refine ⟨fun z => limUnder atTop (fun m => K3.harmH X 0 r (rSeq r m) ω z) + cω, ?_, ?_, ?_, ?_⟩
  · intro z₀ hz₀
    have hz₀' : ‖z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz₀.1
    obtain ⟨N, hN⟩ := exists_rSeq_gt hr hz₀'
    have hball : z₀ ∈ Metric.ball (0 : ℂ) (rSeq r N) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hN
    have hev : (fun z => limUnder atTop (fun m => K3.harmH X 0 r (rSeq r m) ω z) + cω)
        =ᶠ[𝓝 z₀] (fun z => K3.harmH X 0 r (rSeq r N) ω z + cω) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hball] with z hz
      rw [hlim N z (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz))]
    exact ((K3.continuous_harmH (P := P) (t := 0) hX hr (rSeq_pos hr N) (rSeq_lt hr N)
      ω).add continuous_const).continuousAt.congr_of_eventuallyEq hev |>.continuousWithinAt
  · refine ⟨rSeq r 0, rSeq_pos hr 0, ?_⟩
    intro x hx
    have hev : (fun z => limUnder atTop (fun m => K3.harmH X 0 r (rSeq r m) ω (foldH z)) + cω)
        =ᶠ[𝓝 x] (fun z => K3.harmH X 0 r (rSeq r 0) ω z + cω) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
      have hz' : ‖z‖ ≤ rSeq r 0 :=
        le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
      rw [congrArg (limUnder atTop) (funext fun m => harmH_foldH X 0 r (rSeq r m) ω z),
        hlim 0 z hz']
    rw [InnerProductSpace.harmonicAt_congr_nhds hev]
    exact (hharmω x hx).add (InnerProductSpace.harmonicAt_const cω)
  · show limUnder atTop (fun m => K3.harmH X 0 r (rSeq r m) ω 0) + cω = cω
    rw [hlim 0 0 (by simpa using (rSeq_pos hr 0).le), hzeroω, zero_add]
  · intro p hp hp0 hpr
    obtain ⟨N, hN⟩ := exists_rSeq_gt hr hpr
    have hkey := hdecω N p hp hp0 hN.le
    have hsupp := foldedCircle_compl_closedBall (d := p.1) hp0
    rw [Complex.ofReal_zero] at hsupp
    have hae : (fun z' => limUnder atTop (fun m => K3.harmH X 0 r (rSeq r m) ω z') + cω)
        =ᵐ[foldedCircle p.1 p.2] fun z' => K3.harmH X 0 r (rSeq r N) ω z' + cω := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsupp] with z' hz'
      have hz'' : ‖z'‖ ≤ rSeq r N :=
        le_trans (by simpa [Metric.mem_closedBall, dist_eq_norm] using (not_not.1 hz')) hN.le
      rw [hlim N z' hz'']
    have hint : Integrable (fun z' => K3.harmH X 0 r (rSeq r N) ω z')
        (foldedCircle p.1 p.2) :=
      integrable_of_admCorr (r := r) le_rfl
        ((K3.continuous_harmH (P := P) (t := 0) hX hr (rSeq_pos hr N) (rSeq_lt hr N)
          ω).continuousOn) ⟨_, isLocalH_foldedCircle_repr hp0 hpr⟩
    rw [integral_congr_ae hae, integral_add hint (integrable_const cω), integral_const,
      Measure.real, measure_univ, ENNReal.toReal_one, one_smul, hkey]

end Harm

end D3Plus
end QuantumZipper
