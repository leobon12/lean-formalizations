import QuantumZipper.Proofs.Zipper.D3PlusN2RRead
import QuantumZipper.Proofs.Zipper.D3PlusN2H3Split

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-H3 on the restricted index (Decision D36)

Task D36-IMPL, step (4). The window data on the restricted index `WinIdx K` (`D3PlusN2RIdx.lean`,
D36) are functions `WinIdx K → ℝ`; the heart decomposition of the model's window data
(`D3PlusN2HeartStmt.lean`: `heartPsi`, `heartF`, `heartW` on `LocIdx K`) is restated here on the
restricted index:

* `heartPsiW Q K p`, `heartFW γ r K`, `heartWW γ K`: the radial part and the two heart maps on
  `WinIdx K`, reading the window measures `winIdx K i` exactly as `heartF`/`heartW` read `μ.1`;
* `measurable_heartPsiW` (`= measurable_heartPsi` at the restricted measures),
  `measurable_latWinW_joint`, `measurable_heartFW`, `measurable_heartWW`;
* **H3'** `N2HModelDecompWinStmt`: a.s. on `{Tc ≥ log K + 1}`, the restricted window datum of the
  embedded model is `heartFW` of the (lateral data, radial data) — the D36 form of
  `N2HModelDecompStmt`;
* **H3'-SPLIT** `N2H3SplitWinStmt`: the lateral/radial splitting of the regularized evaluation of
  the model field at the rescaled restricted measures (D36 form of `N2H3SplitStmt`).

The reduction `n2HModelDecompWin_of_split : N2H3SplitWinStmt → N2HModelDecompWinStmt` is the
bookkeeping of `n2HModelDecomp_of_split` (`D3PlusN2H3Split.lean`) with the local-measure witnesses
of `LocIdx K` replaced by those of the restricted index (`(isLocalH_winIdx K hK i).2`: the
circles have `‖d‖ + ρ < K`, the densities are carried by `closedBall 0 (winRad K)`,
`winRad K < K`). Nothing else changes: the radial time shift `n2_radial_pointwise`, the continuity
of the radial path and the integrability arguments are index-free.

The analytic content of H3'-SPLIT is the same as H3-SPLIT (regularity of the local field `Z` at
the rescaled measure); on the restricted index the a.s. convergence of the regularization is
available (`winRegFam_winIdx`, `regAt_winIdx`), so H3'-SPLIT is the D36 form in which the node is
expected to be provable — the proof is not part of this task (open node).

Sources: Duplantier–Miller–Sheffield, arXiv:1409.7055, pp. 77–78; Sheffield, arXiv:1012.4797,
p. 25.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## The heart maps on the restricted index -/

/-- The radial part of the restricted window datum, read from a path through `extP`. -/
def heartPsiW (Q : ℝ) (K : ℕ) (p : ℝ → ℝ) : WinIdx K → ℝ :=
  fun i => ∫ z, (Q * (-Real.log ‖z‖) + WedgeLaw.extP p (-Real.log ‖z‖)) ∂(winIdx K i)

/-- The model's restricted window data as a function of (lateral data, radial data). -/
def heartFW (γ r : ℝ) (K : ℕ) (p : FieldSample × (ℝ × (ℝ → ℝ))) : WinIdx K → ℝ :=
  latWinW K (r * Real.exp (-p.2.1)) p.1 + heartPsiW (Qc γ) K p.2.2

/-- The wedge's restricted window data as a function of (lateral window, radial path). -/
def heartWW (γ : ℝ) (K : ℕ) (p : (WinIdx K → ℝ) × (ℝ → ℝ)) : WinIdx K → ℝ :=
  p.1 + heartPsiW (Qc γ) K p.2

theorem measurable_heartPsiW (Q : ℝ) (K : ℕ) : Measurable (heartPsiW Q K) := by
  refine measurable_pi_iff.2 fun i => ?_
  haveI : IsFiniteMeasure (winIdx K i) := (isAdmissibleH_winIdx K i).1
  have hlog : Measurable fun q : (ℝ → ℝ) × ℂ => -Real.log ‖q.2‖ :=
    (Real.measurable_log.comp (measurable_norm.comp measurable_snd)).neg
  have hf : Measurable fun q : (ℝ → ℝ) × ℂ =>
      Q * (-Real.log ‖q.2‖) + WedgeLaw.extP q.1 (-Real.log ‖q.2‖) :=
    (measurable_const.mul hlog).add (WedgeLaw.measurable_extP.comp (measurable_fst.prodMk hlog))
  exact (StronglyMeasurable.integral_prod_right' (ν := winIdx K i) hf.stronglyMeasurable).measurable

/-- Joint measurability of the restricted lateral window in the scale and the field (from the
full-index `measurable_latWin_joint` at the `LocIdx` element of the restricted index). -/
theorem measurable_latWinW_joint (K : ℕ) (hK : 0 < K) :
    Measurable fun p : ℝ × FieldSample => latWinW K p.1 p.2 := by
  refine Measurable.of_eval fun i => ?_
  show Measurable fun p : ℝ × FieldSample =>
    latWin K p.1 p.2 (⟨winIdx K i, isLocalH_winIdx K hK i⟩ : LocIdx (K : ℝ))
  exact (measurable_pi_apply (⟨winIdx K i, isLocalH_winIdx K hK i⟩ : LocIdx (K : ℝ))).comp
    (measurable_latWin_joint K)

theorem measurable_heartFW (γ r : ℝ) (K : ℕ) (hK : 0 < K) : Measurable (heartFW γ r K) := by
  have ha : Measurable fun p : FieldSample × (ℝ × (ℝ → ℝ)) => r * Real.exp (-p.2.1) :=
    measurable_const.mul (Real.measurable_exp.comp (measurable_fst.comp measurable_snd).neg)
  exact ((measurable_latWinW_joint K hK).comp (ha.prodMk measurable_fst)).add
    ((measurable_heartPsiW _ K).comp (measurable_snd.comp measurable_snd))

theorem measurable_heartWW (γ : ℝ) (K : ℕ) : Measurable (heartWW γ K) :=
  measurable_fst.add ((measurable_heartPsiW _ K).comp measurable_snd)

/-! ## The restricted nodes -/

/-- **N2-H3-SPLIT'** (restricted index, D36 form of `N2H3SplitStmt`): the lateral/radial splitting
of the regularized evaluation of the model field at the rescaled restricted window measure. -/
def N2H3SplitWinStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), 0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P →
    ∀ K : ℕ, 0 < K → ∀ L, 0 < n2Lev γ α L r → ∀ i : WinIdx K, ∀ᵐ ω ∂P,
      Real.log K + 1 ≤ ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω →
      Integrable (fun z => radAvgReg (locZField X r ω) (n2EmbScale γ α L r X ω * ‖z‖))
        (winIdx K i) ∧
      evalReg (n2Model γ α L r X ω) ((winIdx K i).map fun z => (n2EmbScale γ α L r X ω : ℂ) * z) =
        evalReg (n2LatY X r ω) ((winIdx K i).map fun z => (n2EmbScale γ α L r X ω : ℂ) * z) +
        ∫ z, (radAvgReg (locZField X r ω) (n2EmbScale γ α L r X ω * ‖z‖) +
          α * (-Real.log (n2EmbScale γ α L r X ω * ‖z‖)) + L / γ) ∂(winIdx K i)

/-- **N2-H3'** (restricted index, D36 form of `N2HModelDecompStmt`): for each restricted window
measure, a.s. on `{Tc ≥ log K + 1}`, the restricted window datum of the embedded model is
`heartFW` of (lateral data, radial data). -/
def N2HModelDecompWinStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), 0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P →
    ∀ K : ℕ, 0 < K → ∀ L, 0 < n2Lev γ α L r → ∀ i : WinIdx K, ∀ᵐ ω ∂P,
      Real.log K + 1 ≤ ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω →
      resFieldW K (n2Emb γ α L r X ω) i =
        heartFW γ r K (n2LatY X r ω, n2RadR γ α L r K X ω) i

/-- The support condition of the restricted index: `winIdx K i` is carried by a ball of radius
`r' < K` (the circles have `‖d‖ + ρ < K`, the densities `closedBall 0 (winRad K)`,
`winRad K < K`). -/
theorem winIdx_support (K : ℕ) (hK : 0 < K) (i : WinIdx K) :
    ∃ r' < (K : ℝ), winIdx K i (Metric.closedBall (0 : ℂ) r')ᶜ = 0 :=
  (isLocalH_winIdx K hK i).2

/-- **N2-H3' from the splitting sub-node on the restricted index** (bookkeeping copy of
`n2HModelDecomp_of_split`, with the local-measure witnesses of `LocIdx K` replaced by
`winIdx_support`). -/
theorem n2HModelDecompWin_of_split (hS : N2H3SplitWinStmt) : N2HModelDecompWinStmt := by
  intro γ α r Ω _ P _ X hγ hγ2 hα hr hX K hK L hL i
  filter_upwards [hS γ α r P X hγ hγ2 hα hr hX K hK L hL i,
    (isBrownianReal_zRadB hX hr).cont] with ω hω hc hT
  obtain ⟨hint, hsplit⟩ := hω hT
  set a := n2EmbScale γ α L r X ω with hadef
  have ha : 0 < a := mul_pos hr (Real.exp_pos _)
  haveI : IsFiniteMeasure (winIdx K i) := (isAdmissibleH_winIdx K i).1
  have hLHS : resFieldW K (n2Emb γ α L r X ω) i =
      evalReg (n2Model γ α L r X ω) ((winIdx K i).map fun z => (a : ℂ) * z) +
        Qc γ * (((winIdx K i) Set.univ).toReal * Real.log ‖(a : ℂ)‖) :=
    rescale_apply_eq _ _ _ _
  have hRHS : heartFW γ r K (n2LatY X r ω, n2RadR γ α L r K X ω) i =
      evalReg (n2LatY X r ω) ((winIdx K i).map fun z => (a : ℂ) * z) +
        ∫ z, (Qc γ * (-Real.log ‖z‖) +
          WedgeLaw.extP (n2RadR γ α L r K X ω).2 (-Real.log ‖z‖)) ∂(winIdx K i) := rfl
  rw [hLHS, hRHS, WedgeLaw.extP_of_continuous (continuous_n2RadR_snd K hc)]
  -- the radial integrand, `winIdx K i`-a.e.
  obtain ⟨r', hr', h0⟩ := winIdx_support K hK i
  have hball : ∀ᵐ z ∂(winIdx K i), z ∈ Metric.closedBall (0 : ℂ) r' :=
    (ae_iff (μ := winIdx K i) (p := fun z => z ∈ Metric.closedBall (0 : ℂ) r')).2
      (by simpa only [Set.compl_def] using h0)
  have hne : ∀ᵐ z ∂(winIdx K i), z ≠ 0 := by
    rw [ae_iff]
    simpa only [ne_eq, not_not, ofPred_eq_eq_singleton] using
      GFFExist.gffEx_measure_singleton (isAdmissibleH_winIdx K i) 0
  set f : ℂ → ℝ := fun z => radAvgReg (locZField X r ω) (a * ‖z‖) +
    α * (-Real.log (a * ‖z‖)) + L / γ with hf
  have hae : ∀ᵐ z ∂(winIdx K i), Qc γ * (-Real.log ‖z‖) +
      (n2RadR γ α L r K X ω).2 (-Real.log ‖z‖) = f z + Qc γ * Real.log a := by
    filter_upwards [hball, hne] with z hz hz0
    have hzK : ‖z‖ ≤ K := by
      rw [Metric.mem_closedBall, dist_zero_right] at hz; linarith
    exact n2_radial_pointwise hK hr hT hz0 hzK
  have hlogint : Integrable (fun z => Real.log (a * ‖z‖)) (winIdx K i) := by
    refine ((integrable_const (Real.log a)).add
      (WedgeRes.integrable_log_norm_adm (isAdmissibleH_winIdx K i))).congr ?_
    filter_upwards [hne] with z hz0
    rw [Real.log_mul ha.ne' (norm_pos_iff.2 hz0).ne']
    rfl
  have hfint : Integrable f (winIdx K i) :=
    (hint.add (hlogint.neg.const_mul α)).add (integrable_const _)
  rw [integral_congr_ae hae, integral_add hfint (integrable_const _), integral_const, hsplit,
    Complex.norm_real, Real.norm_of_nonneg ha.le, smul_eq_mul, Measure.real]
  ring

end D3Plus
end QuantumZipper
