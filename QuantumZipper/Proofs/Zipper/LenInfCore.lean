import QuantumZipper.Proofs.Zipper.E6InReduce
import QuantumZipper.Proofs.Zipper.HitScaleZip
import QuantumZipper.Proofs.Zipper.LocHitScaleRead
import QuantumZipper.Proofs.Zipper.JointModAssembly
import QuantumZipper.Proofs.Thm18.G4CapLen
import QuantumZipper.Proofs.Thm18.G4UnzipGoodField
import QuantumZipper.Proofs.Loewner.Algebra
import QuantumZipper.Proofs.Section5.Prop16LocalRule
import QuantumZipper.Proofs.Zipper.UnifD33Close
import QuantumZipper.Proofs.Zipper.FlowRegG4
import QuantumZipper.Proofs.Zipper.F2LocalScale
import QuantumZipper.Proofs.LQG.WedgeBdryInfABasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LEN-INF: infinite total left length of the `Γ⁰` sample (`E6.CfgLenInfStmt`)

Theorem 1.3, nodes E6/F1. Sheffield (arXiv:1012.4797, §5.4, pp. 70–72) uses without proof that
the left side of `η[0,t]` has quantum length tending to `∞` as `t → ∞`. For `P_*` samples this is
`E6.pStarLenInfStmt_of` (scale invariance of the wedge). The `Γ⁰` configuration
`𝒵 = (𝔥₀ + X, √κ B)` is scale invariant only *modulo constants*, so the wedge argument
(`law(n S) = law(S)`) does not apply literally; the constant carries a drift instead.

**Argument (own; no published proof found — Sheffield uses the fact without proof).** Write
`S = sup_{t ≥ 0} L⁻_t(𝒵)`. For `a ≥ 1` rescale by `z ↦ a z` (Sheffield §5.1: quantum lengths are
invariant under `h ↦ h(a·) + Q log a`; Brownian scaling of the driver), and normalize the rescaled
free field to have unit-semicircle average `0`. Since `𝔥₀(a z) = 𝔥₀(z) + (2/γ) log a` and adding
a constant `C` multiplies lengths by `e^{γC/2}`,
`S = e^{c_a} S_a`, `c_a = log a + (γ/2) (X(ρ_a) + Q log a)` (`ρ_a` the semicircle of radius `a`),
where `S_a` is the total left length of a *normalized* `Γ⁰` sample, whose law does not depend on
`a`. Since `X(ρ_a) − X(ρ_1)` is centered with variance `2 log a` (the semicircle-average process of
the free boundary GFF), `c_a → ∞` in probability; with `S_a > 0` a.s. this forces `S = ∞` a.s.:
`P(S ≤ M) ≤ P(c_a ≤ K) + P(S_1 ≤ M e^{-K})` for all `a, K` (`ae_eq_top_of_drift`).

* `ae_eq_top_of_drift` (deterministic measure theory, own elementary);
* `CfgLenDriftStmt` and `cfgLenInfStmt_of_drift`: the abstract drift form;
* `semicircleDriftStmt_holds`: the drift of the semicircle averages (Chebyshev with the
  variance `2 log a`, `WedgeBdry.tendsto_prob_drift`);
* `cfgLenDriftStmt_of_parts`, `cfgLenInfStmt_of_parts`, `flowGoodAllStmt_of_lenInfParts`: from two
  open named inputs `CfgLenScaleNormStmt` (scaling + normalization identity, Sheffield §5.1) and
  `CfgNormLenLawStmt` (the law of the total length of a normalized `Γ⁰` sample is universal), plus
  UW/UA (positivity of the total length).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open B2 E1 D3Plus

/-! ## The zero–infinity lemma with drift -/

/-- **Zero–infinity with drift.** If `T > 0` a.s. and, for every level `K` and `ε > 0`,
`S = e^{c} S'` a.s. with `S'` distributed as `T` and `P(c ≤ K) ≤ ε`, then `S = ∞` a.s. -/
theorem ae_eq_top_of_drift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S T : Ω → ℝ≥0∞} (hT : AEMeasurable T P) (hT0 : ∀ᵐ ω ∂P, 0 < T ω)
    (h : ∀ (K : ℝ) (ε : ℝ≥0∞), 0 < ε → ∃ (c : Ω → ℝ) (S' : Ω → ℝ≥0∞), AEMeasurable S' P ∧
      P.map S' = P.map T ∧ (∀ᵐ ω ∂P, S ω = ENNReal.ofReal (Real.exp (c ω)) * S' ω) ∧
      P {ω | c ω ≤ K} ≤ ε) :
    ∀ᵐ ω ∂P, S ω = ⊤ := by
  have hstep : ∀ (M : ℝ≥0∞) (n : ℕ),
      P {ω | S ω ≤ M} ≤ P.map T (Iic (M / ((n : ℝ≥0∞) + 1))) := by
    intro M n
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨c, S', hS', hlaw, heq, hc⟩ :=
      h (Real.log ((n : ℝ) + 1)) ε (by exact_mod_cast hε)
    have hsub : {ω | S ω ≤ M} ⊆
        {ω | ¬ (S ω = ENNReal.ofReal (Real.exp (c ω)) * S' ω)} ∪
          {ω | c ω ≤ Real.log ((n : ℝ) + 1)} ∪ S' ⁻¹' Iic (M / ((n : ℝ≥0∞) + 1)) := by
      intro ω hω
      by_cases he : S ω = ENNReal.ofReal (Real.exp (c ω)) * S' ω
      · by_cases hc' : c ω ≤ Real.log ((n : ℝ) + 1)
        · exact Or.inl (Or.inr hc')
        · right
          replace hc' := not_le.1 hc'
          have hlt : (n : ℝ) + 1 < Real.exp (c ω) := by
            rw [← Real.exp_log (by positivity : (0 : ℝ) < n + 1)]
            exact Real.exp_lt_exp.2 hc'
          have hle : (n : ℝ≥0∞) + 1 ≤ ENNReal.ofReal (Real.exp (c ω)) := by
            have e1 : ENNReal.ofReal ((n : ℝ) + 1) = (n : ℝ≥0∞) + 1 := by
              rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
                ENNReal.ofReal_one]
            rw [← e1]
            exact ENNReal.ofReal_le_ofReal hlt.le
          show S' ω ≤ M / ((n : ℝ≥0∞) + 1)
          rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
          calc S' ω * ((n : ℝ≥0∞) + 1) ≤ S' ω * ENNReal.ofReal (Real.exp (c ω)) := by
                gcongr
            _ = S ω := by rw [he, mul_comm]
            _ ≤ M := hω
      · exact Or.inl (Or.inl he)
    have hnull : P {ω | ¬ (S ω = ENNReal.ofReal (Real.exp (c ω)) * S' ω)} = 0 := ae_iff.1 heq
    have hmap : P (S' ⁻¹' Iic (M / ((n : ℝ≥0∞) + 1))) =
        P.map T (Iic (M / ((n : ℝ≥0∞) + 1))) := by
      rw [← Measure.map_apply_of_aemeasurable hS' measurableSet_Iic, hlaw]
    calc P {ω | S ω ≤ M}
        ≤ P ({ω | ¬ (S ω = ENNReal.ofReal (Real.exp (c ω)) * S' ω)} ∪
          {ω | c ω ≤ Real.log ((n : ℝ) + 1)} ∪ S' ⁻¹' Iic (M / ((n : ℝ≥0∞) + 1))) :=
          measure_mono hsub
      _ ≤ P {ω | ¬ (S ω = ENNReal.ofReal (Real.exp (c ω)) * S' ω)} +
          P {ω | c ω ≤ Real.log ((n : ℝ) + 1)} + P (S' ⁻¹' Iic (M / ((n : ℝ≥0∞) + 1))) :=
          (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
      _ ≤ 0 + ε + P.map T (Iic (M / ((n : ℝ≥0∞) + 1))) := by
          rw [hnull, hmap]
          gcongr
      _ = P.map T (Iic (M / ((n : ℝ≥0∞) + 1))) + ε := by rw [zero_add, add_comm]
  have hzero : ∀ M : ℝ≥0∞, M ≠ ⊤ → P {ω | S ω ≤ M} = 0 := by
    intro M hM
    have hanti : Antitone fun n : ℕ => Iic (M / ((n : ℝ≥0∞) + 1)) := by
      intro i j hij
      refine Iic_subset_Iic.2 (ENNReal.div_le_div_left ?_ M)
      gcongr
    have hlim := tendsto_measure_iInter_atTop (μ := P.map T)
      (s := fun n : ℕ => Iic (M / ((n : ℝ≥0∞) + 1)))
      (fun n => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    have hle := ge_of_tendsto' hlim fun n => hstep M n
    have htend : Tendsto (fun n : ℕ => M / ((n : ℝ≥0∞) + 1)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ≥0∞))⁻¹) atTop (𝓝 0) :=
        ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr hM)
      rw [mul_zero] at h2
      refine h2.congr fun n => ?_
      rw [div_eq_mul_inv, Nat.cast_succ]
    have hsub : (⋂ n : ℕ, Iic (M / ((n : ℝ≥0∞) + 1))) ⊆ Iic 0 := by
      intro x hx
      exact ge_of_tendsto' htend fun n => mem_iInter.1 hx n
    have hT0' : P.map T (Iic 0) = 0 := by
      rw [Measure.map_apply_of_aemeasurable hT measurableSet_Iic]
      refine measure_mono_null (fun ω (hω : T ω ≤ 0) => ?_) (ae_iff.1 hT0)
      exact fun h => (not_lt.2 hω) h
    exact le_antisymm (hle.trans ((measure_mono hsub).trans hT0'.le)) zero_le
  have hall : ∀ m : ℕ, ∀ᵐ ω ∂P, ¬ S ω ≤ m := by
    intro m
    rw [ae_iff]
    simpa only [not_not] using hzero m (ENNReal.natCast_ne_top m)
  filter_upwards [ae_all_iff.2 hall] with ω hω
  by_contra hne
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hne
  exact hω m hm.le

/-! ## The drift form of the `Γ⁰` node -/

variable {Ω : Type} [MeasurableSpace Ω]

/-! ## The drift form from scaling, a universal law and the semicircle drift -/

/-- The drift exponent `c_a(x) = log a + (γ/2) (x(ρ_a) + Q log a)`, `γ = √κ`, where
`ρ_a = ρ_1.map (a ·)` is the unit mass on the semicircle of radius `a` about `0`
(`ρ_1 = InfMass.fc01 = foldedCircle 0 1`); `x(ρ_a) + Q log a` is `(rescale x Q a)(ρ_1)`. -/
def driftC (κ a : ℝ) (x : FieldSample) : ℝ :=
  Real.log a + Real.sqrt κ / 2 *
    (x (InfMass.fc01.map fun u => (a : ℂ) * u) + Qc (Real.sqrt κ) * Real.log a)

/-- **Drift of the semicircle averages**: `c_a(X) → ∞` in probability as `a → ∞` (along
`a = 2ⁿ`). `X(ρ_a) − X(ρ_1)` is centered with variance `2 log a` (the semicircle-average process of
the free boundary GFF; `InfMass.kernelCov2_dPair`), while the drift is `(1 + γQ/2) log a`;
Chebyshev (`WedgeBdry.tendsto_prob_drift`). Proved below (`semicircleDriftStmt_holds`). -/
def SemicircleDriftStmt (κ : ℝ) : Prop :=
  0 < κ →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → FieldSample),
    IsFreeGFFModConstH X P → ∀ (K : ℝ) (ε : ℝ≥0∞), 0 < ε →
      ∃ a : ℝ, 1 ≤ a ∧ P {ω | driftC κ a (X ω) ≤ K} ≤ ε

/-- A real random variable is tight from below: `P(Y ≤ −m) → 0`. -/
theorem tendsto_prob_le_neg_nat {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}
    [IsProbabilityMeasure P] {Y : Ω' → ℝ} (hY : Measurable Y) :
    Tendsto (fun m : ℕ => P {ω | Y ω ≤ -(m : ℝ)}) atTop (𝓝 0) := by
  have hanti : Antitone fun m : ℕ => {ω | Y ω ≤ -(m : ℝ)} := by
    intro i j hij ω (hω : Y ω ≤ -(j : ℝ))
    show Y ω ≤ -(i : ℝ)
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have h := tendsto_measure_iInter_atTop (μ := P) (s := fun m : ℕ => {ω | Y ω ≤ -(m : ℝ)})
    (fun m => (measurableSet_le hY measurable_const).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ m : ℕ, {ω | Y ω ≤ -(m : ℝ)}) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
    obtain ⟨m, hm⟩ := exists_nat_gt (-Y ω)
    have := mem_iInter.1 hω m
    simp only [mem_ofPred_eq] at this
    linarith
  rw [hempty, measure_empty] at h
  exact h

/-- **The semicircle drift holds.** -/
theorem semicircleDriftStmt_holds (κ : ℝ) : SemicircleDriftStmt κ := by
  intro hκ Ω _ P _ X hX K ε hε
  set γ := Real.sqrt κ with hγdef
  have hγ : 0 < γ := Real.sqrt_pos.2 hκ
  have hQ : 0 < Qc γ := by unfold Qc; positivity
  set q : ℝ := 2 / γ + Qc γ with hqdef
  have hq : 0 < q := by positivity
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨m, hm⟩ := ((tendsto_prob_le_neg_nat (P := P) (hX.measurable_coord InfMass.fc01)).eventually
    (ge_mem_nhds hε2)).exists
  have hdr := WedgeBdry.tendsto_prob_drift (P := P) hX hq (2 * K / γ + m)
  obtain ⟨n, hn⟩ := (hdr.eventually (ge_mem_nhds hε2)).exists
  refine ⟨(2 : ℝ) ^ n, one_le_pow₀ one_le_two, ?_⟩
  have hsub : {ω | driftC κ ((2 : ℝ) ^ n) (X ω) ≤ K} ⊆
      {ω | X ω InfMass.fc01 ≤ -(m : ℝ)} ∪
        {ω | X ω (InfMass.fc01.map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) - X ω InfMass.fc01 +
          q * (n * Real.log 2) ≤ 2 * K / γ + m} := by
    intro ω hω
    simp only [mem_ofPred_eq, driftC, Real.log_pow] at hω
    by_cases h1 : X ω InfMass.fc01 ≤ -(m : ℝ)
    · exact Or.inl h1
    · right
      simp only [mem_ofPred_eq]
      replace h1 := not_le.1 h1
      rw [← hγdef] at hω
      have hK : γ * (X ω (InfMass.fc01.map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) +
          Qc γ * (n * Real.log 2)) + 2 * (n * Real.log 2) ≤ 2 * K := by
        push_cast at hω ⊢
        linarith
      have hqγ : q * γ = 2 + Qc γ * γ := by rw [hqdef, add_mul, div_mul_cancel₀ _ hγ.ne']
      have key : ∀ Y : ℝ, γ * (Y + Qc γ * (n * Real.log 2)) + 2 * (n * Real.log 2) ≤ 2 * K →
          Y + q * (n * Real.log 2) ≤ 2 * K / γ := fun Y hY => by
        rw [le_div_iff₀ hγ]
        linear_combination hY + (n * Real.log 2) * hqγ
      have := key _ hK
      linarith
  calc P {ω | driftC κ ((2 : ℝ) ^ n) (X ω) ≤ K}
      ≤ P {ω | X ω InfMass.fc01 ≤ -(m : ℝ)} +
        P {ω | X ω (InfMass.fc01.map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) - X ω InfMass.fc01 +
          q * (n * Real.log 2) ≤ 2 * K / γ + m} := (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ε / 2 + ε / 2 := add_le_add hm hn
    _ = ε := ENNReal.add_halves ε

end QuantumZipper.E6
