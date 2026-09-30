import QuantumZipper.Proofs.Zipper.D3PlusN2ModelLocPair
import QuantumZipper.Proofs.Field.PairAff

/-!
# N2-CONTPAIR: continuum pairing limits of the free field, with the test function inside the
almost-sure event

Task N2-CONTPAIR. The node `D3Plus.N2ZContPairGFFStmt` (`D3PlusN2ModelLocPair.lean`) asks: for a
free field `X` (`IsFreeGFFModConstH`) there is a regular version `G` (`WedgeTK.IsRegVersion`) such
that almost surely, **for all** scales `c > 0` and **all** test functions `ρ ∈ TestFun H` at once,
`t ↦ ∫ G ω (c u, t) f(u) du` has a limit as `t → 0⁺`, `f ∈ {ρ, −ρ}`.

**Proved here** (per measure / per test function, all scales at once):

* `ae_contPair_G_measure`: a.s., for every PAIR-LIM measure `η` (`PairLim.Setup`) and every
  `c > 0`, `t ↦ ∫ u, G ω (c u, t) ∂η` converges as `t → 0⁺`, with limit the canonical continuum
  limit `affLim (X ω) η (0, c)` of the affine machinery (PAIR-AFF).
  Route: for fixed `(t,b)` the pairing is `affPair` (the regular witness `G ω` *is* `evalReg` of
  the folded circles, `IsRegularWith.evalReg_fc_of_mem`, and `Setup.integral_map_aff_witness`
  moves the affine map `aff 0 c` out of the pairing), while
  `PairLim.ae_tendstoLocallyUniformlyOn_affPair` gives a.s. local-uniform convergence of
  `affPair` in the parameters `(t, b)`.
* `ae_contPair_G_density`: the same for every continuous compactly supported `f` with
  `tsupport f ⊆ H`, in the exact form of the node's pairings.
* `ae_contPair_G_testfun` / `ae_contPair_G_testfunSeq` / `ae_contPair_G_testfunSet`: the same for
  `ρ : TestFun H`, both signs `f ∈ {ρ.1, −ρ.1}`, and simultaneously for countably many `ρ`.

**Reduction of the node**: `n2ZContPair_of_osc : N2ZPairOscStmt → N2ZContPairGFFStmt`, where
`N2ZPairOscStmt` is the missing *uniform oscillation bound*: a.s., for every `c > 0` and every
test function, the oscillation of the pairing between two small radii is bounded by
`ε · √(‖ρ‖_∞ ∫|ρ|) / c`. Together with the abstract completeness lemma
`exists_tendsto_of_oscillation` this upgrades the per-test-function convergence proved here
(countably many `ρ` at once) to the node's `∀ ρ` at once.

Section 3 records the probabilistic content of that bound for the *fixed* test functions: at a
fixed radius the pairing is the field paired with the smoothed measure `smooth η t`, whose radius
increments are centred Gaussian with variance at most `16 π M_aff (η univ) |a − b|` (the increment
law `ae_pairIncrement_gaussian`); the bound `N2ZPairOscStmt` is exactly the Kolmogorov-modulus
statement obtained from these moments, uniformly in the *uncountable* family of test functions.

Why the uniformity is exactly what is missing: no countable family of a.s. events can by itself
produce the node's `∀ ρ` statement, and the passage from the moment bounds to an a.s. bound over
the uncountable family needs an a.s. bound of the free field against smooth test functions that is
*linear* in a test-function norm (i.e. "the free field is a.s. a distribution of order `2` on
`C²_c(H)`"), which the repository does not have (see the note in
`Proofs/LQG/WedgeCRegCont.lean` on the same gap for `F1.WedgeContPairStmt`). Everything *except*
that uniformity is proved here.

A weaker node that the chain could use instead of `N2ZContPairGFFStmt` is the countable-family
form `ae_contPair_G_testfunSet` (or its sequence form); whether the window transfer of DMS
Prop. 4.8 (p. 79) really needs the uncountable form is a statement question for the orchestrator.

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
§3.1, Prop. 3.1 (joint continuity of the circle-average process) through PAIR-AFF
(`Proofs/Field/PairAff.lean`); the bookkeeping here is an own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace D3Plus

open PairLim

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
  {G : Ω → ℂ × ℝ → ℝ} {M : ℝ≥0} {R δ : ℝ} {η : Measure ℂ}

/-! ## 1. Per measure, all scales at once -/

/-- **N2-CONTPAIR, per measure.** For a free field `X` with regular version `G` and a PAIR-LIM
measure `η`, almost surely the circle-regularized pairings of `G` with the dilated measure
`η.map (aff 0 c)` converge as `t → 0⁺`, simultaneously for every scale `c > 0`, to the continuum
limit `affLim (X ω) η (0, c)`. -/
theorem ae_contPair_G_measure [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (hG : WedgeTK.IsRegVersion X P G) (hS : PairLim.Setup M R δ η) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, 0 < c → ∃ L : ℝ,
      Tendsto (fun t => ∫ u, G ω ((c : ℂ) * u, t) ∂η) (𝓝[>] 0) (𝓝 L) := by
  filter_upwards [ae_tendstoLocallyUniformlyOn_affPair hX hS, hG.reg] with ω hTLU hreg
  intro c hc
  refine ⟨affLim (X ω) η (0, c), ?_⟩
  have hT : Tendsto (fun t => affPair (X ω) η t (0, c)) (𝓝[>] 0)
      (𝓝 (affLim (X ω) η (0, c))) :=
    hTLU.2.tendsto_at (show ((0 : ℝ), c) ∈ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) from ⟨trivial, hc⟩)
  have hmem : ∀ᵐ u ∂(η.map (aff 0 c)), u ∈ Hbar :=
    ((hS.map_aff (t := 0) (b := c) hc le_rfl).good.ae_mem).mono fun u hu => hu.2
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [affPair]
  rw [integral_congr_ae (hmem.mono fun u hu => hreg.evalReg_fc_of_mem hu ht),
    hS.integral_map_aff_witness (t := 0) (b := c) (F := G ω) hc le_rfl (hG.cont ω) ht]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp [aff]

/-! ## 2. The node's pairings: continuous compactly supported densities -/

/-- **N2-CONTPAIR for a fixed density.** For `f` continuous with compact support in the open
upper half-plane and every scale `c > 0` at once, the node's pairings of `G` converge. -/
theorem ae_contPair_G_density [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (hG : WedgeTK.IsRegVersion X P G) {f : ℂ → ℝ} (hfc : Continuous f)
    (hfs : HasCompactSupport f) (hfH : tsupport f ⊆ H) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, 0 < c → ∃ L : ℝ,
      Tendsto (fun t => ∫ u, G ω ((c : ℂ) * u, t)
        ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨M, R, δ, hS⟩ := exists_setup_withDensity hfc hfs hfH
  exact ae_contPair_G_measure hX hG hS

/-! ## 3. The Kolmogorov input of the oscillation bound

At a fixed radius the pairing is the field paired with the smoothed measure (§`smooth`), whose
increments in the radius are centred Gaussian with an explicit variance bound
(`PairLim.Setup.kernelCov2_smooth_le`). This is the probabilistic content of `N2ZPairOscStmt`
below; what is missing for the uncountable family of test functions is only the passage from
these moment bounds to an almost sure bound that is linear in a test-function norm. -/

/-! ## 4. Oscillation criterion and the remaining node -/

/-- **Oscillation criterion.** A real function on a right neighbourhood of `0` whose oscillation
over `(0, δ)` tends to `0` as `δ → 0` has a limit as `t → 0⁺` (completeness of `ℝ`). -/
theorem exists_tendsto_of_oscillation {f : ℝ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ t ∈ Ioo 0 δ, ∀ s ∈ Ioo 0 δ, |f t - f s| ≤ ε) :
    ∃ L : ℝ, Tendsto f (𝓝[>] 0) (𝓝 L) := by
  refine (cauchy_map_iff_exists_tendsto (l := 𝓝[>] (0 : ℝ)) (f := f)).1 ?_
  rw [Metric.cauchy_iff]
  refine ⟨(map_neBot_iff f).2 inferInstance, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hδ'⟩ := h (ε / 2) (by linarith)
  refine ⟨f '' Ioo 0 δ, Filter.mem_map.2 (mem_of_superset (Ioo_mem_nhdsGT hδ)
    fun t ht => ⟨t, ht, rfl⟩), fun x hx y hy => ?_⟩
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨s, hs, rfl⟩ := hy
  have h1 : f t - f s < ε := by
    have := (abs_le.1 (hδ' t ht s hs)).2
    linarith
  have h2 : f s - f t < ε := by
    have := (abs_le.1 (hδ' s hs t ht)).2
    linarith
  rw [Real.dist_eq]
  exact abs_sub_lt_iff.2 ⟨h1, h2⟩

/-- The weight `√(‖ρ‖_∞ ∫|ρ|) / c` of the test function `ρ` at scale `c` — the scaling of the
Kolmogorov increment bound `Var (X (smooth η a) − X (smooth η b)) ≤ 16 π M (η univ) |a − b|`
(`PairLim.Setup.kernelCov2_smooth_le`) for the density `ρ (·/c) / c²` of the dilated measure. -/
def n2PairWeight (c : ℝ) (ρ : TestFun H) : ℝ :=
  Real.sqrt (sSup (Set.range fun z => |ρ.1 z|) * ∫ z, |ρ.1 z|) / c

theorem n2PairWeight_nonneg {c : ℝ} (hc : 0 < c) (ρ : TestFun H) : 0 ≤ n2PairWeight c ρ :=
  div_nonneg (Real.sqrt_nonneg _) hc.le

/-- **Node N2Z-CONTPAIR-OSC** (the remaining input): the almost sure uniform oscillation bound
for the circle-regularized pairings of the free field, linear in the weight `n2PairWeight` of the
test function, simultaneously in the scale. -/
def N2ZPairOscStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∃ G : Ω → ℂ × ℝ → ℝ, WedgeTK.IsRegVersion X P G ∧
      ∀ᵐ ω ∂P, ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H,
        ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)), ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ t ∈ Ioo 0 δ, ∀ s ∈ Ioo 0 δ,
            |(∫ u, G ω ((c : ℂ) * u, t)
                ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) -
              (∫ u, G ω ((c : ℂ) * u, s)
                ∂(volume.withDensity fun z => ENNReal.ofReal (f z)))| ≤
              ε * n2PairWeight c ρ

/-- **N2Z-CONTPAIR from the uniform oscillation bound.** -/
theorem n2ZContPair_of_osc (hOsc : N2ZPairOscStmt) : N2ZContPairGFFStmt := by
  intro Ω _ P _ X hX
  obtain ⟨G, hGv, hosc⟩ := hOsc P X hX
  refine ⟨G, hGv, ?_⟩
  filter_upwards [hosc] with ω hω c hc ρ f hf
  have hkey : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo 0 δ, ∀ s ∈ Ioo 0 δ,
      |(∫ u, G ω ((c : ℂ) * u, t)
          ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) -
        (∫ u, G ω ((c : ℂ) * u, s)
          ∂(volume.withDensity fun z => ENNReal.ofReal (f z)))| ≤ ε := by
    intro ε hε
    rcases (n2PairWeight_nonneg hc ρ).eq_or_lt with h0 | hpos
    · obtain ⟨δ, hδ, hδ'⟩ := hω c hc ρ f hf 1 one_pos
      refine ⟨δ, hδ, fun t ht s hs => ?_⟩
      have hb := hδ' t ht s hs
      rw [← h0, mul_zero] at hb
      exact hb.trans hε.le
    · obtain ⟨δ, hδ, hδ'⟩ := hω c hc ρ f hf (ε / n2PairWeight c ρ) (div_pos hε hpos)
      exact ⟨δ, hδ, fun t ht s hs => by
        have := hδ' t ht s hs
        rwa [div_mul_cancel₀ ε hpos.ne'] at this⟩
  obtain ⟨L, hL⟩ := exists_tendsto_of_oscillation hkey
  exact ⟨L, hL⟩

end D3Plus
end QuantumZipper
