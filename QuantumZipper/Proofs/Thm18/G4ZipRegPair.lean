import QuantumZipper.Proofs.Thm18.G4ZipRegPairDet
import QuantumZipper.Proofs.LQG.WedgeCRegCont
import QuantumZipper.Proofs.LQG.WedgeBoundaryReg
import QuantumZipper.Proofs.LQG.LogSingGood

/-!
# Theorem 1.8, node G4-ZIPREG: continuum limits of the wedge pairings; `G4ZipRegStmt`

`WedgePairContStmt` (`G4ZipRegCore.lean`) is proved here (`wedgePairContStmt_holds`), hence
`G4ZipRegStmt` modulo the round-trip node `G4RoundUpRezipCoreStmt` only
(`g4ZipRegStmt_of_rezipCore`), and the headline `g4Stmt_of_coreNodesZipReg` no longer carries
`G4ZipRegStmt`.

Route. For the reference field `canonical γ W`, `W = wedgeField (lateralPart X) A Q`, the smoothed
pairing at `g dz` is, with `b = scaleParam γ W > 0`, the smoothed pairing of `W` against the
dilation of `g dz` by `b` at radius `b s`, plus the constant `Q log b · ∫ g⁺`; its continuum limit
is `WedgeCReg.ae_contPair_wedge` (per test function, all dilations at once; PAIR-AFF, i.e.
Duplantier–Sheffield, Invent. Math. 185 (2011), §3.1, Prop. 3.1), applied to `g ∘ (−conj)`. The
Cauchy-along-rationals event (`ZipReg.CauchyQ`) is measurable and reads only the regularization,
so it transfers to every quantum wedge through the law of its data
(`WedgeBdry.ae_of_fieldLawFull_eq`); for a regular sample it is equivalent to the continuum limit
(`ZipReg.exists_tendsto_of_cauchyQ`). **Own elementary argument** (bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace ZipReg

/-- `ρ ∘ (−conj)` as a test function. -/
def negConjTest (ρ : TestFun H) : TestFun H :=
  ⟨fun z => ρ.1 (-conj z), by
    obtain ⟨hs, hc, hH⟩ := ρ.2
    obtain ⟨-, h2, h3⟩ := WedgeCReg.testFun_negConj hs.continuous hc hH
    refine ⟨?_, h2, h3⟩
    have e : (fun z => ρ.1 (-conj z)) =
        ρ.1 ∘ (-(Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap) := by
      funext z; simp
    rw [e]
    exact hs.comp (ContinuousLinearMap.contDiff _)⟩

theorem negConj_negConj (f : ℂ → ℝ) : (fun z => f (-conj (-conj z))) = f := by
  funext z; simp

/-- **Reference side**: the smoothed pairing of the canonical reference wedge with `g dz` has a
continuum limit, given the continuum limits of `W` at all dilations of `g ∘ (−conj)`. -/
theorem tendsto_pairSm_canonical {γ : ℝ} {W : FieldSample} (hW : IsRegularSample W)
    (hb : 0 < scaleParam γ W) {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgH : tsupport g ⊆ H)
    (hc : ∃ L : ℝ, Tendsto (fun r => ∫ u, evalReg W
      (foldedCircle ((scaleParam γ W : ℂ) * -conj u) r)
        ∂(volume.withDensity fun z => ENNReal.ofReal (g (-conj z)))) (𝓝[>] 0) (𝓝 L)) :
    ∃ L : ℝ, Tendsto (pairSm (canonical γ W) g) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨F, hF⟩ := hW
  set b := scaleParam γ W with hbdef
  set Q := Qc γ
  obtain ⟨L, hL⟩ := hc
  have hF' := hF.rescale' Q hb
  obtain ⟨M, R, δ, hS⟩ := PairLim.exists_setup_withDensity hg hgc hgH
  have hfin := hS.good.isFiniteMeasure
  -- the reflected integral is the dilated one
  have e1 : ∀ r, ∫ u, evalReg W (foldedCircle ((b : ℂ) * -conj u) r)
      ∂(volume.withDensity fun z => ENNReal.ofReal (g (-conj z))) =
      ∫ v, evalReg W (foldedCircle ((b : ℂ) * v) r) ∂G1.tmeas g := by
    intro r
    rw [WedgeCReg.integral_withDensity_negConj
      (fun v => evalReg W (foldedCircle ((b : ℂ) * v) r)) (fun z => g (-conj z))]
    simp only [map_neg, Complex.conj_conj, neg_neg]
  have hbs : Tendsto (fun s : ℝ => b * s) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs =>
      mul_pos hb hs⟩
    have h0 : Tendsto (fun s : ℝ => b * s) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul b
    exact h0.mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun s => ∫ v, evalReg W (foldedCircle ((b : ℂ) * v) (b * s)) ∂G1.tmeas g)
      (𝓝[>] 0) (𝓝 L) := by
    have := hL.comp hbs
    simp only [Function.comp_def, e1] at this
    exact this
  refine ⟨L + (G1.tmeas g).real univ * (Q * Real.log b),
    (hA.add tendsto_const_nhds).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hmem : ∀ v ∈ Hbar, evalReg (canonical γ W) (foldedCircle v s) =
      evalReg W (foldedCircle ((b : ℂ) * v) (b * s)) + Q * Real.log b := by
    intro v hv
    rw [show canonical γ W = rescale W Q b from rfl, hF'.evalReg_fc_of_mem hv hs,
      hF.evalReg_fc_of_mem (RegClosure.mapsTo_mul_pos hb hv) (mul_pos hb hs)]
  have hi : Integrable (fun v => evalReg (canonical γ W) (foldedCircle v s)) (G1.tmeas g) :=
    integrable_evalReg_fc_tmeas hF' hg hgc hgH hs
  have hi' : Integrable (fun v => evalReg W (foldedCircle ((b : ℂ) * v) (b * s)))
      (G1.tmeas g) := by
    refine (hi.sub (integrable_const (Q * Real.log b))).congr
      (hS.good.ae_mem.mono fun v hv => ?_)
    show evalReg (canonical γ W) (foldedCircle v s) - Q * Real.log b = _
    rw [hmem v hv.2, add_sub_cancel_right]
  show _ = ∫ v, evalReg (canonical γ W) (foldedCircle v s) ∂G1.tmeas g
  rw [integral_congr_ae (hS.good.ae_mem.mono fun v hv => hmem v hv.2),
    integral_add hi' (integrable_const _), integral_const, smul_eq_mul]

end ZipReg

/-- **`WedgePairContStmt` holds.** -/
theorem wedgePairContStmt_holds : WedgePairContStmt := by
  intro γ Ω _ P _ Y hγ hγ2 hW ρ
  have hY := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hW.1 hW
  have hreg := wedgeRegSampleStmt_holds γ P Y hγ hγ2 hW
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hW
  have hZW : IsQuantumWedge γ (γ - 2 / γ)
      (fun ω => canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) P' :=
    ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, rfl⟩
  have hZ := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hZW
  obtain ⟨hs, hc, hH⟩ := ρ.2
  have hH' : tsupport (-ρ.1) ⊆ H := by rw [tsupport_neg]; exact hH
  let S : FieldSample → Prop := fun x =>
    ZipReg.CauchyQ (ZipReg.pairSm x ρ.1) ∧ ZipReg.CauchyQ (ZipReg.pairSm x (-ρ.1))
  have hSm : MeasurableSet {x : FieldSample | S x} :=
    measurableSet_setOfPred.2 ((ZipReg.measurable_cauchyQ _).and (ZipReg.measurable_cauchyQ _))
  have hrec : ∀ x, S (Factorization.reconstruct (Factorization.coords x)) ↔ S x := by
    intro x
    simp only [S, ZipReg.pairSm_reconstruct]
  -- the reference side
  have href : ∀ᵐ ω ∂P',
      S (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) := by
    filter_upwards [WedgeCReg.ae_contPair_wedge hX (WedgeCan4.ae_continuous_wedgeProcess hA)
        (Qc γ) (ZipReg.negConjTest ρ),
      WedgeCan4.ae_wedge_canonical_spec_of_inputs (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα)
        (WedgeInf.wedgeInfiniteTotal hγ hγ2 hα) hγ hγ2 hα hX hA hI,
      LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A hP' hX hA hI] with ω hcp hsp hgood
    have hb := hsp.1
    obtain ⟨-, c1, s1, t1⟩ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ρ.1 (-conj z)) ∧
        Continuous (fun z => ρ.1 (-conj z)) ∧ HasCompactSupport (fun z => ρ.1 (-conj z)) ∧
        tsupport (fun z => ρ.1 (-conj z)) ⊆ H :=
      ⟨(ZipReg.negConjTest ρ).2.1, WedgeCReg.testFun_negConj hs.continuous hc hH⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨L, hL⟩ := ZipReg.tendsto_pairSm_canonical (γ := γ) hgood.1 hb hs.continuous hc hH
        (by
          have := hcp _ hb (fun z => ρ.1 (-conj z)) (Set.mem_insert _ _)
          simpa only [ZipReg.negConj_negConj] using this)
      exact ZipReg.cauchyQ_of_tendsto hL
    · obtain ⟨L, hL⟩ := ZipReg.tendsto_pairSm_canonical (γ := γ) hgood.1 hb hs.continuous.neg
        hc.neg hH'
        (by
          have := hcp _ hb (-(fun z => ρ.1 (-conj z))) (Set.mem_insert_of_mem _ rfl)
          simpa only [Pi.neg_apply, neg_neg, map_neg, Complex.conj_conj] using this)
      exact ZipReg.cauchyQ_of_tendsto hL
  have hYS : ∀ᵐ ω ∂P, S (Y ω) :=
    WedgeBdry.ae_of_fieldLawFull_eq hlaw hY hZ S hSm hrec href
  filter_upwards [hYS, hreg] with ω hω hr
  obtain ⟨F, hF⟩ := hr
  intro f hf
  rcases hf with rfl | hf
  · exact ⟨fun s hs' => ZipReg.integrable_evalReg_fc_tmeas hF hs.continuous hc hH hs',
      ZipReg.exists_tendsto_of_cauchyQ (ZipReg.continuousOn_pairSm hF hs.continuous hc hH) hω.1⟩
  · rw [Set.mem_singleton_iff] at hf
    subst hf
    exact ⟨fun s hs' => ZipReg.integrable_evalReg_fc_tmeas hF hs.continuous.neg hc.neg hH' hs',
      ZipReg.exists_tendsto_of_cauchyQ (ZipReg.continuousOn_pairSm hF hs.continuous.neg hc.neg
        hH') hω.2⟩

end Thm18Asm
end QuantumZipper
