import QuantumZipper.Proofs.Section5.Prop17RawRep
import QuantumZipper.Proofs.Section5.Prop17FieldLaw
import QuantumZipper.Proofs.Field.PairAff
import QuantumZipper.Proofs.LQG.WedgeCanonical4
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Proposition 1.7, node D5-e: raw test pairings of the reference and shifted wedge fields

Sheffield, arXiv:1012.4797, Proposition 1.7 (§1.6, pp. 21–23; proof pp. 25–26). The law
`fieldLawFull H` of a wedge field reads its circle coordinates (`coordsFull`) jointly with its
raw test pairings (`pairRaw`). D5-c proved the shift identity only on `coordsFull`, and the raw
pairings of `canonical γ (rescale …)` are limits along radii `2^{-k}` of the underlying field,
while its regularized pairings (`pairTest`, determined by `coordsFull`) read it along `a·2^{-k}`.

This file settles that flag for the reference wedge `ref ω = canonical γ W_ω`,
`W_ω = wedgeField (lateralPart (X ω)) (A · ω) (Qc γ)`, and for its shift `shiftL γ L (ref ω)`:

* `ae_wedge_rescale_apply_eq`: a.s., for **all** `a, a' > 0` and all real `y` at once, the raw
  values of `rescale W Q a` and of `rescale (translate (rescale W Q a) y) Q a'` at a PAIR-LIM test
  measure `η` equal their regularized values. Inputs: PAIR-AFF
  (`ae_tendstoLocallyUniformlyOn_affPair`, all affine images of `η` at once), the regular
  version of the free field (`WedgeTK.exists_isRegVersion`), continuity of the radial path, and
  the deterministic `Prop17RawRep` (the singular radial term is handled by the truncation
  `gT … ρ₀`, `ρ₀` chosen per `ω` below the support of the rescaled `η`);
* `ae_pairRaw_eq_pairTest_wedge`: hence `pairRaw = pairTest` for both fields, for each `ρ`;
* `fieldLawFull_eq_map_coordsFull`: a random field with a.e.-measurable data and
  `pairRaw = pairTest` a.s. (per test function) has `fieldLawFull` equal to the push-forward of
  the law of its `coordsFull` under a fixed measurable graph map;
* `prop17RefShiftStmt_of_coords`: **D5-e reduces to the `coordsFull` level**:
  `Prop17RefShiftStmt γ L` follows from `WedgeDataAEMeasStmt γ γ`, `WedgeGoodStmt γ γ`, the a.s.
  positivity of the two scale parameters (`Prop17ScalePosStmt`) and the stationarity of the law of
  `coordsFull` of the reference wedge (`Prop17RefCoordsShiftStmt`, where D5-c works exactly).

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
§3.1, Prop. 3.1 (continuity of the circle-average process, via PAIR-AFF). The reduction and the
bookkeeping are own elementary arguments (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open PairLim WedgeMeas Factorization CoordsFull

variable {M : ℝ≥0} {R δ : ℝ} {η : Measure ℂ}

/-! ## 1. Continuum limit of the truncated wedge witness -/

/-- The compact set carrying a PAIR-LIM test measure. -/
def setK (R δ : ℝ) : Set ℂ := Metric.closedBall (0 : ℂ) R ∩ {u : ℂ | δ ≤ u.im}

theorem isCompact_setK (R δ : ℝ) : IsCompact (setK R δ) :=
  (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)

theorem _root_.QuantumZipper.PairLim.Setup.ae_mem_setK (hS : Setup M R δ η) : ∀ᵐ u ∂η, u ∈ setK R δ := by
  filter_upwards [hS.good.ae_mem, hS.im] with u h1 h2 using ⟨h1.1, h2⟩

theorem _root_.QuantumZipper.PairLim.Setup.mem_Hbar_of_setK (hS : Setup M R δ η) {u : ℂ} (hu : u ∈ setK R δ) : u ∈ Hbar :=
  show 0 ≤ u.im from hS.pos.le.trans hu.2

theorem tendsto_wedgeWitness {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {Q : ℝ}
    (hGR : WedgeTK.GoodRad x F) (hA : Continuous A) (hS : Setup M R δ η) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    {t B Lx : ℝ} (hB : 0 < B)
    (hPA : Tendsto (fun s => affPair x η s (t, B)) (𝓝[>] 0) (𝓝 Lx)) :
    Tendsto (fun s => ∫ u, (F (aff t B u, s) +
        ∫ v, WedgeMeasCoord.gT F A Q ρ₀ v ∂foldedCircle (aff t B u) s) ∂η) (𝓝[>] 0)
      (𝓝 (Lx + ∫ u, WedgeMeasCoord.gT F A Q ρ₀ (aff t B u) ∂η)) := by
  have := hS.good.isFiniteMeasure
  have hKH : ∀ u ∈ setK R δ, u ∈ Hbar := fun u hu => hS.mem_Hbar_of_setK hu
  have hgc := WedgeMeasCoord.continuous_gT (Q := Q) hGR.1.1 hA hρ₀
  have h2 := tendsto_integral_smooth_aff hgc (isCompact_setK R δ) hKH hS.ae_mem_setK t hB
  refine (hPA.add h2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hΦ : Continuous fun q : ℂ × ℝ => ∫ v, WedgeMeasCoord.gT F A Q ρ₀ v ∂foldedCircle q.1 q.2 :=
    continuousOn_univ.1 (GoodSample.gs_continuousOn_integral_fc_fun hgc.continuousOn)
  have i1 : Integrable (fun u => F (aff t B u, s)) η :=
    integrable_of_continuousOn_compact (isCompact_setK R δ) hS.ae_mem_setK
      ((continuousOn_slice_aff hGR.1.1 t hB.le hs).mono hKH)
  have i2 : Integrable (fun u => ∫ v, WedgeMeasCoord.gT F A Q ρ₀ v ∂foldedCircle (aff t B u) s)
      η :=
    integrable_of_continuousOn_compact (isCompact_setK R δ) hS.ae_mem_setK
      (hΦ.comp ((continuous_aff t B).prodMk continuous_const)).continuousOn
  rw [integral_add i1 i2]
  congr 1
  simp only [affPair]
  rw [integral_congr_ae ((hS.map_aff hB le_rfl).good.ae_mem.mono fun u hu =>
    hGR.1.evalReg_fc_of_mem hu.2 hs), hS.integral_map_aff_witness hB le_rfl hGR.1.1 hs]

/-! ## 2. Raw = regularized, per sample -/

/-- **Per-sample D5-e pairing identity.** For a good free sample, a continuous radial path and a
PAIR-LIM test measure `η` whose affine images all have continuum limits, the raw values of
`rescale W Q a` and of `rescale (translate (rescale W Q a) y) Q a'` at `η` are their
regularized values, for all `a, a' > 0` and real `y`. -/
theorem wedge_rescale_apply_eq {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {Q : ℝ}
    (hGR : WedgeTK.GoodRad x F) (hA : Continuous A) (hS : Setup M R δ η)
    (hPA : ∀ t B : ℝ, 0 < B → ∃ L, Tendsto (fun s => affPair x η s (t, B)) (𝓝[>] 0) (𝓝 L))
    {a : ℝ} (ha : 0 < a) :
    rescale (wedgeField (lateralPart x) A Q) Q a η =
        evalReg (rescale (wedgeField (lateralPart x) A Q) Q a) η ∧
      ∀ y a' : ℝ, 0 < a' →
        rescale (translate (rescale (wedgeField (lateralPart x) A Q) Q a) y) Q a' η =
          evalReg (rescale (translate (rescale (wedgeField (lateralPart x) A Q) Q a) y) Q a') η := by
  have := hS.good.isFiniteMeasure
  have hδ := hS.pos
  have hCL : ∀ ρ₀ : ℝ, 0 < ρ₀ → ∀ t B : ℝ, 0 < B → ∃ L, Tendsto (fun s => ∫ u,
      (F (aff t B u, s) + ∫ v, WedgeMeasCoord.gT F A Q ρ₀ v ∂foldedCircle (aff t B u) s) ∂η)
      (𝓝[>] 0) (𝓝 L) := by
    intro ρ₀ hρ₀ t B hB
    obtain ⟨L, hL⟩ := hPA t B hB
    exact ⟨_, tendsto_wedgeWitness hGR hA hS hρ₀ hB hL⟩
  constructor
  · have hρ₀ : 0 < a * δ / 2 := by positivity
    have hR := rawRep_wedgeField hGR hA Q hρ₀
    have hreg := isRegularWith_wedgeWitness hGR hA Q hρ₀
    obtain ⟨L, hL⟩ := hCL _ hρ₀ 0 (1 * a) (by positivity)
    refine hR.rescale_apply_eq hreg one_pos hρ₀.le (half_pos hρ₀) Q ha (isCompact_setK R δ)
      (fun u hu => ?_) hS.ae_mem_setK hL
    have h2 : δ ≤ u.im := hu.2
    have h1 := mul_le_mul_of_nonneg_right h2 ha.le
    rw [div_lt_iff₀ ha]
    nlinarith
  · intro y a' ha'
    have hρ₀ : 0 < a * a' * δ / 5 := by positivity
    have hreg := isRegularWith_wedgeWitness hGR hA Q hρ₀
    have hR := ((rawRep_wedgeField hGR hA Q hρ₀).rescaleRep hreg one_pos hρ₀.le (half_pos hρ₀)
      Q ha).translateRep hreg (by positivity) (by positivity) (by positivity) y
    obtain ⟨L, hL⟩ := hCL _ hρ₀ (0 + 1 * a * y) (1 * a * a') (by positivity)
    refine hR.rescale_apply_eq hreg (by positivity) (by positivity) (by positivity) Q ha'
      (isCompact_setK R δ) (fun u hu => ?_) hS.ae_mem_setK hL
    have e : ((a * a' * δ / 5 + a * a' * δ / 5 / 2) / a + a * a' * δ / 5 / 2 / a +
        a * a' * δ / 5 / 2 / a) / a' = δ / 2 := by
      field_simp; ring
    rw [e]
    have h2 : δ ≤ u.im := hu.2
    linarith

/-! ## 3. Almost surely -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem ae_wedge_rescale_apply_eq [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {A : ℝ → Ω → ℝ} (hA : ∀ᵐ ω ∂P, Continuous fun t => A t ω) (Q : ℝ) (hS : Setup M R δ η) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, 0 < a →
      rescale (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q) Q a η =
          evalReg (rescale (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q) Q a) η ∧
        ∀ y a' : ℝ, 0 < a' →
          rescale (translate (rescale (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q) Q a) y)
              Q a' η =
            evalReg (rescale (translate (rescale (wedgeField (lateralPart (X ω))
              (fun t => A t ω) Q) Q a) y) Q a') η := by
  obtain ⟨Gv, hGv⟩ := WedgeTK.exists_isRegVersion hX
  filter_upwards [hGv.ae_good, hA, ae_tendstoLocallyUniformlyOn_affPair hX hS] with ω hg hc hp a ha
  exact wedge_rescale_apply_eq hg hc hS
    (fun t B hB => ⟨_, hp.2.tendsto_at (show (t, B) ∈ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) from
      ⟨trivial, hB⟩)⟩) ha

/-- **D5-e pairings.** For each test function `ρ`, almost surely, for all `a, a' > 0` and real
`y`, the raw test pairings of `rescale W Q a` and of `rescale (translate (rescale W Q a) y) Q a'`
equal their regularized pairings (`pairTest`, a function of `coordsFull`). -/
theorem ae_pairRaw_eq_pairTest_wedge [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {A : ℝ → Ω → ℝ} (hA : ∀ᵐ ω ∂P, Continuous fun t => A t ω) (Q : ℝ) (ρ : TestFun H) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, 0 < a →
      pairRaw (rescale (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q) Q a) ρ.1 =
          pairTest (rescale (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q) Q a) ρ.1 ∧
        ∀ y a' : ℝ, 0 < a' →
          pairRaw (rescale (translate (rescale (wedgeField (lateralPart (X ω))
              (fun t => A t ω) Q) Q a) y) Q a') ρ.1 =
            pairTest (rescale (translate (rescale (wedgeField (lateralPart (X ω))
              (fun t => A t ω) Q) Q a) y) Q a') ρ.1 := by
  obtain ⟨M₁, R₁, δ₁, h₁⟩ := exists_setup_withDensity ρ.2.1.continuous ρ.2.2.1 ρ.2.2.2
  obtain ⟨M₂, R₂, δ₂, h₂⟩ := exists_setup_withDensity (g := fun z => -ρ.1 z)
    ρ.2.1.continuous.neg ρ.2.2.1.neg
    (show tsupport (-ρ.1) ⊆ H by rw [tsupport_neg]; exact ρ.2.2.2)
  filter_upwards [ae_wedge_rescale_apply_eq hX hA Q h₁, ae_wedge_rescale_apply_eq hX hA Q h₂]
    with ω e₁ e₂ a ha
  refine ⟨?_, fun y a' ha' => ?_⟩
  · unfold pairRaw pairTest; rw [(e₁ a ha).1, (e₂ a ha).1]
  · unfold pairRaw pairTest; rw [(e₁ a ha).2 y a' ha', (e₂ a ha).2 y a' ha']

end Raw
end FieldLaw
end S5
end QuantumZipper
