import QuantumZipper.Proofs.Thm18.R18AreaNullIndep
import QuantumZipper.Proofs.Thm18.R18AreaNullScale
import QuantumZipper.Proofs.Thm18.D74Null
import QuantumZipper.Proofs.Thm18.D74Curve
import QuantumZipper.Proofs.RS.TraceMeas
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.RS.RohdeSchrammSimple
import QuantumZipper.Proofs.Wire2b
import QuantumZipper.Proofs.Zipper.F2Unscaled

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-AREANULL, part 4: the curve as an independent random null set; the reference wedge

* `exists_curveSeq`: for a Brownian motion `B` and `0 < κ < 4`, the curve
  `curveOf (drive κ B ω)` is a.s. the closure of `{T m ω}` for a measurable sequence `T` that is a
  function of the path of `B` (independent of anything independent of `pathOf B`), and it is
  Lebesgue-null (`D74.ae_volume_sleTrace_eq_zero_lt_four`, Rohde–Schramm via `RS`).
* `ref_curveAreaNull`: on the reference space of a quantum wedge (free field `X`, wedge process
  `A`, unscaled field `Z = wedgeField …`) with a Brownian motion `B` independent of `(X, A)`, the
  canonical description `canonical γ Z` gives zero area to the curve of the canonicalized driver
  `W(a² ·)/a`, `a = scaleParam γ Z` (Sheffield (1.8), p. 21): the rescaling moves area and curve
  together (`qAreaMeasure_canonical_curveOf_scale`), and `Z` charges no independent null set
  (`ae_qAreaMeasure_wedgeField_indep_null`).

Source: Sheffield (arXiv:1012.4797), §4.1 p. 48 ("the measure zero set η", η independent of h).
The measurability bookkeeping is our own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- **The SLE curve as a measurable, path-determined random closed null set.** -/
theorem exists_curveSeq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ T : Ω → ℕ → ℂ, Measurable T ∧
      (∀ {β : Type} [MeasurableSpace β] {ξ : Ω → β}, IndepFun ξ (pathOf B) P → IndepFun ξ T P) ∧
      ∀ᵐ ω ∂P, curveOf (drive κ B ω) = closure (range (T ω)) ∧
        volume (curveOf (drive κ B ω)) = 0 := by
  obtain ⟨B₁, hB₁m, hB₁c, -, hB₁, hB₁eq⟩ := RS.exists_good_version0 hB
  have hm := RS.measurable_toCPath hB₁m hB₁c
  set ν : Measure RS.CPath := P.map (RS.toCPath B₁ hB₁c) with hνdef
  have : IsProbabilityMeasure ν := inferInstance
  have hν : IsBrownianReal RS.canonBM ν :=
    RS.isBrownianReal_canonBM hB₁.toIsPreBrownianReal hB₁m hB₁c
  obtain ⟨η, -, hηm, -, hηeq⟩ := RS.exists_measurable_sleTrace hν hκ (by linarith)
  have : Countable ℚ≥0 := inferInstanceAs (Countable {q : ℚ // 0 ≤ q})
  obtain ⟨qn, hqn⟩ := exists_surjective_nat ℚ≥0
  set τ : RS.CPath → ℕ → ℂ := fun f m => η f (qn m) with hτdef
  have hτ : Measurable τ := measurable_pi_iff.2 fun m => (measurable_pi_apply _).comp hηm
  refine ⟨fun ω => τ (RS.toCPath B₁ hB₁c ω), hτ.comp hm, ?_, ?_⟩
  · intro β _ ξ hξ
    have h1 : IndepFun ξ (pathOf B₁) P := hξ.congr EventuallyEq.rfl (by
      filter_upwards [hB₁eq] with ω h
      funext t
      exact (h t).symm)
    have h2 : IndepFun ξ (RS.toCPath B₁ hB₁c) P := by
      rw [indepFun_iff_measure_inter_preimage_eq_mul] at h1 ⊢
      intro S C hS hC
      obtain ⟨C', hC', e2⟩ := MeasurableSpace.measurableSet_comap.1 hC
      have e3 : RS.toCPath B₁ hB₁c ⁻¹' C = pathOf B₁ ⁻¹' C' := by rw [← e2]; rfl
      rw [e3]
      exact h1 S C' hS hC'
    exact h2.comp measurable_id hτ
  · have hEq : ∀ᵐ ω ∂P, EqOn (η (RS.toCPath B₁ hB₁c ω)) (sleTrace κ B ω) (Ici 0) := by
      filter_upwards [ae_of_ae_map hm.aemeasurable hηeq, hB₁eq] with ω h hb
      rw [RS.sleTrace_toCPath, RS.sleTrace_congr_of_eq hb] at h
      exact h
    filter_upwards [hEq, RS.rohdeSchrammSimple κ hκ hκ4.le P B hB,
      Thm18Asm.D74.ae_volume_sleTrace_eq_zero_lt_four hB hκ hκ4] with ω he hrs hv
    obtain ⟨⟨-, hc, -, -, ht⟩, -⟩ := hrs
    have hcurve : curveOf (drive κ B ω) = sleTrace κ B ω '' Ici 0 :=
      Thm18Asm.D74.curveOf_eq_image hc ht
    have hrange : range (fun m => τ (RS.toCPath B₁ hB₁c ω) m) =
        range (fun q : ℚ≥0 => trace (drive κ B ω) (q : ℝ)) := by
      rw [show (fun m => τ (RS.toCPath B₁ hB₁c ω) m) =
        (fun q : ℚ≥0 => η (RS.toCPath B₁ hB₁c ω) (q : ℝ)) ∘ qn from rfl, hqn.range_comp]
      congr 1
      funext q
      exact he (show (0 : ℝ) ≤ (q : ℝ) by positivity)
    refine ⟨?_, by rw [hcurve]; exact hv⟩
    rw [hrange]
    rfl

/-- The unscaled wedge field of the reference space. -/
def zRef (γ : ℝ) {Ω : Type} (X : Ω → FieldSample) (A : ℝ → Ω → ℝ) (ω : Ω) : FieldSample :=
  wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)

/-- **Reference form of the curve-area-null statement.** -/
theorem ref_curveAreaNull {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample} {A : ℝ → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hX : IsFreeGFFModConstH X P) (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P)
    (hI : IndepFun X (fun ω t => A t ω) P) (hB : IsBrownianReal B P)
    (hIB : IndepFun (fun ω => (X ω, fun t => A t ω)) (pathOf B) P) :
    ∀ᵐ ω ∂P, qAreaMeasure γ (canonical γ (zRef γ X A ω))
      (curveOf fun r => drive (γ ^ 2) B ω (scaleParam γ (zRef γ X A ω) ^ 2 * r) /
        scaleParam γ (zRef γ X A ω)) = 0 := by
  have hκ : 0 < γ ^ 2 := by positivity
  have hκ4 : γ ^ 2 < 4 := by nlinarith
  have halpha : γ - 2 / γ < Qc γ := F2.alpha_lt_Qc' hγ hγ2
  obtain ⟨T, hTm, hTind, hTae⟩ := exists_curveSeq hB hκ hκ4
  have hXT : IndepFun T X P :=
    (hTind (ξ := X) (hIB.comp measurable_fst measurable_id)).symm
  have hS : ∀ᵐ ω ∂P, volume (closure (range (T ω))) = 0 :=
    hTae.mono fun ω h => h.1 ▸ h.2
  have hnull := ae_qAreaMeasure_wedgeField_indep_null hX hγ hγ2 (Q := Qc γ)
    (WedgeCan4.ae_continuous_wedgeProcess hA) hTm hXT hS
  obtain ⟨δ, hδ, hgood⟩ := RS.ae_sleTrace_good hB hκ (by linarith)
  filter_upwards [hnull, hTae, hgood, Wire2.ae_wedge_canonical_spec hγ hγ2 halpha hX hA hI,
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 halpha Ω _ P X A inferInstance hX hA hI, hB.cont,
    hB.eval_zero_ae_eq_zero] with ω hn hT hg hspec hZg hc h0
  have hW : Continuous (drive (γ ^ 2) B ω) := drive_continuous hc
  have hW0 : drive (γ ^ 2) B ω 0 = 0 := drive_zero h0
  have hlim : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ, Tendsto
      (fun y : ℝ => fwdMapInv (drive (γ ^ 2) B ω) t (y * Complex.I)) (𝓝[>] 0) (𝓝 p) := by
    intro t ht
    obtain ⟨C, hC⟩ := hg.2.2 ⌈t⌉₊
    exact ⟨_, RS.tendsto_fwdMapInv_of_rpow_bound hδ (hC t ⟨ht, Nat.le_ceil t⟩)⟩
  rw [zRef, qAreaMeasure_canonical_curveOf_scale hγ hZg hspec.1 hW hW0 hlim hg.2.1, hT.1]
  exact hn

end R18
end QuantumZipper
