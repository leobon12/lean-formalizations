import QuantumZipper.Proofs.Section5.Prop17StatLocal
import QuantumZipper.Proofs.Abstract.PalmShift

/-!
# Proposition 1.7, node D5-e: the pre-limit from Palm zooms (PROP17-STAT)

Sheffield, arXiv:1012.4797, proof of Proposition 1.7 (pp. 25–26): let `x` be sampled from the
quantum boundary measure (the Palm law of Proposition 1.6) and `x'` the point `δ L` quantum
length units to the right of `x`; "the law of `x'` converges (in total variation sense) to the law
of `x` as `δ → 0`"; "in the rescaled surfaces boundary lengths are scaled by `e^{C/2}`, so if we
set `δ = e^{-C/2}` the distance between `x` and `x'` is `L` after the rescaling".

This file proves `Prop17ApproxStmt γ L` from one hypothesis, `Prop17PalmZoomStmt γ` (D4⁺: the
reference wedge is the TV-local limit, on `locFull`, of the canonical zooms at a Palm point, with
the regularity of the boundary measure needed by D5-b/D5-c). The pieces:

* the Palm law is a probability measure, and `P`-a.s. properties hold `palmLaw`-a.s.;
* **D5-b + D5-c** (`Prop17Shift.lean`, `Prop17Field.lean`): a.s. the shift of the canonical zoom
  at `x` has the circle coordinates of the canonical zoom at `x' = palmShiftRight ν (L e^{-C/2}) x`;
* **A6** (`palm_shift_right_bound`): `|P(Ψ_C(x') ∈ E) − P(Ψ_C(x) ∈ E)| ≤ 2 L e^{-C/2} / Eν[a,b]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull TV PalmShift FieldShift

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## 1. The Palm law -/

theorem isProbabilityMeasure_palmLaw (P : Measure Ω) [IsProbabilityMeasure P] (ν : Kernel Ω ℝ)
    [IsSFiniteKernel ν] (a b : ℝ) (h0 : palmMass P ν a b ≠ 0) (htop : palmMass P ν a b ≠ ∞) :
    IsProbabilityMeasure (palmLaw P ν a b) := by
  constructor
  rw [palmLaw, Measure.smul_apply, Measure.compProd_apply MeasurableSet.univ, smul_eq_mul]
  have : ∫⁻ ω, (ν.restrict (measurableSet_Icc (a := a) (b := b))) ω (Prod.mk ω ⁻¹' univ) ∂P =
      palmMass P ν a b := by
    simp only [preimage_univ, Kernel.restrict_apply, Measure.restrict_apply_univ, palmMass]
  rw [this, ENNReal.inv_mul_cancel h0 htop]

theorem ae_palmLaw_of_ae (P : Measure Ω) [IsProbabilityMeasure P] (ν : Kernel Ω ℝ)
    [IsSFiniteKernel ν] (a b : ℝ) {R : Ω × ℝ → Prop} (h : ∀ᵐ ω ∂P, ∀ x, R (ω, x)) :
    ∀ᵐ p ∂palmLaw P ν a b, R p := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have hN : palmLaw P ν a b (Prod.fst ⁻¹' N) = 0 := by
    rw [palmLaw, Measure.smul_apply, Measure.compProd_apply (hNm.preimage measurable_fst),
      smul_eq_mul]
    have : ∫⁻ ω, (ν.restrict (measurableSet_Icc (a := a) (b := b))) ω
        (Prod.mk ω ⁻¹' (Prod.fst ⁻¹' N)) ∂P = 0 := by
      rw [lintegral_eq_zero_iff' (Kernel.measurable_kernel_prodMk_left
        (hNm.preimage measurable_fst)).aemeasurable]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
      have : (Prod.mk ω : ℝ → Ω × ℝ) ⁻¹' (Prod.fst ⁻¹' N) = ∅ := by
        ext x; simp [hω]
      simp [this]
    rw [this, mul_zero]
  refine measure_mono_null (fun p hp => ?_) hN
  by_contra hpN
  exact hp (by_contra fun hR => hpN (hsub fun hall => hR (hall p.2)))

/-! ## 2. The hypothesis D4⁺ (Palm zoom convergence) -/

/-- The circle coordinates of the canonical zoom at level `C` at `x`. -/
def zoomCoords (γ C : ℝ) (h : Ω → FieldSample) (p : Ω × ℝ) : ℕ → ℝ :=
  coordsFull (canonical γ (zoomField γ C (h p.1) p.2))

/-- **D4⁺ for Proposition 1.7 (hypothesis).** For every reference construction of the `γ`-wedge
there is a boundary-LQG field `h` with measurable boundary-measure kernel `ν`, and an interval
`[a, b]` of finite positive expected `ν`-mass, such that a.s. `h` is good, `ν_h` is atomless,
charges every open interval and has infinite mass to the right of every point, every zoom has a
positive scale parameter, the zoom coordinates are measurable, and the laws of the zoom
coordinates under the Palm law converge TV-locally (on `locFull`) to the law of the reference
coordinates as `C → ∞` (Proposition 1.6 in its TV-local form, with `D = ℍ`; intended instance:
`h` a free boundary GFF on `ℍ` with a fixed normalization). -/
def Prop17PalmZoomStmt (γ : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess γ (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (h : Ω → FieldSample)
      (ν : Kernel Ω ℝ) (a b : ℝ), IsProbabilityMeasure P ∧ IsSFiniteKernel ν ∧
      palmMass P ν a b ≠ 0 ∧ palmMass P ν a b ≠ ∞ ∧
      (∀ᵐ ω ∂P, ν ω = qBoundaryMeasure γ (h ω) ∧ IsLQGGood γ (h ω) ∧
        (∀ t : ℝ, ν ω {t} = 0) ∧ (∀ u v : ℝ, u < v → 0 < ν ω (Ioo u v)) ∧
        (∀ x : ℝ, ν ω (Ici x) = ⊤) ∧ ∀ C x : ℝ, 0 < scaleParam γ (zoomField γ C (h ω) x)) ∧
      (∀ C : ℝ, Measurable (zoomCoords γ C h)) ∧
      TVLocalTendsto atTop (fun C : ℝ => (palmLaw P ν a b).map (zoomCoords γ C h))
        (P'.map fun ω => coordsFull (refField γ X A ω)) locFull

/-! ## 3. The pointwise shift identity (D5-b + D5-c) -/

theorem shiftCoords_zoomCoords {γ L C : ℝ} (hγ : 0 < γ) (hL : 0 < L) {h : FieldSample}
    (hg : IsLQGGood γ h) (hatom : ∀ t : ℝ, qBoundaryMeasure γ h {t} = 0)
    (hpos : ∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ h (Ioo u v))
    (hinf : ∀ x : ℝ, qBoundaryMeasure γ h (Ici x) = ⊤)
    (hsc : ∀ C x : ℝ, 0 < scaleParam γ (zoomField γ C h x)) (x : ℝ) :
    shiftCoords γ L (coordsFull (canonical γ (zoomField γ C h x))) =
      coordsFull (canonical γ (zoomField γ C h
        (palmShiftRight (qBoundaryMeasure γ h) (Real.toNNReal (L * Real.exp (-C / 2))) x))) := by
  have ha := hsc C x
  have hZ : IsLQGGood γ (canonical γ (zoomField γ C h x)) :=
    (isLQGGood_zoomField hg C x).rescale hγ ha
  rw [← coordsFull_shiftL hZ, shiftL]
  have hy := wedgeLengthPoint_canonical_zoomField hγ hg hL ha hatom hpos (hinf x)
  set x' := palmShiftRight (qBoundaryMeasure γ h) (Real.toNNReal (L * Real.exp (-C / 2))) x
  have hx' : x + scaleParam γ (zoomField γ C h x) *
      wedgeLengthPoint γ L (canonical γ (zoomField γ C h x)) = x' := by
    rw [hy, mul_div_cancel₀ _ ha.ne']; ring
  have := coordsFull_canonical_translate_canonical_zoomField hγ hg C x
    (wedgeLengthPoint γ L (canonical γ (zoomField γ C h x))) ha (hsc C _)
  rw [this, hx']

theorem zoomCoords_mem_goodC {γ C : ℝ} (hγ : 0 < γ) {h : FieldSample} (hg : IsLQGGood γ h)
    (hinf : ∀ x : ℝ, qBoundaryMeasure γ h (Ici x) = ⊤)
    (hsc : ∀ C x : ℝ, 0 < scaleParam γ (zoomField γ C h x)) (x : ℝ) :
    coordsFull (canonical γ (zoomField γ C h x)) ∈ GoodC γ := by
  have ha := hsc C x
  refine coordsFull_mem_goodC ((isLQGGood_zoomField hg C x).rescale hγ ha) ?_
  rw [qBoundaryMeasure_canonical_zoomField hγ hg x C ha, Measure.smul_apply,
    Measure.map_apply (by fun_prop) measurableSet_Ici, smul_eq_mul]
  have : (fun t : ℝ => (t - x) / scaleParam γ (zoomField γ C h x)) ⁻¹' Ici 0 = Ici x := by
    ext t
    simp only [mem_preimage, mem_Ici]
    rw [div_nonneg_iff]
    constructor
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · linarith
      · exact absurd h2 (not_le.2 ha)
    · intro ht; exact Or.inl ⟨by linarith, ha.le⟩
  rw [this, hinf x, ENNReal.mul_top]
  exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

/-! ## 4. The pre-limit statement from D4⁺ (A6 + D5-b + D5-c) -/

theorem tendsto_prop17_bound (L M : ℝ) :
    Tendsto (fun C : ℝ => 2 * (L * Real.exp (-C / 2)) * 1 / M) atTop (𝓝 0) := by
  have h1 : Tendsto (fun C : ℝ => -C / 2) atTop atBot :=
    tendsto_neg_atTop_atBot.atBot_div_const (by norm_num : (0 : ℝ) < 2)
  have he : Tendsto (fun C : ℝ => Real.exp (-C / 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h1
  have := (((he.const_mul L).const_mul 2).mul_const 1).div_const M
  simpa using this

/-- **`Prop17ApproxStmt` from D4⁺.** -/
theorem prop17ApproxStmt_of_palmZoom {γ L : ℝ} (hγ : 0 < γ) (hL : 0 < L)
    (hD4 : Prop17PalmZoomStmt γ) : Prop17ApproxStmt γ L := by
  intro Ω' _ P' X A hP' hX hA hI
  obtain ⟨Ω, _, P, h, ν, a, b, hP, hν, h0, htop, hae, hmeas, hTV⟩ :=
    hD4 Ω' _ P' X A hP' hX hA hI
  haveI := hP
  haveI := hν
  haveI := isProbabilityMeasure_palmLaw P ν a b h0 htop
  set Q := palmLaw P ν a b with hQ
  refine ⟨ℝ, atTop, fun C => Q.map (zoomCoords γ C h), inferInstance, fun C => inferInstance,
    hTV, fun C => ?_, fun E hE => ?_⟩
  · refine (ae_map_iff (hmeas C).aemeasurable (measurableSet_goodC γ)).2 ?_
    refine ae_palmLaw_of_ae P ν a b (R := fun p => zoomCoords γ C h p ∈ GoodC γ) ?_
    filter_upwards [hae] with ω hω x
    obtain ⟨he, hg, -, -, hinf, hsc⟩ := hω
    exact zoomCoords_mem_goodC hγ hg (fun x => by rw [← he]; exact hinf x) hsc x
  · have hEm : MeasurableSet E := MeasurableSet.of_mem_measurableCylinders hE
    refine squeeze_zero_norm (fun C => ?_) (tendsto_prop17_bound L (palmMass P ν a b).toReal)
    set ℓ := Real.toNNReal (L * Real.exp (-C / 2)) with hℓdef
    have hℓ : ((ℓ : ℝ≥0) : ℝ) = L * Real.exp (-C / 2) :=
      Real.coe_toNNReal _ (mul_nonneg hL.le (Real.exp_pos _).le)
    set G : Ω × ℝ → ℝ := (zoomCoords γ C h ⁻¹' E).indicator 1 with hGdef
    have hGm : Measurable G := measurable_const.indicator ((hmeas C) hEm)
    have hGM : ∀ p, |G p| ≤ 1 := fun p => by
      simp only [hGdef, Set.indicator]
      split_ifs <;> simp
    have hA6 := palm_shift_right_bound P ν a b ℓ
      (hae.mono fun ω hω => ⟨hω.2.2.1⟩) (hae.mono fun ω hω => hω.2.2.2.1)
      (hae.mono fun ω hω => by rw [hω.2.2.2.2.1 b]; exact le_top) htop hGm hGM
    have hint1 : ∫ p, G p ∂Q = (Q.map (zoomCoords γ C h)).real E := by
      rw [hGdef, integral_indicator_one ((hmeas C) hEm),
        map_measureReal_apply (hmeas C) hEm]
    have hint2 : ∫ p, G (p.1, palmShiftRight (ν p.1) ℓ p.2) ∂Q =
        (Q.map (zoomCoords γ C h)).real (shiftCoords γ L ⁻¹' E) := by
      rw [map_measureReal_apply (hmeas C) (measurable_shiftCoords γ L hEm),
        ← integral_indicator_one ((hmeas C) (measurable_shiftCoords γ L hEm))]
      refine integral_congr_ae ?_
      refine ae_palmLaw_of_ae P ν a b (R := fun p => G (p.1, palmShiftRight (ν p.1) ℓ p.2) =
        (zoomCoords γ C h ⁻¹' (shiftCoords γ L ⁻¹' E)).indicator 1 p) ?_
      filter_upwards [hae] with ω hω x
      obtain ⟨he, hg, hat, hpo, hinf, hsc⟩ := hω
      have key := shiftCoords_zoomCoords (C := C) hγ hL hg (fun t => by rw [← he]; exact hat t)
        (fun u v huv => by rw [← he]; exact hpo u v huv) (fun x => by rw [← he]; exact hinf x)
        hsc x
      rw [← he] at key
      have key' : zoomCoords γ C h (ω, palmShiftRight (ν ω) ℓ x) =
          shiftCoords γ L (zoomCoords γ C h (ω, x)) := key.symm
      have hmem : (ω, palmShiftRight (ν ω) ℓ x) ∈ zoomCoords γ C h ⁻¹' E ↔
          (ω, x) ∈ zoomCoords γ C h ⁻¹' (shiftCoords γ L ⁻¹' E) := by
        rw [mem_preimage, mem_preimage, mem_preimage, key']
      show G (ω, palmShiftRight (ν ω) ℓ x) = _
      rw [hGdef]
      by_cases hm : (ω, x) ∈ zoomCoords γ C h ⁻¹' (shiftCoords γ L ⁻¹' E)
      · rw [indicator_of_mem (hmem.2 hm), indicator_of_mem hm]; rfl
      · rw [indicator_of_notMem (mt hmem.1 hm), indicator_of_notMem hm]
    rw [← hint1, ← hint2, Real.norm_eq_abs]
    refine hA6.trans (le_of_eq ?_)
    rw [hℓ]

/-! ## 5. Assembly -/

end Raw
end FieldLaw
end S5
end QuantumZipper
