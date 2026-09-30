import QuantumZipper.Proofs.Zipper.E5Asm2
import QuantumZipper.Proofs.Loewner.ReverseHolo

/-!
# E5-ASM, part 3: joint measurability of the collision target coordinates at the level point

Task E5-ASM (Theorem 1.3, node E5). Discharges the coordinate input `hcm` of
`E5Asm1.measurable_modelInt_of_coords` (via `measurable_coords_target_of_level`) for the D28
field `X' = regField ϖ ρ₀ ∘ X₁`:

`(ℓ, ω, ω') ↦ coordsFull (targetColl κ (Vr κ T B ω) (T − T_ℓ) ϖ (X' ω'))` is measurable.

The collision target field is `(ofFun sh + X') − (ofFun sh + X')(ϖ_τ) − q_τ` with
`sh = 𝔥₀ + (γ/2)(neumannH 0 · − k_{ϖ_τ})`, `ϖ_τ = (revMap V τ)_* ϖ`. With the jointly measurable
reverse maps `revL` (`E5Asm2.measurable_revMap_level`):

* `derivL`: a jointly measurable version of `deriv (revMap V τ)` on `ℍ` (difference quotients,
  as `CharFun.Dm`), so `q_τ` is measurable;
* `k_{ϖ_τ}(u) = ∫ neumannH u (revL w) dϖ(w)` and the circle and `ϖ_τ` integrals of `sh` are
  parametric integrals of jointly measurable functions (`StronglyMeasurable.integral_prod_right'`);
* `X'(ϖ_τ)` is `E5Asm2.measurable_regField_level`.

Own elementary measure-theoretic arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov StrongMarkov B2 E1 E4Grid CoordsFull

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- The level collision time `τ = T − T_ℓ`. -/
def tauL (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω)
    (z : ℝ≥0 × NullMeasurableSpace Ω P) : ℝ :=
  T - ((levelTime (lenA κ T B X) T.toNNReal z.1 (ofCompl P z.2) : ℝ≥0) : ℝ)

/-- The reverse map at the level point. -/
def revL (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω)
    (z : ℝ≥0 × NullMeasurableSpace Ω P) (u : ℂ) : ℂ :=
  revMap (Vr κ T B (ofCompl P z.2)) (tauL κ T B X P z) u

/-- Difference-quotient version of `deriv (revMap V τ)`. -/
def derivL (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω)
    (p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ) : ℂ :=
  limUnder atTop fun n => (CharFun.hstep n)⁻¹ •
    (revL κ T B X P p.1 (p.2 + CharFun.hstep n) - revL κ T B X P p.1 p.2)

theorem measurable_revL (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω)) :
    Measurable fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ => revL κ T B X P p.1 p.2 :=
  measurable_revMap_level hS hBc

theorem measurable_derivL (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω)) :
    Measurable (derivL κ T B X P) := by
  have hR := measurable_revL hS hBc
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  refine Measurable.stronglyMeasurable ?_
  exact ((hR.comp (measurable_fst.prodMk (measurable_snd.add_const _))).sub hR).const_smul
    ((CharFun.hstep n)⁻¹ : ℂ)

omit [IsProbabilityMeasure P] in
theorem tauL_nonneg (hT : 0 < T) (z : ℝ≥0 × NullMeasurableSpace Ω P) : 0 ≤ tauL κ T B X P z :=
  (levelArg_mem_Icc (κ := κ) (B := B) (X := X) hT z.1 (ofCompl P z.2)).1

omit [IsProbabilityMeasure P] in
theorem derivL_eq (hT : 0 < T) (hBc : ∀ ω, Continuous (B · ω))
    (z : ℝ≥0 × NullMeasurableSpace Ω P) {u : ℂ} (hu : u ∈ H) :
    derivL κ T B X P (z, u) = deriv (revMap (Vr κ T B (ofCompl P z.2)) (tauL κ T B X P z)) u := by
  have hd := hasDerivAt_revMap _ (continuous_Vr_e5 (κ := κ) (T := T)
    (hBc (ofCompl P z.2))) (tauL_nonneg (κ := κ) (B := B) (X := X) hT z) hu
  have ht := hd.tendsto_slope_zero
  have hs : Tendsto CharFun.hstep atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      mem_compl_singleton_iff.2 (Complex.ofReal_ne_zero.2 (by positivity))⟩
    have := (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Complex.ofReal_zero] at this
    exact this
  rw [hd.deriv]
  exact (ht.comp hs).limUnder_eq

/-- `q_τ` at the level point is measurable. -/
theorem measurable_qt_level (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω)) :
    Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      qt κ (Vr κ T B (ofCompl P z.2)) (tauL κ T B X P z) ϖ := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := id hS
  have := hϖ.prob
  have e : (fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      qt κ (Vr κ T B (ofCompl P z.2)) (tauL κ T B X P z) ϖ) =
      fun z => Qc (Real.sqrt κ) * ∫ v, Real.log ‖derivL κ T B X P (z, v)‖ ∂ϖ := by
    funext z
    simp only [qt]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hϖ.ae_mem_H] with v hv
    rw [derivL_eq hT hBc z hv]
  rw [e]
  have hm : Measurable fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      Real.log ‖derivL κ T B X P p‖ :=
    Real.measurable_log.comp (measurable_derivL hS hBc).norm
  exact measurable_const.mul (hm.stronglyMeasurable.integral_prod_right').measurable

/-- `k_{ϖ_τ}` at the level point, as an integral against `ϖ`. -/
theorem kPot_varpiT_level_eq (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    (z : ℝ≥0 × NullMeasurableSpace Ω P) (u : ℂ) :
    PalmNorm.kPot (varpiT (Vr κ T B (ofCompl P z.2)) (tauL κ T B X P z) ϖ) u =
      ∫ w, neumannH u (revL κ T B X P z w) ∂ϖ := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := id hS
  have hm := TwoPoint.measurable_revMap (continuous_Vr_e5 (κ := κ) (T := T)
    (hBc (ofCompl P z.2))) (tauL_nonneg (κ := κ) (B := B) (X := X) hT z)
  simp only [PalmNorm.kPot, varpiT]
  rw [integral_map hm.aemeasurable]
  · rfl
  · exact (measurable_neumannH.comp (measurable_const.prodMk measurable_id) :
      Measurable fun w => neumannH u w).aestronglyMeasurable

theorem measurable_kPot_level (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω)) :
    Measurable fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      PalmNorm.kPot (varpiT (Vr κ T B (ofCompl P p.1.2)) (tauL κ T B X P p.1) ϖ) p.2 := by
  have e : (fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      PalmNorm.kPot (varpiT (Vr κ T B (ofCompl P p.1.2)) (tauL κ T B X P p.1) ϖ) p.2) =
      fun p => ∫ w, neumannH p.2 (revL κ T B X P p.1 w) ∂ϖ :=
    funext fun p => kPot_varpiT_level_eq hS hBc p.1 p.2
  rw [e]
  have := hS.2.2.2.2.2.2.prob
  have hR := measurable_revL hS hBc
  have hF : Measurable fun q : ((ℝ≥0 × NullMeasurableSpace Ω P) × ℂ) × ℂ =>
      neumannH q.1.2 (revL κ T B X P q.1.1 q.2) :=
    measurable_neumannH.comp ((measurable_snd.comp measurable_fst).prodMk
      (hR.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  exact (hF.stronglyMeasurable.integral_prod_right').measurable

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The circle coordinates of the collision target field, unfolded. -/
theorem coordsFull_targetColl_apply (V : ℝ → ℝ) (t : ℝ) (Y : FieldSample) (i : ℕ) :
    coordsFull (targetColl κ V t ϖ Y) i =
      ((∫ u, PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0 u
          ∂foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) +
        Y (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) +
        -((∫ u, PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0 u ∂varpiT V t ϖ) +
            Y (varpiT V t ϖ)) *
          ((foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) univ).toReal) +
      -(qt κ V t ϖ) *
        ((foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) univ).toReal := rfl

/-- The shift function at the level point is jointly measurable. -/
theorem measurable_shiftFun_level (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω)) :
    Measurable fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
        (varpiT (Vr κ T B (ofCompl P p.1.2)) (tauL κ T B X P p.1) ϖ) 0 p.2 := by
  unfold PalmNorm.shiftFun
  refine ((UnzipInvariance.measurable_h0rev κ).comp measurable_snd).add
    (measurable_const.mul (Measurable.sub ?_ (measurable_kPot_level hS hBc)))
  exact measurable_neumannH.comp (measurable_const.prodMk measurable_snd)

/-- **The coordinate input `hcm`** (with the level time) for `X' = regField ϖ ρ₀ ∘ X₁`. -/
theorem measurable_coords_targetColl_level {Ω' : Type} [MeasurableSpace Ω']
    {X₁ : Ω' → FieldSample} (hXm : ∀ μ, Measurable fun ω' => X₁ ω' μ) (ρ₀ : Measure ℂ)
    (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω)) :
    Measurable fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' =>
      coordsFull (targetColl κ (Vr κ T B (ofCompl P z.1.2))
        (T - ((levelTime (lenA κ T B X) T.toNNReal z.1.1 (ofCompl P z.1.2) : ℝ≥0) : ℝ)) ϖ
          (regField ϖ ρ₀ (X₁ z.2))) := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := id hS
  have := hϖ.prob
  have hsh := measurable_shiftFun_level hS hBc
  have hR := measurable_revL hS hBc
  refine measurable_pi_iff.2 fun i => ?_
  simp only [coordsFull_targetColl_apply]
  set fc := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2
  -- the `ϖ_τ`-integral of the shift function, as a `ϖ`-integral
  have e2 : ∀ z : ℝ≥0 × NullMeasurableSpace Ω P,
      (∫ u, PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
          (varpiT (Vr κ T B (ofCompl P z.2)) (tauL κ T B X P z) ϖ) 0 u
          ∂varpiT (Vr κ T B (ofCompl P z.2)) (tauL κ T B X P z) ϖ) =
        ∫ w, PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
          (varpiT (Vr κ T B (ofCompl P z.2)) (tauL κ T B X P z) ϖ) 0 (revL κ T B X P z w) ∂ϖ := by
    intro z
    have hm := TwoPoint.measurable_revMap (continuous_Vr_e5 (κ := κ) (T := T)
      (hBc (ofCompl P z.2))) (tauL_nonneg (κ := κ) (B := B) (X := X) hT z)
    rw [varpiT, integral_map hm.aemeasurable]
    · rfl
    · exact (hsh.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hA : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      ∫ u, PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
        (varpiT (Vr κ T B (ofCompl P z.2)) (tauL κ T B X P z) ϖ) 0 u ∂fc :=
    (hsh.stronglyMeasurable.integral_prod_right').measurable
  have hC : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      ∫ u, PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
          (varpiT (Vr κ T B (ofCompl P z.2)) (tauL κ T B X P z) ϖ) 0 u
          ∂varpiT (Vr κ T B (ofCompl P z.2)) (tauL κ T B X P z) ϖ := by
    rw [funext e2]
    have hF : Measurable fun q : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
        PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
          (varpiT (Vr κ T B (ofCompl P q.1.2)) (tauL κ T B X P q.1) ϖ) 0 (revL κ T B X P q.1 q.2) :=
      hsh.comp (measurable_fst.prodMk hR)
    exact (hF.stronglyMeasurable.integral_prod_right').measurable
  have hY1 : Measurable fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' => regField ϖ ρ₀ (X₁ z.2) fc :=
    (measurable_regField_coord hXm ϖ ρ₀ fc).comp measurable_snd
  have hY2 := measurable_regField_level (κ := κ) (T := T) (B := B) (X := X) hXm ρ₀ hS hBc
  have hq := measurable_qt_level hS hBc
  exact (((hA.comp measurable_fst).add hY1).add
    (((hC.comp measurable_fst).add hY2).neg.mul measurable_const)).add
    ((hq.comp measurable_fst).neg.mul measurable_const)

end E5
end QuantumZipper
