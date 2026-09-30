import QuantumZipper.Proofs.Zipper.E5HW0
import QuantumZipper.Proofs.Zipper.E5ESM8
import QuantumZipper.Proofs.Zipper.UnifUGTip
import QuantumZipper.Proofs.Zipper.MeasUnzipField
import QuantumZipper.Proofs.Zipper.F2Gamma0Trunc

/-!
# E5-HW0, part 3: the literal `hw0` for a version of `B` that is good at every sample

Task E5-ASM (Theorem 1.3, node E5). `E5.e5_esm_model` (`E5ESM7`) takes the hypothesis `hw0`:
**literal** measurability of `z ↦ w0 κ T B X ϖ δ z.1 (ofCompl P z.2)` on the level space
`ℝ≥0 × NullMeasurableSpace Ω P`. The Palm point `x(ℓ) = 0₋(T − T_ℓ)` is controlled only on the
conull set where the `0₋` facts hold, and a function on `Borel ⊗ NS(P)` is not measurable just
because it agrees with a measurable one off `ℝ≥0 × N` (`N` null): its sections over `N` matter.
So we first pass to a **version** of `B` whose paths are good at *every* sample:

* `GoodVr κ T V`: the `0₋` facts of `Wire2.ae_zeroMinus_Vr_facts` and the simple-curve property of
  the reversed hull (`B5.ae_isSimpleCurveHull_revHull_Vr`, Rohde–Schramm input), for one path;
* `exists_goodVersion`: every E5 setup has a version `B'` with continuous paths, again an E5 setup,
  with `GoodVr` at **every** sample and the same left side and Palm mass (the version of
  `e5_setup_version`, redefined on a null set by the path of one fixed good sample);
* `aemeasurable_mReg`: `ω ↦ mReg = evalReg h⁰ ϖ` is a.e.-measurable (`evalReg` only reads
  `avgReg`, and `avgReg h⁰` is a.s. that of the measurable unzipping `MeasUnzip.ufJ`, as in
  `RegUnif.aemeasurable_bdryApprox_h0f`);
* **`measurable_w0_level_good`**: the literal `hw0` for such a version.

Own elementary measure-theoretic arguments (Sheffield, arXiv:1012.4797, §5.4, pp. 66–72, uses
these random variables without discussing measurability).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov StrongMarkov B2 B5 CharFun RegCont UnzipInvariance RegUnif

/-- **Good reversed driver path**: the `0₋` facts of `Wire2.ae_zeroMinus_Vr_facts` and a simple
curve hull at time `T`. -/
def GoodVr (κ T : ℝ) (V : ℝ → ℝ) : Prop :=
  (zeroMinus V 0 = 0 ∧ zeroMinus V T < 0 ∧ StrictAntiOn (zeroMinus V) (Icc 0 T) ∧
    ContinuousOn (zeroMinus V) (Icc 0 T) ∧
    (∀ x ∈ Ioc (zeroMinus V T) 0,
      realHitTime V x = ENNReal.ofReal (realHitTime V x).toReal ∧
        (realHitTime V x).toReal ∈ Icc 0 T ∧ zeroMinus V (realHitTime V x).toReal = x) ∧
    (∀ x ≤ 0, realHitTime V x < ENNReal.ofReal T ↔ zeroMinus V T < x)) ∧
  IsSimpleCurveHull (revHull V T)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

theorem ae_goodVr (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hT : 0 < T) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, GoodVr κ T (Vr κ T B ω) := by
  filter_upwards [Wire2.ae_zeroMinus_Vr_facts hκ hκ4 hT P B hB,
    B5.ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4 hT P B hB] with ω h1 h2
  exact ⟨h1, h2⟩

/-- `mReg = evalReg h⁰ ϖ` is a.e.-measurable. -/
theorem aemeasurable_mReg (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hT : 0 < T)
    (ϖ : Measure ℂ) [SFinite ϖ] : AEMeasurable (fun ω => E1.mReg κ T B X ϖ ω) P := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hXm : Measurable fun ω => ofFun (h0rev κ) + X ω := by
    refine measurable_pi_iff.2 fun μ => ?_
    simp only [Pi.add_apply]
    exact measurable_const.add (hX.measurable_coord μ)
  have hFm : Measurable fun ω => MeasUnzip.ufJ hT.le (Real.sqrt κ) κ
      ((pathC T B' hB'c ω, ofFun (h0rev κ) + X ω), T) :=
    (MeasUnzip.measurable_ufJ hT.le _ κ).comp
      (((measurable_pathC T hB'm hB'c).prodMk hXm).prodMk measurable_const)
  refine ⟨fun ω => evalReg (MeasUnzip.ufJ hT.le (Real.sqrt κ) κ
      ((pathC T B' hB'c ω, ofFun (h0rev κ) + X ω), T)) ϖ,
    (measurable_evalReg ϖ).comp hFm, ?_⟩
  have hq : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  filter_upwards [ae_pathC_good hB hB'c hB'eq hT, hB'eq] with ω hgood heq
  have hf0 := Wof_zero_of_GoodP hT.le κ hgood
  obtain ⟨hdc, hd0, hEq⟩ := drive_facts κ hB'c hT heq hf0
  have hmap := fwdMapInv_congr hdc hd0 (continuous_Wof κ T hT.le _) hf0 hEq hq
  have hav : avgReg (h0f κ T B X ω) = avgReg (MeasUnzip.ufJ hT.le (Real.sqrt κ) κ
      ((pathC T B' hB'c ω, ofFun (h0rev κ) + X ω), T)) := by
    rw [MeasUnzip.avgReg_ufJ hT.le _ κ hf0 hq, h0f_eq_unzippedField]
    funext j z
    unfold avgReg
    congr 1
    funext n
    exact coordChange_congr_of_eqOn hmap
      (ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos j))) _ _
  exact F2.evalReg_congr_avgReg hav ϖ

omit [IsProbabilityMeasure P] in
/-- The level argument `T − T_ℓ` lies in `[0, T]`. -/
theorem levelArg_mem_Icc (hT : 0 < T) (ℓ : ℝ≥0) (ω : Ω) :
    T - ((levelTime (lenA κ T B X) T.toNNReal ℓ ω : ℝ≥0) : ℝ) ∈ Icc 0 T := by
  refine ⟨?_, sub_le_self _ (by positivity)⟩
  rw [sub_nonneg]
  refine (NNReal.coe_le_coe.2 (levelTime_le (continuous_lenA hT.le) (monotone_lenA hT.le)
    T.toNNReal ℓ ω)).trans ?_
  exact (Real.coe_toNNReal T hT.le).le

/-- **Good continuous version of an E5 setup.** -/
theorem exists_goodVersion (hS : E5.Setup κ T P B X ϖ) :
    ∃ B' : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (B' · ω)) ∧ E5.Setup κ T P B' X ϖ ∧
      (∀ ω, GoodVr κ T (Vr κ T B' ω)) ∧
      (∀ {L : Type*} (loc : ℕ → FieldSample × (ℝ → ℝ) → L) (δ : ℝ) (R : ℕ),
        lhsF loc κ T P B' X ϖ δ R = lhsF loc κ T P B X ϖ δ R) ∧
      ∀ δ : ℝ, pmass κ T P B' X ϖ δ = pmass κ T P B X ϖ δ := by
  classical
  obtain ⟨B'', hc, hS'', hlhs, hpm⟩ := e5_setup_version hS
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := hS''
  have hG := ae_goodVr hκ hκ4.le hT hB
  set N := toMeasurable P {ω | ¬ GoodVr κ T (Vr κ T B'' ω)} with hNdef
  have hN : P N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hG
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀, ω₀ ∉ N := by
    by_contra h
    push Not at h
    have hU : N = univ := eq_univ_of_forall h
    rw [hU, measure_univ] at hN
    exact one_ne_zero hN
  have hG₀ : GoodVr κ T (Vr κ T B'' ω₀) := by
    by_contra h
    exact hω₀ (subset_toMeasurable _ _ h)
  set B' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ N then B'' t ω₀ else B'' t ω with hB'def
  have hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B'' t ω := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with ω hω t
    simp only [hB'def, if_neg hω]
  have hpath : pathOf B' =ᵐ[P] pathOf B'' := hae.mono fun ω h => funext h
  have hcont : ∀ ω, Continuous (B' · ω) := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [hB'def, if_pos hω]; exact hc ω₀
    · simp only [hB'def, if_neg hω]; exact hc ω
  have hB' : IsBrownianReal B' P :=
    ⟨hB.toIsPreBrownianReal.congr fun t => hae.mono fun ω h => (h t).symm,
      ae_of_all _ hcont⟩
  refine ⟨B', hcont, ⟨hκ, hκ4, hT, hB', hX, hind.congr hpath.symm (ae_eq_refl _), hϖ⟩,
    fun ω => ?_, fun loc δ R => (lhsF_congr_ae loc hae δ R).trans (hlhs loc δ R),
    fun δ => (pmass_congr_ae hae δ).trans (hpm δ)⟩
  by_cases hω : ω ∈ N
  · have e : Vr κ T B' ω = Vr κ T B'' ω₀ := by
      funext s; simp only [Vr, vrev, drive, hB'def, if_pos hω]
    rw [e]; exact hG₀
  · have e : Vr κ T B' ω = Vr κ T B'' ω := by
      funext s; simp only [Vr, vrev, drive, hB'def, if_neg hω]
    rw [e]
    by_contra h
    exact hω (subset_toMeasurable _ _ h)

/-- **`hw0`, literal form**, for a continuous version that is good at every sample. -/
theorem measurable_w0_level_good (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    (hG : ∀ ω, GoodVr κ T (Vr κ T B ω)) (δ : ℝ) :
    Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P => w0 κ T B X ϖ δ z.1 (ofCompl P z.2) := by
  classical
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := hS
  have := hϖ.prob
  refine measurable_w0_level_of hκ hκ4 hT hB hX hind hBc ?_ ?_ δ
  · exact (aemeasurable_mReg hB hX hT ϖ).nullMeasurable.measurable'.comp measurable_snd
  · set g : ℚ → ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞ := fun q z =>
      if (q : ℝ) < 0 then realHitTime (Vr κ T B (ofCompl P z.2)) q else 0 with hgdef
    have hg : ∀ q, Measurable (g q) := by
      intro q
      by_cases hq : (q : ℝ) < 0
      · have h1 : Measurable fun ω : NullMeasurableSpace Ω P =>
            realHitTime (Vr κ T B (ofCompl P ω)) q :=
          (aemeasurable_realHitTime_Vr hB κ hT.le hq).nullMeasurable.measurable'
        simp only [hgdef, if_pos hq]
        exact h1.comp measurable_snd
      · simp only [hgdef, if_neg hq]
        exact measurable_const
    have e : (fun z : ℝ≥0 × NullMeasurableSpace Ω P => xL κ T B X z.1 (ofCompl P z.2)) =
        fun z => xLm κ T B X P g z := by
      funext z
      have hs := levelArg_mem_Icc (κ := κ) (B := B) (X := X) hT z.1 (ofCompl P z.2)
      have h := zetaHatS_eq_zeroMinus_of (B := fun t (z : ℝ≥0 × NullMeasurableSpace Ω P) =>
        B t (ofCompl P z.2)) (ω := z) (g := g) hT (hG (ofCompl P z.2)).1
        (fun q hq => by simp only [hgdef, if_pos hq]; rfl) _ hs
      exact h.symm
    rw [e]
    exact measurable_xLm hκ hκ4 hT hB hX hind hBc hg

end E5
end QuantumZipper
