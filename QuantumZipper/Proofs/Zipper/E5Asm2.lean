import QuantumZipper.Proofs.Zipper.E5Asm1
import QuantumZipper.Proofs.Zipper.UnifRC3Det
import QuantumZipper.Proofs.Zipper.E5JointMeasCore

/-!
# E5-ASM, part 2: joint measurability of the reverse maps at the level time

Task E5-ASM (Theorem 1.3, node E5). The remaining input of `measurable_modelInt_of_coords`
(`E5Asm1`) is joint measurability of the circle coordinates of the collision target field at the
level point, whose three random ingredients (`X'(ϖ_τ)`, `k_{ϖ_τ}`, `q_τ` with
`ϖ_τ = (revMap (Vr κ T B ω) τ)_* ϖ`, `τ = T − T_ℓ`) all read the reverse Loewner maps at the
random time. Here the basic fact is proved:

* `vrPath`, `Vr_eq_vrPath`: the reversed driver `Vr κ T B ω` is a fixed continuous functional of
  the path `B|_{[0,T]} ∈ C([0,T], ℝ)`;
* `continuous_revMap_vrPath`: for fixed `t ≥ 0`, `z ∈ ℍ`, the reverse map is Lipschitz in that
  path (`ReverseFlow.norm_revMap_sub_revMap_le`, Grönwall);
* **`measurable_revMap_level`**: `(ℓ, ω, u) ↦ revMap (Vr κ T B ω) (T − T_ℓ) u` is jointly
  measurable on `(ℝ≥0 × NullMeasurableSpace Ω P) × ℂ` (Carathéodory: continuous in `(t, u)` on
  `[0, ∞) × ℍ` by `RegUnif.continuousOn_revMap_family`, measurable in the path; `0` off `ℍ`).

Own elementary measure-theoretic argument (Carathéodory functions).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov StrongMarkov B2 E1

/-- The reversed driver as a functional of the path `f = B|_{[0,T]}`. -/
def vrPath (κ T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) : ℝ → ℝ := fun s =>
  Real.sqrt κ * f (projIcc 0 T hT (T - min (max s 0) T)) - Real.sqrt κ * f (projIcc 0 T hT T)

theorem continuous_vrPath (κ T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) :
    Continuous (vrPath κ T hT f) := by
  unfold vrPath
  refine (continuous_const.mul (f.continuous.comp (continuous_projIcc.comp
    (continuous_const.sub ((continuous_id.max continuous_const).min continuous_const))))).sub
    continuous_const

theorem abs_vrPath_sub_le (κ T : ℝ) (hT : 0 ≤ T) (f f' : C(Icc (0 : ℝ) T, ℝ)) (s : ℝ) :
    |vrPath κ T hT f s - vrPath κ T hT f' s| ≤ 2 * Real.sqrt κ * dist f f' := by
  unfold vrPath
  have h1 := ContinuousMap.dist_apply_le_dist (f := f) (g := f')
    (projIcc 0 T hT (T - min (max s 0) T))
  have h2 := ContinuousMap.dist_apply_le_dist (f := f) (g := f') (projIcc 0 T hT T)
  rw [Real.dist_eq] at h1 h2
  have hk := Real.sqrt_nonneg κ
  calc _ = |Real.sqrt κ * (f (projIcc 0 T hT (T - min (max s 0) T)) -
          f' (projIcc 0 T hT (T - min (max s 0) T))) -
          Real.sqrt κ * (f (projIcc 0 T hT T) - f' (projIcc 0 T hT T))| := by ring_nf
    _ ≤ |Real.sqrt κ * (f (projIcc 0 T hT (T - min (max s 0) T)) -
          f' (projIcc 0 T hT (T - min (max s 0) T)))| +
          |Real.sqrt κ * (f (projIcc 0 T hT T) - f' (projIcc 0 T hT T))| := abs_sub _ _
    _ ≤ Real.sqrt κ * dist f f' + Real.sqrt κ * dist f f' := by
        rw [abs_mul, abs_mul, abs_of_nonneg hk]
        gcongr
    _ = 2 * Real.sqrt κ * dist f f' := by ring

/-- The path `B|_{[0,T]}` as a point of `C([0,T], ℝ)`. -/
def pathIcc {Ω : Type*} (T : ℝ) (B : ℝ≥0 → Ω → ℝ) (hBc : ∀ ω, Continuous (B · ω)) (ω : Ω) :
    C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun x => B x.1.toNNReal ω, (hBc ω).comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩

theorem Vr_eq_vrPath {Ω : Type*} {κ T : ℝ} (hT : 0 ≤ T) {B : ℝ≥0 → Ω → ℝ}
    (hBc : ∀ ω, Continuous (B · ω)) (ω : Ω) :
    Vr κ T B ω = vrPath κ T hT (pathIcc T B hBc ω) := by
  funext s
  have hm : T - min (max s 0) T ∈ Icc (0 : ℝ) T :=
    ⟨sub_nonneg.2 (min_le_right _ _), sub_le_self _ (le_min (le_max_right _ _) hT)⟩
  simp only [vrPath, pathIcc, ContinuousMap.coe_mk, projIcc_of_mem hT hm,
    projIcc_of_mem hT ⟨hT, le_rfl⟩]
  simp only [Vr, vrev, drive]

/-- For fixed `t ≥ 0` and `z ∈ ℍ`, the reverse map is continuous in the path. -/
theorem continuous_revMap_vrPath (κ T : ℝ) (hT : 0 ≤ T) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : 0 < z.im) : Continuous fun f : C(Icc (0 : ℝ) T, ℝ) => revMap (vrPath κ T hT f) t z := by
  have hL : LipschitzWith ⟨2 * Real.sqrt κ * Real.exp (2 * t / z.im ^ 2), by positivity⟩
      fun f : C(Icc (0 : ℝ) T, ℝ) => revMap (vrPath κ T hT f) t z := by
    refine LipschitzWith.of_dist_le_mul fun f f' => ?_
    rw [dist_eq_norm]
    have := ReverseFlow.norm_revMap_sub_revMap_le _ _ (continuous_vrPath κ T hT f)
      (continuous_vrPath κ T hT f') z hz ht (ε := 2 * Real.sqrt κ * dist f f')
      (fun r _ => abs_vrPath_sub_le κ T hT f f' r)
    refine this.trans (le_of_eq ?_)
    show 2 * Real.sqrt κ * dist f f' * Real.exp (2 * t / z.im ^ 2) =
      (2 * Real.sqrt κ * Real.exp (2 * t / z.im ^ 2)) * dist f f'
    ring
  exact hL.continuous

/-- The Carathéodory family on `(ℝ × ℍ) × C([0,T], ℝ)`. -/
theorem measurable_revMap_vrPath_uncurry (κ T : ℝ) (hT : 0 ≤ T) :
    Measurable fun p : (ℝ × {z : ℂ // 0 < z.im}) × C(Icc (0 : ℝ) T, ℝ) =>
      revMap (vrPath κ T hT p.2) (max p.1.1 0) p.1.2.1 := by
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun (i : ℝ × {z : ℂ // 0 < z.im}) (f : C(Icc (0 : ℝ) T, ℝ)) =>
      revMap (vrPath κ T hT f) (max i.1 0) i.2.1) (fun f => ?_) (fun i => ?_)
  · have hV : Continuous fun p : ℝ × ℝ => vrPath κ T hT f p.2 :=
      (continuous_vrPath κ T hT f).comp continuous_snd
    have hc := RegUnif.continuousOn_revMap_family (V := fun _ : ℝ => vrPath κ T hT f) hV
    refine hc.comp_continuous (f := fun i : ℝ × {z : ℂ // 0 < z.im} => ((0 : ℝ), max i.1 0, i.2.1))
      (by fun_prop) fun i => ⟨le_max_right _ _, i.2.2⟩
  · exact (continuous_revMap_vrPath κ T hT (le_max_right i.1 0) i.2.2).measurable

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **The reverse maps at the level time are jointly measurable** on the level space `× ℂ`. -/
theorem measurable_revMap_level (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω)) :
    Measurable fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      revMap (Vr κ T B (ofCompl P p.1.2))
        (T - ((levelTime (lenA κ T B X) T.toNNReal p.1.1 (ofCompl P p.1.2) : ℝ≥0) : ℝ)) p.2 := by
  classical
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, -⟩ := id hS
  set τ : ℝ≥0 × NullMeasurableSpace Ω P → ℝ := fun z =>
    T - ((levelTime (lenA κ T B X) T.toNNReal z.1 (ofCompl P z.2) : ℝ≥0) : ℝ) with hτ
  have hτm : Measurable τ := measurable_const.sub
    (NNReal.continuous_coe.measurable.comp (measurable_levelTime_level hκ hκ4 hT hB hX hind hBc))
  have hτ0 : ∀ z, 0 ≤ τ z := fun z => (levelArg_mem_Icc (X := X) hT z.1 (ofCompl P z.2)).1
  have hg : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P => pathIcc T B hBc (ofCompl P z.2) :=
    ContinuousMap.measurable_iff_eval.2 fun x =>
      (measurable_B_compl hB x.1.toNNReal).comp measurable_snd
  set S : Set ((ℝ≥0 × NullMeasurableSpace Ω P) × ℂ) := {p | 0 < p.2.im} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const (Complex.measurable_im.comp
    measurable_snd)
  set F : S → ℂ := fun q => revMap (vrPath κ T hT.le (pathIcc T B hBc (ofCompl P q.1.1.2)))
    (max (τ q.1.1) 0) q.1.2 with hFdef
  have e : (fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      revMap (Vr κ T B (ofCompl P p.1.2)) (τ p.1) p.2) = fun p =>
      if hp : p ∈ S then F ⟨p, hp⟩ else (0 : ℂ) := by
    funext p
    split_ifs with hp
    · rw [Vr_eq_vrPath hT.le hBc, hFdef]
      simp only [max_eq_left (hτ0 p.1)]
    · exact CharFun.revMap_of_not_mem (hτ0 p.1) hp
  show Measurable fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
    revMap (Vr κ T B (ofCompl P p.1.2)) (τ p.1) p.2
  rw [e]
  refine Measurable.dite (f := F) (g := fun _ => (0 : ℂ)) ?_ measurable_const hSm
  have hin : Measurable fun q : S =>
      (((τ q.1.1, ⟨q.1.2, q.2⟩) : ℝ × {z : ℂ // 0 < z.im}),
        pathIcc T B hBc (ofCompl P q.1.1.2)) :=
    ((hτm.comp (measurable_fst.comp measurable_subtype_coe)).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk)).prodMk
      (hg.comp (measurable_fst.comp measurable_subtype_coe))
  exact (measurable_revMap_vrPath_uncurry κ T hT.le).comp hin

/-- **The pushed normalizer at the level time is a measurable family of measures.** -/
theorem measurable_varpiT_level (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    {A : Set ℂ} (hA : MeasurableSet A) :
    Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      varpiT (Vr κ T B (ofCompl P z.2))
        (T - ((levelTime (lenA κ T B X) T.toNNReal z.1 (ofCompl P z.2) : ℝ≥0) : ℝ)) ϖ A := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := id hS
  have := hϖ.prob
  have hR := measurable_revMap_level hS hBc
  have e : (fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      varpiT (Vr κ T B (ofCompl P z.2))
        (T - ((levelTime (lenA κ T B X) T.toNNReal z.1 (ofCompl P z.2) : ℝ≥0) : ℝ)) ϖ A) =
      fun z => ∫⁻ v, A.indicator 1 (revMap (Vr κ T B (ofCompl P z.2))
        (T - ((levelTime (lenA κ T B X) T.toNNReal z.1 (ofCompl P z.2) : ℝ≥0) : ℝ)) v) ∂ϖ := by
    funext z
    have hm := TwoPoint.measurable_revMap (continuous_Vr_e5 (κ := κ) (T := T)
      (hBc (ofCompl P z.2))) (levelArg_mem_Icc (κ := κ) (B := B) (X := X) hT z.1 (ofCompl P z.2)).1
    rw [varpiT, Measure.map_apply hm hA, ← lintegral_indicator_one (hm hA)]
    rfl
  rw [e]
  exact ((measurable_one.indicator hA).comp hR).lintegral_prod_right'

/-- **The regular version of `X'` at the random measure `ϖ_{T−T_ℓ}` is jointly measurable**
(decision D28; `measurable_regField_varpiT_prod` with the family `measurable_varpiT_level`). -/
theorem measurable_regField_level {Ω' : Type} [MeasurableSpace Ω'] {X₁ : Ω' → FieldSample}
    (hXm : ∀ μ, Measurable fun ω' => X₁ ω' μ) (ρ₀ : Measure ℂ) (hS : E5.Setup κ T P B X ϖ)
    (hBc : ∀ ω, Continuous (B · ω)) :
    Measurable fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' =>
      regField ϖ ρ₀ (X₁ p.2) (varpiT (Vr κ T B (ofCompl P p.1.2))
        (T - ((levelTime (lenA κ T B X) T.toNNReal p.1.1 (ofCompl P p.1.2) : ℝ≥0) : ℝ)) ϖ) := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := id hS
  have hτ0 := fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
    (levelArg_mem_Icc (κ := κ) (B := B) (X := X) hT z.1 (ofCompl P z.2)).1
  have hV := fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
    continuous_Vr_e5 (κ := κ) (T := T) (hBc (ofCompl P z.2))
  exact measurable_regField_varpiT_prod hXm ρ₀ _ (fun A hA => measurable_varpiT_level hS hBc hA)
    (fun z => isProbabilityMeasure_varpiT hϖ (hV z) (hτ0 z))
    (fun z => ⟨(isProbabilityMeasure_varpiT hϖ (hV z) (hτ0 z)).measure_univ, _, hV z, _, hτ0 z,
      rfl⟩)

end E5
end QuantumZipper
