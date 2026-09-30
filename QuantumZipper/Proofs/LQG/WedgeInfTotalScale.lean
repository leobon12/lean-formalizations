import QuantumZipper.Proofs.LQG.InfiniteMass
import QuantumZipper.Field.CoordsFull

/-!
# WEDGE-INF-2, scaling tools: full normalized coordinates and radial averages

Reusable tools for exact-scaling arguments that read radial averages `radAvgReg` at radii `> 1`
(which the dyadic coordinates `Factorization.coords` do not record, only `coordsFull` does).

* `normCF x i = x(fc_i) − x(fc(0,1))` along all circles of `coordsFull` (positive dyadic
  radii); `map_normCF_rescale`: for the free field its law is invariant under
  `x ↦ rescale x Q b` (the full-coordinate version of `InfMass.map_normC_rescale`, same proof:
  kernel invariance `WedgeTK.kernelCov2_map_mul` and `WedgeTK.map_gaussFam_eq`).
* `reconF`: measurable reconstruction of a field sample from `coordsFull`, with
  `coordsFull (reconF (coordsFull x)) = coordsFull x`; `normCF_eq`: `normCF x` are the full
  coordinates of `x − x(fc(0,1))`.
* `RadLim x f`: the raw semicircle values about `0` converge to a function `f` continuous on
  `(0,∞)`. Then `radAvgReg x = f` on `(0,∞)`; it holds for `GoodRad` samples, is preserved by
  adding constants (`f + c`) and holds for `rescale x Q s` of a regular sample
  (`f r = F(0, s r) + Q log s`).

All arguments are elementary (own arguments); the law invariance is the scaling argument of
Duplantier–Sheffield, *Liouville quantum gravity and KPZ* (arXiv:0808.1560), as formalized in
`InfiniteMass.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper

namespace WedgeInf

open Factorization CoordsFull InfMass

/-! ## 1. Full normalized coordinates -/

/-- The `i`-th circle of `coordsFull`. -/
def fcF (i : ℕ) : Measure ℂ := foldedCircle (fullIndex i).1 (fullIndex i).2

instance isProbabilityMeasure_fcF (i : ℕ) : IsProbabilityMeasure (fcF i) := by
  unfold fcF; infer_instance

theorem fullIndex_pos (i : ℕ) : 0 < (fullIndex i).2 := by
  simp only [fullIndex]; positivity

theorem fcF_admissible (i : ℕ) : IsAdmissibleH (fcF i) := by
  rw [fcF, ← WedgeTK.fc_foldH_eq]
  exact isAdmissibleH_foldedCircle (CircleFubini.foldH_mem_Hbar' _) (fullIndex_pos i)

/-- Full normalized coordinates `x(fc_i) − x(fc(0,1))`. -/
def normCF (x : FieldSample) : ℕ → ℝ := fun i => x (fcF i) - x fc01

theorem fcF_univ (i : ℕ) : fcF i Set.univ = fc01 Set.univ := by
  simp only [fcF, fc01, measure_univ]

/-- The balanced pairs `(fc_i, fc(0,1))`. -/
def pF (i : ℕ) : WedgeTK.BPair := ⟨(fcF i, fc01), fcF_admissible i, fc01_admissible, fcF_univ i⟩

/-- Their images under `z ↦ b z`. -/
def qF {b : ℝ} (hb : 0 < b) (i : ℕ) : WedgeTK.BPair :=
  ⟨((fcF i).map fun u => (b : ℂ) * u, fc01.map fun u => (b : ℂ) * u),
    WedgeTK.isAdmissibleH_map_mul hb (fcF_admissible i),
    WedgeTK.isAdmissibleH_map_mul hb fc01_admissible,
    by rw [WedgeTK.map_univ_mul, WedgeTK.map_univ_mul, fcF_univ]⟩

section FreeField

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **Scale invariance of the full normalized coordinates** of the free field. -/
theorem map_normCF_rescale (hX : IsFreeGFFModConstH X P) {G : Ω → ℂ × ℝ → ℝ}
    (hG : WedgeTK.IsRegVersion X P G) (Q : ℝ) {b : ℝ} (hb : 0 < b) :
    P.map (fun ω => normCF (rescale (X ω) Q b)) = P.map (fun ω => normCF (X ω)) := by
  have h1 : (fun ω => normCF (X ω)) = fun ω i => WedgeTK.gaussFam X pF i ω := rfl
  have h01 := ae_evalReg_map_fc hG hb 0 one_pos
  have hI : ∀ᵐ ω ∂P, ∀ i, evalReg (X ω) ((fcF i).map fun u => (b : ℂ) * u) =
      X ω ((fcF i).map fun u => (b : ℂ) * u) :=
    ae_all_iff.2 fun i => ae_evalReg_map_fc hG hb _ (fullIndex_pos i)
  have h2 : (fun ω => normCF (rescale (X ω) Q b)) =ᵐ[P]
      fun ω i => WedgeTK.gaussFam X (qF hb) i ω := by
    filter_upwards [h01, hI] with ω h01 hI
    funext i
    simp only [normCF, WedgeTK.gaussFam, qF]
    have : IsProbabilityMeasure fc01 := by unfold fc01; infer_instance
    rw [rescale_fc_apply _ _ hb (fcF i), rescale_fc_apply _ _ hb fc01, hI i]
    rw [show fc01 = foldedCircle 0 1 from rfl]
    rw [h01]
    ring
  rw [Measure.map_congr h2, h1]
  exact WedgeTK.map_gaussFam_eq hX _ _ fun i j => WedgeTK.kernelCov2_map_mul hb (pF i) (pF j)

end FreeField

/-! ## 2. Reconstruction from the full coordinates -/

open Classical in
/-- Measurable reconstruction of a field sample from its full coordinates. -/
def reconF (c : ℕ → ℝ) : FieldSample := fun μ =>
  if h : ∃ i, fcF i = μ then c (Nat.find h) else 0

theorem measurable_reconF : Measurable reconF := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  unfold reconF
  by_cases h : ∃ i, fcF i = μ
  · simp only [dif_pos h]; exact measurable_pi_apply _
  · simp only [dif_neg h]; exact measurable_const

theorem coordsFull_reconF (x : FieldSample) : coordsFull (reconF (coordsFull x)) = coordsFull x := by
  classical
  funext i
  have h : ∃ j, fcF j = fcF i := ⟨i, rfl⟩
  show reconF (coordsFull x) (fcF i) = x (fcF i)
  simp only [reconF, dif_pos h]
  exact congrArg x (Nat.find_spec h)

theorem normCF_eq (x : FieldSample) : normCF x = coordsFull (addConst x (-(x fc01))) := by
  funext i
  simp only [normCF, coordsFull, addConst, measure_univ, ENNReal.toReal_one, mul_one]
  rfl

/-! ## 3. Radial averages through their raw values -/

/-- The radii read by `radAvgReg x r`. -/
theorem tendsto_radRadius {r : ℝ} :
    Tendsto (fun n : ℕ => dyadicRound n r + radius n) atTop (𝓝 r) := by
  have h1 : Tendsto (fun n : ℕ => dyadicRound n r) atTop (𝓝 r) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact CircleCont.abs_dyadicRound_sub_le n r)
      WedgeTK.tendsto_one_div_two_pow
  have h2 : Tendsto (fun n : ℕ => radius n) atTop (𝓝 0) :=
    tendsto_nhds_of_tendsto_nhdsWithin RegClosure.tendsto_radius_nhdsGT
  simpa using h1.add h2

/-- The raw semicircle values about `0` converge to a function continuous on `(0,∞)`. -/
def RadLim (x : FieldSample) (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Ioi 0) ∧ ∀ r : ℝ, 0 < r →
    Tendsto (fun n : ℕ => x (foldedCircle 0 (dyadicRound n r + radius n))) atTop (𝓝 (f r))

theorem RadLim.radAvgReg_eq {x : FieldSample} {f : ℝ → ℝ} (h : RadLim x f) {r : ℝ}
    (hr : 0 < r) : radAvgReg x r = f r :=
  (h.2 r hr).limUnder_eq

theorem RadLim.add_const {x : FieldSample} {f : ℝ → ℝ} (h : RadLim x f) (c : ℝ) :
    RadLim (QuantumZipper.addConst x c) (fun r => f r + c) := by
  refine ⟨h.1.add continuousOn_const, fun r hr => ?_⟩
  have e : (fun n : ℕ => QuantumZipper.addConst x c (foldedCircle 0 (dyadicRound n r + radius n))) =
      fun n => x (foldedCircle 0 (dyadicRound n r + radius n)) + c := by
    funext n; simp [QuantumZipper.addConst]
  rw [e]
  exact (h.2 r hr).add tendsto_const_nhds

theorem continuousOn_F0 {F : ℂ × ℝ → ℝ} (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) {s : ℝ}
    (hs : 0 < s) : ContinuousOn (fun r : ℝ => F (0, s * r)) (Ioi 0) :=
  hF.comp (continuousOn_const.prodMk (continuousOn_const.mul continuousOn_id))
    fun r (hr : 0 < r) => ⟨GaussTK.zero_mem_Hbar, mul_pos hs hr⟩

theorem tendsto_F0 {F : ℂ × ℝ → ℝ} (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) {s : ℝ}
    (hs : 0 < s) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => F (0, s * (dyadicRound n r + radius n))) atTop (𝓝 (F (0, s * r))) :=
  ((continuousOn_F0 hF hs).continuousAt (Ioi_mem_nhds hr)).tendsto.comp tendsto_radRadius

theorem radRadius_pos (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 < dyadicRound n r + radius n := by
  rw [radAvg_radius_eq_div]
  have h0 : 0 ≤ ⌊(2 : ℝ) ^ n * r⌋ := Int.floor_nonneg.2 (by positivity)
  have h1 : (0 : ℤ) < ⌊(2 : ℝ) ^ n * r⌋ + 1 := by omega
  have : (0 : ℝ) < ((⌊(2 : ℝ) ^ n * r⌋ + 1 : ℤ) : ℝ) := by exact_mod_cast h1
  positivity

theorem GoodRad.radLim {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : WedgeTK.GoodRad x F) :
    RadLim x (fun r => F (0, r)) := by
  refine ⟨by simpa using continuousOn_F0 h.1.1 one_pos, fun r hr => ?_⟩
  have e : (fun n : ℕ => x (foldedCircle 0 (dyadicRound n r + radius n))) =
      fun n => F (0, 1 * (dyadicRound n r + radius n)) := by
    funext n
    rw [one_mul, ← h.1.evalReg_fc_of_mem GaussTK.zero_mem_Hbar (radRadius_pos n hr.le)]
    have hs : dyadicRound n r + radius n = WedgeTK.dyRad n (⌊(2 : ℝ) ^ n * r⌋.toNat) := by
      rw [radAvg_radius_eq_div, WedgeTK.dyRad]
      have h0 : 0 ≤ ⌊(2 : ℝ) ^ n * r⌋ := Int.floor_nonneg.2 (by positivity)
      have : ((⌊(2 : ℝ) ^ n * r⌋.toNat : ℕ) : ℝ) = (⌊(2 : ℝ) ^ n * r⌋ : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg h0
      rw [this]; push_cast; ring
    rw [hs, h.2, h.1.evalReg_fc_of_mem GaussTK.zero_mem_Hbar (WedgeTK.dyRad_pos _ _)]
  rw [e]
  simpa using tendsto_F0 h.1.1 one_pos hr

/-- Raw semicircle values of a rescaled field about `0`. -/
theorem rescale_fc0' (y : FieldSample) (Q : ℝ) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    rescale y Q s (foldedCircle 0 r) = evalReg y (foldedCircle 0 (s * r)) + Q * Real.log s := by
  rw [rescale_fc_apply _ _ hs, WedgeTK.fc_map_mul 0 r hs, mul_zero]

theorem radLim_rescale {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F) (Q : ℝ)
    {s : ℝ} (hs : 0 < s) :
    RadLim (rescale x Q s) (fun r => F (0, s * r) + Q * Real.log s) := by
  refine ⟨(continuousOn_F0 h.1 hs).add continuousOn_const, fun r hr => ?_⟩
  have e : (fun n : ℕ => rescale x Q s (foldedCircle 0 (dyadicRound n r + radius n))) =
      fun n => F (0, s * (dyadicRound n r + radius n)) + Q * Real.log s := by
    funext n
    rw [rescale_fc0' _ _ hs, h.evalReg_fc_of_mem GaussTK.zero_mem_Hbar
      (mul_pos hs (radRadius_pos n hr.le))]
  rw [e]
  exact (tendsto_F0 h.1 hs hr).add tendsto_const_nhds

end WedgeInf

end QuantumZipper
