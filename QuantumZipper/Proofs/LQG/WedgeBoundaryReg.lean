import QuantumZipper.Proofs.LQG.WedgeBoundaryTransfer
import QuantumZipper.Proofs.LQG.GoodTransforms

/-!
# WEDGE-BDRY (2): the boundary-regularity event `BReg` of a field sample

`BReg γ x`: `x` is a good sample, and its boundary measure `ν_x` has no atoms and charges every
nonempty open interval. Both measure conditions are written with countably many quantifiers
(`AtomCond`, `PosCond`), so that `BReg` is a measurable event of the countable coordinates:

* `noAtom_of_atomCond`, `atomCond_of_noAtom`: for a locally finite `ν` on `ℝ`, "no atoms" is
  equivalent to "`∀ n m, ∃ k, ∀ j`, the dyadic interval `[j 2^{-k}, (j+1) 2^{-k}] ∩ [-n,n]` has
  `ν`-mass `≤ 1/m`" (own elementary proof, by Bolzano–Weierstrass; cost rule);
* `measurableSet_bReg`, `bReg_reconstruct`: `BReg` is measurable and only sees `coords`;
* `BReg.add_ofFun`, `BReg.rescale`: stable under adding a function continuous on `Hbar`
  (rule (5.1)) and under the coordinate change `rescale x Q a`, `a > 0`;
* `ae_of_fieldLawFull_eq`: a coordinate event transfers along an equality of `fieldLawFull`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper

namespace WedgeBdry

/-! ## 1. Countable forms of "no atoms" and "positive on intervals" -/

/-- Countable no-atom condition on dyadic intervals. -/
def AtomCond (ν : Measure ℝ) : Prop :=
  ∀ n m : ℕ, ∃ k : ℕ, ∀ j : ℤ,
    ν (Icc ((j : ℝ) / 2 ^ k) (((j : ℝ) + 1) / 2 ^ k) ∩ Icc (-(n : ℝ)) n) ≤ (m : ℝ≥0∞)⁻¹

/-- Positivity on rational intervals. -/
def PosCond (ν : Measure ℝ) : Prop := ∀ a b : ℚ, a < b → 0 < ν (Ioo (a : ℝ) b)

theorem noAtom_of_atomCond {ν : Measure ℝ} (h : AtomCond ν) (t : ℝ) : ν {t} = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_ge |t|
  have hle : ∀ m : ℕ, ν {t} ≤ (m : ℝ≥0∞)⁻¹ := by
    intro m
    obtain ⟨k, hk⟩ := h n m
    refine le_trans (measure_mono ?_) (hk ⌊t * 2 ^ k⌋)
    intro s hs
    rw [mem_singleton_iff] at hs
    subst hs
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [div_le_iff₀ h2]; exact Int.floor_le _
    · rw [le_div_iff₀ h2]; exact (Int.lt_floor_add_one _).le
    · linarith [neg_abs_le s]
    · linarith [le_abs_self s]
  exact le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero hle) zero_le

theorem pos_of_posCond {ν : Measure ℝ} (h : PosCond ν) {u v : ℝ} (huv : u < v) :
    0 < ν (Ioo u v) := by
  obtain ⟨a', ha1, ha2⟩ := exists_rat_btwn huv
  obtain ⟨b', hb1, hb2⟩ := exists_rat_btwn ha2
  exact (h a' b' (by exact_mod_cast hb1)).trans_le (measure_mono (Ioo_subset_Ioo ha1.le hb2.le))

theorem posCond_of_pos {ν : Measure ℝ} (h : ∀ u v : ℝ, u < v → 0 < ν (Ioo u v)) : PosCond ν :=
  fun a b hab => h a b (by exact_mod_cast hab)

theorem iInter_Ioo_eq_singleton (t : ℝ) :
    (⋂ i : ℕ, Ioo (t - 1 / ((i : ℝ) + 1)) (t + 1 / ((i : ℝ) + 1))) = {t} := by
  ext y
  simp only [mem_iInter, mem_Ioo, mem_singleton_iff]
  constructor
  · intro hy
    by_contra hne
    have hpos : 0 < |y - t| := abs_pos.2 (sub_ne_zero.2 hne)
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt hpos
    have := hy i
    rcases le_or_gt 0 (y - t) with h0 | h0
    · rw [abs_of_nonneg h0] at hi; linarith [this.2]
    · rw [abs_of_neg h0] at hi; linarith [this.1]
  · rintro rfl i
    have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    constructor <;> linarith

theorem atomCond_of_noAtom {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (h : ∀ t, ν {t} = 0) :
    AtomCond ν := by
  intro n m
  by_contra hcon
  push_neg at hcon
  choose j hj using hcon
  have hne : ∀ k, (Icc ((j k : ℝ) / 2 ^ k) (((j k : ℝ) + 1) / 2 ^ k) ∩
      Icc (-(n : ℝ)) n).Nonempty := by
    intro k
    by_contra he
    rw [not_nonempty_iff_eq_empty] at he
    have := hj k
    rw [he, measure_empty] at this
    exact not_lt_zero' this
  choose x hx using hne
  obtain ⟨t, -, φ, hφ, hlim⟩ :=
    (isCompact_Icc (a := -(n : ℝ)) (b := n)).tendsto_subseq (fun k => (hx k).2)
  have hball : ∀ δ : ℝ, 0 < δ → (m : ℝ≥0∞)⁻¹ ≤ ν (Ioo (t - δ) (t + δ)) := by
    intro δ hδ
    have h1 : ∀ᶠ k in atTop, |x (φ k) - t| < δ / 2 := by
      filter_upwards [(Metric.tendsto_nhds.1 hlim) (δ / 2) (by positivity)] with k hk
      rwa [Real.dist_eq] at hk
    have h2 : ∀ᶠ k in atTop, (1 / 2 : ℝ) ^ (φ k) < δ / 2 :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).comp
        hφ.tendsto_atTop).eventually (gt_mem_nhds (by positivity))
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    refine (hj (φ k)).le.trans (measure_mono ?_)
    intro y hy
    set K := φ k
    have hlen : ((j K : ℝ) + 1) / 2 ^ K - (j K : ℝ) / 2 ^ K = (1 / 2 : ℝ) ^ K := by
      rw [div_pow, one_pow]; field_simp; ring
    have hxK := (hx K).1
    have hy1 := hy.1
    rw [mem_Icc] at hxK hy1
    obtain ⟨ha, hb⟩ := abs_lt.1 hk1
    rw [mem_Ioo]
    constructor <;> linarith
  have hconv := tendsto_measure_iInter_atTop (μ := ν)
    (s := fun i : ℕ => Ioo (t - 1 / ((i : ℝ) + 1)) (t + 1 / ((i : ℝ) + 1)))
    (fun i => measurableSet_Ioo.nullMeasurableSet)
    (fun i i' hii' => Ioo_subset_Ioo
      (by gcongr) (by gcongr))
    ⟨0, measure_Ioo_lt_top.ne⟩
  rw [iInter_Ioo_eq_singleton, h t] at hconv
  have hge : (m : ℝ≥0∞)⁻¹ ≤ 0 :=
    ge_of_tendsto hconv (Eventually.of_forall fun i => hball _ (by positivity))
  exact (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top m)).ne' (le_antisymm hge zero_le)

/-! ## 2. The event `BReg` -/

/-- Boundary regularity: good sample, atomless boundary measure, positive on rational intervals. -/
def BReg (γ : ℝ) (x : FieldSample) : Prop :=
  IsLQGGood γ x ∧ AtomCond (qBoundaryMeasure γ x) ∧ PosCond (qBoundaryMeasure γ x)

theorem bReg_of {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x)
    (hat : ∀ t, qBoundaryMeasure γ x {t} = 0)
    (hpos : ∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ x (Ioo u v)) : BReg γ x := by
  have := hx.qBoundaryMeasure_spec.1
  exact ⟨hx, atomCond_of_noAtom hat, posCond_of_pos hpos⟩

theorem BReg.noAtom {γ : ℝ} {x : FieldSample} (h : BReg γ x) (t : ℝ) :
    qBoundaryMeasure γ x {t} = 0 := noAtom_of_atomCond h.2.1 t

theorem BReg.pos {γ : ℝ} {x : FieldSample} (h : BReg γ x) {u v : ℝ} (huv : u < v) :
    0 < qBoundaryMeasure γ x (Ioo u v) := pos_of_posCond h.2.2 huv

theorem measurableSet_atomCond {β : Type*} [MeasurableSpace β] {g : β → Measure ℝ}
    (hg : Measurable g) : MeasurableSet {b | AtomCond (g b)} := by
  simp only [AtomCond, setOf_forall, setOf_exists]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun m => MeasurableSet.iUnion fun k =>
    MeasurableSet.iInter fun j => measurableSet_le
      ((Measure.measurable_coe (measurableSet_Icc.inter measurableSet_Icc)).comp hg)
      measurable_const

theorem measurableSet_posCond {β : Type*} [MeasurableSpace β] {g : β → Measure ℝ}
    (hg : Measurable g) : MeasurableSet {b | PosCond (g b)} := by
  simp only [PosCond, setOf_forall]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => MeasurableSet.iInter fun _ =>
    measurableSet_lt measurable_const ((Measure.measurable_coe measurableSet_Ioo).comp hg)

open Classical in
theorem measurableSet_bReg (γ : ℝ) : MeasurableSet {x : FieldSample | BReg γ x} := by
  set g : FieldSample → Measure ℝ := fun x => if IsLQGGood γ x then qBoundaryMeasure γ x else 0
  have hg : Measurable g := GoodMeas.measurable_qBoundaryMeasure_global γ
  have e : {x : FieldSample | BReg γ x} = {x | IsLQGGood γ x} ∩
      ({x | AtomCond (g x)} ∩ {x | PosCond (g x)}) := by
    ext x
    simp only [mem_setOf_eq, mem_inter_iff, BReg, g]
    constructor
    · rintro ⟨h1, h2, h3⟩; simp only [if_pos h1]; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; simp only [if_pos h1] at h2 h3; exact ⟨h1, h2, h3⟩
  rw [e]
  exact (GoodMeas.measurableSet_isLQGGood γ).inter
    ((measurableSet_atomCond hg).inter (measurableSet_posCond hg))

theorem qBoundaryMeasure_reconstruct (γ : ℝ) (x : FieldSample) :
    qBoundaryMeasure γ (Factorization.reconstruct (Factorization.coords x)) =
      qBoundaryMeasure γ x := by
  have hb : bdryApprox γ (Factorization.reconstruct (Factorization.coords x)) = bdryApprox γ x := by
    funext k
    unfold bdryApprox
    rw [Factorization.avgReg_reconstruct_coords]
  unfold qBoundaryMeasure
  rw [hb]

theorem bReg_reconstruct (γ : ℝ) (x : FieldSample) :
    BReg γ (Factorization.reconstruct (Factorization.coords x)) ↔ BReg γ x := by
  simp only [BReg, qBoundaryMeasure_reconstruct, GoodSample.isLQGGood_iff_reconstruct]

/-- A density that never vanishes preserves atomlessness and positivity. -/
theorem reg_withDensity {ν : Measure ℝ} {f : ℝ → ℝ≥0∞} (hf : AEMeasurable f ν)
    (hf0 : ∀ t, f t ≠ 0) (hat : ∀ t, ν {t} = 0)
    (hpos : ∀ u v : ℝ, u < v → 0 < ν (Ioo u v)) :
    (∀ t, ν.withDensity f {t} = 0) ∧ ∀ u v : ℝ, u < v → 0 < ν.withDensity f (Ioo u v) := by
  refine ⟨fun t => withDensity_absolutelyContinuous _ _ (hat t), fun u v huv => ?_⟩
  refine pos_iff_ne_zero.2 fun h0 => (hpos u v huv).ne' ?_
  rw [withDensity_apply_eq_zero' hf] at h0
  have e : {x | f x ≠ 0} ∩ Ioo u v = Ioo u v := by
    ext x; simp [hf0 x]
  rwa [e] at h0

theorem BReg.add_ofFun {γ : ℝ} {x : FieldSample} (h : BReg γ x) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Hbar) : BReg γ (x + ofFun φ) := by
  have hφR : Continuous fun t : ℝ => φ t :=
    hφ.comp_continuous Complex.continuous_ofReal fun t => show (0 : ℝ) ≤ (t : ℂ).im by simp
  have hm : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (γ / 2 * φ t)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hφR)).measurable
  obtain ⟨h1, h2⟩ := reg_withDensity (ν := qBoundaryMeasure γ x) hm.aemeasurable
    (fun t => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne') h.noAtom (fun u v huv => h.pos huv)
  refine bReg_of (h.1.add_ofFun hφ) ?_ ?_
  · rw [GoodSample.qBoundaryMeasure_add_ofFun h.1 hφ]; exact h1
  · rw [GoodSample.qBoundaryMeasure_add_ofFun h.1 hφ]; exact h2

theorem BReg.rescale {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (h : BReg γ x) {a : ℝ} (ha : 0 < a) :
    BReg γ (rescale x (Qc γ) a) := by
  have hm : Measurable fun u : ℝ => u / a := measurable_id.div_const a
  refine bReg_of (h.1.rescale hγ ha) (fun t => ?_) (fun u v huv => ?_)
  · rw [GoodTransforms.qBoundaryMeasure_rescale h.1 hγ ha, Measure.map_apply hm
      (measurableSet_singleton t)]
    have e : (fun u : ℝ => u / a) ⁻¹' {t} = {t * a} := by
      ext u; simp only [mem_preimage, mem_singleton_iff]; constructor
      · intro hu; rw [← hu]; field_simp
      · intro hu; rw [hu]; field_simp
    rw [e]; exact h.noAtom _
  · rw [GoodTransforms.qBoundaryMeasure_rescale h.1 hγ ha, Measure.map_apply hm measurableSet_Ioo]
    have e : (fun u : ℝ => u / a) ⁻¹' Ioo u v = Ioo (u * a) (v * a) := by
      ext w; simp only [mem_preimage, mem_Ioo, lt_div_iff₀ ha, div_lt_iff₀ ha]
    rw [e]; exact h.pos (by nlinarith)

/-! ## 3. Transfer along `fieldLawFull` -/

/-- A coordinate event transfers along an equality of the full laws, provided both full-coordinate
maps are a.e.-measurable. (With the pinned mathlib, `Measure.map` of a non-a.e.-measurable map is a
Dirac mass, not `0`, so the law identity alone does not give the measurability of the `Y` side.) -/
theorem ae_of_fieldLawFull_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {Y : Ω → FieldSample} {Y' : Ω' → FieldSample}
    (hlaw : fieldLawFull H Y P = fieldLawFull H Y' P')
    (hY : AEMeasurable (fun ω => (CoordsFull.coordsFull (Y ω),
      fun ρ : TestFun H => pairRaw (Y ω) ρ.1)) P)
    (hY' : AEMeasurable (fun ω => (CoordsFull.coordsFull (Y' ω),
      fun ρ : TestFun H => pairRaw (Y' ω) ρ.1)) P')
    (S : FieldSample → Prop) (hSm : MeasurableSet {x : FieldSample | S x})
    (hrec : ∀ x, S (Factorization.reconstruct (Factorization.coords x)) ↔ S x)
    (h' : ∀ᵐ ω ∂P', S (Y' ω)) : ∀ᵐ ω ∂P, S (Y ω) := by
  choose j hj using WedgeGood.exists_fullIndex
  set ι : (ℕ → ℝ) × (TestFun H → ℝ) → FieldSample := fun p =>
    Factorization.reconstruct fun i => p.1 (j i)
  have hι : Measurable ι := Factorization.measurable_reconstruct.comp
    (measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp measurable_fst)
  have hE : MeasurableSet {p | S (ι p)} := hι hSm
  have hcoords : ∀ y : FieldSample, (fun i => CoordsFull.coordsFull y (j i)) =
      Factorization.coords y := by
    intro y; funext i
    simp only [CoordsFull.coordsFull, hj i]
    rfl
  have hmem : ∀ y : FieldSample,
      S (ι (CoordsFull.coordsFull y, fun ρ : TestFun H => pairRaw y ρ.1)) ↔ S y := by
    intro y
    show S (Factorization.reconstruct fun i => CoordsFull.coordsFull y (j i)) ↔ S y
    rw [hcoords, hrec]
  have h1 : ∀ᵐ p ∂fieldLawFull H Y' P', S (ι p) :=
    (ae_map_iff hY' hE).2 (h'.mono fun ω hω => (hmem _).2 hω)
  rw [← hlaw] at h1
  exact ((ae_map_iff hY hE).1 h1).mono fun ω hω => (hmem _).1 hω

end WedgeBdry

end QuantumZipper
