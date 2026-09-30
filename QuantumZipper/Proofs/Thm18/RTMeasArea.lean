import QuantumZipper.Proofs.Thm18.RTMeasCoord
import QuantumZipper.Proofs.Thm18.R18T6Meas
import Mathlib.Probability.Kernel.MeasurableLIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS, part 3: measurable readings of the area of the pieces on random sets

`R18.areaBallRead` (R18T6Meas.lean) reads the area of the pieces on the balls `B_a(0)`. Here the
same cut-off argument (`Prop16Area.Meas.IsBumpFamily`, `lintegral_eq_iSup`) reads the area on
`O ∩ ℍ` for every fixed open `O ⊆ B_R(0)` (`readO_eq`). On a Borel set `GA` of data where the local
area limit exists and is finite on the compacts of `ℍ`, this makes the truncated area family
`p ↦ areaOfData (dfull p)|_{hExh N}` measurable (π-system of open sets,
`Measurable.measure_of_isPiSystem`), and then the mass of a jointly measurable random set is
measurable in the parameter (`measurable_measure_section`, the normalised finite kernel argument of
`R18.measurable_areaScale_map`).

Own elementary bookkeeping (measurability the paper leaves implicit).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm Prop16Area.Meas

/-- The random open set `O ∩ ℍ ∖ curve`. -/
def openOff (O : Set ℂ) (d : E6.FullData) : Set ℂ := O ∩ offSet d

theorem isOpen_openOff {O : Set ℂ} (hO : IsOpen O) (d : E6.FullData) : IsOpen (openOff O d) :=
  hO.inter (isOpen_offSet d)

theorem compl_openOff_nonempty (O : Set ℂ) (d : E6.FullData) : (openOff O d)ᶜ.Nonempty :=
  ⟨0, fun h => by have : (0 : ℝ) < (0 : ℂ).im := h.2.1; simp at this⟩

theorem measurable_infDist_openOff_fix {O : Set ℂ} (hO : IsOpen O) (z : ℂ) :
    Measurable fun d : E6.FullData => infDist z (openOff O d)ᶜ := by
  set X : Set ℂ := Oᶜ ∪ Hᶜ with hXdef
  have hX : IsClosed X := hO.isClosed_compl.union isOpen_H.isClosed_compl
  have e : ∀ d : E6.FullData, (openOff O d)ᶜ =
      closure (X ∪ range fun q : ℚ≥0 => G1Pkg.traceSel 1 d.2 (q : ℝ)) := by
    intro d
    rw [closure_union, hX.closure_eq]
    ext w
    simp only [openOff, offSet, D74.curveSel, mem_compl_iff, mem_inter_iff, Set.mem_sdiff, hXdef,
      mem_union]
    tauto
  have hne : ∀ d : E6.FullData, (X ∪ range fun q : ℚ≥0 => G1Pkg.traceSel 1 d.2 (q : ℝ)).Nonempty :=
    fun d => ⟨0, Or.inl (Or.inr fun h => by have : (0 : ℝ) < (0 : ℂ).im := h; simp at this)⟩
  refine measurable_of_Iio fun r => ?_
  have e2 : (fun d : E6.FullData => infDist z (openOff O d)ᶜ) ⁻¹' Iio r =
      {_d | ∃ y ∈ X, dist z y < r} ∪
        ⋃ q : ℚ≥0, {d : E6.FullData | dist z (G1Pkg.traceSel 1 d.2 (q : ℝ)) < r} := by
    ext d
    simp only [mem_preimage, mem_Iio, e d, infDist_closure, infDist_lt_iff (hne d), mem_union,
      mem_setOf_eq, mem_iUnion, mem_range]
    constructor
    · rintro ⟨y, hy | ⟨q, rfl⟩, hd⟩
      · exact Or.inl ⟨y, hy, hd⟩
      · exact Or.inr ⟨q, hd⟩
    · rintro (⟨y, hy, hd⟩ | ⟨q, hd⟩)
      · exact ⟨y, Or.inl hy, hd⟩
      · exact ⟨_, Or.inr ⟨q, rfl⟩, hd⟩
  rw [e2]
  refine (MeasurableSet.const _).union (MeasurableSet.iUnion fun q => ?_)
  exact measurableSet_lt (measurable_const.dist
    ((D74.measurable_traceSel_apply _).comp measurable_snd)) measurable_const

theorem measurable_infDist_openOff {O : Set ℂ} (hO : IsOpen O) :
    Measurable fun q : E6.FullData × ℂ => infDist q.2 (openOff O q.1)ᶜ := by
  set u : ℂ → E6.FullData → ℝ := fun z d => infDist z (openOff O d)ᶜ with hu
  have h : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable (fun d => continuous_infDist_pt _)
      (fun z => measurable_infDist_openOff_fix hO z)
  have e : (fun q : E6.FullData × ℂ => infDist q.2 (openOff O q.1)ᶜ) =
      Function.uncurry u ∘ Prod.swap := by
    funext q; rfl
  rw [e]
  exact h.comp measurable_swap

/-- The cut-offs of `openOff O d`. -/
def bumpO (O : Set ℂ) (n : ℕ) (d : E6.FullData) (z : ℂ) : ℝ :=
  min 1 (max 0 (((n : ℝ) + 1) * infDist z (openOff O d)ᶜ - 1))

theorem isBumpFamily_bumpO {O : Set ℂ} (hO : IsOpen O) : IsBumpFamily (openOff O) (bumpO O) where
  meas n := measurable_const.min (measurable_const.max
    (((measurable_infDist_openOff hO).const_mul _).sub_const 1))
  cont n d := continuous_const.min (continuous_const.max
    ((continuous_infDist_pt _).const_mul _ |>.sub continuous_const))
  nonneg n d z := le_min zero_le_one (le_max_left _ _)
  le_one n d z := min_le_left _ _
  tsupp n d := by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hsub : tsupport (bumpO O n d) ⊆ {z | 1 / ((n : ℝ) + 1) ≤ infDist z (openOff O d)ᶜ} := by
      refine closure_minimal (fun z hz => ?_) (isClosed_le continuous_const
        (continuous_infDist_pt _))
      simp only [Function.mem_support, bumpO] at hz
      simp only [mem_setOf_eq]
      by_contra hlt
      push Not at hlt
      apply hz
      have : ((n : ℝ) + 1) * infDist z (openOff O d)ᶜ - 1 ≤ 0 := by
        rw [lt_div_iff₀ hpos] at hlt; linarith
      rw [max_eq_left this, min_eq_right zero_le_one]
    refine hsub.trans fun z hz => ?_
    by_contra hz'
    have h0 := infDist_zero_of_mem (s := (openOff O d)ᶜ) hz'
    simp only [mem_setOf_eq, h0] at hz
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  mono d z := by
    intro n m hnm
    simp only [bumpO]
    refine min_le_min le_rfl (max_le_max le_rfl (sub_le_sub_right
      (mul_le_mul_of_nonneg_right ?_ infDist_nonneg) 1))
    exact_mod_cast Nat.add_le_add_right hnm 1
  reach d z hz := by
    have hpos : 0 < infDist z (openOff O d)ᶜ :=
      ((isOpen_openOff hO d).isClosed_compl.notMem_iff_infDist_pos
        (compl_openOff_nonempty O d)).1 (fun h => h hz)
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / infDist z (openOff O d)ᶜ)
    refine ⟨n, ?_⟩
    have h2 : 2 ≤ ((n : ℝ) + 1) * infDist z (openOff O d)ᶜ := by
      rw [div_lt_iff₀ hpos] at hn; nlinarith
    simp only [bumpO]
    rw [max_eq_right (by linarith), min_eq_left (by linarith)]

/-- **The measurable reading of the area on `O ∩ ℍ`** (`O` open, inside `B_R(0)`). -/
def readO (γ : ℝ) (O : Set ℂ) (R : ℝ) (d : E6.FullData) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (Prop16Area.Meas.Psi γ readOffField
    (fun d z => ballCut R z * bumpO O n d z) d)

theorem measurable_readO (γ : ℝ) {O : Set ℂ} (hO : IsOpen O) (R : ℝ) :
    Measurable (readO γ O R) :=
  Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
    (Prop16Area.Meas.measurable_Psi γ measurable_readOffField
    (((continuous_ballCut R).measurable.comp measurable_snd).mul
      ((isBumpFamily_bumpO hO).meas n)))

theorem readO_eq {γ R : ℝ} {O : Set ℂ} (hO : IsOpen O) (hOR : O ⊆ ball 0 R) {d : E6.FullData}
    {m : Measure ℂ} (hm : IsVagueLimitOn (offSet d) (areaApprox γ (readOffField d)) m) :
    readO γ O R d = areaOfData γ d (O ∩ H) := by
  have hdef : areaOfData γ d = m := LocalRule.qAreaMeasureOn_eq (isOpen_offSet d) hm
  have hm' : IsVagueLimitOn (openOff O d) (areaApprox γ (readOffField d))
      (m.restrict (openOff O d)) :=
    isVagueLimitOn_restrict_R18 (isOpen_openOff hO d) inter_subset_right hm
  have hφ := isBumpFamily_bumpO hO
  have hL := lintegral_eq_iSup (x := readOffField) (p := d) hφ hm' (continuous_ballCut R)
    (hasCompactSupport_ballCut R) (fun z => le_max_left _ _)
  have eP : ∀ n : ℕ, Prop16Area.Meas.Psi γ readOffField
      (fun d z => ballCut R z * bumpO O n d z) d =
      ∫ z, ballCut R z * bumpO O n d z ∂(m.restrict (openOff O d)) := fun n =>
    ((hm'.2.2 _ ((continuous_ballCut R).mul (hφ.cont n d))
      ((hasCompactSupport_ballCut R).mul_right)
      ((tsupport_mul_subset_right).trans (hφ.tsupp n d))).limUnder_eq)
  unfold readO
  simp_rw [eP, ← hL, hdef]
  have hS : MeasurableSet (openOff O d) := (isOpen_openOff hO d).measurableSet
  rw [lintegral_congr_ae (g := fun _ => (1 : ℝ≥0∞)) ?_, lintegral_one, Measure.restrict_apply_univ]
  · refine le_antisymm (measure_mono fun z hz => ⟨hz.1, hz.2.1⟩) ?_
    calc m (O ∩ H) ≤ m (openOff O d ∪ (offSet d)ᶜ) := measure_mono fun z hz => by
          by_cases h : z ∈ offSet d
          · exact Or.inl ⟨hz.1, h⟩
          · exact Or.inr h
      _ ≤ m (openOff O d) + m (offSet d)ᶜ := measure_union_le _ _
      _ = m (openOff O d) := by rw [hm.1, add_zero]
  · filter_upwards [ae_restrict_mem hS] with z hz
    rw [ballCut_eq_one (hOR hz.1), ENNReal.ofReal_one]

/-! ## The truncated area family -/

/-- The regularity of the area of the pieces used for the reading. -/
def AreaGood (γ : ℝ) (d : E6.FullData) : Prop :=
  (∃ m, IsVagueLimitOn (offSet d) (areaApprox γ (readOffField d)) m) ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ H → areaOfData γ d K < ⊤

open Classical in
/-- The area of the pieces on `hExh N`, on the Borel set `GA` (and `0` off it). -/
def areaN (γ : ℝ) (GA : Set PX) (N : ℕ) (p : PX) : Measure ℂ :=
  if p ∈ GA then (areaOfData γ (dfull p)).restrict (LQGMeas.hExh N) else 0

theorem areaN_univ_lt_top {γ : ℝ} {GA : Set PX} (hGA : ∀ p ∈ GA, AreaGood γ (dfull p)) (N : ℕ)
    (p : PX) : areaN γ GA N p univ < ⊤ := by
  unfold areaN
  split_ifs with hp
  · rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono (LQGMeas.hExh_subset_compact N))
      ((hGA p hp).2 _ (LQGMeas.isCompact_hExhK N) (LQGMeas.hExhK_subset_H N))
  · simp

theorem measurable_areaN (γ : ℝ) {GA : Set PX} (hGAm : MeasurableSet GA)
    (hGA : ∀ p ∈ GA, AreaGood γ (dfull p)) (N : ℕ) : Measurable (areaN γ GA N) := by
  classical
  have : ∀ p, IsFiniteMeasure (areaN γ GA N p) := fun p =>
    ⟨areaN_univ_lt_top hGA N p⟩
  have hbasic : ∀ O : Set ℂ, IsOpen O → Measurable fun p => areaN γ GA N p O := by
    intro O hO
    have hO' : IsOpen (O ∩ LQGMeas.hExh N) := hO.inter (LQGMeas.isOpen_hExh N)
    have hOR : O ∩ LQGMeas.hExh N ⊆ ball 0 N := fun z hz => by
      simpa [mem_ball, dist_zero_right] using hz.2.1
    have e : (fun p => areaN γ GA N p O) = fun p =>
        if p ∈ GA then readO γ (O ∩ LQGMeas.hExh N) N (dfull p) else 0 := by
      funext p
      unfold areaN
      split_ifs with hp
      · obtain ⟨m, hm⟩ := (hGA p hp).1
        rw [readO_eq hO' hOR hm, Measure.restrict_apply hO.measurableSet, inter_assoc,
          inter_eq_left.2 (fun z hz => LQGMeas.hExhK_subset_H N
            (LQGMeas.hExh_subset_compact N hz))]
      · rfl
    rw [e]
    exact Measurable.ite hGAm ((measurable_readO γ hO' _).comp measurable_dfull) measurable_const
  exact Measurable.measure_of_isPiSystem (S := {s : Set ℂ | IsOpen s}) BorelSpace.measurable_eq
    isPiSystem_isOpen (fun s hs => hbasic s hs) (hbasic univ isOpen_univ)

/-- **The mass of a jointly measurable random set** under a measurable family of finite
measures is measurable (normalised finite kernel; own elementary argument). -/
theorem measurable_measure_section {D E : Type*} [MeasurableSpace D] [MeasurableSpace E]
    {ν : D → Measure E} (hν : Measurable ν) (hfin : ∀ d, ν d univ < ⊤) {S : Set (D × E)}
    (hS : MeasurableSet S) : Measurable fun d => ν d (Prod.mk d ⁻¹' S) := by
  set c : D → ℝ≥0∞ := fun d => ν d univ with hcdef
  have hc : Measurable c := (Measure.measurable_coe MeasurableSet.univ).comp hν
  let κ : ProbabilityTheory.Kernel D E :=
    ⟨fun d => (c d)⁻¹ • ν d, by
      refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
      simp only [Measure.smul_apply, smul_eq_mul]
      exact hc.inv.mul ((Measure.measurable_coe hs).comp hν)⟩
  have hκ : ∀ d s, κ d s = (c d)⁻¹ * ν d s := fun d s => by
    show ((c d)⁻¹ • ν d) s = _
    rw [Measure.smul_apply, smul_eq_mul]
  have : ProbabilityTheory.IsFiniteKernel κ := ⟨⟨1, ENNReal.one_lt_top, fun d => by
    rw [hκ d univ]
    by_cases h0 : c d = 0
    · rw [show ν d univ = 0 from h0, mul_zero]; exact bot_le
    · rw [ENNReal.inv_mul_cancel h0 (hfin d).ne]⟩⟩
  have hrepr : (fun d => ν d (Prod.mk d ⁻¹' S)) = fun d => c d * κ d (Prod.mk d ⁻¹' S) := by
    funext d
    rw [hκ, ← mul_assoc]
    by_cases h0 : c d = 0
    · have : ν d (Prod.mk d ⁻¹' S) = 0 :=
        le_antisymm ((measure_mono (subset_univ _)).trans (le_of_eq h0)) bot_le
      rw [this, h0]; simp
    · rw [ENNReal.mul_inv_cancel h0 (hfin d).ne, one_mul]
  rw [hrepr]
  exact hc.mul (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hS)

end RTMeas
end R18
end QuantumZipper
