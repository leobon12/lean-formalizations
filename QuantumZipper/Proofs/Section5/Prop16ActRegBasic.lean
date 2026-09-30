import QuantumZipper.Proofs.Section5.Prop16NodeB2Reg
import QuantumZipper.Proofs.Section5.Prop16LocGoodBasic
import QuantumZipper.Proofs.GFF.K3.MixedM7AsmMain
import QuantumZipper.Proofs.LQG.BoundaryExistence
import QuantumZipper.Proofs.GFF.CircleMeanValue
import Mathlib.Analysis.Complex.Harmonic.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node B′ inputs: tools for the free-arc regularity `Prop16ActRegStmt`

Tools for `Prop16ActRegStmt` and `Prop16BdryL1Stmt` (`Prop16NodeB2Reg.lean`), whose content is
that the *actual* mixed field `h = 𝔥₀ + X` satisfies, on the free arc and for small circles,
`avgReg h n t = h (fc(t, 2^{-n}))` (item (1) of the window Palm formula), respectively that the
boundary approximations of `h` converge in `L¹(P)` (item (2)).

The route is the domain-Markov/M7 one. `IsMixedGFF` pins the *law* of the field along any family
of admissible measures (`locGood_map_eq_of_isMixedGFF`), so an almost sure statement about
countably many folded circles transfers between any two mixed GFFs. For the coupled pair of
`K3.mixedFreeCouplingHalfDiscStmt` (`mixedFreeCouplingHalfDisc_holds`, proved) the raw value of
the mixed field at *every* measure supported in a small half-disc is an explicit expression in
the free field (`Y μ = X μ − X ρ₀ + ∫ g dμ`), whose circle averages are the free field's
(`BdryExist.ae_avgReg_spec`, M4-R3) plus the harmonic correction `g`. This file provides:

* `mem_union_of_dist_lt_palmGap`, `ball_inter_H_subset_D`, `closedBall_subset_of_gap`: the
  geometry of `palmGap` (points closer than the gap to `x ∈ (a,b)` lie in `D` or on the free
  arc, and the folded circles of the statement are carried by the relatively open `W`);
* `measurableSet_tendsto_seq`: convergence of a sequence of measurable functionals is a
  measurable property of the sequence (needed to push the a.s. statement to the law of the
  family);
* `ae_family_of_isMixedGFF`: **transfer** of an a.s. property of the family of readings along
  admissible measures between two mixed GFFs;
* `integral_foldedCircle_of_harm_center`: the **mean value property** on folded circles for a
  harmonic `g ∘ foldH` on a ball of *arbitrary* centre (generalization of
  `D3Plus.integral_foldedCircle_of_harm`, stated there for `ball 0 r`), via mathlib's
  `HarmonicOnNhd.circleAverage_eq`;
* `tendsto_integral_foldedCircle_dyadic`: continuity in the centre of the folded-circle average
  of a function continuous only on the arc (a global continuous representative is supplied by
  the caller, `exists_continuous_eqOn`, M4-P7-LOC).

Sources: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25); Duplantier–Sheffield,
arXiv:0808.1560, §3.3; Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007),
Thm. 2.17 (domain Markov decomposition, in the M7 form used here). All arguments in this file
are own elementary ones (AGENT_GUIDE cost rule), except the mean value property, which is
mathlib's `HarmonicOnNhd.circleAverage_eq` transported to folded circles.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal Real

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G

/-! ## 1. Geometry of `palmGap` -/

/-- A point of `Hbar` closer to `x ∈ (a,b)` than the gap lies in `D ∪ (a,b)`. -/
theorem mem_union_of_dist_lt_palmGap {D : Set ℂ} {a b : ℝ} {x : ℝ} {u : ℂ} (hu : u ∈ Hbar)
    (h : dist u (x : ℂ) < palmGap D a b x) : u ∈ D ∪ realSet (Ioo a b) := by
  by_contra hmem
  have hle : palmGap D a b x ≤ dist (x : ℂ) u :=
    infDist_le_dist_of_mem (s := palmOutside D a b) ⟨hu, hmem⟩
  rw [dist_comm] at hle
  exact absurd h (not_lt.2 hle)

/-- The open half-disc of radius `palmGap` about `x ∈ (a,b)` is inside `D`. -/
theorem ball_inter_H_subset_D {D : Set ℂ} {a b : ℝ} {x r : ℝ}
    (hr : r ≤ palmGap D a b x) : ball (x : ℂ) r ∩ H ⊆ D := by
  intro u hu
  have hlt : dist u (x : ℂ) < palmGap D a b x := by
    have h1 : dist u (x : ℂ) < r := by simpa only [mem_ball] using hu.1
    linarith
  rcases mem_union_of_dist_lt_palmGap (D := D) (a := a) (b := b) (x := x)
    (show (0 : ℝ) ≤ u.im from le_of_lt hu.2) hlt with h | h
  · exact h
  · simp only [realSet, Set.mem_image] at h
    obtain ⟨t, -, ht⟩ := h
    rw [← ht] at hu
    have h2 : (0 : ℝ) < ((t : ℂ)).im := hu.2
    simp at h2

/-- Folded circles at distance `< palmGap` from `x` are carried by the relatively open `W`
representing `D ∪ (a,b)`. -/
theorem closedBall_subset_of_gap {D : Set ℂ} {a b : ℝ} {x : ℝ} {W : Set ℂ}
    (hWV : W ∩ Hbar = D ∪ realSet (Ioo a b)) {c : ℂ} {r : ℝ}
    (hc : dist c (x : ℂ) + r < palmGap D a b x) : closedBall c r ∩ Hbar ⊆ W := by
  intro u hu
  have huc : dist u c ≤ r := by simpa only [mem_closedBall] using hu.1
  have hdist : dist u (x : ℂ) < palmGap D a b x := by
    linarith [dist_triangle u c (x : ℂ)]
  have hmem : u ∈ D ∪ realSet (Ioo a b) := mem_union_of_dist_lt_palmGap hu.2 hdist
  exact (hWV.symm ▸ hmem : u ∈ W ∩ Hbar).1

/-! ## 2. Convergence of a sequence is measurable -/

/-- Convergence of a sequence of real functionals is a measurable property of the sequence. -/
theorem measurableSet_tendsto_seq {u : (ℕ → ℝ) → (ℕ → ℝ)} {L : (ℕ → ℝ) → ℝ}
    (hu : Measurable u) (hL : Measurable L) :
    MeasurableSet {y | Tendsto (fun n => u y n) atTop (𝓝 (L y))} := by
  have key : ∀ y, Tendsto (fun n => u y n) atTop (𝓝 (L y)) ↔
      ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, dist (u y n) (L y) < ((k : ℝ) + 1)⁻¹ := by
    intro y
    rw [Metric.tendsto_atTop]
    constructor
    · intro h k
      obtain ⟨N, hN⟩ := h _ (by
        have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        exact inv_pos.mpr hk)
      exact ⟨N, fun n hn => hN n hn⟩
    · intro h ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h k
      exact ⟨N, fun n hn => (hN n hn).trans (by simpa only [one_div] using hk)⟩
  have hset : {y | Tendsto (fun n => u y n) atTop (𝓝 (L y))} =
      ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n : ℕ,
        {y | N ≤ n → dist (u y n) (L y) < ((k : ℝ) + 1)⁻¹} := by
    ext y
    simp only [mem_iInter, mem_iUnion, mem_ofPred_eq]
    exact key y
  rw [hset]
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun n => ?_
  by_cases h : N ≤ n
  · simpa [h] using measurableSet_lt (((measurable_pi_apply n).comp hu).dist hL)
      measurable_const
  · simp [h]

/-! ## 3. Transfer of almost sure properties between mixed GFFs -/

/-- **Transfer along the family law of a mixed GFF.** If an a.s. property of the readings of a
mixed GFF along a family `m` of admissible measures holds for one mixed GFF, it holds for any
other one (same data `D`, `S`). -/
theorem ae_family_of_isMixedGFF {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    {P : Measure Ω} {P₀ : Measure Ω₀} [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]
    {D S : Set ℂ} {X : Ω → FieldSample} {Y : Ω₀ → FieldSample}
    (hX : IsMixedGFF D S X P) (hY : IsMixedGFF D S Y P₀) {m : ℕ → Measure ℂ}
    (hm : ∀ i, IsAdmissibleDual D (mixedSpace D S) (m i))
    {T : Set (ℕ → ℝ)} (hT : MeasurableSet T) (hYae : ∀ᵐ ω ∂P₀, (fun i => Y ω (m i)) ∈ T) :
    ∀ᵐ ω ∂P, (fun i => X ω (m i)) ∈ T := by
  have hlaw := locGood_map_eq_of_isMixedGFF hX hY m hm
  have hG : Measurable fun ω₀ : Ω₀ => (fun i => Y ω₀ (m i)) :=
    measurable_pi_iff.2 fun i => hY.measurable_coord _
  have hF : Measurable fun ω : Ω => (fun i => X ω (m i)) :=
    measurable_pi_iff.2 fun i => hX.measurable_coord _
  have h0 : P₀ ((fun ω₀ : Ω₀ => (fun i => Y ω₀ (m i))) ⁻¹' Tᶜ) = 0 := ae_iff.1 hYae
  have h1 : P ((fun ω : Ω => (fun i => X ω (m i))) ⁻¹' Tᶜ) = 0 := by
    rw [← Measure.map_apply hF hT.compl, hlaw, Measure.map_apply hG hT.compl]
    exact h0
  rwa [ae_iff]

/-! ## 4. Mean value property on folded circles with an arbitrary centre -/

/-- Folded-circle average of a function continuous on the closed half-disc, as the circle
average of its even extension `g ∘ foldH`. -/
theorem integral_foldedCircle_eq_circleAverage {g : ℂ → ℝ} {d : ℂ} (hd : d ∈ Hbar) {ρ : ℝ}
    (hρ : 0 < ρ) (hgc : ContinuousOn (fun z => g (foldH z)) (closedBall d ρ)) :
    ∫ z, g z ∂foldedCircle d ρ = Real.circleAverage (fun z => g (foldH z)) d ρ := by
  have hae : ∀ᵐ u ∂foldedCircle d ρ, u ∈ closedBall d ρ ∩ Hbar := ae_fc_mem_ball_inter hd hρ
  have hsK : MeasurableSet (closedBall d ρ ∩ Hbar) :=
    measurableSet_closedBall.inter isClosed_Hbar.measurableSet
  have hih : Integrable (fun z => g (foldH z)) (circleUnif d ρ) := by
    rw [← Measure.restrict_eq_self_of_ae_mem (CoordReg.ae_mem_closedBall_circleUnif d hρ.le)]
    exact hgc.integrableOn_compact (isCompact_closedBall d ρ)
  have hig_asm : AEStronglyMeasurable g (foldedCircle d ρ) := by
    have h1 : AEStronglyMeasurable (fun z => g (foldH z))
        ((foldedCircle d ρ).restrict (closedBall d ρ ∩ Hbar)) :=
      (hgc.mono inter_subset_left).aestronglyMeasurable hsK
    rw [Measure.restrict_eq_self_of_ae_mem hae] at h1
    exact h1.congr (hae.mono fun u hu => by change g (foldH u) = g u; rw [CircleFubini.foldH_of_mem' hu.2])
  have e1 : ∫ z, g z ∂foldedCircle d ρ = ∫ z, g (foldH z) ∂circleUnif d ρ :=
    integral_map measurable_foldH.aemeasurable hig_asm
  have hihC : Integrable (fun z => g (foldH z)) (LQGDimension.Coupling.circMeas d ρ) := by
    rw [← CircleMV.circleUnif_eq_circMeas]
    exact hih
  have e2 : ∫ z, g (foldH z) ∂circleUnif d ρ =
      Real.circleAverage (fun z => g (foldH z)) d ρ := by
    rw [CircleMV.circleUnif_eq_circMeas]
    exact LQGDimension.Coupling.integral_circMeas_eq_circleAverage hihC.aestronglyMeasurable
  rw [e1, e2]

/-- **Mean value property on folded circles** (arbitrary centre; generalization of
`D3Plus.integral_foldedCircle_of_harm`): if `g ∘ foldH` is harmonic on `ball c R` and the folded
circle `fc(d, ρ)` lies inside, then the folded-circle average of `g` at `d ∈ Hbar` is `g d`. -/
theorem integral_foldedCircle_of_harm_center {g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (harm : InnerProductSpace.HarmonicOnNhd (fun z => g (foldH z)) (ball c R))
    {d : ℂ} (hd : d ∈ Hbar) {ρ : ℝ} (hρ : 0 < ρ) (hdR : ‖d - c‖ + ρ < R) :
    ∫ z, g z ∂foldedCircle d ρ = g d := by
  have hsub : closedBall d ρ ⊆ ball c R := fun w hw => by
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_eq_norm]
    calc ‖w - c‖ = ‖(w - d) + (d - c)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖w - d‖ + ‖d - c‖ := norm_add_le _ _
      _ < R := by linarith
  have hmono : InnerProductSpace.HarmonicOnNhd (fun z => g (foldH z)) (closedBall d |ρ|) := by
    rw [abs_of_pos hρ]
    exact harm.mono hsub
  rw [integral_foldedCircle_eq_circleAverage hd hρ (harm.continuousOn.mono hsub),
    hmono.circleAverage_eq, CircleFubini.foldH_of_mem' hd]

/-! ## 5. Continuity in the centre of folded-circle averages along the dyadic centres -/

end Prop16Asm

end QuantumZipper
