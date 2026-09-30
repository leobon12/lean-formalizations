import QuantumZipper.Proofs.Thm18.G3AreaCore
import QuantumZipper.Proofs.Thm18.G3G2Scale

/-!
# G3 area input (Theorem 1.8): the measure-theoretic step and the Palm input

`G3AreaStmt γ` (`G3G2Scale.lean`) says: at fixed `δ, η`, the Palm probability that the zoomed
field's area proxy on a fixed half-ball is `< 1` tends to `0` as `C → ∞`, at the Palm point `x`
and at its length partner `R(x)`. Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4,
pp. 70–71): the zoomed area is `e^{C}` times the area of `h` near the Palm point, which is
positive (the quantum area of a good field charges every nonempty open set, `PositivityArea`).

Contents (namespace `QuantumZipper.Thm18Asm`):

* `IsAreaGood γ y`: `y` is good and its quantum area charges every nonempty open subset of `ℍ`;
* `pos_areaProxy_of_isAreaGood`: area-goodness gives a positive area proxy on every half-ball;
* `coords_addConst_eq`: `coords (addConst x c) = coords x + c` (own elementary proof, the local
  copy of `F1.coords_addConst` avoiding an extra import);
* `eventually_measureReal_addConst_areaProxy_lt` (abstract probability): on a probability space,
  if `u` is a measurable field map whose samples are a.s. good and have positive area on the
  half-ball of radius `q`, then the measure of `{areaProxy < 1}` for the constant-shifted field is
  `< ε` for all large constants. Route: on the a.s. good event the area proxy of `addConst (u p) c`
  is `e^{γc} · areaProxy γ (u p) q` (`areaProxy_addConst_of_good`), hence monotone in `c`; the
  intersection of the bad sets over the natural numbers lies in `{areaProxy γ (u p) q = 0}`, a
  null set, so continuity from above (`tendsto_measure_iInter_atTop`) gives the bound at one
  natural `N`, and monotonicity transports it to all larger real `C`. Passing from the a.s.
  pointwise statement to the uniform-in-`C` bound (nested bad sets over the naturals, continuity
  from above, monotonicity) is our own elementary argument; the paper states only that the zoomed
  area tends to infinity;
* the transport lemmas `g3ν₁_congr`, `g3ν₂_congr`, `g3ν₀_congr`, `g3W0_congr`, `g3Z_congr`,
  `g3W_congr`, `g3PalmLaw_congr`, `g3X_congr`, `g3R_congr`: the concrete scheme's Palm law and
  Palm points depend only on `δ, η` (not on `C`);
* `G3AreaPalmStmt γ`: the Palm input, stated exactly: for every index, Palm-a.e. the translated
  field at the Palm point and at `R(x)` is area-good;
* `g3AreaStmt_of_palm`: `0 < γ → G3AreaPalmStmt γ → G3AreaStmt γ`;
* `G3AreaStmt` itself is **not** proved here: `G3AreaPalmStmt` is the remaining probabilistic
  (Palm-transfer) input. It should follow from the Palm formula for the boundary measure
  (`ae_palmFreeField_good`, `Prop17PalmABId.lean`) together with
  `PositivityArea.ae_forall_pos_qAreaMeasure`, plus F2/F3 of `G3Fid2*.lean`/`G3FidMass.lean`,
  which identify the concrete Palm law on `Ω₀ × ℝ` with the length-biased law of `ν_h` on
  `[−δ, 0]`.

Note: `G3AreaStmt γ` is false for `γ ≤ 0` (`C/γ` is `0` at `γ = 0`, so the added constant does
not grow; for `γ < 0` the area shrinks). The theorem below is therefore stated for `0 < γ`, the
range in which the scheme is used (`g3TransferStmt_of_inputs`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm

open LQGMeas LocalRule Factorization CoordsFull

set_option linter.style.haveILetI false

/-! ## Area-good fields -/

/-- A field is area-good if it is good and its quantum area charges every nonempty open subset
of `ℍ`. -/
def IsAreaGood (γ : ℝ) (y : FieldSample) : Prop :=
  IsLQGGood γ y ∧ ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < qAreaMeasure γ y V

/-- The half-ball `B_a(0) ∩ ℍ` is nonempty for `a > 0`. -/
theorem halfBall_nonempty {a : ℝ} (ha : 0 < a) : (Metric.ball (0 : ℂ) a ∩ H).Nonempty := by
  refine ⟨(((a / 2 : ℝ)) : ℂ) * Complex.I, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < a / 2 by linarith)]
    linarith
  · show 0 < ((((a / 2 : ℝ)) : ℂ) * Complex.I).im
    rw [Complex.mul_I_im, Complex.ofReal_re]
    linarith

/-- Area-goodness gives a positive area proxy on every half-ball. -/
theorem pos_areaProxy_of_isAreaGood {γ : ℝ} {y : FieldSample} (hy : IsAreaGood γ y) {a : ℝ}
    (ha : 0 < a) : 0 < areaProxy γ y a := by
  rw [areaProxy_eq_qAreaMeasure (Prop16Area.G.isVagueLimitOn_H_of_good hy.1) a]
  exact hy.2 _ (Metric.isOpen_ball.inter isOpen_H) inter_subset_right (halfBall_nonempty ha)

/-! ## Coordinates of a constant shift -/

/-- Coordinates of a constant-shifted sample (local copy of `F1.coords_addConst`). -/
theorem coords_addConst_eq (x : FieldSample) (c : ℝ) :
    coords (addConst x c) = fun j => coords x j + c := by
  funext j
  have h1 : (foldedCircle (dyadicIndex j).1 (radius (dyadicIndex j).2)) Set.univ = 1 :=
    measure_univ
  simp only [coords, addConst, h1, ENNReal.toReal_one, mul_one]

/-! ## The measure-theoretic step -/

/-- **Area of the constant-shifted field, measure form.** If `u` is a measurable field map whose
samples are a.s. good and have positive area on the half-ball of radius `q`, then with probability
`→ 1` the constant-shifted sample has area `≥ 1` there, uniformly in the constant. -/
theorem eventually_measureReal_addConst_areaProxy_lt {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {γ : ℝ} (hγ : 0 < γ) {u : Ω → FieldSample}
    {q : ℚ} (hcoords : Measurable fun p => coords (u p))
    (hgood : ∀ᵐ p ∂Q, IsLQGGood γ (u p))
    (hpos : ∀ᵐ p ∂Q, 0 < areaProxy γ (u p) (q : ℝ))
    (_hq : 0 < (q : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, Q.real {p | areaProxy γ (addConst (u p) c) (q : ℝ) < 1} < ε := by
  have hGm : MeasurableSet {p | IsLQGGood γ (u p)} := by
    have e : {p | IsLQGGood γ (u p)} =
        (fun p => coords (u p)) ⁻¹' {c : ℕ → ℝ | IsLQGGood γ (reconstruct c)} := by
      ext p
      exact (GoodSample.isLQGGood_iff_reconstruct γ (u p)).symm
    rw [e]
    exact hcoords (IndepParams.measurableSet_good_coords γ)
  have hBm : ∀ c : ℝ, MeasurableSet {p | areaProxy γ (addConst (u p) c) (q : ℝ) < 1} := by
    intro c
    have h2 : Measurable fun p => coords (addConst (u p) c) := by
      have e : (fun p => coords (addConst (u p) c)) = fun p j => coords (u p) j + c := by
        funext p
        exact coords_addConst_eq (u p) c
      rw [e]
      exact measurable_pi_iff.2 fun j => ((measurable_pi_apply j).comp hcoords).add_const c
    have h3 : Measurable fun p => areaProxy γ (reconstruct (coords (addConst (u p) c))) (q : ℝ) :=
      (measurable_areaProxy γ (q : ℝ)).comp (measurable_reconstruct.comp h2)
    have e : ∀ p, areaProxy γ (addConst (u p) c) (q : ℝ) =
        areaProxy γ (reconstruct (coords (addConst (u p) c))) (q : ℝ) :=
      fun p => (areaProxy_recon γ (addConst (u p) c) (q : ℝ)).symm
    rw [show {p | areaProxy γ (addConst (u p) c) (q : ℝ) < 1} =
        {p | areaProxy γ (reconstruct (coords (addConst (u p) c))) (q : ℝ) < 1} from by
      simp only [e]]
    exact measurableSet_lt h3 measurable_const
  -- the zero-area set is null
  have hzero : Q {p | areaProxy γ (u p) (q : ℝ) = 0} = 0 := by
    refine measure_mono_null (fun p hp => ?_) (ae_iff.1 hpos)
    simp only [mem_ofPred_eq] at hp ⊢
    rw [hp]
    exact not_lt.mpr le_rfl
  -- the intersection of the bad sets over the naturals is null
  have hInterNull : Q (⋂ n : ℕ, {p | areaProxy γ (addConst (u p) (n : ℝ)) (q : ℝ) < 1} ∩
      {p | IsLQGGood γ (u p)}) = 0 := by
    refine measure_mono_null (fun p hp => ?_) hzero
    simp only [mem_iInter, mem_inter_iff, mem_ofPred_eq] at hp ⊢
    by_contra hne
    have ha : 0 < areaProxy γ (u p) (q : ℝ) := pos_iff_ne_zero.2 hne
    obtain ⟨c₀, hc₀⟩ := eventually_atTop.1
      (eventually_one_le_areaProxy_addConst_of_good hγ (hp 0).2 ha)
    obtain ⟨n, hn⟩ := exists_nat_ge c₀
    exact absurd (hc₀ (n : ℝ) hn) (not_le.2 (hp n).1)
  have hanti : Antitone fun n : ℕ => {p | areaProxy γ (addConst (u p) (n : ℝ)) (q : ℝ) < 1} ∩
      {p | IsLQGGood γ (u p)} := by
    intro m n hmn p hp
    simp only [mem_inter_iff, mem_ofPred_eq] at hp ⊢
    exact ⟨lt_of_le_of_lt (areaProxy_addConst_mono_of_good hγ hp.2 (by exact_mod_cast hmn)) hp.1,
      hp.2⟩
  have hlim : Tendsto (fun n : ℕ => Q ({p | areaProxy γ (addConst (u p) (n : ℝ)) (q : ℝ) < 1} ∩
      {p | IsLQGGood γ (u p)})) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := Q)
      (s := fun n : ℕ => {p | areaProxy γ (addConst (u p) (n : ℝ)) (q : ℝ) < 1} ∩
        {p | IsLQGGood γ (u p)})
      (fun n => ((hBm (n : ℝ)).inter hGm).nullMeasurableSet) hanti ⟨0, measure_ne_top Q _⟩
    rw [hInterNull] at h
    exact h
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Q.real ({p | areaProxy γ (addConst (u p) (N : ℝ)) (q : ℝ) < 1} ∩
      {p | IsLQGGood γ (u p)}) < ε := by
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 (ENNReal.ofReal ε)
      (ENNReal.ofReal_pos.2 hε)).exists
    refine ⟨n, ?_⟩
    rw [Measure.real, ← ENNReal.toReal_ofReal hε.le]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top Q _) ENNReal.ofReal_ne_top).2 hn
  have hGre : Q.real {p | IsLQGGood γ (u p)}ᶜ = 0 := by
    refine (measureReal_eq_zero_iff (h := measure_ne_top Q _)).2 ?_
    show Q {p | ¬ IsLQGGood γ (u p)} = 0
    exact ae_iff.1 hgood
  rw [eventually_atTop]
  refine ⟨(N : ℝ), fun c hc => ?_⟩
  have hmonoN : {p | areaProxy γ (addConst (u p) c) (q : ℝ) < 1} ⊆
      ({p | areaProxy γ (addConst (u p) (N : ℝ)) (q : ℝ) < 1} ∩ {p | IsLQGGood γ (u p)}) ∪
        {p | IsLQGGood γ (u p)}ᶜ := by
    intro p hp
    by_cases hpG : IsLQGGood γ (u p)
    · exact Or.inl ⟨lt_of_le_of_lt (areaProxy_addConst_mono_of_good hγ hpG hc) hp, hpG⟩
    · exact Or.inr hpG
  calc Q.real {p | areaProxy γ (addConst (u p) c) (q : ℝ) < 1}
      ≤ Q.real (({p | areaProxy γ (addConst (u p) (N : ℝ)) (q : ℝ) < 1} ∩
          {p | IsLQGGood γ (u p)}) ∪ {p | IsLQGGood γ (u p)}ᶜ) := measureReal_mono hmonoN
    _ ≤ Q.real ({p | areaProxy γ (addConst (u p) (N : ℝ)) (q : ℝ) < 1} ∩
          {p | IsLQGGood γ (u p)}) + Q.real {p | IsLQGGood γ (u p)}ᶜ := measureReal_union_le _ _
    _ = Q.real ({p | areaProxy γ (addConst (u p) (N : ℝ)) (q : ℝ) < 1} ∩
          {p | IsLQGGood γ (u p)}) := by rw [hGre, add_zero]
    _ < ε := hN

/-! ## The scheme depends on `C` only through the zoom -/

theorem g3ν₁_congr {γ : ℝ} {i i' : G3Idx} (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1) :
    g3ν₁ γ i = g3ν₁ γ i' := by
  funext ω
  simp only [g3ν₁, G3Idx.t₁, G3Idx.r₁, G3Idx.δ, G3Idx.η, h₁, h₂]

theorem g3ν₂_congr {γ : ℝ} {i i' : G3Idx} (_h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1) :
    g3ν₂ γ i = g3ν₂ γ i' := by
  funext ω
  simp only [g3ν₂, G3Idx.t₂, G3Idx.r₂, G3Idx.η, h₂]

theorem g3ν₀_congr {γ : ℝ} {i i' : G3Idx} (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1) :
    g3ν₀ γ i = g3ν₀ γ i' := by
  funext ω
  simp only [g3ν₀, G3Idx.t₁, G3Idx.r₁, G3Idx.t₂, G3Idx.r₂, G3Idx.δ, G3Idx.η, h₁, h₂]

theorem g3Mass_congr {γ : ℝ} {i i' : G3Idx} (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1) :
    g3Mass γ i = g3Mass γ i' := by
  have hν₁ := g3ν₁_congr (γ := γ) h₁ h₂
  have hν₀ := g3ν₀_congr (γ := γ) h₁ h₂
  funext ω
  simp only [g3Mass, G3Idx.δ, h₁, hν₁, hν₀]

theorem g3W0_congr {γ : ℝ} {i i' : G3Idx} (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1) :
    g3W0 γ i = g3W0 γ i' := by
  have hM := g3Mass_congr (γ := γ) h₁ h₂
  funext p
  show (if 0 < p.2 ∧ ENNReal.ofReal p.2 ≤ g3Mass γ i p.1 then
      ENNReal.ofReal (Real.exp p.2) else 0) =
    if 0 < p.2 ∧ ENNReal.ofReal p.2 ≤ g3Mass γ i' p.1 then
      ENNReal.ofReal (Real.exp p.2) else 0
  rw [hM]

theorem g3Z_congr {γ : ℝ} {i i' : G3Idx} (h : g3W0 γ i = g3W0 γ i') : g3Z γ i = g3Z γ i' := by
  unfold g3Z
  rw [h]

theorem g3W_congr {γ : ℝ} {i i' : G3Idx} (hZ : g3Z γ i = g3Z γ i') (h0 : g3W0 γ i = g3W0 γ i') :
    g3W γ i = g3W γ i' := by
  unfold g3W
  rw [hZ, h0]

theorem g3PalmLaw_congr {γ : ℝ} {i i' : G3Idx} (h : g3W γ i = g3W γ i') :
    g3PalmLaw γ i = g3PalmLaw γ i' := by
  unfold g3PalmLaw
  rw [h]

theorem g3X_congr {γ : ℝ} {i i' : G3Idx} (h₁ : g3ν₁ γ i = g3ν₁ γ i')
    (h₀ : g3ν₀ γ i = g3ν₀ γ i') : g3X γ i = g3X γ i' := by
  unfold g3X
  rw [h₁, h₀]

theorem g3R_congr {γ : ℝ} {i i' : G3Idx} (h₀ : g3ν₀ γ i = g3ν₀ γ i')
    (h₂ : g3ν₂ γ i = g3ν₂ γ i') : g3R γ i = g3R γ i' := by
  unfold g3R
  rw [h₀, h₂]

/-! ## The Palm input and the area statement -/

/-- **The Palm input of the G3 area statement**: at the random Palm point `x` and at its length
partner `R(x)`, the translated field is area-good. -/
def G3AreaPalmStmt (γ : ℝ) : Prop :=
  ∀ i : G3Idx, ∀ᵐ p ∂(g3PalmLaw γ i),
    IsAreaGood γ (translate (normField γ gffBase.X p.1) (g3X γ i p)) ∧
    IsAreaGood γ (translate (normField γ gffBase.X p.1) (g3R γ i p))

/-- `C ↦ C / γ` tends to `∞` for `γ > 0`. -/
theorem tendsto_div_const_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun C : ℝ => C / γ) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b * γ, fun c hc => by rw [le_div_iff₀ hγ]; exact hc⟩

set_option maxHeartbeats 600000 in
/-- **The Palm-area bound at a Palm function.** If the field translated to the Palm point
`pt p` is a.s. area-good, then the zoomed area proxy at `pt` exceeds `1` with Palm probability
`→ 1`. -/
theorem eventually_measureReal_zoomPalm_lt {γ : ℝ} (hγ : 0 < γ) (i : G3Idx)
    (pt : gffBase.Ω × ℝ → ℝ) (hpt : Measurable pt)
    (h : ∀ᵐ p ∂(g3PalmLaw γ i),
      IsAreaGood γ (translate (normField γ gffBase.X p.1) (pt p)))
    {q : ℚ} (hq : 0 < (q : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ C : ℝ in atTop, (g3PalmLaw γ i).real {p | areaProxy γ
        (addConst (translate (normField γ gffBase.X p.1) (pt p)) (C / γ)) (q : ℝ) < 1} < ε := by
  haveI : IsProbabilityMeasure (g3PalmLaw γ i) := isProbabilityMeasure_g3 γ i
  have hcoords : Measurable fun p : gffBase.Ω × ℝ =>
      coords (translate (normField γ gffBase.X p.1) (pt p)) := by
    have hpair : Measurable fun a : gffBase.Ω × ℝ =>
        ((normField γ gffBase.X a.1 : FieldSample), (pt a : ℝ)) :=
      ((measurable_normField_g3 γ).comp measurable_fst).prodMk hpt
    exact (IndepParams.measurable_coords_translate).comp hpair
  exact (tendsto_div_const_atTop hγ).eventually
    (eventually_measureReal_addConst_areaProxy_lt (Q := g3PalmLaw γ i) (γ := γ)
      (u := fun p => translate (normField γ gffBase.X p.1) (pt p)) hγ hcoords
      (h.mono fun p hp => hp.1)
      (h.mono fun p hp => pos_areaProxy_of_isAreaGood hp hq) hq hε)

set_option maxHeartbeats 600000 in
/-- **G3-Area from the Palm input** (`γ > 0`). -/
theorem g3AreaStmt_of_palm {γ : ℝ} (hγ : 0 < γ) (h : G3AreaPalmStmt γ) : G3AreaStmt γ := by
  intro q hq ε hε δ η
  by_cases hcon : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4
  · obtain ⟨hη, hηδ, hδ4⟩ := hcon
    set i₀ : G3Idx := ⟨(δ, η, 0), hη, hηδ, hδ4⟩ with hi₀
    have hX := eventually_measureReal_zoomPalm_lt hγ i₀ (g3X γ i₀) (measurable_g3X' γ i₀)
      ((h i₀).mono fun p hp => hp.1) hq hε
    have hR := eventually_measureReal_zoomPalm_lt hγ i₀ (g3R γ i₀) (measurable_g3R' γ i₀)
      ((h i₀).mono fun p hp => hp.2) hq hε
    filter_upwards [hX, hR] with C hC hR'
    intro i hi
    have h₁ : i.1.1 = i₀.1.1 := by rw [hi]
    have h₂ : i.1.2.1 = i₀.1.2.1 := by rw [hi]
    have hCi : i.C = C := by show i.1.2.2 = C; rw [hi]
    have hν₁ := g3ν₁_congr (γ := γ) h₁ h₂
    have hν₀ := g3ν₀_congr (γ := γ) h₁ h₂
    have hm : g3PalmLaw γ i = g3PalmLaw γ i₀ :=
      g3PalmLaw_congr (g3W_congr (g3Z_congr (g3W0_congr h₁ h₂)) (g3W0_congr h₁ h₂))
    have hx : g3X γ i = g3X γ i₀ := g3X_congr hν₁ hν₀
    have hr : g3R γ i = g3R γ i₀ := g3R_congr hν₀ (g3ν₂_congr h₁ h₂)
    refine ⟨?_, ?_⟩
    · rw [show {p : gffBase.Ω × ℝ | areaProxy γ (zoomField γ i.C (normField γ gffBase.X p.1)
            (g3X γ i p)) (q : ℝ) < 1} =
          {p | areaProxy γ (addConst (translate (normField γ gffBase.X p.1) (g3X γ i₀ p))
            (C / γ)) (q : ℝ) < 1} from by simp only [zoomField, hx, hCi],
        hm]
      exact hC
    · rw [show {p : gffBase.Ω × ℝ | areaProxy γ (zoomField γ i.C (normField γ gffBase.X p.1)
            (g3R γ i p)) (q : ℝ) < 1} =
          {p | areaProxy γ (addConst (translate (normField γ gffBase.X p.1) (g3R γ i₀ p))
            (C / γ)) (q : ℝ) < 1} from by simp only [zoomField, hr, hCi],
        hm]
      exact hR'
  · filter_upwards with C
    intro i hi
    have h2 : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4 := by
      have := i.2
      rwa [hi] at this
    exact absurd h2 hcon

end Thm18Asm
end QuantumZipper
