/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPathClock
import InteractingSLE.Spec.Restart.FCK2FinalCollision
import InteractingSLE.Spec.Restart.FCK2RealizeLaws
import InteractingSLE.Spec.Supplement.RLCERestart

/-!
# No continuation threshold before the A-stop (Lemma G7, real contacts allowed)

Packet PROVE-T15-ASTOP-PATH (item 6 of `RLC.OrdModel.AStopSourceInputs`; supplement p. 498, Lemma G7: "At a new
original-real contact, the cumulative weight is determined by the unchanged original boundary value on that side …
There is no relative threshold strictly before the stated stop").

* `IsAChart ψ K x`: the chart-boundary facts at the retained union `K` of an ordinary pair, with the continued path
  started at `x`: `ψ` is continuous on `ℍ̄`, and every real chart point whose image is off `K` has a real image, left
  of `x` for negative chart points and right of `x` for positive ones;
* `aSet ψ K`: the real chart points over `K` (closed, **`IsAChart.isClosed_aSet`**);
* **`IsAChart.word_limits`**: at an untouched real chart point off the jumps, both one-sided limits of an untouched
  word are the original boundary value;
* **`IsAChart.incident_bounds`**: at an untouched real chart point visited by the path before its lifetime, the
  incident heights of the word are the original admissible ones (the flow line's live incident bounds, no jump visits);
* **`not_threshold_canon`**: the canonical A-stopped clock has no threshold at any positive capacity time before its
  lifetime, for every fixed-type reading of an untouched word;
* **`seed_limits`**, **`isAdmissibleSeed_of_sides`**: canonical side heights next to the tip give the seed's one-sided
  limits and an admissible seed.

Deterministic; for Theorem 1.5 (no Theorem 1.2/1.3 used).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.RLC.AStopPath

open Supp7 Restart PiecewiseConstantBoundaryData MartChar.RealFlow

/-- **The chart-boundary facts used by the A-stop** (see the module docstring). -/
structure IsAChart (ψ : ℂ → ℂ) (K : Set ℂ) (x : ℝ) : Prop where
  cont : ContinuousOn ψ Hbar
  closed : IsClosed K
  real : ∀ w : ℝ, ψ w ∉ K → (ψ w).im = 0
  neg : ∀ w : ℝ, ψ w ∉ K → w < 0 → (ψ w).re < x
  pos : ∀ w : ℝ, ψ w ∉ K → 0 < w → x < (ψ w).re

/-- The real chart points over `K`. -/
def aSet (ψ : ℂ → ℂ) (K : Set ℂ) : Set ℂ := {w | w.im = 0 ∧ ψ w ∈ K}

namespace IsAChart

variable {ψ : ℂ → ℂ} {K : Set ℂ} {x : ℝ}

theorem continuous_real (hA : IsAChart ψ K x) : Continuous fun r : ℝ => ψ r :=
  hA.cont.comp_continuous Complex.continuous_ofReal fun r => by
    show (0 : ℝ) ≤ (r : ℂ).im
    rw [ofReal_im]

theorem isOpen_off (hA : IsAChart ψ K x) : IsOpen {r : ℝ | ψ r ∉ K} :=
  hA.closed.isOpen_compl.preimage hA.continuous_real

theorem isClosed_aSet (hA : IsAChart ψ K x) : IsClosed (aSet ψ K) := by
  have h1 : IsClosed {w : ℂ | w.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  have h2 : ContinuousOn ψ {w : ℂ | w.im = 0} := hA.cont.mono fun w (hw : w.im = 0) => by
    show (0 : ℝ) ≤ w.im
    rw [hw]
  exact h2.preimage_isClosed_of_isClosed h1 hA.closed

/-- **Untouched one-sided limits.** -/
theorem word_limits (hA : IsAChart ψ K x) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {c : BoundaryWord} (hu : IsUntouchedWord b jumps K ψ c)
    {w : ℝ} (hw : ψ w ∉ K) (hyJ : (ψ w).re ∉ jumps) :
    leftLim c.fn w = b (ψ w).re ∧ rightLim c.fn w = b (ψ w).re := by
  have hm : Continuous fun r : ℝ => (ψ r).re := Complex.continuous_re.comp hA.continuous_real
  have hj : {y : ℝ | y ∉ jumps} ∈ 𝓝 (ψ w).re := jumps.finite_toSet.isClosed.isOpen_compl.mem_nhds hyJ
  have he := (hm.tendsto w).eventually ((hb _ hyJ).and hj)
  have ht : ∀ᶠ r in 𝓝 w, c.fn r = b (ψ w).re := by
    filter_upwards [he, hA.isOpen_off.mem_nhds hw] with r hr hrK
    rw [(hu r (hA.real r hrK) hrK hr.2).2]
    exact hr.1
  have hT : Tendsto c.fn (𝓝 w) (𝓝 (b (ψ w).re)) := tendsto_const_nhds.congr' (ht.mono fun r hr => hr.symm)
  exact ⟨(hT.mono_left nhdsWithin_le_nhds).limUnder_eq, (hT.mono_left nhdsWithin_le_nhds).limUnder_eq⟩

/-- **Incident bounds at an untouched visited chart point** (see the module docstring). -/
theorem incident_bounds (hA : IsAChart ψ K x) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {c : BoundaryWord} (hu : IsUntouchedWord b jumps K ψ c)
    {κ θ : ℝ} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hxK : (x : ℂ) ∈ K) (h0K : ψ 0 ∈ K)
    (hv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ y : ℝ, η t = y →
      (y ≤ x → leftLim b y + θ * chiC κ < sleLambda κ) ∧ (x ≤ y → -sleLambda κ < rightLim b y + θ * chiC κ))
    (hj : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → ∀ y ∈ jumps, y ≠ x → η t ≠ y)
    {w : ℝ} (hw : ψ w ∉ K) {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) < ζ) (hηt : η t = ψ w) :
    (w ≤ 0 → leftLim c.fn w + θ * chiC κ < sleLambda κ) ∧
      (0 ≤ w → -sleLambda κ < rightLim c.fn w + θ * chiC κ) := by
  set y : ℝ := (ψ w).re with hydef
  have hψy : ψ w = (y : ℂ) := (ofReal_re_eq (hA.real w hw)).symm
  have hηy : η t = (y : ℂ) := hηt.trans hψy
  have hyx : y ≠ x := fun h => hw (by rw [hψy, h]; exact hxK)
  have hyJ : y ∉ jumps := fun hJ => hj t ht0 ht y hJ hyx hηy
  have hw0 : w ≠ 0 := fun h => hw (by rw [h]; exact_mod_cast h0K)
  obtain ⟨hl, hr⟩ := hA.word_limits hb hu hw hyJ
  rw [← hydef] at hl hr
  have hb1 : leftLim b y = b y := Exist.StagedLaw.leftLim_eq_of_notMem hb hyJ
  have hb2 : rightLim b y = b y := Exist.StagedLaw.rightLim_eq_of_notMem hb hyJ
  constructor
  · intro hwle
    have hlt : y < x := hA.neg w hw (lt_of_le_of_ne hwle hw0)
    rw [hl, ← hb1]
    exact (hv t ht y hηy).1 hlt.le
  · intro hwge
    have hlt : x < y := hA.pos w hw (lt_of_le_of_ne hwge (Ne.symm hw0))
    rw [hr, ← hb2]
    exact (hv t ht y hηy).2 hlt.le

end IsAChart

section Canon

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {a : ℝ≥0} {O : Set ℂ} {φ ψ : ℂ → ℂ}

/-- **No threshold at a positive capacity time before the A-stop** (see the module docstring). -/
theorem not_threshold_canon (hR : IsRetCont η ζ x a O φ ψ) (hA : IsAChart ψ (O ∪ η '' Icc 0 a) x)
    {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {c : BoundaryWord} (hu : IsUntouchedWord b jumps (O ∪ η '' Icc 0 a) ψ c)
    (hv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ y : ℝ, η t = y →
      (y ≤ x → leftLim b y + θ * chiC κ < sleLambda κ) ∧ (x ≤ y → -sleLambda κ < rightLim b y + θ * chiC κ))
    (hj : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → ∀ y ∈ jumps, y ≠ x → η t ≠ y)
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (htype : c ∈ FCDet.typeSet κ θ nL nR ρL ρR)
    {W : ℝ≥0 → ℝ} (hWc : Continuous W) (hW0 : W 0 = 0)
    (hg : IsGeneratingTrace W (canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0)
      (canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0))
    {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0) :
    ¬ ForceWord.ThresholdCondition ρL ρR (W q)
      (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-FCDet.typeXL κ θ nL nR ρL ρR c i) q)
      (fun j => rightImg (fun s : ℝ => W s.toNNReal) (FCDet.typeXR κ θ nL nR ρL ρR c j) q) := by
  refine FCPlumb.not_threshold_type_geom_of_incident_bounds hκ htype hWc hW0 hg hq0 hq.le fun him => ?_
  obtain ⟨s, hs0, hsV, he⟩ := exists_contTime hR hq0 hq
  set z := canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 q with hzdef
  have hzr : z = ((z.re : ℝ) : ℂ) := (ofReal_re_eq him).symm
  have hψ : ψ z = η (a + s) := by rw [he]; exact (hR.contPath_spec hsV.le).2
  have hnot : η (a + s) ∉ O ∪ η '' Icc 0 a :=
    notMem_of_lt_contStop (ζ := ζ) (lt_add_of_pos_right a hs0) (coe_add_lt_iff.1 hsV)
  have hw : ψ (z.re : ℂ) ∉ O ∪ η '' Icc 0 a := by rw [← hzr, hψ]; exact hnot
  have hζ : ((a + s : ℝ≥0) : ℝ≥0∞) < ζ := (coe_add_lt_iff.1 hsV).trans_le contStop_le
  have hx : (x : ℂ) ∈ O ∪ η '' Icc 0 a := Or.inr ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hR.path⟩
  have h0 : ψ 0 ∈ O ∪ η '' Icc 0 a := by rw [hR.tipInv]; exact Or.inr ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩
  exact hA.incident_bounds hb hu hx h0 hv hj hw (lt_of_lt_of_le hs0 le_add_self) hζ (by rw [← hzr, hψ])

/-- **The seed's one-sided limits** from the side heights next to the tip. -/
theorem seed_limits (hR : IsRetCont η ζ x a O φ ψ) (hA : IsAChart ψ (O ∪ η '' Icc 0 a) x) {c : BoundaryWord}
    {L R : ℝ} (hside : ∀ y : ℝ, y ≠ 0 → ψ y ∈ H → ψ y ∉ O → ψ y ∈ η '' Icc 0 a →
      (y < 0 → c.fn y = L) ∧ (0 < y → c.fn y = R)) :
    leftLim c.fn 0 = L ∧ rightLim c.fn 0 = R := by
  have hc0 : ψ ((0 : ℝ) : ℂ) = η a := by rw [ofReal_zero]; exact hR.tipInv
  have hH : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), ψ (y : ℂ) ∈ H := by
    refine (hA.continuous_real.tendsto 0).eventually (QuantumZipper.isOpen_H.mem_nhds ?_)
    rw [hc0]; exact hR.tipH
  have hO : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), ψ (y : ℂ) ∉ O := by
    refine (hA.continuous_real.tendsto 0).eventually (hR.compact.isClosed.isOpen_compl.mem_nhds ?_)
    rw [hc0]; exact hR.tipO
  have hgood : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), y ≠ 0 →
      (y < 0 → c.fn y = L) ∧ (0 < y → c.fn y = R) := by
    filter_upwards [hH, hO] with y hyH hyO hy0
    have hK : ψ y ∈ O ∪ η '' Icc 0 a := by
      by_contra hK
      have him := hA.real y hK
      have : (0 : ℝ) < (ψ y).im := hyH
      linarith
    exact hside y hy0 hyH hyO (hK.resolve_left hyO)
  have hL : ∀ᶠ y : ℝ in 𝓝[<] (0 : ℝ), c.fn y = L := by
    filter_upwards [nhdsWithin_le_nhds hgood, self_mem_nhdsWithin] with y hy hy0
    exact (hy (ne_of_lt hy0)).1 hy0
  have hR' : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), c.fn y = R := by
    filter_upwards [nhdsWithin_le_nhds hgood, self_mem_nhdsWithin] with y hy hy0
    exact (hy (ne_of_gt hy0)).2 hy0
  have h1 : (𝓝[<] (0 : ℝ)).NeBot := inferInstance
  have h2 : (𝓝[>] (0 : ℝ)).NeBot := inferInstance
  exact ⟨(tendsto_const_nhds.congr' (hL.mono fun y hy => hy.symm)).limUnder_eq,
    (tendsto_const_nhds.congr' (hR'.mono fun y hy => hy.symm)).limUnder_eq⟩

end Canon

/-- The canonical tip heights give an admissible seed. -/
theorem isAdmissibleSeed_canonical {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) :
    ExplState.IsAdmissibleSeed κ (-sleLambda κ - θ * chiC κ) (sleLambda κ - θ * chiC κ) θ := by
  have hΛ := Sec4.sleLambda_pos hκ
  constructor <;> linarith

end InteractingSLE.RLC.AStopPath
