/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2Cone
import InteractingSLE.Spec.Supplement.GW0BadGroup
import InteractingSLE.Spec.Supplement.GW2ConeData
import InteractingSLE.Spec.Supplement.GW2aSingle
import InteractingSLE.Spec.Supplement.BR6
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Spec.Supplement.G12Core
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Sec7.CounterflowCentering

/-!
# GW2's forced arcs from Theorem BR6

Packet PROVE-T14-CONE. The named step `GW2Cone.GW2ForcedArcStatement` of Lemma GW2 (p. 621: "For a boundary root `v`,
BR6 forces the whole initial arc `[x, v]`"; p. 622: "The initial arcs `[x, v]` are forced by BR6") is proved here from
* `BR6.BR6Statement` (Theorem BR6, p. 610; stated by PROVE-T14-GW3, being proved by PROVE-T14-BR3) — only its
  sufficiency direction is used;
* `GW0.GW0ForwardStatement` (Lemma GW0's forward implication: the counterflow with infinite lifetime has an admissible
  word, `GW0.counterflow_admissible`; reduced by PROVE-T14-GW3 to `GW0BadGroup.BR3ReferenceStatement`);
* `Exist.Theorem13Statement` (Theorem 1.3: the continuous transient counterflow trace).

**The argument.** The centred counterflow is the flow line, at `k = 16/κ` and angle `0`, of the explicit word of
`counterflowData κ b` (`GW2ConeData`). In its chart `R(z) = −1/z` a physical point `v' ∈ (0, v]` of the first low right
arc is the left point `−1/v'`; reflecting (`IsIntegratedSLEEvolution.reflect`, `LP.isGeneratingTrace_reflect`) puts it
at `1/v' > 0`, the setting of BR6. Its conditions 1–2 are admissibility of the counterflow word (GW0); condition 3 says
that the counterflow word is low beyond `1/v'`: every physical interval below `v'` has height `b − πχ/2 ≤ −λ`
(`lowerArcRoots`), i.e. left cumulative sum `(b + πχ)/λ' − 1 ≤ k/2 − 4` (`λ' = λ − πχ/2`, `πχ/λ' = k/2 − 2`). BR6
then gives a visit of `1/v'` by the reflected trace, i.e. `v'` is a physical point of the counterflow. Rational `v'`,
a countable intersection and closedness of the range give the whole arc `[0, v]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Cone

open Sec7.StripSysField
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### The first low right arc -/

/-- The two conditions encoded in `v ∈ lowerArcRoots κ b jumps`: the right seed is low and every genuine jump in
`(0, v]` keeps the outward height low. -/
theorem low_of_mem_lowerArcRoots {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {v : ℝ} (hv : v ∈ lowerArcRoots κ b jumps) :
    0 < v ∧ rightLim b 0 - Real.pi / 2 * QuantumZipper.chiC κ ≤ -sleLambda κ ∧
      ∀ x ∈ jumpSet b jumps, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * QuantumZipper.chiC κ ≤ -sleLambda κ := by
  unfold lowerArcRoots at hv
  split_ifs at hv with h0
  · exact ⟨hv.2.1, h0, hv.2.2⟩
  · exact absurd hv (notMem_empty v)

/-- **The data are low on the first low right arc**: for `v ∈ lowerArcRoots κ b jumps` and every point `x ∈ (0, v]` off
the jump candidates, `b(x) − πχ/2 ≤ −λ` (`b(x)` is the right limit at the last genuine jump below `x`, or at `0`). -/
theorem le_of_mem_lowerArcRoots {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {v : ℝ} (hv : v ∈ lowerArcRoots κ b jumps) {x : ℝ} (hx0 : 0 < x) (hxv : x ≤ v) (hxJ : x ∉ jumps) :
    b x - Real.pi / 2 * QuantumZipper.chiC κ ≤ -sleLambda κ := by
  obtain ⟨-, hlow0, hlow⟩ := low_of_mem_lowerArcRoots hv
  set G := (jumpSet b jumps).filter (fun z => 0 < z ∧ z < x) with hG
  -- the last genuine jump below `x`, or `0`
  set e : ℝ := if hne : G.Nonempty then G.max' hne else 0 with he
  have he0 : 0 ≤ e := by
    rw [he]
    split_ifs with hne
    · exact (Finset.mem_filter.1 (G.max'_mem hne)).2.1.le
    · exact le_rfl
  have hex : e < x := by
    rw [he]
    split_ifs with hne
    · exact (Finset.mem_filter.1 (G.max'_mem hne)).2.2
    · exact hx0
  have hlowe : rightLim b e - Real.pi / 2 * QuantumZipper.chiC κ ≤ -sleLambda κ := by
    rw [he]
    split_ifs with hne
    · have hm := Finset.mem_filter.1 (G.max'_mem hne)
      exact hlow _ hm.1 hm.2.1 (hm.2.2.le.trans hxv)
    · exact hlow0
  have hsum := Exist.eq_rightLim_add_sum_seed hb hex hxJ
  have hzero : ∑ z ∈ jumps.filter (fun z => e < z ∧ z < x), (rightLim b z - leftLim b z) = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨hzJ, hez, hzx⟩ := Finset.mem_filter.1 hz
    by_contra hne
    have hzG : z ∈ G := Finset.mem_filter.2
      ⟨Finset.mem_filter.2 ⟨hzJ, fun h => hne (by rw [h, sub_self])⟩, he0.trans_lt hez, hzx⟩
    have hle : z ≤ e := by
      rw [he]
      split_ifs with hne'
      · exact G.le_max' z hzG
      · exact absurd ⟨z, hzG⟩ hne'
    linarith
  rw [hsum, hzero, add_zero]
  exact hlowe

/-! ### Parameter identities and the counterflow data on the left -/

/-- `λ(16/κ) = λ(κ) − πχ(κ)/2`. -/
theorem sleLambda_sixteen_div_eq {κ : ℝ} (hκ : 0 < κ) :
    sleLambda (16 / κ) = sleLambda κ - Real.pi * QuantumZipper.chiC κ / 2 := by
  have h1 := Sec7.sleLambda_div_sleLambda_sixteen_div hκ
  have h2 := Sec7.pi_mul_chiC_div_sleLambda_sixteen_div hκ
  have hne : sleLambda (16 / κ) ≠ 0 := Sec4.sleLambda_ne_zero (by positivity)
  rw [div_eq_iff hne] at h1 h2
  rw [h1, h2]
  ring

/-- The counterflow data on the chart's left side: `counterflowData κ b y = −b(−1/y) − πχ` for `y < 0`. -/
theorem counterflowData_of_neg (κ : ℝ) (b : ℝ → ℝ) {y : ℝ} (hy : y < 0) :
    counterflowData κ b y = -b (-y⁻¹) - Real.pi * QuantumZipper.chiC κ := by
  simp only [counterflowData, inverseData, returnData, liftBoundary, hy, ↓reduceIte, cfOffset, cfCoeff]
  ring

/-! ### BR6's condition 3 for the reflected counterflow word -/

/-- **The counterflow word is low beyond `1/v'`** (BR6's condition 3 for the reflected word; the low data of the
first low right arc, BW2.1/GW2.1): for `v ∈ lowerArcRoots κ b jumps` and `0 < v' ≤ v`, every interval `(p, p⁺)` of the
reflected left positions of the counterflow word that meets `(1/v', ∞)` has cumulative weight `≤ 16/κ/2 − 4`. Such an
interval corresponds to a physical interval below `v'`, where `b − πχ/2 ≤ −λ`, and the cumulative weight is
`(b + πχ)/λ' − 1` with `λ' = λ − πχ/2`. -/
theorem rightLowBeyond_counterflow {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {v : ℝ} (hv : v ∈ lowerArcRoots κ b jumps) {v' : ℝ}
    (hv0 : 0 < v') (hvv : v' ≤ v) :
    BR6.RightLowBeyond (16 / κ) (-flowLineXL (counterflowData κ b) (counterflowJumps jumps) 0)
      (flowLineRhoL (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0) v'⁻¹ := by
  intro p hp hgap
  set b' := counterflowData κ b with hb'def
  set J' := counterflowJumps jumps with hJ'def
  set xL := flowLineXL b' J' 0 with hxL
  have hk : 0 < 16 / κ := by positivity
  have hb' : IsPiecewiseConstantBoundaryData b' J' := isPiecewiseConstant_counterflowData κ hb
  have hxL0 : ∀ i, xL i ≤ 0 := (Theorem15.isOrderedForceWord_flowLine b' J' 0).2.1
  have hp0 : 0 ≤ p := by
    rcases hp with rfl | ⟨i, rfl⟩
    · exact le_rfl
    · simp only [Pi.neg_apply, neg_nonneg]
      exact hxL0 i
  have hz0 : 0 < v'⁻¹ := inv_pos.2 hv0
  -- the next reflected position after `p`, if any
  set F := (Finset.univ.image fun i => -xL i).filter (p < ·) with hF
  set m := max p v'⁻¹ with hm
  set q : ℝ := if hne : F.Nonempty then F.min' hne else m + 1 with hq
  have hmq : m < q := by
    rw [hq]
    split_ifs with hne
    · obtain ⟨hmem, hpq⟩ := Finset.mem_filter.1 (F.min'_mem hne)
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hmem
      have hzq : v'⁻¹ < F.min' hne := by
        rcases hgap i with h | h
        · simp only [Pi.neg_apply] at h
          rw [← hi] at hpq
          linarith
        · simpa only [Pi.neg_apply, hi] using h
      exact max_lt hpq hzq
    · linarith
  -- a generic point `s ∈ (m, q)`
  obtain ⟨s, ⟨hms, hsq⟩, hsT⟩ := (Set.Ioo_infinite hmq).exists_notMem_finset
    (J'.image (fun y => -y) ∪ jumps.image (fun x => x⁻¹))
  have hs0 : 0 < s := lt_of_lt_of_le hz0 (le_max_right _ _) |>.trans hms
  have hps : p < s := lt_of_le_of_lt (le_max_left _ _) hms
  have hzs : v'⁻¹ < s := lt_of_le_of_lt (le_max_right _ _) hms
  have hyJ : -s ∉ J' := fun h => hsT (Finset.mem_union_left _ (Finset.mem_image.2 ⟨-s, h, neg_neg s⟩))
  have hxJ : s⁻¹ ∉ jumps := fun h => hsT (Finset.mem_union_right _ (Finset.mem_image.2 ⟨s⁻¹, h, inv_inv s⟩))
  -- the filter of the forced data at `−s` is the filter of the condition
  have hfilt : Finset.univ.filter (fun i => (-xL) i ≤ p) = Finset.univ.filter (fun i => -s < xL i) := by
    refine Finset.filter_congr fun i _ => ?_
    simp only [Pi.neg_apply]
    constructor
    · intro h
      linarith
    · intro h
      by_contra hpi
      push Not at hpi
      have hmemF : -xL i ∈ F := Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, hpi⟩
      have hqle : q ≤ -xL i := by
        rw [hq]
        split_ifs with hne
        · exact F.min'_le _ hmemF
        · exact absurd ⟨_, hmemF⟩ hne
      linarith
  -- the forced data at `−s`
  have hfb := Sec4.forceBoundaryData_flowLine hk hb' (x := -s) (by linarith) hyJ
  have hneg : -s < 0 := by linarith
  unfold forceBoundaryData at hfb
  have hcd : b' (-s) = -b (-(-s)⁻¹) - Real.pi * QuantumZipper.chiC κ := counterflowData_of_neg κ b hneg
  simp only [hneg, ↓reduceIte] at hfb
  rw [hcd] at hfb
  have hinv : -(-s)⁻¹ = s⁻¹ := by rw [inv_neg, neg_neg]
  rw [hinv] at hfb
  -- the physical point `1/s` is on the low arc
  have hlow := le_of_mem_lowerArcRoots hb hv (inv_pos.2 hs0)
    ((inv_lt_of_inv_lt₀ hv0 hzs).le.trans hvv) hxJ
  -- the arithmetic
  have hlam := sleLambda_sixteen_div_eq hκ
  have hπ := Sec7.pi_mul_chiC_div_sleLambda_sixteen_div hκ
  have hpos : 0 < sleLambda (16 / κ) := Sec4.sleLambda_pos hk
  have hL : Real.pi / Real.sqrt (16 / κ) = sleLambda (16 / κ) := rfl
  rw [hL] at hfb
  rw [div_eq_iff hpos.ne'] at hπ
  rw [hfilt]
  set S := ∑ i ∈ Finset.univ.filter (fun i => -s < xL i), flowLineRhoL (16 / κ) b' J' 0 0 i with hS
  have key : sleLambda (16 / κ) * (1 + S) ≤ sleLambda (16 / κ) * (16 / κ / 2 - 3) := by
    nlinarith
  have := le_of_mul_le_mul_left key hpos
  linarith

/-! ### The forced arcs -/

/-- A point whose reflection `−z̄` is the real `r` is `−r`. -/
theorem eq_neg_of_reflectC_eq {w : ℂ} {r : ℝ} (hw : LP.reflectC w = r) : w = -(r : ℂ) := by
  have := congrArg LP.reflectC hw
  rw [LP.reflectC_reflectC] at this
  rw [this, LP.reflectC, Complex.conj_ofReal]

/-- **A point of the first low right arc is a physical point of the counterflow** (BR6, sufficiency, applied to the
reflected counterflow word at `1/v'`): for `v ∈ lowerArcRoots κ b jumps` and `0 < v' ≤ v`, almost surely `v'` lies in
the completed counterflow range. -/
theorem ae_mem_counterflowCompletedRange_of_br6 (hBR6 : BR6.BR6Statement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {v : ℝ} (hv : v ∈ lowerArcRoots κ b jumps) {v' : ℝ} (hv0 : 0 < v')
    (hvv : v' ≤ v) :
    ∀ᵐ ω ∂P, (v' : ℂ) ∈ counterflowCompletedRange (fun t => W' t ω) := by
  obtain ⟨h', -, hfl⟩ := isFlowLineDriver_counterflowData hκ hb hh hcf
  have hk : 0 < 16 / κ := by positivity
  have hk4 : 4 < 16 / κ := by
    rw [lt_div_iff₀ hκ]
    linarith
  obtain ⟨hadmL, hadmR⟩ := GW0.counterflow_admissible hGW0 hκ hκ4 hfl hζ'
  have hγ := GW2aSingle.ae_chosenTrace hT13 hk hfl
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  have hE := hC.1.reflect
  have hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W') t ω) (ζ' ω)
      (fun t => LP.reflectC (GW2aSingle.chosenTrace W' ζ' ω t)) := by
    filter_upwards [hγ] with ω hω
    exact LP.isGeneratingTrace_reflect hω.1
  have hword := Supp7.G12.isOrderedForceWord_reflect
    (Theorem15.isOrderedForceWord_flowLine (counterflowData κ b) (counterflowJumps jumps) 0)
  have hvis := (hBR6 (16 / κ) hk4 _ _ _ _ v'⁻¹ (inv_pos.2 hv0) hword P 𝓕 _ _ _ _ ζ' _ hE hη).2
    ⟨fun j _ => hadmR j, fun m _ _ => hadmL m, rightLowBeyond_counterflow hκ hb hv hv0 hvv⟩
  filter_upwards [hvis, hγ, hζ', hdrv] with ω hω hγω hζω hdω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W' t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  obtain ⟨t, -, ht⟩ := hω
  have hγt := eq_neg_of_reflectC_eq ht
  have hne : GW2aSingle.chosenTrace W' ζ' ω t ≠ 0 := by
    rw [hγt, neg_ne_zero, Complex.ofReal_ne_zero]
    exact (inv_pos.2 hv0).ne'
  unfold counterflowCompletedRange
  rw [CounterflowRange.tipSet_infinitySourceChart_top hγω.1 hWc hdω.1]
  refine Or.inl ⟨t, hne, ?_⟩
  rw [hγt, Complex.ofReal_inv, inv_neg, inv_inv, neg_neg]

/-- **GW2's forced arcs from Theorem BR6** (p. 621: "For a boundary root `v`, BR6 forces the whole initial arc
`[x, v]`"): `GW2ForcedArcStatement` from `BR6.BR6Statement` (its sufficiency direction), Lemma GW0's forward
implication (admissibility of the counterflow word) and Theorem 1.3 (the continuous transient counterflow trace, which
makes the range closed). Every rational point of `(0, v]` is visited, so the closed range contains `[0, v]`. -/
theorem gw2ForcedArcStatement_of_br6 (hBR6 : BR6.BR6Statement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) : GW2ForcedArcStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' v hv
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ v →
      (((q : ℝ) : ℂ)) ∈ counterflowCompletedRange (fun t => W' t ω) := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) ≤ v
    · filter_upwards [ae_mem_counterflowCompletedRange_of_br6 hBR6 hGW0 hT13 hκ hκ4 hb hh hcf hζ' hv hq.1 hq.2]
        with ω hω _ _ using hω
    · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hq
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hk : 0 < 16 / κ := by positivity
  have hγ := GW2aSingle.ae_chosenTrace hT13 hk hfl
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  filter_upwards [hrat, hγ, hζ', hdrv] with ω hq hγω hζω hdω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W' t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  have hclosed := CounterflowRange.isClosed_counterflowCompletedRange hγω.1 hWc hdω.1 (hγω.2 rfl)
  rintro _ ⟨w, ⟨hw0, hwv⟩, rfl⟩
  rcases hw0.eq_or_lt with rfl | hw0
  · rw [Complex.ofReal_zero]
    exact Or.inr rfl
  rw [← hclosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (w - ε) (w / 2) < w by
    exact max_lt (by linarith) (by linarith))
  have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (by positivity) (lt_of_le_of_lt (le_max_right _ _) hq1)
  refine ⟨((q : ℝ) : ℂ), hq q hq0 (hq2.le.trans hwv), ?_⟩
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  linarith [le_max_left (w - ε) (w / 2)]

/-! ### Lemma GW2 with the forced arcs discharged -/

/-- **Lemma GW2 from BR6** (`Theorem14.GW2LightConeStatement`): the forced arcs by `gw2ForcedArcStatement_of_br6`,
the rest by `gw2LightConeStatement_of_inputs`. Remaining inputs: Theorem 1.3, BR6, GW0's forward implication, the
two schedule containments and the exhaustion at interior tips. -/
theorem gw2LightConeStatement_of_br6 (hT13 : Exist.Theorem13Statement.{u}) (hBR6 : BR6.BR6Statement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hC0 : GW2ScheduleContainmentStatement.{u})
    (hCv : GW2ArcScheduleContainmentStatement.{u}) (hEx : GW2TipExhaustionStatement.{u}) :
    GW2LightConeStatement.{u} :=
  gw2LightConeStatement_of_inputs hT13 hC0 (gw2ForcedArcStatement_of_br6 hBR6 hGW0 hT13) hCv hEx

/-- **Lemma GW2 from BR6 and BR3's bounded reference**: as `gw2LightConeStatement_of_br6`, with GW0's forward
implication from `GW0BadGroup.BR3ReferenceStatement` (PROVE-T14-GW3's reduction,
`GW0BadGroup.gw0ForwardStatement_of_br3`). -/
theorem gw2LightConeStatement_of_br3 (hT13 : Exist.Theorem13Statement.{u}) (hBR6 : BR6.BR6Statement.{u})
    (hBR3 : GW0BadGroup.BR3ReferenceStatement) (hC0 : GW2ScheduleContainmentStatement.{u})
    (hCv : GW2ArcScheduleContainmentStatement.{u}) (hEx : GW2TipExhaustionStatement.{u}) :
    GW2LightConeStatement.{u} :=
  gw2LightConeStatement_of_br6 hT13 hBR6 (GW0BadGroup.gw0ForwardStatement_of_br3 hBR3) hC0 hCv hEx

end GW2Cone

end Theorem14

end InteractingSLE
