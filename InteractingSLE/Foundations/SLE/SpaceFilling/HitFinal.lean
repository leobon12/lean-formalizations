import InteractingSLE.Foundations.SLE.SpaceFilling.AreaZero
import InteractingSLE.Foundations.SLE.SpaceFilling.HitMarkov
import InteractingSLE.Foundations.SLE.SpaceFilling.HitPos
import QuantumZipper.Proofs.Thm11.AddendumArea

/-!
# [RS05, Lemma 7.3] and [RS05, Corollary 7.4] for `κ > 8`

Packet `planning/packets/PROVE-RS05-74c.md`. Source: [RS05] `SLEcont.tex` lines 2350–2375 (the
case `κ > 8` of the proof of Lemma 7.3) and lines 2406–2416 (Corollary 7.4).

**Positivity** (`exists_measure_hullContainsHalfBall_ne_zero_of_eight_lt`): for `κ > 8` some hull
`K_{t₀}` contains a half-neighbourhood of `0` with positive probability. As in [RS05], suppose
not. Then (`HitMarkov.lean`) almost surely the trace never leaves the boundary of the later hulls:
`γ([0,u)) ∩ ℍ ⊆ \overline{ℍ \ K_u} \ (ℍ \ K_u)`, a Lebesgue-null set for each `u`
(`AreaZero.lean`, our replacement of [RS05, Corollary 5.3]). So `area(γ[0,∞) ∩ ℍ) = 0` a.s., and by
Fubini (with the jointly measurable version of the trace) `P(z ∈ γ[0,∞)) = 0` for a.e. `z ∈ ℍ`.
A point of `K_T` that is not on `γ[0,T]` is at positive distance from the whole trace
(`mem_image_or_notMem_closure_of_mem_fwdHull`), which has probability `0` by the density of the
trace for `κ > 8` (`ae_mem_closure_sleTrace_of_eight_lt`). Hence `P(z ∈ K_T) = 0` for a.e. `z ∈ ℍ`,
contradicting `P(z ∈ K_{4/κ}) ≥ 1/2` for all `z ∈ ℍ` near `0` (`HitPos.lean`, the positive half of
[RS05, Lemma 6.5]). [RS05] reach the contradiction through the area of `∂K_t` at a random time
`τ(z)`; we use deterministic times and the hulls `K_u` themselves.

## Main results

* `exists_measure_hullContainsHalfBall_ne_zero_of_eight_lt`: positivity in Lemma 7.3, `κ > 8`.
* `ae_forall_sleHull_halfBall_of_eight_lt`: **[RS05, Lemma 7.3] for `κ > 8`** (simultaneously for
  all `t > 0`, the specification's form).
* `ae_sleTrace_image_eq_Hbar_of_eight_lt`: **[RS05, Corollary 7.4] for `κ > 8`**:
  `γ[0,∞) = \overline{ℍ}` almost surely.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

namespace InteractingSLE

open QuantumZipper QuantumZipper.RS

/-! ### Deterministic facts about Loewner traces -/

/-- The trace point `γ(s)` is a limit of points of `ℍ \ K_s` (the tip). -/
theorem IsLoewnerTrace.mem_closure_compl {W : ℝ → ℝ} {γ : ℝ → ℂ} (hγ : IsLoewnerTrace W γ)
    (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) :
    γ s ∈ closure (H \ fwdHull W s) := by
  have hne : (𝓝[H] (0 : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; show (0 : ℂ).im ≥ 0; simp)
  exact mem_closure_of_tendsto (hγ.tendsto_fwdMapInv_tip hW hW0 hs)
    (eventually_nhdsWithin_of_forall fun w hw => fwdMapInv_mem_compl_fwdHull hW hW0 hs hw)

/-- **A swallowed point is at positive distance from the trace.** For a Loewner trace, a point of
`K_T` not on `γ([0,T])` is not in the closure of `γ([0,∞))`: a small disc around it misses
`γ([0,T])`, lies in a bounded component of `ℍ \ γ([0,T])`, hence in `K_T`, and the later trace stays
in `\overline{ℍ \ K_s} ⊆ \overline{ℍ \ K_T}`. -/
theorem mem_image_or_notMem_closure_of_mem_fwdHull {W : ℝ → ℝ} {γ : ℝ → ℂ}
    (hγ : IsLoewnerTrace W γ) (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ fwdHull W T) :
    z ∈ γ '' Icc 0 T ∨ z ∉ closure (γ '' Ici 0) := by
  by_cases hzA : z ∈ γ '' Icc 0 T
  · exact Or.inl hzA
  right
  set A := γ '' Icc 0 T with hA
  have hAc : IsCompact A := hγ.isCompact_image T
  have hzK := hz
  rw [hγ.2.2 T hT] at hzK
  obtain ⟨hzH, hzF⟩ := hzK
  rw [hAc.isClosed.closure_eq] at hzF
  have hbdd : Bornology.IsBounded (connectedComponentIn (H \ A) z) := by
    rcases hzF with h | h
    · exact absurd h hzA
    · exact h
  have hAne : A.Nonempty := ⟨γ 0, mem_image_of_mem _ ⟨le_rfl, hT⟩⟩
  have hd : 0 < infDist z A := (hAc.isClosed.notMem_iff_infDist_pos hAne).1 hzA
  set r : ℝ := min (infDist z A) z.im with hr
  have hr0 : 0 < r := lt_min hd hzH
  have hball : ball z r ⊆ H \ A := by
    intro w hw
    rw [mem_ball] at hw
    refine ⟨?_, fun hwA => ?_⟩
    · show 0 < w.im
      have := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im, ← dist_eq_norm] at this
      have h2 : dist w z < z.im := hw.trans_le (min_le_right _ _)
      linarith [(abs_le.1 this).1]
    · have := infDist_le_dist_of_mem hwA (x := z)
      rw [dist_comm] at this
      linarith [min_le_left (infDist z A) z.im]
  have hballK : ball z r ⊆ fwdHull W T := by
    intro w hw
    have hsub : ball z r ⊆ connectedComponentIn (H \ A) z :=
      (convex_ball z r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr0) hball
    have hwC := hsub hw
    rw [hγ.2.2 T hT, ← hA]
    refine ⟨(hball hw).1, Or.inr ?_⟩
    rw [hAc.isClosed.closure_eq, ← connectedComponentIn_eq hwC]
    exact hbdd
  have hdisj : ∀ s, 0 ≤ s → γ s ∉ ball z r := by
    intro s hs hsb
    rcases le_total s T with hsT | hTs
    · have hmem : γ s ∈ A := mem_image_of_mem γ (⟨hs, hsT⟩ : s ∈ Icc 0 T)
      have := infDist_le_dist_of_mem hmem (x := z)
      rw [mem_ball, dist_comm] at hsb
      linarith [min_le_left (infDist z A) z.im]
    · have hcl := hγ.mem_closure_compl hW hW0 hs
      have hsub : H \ fwdHull W s ⊆ H \ fwdHull W T := fun w hw =>
        ⟨hw.1, fun h => hw.2 ((fwdHull_mono (W := W)).1 hTs h)⟩
      have hcl' : γ s ∈ closure (H \ fwdHull W T) := closure_mono hsub hcl
      obtain ⟨w, hw1, hw2⟩ := Metric.mem_closure_iff.1 hcl' (r - dist (γ s) z)
        (by rw [mem_ball] at hsb; linarith)
      have : w ∈ ball z r := by
        rw [mem_ball]
        linarith [dist_triangle w (γ s) z, dist_comm w (γ s)]
      exact hw1.2 (hballK this)
  intro hcl
  obtain ⟨w, hw1, hw2⟩ := Metric.mem_closure_iff.1 hcl r hr0
  obtain ⟨s, hs, rfl⟩ := hw1
  exact hdisj s hs (by rw [mem_ball, dist_comm]; exact hw2)

/-! ### The contradiction (spaces in `Type`) -/

section Positivity

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- **Under the contrary hypothesis the trace has zero area**: if for every `t > 0` the hull `K_t`
almost surely fails to contain a half-neighbourhood of `0`, then almost surely
`area(γ[0,∞) ∩ ℍ) = 0`. -/
theorem ae_volume_sleTrace_inter_H_eq_zero_of_forall_measure_eq_zero (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 8 < κ) (hA : ∀ t > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t} = 0) :
    ∀ᵐ ω ∂P, volume (sleTrace κ B ω '' Ici 0 ∩ H) = 0 := by
  have hareas : ∀ n : ℕ, ∀ᵐ ω ∂P, volume (closure (H \ fwdHull (drive κ B ω) ((n : ℝ) + 1)) \
      (H \ fwdHull (drive κ B ω) ((n : ℝ) + 1))) = 0 := fun n =>
    ae_volume_closure_diff_eq_zero hB hκ (by positivity)
  filter_upwards [ae_all_iff.2 hareas,
    ae_trace_inter_H_subset_of_forall_measure_eq_zero hB hκ hA] with ω hω hsub
  refine measure_mono_null ?_ (measure_iUnion_null hω)
  rintro z ⟨⟨s, hs, rfl⟩, hzH⟩
  obtain ⟨n, hn⟩ := exists_nat_gt s
  exact mem_iUnion.2 ⟨n, hsub ((n : ℝ) + 1) ⟨⟨s, ⟨hs, by linarith⟩, rfl⟩, hzH⟩⟩

/-- **Fubini**: under the contrary hypothesis, for almost every `z ∈ ℍ` the trace a.s. misses `z`. -/
theorem ae_measure_mem_sleTrace_eq_zero_of_forall_measure_eq_zero (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 8 < κ) (hA : ∀ t > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t} = 0) :
    ∀ᵐ z ∂(volume.restrict H), P {ω | z ∈ sleTrace κ B ω '' Ici 0} = 0 := by
  obtain ⟨η, -, hηm, hηc, hηeq⟩ := exists_measurable_sleTrace_of_eight_lt hB hκ
  have hHm : MeasurableSet H := isOpen_H.measurableSet
  set S : Set (Ω × ℂ) := {p : Ω × ℂ | p.2 ∈ η p.1 '' Ici 0} ∩ (univ ×ˢ H) with hSdef
  have hS : MeasurableSet S :=
    (Thm11Area.measurableSet_mem_image_Ici hηm hηc).inter (MeasurableSet.univ.prod hHm)
  have himg : ∀ᵐ ω ∂P, η ω '' Ici 0 = sleTrace κ B ω '' Ici 0 :=
    hηeq.mono fun ω h => h.image_eq
  have hprod : (P.prod volume) S = 0 := by
    rw [Measure.prod_apply hS]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [himg, ae_volume_sleTrace_inter_H_eq_zero_of_forall_measure_eq_zero hB hκ hA]
      with ω hi h0
    have e : Prod.mk ω ⁻¹' S = η ω '' Ici 0 ∩ H := by
      ext z; simp [hSdef]
    rw [Pi.zero_apply, e, hi, h0]
  rw [Measure.prod_apply_symm hS] at hprod
  have h := (lintegral_eq_zero_iff (measurable_measure_prodMk_right hS)).1 hprod
  rw [ae_restrict_iff' hHm]
  filter_upwards [h] with z hz hzH
  have e : (fun ω => (ω, z)) ⁻¹' S = {ω | z ∈ η ω '' Ici 0} := by
    ext ω; simp [hSdef, hzH]
  rw [Pi.zero_apply, e] at hz
  rw [← hz]
  refine measure_congr (himg.mono fun ω h => ?_)
  change (z ∈ sleTrace κ B ω '' Ici 0) = (z ∈ η ω '' Ici 0)
  rw [h]

/-- **Under the contrary hypothesis no point of `ℍ` is swallowed with positive probability** (for
almost every `z ∈ ℍ`): `K_T ∩ ℍ ⊆ γ[0,T] ∪ (ℍ \ \overline{γ[0,∞)})`, the first set is a.s. missed
by Fubini, the second is a.s. empty by density. -/
theorem ae_measure_mem_fwdHull_eq_zero_of_forall_measure_eq_zero (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 8 < κ) (hA : ∀ t > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t} = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ z ∂(volume.restrict H), P {ω | z ∈ fwdHull (drive κ B ω) T} = 0 := by
  have hHm : MeasurableSet H := isOpen_H.measurableSet
  have h1 := ae_measure_mem_sleTrace_eq_zero_of_forall_measure_eq_zero hB hκ hA
  rw [ae_restrict_iff' hHm] at h1 ⊢
  filter_upwards [h1] with z hz hzH
  have hden := ae_mem_closure_sleTrace_of_eight_lt hB hκ hzH
  refine measure_mono_null_ae ?_ (measure_union_null (hz hzH) (ae_iff.1 hden))
  filter_upwards [ae_isLoewnerTrace_of_eight_lt hB hκ, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hγ hc h0 hzK
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  rcases mem_image_or_notMem_closure_of_mem_fwdHull hγ hW hW0 hT hzK with h | h
  · exact Or.inl (image_mono Icc_subset_Ici_self h)
  · exact Or.inr h

/-- **Positivity in [RS05, Lemma 7.3] for `κ > 8`** (probability spaces in `Type`). -/
theorem exists_measure_hullContainsHalfBall_ne_zero_of_eight_lt_type (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 8 < κ) :
    ∃ t₀ > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t₀} ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hκ0 : 0 < κ := by linarith
  have hκ4 : 4 < κ := by linarith
  set b : ℝ := 1 - 4 / κ with hbdef
  have hb : 0 < b := by rw [hbdef, sub_pos, div_lt_one hκ0]; linarith
  set α : ℝ := Real.sin (2 * π / κ) with hαdef
  have hα : 0 < α := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [div_lt_iff₀ hκ0]; nlinarith [Real.pi_pos]
  -- the open set of good starting points near `0`
  set U : Set ℂ := {z | ‖z‖ < 1 ∧ ‖z‖ ^ b < α / 4} with hUdef
  have hcont : Continuous fun z : ℂ => ‖z‖ ^ b :=
    continuous_norm.rpow_const fun _ => Or.inr hb.le
  have hUo : IsOpen U :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt hcont continuous_const)
  have hU0 : (0 : ℂ) ∈ U := ⟨by simp, by rw [norm_zero, Real.zero_rpow hb.ne']; positivity⟩
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hUo 0 hU0
  set O : Set ℂ := U ∩ H with hO
  have hOo : IsOpen O := hUo.inter isOpen_H
  have hOne : O.Nonempty := by
    refine ⟨((δ / 2 : ℝ) : ℂ) * I, hδU ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · show 0 < (((δ / 2 : ℝ) : ℂ) * I).im
      simp; positivity
  have hOpos : 0 < volume O := hOo.measure_pos volume hOne
  -- every point of `O` is swallowed with probability `≥ 1/2`
  have hhalf : ∀ z ∈ O, P {ω | z ∈ fwdHull (drive κ B ω) (4 / κ)} ≠ 0 := by
    rintro z ⟨⟨hz1, hzb⟩, hzH⟩
    have h := half_le_measure_mem_fwdHull hB hκ4 hzH hz1 (by rw [← hbdef]; linarith)
    exact (lt_of_lt_of_le (by norm_num) h).ne'
  have hzero := ae_measure_mem_fwdHull_eq_zero_of_forall_measure_eq_zero hB hκ hcon
    (T := 4 / κ) (by positivity)
  have hnull : volume.restrict H O = 0 :=
    measure_mono_null (fun z hz => hhalf z hz) (ae_iff.1 hzero)
  rw [Measure.restrict_apply hOo.measurableSet,
    inter_eq_left.2 (inter_subset_right : O ⊆ H)] at hnull
  exact hOpos.ne' hnull

end Positivity

/-! ### [RS05, Lemma 7.3] and [RS05, Corollary 7.4] for `κ > 8` -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Positivity in [RS05, Lemma 7.3] for `κ > 8`**: for some `t₀ > 0` the hull `K_{t₀}` contains a
half-neighbourhood of `0` with positive probability (any Brownian motion; the probability is a law
quantity, transferred from the canonical path space). -/
theorem exists_measure_hullContainsHalfBall_ne_zero_of_eight_lt (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 8 < κ) :
    ∃ t₀ > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t₀} ≠ 0 := by
  have hP : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨G0, hG0m, hG0c, -, hG0br, -⟩ := exists_good_version0 hB
  set μ : Measure CPath := P.map (toCPath G0 hG0c) with hμ
  have hcan : IsBrownianReal canonBM μ :=
    isBrownianReal_canonBM hG0br.toIsPreBrownianReal hG0m hG0c
  have : IsProbabilityMeasure μ :=
    hcan.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  exact exists_measure_hullContainsHalfBall_ne_zero_of hcan hB
    (exists_measure_hullContainsHalfBall_ne_zero_of_eight_lt_type hcan hκ)

/-- **[RS05, Lemma 7.3] for `κ > 8`**, in the specification's form (simultaneously for all
`t > 0`): almost surely, for every `t > 0` there is `ε > 0` with `K_t ⊇ {z ∈ ℍ : |z| < ε}`. -/
theorem ae_forall_sleHull_halfBall_of_eight_lt (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 < κ) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ sleHull κ B ω t :=
  ae_forall_sleHull_halfBall_of_measure_ne_zero hB κ
    (exists_measure_hullContainsHalfBall_ne_zero_of_eight_lt hB hκ)

/-- **Transience for `κ > 8`** ([RS05, Theorem 7.1]): almost surely `|γ(t)| → ∞`. -/
theorem ae_tendsto_norm_sleTrace_of_eight_lt (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 < κ) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖sleTrace κ B ω t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  exact ae_tendsto_norm_sleTrace_of_interior hB (by linarith) (by linarith) fun _ _ _ _ _ hB' =>
    (ae_forall_sleHull_halfBall_of_eight_lt hB' hκ).mono fun _ h => h 1 one_pos

/-- **[RS05, Corollary 7.4] for `κ > 8`**: almost surely the SLE trace is space-filling,
`γ[0,∞) = \overline{ℍ}`. -/
theorem ae_sleTrace_image_eq_Hbar_of_eight_lt (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 < κ) :
    ∀ᵐ ω ∂P, sleTrace κ B ω '' Ici 0 = Hbar := by
  have : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  exact ae_sleTrace_image_eq_Hbar_of_eight_lt_of_measure_ne_zero hB hκ
    (exists_measure_hullContainsHalfBall_ne_zero_of_eight_lt hB hκ)

end Main

end InteractingSLE
