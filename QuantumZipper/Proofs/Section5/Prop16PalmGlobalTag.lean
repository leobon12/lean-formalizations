import QuantumZipper.Proofs.Section5.Prop16NodeB2Rep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node `Prop16PalmGlobalStmt`: local hypotheses on compacts and the tagged field

Two ingredients for the global window Palm formula (`Prop16PalmGlobal.lean`).

* `exists_mixedLocalHyp_pg`: every compact `K ⊆ D ∪ (a,b)` satisfies the K3 local hypotheses
  `MixedLocalHyp` (uniform local discs), so M6 (`K3.mixedLocalKernel`) gives the mixed
  covariance on `K` in kernel form.
* The **tagged field** `tagField Kw X ι μ`: the window-masked field `maskK Kw X` (which carries the
  boundary measure on the window) with the global coordinates `X(μ_j)` attached at the auxiliary
  indices `ι_j = (μ_j)(· - τ_j)` (translates of `μ_j` into disjoint horizontal strips of the lower
  half-plane). No folded circle is an `ι_j`, so the regularization, the boundary approximations
  and the variances are those of the masked field, while the coordinates are the global ones.
  This lets the abstract Palm formula `PalmNorm.palm_lintegral_coords` (one Gaussian field and
  its coordinates) be applied with coordinates carried outside the window set. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-! ## 1. Local discs on compacts of `D ∪ (a,b)` -/

section Geom

variable {D : Set ℂ} {c d a b : ℝ}

/-- `D ∪ (a,b) ∪ {Im < 0}` is open. -/
theorem isOpen_union_lower_pg (hgeom : K3.Prop16Geometry D c d) (hca : c ≤ a) (hbd : b ≤ d) :
    IsOpen (D ∪ realSet (Ioo a b) ∪ {w : ℂ | w.im < 0}) := by
  obtain ⟨hDo, -, -, hDH, -, -, hdisc⟩ := hgeom
  rw [Metric.isOpen_iff]
  rintro z ((hz | ⟨t, ht, rfl⟩) | hz)
  · obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 hDo z hz
    exact ⟨ε, hε, fun w hw => Or.inl (Or.inl (hb hw))⟩
  · obtain ⟨r, hr, hrD⟩ := hdisc t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨min r (min (t - a) (b - t)), lt_min hr (lt_min (by linarith [ht.1])
      (by linarith [ht.2])), fun w hw => ?_⟩
    have hw' := mem_ball.1 hw
    rcases lt_trichotomy w.im 0 with h | h | h
    · exact Or.inr h
    · refine Or.inl (Or.inr ⟨w.re, ?_, Complex.ext (by simp) (by simp [h])⟩)
      have h1 : |w.re - t| ≤ dist w (t : ℂ) := by
        rw [Complex.dist_eq]
        have := Complex.abs_re_le_norm (w - (t : ℂ))
        simpa using this
      have h2 := abs_lt.1 (lt_of_le_of_lt h1 (lt_of_lt_of_le hw' (min_le_right _ _)))
      constructor
      · linarith [h2.1, min_le_left (t - a) (b - t)]
      · linarith [h2.2, min_le_right (t - a) (b - t)]
    · exact Or.inl (Or.inl (hrD ⟨lt_of_lt_of_le hw' (min_le_left _ _), h⟩))
  · refine ⟨-z.im, by simpa using hz, fun w hw => Or.inr ?_⟩
    have h1 : |w.im - z.im| ≤ dist w z := by
      rw [Complex.dist_eq]
      have := Complex.abs_im_le_norm (w - z)
      simpa using this
    have h2 := abs_lt.1 (lt_of_le_of_lt h1 (mem_ball.1 hw))
    show w.im < 0
    linarith [h2.2]

/-- A local disc from `closedBall z R ∩ ℍ̄ ⊆ D ∪ (a,b)`. -/
theorem localBall_of_subset_pg (hgeom : K3.Prop16Geometry D c d) (hca : c ≤ a) (hbd : b ≤ d)
    {z : ℂ} (hz : z ∈ Hbar) {R : ℝ} (hR : 0 < R)
    (hsub : closedBall z R ∩ Hbar ⊆ D ∪ realSet (Ioo a b)) :
    K3.LocalBall D (realSet (Icc c d)) z R := by
  obtain ⟨hDo, -, -, hDH, -, hfront, -⟩ := hgeom
  have hreal : ∀ t ∈ Ioo a b, (t : ℂ) ∈ frontier D := by
    intro t ht
    have : (t : ℂ) ∈ realSet (Icc c d) :=
      ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
    rw [← hfront] at this
    exact this.1
  refine ⟨hz, hR, hDH, fun w hw => ?_, fun w hw => ?_⟩
  · rcases hsub hw with h | ⟨t, ht, rfl⟩
    · exact subset_closure h
    · exact frontier_subset_closure (hreal t ht)
  · have hwc : w ∈ closure D := frontier_subset_closure hw.2
    have hwH : w ∈ Hbar := (closure_minimal (fun u (hu : u ∈ D) =>
      show u ∈ Hbar from le_of_lt (show (0 : ℝ) < u.im from hDH hu)) isClosed_Hbar) hwc
    rcases hsub ⟨hw.1, hwH⟩ with h | ⟨t, ht, rfl⟩
    · have := hw.2
      rw [hDo.frontier_eq] at this
      exact absurd h this.2
    · have : (t : ℂ) ∈ frontier D ∩ {z : ℂ | z.im = 0} := ⟨hw.2, by simp⟩
      rw [hfront] at this
      exact this

/-- **Every compact subset of `D ∪ (a,b)` satisfies the K3 local hypotheses.** -/
theorem exists_mixedLocalHyp_pg (hgeom : K3.Prop16Geometry D c d) (hca : c ≤ a) (hbd : b ≤ d)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ D ∪ realSet (Ioo a b)) :
    ∃ R > 0, K3.MixedLocalHyp D (realSet (Icc c d)) K R := by
  obtain ⟨δ, hδ, hδsub⟩ :=
    hK.exists_cthickening_subset_open (isOpen_union_lower_pg hgeom hca hbd)
      (hKsub.trans subset_union_left)
  obtain ⟨hDo, -, hDb, hDH, -, -, -⟩ := id hgeom
  refine ⟨δ / 2, by positivity, ⟨hDo, hDH, hDb, ?_, hK, by positivity, fun z hz => ?_⟩⟩
  · rintro _ ⟨s, -, rfl⟩; simp
  · have hzH : z ∈ Hbar := by
      rcases hKsub hz with h | ⟨t, -, rfl⟩
      · show (0 : ℝ) ≤ z.im; exact le_of_lt (hDH h)
      · show (0 : ℝ) ≤ ((t : ℂ)).im; simp
    refine localBall_of_subset_pg hgeom hca hbd hzH (by positivity) fun w hw => ?_
    have hwK : w ∈ cthickening δ K :=
      mem_cthickening_of_dist_le w z δ K hz (by
        have := mem_closedBall.1 hw.1; linarith)
    rcases hδsub hwK with h | h
    · exact h
    · exact absurd (show (0 : ℝ) ≤ w.im from hw.2) (not_le.2 h)

end Geom

/-! ## 2. Tags in the lower half-plane -/

section Tag

/-- The tag translation of the `j`-th coordinate: `-(j s + ρ + 1) i`. -/
def tagShift (ρ s : ℝ) (j : ℕ) : ℂ := ⟨0, -((j : ℝ) * s + ρ + 1)⟩

/-- The strip index `⌊-Im w / s⌋₊`. -/
def tagIndex (s : ℝ) (w : ℂ) : ℕ := ⌊-w.im / s⌋₊

/-- The tagged index measures `ι_j = (μ_j)(· - τ_j)`. -/
def tagMeas (ρ s : ℝ) (μ : ℕ → Measure ℂ) (j : ℕ) : Measure ℂ :=
  (μ j).map fun z => z + tagShift ρ s j

/-- The strip `{0 ≤ Im ≤ ρ}` carrying the coordinates. -/
def tagBand (ρ : ℝ) : Set ℂ := {z | 0 ≤ z.im ∧ z.im ≤ ρ}

theorem measurable_add_tagShift (ρ s : ℝ) (j : ℕ) :
    Measurable fun z : ℂ => z + tagShift ρ s j := measurable_id.add_const _

theorem tagIndex_add (ρ : ℝ) {j : ℕ} {z : ℂ} (hρ : 0 ≤ ρ) (hz : z ∈ tagBand ρ) :
    tagIndex (ρ + 2) (z + tagShift ρ (ρ + 2) j) = j := by
  unfold tagIndex
  have hs : (0 : ℝ) < ρ + 2 := by linarith
  have e : (z + tagShift ρ (ρ + 2) j).im = z.im - ((j : ℝ) * (ρ + 2) + ρ + 1) := by
    simp [tagShift]; ring
  rw [e, Nat.floor_eq_iff (div_nonneg (by nlinarith [hz.2, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    hs.le), le_div_iff₀ hs, div_lt_iff₀ hs]
  constructor <;> nlinarith [hz.1, hz.2]

theorem im_add_tagShift_neg {ρ : ℝ} (hρ : 0 ≤ ρ) {j : ℕ} {z : ℂ} (hz : z ∈ tagBand ρ) :
    (z + tagShift ρ (ρ + 2) j).im < 0 := by
  simp only [tagShift, Complex.add_im]
  nlinarith [hz.2, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

variable {ρ : ℝ} {μ : ℕ → Measure ℂ}

/-- `ι_j` is carried by the strip of index `j`. -/
theorem tagMeas_ae (hρ : 0 ≤ ρ) (hμ : ∀ j, μ j (tagBand ρ)ᶜ = 0) (j : ℕ) :
    ∀ᵐ w ∂(tagMeas ρ (ρ + 2) μ j), tagIndex (ρ + 2) w = j ∧ w.im < 0 := by
  unfold tagMeas
  rw [ae_map_iff (measurable_add_tagShift ρ _ j).aemeasurable]
  · have hb : ∀ᵐ z ∂(μ j), z ∈ tagBand ρ := by rw [ae_iff]; exact hμ j
    filter_upwards [hb] with z hz
    exact ⟨tagIndex_add ρ hρ hz, im_add_tagShift_neg hρ hz⟩
  · exact (measurableSet_eq_fun ((Nat.measurable_floor.comp
      ((Complex.measurable_im.neg).div_const _))) measurable_const).inter
      (measurableSet_lt Complex.measurable_im measurable_const)

theorem tagMeas_inj (hρ : 0 ≤ ρ) (hμ : ∀ j, μ j (tagBand ρ)ᶜ = 0) {i j : ℕ}
    (h : tagMeas ρ (ρ + 2) μ i = tagMeas ρ (ρ + 2) μ j) : μ i = μ j := by
  by_cases hij : i = j
  · rw [hij]
  have h0 : ∀ k, tagMeas ρ (ρ + 2) μ k = 0 → μ k = 0 := fun k hk =>
    (Measure.map_eq_zero_iff (measurable_add_tagShift ρ _ k).aemeasurable).1 hk
  have hi := tagMeas_ae hρ hμ i
  have hj := tagMeas_ae hρ hμ j
  rw [h] at hi
  have hz : tagMeas ρ (ρ + 2) μ j = 0 := by
    rw [← Measure.measure_univ_eq_zero]
    have h3 : ∀ᵐ w ∂(tagMeas ρ (ρ + 2) μ j), False := by
      filter_upwards [hi, hj] with w h1 h2
      exact hij (h1.1.symm.trans h2.1)
    simpa [ae_iff] using h3
  rw [h0 j hz, h0 i (h.trans hz)]

/-- No folded circle is a tag. -/
theorem tagMeas_ne_foldedCircle (hρ : 0 ≤ ρ) (hμ : ∀ j, μ j (tagBand ρ)ᶜ = 0) (j : ℕ) (z : ℂ)
    (r : ℝ) : tagMeas ρ (ρ + 2) μ j ≠ foldedCircle z r := by
  intro h
  have h1 := tagMeas_ae hρ hμ j
  rw [h] at h1
  have h2 : ∀ᵐ w ∂(foldedCircle z r), 0 ≤ w.im := by
    unfold foldedCircle
    rw [ae_map_iff measurable_foldH.aemeasurable (measurableSet_le measurable_const
      Complex.measurable_im)]
    refine ae_of_all _ fun w => ?_
    unfold foldH
    split_ifs with hw
    · exact hw
    · simp only [Complex.conj_im]; linarith [not_le.1 hw]
  have h3 : ∀ᵐ w ∂(foldedCircle z r), False := by
    filter_upwards [h1, h2] with w hw1 hw2
    exact absurd hw2 (not_le.2 hw1.2)
  have := measure_univ (μ := foldedCircle z r)
  rw [ae_iff] at h3
  simp at h3

open Classical in
/-- **The tagged field**: `X(μ_j)` at the tag `ι_j`, the window-masked field elsewhere. -/
def tagField (Kw : Set ℂ) {Ω : Type} (X : Ω → FieldSample) (ι μ : ℕ → Measure ℂ) (ω : Ω) :
    FieldSample := fun ν => if h : ∃ j, ι j = ν then X ω (μ h.choose) else maskK Kw X ω ν

theorem tagField_tag {Kw : Set ℂ} {Ω : Type} {X : Ω → FieldSample} {ι μ : ℕ → Measure ℂ}
    (hinj : ∀ i j, ι i = ι j → μ i = μ j) (ω : Ω) (j : ℕ) :
    tagField Kw X ι μ ω (ι j) = X ω (μ j) := by
  have h : ∃ i, ι i = ι j := ⟨j, rfl⟩
  simp only [tagField, dif_pos h]
  rw [hinj _ _ h.choose_spec]

theorem tagField_of_not {Kw : Set ℂ} {Ω : Type} {X : Ω → FieldSample} {ι μ : ℕ → Measure ℂ}
    {ν : Measure ℂ} (hν : ∀ j, ι j ≠ ν) (ω : Ω) :
    tagField Kw X ι μ ω ν = maskK Kw X ω ν := by
  have h : ¬ ∃ j, ι j = ν := fun ⟨j, hj⟩ => hν j hj
  simp only [tagField, dif_neg h]

/-- **The tagged field is a centered Gaussian field.** -/
theorem isCenteredGaussianField_tagField {D S Kw : Set ℂ} {R : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} (hL : K3.MixedLocalHyp D S Kw R)
    (hX : IsMixedGFF D S X P) {ι μ : ℕ → Measure ℂ}
    (hadm : ∀ j, IsAdmissibleDual D (mixedSpace D S) (μ j)) :
    Palm.IsCenteredGaussianField P (tagField Kw X ι μ) := by
  classical
  refine ⟨?_, fun ν => ?_, fun ν => ?_⟩
  · refine hX.gaussian.of_isGaussianProcess fun ν => ?_
    by_cases h : ∃ j, ι j = ν
    · let t : {μ : Measure ℂ // IsAdmissibleDual D (mixedSpace D S) μ} :=
        ⟨μ h.choose, hadm _⟩
      refine ⟨{t}, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({t} : Finset _) => ℝ)
        ⟨t, Finset.mem_singleton_self t⟩, fun ω => ?_⟩
      simp only [ContinuousLinearMap.proj_apply, Finset.restrict, tagField, dif_pos h]
      rfl
    · by_cases hμ : KAdm Kw ν
      · let t : {μ : Measure ℂ // IsAdmissibleDual D (mixedSpace D S) μ} :=
          ⟨ν, isAdmissibleDual_of_localHyp hL hμ.1 hμ.2⟩
        refine ⟨{t}, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({t} : Finset _) => ℝ)
          ⟨t, Finset.mem_singleton_self t⟩, fun ω => ?_⟩
        simp only [ContinuousLinearMap.proj_apply, Finset.restrict, tagField, dif_neg h]
        exact maskK_of_KAdm hμ ω
      · exact ⟨∅, 0, fun ω => by
          simp only [ContinuousLinearMap.zero_apply, tagField, dif_neg h]
          exact maskK_of_not hμ ω⟩
  · by_cases h : ∃ j, ι j = ν
    · simp only [tagField, dif_pos h]; exact hX.measurable_coord _
    · simp only [tagField, dif_neg h]
      by_cases hμ : KAdm Kw ν
      · simp_rw [maskK_of_KAdm hμ]; exact hX.measurable_coord ν
      · simp_rw [maskK_of_not hμ]; exact measurable_const
  · by_cases h : ∃ j, ι j = ν
    · simp only [tagField, dif_pos h]; exact hX.centered _ (hadm _)
    · simp only [tagField, dif_neg h]
      by_cases hμ : KAdm Kw ν
      · simp_rw [maskK_of_KAdm hμ]
        exact hX.centered ν (isAdmissibleDual_of_localHyp hL hμ.1 hμ.2)
      · simp_rw [maskK_of_not hμ]; simp

end Tag

end Prop16Asm

end QuantumZipper
