import QuantumZipper.Proofs.Section5.Prop16NodeCMaskLocal
import QuantumZipper.Proofs.Section5.Prop16MeasScale
import QuantumZipper.Proofs.Section5.Prop16MeasInst
import QuantumZipper.Proofs.Section5.Prop16MeasCoords
import QuantumZipper.Proofs.LQG.WedgeRestriction

/-!
# Proposition 1.6, node C′ (masked): law of the admissible coordinates and a measurable reading

Steps (a) and (c) of task P16-NODEC-MASK:

* `map_admCoords_eq` (**Gaussian uniqueness**): for two mixed GFFs (on any probability spaces)
  the laws of their admissible dyadic circle coordinates `admCoords` agree: the finite-dimensional
  laws are centred Gaussian with the covariance `dualCov` (`WedgeRes.map_eq_of_gaussian_vec`),
  and a law on a countable product is fixed by its finite-dimensional marginals
  (`isProjectiveLimit_map`, `IsProjectiveLimit.unique`: the monotone class lemma, Le Gall,
  *Brownian Motion, Martingales, and Stochastic Calculus* (2016), Appendix A1).
* `palmMaskRead` (**measurable reading**): a measurable map `(ℕ → ℝ) → (ℕ → ℝ)` which, on the
  event that the local area measure of the zoomed reconstruction is a genuine vague limit
  (`goodSet`), equals the masked zoom coordinates of the reconstructed Palm-shifted field. The
  scale is read through the measurable proxy `Meas.M` (sInf over rational radii;
  `sInf_rat_upClosure_eq`), as in `Prop16MeasScale.lean`.

Own elementary bookkeeping, following the project's `aemeasurable_scaleParamOn`
(`Prop16MeasScale.lean`) and `WedgeRes.map_gaussFam_eq₂` (`WedgeRestriction.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization Prop16Area Prop16Area.Meas LQGMeas

/-! ## 1. Gaussian uniqueness for the admissible coordinates -/

open Classical in
/-- Extension by `0` from the admissible indices. -/
def admExt (D S : Set ℂ) (v : {i : ℕ // AdmIdx D S i} → ℝ) : ℕ → ℝ :=
  fun i => if h : AdmIdx D S i then v ⟨i, h⟩ else 0

theorem measurable_admExt (D S : Set ℂ) : Measurable (admExt D S) := by
  classical
  refine measurable_pi_iff.2 fun i => ?_
  unfold admExt
  by_cases h : AdmIdx D S i
  · simp only [h, dite_true]; exact measurable_pi_apply _
  · simp only [h, dite_false]; exact measurable_const

theorem admCoords_eq_admExt (D S : Set ℂ) (x : FieldSample) :
    admCoords D S x = admExt D S fun i =>
      x (foldedCircle (dyadicIndex i.1).1 (radius (dyadicIndex i.1).2)) := by
  classical
  funext i
  unfold admCoords admExt
  by_cases h : AdmIdx D S i
  · simp only [h, if_true, dite_true, coords]
  · simp only [h, if_false, dite_false]

theorem measurable_admCoords {Ω : Type*} [MeasurableSpace Ω] {D S : Set ℂ} {X : Ω → FieldSample}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) :
    Measurable fun ω => admCoords D S (X ω) := by
  simp_rw [admCoords_eq_admExt]
  exact (measurable_admExt D S).comp (measurable_pi_iff.2 fun i => hX _)

/-- **Gaussian uniqueness**: the admissible coordinates of two mixed GFFs have the same law. -/
theorem map_admCoords_eq {D S : Set ℂ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X : Ω → FieldSample} {X' : Ω' → FieldSample} (hX : IsMixedGFF D S X P)
    (hX' : IsMixedGFF D S X' P') :
    P.map (fun ω => admCoords D S (X ω)) = P'.map (fun ω => admCoords D S (X' ω)) := by
  set I := {i : ℕ // AdmIdx D S i}
  set p : I → {μ // IsAdmissibleDual D (mixedSpace D S) μ} := fun i =>
    ⟨foldedCircle (dyadicIndex i.1).1 (radius (dyadicIndex i.1).2), i.2⟩ with hp
  set Z : I → Ω → ℝ := fun i ω => X ω (p i).1 with hZ
  set Z' : I → Ω' → ℝ := fun i ω => X' ω (p i).1 with hZ'
  have hG : IsGaussianProcess Z P := hX.gaussian.comp_right p
  have hG' : IsGaussianProcess Z' P' := hX'.gaussian.comp_right p
  have hZm : ∀ i, Measurable (Z i) := fun i => hX.measurable_coord _
  have hZm' : ∀ i, Measurable (Z' i) := fun i => hX'.measurable_coord _
  have hmain : P.map (fun ω i => Z i ω) = P'.map (fun ω i => Z' i ω) := by
    have h1 := isProjectiveLimit_map (P := P) (X := Z) (measurable_pi_iff.2 hZm).aemeasurable
    have h2 := isProjectiveLimit_map (P := P') (X := Z') (measurable_pi_iff.2 hZm').aemeasurable
    have e : (fun J : Finset I => P'.map fun ω => J.restrict fun i => Z' i ω) =
        fun J => P.map fun ω => J.restrict fun i => Z i ω := by
      funext J
      exact (WedgeRes.map_eq_of_gaussian_vec (U := fun i : J => Z i) (V := fun i : J => Z' i)
        (hG.hasGaussianLaw J) (hG'.hasGaussianLaw J) (fun i => hZm i) (fun i => hZm' i)
        (fun i => (hG.hasGaussianLaw_eval i).memLp_two)
        (fun i => (hG'.hasGaussianLaw_eval i).memLp_two)
        (fun i => hX.centered _ (p i).2) (fun i => hX'.centered _ (p i).2)
        (fun i j => by
          rw [hX.covariance_eq _ _ (p i).2 (p j).2, hX'.covariance_eq _ _ (p i).2 (p j).2])).symm
    rw [e] at h2
    exact h1.unique h2
  have e1 : (fun ω => admCoords D S (X ω)) = admExt D S ∘ fun ω i => Z i ω := by
    funext ω; exact admCoords_eq_admExt D S (X ω)
  have e2 : (fun ω => admCoords D S (X' ω)) = admExt D S ∘ fun ω i => Z' i ω := by
    funext ω; exact admCoords_eq_admExt D S (X' ω)
  rw [e1, e2, ← Measure.map_map (measurable_admExt D S) (measurable_pi_iff.2 hZm),
    ← Measure.map_map (measurable_admExt D S) (measurable_pi_iff.2 hZm'), hmain]

/-! ## 2. A measurable reading of the masked coordinates -/

/-- The `sInf` of an up-closed set of positive reals is read at rational points. -/
theorem sInf_rat_upClosure_eq (S0 : Set ℝ) (hup : ∀ a b, a ∈ S0 → a ≤ b → b ∈ S0)
    (hpos : ∀ a ∈ S0, 0 < a) :
    sInf {a : ℝ | 0 < a ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧ (q : ℝ) ∈ S0} = sInf S0 := by
  set S' := {a : ℝ | 0 < a ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧ (q : ℝ) ∈ S0} with hS'
  have hsub : S' ⊆ S0 := fun a ⟨_, q, _, hqa, hq⟩ => hup _ _ hq hqa
  have hbdd : ∀ T : Set ℝ, T ⊆ S0 → BddBelow T := fun T hT =>
    ⟨0, fun a ha => (hpos a (hT ha)).le⟩
  rcases S0.eq_empty_or_nonempty with h0 | hne
  · have : S' = ∅ := Set.eq_empty_of_subset_empty (h0 ▸ hsub)
    rw [this, h0]
  · have hrat : ∀ a ∈ S0, ∀ q : ℚ, a < q → (q : ℝ) ∈ S' := fun a ha q hq =>
      ⟨lt_trans (hpos a ha) hq, q, lt_trans (hpos a ha) hq, le_rfl, hup _ _ ha hq.le⟩
    obtain ⟨a0, ha0⟩ := hne
    obtain ⟨q0, hq0⟩ := exists_rat_gt a0
    have hne' : S'.Nonempty := ⟨_, hrat a0 ha0 q0 hq0⟩
    refine le_antisymm ?_ (csInf_le_csInf (hbdd S0 le_rfl) hne' hsub)
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨a, ha, hlt⟩ := exists_lt_of_csInf_lt ⟨a0, ha0⟩ (show sInf S0 < sInf S0 + ε / 2 by
      linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show a < a + ε / 2 by linarith)
    calc sInf S' ≤ q := csInf_le (hbdd S' hsub) (hrat a ha q hq1)
      _ < sInf S0 + ε := by linarith

variable (γ C : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) (x : ℝ)

/-- The Palm-shifted field reconstructed from coordinates. -/
def palmFam (v : ℕ → ℝ) : FieldSample :=
  reconstruct v + (γ / 2) • mixedGreenSample D (realSet (Icc c d)) x

/-- The reconstruction of its zoomed field (a measurable function of `v`). -/
def palmZr (v : ℕ → ℝ) : FieldSample :=
  recon (zoomFree γ C h0 (palmFam γ D c d x) (v, x))

/-- The cut-offs of `D − x`. -/
def palmPhi : ℕ → (ℕ → ℝ) → ℂ → ℝ := fun n _ z => openBump D n (z + (x : ℂ))

/-- The measurable scale proxy. -/
def palmScaleProxy (v : ℕ → ℝ) : ℝ :=
  sInf {s : ℝ | 0 < s ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ s ∧
    1 ≤ M γ (palmZr γ C D c d h0 x) (palmPhi D x) v q}

/-- **The measurable reading** of the masked zoom coordinates. -/
def palmMaskRead (v : ℕ → ℝ) : ℕ → ℝ :=
  maskCoords D a b (palmScaleProxy γ C D c d h0 x v) x
    (coords (rescale (reconstruct (coords (zoomFree γ C h0 (palmFam γ D c d x) (v, x))))
      (Qc γ) (palmScaleProxy γ C D c d h0 x v)))

variable {γ C D c d a b h0 x}

theorem measurable_coords_palmZoom :
    Measurable fun v : ℕ → ℝ => coords (zoomFree γ C h0 (palmFam γ D c d x) (v, x)) := by
  have hF : ∀ μ : Measure ℂ, Measurable fun v : ℕ → ℝ => palmFam γ D c d x v μ := fun μ =>
    ((measurable_pi_apply μ).comp measurable_reconstruct).add measurable_const
  have e0 : ∀ v, ofFun (fun _ => (0 : ℝ)) + palmFam γ D c d x v = palmFam γ D c d x v :=
    fun v => by funext μ; simp [ofFun]
  have hZ : Measurable fun v : ℕ → ℝ => coords (zoomField γ C (palmFam γ D c d x v) x) := by
    have := (measurable_coords_zoomField γ C (fun _ => (0 : ℝ)) hF).comp
      (measurable_id.prodMk measurable_const : Measurable fun v : ℕ → ℝ => (v, x))
    simpa only [Function.comp_def, id_eq, e0] using this
  refine measurable_pi_iff.2 fun i => ?_
  have e : (fun v : ℕ → ℝ => coords (zoomFree γ C h0 (palmFam γ D c d x) (v, x)) i) = fun v =>
      coords (zoomField γ C (palmFam γ D c d x v) x) i +
        h0 x * ((foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)) univ).toReal := by
    funext v; rfl
  rw [e]
  exact ((measurable_pi_apply i).comp hZ).add measurable_const

theorem measurable_palmZr : Measurable (palmZr γ C D c d h0 x) :=
  measurable_reconstruct.comp measurable_coords_palmZoom

theorem isBumpFamily_palmPhi (hDo : IsOpen D) (hDH : D ⊆ H) :
    IsBumpFamily (fun _ : ℕ → ℝ => zoomDomain D x) (palmPhi D x) := by
  have hDc : Dᶜ.Nonempty := ⟨0, fun h => by simpa [H] using hDH h⟩
  exact isBumpFamily_comp (α := ℕ → ℝ) hDo hDc (g := fun _ z => z + (x : ℂ)) (by fun_prop)
    (fun _ => by fun_prop)

theorem measurable_palmScaleProxy (hDo : IsOpen D) (hDH : D ⊆ H) :
    Measurable (palmScaleProxy γ C D c d h0 x) := by
  have hM := fun q : ℚ => measurable_M (γ := γ)
    (measurable_palmZr (γ := γ) (C := C) (D := D) (c := c) (d := d) (h0 := h0) (x := x))
    (isBumpFamily_palmPhi (x := x) hDo hDH) (q : ℝ)
  refine LQGMeas.measurable_sInf_upClosed _ (fun r => ?_) (fun v s t hs hst => ?_)
    (fun v s hs => hs.1)
  · have e : {v : ℕ → ℝ | (r : ℝ) ∈ {s : ℝ | 0 < s ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ s ∧
        1 ≤ M γ (palmZr γ C D c d h0 x) (palmPhi D x) v q}} =
        {_v | 0 < (r : ℝ)} ∩ ⋃ q : ℚ, ({_v | 0 < (q : ℝ) ∧ (q : ℝ) ≤ r} ∩
          {v | 1 ≤ M γ (palmZr γ C D c d h0 x) (palmPhi D x) v q}) := by
      ext v; simp only [mem_setOf_eq, mem_inter_iff, mem_iUnion, and_assoc]
    rw [e]
    exact (MeasurableSet.const _).inter (MeasurableSet.iUnion fun q =>
      (MeasurableSet.const _).inter (measurableSet_le measurable_const (hM q)))
  · obtain ⟨h1, q, hq0, hqs, hq⟩ := hs
    exact ⟨lt_of_lt_of_le h1 hst, q, hq0, hqs.trans hst, hq⟩

theorem measurable_palmMaskRead (hDo : IsOpen D) (hDH : D ⊆ H) :
    Measurable (palmMaskRead γ C D c d a b h0 x) := by
  have hs := measurable_palmScaleProxy (γ := γ) (C := C) (c := c) (d := d) (h0 := h0) (x := x) hDo hDH
  exact (measurable_maskCoords D a b).comp (hs.prodMk (measurable_const.prodMk
    ((measurable_coords_rescale_reconstruct (Qc γ)).comp
      (measurable_coords_palmZoom.prodMk hs))))

/-- **On the good event the reading is exact.** -/
theorem palmMaskRead_eq (hDo : IsOpen D) (hDH : D ⊆ H) {v : ℕ → ℝ}
    (hv : v ∈ goodSet γ (palmZr γ C D c d h0 x) fun _ => zoomDomain D x) :
    palmMaskRead γ C D c d a b h0 x v = palmCanonMask γ C D a b h0 (palmFam γ D c d x) (v, x) := by
  have hsc : palmScaleProxy γ C D c d h0 x v = palmScale γ C D h0 (palmFam γ D c d x) (v, x) := by
    unfold palmScaleProxy
    have e : ∀ q : ℚ, M γ (palmZr γ C D c d h0 x) (palmPhi D x) v q =
        qAreaMeasureOn γ (palmZr γ C D c d h0 x v) (zoomDomain D x) (hb q) := fun q =>
      (measure_eq_M (isBumpFamily_palmPhi hDo hDH) hv q).symm
    simp_rw [e]
    have := sInf_rat_upClosure_eq
      {s : ℝ | 0 < s ∧ 1 ≤ qAreaMeasureOn γ (palmZr γ C D c d h0 x v) (zoomDomain D x) (hb s)}
      (fun s t hs hst => ⟨lt_of_lt_of_le hs.1 hst, hs.2.trans (measure_mono
        (inter_subset_inter_left _ (Metric.ball_subset_ball hst)))⟩) (fun s hs => hs.1)
    simp only [mem_setOf_eq] at this
    rw [show (fun s : ℝ => 0 < s ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ s ∧
        1 ≤ qAreaMeasureOn γ (palmZr γ C D c d h0 x v) (zoomDomain D x) (hb q)) =
        fun s => 0 < s ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ s ∧ 0 < (q : ℝ) ∧
        1 ≤ qAreaMeasureOn γ (palmZr γ C D c d h0 x v) (zoomDomain D x) (hb q) from by
      funext s; apply propext; constructor
      · rintro ⟨h1, q, h2, h3, h4⟩; exact ⟨h1, q, h2, h3, h2, h4⟩
      · rintro ⟨h1, q, h2, h3, -, h4⟩; exact ⟨h1, q, h2, h3, h4⟩]
    rw [this]
    exact scaleParamOn_recon γ _ _
  show maskCoords D a b _ x _ = maskCoords D a b _ x _
  rw [hsc]
  congr 1
  show _ = coords (canonicalOn γ _ _)
  unfold canonicalOn
  rw [rescale_reconstruct_coords]
  rfl

end Prop16Asm

end QuantumZipper
