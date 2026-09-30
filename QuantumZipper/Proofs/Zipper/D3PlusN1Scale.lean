import QuantumZipper.Proofs.Zipper.D3PlusN1Model
import QuantumZipper.Proofs.Section5.Prop16MeasScale
import QuantumZipper.Proofs.Section5.Prop16MeasInst
import QuantumZipper.Proofs.Section5.Prop16MeasCoords

/-!
# D3⁺(i), node N1 (part 3): the factorization maps `Tm`

On the parameter space `N1Idx r = (LocIdx r → ℝ) × FieldSample` (local values `s`, macroscopic
data `f`) we define

* `scaleSur γ L r p`: a **measurable** surrogate of the local scale
  `scaleParamOn γ (locModel γ L r p) (halfDisc r)`: the infimum of the rationals `q > 0` at which
  the measurable functional `Prop16Area.Meas.M` (sup of limits of pre-limit area integrals of
  bumps, `Prop16MeasScale.lean`) reaches `1`, made up-closed. On the event where the local area
  measure is a genuine vague limit (`goodSet`) it equals the local scale (`scaleSur_eq`; own
  elementary lemma `sInf_rat_eq` for monotone functions).
* `zoomN1 γ L r p = rescale (locModel γ L r p) (Qc γ) (scaleSur γ L r p)` and the maps
  `TmN1 γ r R L = locField R ∘ zoomN1` (D23 data) and `TmRichN1 γ r R L = locFieldFull R ∘ zoomN1`
  (D25 rich data), both measurable (`measurable_TmN1`, `measurable_TmRichN1`; every coordinate
  is a raw value at an s-finite measure, `Prop16Area.measurable_rescale_apply_joint`).

Own elementary arguments (measurability plumbing; AGENT_GUIDE cost rule), following
`Prop16Area.Meas.aemeasurable_scaleParamOn`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace D3Plus

/-- The parameter space of the factorization: local values and macroscopic data. -/
abbrev N1Idx (r : ℝ) : Type := (LocIdx r → ℝ) × FieldSample

/-- The bump family exhausting `halfDisc r` (parameter-independent). -/
def bumpHD (r : ℝ) : ℕ → N1Idx r → ℂ → ℝ := fun n _ z => LQGMeas.openBump (halfDisc r) n z

theorem isBumpFamily_bumpHD (r : ℝ) :
    Prop16Area.Meas.IsBumpFamily (fun _ : N1Idx r => halfDisc r) (bumpHD r) :=
  Prop16Area.Meas.isBumpFamily_comp (isOpen_halfDisc r) ⟨0, fun h => by simpa [H] using h.2⟩
    (g := fun _ z => z) measurable_snd (fun _ => continuous_id)

/-- **Own elementary lemma.** For monotone `f`, the infimum of the up-closure of the rationals
`q > 0` with `1 ≤ f q` is the infimum of the reals `a > 0` with `1 ≤ f a`. -/
theorem sInf_rat_eq {f : ℝ → ℝ≥0∞} (hf : Monotone f) :
    sInf {a : ℝ | ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧ 1 ≤ f q} =
      sInf {a : ℝ | 0 < a ∧ 1 ≤ f a} := by
  set S := {a : ℝ | ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧ 1 ≤ f q}
  set T := {a : ℝ | 0 < a ∧ 1 ≤ f a}
  have hST : S ⊆ T := fun a ⟨q, h0, hqa, h1⟩ => ⟨h0.trans_le hqa, h1.trans (hf hqa)⟩
  have hbT : BddBelow T := ⟨0, fun a ha => ha.1.le⟩
  have hbS : BddBelow S := hbT.mono hST
  rcases T.eq_empty_or_nonempty with hT | hT
  · have hS : S = ∅ := Set.subset_empty_iff.1 (hT ▸ hST)
    rw [hS, hT]
  · have key : ∀ a ∈ T, ∀ δ > 0, ∃ b ∈ S, b < a + δ := by
      intro a ha δ hδ
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right a hδ)
      exact ⟨q, ⟨q, ha.1.trans hq1, le_rfl, ha.2.trans (hf hq1.le)⟩, hq2⟩
    obtain ⟨a0, ha0⟩ := hT
    obtain ⟨b0, hb0, -⟩ := key a0 ha0 1 one_pos
    apply le_antisymm
    · refine le_csInf ⟨a0, ha0⟩ fun a ha => le_of_forall_pos_lt_add fun δ hδ => ?_
      obtain ⟨b, hb, hlt⟩ := key a ha δ hδ
      exact (csInf_le hbS hb).trans_lt hlt
    · exact csInf_le_csInf hbT ⟨b0, hb0⟩ hST

/-- The measurable surrogate of the local scale of `locModel γ L r p`. -/
def scaleSur (γ L r : ℝ) (p : N1Idx r) : ℝ :=
  sInf {a : ℝ | ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧
    1 ≤ Prop16Area.Meas.M γ (locModel γ L r) (bumpHD r) p q}

theorem measurable_scaleSur (γ L r : ℝ) : Measurable (scaleSur γ L r) := by
  refine LQGMeas.measurable_sInf_upClosed _ (fun q' => ?_)
    (fun p a b ⟨q, h0, hqa, h1⟩ hab => ⟨q, h0, hqa.trans hab, h1⟩)
    (fun p a ⟨q, h0, hqa, _⟩ => h0.trans_le hqa)
  have e : {p : N1Idx r | ((q' : ℚ) : ℝ) ∈ {a : ℝ | ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧
      1 ≤ Prop16Area.Meas.M γ (locModel γ L r) (bumpHD r) p q}} =
      ⋃ q : ℚ, {_p : N1Idx r | 0 < (q : ℝ) ∧ (q : ℝ) ≤ q'} ∩
        {p | 1 ≤ Prop16Area.Meas.M γ (locModel γ L r) (bumpHD r) p q} := by
    ext p
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff, and_assoc]
  rw [e]
  exact MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter
    (measurableSet_le measurable_const (Prop16Area.Meas.measurable_M (γ := γ)
      (measurable_locModel γ L r) (isBumpFamily_bumpHD r) q))

/-- The event (in parameter space) that the local area measure is a genuine vague limit. -/
abbrev goodN1 (γ L r : ℝ) : Set (N1Idx r) :=
  Prop16Area.Meas.goodSet γ (locModel γ L r) (fun _ => halfDisc r)

theorem scaleSur_eq {γ L r : ℝ} {p : N1Idx r} (hp : p ∈ goodN1 γ L r) :
    scaleSur γ L r p = scaleParamOn γ (locModel γ L r p) (halfDisc r) := by
  have hM : ∀ q : ℝ, Prop16Area.Meas.M γ (locModel γ L r) (bumpHD r) p q =
      qAreaMeasureOn γ (locModel γ L r p) (halfDisc r) (Metric.ball 0 q ∩ H) := fun q =>
    (Prop16Area.Meas.measure_eq_M (isBumpFamily_bumpHD r) hp q).symm
  have hmono : Monotone fun a : ℝ =>
      qAreaMeasureOn γ (locModel γ L r p) (halfDisc r) (Metric.ball 0 a ∩ H) := fun a b h =>
    measure_mono (inter_subset_inter_left _ (Metric.ball_subset_ball h))
  simp only [scaleSur, scaleParamOn, hM]
  exact sInf_rat_eq hmono

theorem mem_goodN1_of_pos {γ L r : ℝ} {p : N1Idx r}
    (h : 0 < scaleParamOn γ (locModel γ L r p) (halfDisc r)) : p ∈ goodN1 γ L r := by
  by_contra hp
  rw [Prop16Area.Meas.scaleParamOn_of_not hp] at h
  exact lt_irrefl _ h

/-- The rescaled local model: the candidate for the local canonical field. -/
def zoomN1 (γ L r : ℝ) (p : N1Idx r) : FieldSample :=
  rescale (locModel γ L r p) (Qc γ) (scaleSur γ L r p)

/-- **The factorization map for D25's rich local data.** -/
def TmRichN1 (γ r : ℝ) (R : ℕ) (L : ℝ) (p : N1Idx r) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  locFieldFull R (zoomN1 γ L r p)

theorem measurable_zoomN1_apply (γ L r : ℝ) (ν : Measure ℂ) [SFinite ν] :
    Measurable fun p => zoomN1 γ L r p ν := by
  have h1 : Measurable fun p : N1Idx r => (locModel γ L r p, scaleSur γ L r p) :=
    (measurable_locModel γ L r).prodMk (measurable_scaleSur γ L r)
  exact Measurable.comp (g := fun q : FieldSample × ℝ => rescale q.1 (Qc γ) q.2 ν)
    (f := fun p : N1Idx r => (locModel γ L r p, scaleSur γ L r p))
    (Prop16Area.measurable_rescale_apply_joint (Qc γ) ν) h1

theorem measurable_TmRichN1 (γ r : ℝ) (R : ℕ) (L : ℝ) : Measurable (TmRichN1 γ r R L) := by
  classical
  unfold TmRichN1 locFieldFull
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun ρ => ?_)
  · split_ifs
    · simp only [CoordsFull.coordsFull]
      exact measurable_zoomN1_apply γ L r _
    · exact measurable_const
  · split_ifs
    · simp only [pairRaw]
      exact (measurable_zoomN1_apply γ L r _).sub (measurable_zoomN1_apply γ L r _)
    · exact measurable_const

end D3Plus
end QuantumZipper
