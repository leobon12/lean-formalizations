import Mathlib
import MatedCRTHarmonic.GMSLemma27.CellModel
import MatedCRTHarmonic.CellFamily.Interfaces

/-!
# Measurability of curve-image cells for the scaled-grid estimate

This module records the random-curve measurability input in a form compatible with the a.s.
continuity field of `GMSLemma27.CellModel`, and proves measurability of the two geometric
predicates used to define the scaled-grid estimate diameter event. It does not yet identify the
resulting curve-image cells with the graph-valued `RandomCellFamily` data; that adapter also has
to handle the a.e. graph/cell identification and the parameter-dependent walk law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace MatedCRTHarmonic.CellFamily

/-- The continuous-map representative of a possibly discontinuous curve. It agrees with the
original curve wherever that curve is continuous; on the exceptional set it is set to the zero
curve. -/
def continuousCurveView {Ω : Type*} (η : Ω → ℝ → ℂ) (ω : Ω) : C(ℝ, ℂ) :=
  by
    classical
    exact if h : Continuous (η ω) then ⟨η ω, h⟩ else 0

theorem continuousCurveView_apply {Ω : Type*} (η : Ω → ℝ → ℂ) (ω : Ω)
    (h : Continuous (η ω)) (t : ℝ) : continuousCurveView η ω t = η ω t := by
  simp [continuousCurveView, h]

/-- The random-curve measurability hypothesis used here: the continuous-map representative is a.e.
measurable. It agrees with the raw curve on the a.s. continuity event. -/
def AEMeasurableCurve {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (η : Ω → ℝ → ℂ) : Prop :=
  AEMeasurable (continuousCurveView η) μ

/-- The curve-image cell associated to a continuous-map representative. -/
def curveCell {Ω : Type*} (η : Ω → C(ℝ, ℂ)) (ε : ℝ) (ω : Ω) (x : ℤ) : Set ℂ :=
  η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)

/-- The same interval image formed from a curve that is not assumed continuous everywhere. -/
def rawCurveCell {Ω : Type*} (η : Ω → ℝ → ℂ) (ε : ℝ) (ω : Ω) (x : ℤ) : Set ℂ :=
  η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)

private def curveCellDiameterSup (a b : ℝ) (η : C(ℝ, ℂ)) : ℝ :=
  sSup ((fun p : ℝ × ℝ => dist (η p.1) (η p.2)) '' (Icc a b ×ˢ Icc a b))

private theorem curveCellDiameterSup_eq_diam {a b : ℝ} (hab : a ≤ b)
    (η : C(ℝ, ℂ)) :
    curveCellDiameterSup a b η = Metric.diam (η '' Icc a b) := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc a b
  let d : ℝ × ℝ → ℝ := fun p => dist (η p.1) (η p.2)
  have hK : K.Nonempty := ⟨(a, a), ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hab⟩⟩⟩
  have hbd : BddAbove (d '' K) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.image η.continuous).isBounded.exists_norm_le
    refine ⟨2 * C, ?_⟩
    rintro r ⟨p, hp, rfl⟩
    rcases hp with ⟨hp1, hp2⟩
    have h1 : ‖η p.1‖ ≤ C := hC _ ⟨p.1, hp1, rfl⟩
    have h2 : ‖η p.2‖ ≤ C := hC _ ⟨p.2, hp2, rfl⟩
    calc dist (η p.1) (η p.2) ≤ ‖η p.1‖ + ‖η p.2‖ := by
          rw [dist_eq_norm]
          exact norm_sub_le _ _
      _ ≤ 2 * C := by linarith
  have hnonempty : (η '' Icc a b).Nonempty := (nonempty_Icc.mpr hab).image η
  have hsNonempty : (d '' K).Nonempty := hK.image d
  have hsup_nonneg : 0 ≤ sSup (d '' K) := by
    apply le_csSup hbd
    exact ⟨(a, a), ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hab⟩⟩, by simp [d]⟩
  apply le_antisymm
  · apply csSup_le hsNonempty
    rintro r ⟨p, hp, rfl⟩
    rcases hp with ⟨hp1, hp2⟩
    exact Metric.dist_le_diam_of_mem (isCompact_Icc.image η.continuous).isBounded
      ⟨p.1, hp1, rfl⟩ ⟨p.2, hp2, rfl⟩
  · apply Metric.diam_le_of_forall_dist_le (s := η '' Icc a b) hsup_nonneg
    rintro u ⟨t, ht, rfl⟩ v ⟨s, hs, rfl⟩
    apply le_csSup hbd
    exact ⟨(t, s), ⟨ht, hs⟩, rfl⟩

private theorem continuous_curveCellDiameterSup (a b : ℝ) :
    Continuous (fun η : C(ℝ, ℂ) => curveCellDiameterSup a b η) := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc a b
  have hI : IsCompact (Icc a b) := isCompact_Icc
  have hK : IsCompact K := hI.prod hI
  have heval : Continuous (fun p : C(ℝ, ℂ) × (ℝ × ℝ) => p.1 p.2.1) := by
    exact continuous_eval.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have heval₂ : Continuous (fun p : C(ℝ, ℂ) × (ℝ × ℝ) => p.1 p.2.2) := by
    exact continuous_eval.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have hd : Continuous (fun p : C(ℝ, ℂ) × (ℝ × ℝ) =>
      dist (p.1 p.2.1) (p.1 p.2.2)) :=
    continuous_dist.comp (heval.prodMk heval₂)
  simpa [curveCellDiameterSup, K] using hK.continuous_sSup hd

/-- Diameter of a curve-image cell is a continuous, hence measurable, functional of the random
continuous curve in the compact-open topology. -/
theorem measurable_curveCell_diam {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → C(ℝ, ℂ)) (hη : Measurable η) {ε : ℝ} (hε : 0 ≤ ε) (x : ℤ) :
    Measurable (fun ω => Metric.diam (curveCell η ε ω x)) := by
  let a := ε * ((x : ℝ) - 1)
  let b := ε * x
  have hab : a ≤ b := by
    have hx : ((x : ℝ) - 1) ≤ x := by linarith
    dsimp [a, b]
    exact mul_le_mul_of_nonneg_left hx hε
  have hcont := continuous_curveCellDiameterSup a b
  have hEq : (fun ω => Metric.diam (curveCell η ε ω x)) =
      (fun ω => curveCellDiameterSup a b (η ω)) := by
    funext ω
    exact (curveCellDiameterSup_eq_diam hab (η ω)).symm
  rw [hEq]
  exact hcont.measurable.comp hη

private def curveCellMinNorm (a b : ℝ) (η : C(ℝ, ℂ)) : ℝ :=
  sInf ((fun t : ℝ => ‖η t‖) '' Icc a b)

private theorem curveCell_meets_closedBall_iff_minNorm_le {a b ρ : ℝ}
    (hab : a ≤ b) (η : C(ℝ, ℂ)) :
    ((η '' Icc a b) ∩ closedBall (0 : ℂ) ρ).Nonempty ↔
      curveCellMinNorm a b η ≤ ρ := by
  let K : Set ℝ := Icc a b
  let n : ℝ → ℝ := fun t => ‖η t‖
  let R : Set ℝ := n '' K
  have hK : K.Nonempty := ⟨a, ⟨le_rfl, hab⟩⟩
  have hR : R.Nonempty := hK.image n
  have hbdd : BddBelow R := ⟨0, by
    rintro y ⟨t, ht, rfl⟩
    exact norm_nonneg _⟩
  have hcompact : IsCompact R := by
    exact isCompact_Icc.image (continuous_norm.comp η.continuous)
  change IsCompact (n '' K) at hcompact
  constructor
  · rintro ⟨z, ⟨t, ht, rfl⟩, hz⟩
    have htNorm : ‖η t‖ ≤ ρ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    exact csInf_le hbdd ⟨t, ht, rfl⟩ |>.trans htNorm
  · intro hmin
    have hminMem : curveCellMinNorm a b η ∈ R := by
      exact hcompact.sInf_mem hR
    rcases hminMem with ⟨t, ht, hEq⟩
    refine ⟨η t, ⟨t, ht, rfl⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa [curveCellMinNorm, n, R, hEq] using hmin

private theorem continuous_curveCellMinNorm (a b : ℝ) :
    Continuous (fun η : C(ℝ, ℂ) => curveCellMinNorm a b η) := by
  have hI : IsCompact (Icc a b) := isCompact_Icc
  have heval : Continuous (fun p : C(ℝ, ℂ) × ℝ => p.1 p.2) :=
    continuous_eval
  have hn : Continuous (fun p : C(ℝ, ℂ) × ℝ => ‖p.1 p.2‖) :=
    continuous_norm.comp heval
  simpa [curveCellMinNorm] using hI.continuous_sInf hn

/-- A continuous curve's cell meets a fixed closed ball on a measurable event. Compactness of
the time interval makes the infimum norm attained, so the existential hit predicate is a closed
sublevel set of a continuous minimum functional. -/
theorem measurable_curveCell_meets_closedBall {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → C(ℝ, ℂ)) (hη : Measurable η) {ε : ℝ} (hε : 0 ≤ ε)
    (x : ℤ) (ρ : ℝ) :
    MeasurableSet {ω | (curveCell η ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty} := by
  let a := ε * ((x : ℝ) - 1)
  let b := ε * x
  have hab : a ≤ b := by
    have hx : ((x : ℝ) - 1) ≤ x := by linarith
    dsimp [a, b]
    exact mul_le_mul_of_nonneg_left hx hε
  have hcont := continuous_curveCellMinNorm a b
  have hmeas : Measurable (fun ω => curveCellMinNorm a b (η ω)) :=
    hcont.measurable.comp hη
  have hEq : {ω | (curveCell η ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty} =
      {ω | curveCellMinNorm a b (η ω) ≤ ρ} := by
    ext ω
    exact curveCell_meets_closedBall_iff_minNorm_le hab (η ω)
  rw [hEq]
  exact measurableSet_le hmeas measurable_const

/-- The cell-diameter event of the scaled-grid estimate for a measurable random continuous curve. -/
def curveDiameterGood {Ω : Type*} (η : Ω → C(ℝ, ℂ)) (ε q ρ : ℝ) : Set Ω :=
  {ω | ∀ x : ℤ,
    ((curveCell η ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty →
      Metric.diam (curveCell η ε ω x) ≤ ε ^ q)}

/-- The curve-generated diameter-good event is measurable for every nonnegative mesh. -/
theorem measurable_curveDiameterGood {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → C(ℝ, ℂ)) (hη : Measurable η) {ε : ℝ} (hε : 0 ≤ ε)
    (q ρ : ℝ) : MeasurableSet (curveDiameterGood η ε q ρ) := by
  classical
  unfold curveDiameterGood
  rw [show {ω : Ω | ∀ x : ℤ,
      (curveCell η ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty →
        Metric.diam (curveCell η ε ω x) ≤ ε ^ q} =
      ⋂ x : ℤ, {ω : Ω |
        (curveCell η ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty →
          Metric.diam (curveCell η ε ω x) ≤ ε ^ q} by
        ext ω
        simp]
  apply MeasurableSet.iInter
  intro x
  have hhit := measurable_curveCell_meets_closedBall η hη hε x ρ
  have hdiam := measurable_curveCell_diam η hη hε x
  rw [show {ω : Ω | (curveCell η ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty →
        Metric.diam (curveCell η ε ω x) ≤ ε ^ q} =
      {ω | ω ∉ {ω | (curveCell η ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty} ∨
      Metric.diam (curveCell η ε ω x) ≤ ε ^ q} by
        ext ω
        simp [imp_iff_not_or]]
  exact hhit.compl.union (measurableSet_le hdiam measurable_const)

/-- Measurability of the cell-diameter events `DiameterGood` when the random-cell embedding is the curve-image
embedding at each mesh (the scaled-grid estimate chain needs no event measurability, so this is used only by the
good-to-bad adapter `lemma27CellDiamBad_of_good_curveCells`). -/
theorem measurable_diameterGood_of_curveCells (F : RandomCellFamily)
    (η : F.Ω → C(ℝ, ℂ)) (hη : Measurable η) (q ρ : ℝ)
    (hmesh : ∀ k, 0 ≤ mesh k)
    (hcell : ∀ k ω x, (F.H k ω).cell x = curveCell η (mesh k) ω x) :
    ∀ k, MeasurableSet (DiameterGood F k q ρ) := by
  intro k
  have hm := measurable_curveDiameterGood η hη (hmesh k) q ρ
  have hEq : DiameterGood F k q ρ = curveDiameterGood η (mesh k) q ρ := by
    ext ω
    change (∀ x : ℤ,
      ((F.H k ω).cell x ∩ closedBall (0 : ℂ) ρ).Nonempty →
        Metric.diam ((F.H k ω).cell x) ≤ mesh k ^ q) ↔
      (∀ x : ℤ,
        (curveCell η (mesh k) ω x ∩ closedBall (0 : ℂ) ρ).Nonempty →
          Metric.diam (curveCell η (mesh k) ω x) ≤ mesh k ^ q)
    constructor
    · intro h x
      simpa only [hcell k ω x] using h x
    · intro h x
      simpa only [hcell k ω x] using h x
  rw [hEq]
  exact hm

/-- The original curve-image diameter event has a measurable version under the natural random
continuous-curve hypothesis and a.s. continuity. This is the form available from `CellModel`'s
current fields: the raw event need not itself be measurable off the continuity event. -/
theorem exists_measurable_version_rawCurveDiameterGood {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (η : Ω → ℝ → ℂ) (hη : AEMeasurableCurve μ η)
    (hcont : ∀ᵐ ω ∂μ, Continuous (η ω)) {ε : ℝ} (hε : 0 ≤ ε) (q ρ : ℝ) :
    ∃ S : Set Ω, MeasurableSet S ∧
      {ω | ∀ x : ℤ,
        ((rawCurveCell η ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty →
          Metric.diam (rawCurveCell η ε ω x) ≤ ε ^ q)} =ᵐ[μ] S := by
  let ηm : Ω → C(ℝ, ℂ) := AEMeasurable.mk (continuousCurveView η) hη
  have hηm : Measurable ηm := hη.measurable_mk
  let S : Set Ω := curveDiameterGood ηm ε q ρ
  have hS : MeasurableSet S := measurable_curveDiameterGood ηm hηm hε q ρ
  have heq :
      {ω | ∀ x : ℤ,
        ((rawCurveCell η ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty →
          Metric.diam (rawCurveCell η ε ω x) ≤ ε ^ q)} =ᵐ[μ] S := by
    filter_upwards [hη.ae_eq_mk, hcont] with ω hω hωcont
    have hfun : ηm ω = η ω := by
      funext t
      calc
        ηm ω t = continuousCurveView η ω t := by
          change (AEMeasurable.mk (continuousCurveView η) hη ω) t = _
          rw [hω]
        _ = η ω t := continuousCurveView_apply η ω hωcont t
    simp [S, curveDiameterGood, curveCell, rawCurveCell, hfun]
  exact ⟨S, hS, heq⟩

/-- The raw curve-cell hit event also has a measurable version under a.s. continuity. -/
theorem exists_measurable_version_rawCurveCell_meets_closedBall {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (η : Ω → ℝ → ℂ)
    (hη : AEMeasurableCurve μ η) (hcont : ∀ᵐ ω ∂μ, Continuous (η ω))
    {ε : ℝ} (hε : 0 ≤ ε) (x : ℤ) (ρ : ℝ) :
    ∃ S : Set Ω, MeasurableSet S ∧
      {ω | (rawCurveCell η ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty} =ᵐ[μ] S := by
  let ηm : Ω → C(ℝ, ℂ) := AEMeasurable.mk (continuousCurveView η) hη
  have hηm : Measurable ηm := hη.measurable_mk
  let S : Set Ω := {ω | (curveCell ηm ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty}
  have hS : MeasurableSet S := measurable_curveCell_meets_closedBall ηm hηm hε x ρ
  have heq :
      {ω | (rawCurveCell η ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty} =ᵐ[μ] S := by
    filter_upwards [hη.ae_eq_mk, hcont] with ω hω hωcont
    have hfun : ηm ω = η ω := by
      funext t
      change (AEMeasurable.mk (continuousCurveView η) hη ω) t = _
      calc
        (AEMeasurable.mk (continuousCurveView η) hη ω) t =
            continuousCurveView η ω t := congrArg (fun f : C(ℝ, ℂ) => f t) hω.symm
        _ = η ω t := continuousCurveView_apply η ω hωcont t
    simp [S, curveCell, rawCurveCell, hfun]
  exact ⟨S, hS, heq⟩

end MatedCRTHarmonic.CellFamily
