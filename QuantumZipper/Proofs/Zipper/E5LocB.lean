import QuantumZipper.Proofs.Zipper.E5LocA
import QuantumZipper.Proofs.LQG.WedgeCanonical
import QuantumZipper.Proofs.LQG.LocalRule
import QuantumZipper.Proofs.LQG.AreaExistenceAS
import QuantumZipper.Proofs.LQG.RegularSample

/-!
# E5-LOC2, part B: area limit of the collision field; random radius; good-event agreement

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4 E5, steps (1)–(2); Sheffield, arXiv:1012.4797,
§5.4 (pp. 66–72).

* (iii) `isVagueLimitOn_targetColl_addConst`: if `x` is a regular sample whose area
  approximations converge vaguely on `ℍ` and `k_{ϖ_t}` is continuous, then the (shifted)
  collision field `addConst (targetColl κ V t ϖ x) b` has a vague area limit on `ℍ`. Proof: on
  every folded circle it equals `x + ofFun φ` with `φ = s + K` (`s` the Palm shift function,
  continuous off `0`), and the local rule (5.1) (`LocalRule.isVagueLimitOn_add_ofFun`, with the
  open set `{0}ᶜ ⊇ ℍ`) applies. `ae_isVagueLimitOn_targetColl`: the a.s. version for a free
  field, simultaneously for all `(κ, V, t, ϖ, b)`.
* (ii) `exists_radius_bad_le`: for a random measure `ν` with `ν_ω(ball 0 r) = 0` for some
  `r > 0` a.s., there is a deterministic `r_ε > 0` with `Q(ν(ball 0 r_ε) ≠ 0) ≤ ε` (continuity
  of measure from above); `measurableSet_radiusBad`: the bad event is measurable for any
  σ-algebra for which `ω ↦ ν_ω(A)` is measurable (e.g. `σ(Ξ)` when `Ξ` carries the driver data).
  `setup_switch_of_harm_off`: switching `g` to a fallback `g₀` on that event gives a D3⁺ `Setup`
  when `g` is harmonic off the event and agrees off the event with a `condSigma`-measurable `gt`.
* `locG_canonConfig_eq_data_of_good`: on the good event, the rich local data of the collision
  configuration is the zoom-model data `(zLoc, drvWin (rescale …))`, given the driver identity
  (`DrvIdentStmt`, proved separately in `E5LocDrv.lean`).

Own elementary arguments (definitions, continuity of measure), assembling project lemmas; the
local rule is Sheffield (5.1) / Duplantier–Sheffield, *LQG and KPZ*, as formalized in
`LocalRule`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open D3Plus E1 B2

/-! ## (iii) Area limit of the collision field -/

/-- The additive constant of the (shifted) collision field. -/
def collConst (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ) (x : FieldSample) (b : ℝ) : ℝ :=
  -((ofFun (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0) + x) (varpiT V t ϖ)) -
    qt κ V t ϖ + b

theorem targetColl_addConst_apply_eq_add_ofFun (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ)
    (x : FieldSample) (b : ℝ) (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hs : Integrable (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0) μ) :
    addConst (Thm13Asm.targetColl κ V t ϖ x) b μ =
      (x + ofFun fun z => PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0 z +
        collConst κ V t ϖ x b) μ := by
  have hμ : (μ Set.univ).toReal = 1 := by simp
  simp only [Thm13Asm.targetColl, PalmNorm.normAt, addConst, Pi.add_apply, hμ, mul_one]
  simp only [ofFun]
  rw [integral_add hs (integrable_const _), integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul, collConst, ofFun, Pi.add_apply]
  ring

theorem integrable_shiftFun_foldedCircle (κ : ℝ) {ϖ' : Measure ℂ}
    (hk : Continuous (PalmNorm.kPot ϖ')) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) ϖ' 0) (foldedCircle c ρ) := by
  rw [TRegE4.shiftFun_zero_eq]
  exact ((CoordReg.integrable_log_norm_foldedCircle c ρ).const_mul _).add
    ((integrable_foldedCircle_of_continuousOn (r := ‖c‖ + ρ + 1) hk.continuousOn c ρ hρ
      (lt_add_one _)).const_mul _)

theorem continuousOn_shiftFun (κ : ℝ) {ϖ' : Measure ℂ} (hk : Continuous (PalmNorm.kPot ϖ'))
    (K : ℝ) :
    ContinuousOn (fun z => PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) ϖ' 0 z + K)
      ({0}ᶜ ∩ Hbar) := by
  rw [TRegE4.shiftFun_zero_eq]
  refine ContinuousOn.add (ContinuousOn.add ?_ ?_) continuousOn_const
  · exact continuousOn_const.mul (ContinuousOn.log continuous_norm.continuousOn
      fun v hv => norm_ne_zero_iff.2 hv.1)
  · exact continuousOn_const.mul hk.continuousOn

theorem fullIndex_radius_pos (i : ℕ) : 0 < (CoordsFull.fullIndex i).2 := by
  simp only [CoordsFull.fullIndex]
  positivity

/-- **(iii) The collision field has a vague area limit on `ℍ`** (deterministic form). -/
theorem isVagueLimitOn_targetColl_addConst {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x)
    {μ : Measure ℂ} (hμ : IsVagueLimitOn H (areaApprox γ x) μ) (κ : ℝ) (V : ℝ → ℝ) (t : ℝ)
    (ϖ : Measure ℂ) (hk : Continuous (PalmNorm.kPot (varpiT V t ϖ))) (b : ℝ) :
    ∃ μ', IsVagueLimitOn H (areaApprox γ (addConst (Thm13Asm.targetColl κ V t ϖ x) b)) μ' := by
  set φ : ℂ → ℝ := fun z => PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0 z +
    collConst κ V t ϖ x b with hφ
  have hc : CoordsFull.coordsFull (addConst (Thm13Asm.targetColl κ V t ϖ x) b) =
      CoordsFull.coordsFull (x + ofFun φ) := by
    funext i
    simp only [CoordsFull.coordsFull]
    exact targetColl_addConst_apply_eq_add_ofFun κ V t ϖ x b _
      (integrable_shiftFun_foldedCircle κ hk _ (fullIndex_radius_pos i))
  have ha : areaApprox γ (addConst (Thm13Asm.targetColl κ V t ϖ x) b) =
      areaApprox γ (x + ofFun φ) :=
    WedgeCan.areaApprox_congr_of_avgReg_Hbar fun k z _ => by
      rw [CoordsFull.avgReg_congr_full hc]
  have hH : H ⊆ ({0}ᶜ : Set ℂ) := fun z hz h0 => by
    have h' : (0 : ℝ) < z.im := hz
    rw [show z = 0 from h0, Complex.zero_im] at h'
    exact lt_irrefl _ h'
  rw [ha]
  exact ⟨_, LocalRule.isVagueLimitOn_add_ofFun hx isOpen_H subset_rfl hμ isOpen_compl_singleton
    hH (continuousOn_shiftFun κ hk _)⟩

/-- **(iii), almost surely**: for a free field `X`, a.s. for all `(κ, V, t, ϖ, b)` with
`k_{ϖ_t}` continuous, the shifted collision field of `X ω` has a vague area limit on `ℍ`. -/
theorem ae_isVagueLimitOn_targetColl {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ) (b : ℝ),
      Continuous (PalmNorm.kPot (varpiT V t ϖ)) →
      ∃ μ', IsVagueLimitOn H (areaApprox γ (addConst (Thm13Asm.targetColl κ V t ϖ (X ω)) b)) μ' := by
  filter_upwards [RegSample.ae_isRegularSample hX,
    AreaExist.ae_exists_isVagueLimitOn_areaApprox hX hγ hγ2] with ω h1 h2 κ V t ϖ b hk
  obtain ⟨μ, hμ⟩ := h2
  exact isVagueLimitOn_targetColl_addConst h1 hμ κ V t ϖ hk b

/-! ## (ii) The random radius and the switch -/

/-- The event that the random measure `ν` charges `ball 0 r`. -/
def radiusBad {Ω : Type*} (ν : Ω → Measure ℂ) (r : ℝ) : Set Ω := {ω | ν ω (ball (0 : ℂ) r) ≠ 0}

theorem measurableSet_radiusBad {Ω : Type*} {m : MeasurableSpace Ω} (ν : Ω → Measure ℂ)
    (hν : ∀ A : Set ℂ, MeasurableSet A → Measurable[m] fun ω => ν ω A) (r : ℝ) :
    MeasurableSet[m] (radiusBad ν r) :=
  (hν _ measurableSet_ball) (measurableSet_singleton (0 : ℝ≥0∞)).compl

theorem radiusBad_mono {Ω : Type*} (ν : Ω → Measure ℂ) {r r' : ℝ} (h : r ≤ r') :
    radiusBad ν r ⊆ radiusBad ν r' := fun _ω hω h0 =>
  hω (measure_mono_null (ball_subset_ball h) h0)

/-- **(ii) Choice of the deterministic radius `r_ε`.** -/
theorem exists_radius_bad_le {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsFiniteMeasure Q]
    (ν : Ω → Measure ℂ) (hν : ∀ A : Set ℂ, MeasurableSet A → Measurable fun ω => ν ω A)
    (hpos : ∀ᵐ ω ∂Q, ∃ r > 0, ν ω (ball (0 : ℂ) r) = 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r > 0, Q (radiusBad ν r) ≤ ε := by
  set A : ℕ → Set Ω := fun n => radiusBad ν (1 / ((n : ℝ) + 1)) with hA
  have hanti : Antitone A := fun n m hnm => radiusBad_mono ν
    (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1))
  have hnull : Q (⋂ n, A n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hpos)
    intro ⟨r, hr, h0⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
    exact (mem_iInter.1 hω n) (measure_mono_null (ball_subset_ball hn.le) h0)
  have ht := tendsto_measure_iInter_atTop (μ := Q)
    (fun n => (measurableSet_radiusBad ν hν _).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hnull] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, (le_of_lt hn)⟩

/-- **The switched correction satisfies the D3⁺ `Setup`**, when `g` is folded-harmonic off the
bad event and agrees there with a `condSigma`-measurable `gt`, the bad event is
`condSigma`-measurable, and the fallback `g₀` satisfies `Setup`. -/
theorem setup_switch_of_harm_off {Ω₁ E' : Type} [MeasurableSpace Ω₁] [MeasurableSpace E']
    {γ α r : ℝ} {ρ₀ : Measure ℂ} {Q : Measure Ω₁} {X' : Ω₁ → FieldSample} {Ξ : Ω₁ → E'}
    {g gt g₀ : Ω₁ → ℂ → ℝ} (hS₀ : D3Plus.Setup γ α r ρ₀ Q X' Ξ g₀) {bad : Set Ω₁}
    (hbad : MeasurableSet[condSigma Ξ X' r] bad)
    (hharm : ∀ ω ∉ bad,
      InnerProductSpace.HarmonicOnNhd (fun z => g ω (foldH z)) (ball (0 : ℂ) r))
    (hgt : ∀ ω ∉ bad, g ω = gt ω) (hgtm : ∀ z, Measurable[condSigma Ξ X' r] fun ω => gt ω z) :
    D3Plus.Setup γ α r ρ₀ Q X' Ξ (switchG bad g g₀) where
  hγ := hS₀.hγ
  hγ2 := hS₀.hγ2
  hα := hS₀.hα
  hr := hS₀.hr
  hX := hS₀.hX
  hΞ := hS₀.hΞ
  hind := hS₀.hind
  hρ := hS₀.hρ
  hρ1 := hS₀.hρ1
  hρB := hS₀.hρB
  harm ω := by
    by_cases h : ω ∈ bad
    · rw [switchG_of_mem h]; exact hS₀.harm ω
    · rw [switchG_of_not_mem h]; exact hharm ω h
  gmeas z := by
    classical
    have : (fun ω => switchG bad g g₀ ω z) =
        bad.piecewise (fun ω => g₀ ω z) (fun ω => gt ω z) := by
      funext ω
      by_cases h : ω ∈ bad
      · simp [switchG, h]
      · simp [switchG, h, hgt ω h]
    rw [this]
    exact Measurable.piecewise hbad (hS₀.gmeas z) (hgtm z)

/-! ## Agreement with the model data on the good event -/

/-- **The driver identity** (item (v), proved in `E5LocDrv.lean`): the time-windowed driver of
the canonicalized configuration `(y, d)` is the window `drvWin` of the germ `D` rescaled by `a`. -/
def DrvIdentStmt (κ : ℝ) (R : ℕ) (y : FieldSample) (d : ℝ → ℝ) (a : ℝ) (D : ℝ≥0 → ℝ) : Prop :=
  ∀ s : ℝ≥0, (canonConfig (Real.sqrt κ) (y, d)).2 (min (s : ℝ) R) =
    drvWin κ R (LengthMarkov.GermDensity.rescale (R : ℝ≥0) a.toNNReal D) s

/-- **E5-LOC on the good event**: the rich local data of the canonicalized collision
configuration is the zoom-model data (`ZoomModel.data` with `g = locCorr`). -/
theorem locG_canonConfig_eq_data_of_good (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ ρ₀ : Measure ℂ)
    (x : FieldSample) (C r : ℝ) (R : ℕ) (d : ℝ → ℝ) (D : ℝ≥0 → ℝ)
    (hk : ContinuousOn (PalmNorm.kPot (varpiT V t ϖ)) (ball (0 : ℂ) r))
    {μ : Measure ℂ} (hy : IsVagueLimitOn H (areaApprox (Real.sqrt κ)
      (addConst (Thm13Asm.targetColl κ V t ϖ x) (C / Real.sqrt κ))) μ)
    (hpos : 0 < zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C x
      (locCorr κ V t ϖ ρ₀ x))
    (hlt : zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C x
      (locCorr κ V t ϖ ρ₀ x) * ((R : ℝ) + 1) < r)
    (hdrv : DrvIdentStmt κ R (addConst (Thm13Asm.targetColl κ V t ϖ x) (C / Real.sqrt κ)) d
      (zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C x (locCorr κ V t ϖ ρ₀ x)) D) :
    locG locFieldFull R (canonConfig (Real.sqrt κ)
        (addConst (Thm13Asm.targetColl κ V t ϖ x) (C / Real.sqrt κ), d)) =
      (zLoc locFieldFull (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ R C x
          (locCorr κ V t ϖ ρ₀ x),
        drvWin κ R (LengthMarkov.GermDensity.rescale (R : ℝ≥0)
          (zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C x
            (locCorr κ V t ϖ ρ₀ x)).toNNReal D)) :=
  Prod.ext (locG_canonConfig_targetColl_eq_zLoc κ V t ϖ ρ₀ x C r R d hk hy hpos hlt).2
    (funext hdrv)

end E5
end QuantumZipper
