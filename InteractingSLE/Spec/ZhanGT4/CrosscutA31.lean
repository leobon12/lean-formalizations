/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Measurable

/-!
# A.3.1: the first-swallow crosscut for `κ ≥ 8`, and A.3 for every `κ > 4`

Packet PROVE-ZHAN-A35. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.1
(`source/external/AstraIG1/ig1_followup_proofs.txt` L657–L671, ruling R38): "By reflection suppose `x < 0`. In the
three-force version of §A.2 put `x₁ = x, x₂ = 0, p₁ = x⁻, p₂ = ∞, p₃ = x⁺, C₁ = 2/(κ − 4), C₂ = 1 − C₁`. Since `κ ≥ 8`,
`C₁ ≤ 1/2`. The large curve's three finite charges at `x` amalgamate to `−κ/2 + 2 + (κ − 4)/2 = 0`. It is therefore
ordinary SLE stopped at `T_x`. Its outer boundary is the crosscut given by §A.2. … The outer boundary of the closure of
preterminal hulls equals the active-domain boundary at `T_x`: by the kernel theorem, any new open component at the
swallowing time is precisely a bounded complementary component of that closure."

## The input

`ThreeForceCrosscutEightStatement κ`: A.2's three-force crosscut assertion (§A.2 L519–L521, three-force version
L604–L607) in the A.3.1 configuration. The large curve starts at `x₂ = 0`; its charges `C₁(κ − 4) = 2` at `x⁻`,
`−κ/2` at `x`, `(κ − 4)/2` at `x⁺` amalgamate to `0` (`OuterBoundary.firstSwallow_eight_amalgamate`), and the mark at
`p₂ = ∞` has no driver drift; so it is the integrated evolution from `(0; x)` with the single weight `0` at `x`, and
"before its first force collision" is the strip life of `x`. A.2 asserts that the outer boundary in `ℍ` of the closure
of the union of its hulls over that strip life is a simple crosscut from `x₁ = x` to a point of `(x₂, p₂) = (0, ∞)`.

## Main results

* `ae_firstSwallowGood_neg_one_eight`: ordinary `SLE_κ`, `κ ≥ 8`, satisfies the first-swallow conclusion at `−1`
  (the zero-weight construction on the given Brownian motion is "ordinary SLE stopped at `T_x`"; the strip life of `−1`
  is `[0, T_{−1})`, `A34.isStripLife_iff_lt_of_realSwallowAt`; kernel identity
  `A34.frontier_compl_fwdHull_eq_outerBoundary`);
* `firstSwallowCrosscutStatement_of_eight`: `FirstSwallowCrosscutStatement κ` for `κ ≥ 8` from the input;
* **`firstSwallowCrosscutStatement_of_A2`**: `FirstSwallowCrosscutStatement κ` for every `κ` (the statement is about
  `κ > 4`) from A.2's two named forms, `A34.FourForceCrosscutG3LifeStatement` (`4 < κ < 8`) and
  `ThreeForceCrosscutEightStatement` (`κ ≥ 8`). No measurability input remains.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A35

open A34 QuantumZipper

/-- **A.2's three-force crosscut assertion in the A.3.1 configuration, over the strip life of the mark** (§A.2
L519–L521 and L604–L607, §A.3.1 L657–L667): for `κ ≥ 8`, `x < 0` and every integrated evolution from `(0; x)` with the
amalgamated weight `0` at `x` (charges `2, −κ/2, (κ − 4)/2` at `x⁻, x, x⁺`; no drift from the mark at `∞`), almost
surely the outer boundary in `ℍ` of the closure of the union of its hulls before the driver first meets the flow of `x`
is `γ((0, 1))` for a simple crosscut `γ` with `γ(0) = x` and `γ(1) > 0`. -/
def ThreeForceCrosscutEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x] ![] ![0] ![] P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = x ∧ 0 < (γ 1).re ∧
          outerBoundary (closure (⋃ (t : ℝ≥0) (_ : Strip.IsStripLife (W · ω) (VL 0 · ω) (ζ ω) t),
            fwdHull (fun s : ℝ => W s.toNNReal ω) t)) = γ '' Ioo 0 1

/-- **Ordinary `SLE_κ` at the point `−1`**, `κ ≥ 8`: on a filtered probability space carrying a Brownian motion with
continuous paths started at `0`, almost surely the first-swallow conclusion holds at `−1`, with the crosscut ending at
`−1`. -/
theorem ae_firstSwallowGood_neg_one_eight {κ : ℝ} (hκ8 : 8 ≤ κ) (hA2 : ThreeForceCrosscutEightStatement.{u} κ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) :
    ∀ᵐ ω ∂P, FirstSwallowGood κ (drive κ B ω) (-1) := by
  have hκ0 : 0 < κ := by linarith
  have hκ4 : 4 < κ := by linarith
  have hP : IsProbabilityMeasure P := hB.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hBm : ∀ t, Measurable (B t) := fun t => (hB.2.1 t).mono (𝓕.le t) le_rfl
  have hE := isStripSLEEvolution_ord hκ0 hB hBc hB0
  have hE' : IsIntegratedSLEEvolution κ ![-1] ![] ![0] ![] P 𝓕 (ordW κ B) (fun _ => ordV κ B)
      (fun i => i.elim0) B (fun _ => ⊤) := by
    have h := hE
    unfold Strip.IsStripSLEEvolution at h
    rwa [wordXL_nil, wordXR_nil, wordRhoL_nil] at h
  have hsepw : Strip.IsSeparatedStripWord (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) :=
    ⟨fun a => a.elim0, fun i => i.elim0, fun a => a.elim0, fun i => i.elim0⟩
  have hpre : Strip.HasStripPrefixSums κ (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) :=
    ⟨fun j => j.elim0, fun j => j.elim0⟩
  -- `−1` is swallowed
  have hsw : ∀ᵐ ω ∂P, ∃ σ, RealSwallowAt (drive κ B ω) (-1) σ := by
    have hnB : IsBrownianReal (-B) P := hB.1.neg
    filter_upwards [ae_exists_realSwallowAt hnB (fun t => (hBm t).neg) (fun ω => (hBc ω).neg)
      (fun ω => by simp [hB0 ω]) hκ4 one_pos] with ω ⟨σ, hσ⟩
    rw [drive_neg_eq, show (1 : ℝ) = -(-1) by norm_num] at hσ
    exact ⟨σ, realSwallowAt_neg_iff.1 hσ⟩
  filter_upwards [hA2 hκ8 (-1) (by norm_num) P 𝓕 _ _ _ B _ hE', hsw, ae_ordW_eq hκ0 hB hBc hB0, hE.2.2.2.2]
    with ω hγ ⟨σ, hσ⟩ hW hp
  obtain ⟨γ, hγc, hγ0, hγ1, hob⟩ := hγ
  set w : ℝ≥0 → ℝ := fun t => ordW κ B t ω with hw
  set v : ℝ≥0 → ℝ := fun t => ordV κ B t ω with hv
  have hdrive : Strip.extPath w = drive κ B ω := funext fun r => by simp [Strip.extPath, drive, hw, hW]
  have hwc : Continuous w := by
    have : w = fun t => Real.sqrt κ * B t ω := funext hW
    rw [this]; exact continuous_const.mul (hBc ω)
  have hw0 : w 0 = 0 := by simp [hw, hW, hB0]
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun t => ENNReal.coe_lt_top
  have hvc : Continuous v := by
    have h := hp.2.2.2.2.1 0
    rw [hset, continuousOn_univ] at h
    exact h
  have hle : ∀ t, v t ≤ w t := fun t => hp.2.2.2.2.2.2.2.1 t ENNReal.coe_lt_top 0
  have hveq : ∀ t : ℝ≥0, v t = -1 + ∫ r in (0 : ℝ)..t, 2 / (v r.toNNReal - w r.toNNReal) := fun t => by
    have h := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ENNReal.coe_lt_top 0
    rwa [show Strip.wordXL (![] : Fin 0 → ℝ) 0 = -1 from Strip.wordXL_last _] at h
  have hσ' : RealSwallowAt (Strip.extPath w) (-1) σ := by rw [hdrive]; exact hσ
  have hlife := isStripLife_iff_lt_of_realSwallowAt hwc hvc hw0 hveq hle hσ'
  have hdc : Continuous (drive κ B ω) := by rw [← hdrive]; exact hwc.comp continuous_real_toNNReal
  have hd0 : drive κ B ω 0 = 0 := by simp [drive, hB0]
  -- the union of the hulls over the strip life is the union before `σ`
  have hU : (⋃ (t : ℝ≥0) (_ : Strip.IsStripLife (fun t => ordW κ B t ω) (fun t => ordV κ B t ω) ⊤ t),
      fwdHull (fun s : ℝ => ordW κ B s.toNNReal ω) t) = hullBefore (drive κ B ω) σ := by
    have hf : (fun s : ℝ => ordW κ B s.toNNReal ω) = drive κ B ω := hdrive
    rw [hf]
    ext z
    simp only [mem_iUnion, hullBefore]
    constructor
    · rintro ⟨t, ht, hz⟩
      exact ⟨t, ⟨t.coe_nonneg, (hlife t).1 ht⟩, hz⟩
    · rintro ⟨t, ht, hz⟩
      refine ⟨t.toNNReal, (hlife _).2 (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2), ?_⟩
      rw [Real.coe_toNNReal _ ht.1]
      exact hz
  have hfr : frontier (H \ fwdHull (drive κ B ω) σ) ∩ H = γ '' Ioo 0 1 := by
    rw [frontier_compl_fwdHull_eq_outerBoundary hdc hd0 hσ.1, ← hU, hob]
  refine ⟨σ, hσ, γ, hγc, by rw [hγ0]; norm_num, hγ1, hfr,
    fun _ => ⟨fun _ => hγ0, fun h8 => absurd hκ8 (not_le.2 h8)⟩, fun h => absurd h (by norm_num)⟩

/-- **A.3.1** (`κ ≥ 8`): `FirstSwallowCrosscutStatement κ` from A.2's three-force version in the A.3.1 configuration. -/
theorem firstSwallowCrosscutStatement_of_eight {κ : ℝ} (hκ8 : 8 ≤ κ)
    (hA2 : ThreeForceCrosscutEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ := by
  refine firstSwallowCrosscutStatement_of_neg_one fun _ {Ω} _ P B hB => ?_
  obtain ⟨B'', hB''m, hB''c, hB''0, hB'', hae⟩ := RS.exists_good_version0 hB
  have hF := OneForce.isFilteredBrownianReal_natFilt hB'' hB''m
  filter_upwards [ae_firstSwallowGood_neg_one_eight hκ8 hA2 hF hB''c hB''0, hae] with ω hω hae
  have : drive κ B ω = drive κ B'' ω := funext fun t => by simp [drive, hae]
  rwa [this]

/-- **A.3 for every `κ > 4`** (§A.3.1–A.3.2): `FirstSwallowCrosscutStatement κ` from A.2's two named forms, the
four-force (G3) form over the strip life (used for `4 < κ < 8`) and the three-force form (used for `κ ≥ 8`). -/
theorem firstSwallowCrosscutStatement_of_A2 {κ : ℝ} (hA2 : FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ThreeForceCrosscutEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ := by
  rcases lt_or_ge κ 8 with h8 | h8
  · exact firstSwallowCrosscutStatement_of_life_meas h8 hA2
  · exact firstSwallowCrosscutStatement_of_eight h8 hA2'

/-- `FirstSwallowCrosscutStatement` for all parameters at once (the form consumed by `Wire.Thm13Inputs4`). -/
theorem forall_firstSwallowCrosscutStatement_of_A2 (hA2 : ∀ κ : ℝ, FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ThreeForceCrosscutEightStatement.{u} κ) : ∀ κ : ℝ, FirstSwallowCrosscutStatement.{u} κ :=
  fun κ => firstSwallowCrosscutStatement_of_A2 (hA2 κ) (hA2' κ)

end InteractingSLE.ZhanGT4.A35
