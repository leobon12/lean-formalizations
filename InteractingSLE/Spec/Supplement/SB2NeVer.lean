/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeStop

/-!
# F2b′'s versions from the stop inputs

Packet PROVE-AUX61-NOJUMP (round 22, components C–D assembled). For F2b′'s stop inputs `T : Nd.StopIn` on the tail
line family (`𝓖 t = Nd.lineSigmaT t`), the joint line sets `A₁`, `A₂` of `Nd.SB2LowerStageVersionStatement5`, and a
word `β` equal almost surely to the stop word:

* `ver m` (`Na.StageVersionG`): the driver frozen at the `m`-th stop, the clock in B's time, the stop as horizon
  (SB2(1)'s `Vs.SB2StopData.ver`, the hull field `Nd.StopIn.hull_of_mem`);
* `versionS` (`Na.StageVersionS`);
* `cover_of`, `le_thr_of` (clauses (i), (ii) of the statement).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nd

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv Vr

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

namespace StopIn

variable (T : StopIn P κ b jumps E u l k ℓ (-(Real.pi / 2)))
  (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
  (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
  (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
  (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
  (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
  {𝓖 : Filtration ℝ≥0 mΩ} (h𝓖 : ∀ t, 𝓖 t = lineSigmaT κ b jumps E u l k ℓ t)
  {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
  (hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω ∧
    A₂ t ω = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 1) ω) ω)
  {β : Ω → BoundaryWord} (hβ : ∀ᵐ ω ∂P, T.cw ω = β ω) (types : Set WordType)

/-- The cells of two words agree at a sample where the words agree. -/
theorem cellXL_congr {β' : Ω → BoundaryWord} {w : WordType} {ω : Ω} (h : T.cw ω = β' ω) :
    cellXL κ (-(Real.pi / 2)) T.cw w ω = cellXL κ (-(Real.pi / 2)) β' w ω := by
  simp only [cellXL, h]

theorem cellXR_congr {β' : Ω → BoundaryWord} {w : WordType} {ω : Ω} (h : T.cw ω = β' ω) :
    cellXR κ (-(Real.pi / 2)) T.cw w ω = cellXR κ (-(Real.pi / 2)) β' w ω := by
  simp only [cellXR, h]

include hβ in
/-- **The stop is at most the threshold on the statement word's cells.** -/
theorem ae_V_le_thr (m : ℕ) (w : WordType) : ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ (-(Real.pi / 2)) β T.S.F w →
    T.V m ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (T.W m) (cellXL κ (-(Real.pi / 2)) β w)
      (cellXR κ (-(Real.pi / 2)) β w) ω := by
  filter_upwards [T.ae_mem_Gs, hβ] with ω hG hβω hc
  have hw : angleWordType κ (-(Real.pi / 2)) (T.cw ω) = w := by rw [hβω]; exact hc.2
  rw [← thr_congr _ _ _ (T.cellXL_congr hβω) (T.cellXR_congr hβω)]
  exact T.V_le_thr_of_mem (hG hc.1) hw

include hE hER hlθ hℓ hwℓ h𝓖 hA hβ in
/-- **The `m`-th version**: the driver frozen at the `m`-th stop, the clock in B's time, the stop as horizon. -/
def ver (m : ℕ) : Na.StageVersionG κ (-(Real.pi / 2)) P T.S.F 𝓖 A₁ A₂
    (fun ω => Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)) β types (bPc κ b jumps E ℓ) (fun _ => 0)
    (bLife b jumps E ℓ) where
  𝓗 := Tc.tcFilt (lineFiltC P 𝓖) T.S.a (T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖)
  W := T.W m
  a := T.S.a
  Λ := fun _ => T.V m
  marks_le := Tc.le_tcFilt_zero fun t => (lineFiltC P 𝓖).mono (zero_le : (0 : ℝ≥0) ≤ t)
  W_zero := T.W_zero m
  W_cont := T.continuous_W m
  W_adapted := T.stronglyAdapted_W hE hER hlθ hℓ hwℓ h𝓖 m
  clock_cont := T.S.continuous_a
  clock_mono := T.S.monotone_a
  clock_zero := T.S.a_zero
  clock_meas := T.measurable_a_lineFilt hE hER hlθ hℓ hwℓ h𝓖
  timeChange := fun q D' hD' t => Tc.tcFilt_inter q D' hD' t
  reach := fun _ _ q => by
    filter_upwards [T.ae_mem_Gs] with ω hG hc hq using T.reach_of_mem (hG hc.1.1) hq
  reg := fun w _ => by
    filter_upwards [T.ae_V_le_thr hβ m w] with ω hle hc using isForceReg_mono
      (Vh.reg_of_continuous (T.W_zero m) (T.continuous_W m) _ _ _ _ ω) (hle hc.1)
  safeS := fun _ _ _ t => T.measurableSet_safe_stop hE hER hlθ hℓ hwℓ h𝓖 m (isClosed_tsupport _) t
  safeL := fun _ _ Fb t => T.measurableSet_safe_stop hE hER hlθ hℓ hwℓ h𝓖 m
    (Set.Finite.isClosed_biUnion Fb.finite_toSet fun _ _ => isClosed_closedBall) t
  hull := fun _ _ t => by
    filter_upwards [T.ae_mem_Gs, hA t] with ω hG hAω hc hlt using T.hull_of_mem (hG hc.1.1) hlt hAω.1 hAω.2
  trace := fun _ _ t => by
    filter_upwards [T.ae_mem_Gs] with ω hG hc hlt using T.trace_of_mem (hG hc.1.1) hlt
  alive := fun _ _ t => by
    filter_upwards [T.ae_mem_Gs] with ω hG hc hlt using T.lt_life_of_lt (hG hc.1.1) hlt
  Λ_le := fun w _ => by
    filter_upwards [T.ae_V_le_thr hβ m w] with ω hle hc using hle hc.1

include hE hER hlθ hℓ hwℓ h𝓖 hA hβ in
/-- **F2b′'s versions at announced stops.** -/
def versionS : Na.StageVersionS κ (-(Real.pi / 2)) P T.S.F 𝓖 A₁ A₂
    (fun ω => Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)) β types (bPc κ b jumps E ℓ) (fun _ => 0)
    (bLife b jumps E ℓ) (fun ω => capLife (T.S.ρM ω)) where
  ver := T.ver hE hER hlθ hℓ hwℓ h𝓖 hA hβ types
  V := T.V
  record := T.record
  record_meas := T.measurable_record_line.mono (T.lineC0_le_lineFilt hE hER hℓ hwℓ h𝓖 0) le_rfl
  ρ := stopRule
  ρs := annRules gaugeRead
  ρ_meas := measurable_stopRule
  ρ_rule := isPathRule_stopRule
  ρs_meas := measurable_annRules measurable_gaugeRead
  ρs_rule := isPathRule_annRules isCausal_gaugeRead
  ρs_fin := annRules_ne_top gaugeRead
  ρs_mono := monotone_annRules gaugeRead
  Λ_eq := fun _ _ => rfl
  V_eq := fun _ _ => rfl
  ann := fun _ => by
    filter_upwards [T.ae_mem_Gs] with ω hG hF using T.ann_of_mem (hG hF)
  V_lt := fun m => by
    filter_upwards [T.ae_mem_Gs] with ω hG hF
    rw [T.V_eq (hG hF)]
    exact T.Vstop_lt (hG hF)
  V_mono := T.V_mono
  V_sup := by
    filter_upwards [T.ae_mem_Gs] with ω hG hF using T.V_sup (hG hF)
  W_eq := fun m m' hmm' => by
    filter_upwards [T.ae_mem_Gs] with ω hG hF t ht using T.W_eq hmm' (hG hF) ht

/-- **Clause (i): every B-time before B's lifetime is before some stop.** -/
theorem ae_cover (t : ℝ≥0) : ∀ᵐ ω ∂P, ω ∈ T.S.F → (t : ℝ≥0∞) < bLife b jumps E ℓ ω → ∃ m, T.S.a t ω < T.V m ω := by
  filter_upwards [T.ae_mem_Gs] with ω hG hF ht
  have h1 := T.a_lt_capLife_of_lt (T.Gs_subset_Eg (hG hF)) ht
  rw [← T.V_sup (hG hF)] at h1
  exact lt_iSup_iff.1 h1

end StopIn

end InteractingSLE.Theorem14.SB.Nd
