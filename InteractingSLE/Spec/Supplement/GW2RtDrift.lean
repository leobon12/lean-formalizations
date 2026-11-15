/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdzPair
import InteractingSLE.Spec.Supplement.GW2RwDrift

/-!
# J32 with a fixed drift family: the minimal successor for the shell's drift clause (decision D30)

PROVE-GW2-ROOTX round 7. J32's drift constant is not a parameter. It is the field `driftBound := sourceDriftBound c r`
of every experiment (`RootJ32.experiment`), and round 5 showed that the shell's clause against it is false. Every
generic consumer reads that field: `RetainedSlowComparisons(Lossy)Statement`, the cut slow comparison, and the C24
assembly through `RestartWindow κ C J`. SDE's `VPairInputsXCS` hard-codes `sourceDriftBound` in `shell`. The geometry,
the near binder and the SDE half do not read it, and the top `GW2Sdy.theorem14Statement_scaled_A_lossyS` is generic
in the construction family. So the minimal successor replaces the field and nothing else. The consumers that follow
are exactly these:

* `DriftFamily`, **`withDrift D C`**: the family with `driftBound := C Ω c r`; `withScaledCover_withDrift` (by `rfl`);
* the carry-overs: `ExperimentGeometryA.withDrift`, **`rootGeometryAStatement_withDrift`**, `nearLossy_withDrift`
  (by definitional equality), `stoppedSDEN_withDrift`;
* **`VPairInputsXCSD V lam gap C`**: `GW2Sdz.VPairInputsXCS` with the shell's drift clause against `C`;
* **`retainedComparisonsLossyXCSD_vpkg`**: both lossy binders for `withDrift (J32S gap) C`, using SDE's
  `ae_slowBufferCut_on`, which is generic in the drift constant;
* **`theorem14Statement_J32D_scaled_vpkgXCS`**: Theorem 1.4 from `VPairInputsXCSD`, for any drift family `C`.

Any valid `C` satisfies `C ≥ 8M/3 + (4/3)(4 − κ)` (`GW2Rw.le_stageDriftBound_schedWordMapX`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rt

open ZhanGT4.UpMark GW2JDetR11 GW2Sde GW2Sdf GW2Sdg GW2Sdh GW2Sdi GW2Sdx GW2Sdy GW2Sdz GW2TipSystem
  GW2TipSystem.RootC24 GW2TipSystem.RootL6 GW2TipSystem.RootN4 GW2TipSystem.RootV7 Sec5

/-- **A deterministic drift constant for every source setup and root.** -/
abbrev DriftFamily : Type (u + 1) :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω), ScaledRootIdx c.Θ c.Q → ℝ

/-- **A construction family with its drift constants replaced** (DECISIONS-FABLE-2 §F1 item 3, decision D30): only the
field `driftBound` of every experiment changes. -/
def withDrift (D : ConstructionFamily.{u}) (C : DriftFamily.{u}) : ConstructionFamily.{u} :=
  fun Ω _ _ c => ⟨(D Ω c).G, fun r => { (D Ω c).experiment r with driftBound := C Ω c r }⟩

theorem withScaledCover_withDrift (D : ConstructionFamily.{u}) (C : DriftFamily.{u}) (gap : RootCv.GapFamily.{u}) :
    RootCv.withScaledCover (withDrift D C) gap = withDrift (RootCv.withScaledCover D gap) C := rfl

/-- **The D2 geometry does not read the drift constant.** -/
theorem _root_.InteractingSLE.Theorem14.GW2TipSystem.Gm.ExperimentGeometryA.withDrift {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {G : Set Ω}
    {e : Experiment c r} (h : Gm.ExperimentGeometryA c r G e) (C : ℝ) :
    Gm.ExperimentGeometryA c r G { e with driftBound := C } :=
  ⟨h.band_open, h.observation, h.regularity, h.reach_measurable, h.reach_identification, h.record_read,
    h.clock_spec⟩

theorem rootGeometryAStatement_withDrift {D : ConstructionFamily.{u}} (h : Gm.RootGeometryAStatement D)
    (C : DriftFamily.{u}) : Gm.RootGeometryAStatement (withDrift D C) :=
  fun Ω _ _ c r => (h Ω c r).withDrift (C Ω c r)

theorem nearLossy_withDrift {D : ConstructionFamily.{u}} (h : RetainedNearModelsLossyStatement D)
    (C : DriftFamily.{u}) : RetainedNearModelsLossyStatement (withDrift D C) := h

theorem stoppedSDEN_withDrift {D : ConstructionFamily.{u}} {C₀ : ComparisonFamily.{u}}
    {S : ℕ → ComparisonFamily.{u}} (h : RetainedStoppedSDEStatementN D C₀ S) (C : DriftFamily.{u}) :
    RetainedStoppedSDEStatementN (withDrift D C) C₀ S := ⟨h.near, h.slow⟩

/-! ### The successor pair on the scaled cover with a drift family -/

/-- **The successor of `GW2Sdz.VPairInputsXCS` with the shell's drift clause against a drift family `C`** (decision
D30): every field is `VPairInputsXCS`'s except `shell`, which asks `ShellFactLe κ (C Ω c r)`. -/
structure VPairInputsXCSD (V : ℕ → VPkgXFamily.{u}) (lam : NearDil.{u}) (gap : RootCv.GapFamily.{u})
    (C : DriftFamily.{u}) : Prop where
  lam_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0
  safe : ∀ k : ℕ, VPkgXSafe (V k)
  words : ∀ k : ℕ, VWordsX (J32S gap) (V k) lam
  nearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    VNearImgOn ((V k).at 0) lam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
      (((J32S gap Ω c).experiment r).data.alive ((J32S gap Ω c).G r) l)
  driverId : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a n : ℕ,
      VDriverIdN (V 0) Ω c r l a n
  stopExhausts : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      VStopExhaustsN (V 0) Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      ∀ᵐ ω ∂c.P, ω ∈ ((J32S gap Ω c).experiment r).data.alive ((J32S gap Ω c).G r) l →
        ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
          ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω

/-- **Both lossy binders for J32 on the scaled cover with the drift family `C`** (the successor of
`GW2Sdz.retainedComparisonsLossyXCS_vpkg`; Theorems 1.2–1.3, R48). -/
theorem retainedComparisonsLossyXCSD_vpkg (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (V : ℕ → VPkgXFamily.{u})
    (lam : NearDil.{u}) (gap : RootCv.GapFamily.{u}) (C : DriftFamily.{u}) (hV : VPairInputsXCSD V lam gap C) :
    RetainedNearModelsLossyStatement (withDrift (J32S gap) C) ∧
      RetainedSlowComparisonsLossyStatement (withDrift (J32S gap) C) := by
  have hsde : ∀ k, RetainedStoppedSDEStatementN (J32S gap)
      (comparisonFamilyN (((V k).at 0).frameN lam)) fun n => comparisonFamilyN (((V k).at n).frameN lam) :=
    fun k => retainedStoppedSDEStatementN_vpkgX h12p₀ h13₀ h13 (V k) lam hV.lam_ne (aliveOrdered_scaled gap)
      (hV.safe k) (hV.words k)
  have hnear : RetainedNearModelsLossyStatement (J32S gap) := by
    refine retainedNearModelsLossy_of_nearSDE (J32S gap)
      (fun k => comparisonFamilyN (((V k).at 0).frameN lam)) (fun k => (hsde k).near) ?_
    intro Ω _ _ c r l k
    filter_upwards [(hsde k).near Ω c r l,
      nearImgPathLossy_on ((V k).at 0) lam Ω c r l (hV.lam_ne Ω c r l) (hV.nearImg k Ω c r l)]
      with ω hs hi halive n
    filter_upwards [hs halive n, hi halive n] with m h1 h2
    exact nearBufferFactLossy_of_imgPath h1 (RootJ32.experiment_reach_measurable c r l _) h2
  refine ⟨nearLossy_withDrift hnear C, retainedSlowComparisonsLossy_of_stoppedSDE_cut (withDrift (J32S gap) C)
    (fun n => comparisonFamilyN (((V 0).at n).frameN lam)) ((stoppedSDEN_withDrift (hsde 0) C).slow) ?_⟩
  intro Ω _ _ c r k l hl a
  filter_upwards [ae_slowBufferCut_on h13 (V 0) lam Ω c r l a (fun ω h => alive_scaled_subset gap Ω c r l h)
    (fun hTO n => ((hV.safe 0).slowSafe n Ω c r k l hl hTO a).2.measurable_stop) (hV.driverId Ω c r k l hl a)
    (hV.stopExhausts Ω c r k l hl a) (C Ω c r) (hV.shell Ω c r k l hl a)] with ω h halive
  exact ⟨Eventually.of_forall (h halive).1, (h halive).2⟩

/-- **Theorem 1.4 with J32 on the scaled cover, drift family `C`, from the successor pair** (decision D30; the
successor of `GW2Sdz.theorem14Statement_J32_scaled_vpkgXCS`): only the shell's drift clause changes. -/
theorem theorem14Statement_J32D_scaled_vpkgXCS (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (C : DriftFamily.{u}) (V : ℕ → VPkgXFamily.{u}) (lam : NearDil.{u}) (hV : VPairInputsXCSD V lam gap C)
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  have h := retainedComparisonsLossyXCSD_vpkg
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0})
    Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} V lam gap C hV
  theorem14Statement_scaled_A_lossyS (withDrift RootJ32.constructionFamily C) gap hgap hpos
    (rootGeometryAStatement_withDrift
      (RootJ32.rootGeometryAStatement_withScaledCover Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} gap) C)
    h.1 h.2 hN hgeo hcond

end InteractingSLE.Theorem14.GW2Rt
