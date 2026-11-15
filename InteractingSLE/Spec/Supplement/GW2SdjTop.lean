/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmVAsm
import InteractingSLE.Spec.Supplement.GW2SdiInst
import InteractingSLE.Spec.Supplement.GW2SdiVar

/-!
# Theorem 1.4's top with the lossy near binder, for J32 (ruling R114)

Packet PROVE-GW2-SDE (round 7). R114 made GW2's near interface lossy. Round 6 showed that the exact C24 near binder
`RetainedNearModelsStatement` does not follow from the lossy fact, but that every consumer uses it only through
`RootN4.HasNearCrossingModels.modelCross`, which the lossy binder also gives
(`GW2Sdi.HasNearCrossingModelsLossy.modelCross`). This file switches the Theorem 1.4 top to the lossy binder. It
copies GEOM2's successor chain (`Gm.testClaims_of_nearModels_unitEvent_V`, `Gm.ExperimentGeometryV.exists_testClaims`,
`Gm.gw2RootTestStatement_of_oneSided_comparisons_V`, `…_of_cover_V`, `Gm.theorem14Statement_unscaled_V`), whose only
use of `hNear` is `hNear.modelCross`:

* **`testClaims_of_modelCross_unitEvent_V`**: the per-root claims from the model crossing clause itself;
* `ExperimentGeometryV.exists_testClaims_lossy`, `gw2RootTestStatement_of_oneSided_comparisons_V_lossy`,
  `gw2RootTestStatement_of_cover_V_lossy`;
* **`theorem14Statement_unscaled_V_lossy`**: the successor of `Wire.theorem14Statement_assembled6_covers_unscaled`
  (Theorems 1.2–1.3 from the proved fibre leaf, as GEOM2's top) with `RetainedNearModelsLossyStatement`;
* **`theorem14Statement_J32_lossy`**: the same with J32 as the construction (`RootJ32.withCover_constructionFamily`);
* **`theorem14Statement_J32_schedS`**, **`theorem14Statement_J32_vpkg`**: the J32 top with the near and slow
  binders produced by round 6's frozen pair theorems (`GW2Sdi.retainedComparisonsLossy_rootJ32B_schedS`,
  `GW2Sdi.retainedComparisonsLossy_vpkg`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u v

namespace InteractingSLE.Theorem14.GW2Sdj

open GW2TipSystem GW2TipSystem.Gm GW2Schedule Exist Staged StagedLaw Restart LQGMetric GW2TipSystem.RootC24
  GW2TipSystem.RootK3

section Claims

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The per-root claims from the model crossing clause** (`Gm.testClaims_of_nearModels_unitEvent_V`, whose only
use of `hNear` is `hNear.modelCross`). -/
theorem testClaims_of_modelCross_unitEvent_V {Ξ : Type v} [MeasurableSpace Ξ]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {G : Set Ω}
    (d : StageModelData Ω c.Θ c.Q Ξ (c.sigma r))
    (hModelCross : ∀ l (δ : ℝ≥0∞), 0 < δ → ∀ᵐ ω ∂c.P,
      ω ∈ d.alive G l → ∃ a, 1 - δ < d.kernel l a ω (d.reach l a))
    (hG : MeasurableSet[c.sigma r []] G)
    (hI : ∀ l a, IsOpen (d.I l a))
    (hObs : ∀ l a (q q' : c.Q), q ≤ q' → ∃ g : Ω → ℝ × ℂ,
      Measurable[c.sigma r ((d.ang a, q') :: l)] g ∧ d.observation l a q =ᵐ[c.P] g)
    (hReg : ∀ l a, ∀ᵐ ω ∂c.P, ω ∈ d.alive G l → d.S l a ω < d.F l a ω →
      0 ≤ d.S l a ω ∧ ContinuousAt (d.X l a ω) (d.S l a ω) ∧
      d.X l a ω (d.S l a ω) ∈ d.I l a ∧
      ContinuousOn (d.γ l a ω) (Ioo (d.S l a ω) (d.F l a ω)) ∧
      volume {t | t ∈ Ioo (d.S l a ω) (d.F l a ω) ∧ d.γ l a ω t ∉ H} = 0)
    (hSample : ∀ l a, Measurable (d.sample l a))
    (hReachMeas : ∀ l a, MeasurableSet (d.reach l a))
    (hSlowMeas : ∀ l a, MeasurableSet (d.slow l a))
    (hLaw : ∀ l a, ∀ᵐ ω ∂c.P, ω ∈ d.alive G l →
      (condExpKernel c.P (c.sigma r l) ω).map (d.sample l a) = d.kernel l a ω)
    (hReachIdent : ∀ l a, d.sample l a ⁻¹' d.reach l a =ᵐ[c.P]
      {ω | d.S l a ω < d.F l a ω})
    (hp₀ : 0 < d.p₀) (hp₀1 : d.p₀ ≤ 1)
    (hModelSlow : ∀ (k : ℕ) l, l.length = 2 * k + 4 → ∀ a,
      ∀ᵐ ω ∂c.P, ω ∈ d.alive G l →
        ENNReal.ofReal d.p₀ ≤ d.kernel l a ω (d.slow l a))
    (hUnit : ∀ l a, ∀ᵐ ω ∂c.P, ω ∈ d.alive G l →
      d.sample l a ω ∈ d.slow l a → ∀ q : c.Q, ω ∈ d.tests l a q →
        capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω + 1 ≤
          capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r ((d.ang a, q) :: l) ω) :
    ∃ (A : List (EntryIdx c.Θ c.Q) → Set Ω) (T : List (EntryIdx c.Θ c.Q) → ℕ → c.Q → Set Ω),
      TestClaims c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P r G A d.ang T
        (RootF27.unitEvent c r) d.p₀ := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hle : ∀ l, c.sigma r l ≤ mΩ := fun l => stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  choose g hgm hgeq using fun l a (q : c.Q) => hObs l a q q le_rfl
  set T' : List (EntryIdx c.Θ c.Q) → ℕ → c.Q → Set Ω :=
    fun l a q => g l a q ⁻¹' (d.I l a ×ˢ H) with hT'def
  have hT'm : ∀ l a (q q' : c.Q), q ≤ q' →
      MeasurableSet[c.sigma r ((d.ang a, q') :: l)] (T' l a q) := fun l a q q' hqq' =>
    RootH29.rootSigma_next_mono c r l (d.ang a) hqq' _
      (hgm l a q ((hI l a).measurableSet.prod QuantumZipper.isOpen_H.measurableSet))
  have hT'eq : ∀ l a q, T' l a q =ᵐ[c.P] d.tests l a q := by
    intro l a q
    rw [d.tests_eq_preimage_observation l a q]
    filter_upwards [hgeq l a q] with ω hω
    change (g l a q ω ∈ d.I l a ×ˢ H) = (d.observation l a q ω ∈ d.I l a ×ˢ H)
    rw [hω]
  have hpt : ∀ᵐ ω ∂c.P, ∀ l a q, ω ∈ T' l a q ↔ ω ∈ d.tests l a q := by
    rw [ae_all_iff]; intro l; rw [ae_all_iff]; intro a; rw [ae_all_iff]; intro q
    filter_upwards [hT'eq l a q] with ω hω
    exact Iff.of_eq hω
  have halive : ∀ᵐ ω ∂c.P, ∀ l, ω ∈ TestEvents.aliveTests G d.ang T' l ↔ ω ∈ d.alive G l := by
    filter_upwards [hpt] with ω hω
    exact mem_aliveTests_iff hω
  refine ⟨TestEvents.aliveTests G d.ang T', T', testClaims_unitEvent_V c r hG d.ang d.X d.γ d.S
    d.F d.I hI T' hT'm hT'eq ?_ ?_ (fun l a => d.sample l a ⁻¹' d.slow l a)
    (fun l a => hSample l a (hSlowMeas l a)) hp₀ hp₀1 ?_ ?_⟩
  · intro l a
    filter_upwards [hReg l a, halive] with ω hω hal hωA
    exact hω ((hal l).1 hωA)
  · intro l ε hε
    have heq := ae_all_iff.2 fun a =>
      ae_condExpKernel_event_eq_of_map (hle l) (hSample l a)
        (hReachMeas l a) (hLaw l a) (hReachIdent l a)
    filter_upwards [heq, hModelCross l ε hε, halive] with ω hωeq hωcross hal hωA
    have hωA' := (hal l).1 hωA
    obtain ⟨a, ha⟩ := hωcross hωA'
    exact ⟨a, (hωeq a hωA').symm ▸ ha⟩
  · intro k l hl a C hC hCA
    have hLaw' : ∀ᵐ ω ∂c.P, ω ∈ TestEvents.aliveTests G d.ang T' l →
        (condExpKernel c.P (c.sigma r l) ω).map (d.sample l a) = d.kernel l a ω := by
      filter_upwards [hLaw l a, halive] with ω h hal hωA
      exact h ((hal l).1 hωA)
    have hSlow' : ∀ᵐ ω ∂c.P, ω ∈ TestEvents.aliveTests G d.ang T' l →
        ENNReal.ofReal d.p₀ ≤ d.kernel l a ω (d.slow l a) := by
      filter_upwards [hModelSlow k l hl a, halive] with ω h hal hωA
      exact h ((hal l).1 hωA)
    exact le_measure_inter_preimage_of_map (hle l) (hSample l a)
      (hSlowMeas l a) hLaw' hSlow' hC hCA
  · intro l a
    filter_upwards [hUnit l a, halive, hpt] with ω h hal hpω hωA hE q hq
    exact h ((hal l).1 hωA) hE q ((hpω l a q).1 hq)

/-- **All per-root claims from the successor geometry and the LOSSY near models** (as
`Gm.ExperimentGeometryV.exists_testClaims`; Theorem 1.3). -/
theorem ExperimentGeometryV.exists_testClaims_lossy {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {G : Set Ω} {e : Experiment c r}
    (hg : ExperimentGeometryV c r G e) (h13 : Theorem13Statement.{u})
    (hG : MeasurableSet[c.sigma r []] G)
    (hNear : GW2Sdi.HasNearCrossingModelsLossy.{u} c.κ c.P (e.data.alive G)
      (fun l a ω => e.retained.kernel l a ω (e.data.reach l a)))
    (hSlow : RootS5.HasSlowComparisonModels.{u} c.κ e.driftBound
      (Icc (-Sec5.angleWeightBound c.κ) (Sec5.angleWeightBound c.κ)) c.P
      (e.data.alive G) List.length
      (fun l a ω => e.retained.kernel l a ω RootV7.slowSet)) :
    ∃ (p₀ : ℝ) (A : List (EntryIdx c.Θ c.Q) → Set Ω) (T : List (EntryIdx c.Θ c.Q) → ℕ → c.Q → Set Ω),
      TestClaims c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P r G A e.data.ang T
        (RootF27.unitEvent c r) p₀ := by
  have hJ2 : Icc (-Sec5.angleWeightBound c.κ) (Sec5.angleWeightBound c.κ) ⊆
      Ioi (-2) := by
    intro x hx
    exact (neg_lt_neg (Sec5.angleWeightBound_lt_two c.hκ)).trans_le hx.1
  obtain ⟨p₀, hp₀, hp₀1, hModelSlow⟩ := hSlow.exists_modelSlow c.hκ isCompact_Icc hJ2
  let d' : StageModelData Ω c.Θ c.Q RootV7.DriverRecord (c.sigma r) :=
    { e.retained with p₀ := p₀ }
  have hUnit := RootV7.ae_unit_of_record_clock (d := d') (fun _ _ => rfl)
    e.Y e.clock hg.record_read hg.clock_spec
  obtain ⟨A, T, hc⟩ := testClaims_of_modelCross_unitEvent_V (d := d') c r
    (hNear.modelCross h13 c.hκ c.hκ4) hG hg.band_open
    hg.observation hg.regularity e.sampleMeas hg.reach_measurable
    (fun _ _ => RootV7.measurableSet_slowSet)
    (fun _ _ => Eventually.of_forall fun _ _ => rfl)
    hg.reach_identification hp₀ hp₀1 hModelSlow hUnit
  exact ⟨p₀, A, T, hc⟩

end Claims

/-- **The complete root-test statement with the lossy near binder** (as
`Gm.gw2RootTestStatement_of_oneSided_comparisons_V`). -/
theorem gw2RootTestStatement_of_oneSided_comparisons_V_lossy
    (h13 : Theorem13Statement.{u}) (D : ConstructionFamily.{u})
    (hCover : RootCoverStatement D) (hGeometry : RootGeometryVStatement D)
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement D)
    (hSlow : RetainedSlowComparisonsStatement D) :
    GW2RootTestStatement.{u} := by
  intro κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ Ω _ _ P hP h hh
    W ζ hcf hζ Θ hΘ hΘc hΘd Q hQc hQd hQpos α hα s
  let c : SourceData Ω :=
    { κ := κ, hκ := hκ, hκ4 := hκ4, h12p := h12p, βA := βA, hβA := hβA
      b := b, jumps := jumps, c₀ := c₀, hb := hb, hc₀J := hc₀J, hc₀ := hc₀
      P := P, probability := hP, h := h, hh := hh, W := W, ζ := ζ
      hcf := hcf, hζ := hζ, Θ := Θ, hΘ := hΘ, hΘc := hΘc, hΘd := hΘd
      Q := Q, hQc := hQc, hQd := hQd, hQpos := hQpos, α := α, hα := hα, s := s }
  obtain ⟨hcov, hG⟩ := hCover Ω c
  refine ⟨(D Ω c).G, hcov, ?_⟩
  intro r
  let e := (D Ω c).experiment r
  obtain ⟨p₀, A, T, hp₀⟩ := ExperimentGeometryV.exists_testClaims_lossy (hGeometry Ω c r) h13 (hG r)
    (hNear Ω c r) (hSlow Ω c r)
  exact ⟨A, e.data.ang, T, RootF27.unitEvent c r, p₀, hp₀⟩

/-- **The root-test assembly with COVER's unscaled cover and the lossy near binder.** -/
theorem gw2RootTestStatement_of_cover_V_lossy (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (D : ConstructionFamily.{u})
    (hGeometry : RootGeometryVStatement (RootCv.withCover D))
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withCover D))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withCover D)) :
    GW2RootTestStatement.{u} :=
  gw2RootTestStatement_of_oneSided_comparisons_V_lossy h13 (RootCv.withCover D)
    (RootCv.rootCoverStatement_withCover h13 h13₀ D) hGeometry hNear hSlow

/-- **Theorem 1.4 (all four clauses) with the lossy near binder**: the successor of
`Wire.theorem14Statement_assembled6_covers_unscaled` (via GEOM2's `Gm.theorem14Statement_unscaled_V`): Theorems
1.2–1.3 from the proved fibre leaf, GW2's construction `D` with its geometry and the lossy near and the slow
comparisons, SB2DRV's `SB2EntranceK2NStatement` and SB2LIFT's two halves. -/
theorem theorem14Statement_unscaled_V_lossy (D : ConstructionFamily.{u})
    (hGeometry : RootGeometryVStatement (RootCv.withCover D))
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withCover D))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withCover D))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  Wire.theorem14Statement_assembled6_of_rootTests
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{u} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0}
    (gw2RootTestStatement_of_cover_V_lossy Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} D hGeometry hNear hSlow)
    hN hgeo hcond Sec5.Aux61Cpt.cptFibreCover.{u} Sec5.Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.4 with J32 as the construction and the lossy near binder.** -/
theorem theorem14Statement_J32_lossy
    (hGeometry : RootGeometryVStatement RootJ32.constructionFamily.{u})
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement RootJ32.constructionFamily.{u})
    (hSlow : RetainedSlowComparisonsStatement RootJ32.constructionFamily.{u})
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} := by
  rw [← RootJ32.withCover_constructionFamily] at hGeometry hNear hSlow
  exact theorem14Statement_unscaled_V_lossy RootJ32.constructionFamily hGeometry hNear hSlow hN hgeo hcond

/-- **Theorem 1.4 with J32, from round 6's frozen J32 pair with the corrected schedule instances** (Theorems 1.2–1.3
from the proved fibre leaf). -/
theorem theorem14Statement_J32_schedS
    (hGeometry : RootGeometryVStatement RootJ32.constructionFamily.{u})
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (ver : GW2Sdh.SchedVerFamily.{u}) (ch : GW2Sdh.SchedChoiceFamily.{u})
    (hK : GW2Sdi.RootPairInputsSchedLBS Kb Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} ver ch)
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  have h := GW2Sdi.retainedComparisonsLossy_rootJ32B_schedS
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0})
    Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} Kb ver ch hK
  theorem14Statement_J32_lossy hGeometry h.1 h.2 hN hgeo hcond

/-- **Theorem 1.4 with J32, from round 6's frozen stage-variable pair** (R113's root-agnostic interface). -/
theorem theorem14Statement_J32_vpkg
    (hGeometry : RootGeometryVStatement RootJ32.constructionFamily.{u})
    (V : ℕ → GW2Sdi.VPkgFamily.{u}) (lam : GW2Sdh.NearDil.{u}) (hV : GW2Sdi.VPairInputs V lam)
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  have h := GW2Sdi.retainedComparisonsLossy_vpkg
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0})
    Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} V lam hV
  theorem14Statement_J32_lossy hGeometry h.1 h.2 hN hgeo hcond

end InteractingSLE.Theorem14.GW2Sdj
