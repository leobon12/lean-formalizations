/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmQJ32
import InteractingSLE.Spec.Supplement.GW2SdyCut

/-!
# Theorem 1.4's successor top: J32 on the scaled cover, no geometry binder, both comparison binders lossy

Packet PROVE-GW2-SDE (round 11). The successor of PROVE-GW2-GEOM2's `Gm.theorem14Statement_J32_scaled_lossy_geom`
(decision D2: J32's geometry proved; ruling R118: COVER's scaled cover) with SDE's lossy slow binder
`GW2Sdx.RetainedSlowComparisonsLossyStatement` (decision D3) in place of the exact slow binder. The only change in the
chain is the uniform slow constant: `GW2Sdx.HasSlowComparisonModelsLossy.exists_modelSlow` has the same conclusion as
the exact `exists_modelSlow`.

* `exists_testClaims_lossyS` (GEOM2's `ExperimentGeometryA.exists_testClaims_lossy` with the lossy slow binder);
* `gw2RootTestStatement_of_oneSided_comparisons_A_lossyS`, `gw2RootTestStatement_of_scaledCover_A_lossyS`,
  `theorem14Statement_scaled_A_lossyS`;
* **`theorem14Statement_J32_scaled_lossyS`**: Theorem 1.4 with J32 on the scaled cover; binders: the lossy near
  binder, the lossy slow binder, and the gap's measurability and positivity (plus SB2's three statements);
* **`theorem14Statement_J32_scaled_vpkgXC`**: the same with both comparison binders from SDE's successor pair with
  decision D3a's cut slow facts (`retainedComparisonsLossyXC_vpkg_scaled`, inputs `VPairInputsXC`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdy

open GW2TipSystem GW2TipSystem.Gm GW2TipSystem.RootC24 GW2Schedule Exist Staged StagedLaw

section Claims

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **All per-root claims from the D2 geometry and BOTH lossy comparison binders** (GEOM2's
`ExperimentGeometryA.exists_testClaims_lossy` with `GW2Sdx.HasSlowComparisonModelsLossy`). -/
theorem exists_testClaims_lossyS {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {G : Set Ω} {e : Experiment c r}
    (hg : ExperimentGeometryA c r G e) (h13 : Theorem13Statement.{u})
    (hG : MeasurableSet[c.sigma r []] G)
    (hNear : GW2Sdi.HasNearCrossingModelsLossy.{u} c.κ c.P (e.data.alive G)
      (fun l a ω => e.retained.kernel l a ω (e.data.reach l a)))
    (hSlow : GW2Sdx.HasSlowComparisonModelsLossy.{u} c.κ e.driftBound
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
  let d' : RootK3.StageModelData Ω c.Θ c.Q RootV7.DriverRecord (c.sigma r) :=
    { e.retained with p₀ := p₀ }
  have hUnit := RootV7.ae_unit_of_record_clock (d := d') (fun _ _ => rfl)
    e.Y e.clock hg.record_read hg.clock_spec
  obtain ⟨A, T, hc⟩ := testClaims_of_modelCross_unitEvent_A (d := d') c r
    (hNear.modelCross h13 c.hκ c.hκ4) hG hg.band_open
    hg.observation hg.regularity e.sampleMeas hg.reach_measurable
    (fun _ _ => RootV7.measurableSet_slowSet)
    (fun _ _ => Eventually.of_forall fun _ _ => rfl)
    hg.reach_identification hp₀ hp₀1 hModelSlow hUnit
  exact ⟨p₀, A, T, hc⟩

end Claims

/-- **The complete root-test statement with the D2 geometry and both lossy comparison binders.** -/
theorem gw2RootTestStatement_of_oneSided_comparisons_A_lossyS
    (h13 : Theorem13Statement.{u}) (D : ConstructionFamily.{u})
    (hCover : RootCoverStatement D) (hGeometry : RootGeometryAStatement D)
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement D)
    (hSlow : GW2Sdx.RetainedSlowComparisonsLossyStatement D) :
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
  obtain ⟨p₀, A, T, hp₀⟩ := exists_testClaims_lossyS (hGeometry Ω c r) h13 (hG r) (hNear Ω c r) (hSlow Ω c r)
  exact ⟨A, e.data.ang, T, RootF27.unitEvent c r, p₀, hp₀⟩

/-- **The root-test assembly with COVER's scaled cover, the D2 geometry and both lossy comparison binders.** -/
theorem gw2RootTestStatement_of_scaledCover_A_lossyS (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (D : ConstructionFamily.{u}) (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryAStatement (RootCv.withScaledCover D gap))
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withScaledCover D gap))
    (hSlow : GW2Sdx.RetainedSlowComparisonsLossyStatement (RootCv.withScaledCover D gap)) :
    GW2RootTestStatement.{u} :=
  gw2RootTestStatement_of_oneSided_comparisons_A_lossyS h13 (RootCv.withScaledCover D gap)
    (RootCv.rootCoverStatement_withScaledCover h13 h13₀ D gap hgap hpos) hGeometry hNear hSlow

/-- **Theorem 1.4 (all four clauses) on the scaled cover with the D2 geometry and both lossy comparison binders**
(Theorems 1.2–1.3 from the proved fibre leaf). -/
theorem theorem14Statement_scaled_A_lossyS (D : ConstructionFamily.{u}) (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryAStatement (RootCv.withScaledCover D gap))
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withScaledCover D gap))
    (hSlow : GW2Sdx.RetainedSlowComparisonsLossyStatement (RootCv.withScaledCover D gap))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  Wire.theorem14Statement_assembled6_of_rootTests
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{u} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0}
    (gw2RootTestStatement_of_scaledCover_A_lossyS Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} D gap hgap hpos hGeometry hNear hSlow)
    hN hgeo hcond Sec5.Aux61Cpt.cptFibreCover.{u} Sec5.Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.4 with J32 on the scaled cover, geometry discharged, both comparison binders lossy**: the successor of
GEOM2's `Gm.theorem14Statement_J32_scaled_lossy_geom` with `GW2Sdx.RetainedSlowComparisonsLossyStatement` in place of
the exact slow binder. -/
theorem theorem14Statement_J32_scaled_lossyS (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap))
    (hSlow : GW2Sdx.RetainedSlowComparisonsLossyStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  theorem14Statement_scaled_A_lossyS RootJ32.constructionFamily gap hgap hpos
    (RootJ32.rootGeometryAStatement_withScaledCover Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} gap)
    hNear hSlow hN hgeo hcond

/-- **Theorem 1.4 with J32 on the scaled cover from SDE's successor pair with D3a's cut slow facts** (decisions D1,
D2, D3, D3a; ruling R118): both comparison binders from `VPairInputsXC`, geometry discharged. -/
theorem theorem14Statement_J32_scaled_vpkgXC (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (V : ℕ → GW2Sdx.VPkgXFamily.{u}) (lam : GW2Sdh.NearDil.{u}) (hV : VPairInputsXC V lam)
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  have h := retainedComparisonsLossyXC_vpkg_scaled
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0})
    Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} V lam hV gap
  theorem14Statement_J32_scaled_lossyS gap hgap hpos h.1 h.2 hN hgeo hcond

end InteractingSLE.Theorem14.GW2Sdy
