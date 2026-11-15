/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MgUnb
import InteractingSLE.Spec.Supplement.SB2MgLine

/-!
# SB2(2)'s lower lines: the union with its marks, and the clopen relative region

Packet PROVE-SB2-LCMEAN, round 4. Inputs of K2's (S) at SB2(2)'s lower lines (`Mg.hasSafeLaw_of_markedLines`):

* **`exists_sb2LowerStageSets_marked`**: round 3's sets `A₁`, `A₂` together with the joint-past measurability and the
  history-marked locality of `A₁ ∪ A₂` (the line set at the own time `τ` of piece `ℓ`);
* **`IsStagePullback.image_inv_eq_stageComp`**, **`IsStagePullback.isClopen_stageComp`**: in the mirrored configuration
  read through B's stage chart, the inverse image of the relative domain under the composite relative chart is the
  physical relative component, a connected component of `ℍ ∖ (A₁ ∪ A₂)`, hence open with open complement there (the
  clopen inclusion `hclop` of the (S) lemma).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mg

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **SB2(2)'s retained and explored sets at a lower line, with the union's marks**: `Mf.exists_sb2LowerStageSets`
plus the measurability of `A₁ ∪ A₂` for the joint pasts `pastSigma_up(k) ⊔ pastSigma_cap(ℓ + 1)` and its history-marked
locality for them (the line kernel's input, `Mg.hasSafeLaw_of_markedLines`). -/
theorem exists_sb2LowerStageSets_marked (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ) {θ : ℝ}
    {t : ℝ≥0∞} (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (θ, t))) (τ : ℝ≥0∞)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ A₁ A₂ : Ω → Set ℂ,
      Measurable[mΩ, hittingSigma] A₁ ∧ Measurable[mΩ, hittingSigma] A₂ ∧
      MeasurableSpace.comap A₁ hittingSigma ≤
        aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P ∧
      IsLocalSet A₁ (centredField h u₀) P ∧ IsLocalSet A₂ (centredField h u₀) P ∧
      IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) (centredField h u₀) P ∧
      Measurable[pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
          pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1), hittingSigma]
        (fun ω => A₁ ω ∪ A₂ ω) ∧
      IsHistoryAvoidanceLocal (pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
          pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
        (fun ω => A₁ ω ∪ A₂ ω) (centredField h u₀) P ∧
      (∀ ω, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω)) ∧ (∀ ω, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧
      ∀ᵐ ω ∂P, A₁ ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω ∧
        A₂ ω = fillVer (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) ω := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hup := hE' (Lu.upperSpec u l) (Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  have hcap := isStagedHistory_capSpec (τ := τ) hb (hE' _ hw) (hreg' _) hℓ hwℓ
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  set s₁ := Lu.upperSpec u l with hs₁
  set s₂ := capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ τ with hs₂
  set E₁ := StagedReg.regFam E s₁ with hE₁
  set E₂ := StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) with hE₂
  -- the three marked-local sets
  obtain ⟨hA1, ho1, hd1, hloc1⟩ := Lcd.stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap (hreg' _) (hreg' _)
    hu₀ k ℓ
  obtain ⟨hA2, ho2, hloc2⟩ := Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hcap (hreg' _) hu₀
    (ℓ + 1)
  obtain ⟨-, -, -, hloc⟩ := Lcd.stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap (hreg' _) (hreg' _)
    hu₀ k (ℓ + 1)
  have h𝓜₁ : pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ ℓ ≤ mΩ := sup_le (hup.2.1 k) (hcap.2.1 ℓ)
  have h𝓜₂ : pastSigma κ b jumps s₂ E₂ (ℓ + 1) ≤ mΩ := hcap.2.1 (ℓ + 1)
  have h𝓜 : pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1) ≤ mΩ :=
    sup_le (hup.2.1 k) (hcap.2.1 (ℓ + 1))
  have h𝓜₁𝓜 : pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ ℓ ≤
      pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1) :=
    sup_le_sup_left (pastSigma_mono s₂ E₂ (Nat.le_succ ℓ)) _
  have h𝓜₂𝓜 : pastSigma κ b jumps s₂ E₂ (ℓ + 1) ≤
      pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1) := le_sup_right
  -- line versions and their filled versions
  obtain ⟨B₁, hB₁m, hB₁c, hB₁ae, hB₁loc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, h𝓜₁⟩
    (fun ω => union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω))
    ho1 hA1 hloc1
  obtain ⟨B₂, hB₂m, hB₂c, hB₂ae, hB₂loc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, h𝓜₂⟩
    (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) ho2 hA2 hloc2
  obtain ⟨hA₁m, hA₁c, -, hA₁l⟩ := fillVer_package hh0 h𝓜₁ hB₁c hB₁m hB₁loc
  obtain ⟨hA₂m, hA₂c, -, hA₂l⟩ := fillVer_package hh0 h𝓜₂ hB₂c hB₂m hB₂loc
  -- the union
  have hUm : Measurable[pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1), hittingSigma]
      fun ω => fillVer B₁ ω ∪ fillVer B₂ ω := by
    let _ : MeasurableSpace Ω := pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1)
    exact measurable_union_hitting (hA₁m.mono h𝓜₁𝓜 le_rfl) (hA₂m.mono h𝓜₂𝓜 le_rfl)
  have hUloc : IsHistoryAvoidanceLocal (pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1))
      (fun ω => fillVer B₁ ω ∪ fillVer B₂ ω) (centredField h u₀) P := by
    refine Lv.isHistoryAvoidanceLocal_of_ae_enlargement hloc ?_ fun U hUH => hUm (measurableSet_avoid U.isOpen hUH)
    filter_upwards [hB₁ae, hB₂ae] with ω h1 h2
    rintro z ⟨hz | hz, -⟩
    · have hz' : z ∈ B₁ ω := by rw [h1]; exact Or.inl hz
      exact Or.inl (subset_fillVer (fun ω => (hB₁c ω).1) ω hz')
    · have hz' : z ∈ B₂ ω := by rw [h2]; exact hz
      exact Or.inr (subset_fillVer (fun ω => (hB₂c ω).1) ω hz')
  have hUc : ∀ ω, fillVer B₁ ω ∪ fillVer B₂ ω ⊆ H ∧ IsOpen (H \ (fillVer B₁ ω ∪ fillVer B₂ ω)) := by
    intro ω
    refine ⟨union_subset (hA₁c ω).1 (hA₂c ω).1, ?_⟩
    have e : H \ (fillVer B₁ ω ∪ fillVer B₂ ω) = (H \ fillVer B₁ ω) ∩ (H \ fillVer B₂ ω) := by
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, mem_union]
      tauto
    rw [e]
    exact (hA₁c ω).2.inter (hA₂c ω).2
  have hUl : IsLocalSet (fun ω => fillVer B₁ ω ∪ fillVer B₂ ω) (centredField h u₀) P :=
    ((isLocalSet_tfae hh0 (hUm.mono h𝓜 le_rfl) (Eventually.of_forall hUc)).out 4 1).2 hUloc.isAvoidanceLocal
  refine ⟨fillVer B₁, fillVer B₂, hA₁m.mono h𝓜₁ le_rfl, hA₂m.mono h𝓜₂ le_rfl,
    hA₁m.comap_le.trans hd1, hA₁l, hA₂l, hUl, hUm, hUloc, hA₁c, hA₂c, ?_⟩
  filter_upwards [hB₁ae, hB₂ae] with ω h1 h2
  refine ⟨?_, ?_⟩
  · unfold fillVer; rw [h1]
  · unfold fillVer; rw [h2]

/-! ### The clopen relative region -/

section Clopen

open LP (reflectC)
open _root_.InteractingSLE.Theorem14.SB.Union (relComp)

variable {A' : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t ur χ lam : ℝ}
  {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ} {G₀ GE G v : ℂ → ℝ}

/-- The open complement of a component of an open set. -/
theorem isOpen_sdiff_connectedComponentIn {U : Set ℂ} (hU : IsOpen U) (z : ℂ) :
    IsOpen (U \ connectedComponentIn U z) := by
  refine isOpen_iff_forall_mem_open.2 fun y hy =>
    ⟨connectedComponentIn U y, fun x hx => ⟨connectedComponentIn_subset _ _ hx, fun hxz => hy.2 ?_⟩,
      hU.connectedComponentIn, mem_connectedComponentIn hy.1⟩
  rw [connectedComponentIn_eq hxz, ← connectedComponentIn_eq hx]
  exact mem_connectedComponentIn hy.1

theorem IsRelConfigJKL.inv_fwd
    (hc : Lm.IsRelConfigJKL A' Ψ Ψi LΨ Sb w Wr η ηr t ur χ lam β₀ βE βu S₀ SE Su G₀ GE G v)
    {z : ℂ} (hz : z ∈ H \ A') : Ψi (Ψ z) = z := by
  have h := (FinRel.IsRelConfigJK.chart hc).inv_fwd (z := reflectC z) (Lm.reflectC_mem_H_diff_iff.2 (by
    rwa [LP.reflectC_reflectC]))
  simp only [LP.reflectC_reflectC] at h
  have h2 := congrArg reflectC h
  rwa [LP.reflectC_reflectC, LP.reflectC_reflectC] at h2

/-- **In the mirrored configuration the relative component is a connected component** of the complement of the
union. -/
theorem IsRelConfigJKL.connectedComponentIn_eq_relComp
    (hc : Lm.IsRelConfigJKL A' Ψ Ψi LΨ Sb w Wr η ηr t ur χ lam β₀ βE βu S₀ SE Su G₀ GE G v)
    {z₀ : ℂ} (hz₀ : z₀ ∈ relComp A' Ψ Wr ur) :
    connectedComponentIn (H \ (A' ∪ fwdHull w t)) z₀ = relComp A' Ψ Wr ur := by
  have hz₀' : reflectC z₀ ∈ relComp (reflectC '' A') (fun z => reflectC (Ψ (reflectC z))) (-Wr) ur := by
    rw [Ln.relComp_reflect]
    exact mem_image_of_mem _ hz₀
  have e := Union.connectedComponentIn_eq_relComp (FinRel.IsRelConfigJK.chart hc) (FinRel.IsRelConfigJK.hWr hc)
    (FinRel.IsRelConfigJK.hWr0 hc) (FinRel.IsRelConfigJK.hu hc) (FinRel.IsRelConfigJK.hullIn hc)
    (FinRel.IsRelConfigJK.hullFr hc) hz₀'
  rw [Ln.relComp_reflect, LP.fwdHull_neg, Ln.H_diff_union_image_reflectC] at e
  have hz₀U : z₀ ∈ H \ (A' ∪ fwdHull w t) := Ln.IsRelConfigJKL.relComp_subset hc hz₀
  rw [← Ln.image_reflectC_connectedComponentIn hz₀U] at e
  exact (image_injective.2 LP.reflectC_injective) e

/-- **The clopen relative region** (the `hclop` input of `hasSafeLaw_of_markedLines`): for a composite relative chart
`crel` with `crel.2.1 = c.2.1 ∘ Ψi` on `ℍ`, the inverse image of the relative domain lies in `ℍ ∖ (A₁ ∪ A₂)` with open
remainder there. -/
theorem IsStagePullback.clopen {c : Chart} {gb : ℂ → ℂ} {A₁ A₂ : Set ℂ}
    (hp : Ln.IsStagePullback c gb A₁ A₂ A' (fwdHull w t))
    (hc : Lm.IsRelConfigJKL A' Ψ Ψi LΨ Sb w Wr η ηr t ur χ lam β₀ βE βu S₀ SE Su G₀ GE G v)
    {crel : Chart} (hcrinv : ∀ y ∈ H, crel.2.1 y = c.2.1 (Ψi y)) :
    crel.2.1 '' (H \ fwdHull Wr ur) ⊆ H \ (A₁ ∪ A₂) ∧
      IsOpen ((H \ (A₁ ∪ A₂)) \ crel.2.1 '' (H \ fwdHull Wr ur)) := by
  set R := relComp A' Ψ Wr ur with hR
  set U := H \ (A₁ ∪ A₂) with hU
  set U' := H \ (A' ∪ fwdHull w t) with hU'
  have hRU' : R ⊆ U' := Ln.IsRelConfigJKL.relComp_subset hc
  have hmap' : ∀ y ∈ U', c.2.1 y ∈ U := fun y hy => ⟨hp.conf.2.1 hy.1, fun h => hy.2
    (h.elim (fun h1 => Or.inl ((hp.corr₁ _ hy.1).1 h1)) (fun h2 => Or.inr ((hp.corr₂ _ hy.1).1 h2)))⟩
  have hUD : U ⊆ (c.dom : Set ℂ) := fun y hy => by
    by_contra hyD
    exact hy.2 (Or.inl (hp.dom₁ ⟨hy.1, hyD⟩))
  have hmap : ∀ z ∈ U, c.1 z ∈ U' := fun z hz => by
    obtain ⟨hzH, hzz⟩ := Ln.chart_fwd_mem_of_mem_dom hp.conf (hUD hz)
    refine ⟨hzH, fun h => hz.2 ?_⟩
    rcases h with h | h
    · exact Or.inl (by rw [← hzz]; exact (hp.corr₁ _ hzH).2 h)
    · exact Or.inr (by rw [← hzz]; exact (hp.corr₂ _ hzH).2 h)
  -- the inverse image of the relative domain is the image of the relative component
  have himg : crel.2.1 '' (H \ fwdHull Wr ur) = c.2.1 '' R := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hcrinv y hy.1]
      exact ⟨Ψi y, ⟨Ln.IsRelConfigJKL.inv_mem hc hy.1, by rw [Ln.IsRelConfigJKL.fwd_inv hc hy.1]; exact hy⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Ψ x, hx.2, ?_⟩
      rw [hcrinv _ hx.2.1, IsRelConfigJKL.inv_fwd hc hx.1]
  rw [himg]
  refine ⟨fun z hz => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := hz
    exact hmap' x (hRU' hx)
  · -- the remainder is the image of the remainder
    have hrem : U \ c.2.1 '' R = c.2.1 '' (U' \ R) := by
      ext z
      constructor
      · rintro ⟨hzU, hzR⟩
        refine ⟨c.1 z, ⟨hmap z hzU, fun h => hzR ⟨c.1 z, h, ?_⟩⟩, ?_⟩
        · exact (Ln.chart_fwd_mem_of_mem_dom hp.conf (hUD hzU)).2
        · exact (Ln.chart_fwd_mem_of_mem_dom hp.conf (hUD hzU)).2
      · rintro ⟨y, ⟨hyU', hyR⟩, rfl⟩
        refine ⟨hmap' y hyU', ?_⟩
        rintro ⟨x, hx, e⟩
        exact hyR (hp.conf.injOn (hRU' hx).1 hyU'.1 e ▸ hx)
    rw [hrem]
    have hU'o : IsOpen U' := Ln.IsRelConfigJKL.isOpen_compl_union hc
    have hremo : IsOpen (U' \ R) := by
      rcases R.eq_empty_or_nonempty with hR0 | ⟨z₀, hz₀⟩
      · rw [hR0, sdiff_empty]; exact hU'o
      · have e := IsRelConfigJKL.connectedComponentIn_eq_relComp hc hz₀
        rw [← hR, ← hU'] at e
        rw [← e]
        exact isOpen_sdiff_connectedComponentIn hU'o z₀
    exact SmallGammaGeodesics.CC.isOpen_image_conf hremo (hp.conf.1.mono fun y hy => hy.1.1)
      (hp.conf.injOn.mono fun y hy => hy.1.1)

end Clopen

end InteractingSLE.Theorem14.SB.Mg
