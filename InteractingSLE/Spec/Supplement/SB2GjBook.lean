/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GiRec
import InteractingSLE.Spec.Supplement.SB2GjStmt
import InteractingSLE.Spec.Supplement.SB2CzTail
import InteractingSLE.Spec.Supplement.SB2CvOff
import InteractingSLE.Spec.Supplement.SB2CqRJoint
import InteractingSLE.Spec.Supplement.SB2NcGeo

/-!
# The root's canonical objects from the chain facts on the root event

Packet PROVE-GW2-GEOM2, round 17 (decision D79). **`canonIdent_of_rootChainFacts`**: from the objects of NOJUMP's root
statement (a hull `K` with `fill K = A₁ 0` on the live event `FB`, an offset `x₀`, both measurable for the completed
line σ-algebra `lineFiltC P 𝓖 0`, the root event `Fr` equal a.s. to `Ne.rootEv`), the chain facts `Qx.ChainFacts` of
the canonical driver for the word `shiftW x₀ β₁` a.s. on `Fr`, and ROOTX's positive-root visit
(`Gj.SB2PosRootVisitStatement`'s conclusion), the objects of `Ct.SB2LowerRootIdentStatement`'s conclusion:

* the hull: CANON's exact retained hull (`Cz.exists_exactRetHull`, measurable for the retained past), whose fill is the
  retained union's on B's launches;
* the offset: a version of `x₀` measurable for `Ms.stageMarks (ℓ + 1)` (the capped past at B-time `0` lies there,
  `Cz.capPast_le_stageMarks_succ`; kernel constancy and `Qx.exists_measurable_ae_eq_of_kernel_const`);
* the event `G = FB' ∩ G₁ ∩ {positive root at ℓ}`: `FB'` a version of `FB` in `Ms.stageMarks (ℓ + 1)`, `G₁` the exact
  hull's event, and the positive-root event, which is a function of B's runs through `ℓ + 1` and the upper run
  (`Cf.rootEv_congr`, `Cf.drv_eq_of_run_eq`, `Cf.visitTime_congr`);
* `Dr` by `Gi.exists_canonRec_det`; the chain facts move to the exact objects by CANON's `Cz.chainFacts_congr`, a
  positive root lying in the root event once it visits `R`;
* `Ct.RootCover`: every positive root at `ℓ` is in `G`.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Gj

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf Ms Lu Mz Lk

/-- **The root's canonical objects from the chain facts on the root event.** See the module docstring. -/
theorem canonIdent_of_rootChainFacts (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {𝓖 : Filtration ℝ≥0 mΩ}
    (h𝓖0 : 𝓖 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    {A₁0 : Ω → Set ℂ}
    (hA₁0 : ∀ᵐ ω ∂P, A₁0 ω = Mf.fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        ℓ ω) ω)
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀) {FB Fr : Set Ω} (hFBm : MeasurableSet[lineFiltC P 𝓖 0] FB)
    (hKF : ∀ᵐ ω ∂P, ω ∈ FB → fillH (K ω) = A₁0 ω)
    (hFBiff : ∀ᵐ ω ∂P, ω ∈ FB ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2))
    (hFriff : ∀ᵐ ω ∂P, ω ∈ Fr ↔ ω ∈ Ne.rootEv κ b jumps E u l k ℓ)
    {β₁ : Ω → BoundaryWord} (hβ : Measurable β₁)
    (hfacts : ∀ᵐ ω ∂P, ω ∈ Fr → Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h
      (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) x₀ hKc hKp ω)
    (hvis : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      Ct.PosRootAt (κ := κ) b jumps E u l k ℓ ω →
      ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (Mz.lowerD b jumps E ω ℓ).2 ∧
        Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (Mz.lowerD b jumps E ω) ℓ)
          (Mz.lowerD b jumps E ω ℓ) t = ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ)) :
    ∃ (G : Set Ω) (K' : Ω → Set ℂ) (x₁ : Ω → ℝ) (Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
      (hK'c : ∀ ω, IsCompact (K' ω)) (hK'p : ∀ ω, IsPreconnected (K' ω ∪ Restart.lowerHalf)),
      Ct.RootCover (κ := κ) b jumps P E u l k ℓ G ∧
      Mz.CanonIdentOn h12p hκ b jumps P h E u l k ℓ G (fun ω => BoundaryWord.shiftW (x₁ ω) (β₁ ω)) K' x₁ Dr
        hK'c hK'p := by
  classical
  obtain ⟨hE', -, hrun⟩ := StagedReg.regFam_spec hb hE hER
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have h𝒮₁ : Ms.stageMarks κ b jumps E u l k (ℓ + 1) ≤ mΩ :=
    sup_le ((hE' _ hsu).2.1 k) ((hE' w hw).2.1 (ℓ + 1))
  have hmono : Ms.stageMarks κ b jumps E u l k ℓ ≤ Ms.stageMarks κ b jumps E u l k (ℓ + 1) :=
    Mz.stageMarks_mono (Nat.le_succ ℓ)
  have h𝓖𝒮 : 𝓖 0 ≤ Ms.stageMarks κ b jumps E u l k (ℓ + 1) := by
    rw [h𝓖0]; exact Cz.capPast_le_stageMarks_succ E u l k ℓ hℓ hwℓ
  -- the exact hull
  obtain ⟨Kx, G₁, hKxm, hKxc, hKxp, hG₁m, hG₁cov, hG₁f⟩ :=
    Cz.exists_exactRetHull h12p h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ hu₀
  -- the exact offset
  have hx₀' : Measurable[mΩ ⊓ aeSigma (Ms.stageMarks κ b jumps E u l k (ℓ + 1)) P] x₀ :=
    hx₀.mono (inf_le_inf_left _ (WalkLaw.aeSigma_mono (P := P) h𝓖𝒮)) le_rfl
  have hk := Cz.ae_ae_eq_of_measurable_aeSigma h𝒮₁ hx₀'
  obtain ⟨x₁, hx₁m, hx₁e⟩ := Qx.exists_measurable_ae_eq_of_kernel_const (P := P) h𝒮₁
    (hx₀.mono inf_le_left le_rfl) (G := univ) (by filter_upwards [hk] with ω₀ h1 _ using h1)
  -- the live event in the retained past through `ℓ + 1`
  obtain ⟨FB', hFB'm, hFBe⟩ := Cz.exists_eq_of_measurableSet_inf_aeSigma (P := P) h𝓖𝒮 hFBm
  -- the positive-root event
  set G₂ : Set Ω := {ω | Ct.PosRootAt (κ := κ) b jumps E u l k ℓ ω} with hG₂def
  have hG₂det : ∀ ω ω', (∀ n, n ≤ ℓ + 1 →
        ExplState.run κ b jumps w (lowerD b jumps E ω) n = ExplState.run κ b jumps w (lowerD b jumps E ω') n) →
      ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k =
        ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω') k →
      ω ∈ G₂ → ω' ∈ G₂ := by
    intro ω ω' hwr hur hω
    obtain ⟨hl, hev, hs⟩ := hω
    have hR : realMax (upperPrefix κ b jumps E u l k ω) = realMax (upperPrefix κ b jumps E u l k ω') := by
      have hur' : ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩
          (fun j => E ⟨u, true, scheduleProgram 0 l⟩ j ω) k =
          ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩ (fun j => E ⟨u, true, scheduleProgram 0 l⟩ j ω') k :=
        hur
      congr 1
      unfold SB.upperPrefix
      rw [Qx.prefixPhysSet_congr _ hur']
    rw [hR] at hev hs
    obtain ⟨hent', hrel'⟩ := (Cf.rootEv_congr _ ℓ hwr).1 hev
    have hrel := hev.2
    have hl' : (ExplState.run κ b jumps w (lowerD b jumps E ω') (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [← hwr (ℓ + 1) le_rfl]; exact hl
    obtain ⟨h2, h1⟩ := Cf.drv_eq_of_run_eq (hwr (ℓ + 1) le_rfl) hl
    have h1' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (lowerD b jumps E ω ℓ).2 →
        (lowerD b jumps E ω ℓ).1 t = (lowerD b jumps E ω' ℓ).1 t := fun t ht => h1 t ht.le
    have hsh : Lk.shiftD κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω'))
        (lowerD b jumps E ω) 0 = Lk.shiftD κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω'))
        (lowerD b jumps E ω') 0 := by
      have hrn : Lk.wRun κ (-(Real.pi / 2)) b jumps (lowerD b jumps E ω) ℓ =
          Lk.wRun κ (-(Real.pi / 2)) b jumps (lowerD b jumps E ω') ℓ := hwr ℓ (Nat.le_succ ℓ)
      unfold Lk.shiftD
      rw [ite_eq_left rfl, ite_eq_left rfl, hrel, hrel', ← hrn, Cf.visitTime_congr _ h2 h1' _]
    refine ⟨hl', ⟨hent', hrel'⟩, ?_⟩
    rw [← h2, ← hsh]
    exact hs
  -- the geometry of the retained union and the regularized runs
  have hgeo := Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ
  -- the chain facts for the exact objects on `G`
  have hfacts' : ∀ᵐ ω ∂P, ω ∈ (FB' ∩ G₁) ∩ G₂ → Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h
      (fun ω => BoundaryWord.shiftW (x₁ ω) (β₁ ω)) x₁ hKxc hKxp ω := by
    filter_upwards [hfacts, hFBe, hFBiff, hFriff, hvis, hKF, hA₁0, hG₁f, hx₁e, hgeo, hrun w hw, hrun _ hsu]
      with ω hf hFBe' hFBi hFri hvisω hKFω hA₁ω hG₁ω hx₁ω hgeoω hrw hru hωG
    have hFBω : ω ∈ FB := (show (ω ∈ FB) = (ω ∈ FB') from hFBe').symm ▸ hωG.1.1
    obtain ⟨hst, -, -⟩ := hFBi.1 hFBω
    obtain ⟨hl, hev, hs⟩ := hωG.2
    obtain ⟨t₀, ht₀, ht₀R⟩ := hvisω hst.1 hωG.2
    have hvis' : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (lowerD b jumps E ω ℓ).2 ∧
        Lk.pcPt (ExplState.run κ b jumps w (lowerD b jumps E ω) ℓ) (lowerD b jumps E ω ℓ) t =
          ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) := ⟨t₀, ht₀, ht₀R⟩
    have hrel := hev.2
    have hsh : Lk.shiftD κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (lowerD b jumps E ω) 0 = Lk.visitTime (ExplState.run κ b jumps w (lowerD b jumps E ω) ℓ)
          (lowerD b jumps E ω ℓ) (realMax (upperPrefix κ b jumps E u l k ω)) := by
      unfold Lk.shiftD
      rw [ite_eq_left rfl, hrel]
    have hentr : Nd.entrR κ b jumps E u l k ℓ ω < (E w ℓ ω).2 := by
      have he : Nd.entrR κ b jumps E u l k ℓ ω = (Lk.visitTime (ExplState.run κ b jumps w (lowerD b jumps E ω) ℓ)
          (lowerD b jumps E ω ℓ) (realMax (upperPrefix κ b jumps E u l k ω)) : ℝ≥0∞) :=
        Ck.entrTime_eq_visitTime hvis'
      rw [he, ← hsh]
      exact tsub_pos_iff_lt.1 (pos_iff_ne_zero.2 hs)
    have hroot : ω ∈ Ne.rootEv κ b jumps E u l k ℓ :=
      ⟨hst, hrel, Cf.not_zeroRoot_of_ent (by rw [hrel]; exact hev.1), hentr⟩
    have hfω := hf (hFri.2 hroot)
    have hXc := (hgeoω hl).1
    have hfK : fillH (K ω) = fillH (Nc.retX κ b jumps E u l k ℓ ω) := by
      rw [hKFω hFBω, hA₁ω]
      exact Cz.fillVer_first_eq_of hl hrw hru hXc _
    have hfKx : fillH (Kx ω) = fillH (K ω) := by
      rw [(hG₁ω hωG.1.2).2, hfK]
    have hx : x₁ ω = x₀ ω := (hx₁ω (mem_univ ω)).symm
    exact Cz.chainFacts_congr h12p hκ E u l k ℓ hfKx (by rw [hx]) hx hfω
  have hc₁ : Measurable fun ω => BoundaryWord.shiftW (x₁ ω) (β₁ ω) :=
    BoundaryWord.measurable_shiftW.comp ((hx₁m.mono h𝒮₁ le_rfl).prodMk hβ)
  obtain ⟨Dr, hDrm, hDrreg, hDrrec⟩ := Gi.exists_canonRec_det h12p hκ E u l k ℓ (hER w hw) (hER _ hsu) h𝒮₁
    hh.1 hc₁ hKxc hKxp (fun n j => hmono _ (hKxm n j)) hx₁m (hFB'm.inter (hmono _ hG₁m)) hG₂det hfacts'
  refine ⟨(FB' ∩ G₁) ∩ G₂, Kx, x₁, Dr, hKxc, hKxp, ?_, hDrm, hDrreg, ?_⟩
  · -- every positive root at `ℓ` is in `G`
    filter_upwards [hFBiff, hFBe, hG₁cov] with ω hFBi hFBe' hG₁c hup hpos
    obtain ⟨hl, hev, hs⟩ := hpos
    have hζ : 0 < (E w ℓ ω).2 := by
      refine pos_iff_ne_zero.2 fun h0 => hs ?_
      show (lowerD b jumps E ω ℓ).2 - _ = 0
      rw [show (lowerD b jumps E ω ℓ).2 = 0 from h0, zero_tsub]
    have hFBω : ω ∈ FB := hFBi.2 ⟨⟨hup, hl⟩, hev.2.ge, hζ⟩
    exact ⟨⟨(show (ω ∈ FB) = (ω ∈ FB') from hFBe') ▸ hFBω, hG₁c hl⟩, ⟨hl, hev, hs⟩⟩
  · filter_upwards [hDrrec, hfacts', hG₁f] with ω h1 h2 h3 hωG
    obtain ⟨-, -, -, hch, hpos, -⟩ := h2 hωG
    exact ⟨(h3 hωG.1.2).2, hch, hpos, h1 hωG⟩

end InteractingSLE.Theorem14.SB.Gj
