/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3GeoAccess
import InteractingSLE.Spec.Supplement.SB2HEntry
import InteractingSLE.Spec.Supplement.SB4RMirrorGeom
import InteractingSLE.Spec.Supplement.SB2LkFF

/-!
# Lemma S3: the geometry at the actual run chart of the schedule (the canonical old chart)

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3, specification pp. 579–580; PROVE-T14-S3's "canonical chart choices").
Deterministic. `exists_s3_geometry_of_s2` takes an arbitrary left entry chart of the old history; T14-S3's word
provenance (`HasInteriorStageSides`) and marked-mean identification are stated for the **run chart** of the schedule
and its physical readout `LuM.bdVal`. This file attaches the two:

* **`exists_s3_geometry_runChart`**: for the schedule from `0` (regular pieces, injective launched traces) at an
  unfinished state whose physical prefix is a path image `A`, the run chart recentred at its left entry value `a`
  (`Lx.isLeftEntryValue_runChart`, `Lf.isLeftEntryChart_runChart`) is a left entry chart of `A`; its boundary map
  `g` has finite fibres (`Lk.pinv_schedule`, `Lk.finite_fibre_of_pinv`); and on S2's lift every conclusion of
  `exists_s3_geometry_of_s2` holds for `g(· + a)`, together with the run chart's own readout: it tends along the
  approach to the real coordinate `(γ t).re + a` from `ℍ`, and `LuM.bdVal` of the run chart at that coordinate is the
  physical point (an interior landing, the hypothesis of `HasInteriorStageSides`).

R48 (as amended for Theorem 1.4): nothing here uses Theorem 1.4 or `Theorem14Statement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.SB.S3.Canon

open Supp9B (IsProperCurve leftSide rightSide closedRightSide)
open Exist.Staged Exist.StagedLaw
open Geo

/-- **The S3 geometry at the actual run chart of a schedule** (Lemma S3's canonical old chart). For the schedule from
`0` with regular pieces and injective launched traces, at a state `n` that is not finished and whose physical prefix
is a path image `A`, the run chart recentred at its left entry value `a` at `L = min (A ∩ ℝ)` is a left entry chart
of `A`; its boundary map `g` (continuous on `ℍ̄`, boundary limits of the inverse) has finite fibres; and on S2's lift
`γ` (`g(γ(s) + a) = β'(t_L + s)`) all the conclusions of `exists_s3_geometry_of_s2` hold for the recentred map
`g(· + a)`, together with the readout of the **run chart itself**: along the approach it tends to the real coordinate
`(γ t).re + a` from `ℍ`, whose physical boundary value `LuM.bdVal` is the physical point `β'(t_L + t)`. -/
theorem exists_s3_geometry_runChart {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (l : List (ℝ × ℝ≥0))
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (Lf.sspec 0 l) D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (Lf.sspec 0 l) k) (D k).2))
    (hinj : Lk.InjLaunches κ b jumps (Lf.sspec 0 l) D) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps (Lf.sspec 0 l) D n) ≠ GW1Conn.stDone)
    {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hpA : p '' Icc 0 1 = prefixPhysSet κ b jumps (Lf.sspec 0 l) D n)
    {β' : ℝ≥0 → ℂ} (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hinjη : InjOn η {t | (t : ℝ≥0∞) ≤ ζ}) :
    ∃ (a : ℝ) (g : ℂ → ℂ),
      IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1))
        ((stChart (ExplState.run κ b jumps (Lf.sspec 0 l) D n)).recenter a) ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g (stChart (ExplState.run κ b jumps (Lf.sspec 0 l) D n)).2.1 H ∧
      (∀ q ∈ Hbar, Tendsto (stChart (ExplState.run κ b jumps (Lf.sspec 0 l) D n)).2.1 (𝓝[H] q) (𝓝 (g q))) ∧
      (∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) ∧
      ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ),
        β' tL = realMin (p '' Icc 0 1) ∧ IsProperCurve γ ∧ γ 0 = 0 ∧ (∀ s, g (γ s + a) = β' (tL + s)) ∧
        ∀ a₁ b₁ t : ℝ≥0, t ∈ Ioo a₁ b₁ → β' '' Icc (tL + a₁) (tL + b₁) ⊆ p '' Icc 0 1 →
          ((tL + b₁ : ℝ≥0) : ℝ≥0∞) < ζ → η (tL + b₁) ∈ H → (∀ s ≤ tL + b₁, β' s = η s) →
          (γ t).im = 0 ∧ 0 < (γ t).re ∧ (𝓝[H] (γ t)).NeBot ∧
          Filter.map (fun v => g (v + a)) (𝓝[H] (γ t)) ≤
            𝓟 (leftSide β' ∩ (H \ fillH (p '' Icc 0 1 ∪ η '' Icc 0 (tL + b₁)))) ∧
          Filter.map (fun v => g (v + a)) (𝓝[H] (γ t)) ≤
            𝓝[H \ fillH (p '' Icc 0 1 ∪ η '' Icc 0 (tL + b₁))] (η (tL + t)) ∧
          (∀ S T : Set ℂ, β' '' Icc (tL + a₁) (tL + b₁) ⊆ S →
            S ⊆ fillH (p '' Icc 0 1 ∪ η '' Icc 0 (tL + b₁)) → T ⊆ fillH (p '' Icc 0 1 ∪ η '' Icc 0 (tL + b₁)) →
            ∃ r > 0, Filter.map (fun v => g (v + a)) (𝓝[H] (γ t)) ≤
              𝓝[FinRel.freeNear T S (η (tL + t)) r] (η (tL + t))) ∧
          IsMapOut (fillH (η '' Icc 0 (tL + b₁)))
            (fun z => fwdMap (fun r : ℝ => w r.toNNReal) (tL + b₁) z + w (tL + b₁)) ∧
          (∃ y : ℝ, y < 0 ∧ extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) (tL + b₁)) y = η (tL + t) ∧
            Tendsto (fun z => fwdMap (fun r : ℝ => w r.toNNReal) (tL + b₁) z + w (tL + b₁))
              (Filter.map (fun v => g (v + a)) (𝓝[H] (γ t))) (𝓝[H] ((y + w (tL + b₁) : ℝ) : ℂ)) ∧
            ∃ r > 0, Disjoint (ball ((y + w (tL + b₁) : ℝ) : ℂ) r)
              ((fun z => fwdMap (fun r : ℝ => w r.toNNReal) (tL + b₁) z + w (tL + b₁)) ''
                (fillH (p '' Icc 0 1 ∪ η '' Icc 0 (tL + b₁)) \ fillH (η '' Icc 0 (tL + b₁))))) ∧
          Tendsto (stChart (ExplState.run κ b jumps (Lf.sspec 0 l) D n)).1
            (Filter.map (fun v => g (v + a)) (𝓝[H] (γ t))) (𝓝[H] (((γ t).re + a : ℝ) : ℂ)) ∧
          LuM.bdVal (stChart (ExplState.run κ b jumps (Lf.sspec 0 l) D n)) (((γ t).re + a : ℝ) : ℂ) =
            β' (tL + t) := by
  set s := ExplState.run κ b jumps (Lf.sspec 0 l) D n with hs
  set A : Set ℂ := p '' Icc 0 1 with hAdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  have hAf : fillH A = fillH (prefixPhysSet κ b jumps (Lf.sspec 0 l) D n) := congrArg fillH hpA
  have hLA : ∀ y : ℝ, (y : ℂ) ∈ A → realMin A ≤ y := fun y hy => ((realBase_facts hp hp0).2.2.1 y hy).1
  set a : ℝ := Lx.leftEntry (stChart s) (realMin A) with ha
  have hv := Lx.isLeftEntryValue_runChart (Lf.sspec 0 l) D hreg n hnot hAc hAf hLA
  have hc' : IsLeftEntryChart A (realMin A) ((stChart s).recenter a) :=
    Lf.isLeftEntryChart_runChart (Lf.sspec 0 l) D hreg n hnot hAc hAf hv
  have hcc : (stChart s).IsConformal :=
    (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) (Lf.sspec 0 l) D n
      fun j _ c θ h => hreg j c θ h).1
  obtain ⟨g, hgc, hgi, hgb, hgt⟩ :=
    Lw.exists_bdryMap_of_hasProperBdryExt hcc (GW1P.isClosed_pieces_run (Lf.sspec 0 l) D hreg n).1
  have hD := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) (Lf.sspec 0 l) D hreg n hnot
  have hgf : ∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite :=
    Lk.finite_fibre_of_pinv (Lk.pinv_schedule le_rfl l D hreg hinj n) hD hgc hgi hgb
  set g' : ℂ → ℂ := fun v => g (v + a) with hg'
  have hsh : ∀ v : ℂ, 0 ≤ v.im → 0 ≤ (v + (a : ℂ)).im := fun v hv => by simpa using hv
  have hg'c : ContinuousOn g' {z | 0 ≤ z.im} :=
    hgc.comp (continuous_id.add continuous_const).continuousOn fun v (hv : 0 ≤ v.im) => hsh v hv
  have hg'i : EqOn g' ((stChart s).recenter a).2.1 H := fun v hv => by
    show g (v + (a : ℂ)) = (stChart s).2.1 (v + (a : ℂ))
    exact hgi ((Lw.add_real_mem_H_iff a).2 hv)
  have hg'f : ∀ z, (g' ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite := fun z => by
    refine ((hgf z).image fun v => v - (a : ℂ)).subset fun v hv => ?_
    refine ⟨v + (a : ℂ), ⟨hv.1, hsh v hv.2⟩, ?_⟩
    simp only [add_sub_cancel_right]
  obtain ⟨tL, γ, htL, hγp, hγ0, hlift, hall⟩ :=
    exists_s3_geometry_of_s2 hp hp0 hpH hβ' hβ'0 hA hc' hg'c hg'i hg'f hη hw hw0 hinjη
  refine ⟨a, g, hc', hgc, hgi, hgt, hgf, tL, γ, htL, hγp, hγ0, hlift, fun a₁ b₁ t ht harc hqζ hqH hag => ?_⟩
  obtain ⟨hpos, hne, hFL, hFJ, hacc, hmo, hsec⟩ := hall a₁ b₁ t ht harc hqζ hqH hag
  have hland : g' (γ t) ∈ A := by
    rw [hlift t]
    exact harc ⟨tL + t, ⟨add_le_add le_rfl ht.1.le, add_le_add le_rfl ht.2.le⟩, rfl⟩
  have him : (γ t).im = 0 := im_eq_zero_of_landing_mem hc'.1 hg'i (hγp.2.2.1 t) hland
  have hγt : γ t + (a : ℂ) = (((γ t).re + a : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  refine ⟨him, hpos, hne, hFL, hFJ, hacc, hmo, hsec, ?_, ?_⟩
  · rw [tendsto_map'_iff, ← hγt]
    have h1 : Tendsto (fun v : ℂ => v + (a : ℂ)) (𝓝[H] (γ t)) (𝓝[H] (γ t + (a : ℂ))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun v hv =>
        (Lw.add_real_mem_H_iff a).2 hv⟩
      exact ((continuous_id.add continuous_const).tendsto (γ t)).mono_left nhdsWithin_le_nhds
    refine h1.congr' (eventually_nhdsWithin_of_forall fun v hv => ?_)
    show v + (a : ℂ) = (stChart s).1 (g (v + (a : ℂ)))
    rw [hgi ((Lw.add_real_mem_H_iff a).2 hv), hD.fwd_inv ((Lw.add_real_mem_H_iff a).2 hv)]
  · have hz : (0 : ℝ) ≤ ((((γ t).re + a : ℝ) : ℂ)).im := by simp
    rw [LuM.bdVal_eq_of_tendsto hz (hgt _ hz), ← hγt]
    exact hlift t

end InteractingSLE.Theorem14.SB.S3.Canon
