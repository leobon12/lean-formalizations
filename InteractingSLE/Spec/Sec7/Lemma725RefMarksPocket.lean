/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefMarksGerm
import InteractingSLE.Spec.Sec7.Lemma725RefWireStop
import InteractingSLE.Spec.Sec7.Lemma725RefDetStrip
import InteractingSLE.Spec.Sec7.PocketPhaseMeans
import InteractingSLE.Spec.Coupling.MartMeans2Lemma71
import InteractingSLE.Spec.Sec7.Lemma71JPocket
import InteractingSLE.WangWu.ReverseContactLocal

/-!
# The pocket-stage union law with the enlarged marks, and `PocketChartFieldStatement` from the walls law

Packet PROVE-LEMMA725REF6. Specification §7.4, Aux. lemmas 124–125 (`source/spec/p385-432.md` L171–L250,
pp. 393–398) and Lemma 7.25's proof (pp. 413–414); rulings R67, R68 (as amended in R69: the walls law keeps the walls'
σ-algebra `𝓦`; only the pocket-stage union law carries the exterior projection).

PROVE-LEMMA725REF5's `pocketChartFieldStatement_of_stop_exteriorDecomp` needs the union law and the exterior
decomposition for **one** σ-algebra that also records the exterior projection. Here that σ-algebra is built from the
walls' σ-algebra `𝓦` alone:

* the decomposition set is `E₀ = ℍ ∖ C` on `A` (`ℍ` off `A`), which is the pocket's union-law set at relative time
  `0` (the hull at `T(0)` misses the pocket: `hgeo` at `q = 0`, the empty hull at time `0`, and `ψ` bijective), and is
  `𝓦`-measurable when the inclusion events `{U ⊆ C}` are walls' events (`hCin`);
* `exists_pocketExteriorDecomp` gives its germ version `h₁`, and the record σ-algebra is
  **`marksSigma 𝓦 h₁ = 𝓦 ∨ σ(h₁)`** (Aux. lemma 124's exterior projection `h_B`, R68);
* the union law at every relative time `q` passes from the marks `𝓦` to `𝓦 ∨ σ(h₁)` by
  `isHistoryAvoidanceLocal_sup_germSigma` (`E₀ ∩ ℍ ⊆` the union-law set at `q`, `σ(h₁) ⊆ 𝒜_{E₀}`);
* the record `(E₀, h₁)` generates `𝓦 ∨ σ(h₁)` up to null sets when `E₀` generates `𝓦` (`hgen`).

## Main results

* `marksSigma`, `extA`, `measurable_extA`;
* **`pocketChartFieldStatement_of_stop_marks`**: REF5's stop-level theorem with the union law at the walls' `𝓦`, no
  decomposition hypothesis, and the walls' record;
* `subset_iff_walls`, `measurableSet_subset_cfPocket`: the pocket-inclusion events of the change pocket are walls'
  events;
* **`pocketChartField_cfPocket_marks`**, **`pocketChartField_cfPocketInf_marks`**: one word-shape event of the strip
  system's change pocket, from STRIPSYS35's walls data at `𝓦`, the walls' record, Proposition 5.13 and the
  continuity of the counterflow (REF4's `pocketChartField_cfPocket` with `PocketHistDet` replaced by its proved
  ingredients).

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefMarks

open PocketTraversal Lemma71C LawUnique PocketStop PocketStopField Lemma725RefChart Lemma725RefSafe PocketCoupling
  Lemma725RefRecovery PocketUnionPt LocalSets WholeField

universe u

/-! ### The record σ-algebra and the decomposition set -/

section Defs

variable {Ω : Type*}

/-- **The pocket's record σ-algebra** `𝓦 ∨ σ(h₁)`: the walls' information and the germ version `h₁` of the exterior
projection (R68). -/
@[instance_reducible]
def marksSigma (𝓦 : MeasurableSpace Ω) (h₁ : Ω → DistOn upperHalfPlaneOpens) : MeasurableSpace Ω :=
  𝓦 ⊔ MeasurableSpace.comap h₁ inferInstance

open Classical in
/-- The pocket's exterior in `ℍ` on `A`, and `ℍ` off `A`. -/
def extA (A : Set Ω) (C : Ω → Set ℂ) (ω : Ω) : Set ℂ := if ω ∈ A then H ∩ (C ω)ᶜ else H

theorem extA_of_mem {A : Set Ω} {C : Ω → Set ℂ} {ω : Ω} (hω : ω ∈ A) : extA A C ω = H ∩ (C ω)ᶜ := by
  simp only [extA, hω, ite_true]

theorem extA_of_notMem {A : Set Ω} {C : Ω → Set ℂ} {ω : Ω} (hω : ω ∉ A) : extA A C ω = H := by
  simp only [extA, hω, ite_false]

/-- The exterior set is hitting-measurable for any σ-algebra containing `A` and the pocket-inclusion events
`{U ⊆ C}` of the open `U ⊆ ℍ`. -/
theorem measurable_extA {𝓦 : MeasurableSpace Ω} {A : Set Ω} (hA : MeasurableSet[𝓦] A) {C : Ω → Set ℂ}
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω}) :
    Measurable[𝓦, hittingSigma] (extA A C) := by
  refine @measurable_generateFrom Ω (Set ℂ) 𝓦 _ _ ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  have e : extA A C ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      (Aᶜ ∩ {_ω | U.Nonempty}) ∪ (A \ {ω | ω ∈ A ∧ U ⊆ C ω}) := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
    by_cases hω : ω ∈ A
    · rw [extA_of_mem hω]
      constructor
      · rintro ⟨z, ⟨-, hzC⟩, hzU⟩
        exact Or.inr ⟨hω, fun h => hzC (h.2 hzU)⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd hω h
        · by_contra hne
          refine h ⟨hω, fun z hzU => ?_⟩
          by_contra hzC
          exact hne ⟨z, ⟨hUH hzU, hzC⟩, hzU⟩
    · rw [extA_of_notMem hω]
      constructor
      · rintro ⟨z, -, hzU⟩
        exact Or.inl ⟨hω, z, hzU⟩
      · rintro (⟨-, z, hzU⟩ | ⟨h, -⟩)
        · exact ⟨z, hUH hzU, hzU⟩
        · exact absurd h hω
  rw [e]
  by_cases hU : U.Nonempty
  · simp only [hU, ofPred_true, inter_univ]
    exact hA.compl.union (hA.diff (hCin U hUo hUH))
  · simp only [hU, ofPred_false, inter_empty, empty_union]
    exact hA.diff (hCin U hUo hUH)

end Defs

/-! ### The stop-level theorem -/

section Stop

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PocketChartFieldStatement κ r_L r_R` from one pocket, with the union law at the walls' σ-algebra and the
decomposition built inside** (Aux. lemma 124 with R68's enlarged record): REF5's
`pocketChartFieldStatement_of_stop_exteriorDecomp` with the union law `hU` at `𝓦`, without the decomposition
hypothesis, the record `E₀` and the erasure `hers` for `𝓦`, and the pocket-inclusion events walls' events (`hCin`).
The record σ-algebra of the conclusion is `marksSigma 𝓦 h₁`. -/
theorem pocketChartFieldStatement_of_stop_marks [StandardBorelSpace Ω] [IsProbabilityMeasure P]
    {κ rL rR : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL) (hρR : ρR 0 = rR)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    (hunb : ∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xL ω))
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xR ω))
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hseedR : ∀ ω ∈ A, xR ω 0 = 0)
    (hxLd : ∀ ω ∈ A, ∀ i : Fin nL, xL ω i.succ < 0) (hxRd : ∀ ω ∈ A, ∀ j : Fin nR, 0 < xR ω j.succ)
    (hxLi : ∀ ω ∈ A, Antitone (xL ω)) (hxRi : ∀ ω ∈ A, Monotone (xR ω))
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω})
    {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) {a : ℝ} (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ ρL ρR P A γ xL xR (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀
      u (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) {η : Ω → ℝ → ℂ}
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    (hers : PocketErasure 𝓦 P A γ xL xR η) :
    PocketChartFieldStatement.{u} κ rL rR := by
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A γ q ≤ mΩ := locPrefixSigma_le h𝓦 hA hγ hγm
  have hlive : ∀ ω ∈ A, ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) := fun ω hω => by
    simpa using PocketPhaseMeans.capLife_pos (hγ ω hω)
  -- the hull at relative time `0` misses the pocket
  have hF0 : ∀ ω ∈ A, Disjoint (F 0 ω) (C ω) := by
    intro ω hω
    have h0 := hgeo 0 ω hω (hlive ω hω)
    have hemp : fwdHull (Ito.rpath (segDriver (γ ω))) 0 = ∅ :=
      Coupling.MartMeans2.fwdHull_rpath_zero (hγ ω hω).segDriver_spec.2.1 (PocketPhaseMeans.capLife_pos (hγ ω hω))
    rw [NNReal.coe_zero, show (fun s : ℝ => segDriver (γ ω) s.toNNReal) = Ito.rpath (segDriver (γ ω)) from rfl,
      hemp, sdiff_empty] at h0
    refine Set.disjoint_right.2 fun z hzC hzF => ?_
    have hz : ψ ω z ∈ ψ ω '' (C ω ∩ (H \ F 0 ω)) := by
      rw [h0]
      exact (hψ ω hω).2.mapsTo hzC
    obtain ⟨w, ⟨hwC, hwF⟩, hw⟩ := hz
    have hwz : w = z := (hψ ω hω).2.injOn hwC hzC hw
    exact hwF.2 (hwz ▸ hzF)
  -- the decomposition set: the union-law set at relative time `0`
  have hE₀eq : liveExt A γ C (F 0) 0 = extA A C := by
    funext ω
    by_cases hω : ω ∈ A
    · rw [liveExt_of_live ⟨hω, hlive ω hω⟩, extA_of_mem hω, extHullSet]
      congr 1
      exact union_eq_left.2 fun z hz => Set.disjoint_left.1 (hF0 ω hω) hz
    · rw [liveExt_of_not_live fun h => hω h.1, extA_of_notMem hω]
  have hE₀m : Measurable[𝓦, hittingSigma] (extA A C) := measurable_extA hA hCin
  obtain ⟨E0, hE0m, hE0loc, hE0eq⟩ := hU 0
  have hloc0 : IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ 0) (extA A C) h₀ P := by
    rw [← hE₀eq]
    exact isHistoryAvoidanceLocal_liveExt (measurableSet_live (𝓦 := 𝓦) A γ 0) hE0loc hE0eq
  have hdiff : ∀ ω ∈ A, H \ extA A C ω = C ω := fun ω hω => by
    rw [extA_of_mem hω]
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff, not_and, not_not]
    exact ⟨fun h => h.2 h.1, fun h => ⟨hCH ω hω h, fun _ => h⟩⟩
  have hAc : ∀ᵐ ω ∂P, extA A C ω ⊆ H ∧ IsOpen (H \ extA A C ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ A
    · refine ⟨by rw [extA_of_mem hω]; exact inter_subset_left, ?_⟩
      rw [hdiff ω hω]
      exact hCo ω hω
    · rw [extA_of_notMem hω, sdiff_self]
      exact ⟨subset_rfl, isOpen_empty⟩
  obtain ⟨h₁, hh₁m, hdecall⟩ := exists_pocketExteriorDecomp hh₀ (hE₀m.mono h𝓦 le_rfl) (hpre 0) hloc0 hAc u
  -- the record σ-algebra `𝓦 ∨ σ(h₁)`
  have hh₁mΩ : Measurable h₁ := hh₁m.mono (germSigma_le (hE₀m.mono h𝓦 le_rfl) hh₀.measurable) le_rfl
  have h𝓦𝓦' : 𝓦 ≤ marksSigma 𝓦 h₁ := le_sup_left
  have hh₁𝓦' : Measurable[marksSigma 𝓦 h₁] h₁ := (comap_measurable h₁).mono le_sup_right le_rfl
  have h𝓦'le : marksSigma 𝓦 h₁ ≤ mΩ := sup_le h𝓦 hh₁mΩ.comap_le
  have hdec : @PocketExteriorDecomp Ω (marksSigma 𝓦 h₁) mΩ P A C
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) :=
    hdecall (marksSigma 𝓦 h₁)
      (sup_le ((le_sup_left : 𝓦 ≤ locPrefixSigma 𝓦 A γ 0).trans le_sup_right) (hh₁m.comap_le.trans le_sup_left))
      (hE₀m.mono h𝓦𝓦' le_rfl) hh₁𝓦' A C fun ω hω => (hdiff ω hω).subset
  -- the union law with the enlarged marks at every relative time
  have hU' : ∀ q : ℝ≥0, PocketStopUnionLaw (marksSigma 𝓦 h₁) P A γ C (F q) h₀ q := by
    intro q
    obtain ⟨Eq, hEqm, hEqloc, hEqeq⟩ := hU q
    have hLq := measurableSet_live (𝓦 := 𝓦) A γ q
    have hlocq := isHistoryAvoidanceLocal_liveExt hLq hEqloc hEqeq
    have hmq := measurable_liveExt (hpre q _ hLq) hEqm hEqeq
    have hsub : ∀ ω, extA A C ω ∩ H ⊆ liveExt A γ C (F q) q ω := by
      intro ω z hz
      by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
      · rw [liveExt_of_live hl]
        rw [extA_of_mem hl.1] at hz
        exact ⟨hz.1.1, Or.inl hz.1.2⟩
      · rw [liveExt_of_not_live hl]
        exact hz.2
    have hME := isHistoryAvoidanceLocal_sup_germSigma hh₀ (hpre q) hmq hlocq
      (hE₀m.mono (le_sup_left : 𝓦 ≤ locPrefixSigma 𝓦 A γ q) le_rfl) hsub
    have hle : locPrefixSigma (marksSigma 𝓦 h₁) A γ q ≤ locPrefixSigma 𝓦 A γ q ⊔ germSigma (extA A C) h₀ := by
      unfold locPrefixSigma marksSigma
      exact sup_le (sup_le (le_sup_left.trans le_sup_left) (hh₁m.comap_le.trans le_sup_right))
        (le_sup_right.trans le_sup_left)
    exact ⟨liveExt A γ C (F q) q, hmq, fun U G hUH hG hd M hM => hME U G hUH hG hd M (hle M hM),
      fun ω hω hq => liveExt_of_live ⟨hω, hq⟩⟩
  -- the record
  have hE₀' : Measurable[marksSigma 𝓦 h₁] fun ω => (E₀ ω, h₁ ω) := (hE₀.mono h𝓦𝓦' le_rfl).prodMk hh₁𝓦'
  have hgen' : marksSigma 𝓦 h₁ ≤
      MeasurableSpace.comap (fun ω => (E₀ ω, h₁ ω)) inferInstance ⊔ Ito.nullSets P := by
    have h1 : MeasurableSpace.comap E₀ inferInstance ≤
        MeasurableSpace.comap (fun ω => (E₀ ω, h₁ ω)) inferInstance :=
      (show Measurable[MeasurableSpace.comap (fun ω => (E₀ ω, h₁ ω)) inferInstance] E₀ from
        measurable_fst.comp (comap_measurable _)).comap_le
    have h2 : MeasurableSpace.comap h₁ inferInstance ≤
        MeasurableSpace.comap (fun ω => (E₀ ω, h₁ ω)) inferInstance :=
      (show Measurable[MeasurableSpace.comap (fun ω => (E₀ ω, h₁ ω)) inferInstance] h₁ from
        measurable_snd.comp (comap_measurable _)).comap_le
    exact sup_le (hgen.trans (sup_le_sup_right h1 _)) (h2.trans le_sup_left)
  have hers' : PocketErasure (marksSigma 𝓦 h₁) P A γ xL xR η := by
    obtain ⟨ε, mε, hSB, E, G, hEm, hG, hae⟩ := hers
    exact ⟨ε, mε, hSB, E, G, hEm.mono h𝓦𝓦' le_rfl, hG, hae⟩
  exact pocketChartFieldStatement_of_stop_exteriorDecomp (𝓦 := marksSigma 𝓦 h₁) hρL hρR hsL hsR h𝓦'le
    (h𝓦𝓦' _ hA) hPA hγ hγm hunb (hxLm.mono (MeasurableSpace.comap_mono h𝓦𝓦') le_rfl)
    (hxRm.mono (MeasurableSpace.comap_mono h𝓦𝓦') le_rfl) hseedL hseedR hxLd hxRd hxLi hxRi hCo hCH hψ
    (fun z => h𝓦𝓦' _ (hCm z)) (fun z => (hψm z).mono h𝓦𝓦' le_rfl) hFo hgeo hh₀ hu hub (hn.mono h𝓦𝓦' le_rfl)
    hU' hside hdec hE₀' hgen' h513 hers'

end Stop

end InteractingSLE.Sec7.Lemma725RefMarks
