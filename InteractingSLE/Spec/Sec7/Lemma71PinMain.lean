/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71PinNull
import InteractingSLE.Spec.Sec7.Lemma71FLift

/-!
# Lemma 7.1's pinned pocket statement

Packet PROVE-LEMMA71S. Specification §7.1, pp. 221–225 (the pocket `C`, its chart `ψ` with "the scale factor
determined by an arbitrary rule" and "the argument lift for `ψ⁻¹` … inherited from the outer-curve height convention"),
supplement §2.3 (the deterministic normalization lemma (2), which pins the inherited branch by the canonical logarithm
of an own prefix of a flank).

`Lemma71F.Lemma71PocketPinStatement` asks for one probability space carrying the pocket data of Lemma 7.1 with every
pathwise clause holding for **every** `ω`. It is proved here on the three-curve space
(`Lemma72B.exists_isThreeCurveSpace`) with

* the canonical wall-pair chart rescaled to modulus one at its base point (`isWallPairChart_scaled`), its pocket
  construction (`Lemma71K.isPocketConstruction_of_wallPairChart`), the inherited branch
  (`Lemma71O.pocketBranchStatement`) and the fixed-time chart clause (`isChartCouplingCharFunConst_of_middleLanding`);
* the pin: `exists_pinData` chooses, measurably in the outer curves, a prefix `β([0, J])` of the left wall and chart
  approaches along which the inherited lift minus `Im log g′` tends to `0` wherever the frame, the branch and the wall
  traces hold (`eventually_tendsto_pin`);
* the segment points `cayleyInv (segPt …)` with the boundary values `tendsto_fwd_cayleyInv`;
* on the null set `N` where the frame, the branch, the traces or the segment clause fail, the default data `C = ℍ`,
  a dilation chart, the empty prefix; the base σ-algebra is `𝓐₀ = σ(β, α) ∨ 𝒩` so that the modified data stay
  measurable, and the clause survives (`isChartCouplingCharFunConst_sup_nullSets`).

* **`lemma71PocketPinStatement_of_middleLanding`**, **`lemma71PocketPinStatement_of_midRealOff`**.

Conditional helpers (on the named inputs of the three-curve space and the geometric half of the middle-curve side
limits; R43/R48: no Theorem 1.2/1.3); they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe v

namespace InteractingSLE.Sec7.Lemma71S

open QuantumZipper (H Hbar chiC fwdHull)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71D Lemma71E Lemma71K Lemma71C MartChar
open Lemma71N (IsPocketFrame IsPocketBranch)

/-! ### The pin data, measurably in the outer curves -/

section PinData

variable {Ω : Type*} [m : MeasurableSpace Ω]

/-- **The pin data of the inherited branch, measurably.** For a random conformal chart `c` with domain `C` (measurable
membership, forward map and lift), a measurable branch shift `n`, a left wall `β` with continuous paths from `0` and
measurable coordinates, and a dense sequence `e`: there are a measurable index `J` and measurable indices `Nz k` of
points of `C` such that the prefixes `β([0, J])` are observed through their dyadic hits, and wherever the pocket frame,
the inherited branch and the generating traces of both walls hold, the points `e (Nz k)` lie off the filled prefix
and the inherited lift minus `Im log g′` of the prefix tends to `0` along them. -/
theorem exists_pinData {C : Ω → Set ℂ} {c : Ω → Chart} (hconf : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ ω, ((c ω).dom : Set ℂ) = C ω) (hCmem : ∀ z, MeasurableSet {ω | z ∈ C ω})
    (hfm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hlm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) {n : Ω → ℤ} (hn : Measurable n)
    {β α : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t) {e : ℕ → ℂ} (he : DenseRange e) :
    ∃ (J : Ω → ℕ) (Nz : ℕ → Ω → ℕ), Measurable J ∧ (∀ k, Measurable (Nz k)) ∧ (∀ k ω, e (Nz k ω) ∈ C ω) ∧
      Restart.IsDyadicHitMeasurable (fun ω => β ω '' Icc 0 (J ω : ℝ≥0)) ∧
      ∀ ω, (∃ (Ψ : ℂ → ℂ) (a' b' : ℝ), IsPocketFrame (β ω) (α ω) (C ω) (c ω) Ψ a' b') →
        IsPocketBranch (β ω) (α ω) (c ω) (n ω) →
        (∃ Wβ : ℝ≥0 → ℝ, IsGeneratingTrace Wβ ⊤ (β ω)) → (∃ Wα : ℝ≥0 → ℝ, IsGeneratingTrace Wα ⊤ (α ω)) →
        (∀ k, e (Nz k ω) ∈ H \ fillH (β ω '' Icc 0 (J ω : ℝ≥0))) ∧
          Tendsto (fun k => (shiftLift (c ω) (n ω)).2.2 (e (Nz k ω)) -
            (Restart.canonDerivLog (fillH (β ω '' Icc 0 (J ω : ℝ≥0))) (e (Nz k ω))).im) atTop (𝓝 0) := by
  classical
  choose Nap hNapm hNapC hNapt using fun j : ℕ =>
    Lemma71O.exists_measurable_chart_approach hconf hdom hCmem hfm he (-(1 / ((j : ℝ) + 1)))
  have hKm : ∀ j : ℕ, Restart.IsDyadicHitMeasurable (fun ω => β ω '' Icc 0 (j : ℝ≥0)) := fun j =>
    Lemma71O.isDyadicHitMeasurable_image_Icc hβc hβm j
  have hKc : ∀ (j : ℕ) ω, IsCompact (β ω '' Icc 0 (j : ℝ≥0)) := fun j ω => isCompact_Icc.image (hβc ω)
  have hKp : ∀ (j : ℕ) ω, IsPreconnected (β ω '' Icc 0 (j : ℝ≥0) ∪ Restart.lowerHalf) := fun j ω =>
    Restart.isPreconnected_image_union_lowerHalf (hβc ω).continuousOn (by rw [hβ0 ω]; simp)
  set F : ℕ → ℕ → Ω → ℂ := fun j i => {ω | e i ∈ H \ fillH (β ω '' Icc 0 (j : ℝ≥0))}.indicator fun ω =>
    Restart.canonDerivLog (fillH (β ω '' Icc 0 (j : ℝ≥0))) (e i) with hFdef
  have hFm : ∀ j i, Measurable (F j i) := fun j i =>
    Restart.measurable_indicator_canonDerivLog (hKm j) (hKc j) (hKp j) (e i)
  have hdomm : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom} := fun z => by
    have e1 : {ω | z ∈ (c ω).dom} = {ω | z ∈ C ω} := by
      ext ω
      show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
      rw [hdom ω]
    rw [e1]
    exact hCmem z
  set X : ℕ → ℕ → Ω → ℝ := fun j k ω =>
    (shiftLift (c ω) (n ω)).2.2 (e (Nap j k ω)) - (F j (Nap j k ω) ω).im with hXdef
  have hXm : ∀ j k, Measurable (X j k) := by
    intro j k
    have h1 := Lemma71O.measurable_comp_index (hFm j) (hNapm j k)
    have h2 := Lemma71E.measurable_at_seq (C := fun ω => ((shiftLift (c ω) (n ω)).dom : Set ℂ))
      (f := fun ω z => (shiftLift (c ω) (n ω)).2.2 z) (hNapm j k)
      (fun ω => by show e _ ∈ ((c ω).dom : Set ℂ); rw [hdom]; exact hNapC j k ω)
      (fun z => Lemma71E.measurable_indicator_shiftLift hn z (hdomm z) (hlm z))
    exact h2.sub (Complex.measurable_im.comp h1)
  set Pr : Ω → ℕ → Prop := fun ω j => Tendsto (fun k => X j k ω) atTop (𝓝 0) ∨
    ∀ i, ¬ Tendsto (fun k => X i k ω) atTop (𝓝 0) with hPrdef
  have hex : ∀ ω, ∃ j, Pr ω j := fun ω => by
    by_cases h : ∃ i, Tendsto (fun k => X i k ω) atTop (𝓝 0)
    · obtain ⟨i, hi⟩ := h
      exact ⟨i, Or.inl hi⟩
    · push Not at h
      exact ⟨0, Or.inr h⟩
  have hPrm : ∀ j, MeasurableSet {ω | Pr ω j} := fun j => by
    have e1 : {ω | Pr ω j} = {ω | Tendsto (fun k => X j k ω) atTop (𝓝 0)} ∪
        ⋂ i, {ω | Tendsto (fun k => X i k ω) atTop (𝓝 0)}ᶜ := by
      ext ω
      simp only [hPrdef, mem_union, mem_iInter, mem_compl_iff, mem_ofPred_eq]
    rw [e1]
    exact (measurableSet_tendsto (𝓝 0) (hXm j)).union
      (MeasurableSet.iInter fun i => (measurableSet_tendsto (𝓝 0) (hXm i)).compl)
  have hJm : Measurable fun ω => Nat.find (hex ω) := measurable_find hex hPrm
  refine ⟨fun ω => Nat.find (hex ω), fun k ω => Nap (Nat.find (hex ω)) k ω, hJm,
    fun k => Lemma71O.measurable_comp_index (fun j => hNapm j k) hJm, fun k ω => hNapC _ k ω, ?_, ?_⟩
  · intro p q
    have e1 : {ω | (Restart.dyadicSquare p q ∩ β ω '' Icc 0 ((Nat.find (hex ω) : ℕ) : ℝ≥0)).Nonempty} =
        ⋃ j : ℕ, {ω | Nat.find (hex ω) = j} ∩ {ω | (Restart.dyadicSquare p q ∩ β ω '' Icc 0 (j : ℝ≥0)).Nonempty} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨j, hj, h⟩ => hj ▸ h⟩
    rw [e1]
    exact MeasurableSet.iUnion fun j => (hJm (measurableSet_singleton j)).inter (hKm j p q)
  · intro ω hFω hbr hβtr hαtr
    obtain ⟨Ψ, a', b', hF⟩ := hFω
    obtain ⟨Wβ, htrβ⟩ := hβtr
    obtain ⟨Wα, htrα⟩ := hαtr
    -- the points of every approach are off every filled prefix
    have hmem : ∀ (j : ℕ) k, e (Nap j k ω) ∈ H \ fillH (β ω '' Icc 0 (j : ℝ≥0)) := fun j k =>
      Lemma71O.dom_subset_H_diff_fillH htrβ hF.hdom (Lemma71O.subset_H_diff_fwdHull_left hF htrβ) j
        (by rw [hF.hdom]; exact hNapC j k ω)
    have hXe : ∀ (j : ℕ) k, X j k ω = (shiftLift (c ω) (n ω)).2.2 (e (Nap j k ω)) -
        (Restart.canonDerivLog (fillH (β ω '' Icc 0 (j : ℝ≥0))) (e (Nap j k ω))).im := fun j k => by
      simp only [hXdef, hFdef]
      rw [indicator_of_mem (show ω ∈ {ω' | e (Nap j k ω) ∈ H \ fillH (β ω' '' Icc 0 (j : ℝ≥0))} from hmem j k)]
    -- the predicate holds at some (all large) `j`
    have hev := eventually_tendsto_pin hF hbr htrβ htrα (z := fun j k => e (Nap j k ω)) (fun j k => hNapC j k ω)
      (fun j => hNapt j ω)
    obtain ⟨j₁, hj₁⟩ := hev.exists
    have hX₁ : Tendsto (fun k => X j₁ k ω) atTop (𝓝 0) := hj₁.2.congr fun k => (hXe j₁ k).symm
    have hspec : Pr ω (Nat.find (hex ω)) := Nat.find_spec (hex ω)
    have hX : Tendsto (fun k => X (Nat.find (hex ω)) k ω) atTop (𝓝 0) := by
      rcases hspec with h | h
      · exact h
      · exact absurd hX₁ (h j₁)
    exact ⟨fun k => hmem _ k, hX.congr fun k => hXe _ k⟩

end PinData

/-! ### The pinned pocket statement -/

/-- **The pathwise good event of the pin construction**: the pocket frame with the segment clause of the mapped
segment, the inherited branch, and generating traces of both walls. -/
def PinGood (β α γ : ℝ≥0 → ℂ) (C : Set ℂ) (c : Chart) (n : ℤ) (γ' : ℝ → ℂ) : Prop :=
  (∃ (Ψ : ℂ → ℂ) (a' b' : ℝ), IsPocketFrame β α C c Ψ a' b' ∧
    ∀ u, 0 ≤ u → segPt γ (closure (cayley '' C)) u ∈ closure (cayley '' C) \ {wallPt α b'} ∧
      γ' u = Ψ (segPt γ (closure (cayley '' C)) u)) ∧
    IsPocketBranch β α c n ∧ (∃ Wβ : ℝ≥0 → ℝ, IsGeneratingTrace Wβ ⊤ β) ∧ ∃ Wα : ℝ≥0 → ℝ, IsGeneratingTrace Wα ⊤ α

theorem measurable_cayleyInv : Measurable cayleyInv := by
  unfold QuantumZipper.CA.cayleyInv
  fun_prop

/-- **`Lemma71F.Lemma71PocketPinStatement` (Lemma 7.1's three-curve pocket data with the inherited branch pinned by
the normalization lemma)** from the named inputs of the three-curve space (the §4.2 reference, Proposition 5.5 in `ℍ`,
Lemma 6.13's (MD1) exclusion) and the geometric half of the middle-curve side limits
(`Lemma71Q.MiddleLandingStatement`). Conditional helper. -/
theorem lemma71PocketPinStatement_of_middleLanding (href : Lemma71H.Cond44ReferenceStatement.{v})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{v}) (hMD : Lemma71I.Lemma613ContactStatement.{v})
    (hL : Lemma71Q.MiddleLandingStatement.{v}) : Lemma71F.Lemma71PocketPinStatement.{v} := by
  intro κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  classical
  -- the three-curve space, the rescaled wall-pair chart, the construction, the branch and the clause
  obtain ⟨Ω, mΩ, P, hP, h, u₀, β, α, γ, ζβ, ζα, ζγ, hS⟩ :=
    Lemma72B.exists_isThreeCurveSpace href h55 hMD hκ hκ4 hθ₁ hθ₂ le_rfl le_rfl
  obtain ⟨e, Cw, Np, Nx, Ny, cw, hW⟩ := exists_isWallPairChart
  have hW' := isWallPairChart_scaled hW
  obtain ⟨γ', hpc⟩ := isPocketConstruction_of_wallPairChart hW' hS
  obtain ⟨n, hn, hN⟩ := Lemma71O.pocketBranchStatement κ hκ hκ4 θ₁ θ₂ _ _ hθ₁ hθ₂ le_rfl le_rfl P h u₀ β α γ
    ζβ ζα ζγ hS _ _ γ' hpc
  have hcf := isChartCouplingCharFunConst_of_middleLanding href hL hκ hκ4 hθ₁ hθ₂ le_rfl le_rfl hS hpc hn hN
  -- the components
  have hS' := hS
  obtain ⟨hGFF, -, -, hβfl, hαfl, -, hβ62, hα62, hγ62, hae⟩ := hS'
  have hh : Measurable h := hGFF.1
  have hβm : Measurable β := measurable_pi_iff.2 hβ62.2.2.2.1
  have hαm : Measurable α := measurable_pi_iff.2 hα62.2.2.2.1
  have hγm : Measurable γ := measurable_pi_iff.2 hγ62.2.2.2.1
  have h₀ : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ mΩ := (hβm.prodMk hαm).comap_le
  have hpc' := hpc
  obtain ⟨hC, hCm, hconf, hdom, hfm, hlm, -, hLd, hbetw, hfr, hseg, hγ'm, hmark⟩ := hpc'
  have hW'' := hW'
  obtain ⟨he, hNp, hNx, hNy, -, -, hNpC, hNxC, hNyC, -, -, -, -, -, -, -, -, hnorm, -, -⟩ := hW''
  have hπ : ∀ ω, Continuous (β ω) ∧ Continuous (α ω) ∧ β ω 0 = 0 ∧ α ω 0 = 0 := fun ω =>
    ⟨hβ62.1 ω, hα62.1 ω, hβ62.2.1 ω, hα62.2.1 ω⟩
  have hπm := measurable_toWallPair hπ
  have h𝓑 : MeasurableSpace.comap β MeasurableSpace.pi ⊔ MeasurableSpace.comap α MeasurableSpace.pi ⊔
      MeasurableSpace.comap γ MeasurableSpace.pi ⊔ Ito.nullSets P ≤ mΩ :=
    sup_le (sup_le (sup_le hβm.comap_le hαm.comap_le) hγm.comap_le) (Ito.nullSets_le P)
  have hγ'mΩ : ∀ u, Measurable fun ω => γ' ω u := fun u => (hγ'm u).mono h𝓑 le_rfl
  have hpm : ∀ r n k, MeasurableSet (prefixEvent γ' r n k) := fun r n k =>
    measurableSet_prefixEvent hseg (fun u _ => hγ'mΩ u) r n k
  have hCmem₀ : ∀ z, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | z ∈ Cw (toWallPair (β ω) (α ω))} := fun z =>
    @Lemma71E.measurableSet_mem_of_closedBall Ω (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) _
      (fun ω => (hC ω).1) hCm z
  have hβm₀ : ∀ t, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] fun ω => β ω t :=
    fun t => (measurable_pi_apply t).comp (measurable_fst.comp (comap_measurable (fun ω => (β ω, α ω))))
  -- the pin data
  obtain ⟨J, Nz', hJm, hNz'm, hNz'C, hKm, hpin⟩ :=
    exists_pinData (m := MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) (α := α) hconf hdom hCmem₀
      hfm hlm hn hβ62.1 hβ62.2.1 hβm₀ he
  -- the good event and the null set
  have hgood : ∀ᵐ ω ∂P, PinGood (β ω) (α ω) (γ ω) (Cw (toWallPair (β ω) (α ω)))
      (scaledChart e Np cw (toWallPair (β ω) (α ω))) (n ω) (γ' ω) := by
    filter_upwards [hae, hbetw, hfr, hmark, hN,
      Lemma71P.ae_exists_isGeneratingTrace hβfl (hae.mono fun ω hω => hω.1),
      Lemma71P.ae_exists_isGeneratingTrace hαfl (hae.mono fun ω hω => hω.2.1)] with ω hω hbω hfrω hmω hNω htrβ htrα
    obtain ⟨-, -, -, -, -, -, hβα, hsβ, hsα, -⟩ := hω
    obtain ⟨a', b', Ψ, hM, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq, hsegω, -⟩ := hmω
    exact ⟨⟨Ψ, a', b', ⟨hsβ, hsα, hβα, hbω, hM, hconf ω, hdom ω, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq, hfrω⟩, hsegω⟩,
      hNω, htrβ, htrα⟩
  set N : Set Ω := toMeasurable P {ω | ¬ PinGood (β ω) (α ω) (γ ω) (Cw (toWallPair (β ω) (α ω)))
    (scaledChart e Np cw (toWallPair (β ω) (α ω))) (n ω) (γ' ω)} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable P _
  have hNP : P N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 hgood
  have hgoodN : ∀ ω, ω ∉ N → PinGood (β ω) (α ω) (γ ω) (Cw (toWallPair (β ω) (α ω)))
      (scaledChart e Np cw (toWallPair (β ω) (α ω))) (n ω) (γ' ω) := fun ω hω => by
    by_contra hng
    exact hω (subset_toMeasurable P _ hng)
  have hN𝓐 : MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ⊔ Ito.nullSets P] N :=
    (le_sup_right : Ito.nullSets P ≤ _) _ (MeasurableSpace.measurableSet_generateFrom ⟨hNm, hNP⟩)
  have hle𝓐 : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤
      MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ⊔ Ito.nullSets P := le_sup_left
  -- the default data on `N`
  obtain ⟨Nx₀, hNx₀H, hNx₀t⟩ := exists_index_seq_zero he
  obtain ⟨Ny₀, hNy₀H, hNy₀t⟩ := exists_index_seq_infty he
  have hIH : Complex.I ∈ H := by
    show (0 : ℝ) < Complex.I.im
    rw [Complex.I_im]
    exact one_pos
  obtain ⟨Nb₀, hNb₀H, -⟩ := exists_index_near he hIH one_pos
  have hb0 : e Nb₀ ≠ 0 := fun h0 => by
    have h1 : (0 : ℝ) < (e Nb₀).im := hNb₀H
    rw [h0, Complex.zero_im] at h1
    exact lt_irrefl _ h1
  set r₀ : ℝ := ‖e Nb₀‖⁻¹ with hr₀def
  have hr₀ : 0 < r₀ := inv_pos.2 (norm_pos_iff.2 hb0)
  have hHpre : IsPreconnected H :=
    (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected
  -- the pinned pocket data
  refine ⟨Ω, mΩ, P, hP, MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ⊔ Ito.nullSets P,
    fun ω => if ω ∈ N then H else Cw (toWallPair (β ω) (α ω)), e,
    fun m ω => if ω ∈ N then Nx₀ m else Nx m (toWallPair (β ω) (α ω)),
    fun m ω => if ω ∈ N then Ny₀ m else Ny m (toWallPair (β ω) (α ω)),
    fun ω => if ω ∈ N then Nb₀ else Np (toWallPair (β ω) (α ω)),
    fun ω u => if ω ∈ N then γ' ω u / (r₀ : ℂ) else
      cayleyInv (segPt (γ ω) (closure (cayley '' Cw (toWallPair (β ω) (α ω)))) u), γ', h,
    fun ω => if ω ∈ N then Chart.dilation r₀ else shiftLift (scaledChart e Np cw (toWallPair (β ω) (α ω))) (n ω),
    0, chiC κ, sup_le h₀ (Ito.nullSets_le P), he, fun ω => ?_, fun z r => ?_,
    fun m => Measurable.ite hN𝓐 measurable_const (((hNx m).comp hπm).mono hle𝓐 le_rfl),
    fun m => Measurable.ite hN𝓐 measurable_const (((hNy m).comp hπm).mono hle𝓐 le_rfl),
    Measurable.ite hN𝓐 measurable_const ((hNp.comp hπm).mono hle𝓐 le_rfl), fun m ω => ?_, fun m ω => ?_,
    fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_, ?_, hseg, fun u _ => ?_,
    fun ω u hu => ?_, hh, ?_⟩
  -- the pocket
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      exact ⟨QuantumZipper.isOpen_H, ⟨⟨Complex.I, hIH⟩, hHpre⟩, isSimplyConnected_H, subset_rfl⟩
    · simp only [hω, ↓reduceIte]
      exact hC ω
  · have key : MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ⊔ Ito.nullSets P]
        ((N ∩ {_ω | closedBall z r ⊆ H}) ∪ (Nᶜ ∩ {ω | closedBall z r ⊆ Cw (toWallPair (β ω) (α ω))})) :=
      (hN𝓐.inter (MeasurableSet.const _)).union (hN𝓐.compl.inter (hle𝓐 _ (hCm z r)))
    convert key using 1
    ext ω
    by_cases hω : ω ∈ N <;> simp [hω]
  -- the approach sequences and the base point
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      exact hNx₀H m
    · simp only [hω, ↓reduceIte]
      exact hNxC m _
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      exact hNy₀H m
    · simp only [hω, ↓reduceIte]
      exact hNyC m _
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      exact hNb₀H
    · simp only [hω, ↓reduceIte]
      exact hNpC _
  -- the chart
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      exact Chart.isConformal_dilation hr₀
    · simp only [hω, ↓reduceIte]
      exact isConformal_shiftLift (hconf ω) (n ω)
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      rw [(Chart.isConformal_dilation hr₀).coe_dom, Chart.dilation_image_H hr₀]
    · simp only [hω, ↓reduceIte]
      exact hdom ω
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · have := hNx₀t.const_mul (r₀ : ℂ)
        rw [mul_zero] at this
        exact this
      · refine (hNy₀t.const_mul_atTop hr₀).congr fun m => ?_
        show r₀ * ‖e (Ny₀ m)‖ = ‖(r₀ : ℂ) * e (Ny₀ m)‖
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀]
    · simp only [hω, ↓reduceIte]
      exact hnorm _
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      show ‖(r₀ : ℂ) * e Nb₀‖ = 1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀, hr₀def,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hb0)]
    · simp only [hω, ↓reduceIte]
      exact norm_scaledChart_base hW _
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      refine ⟨fun _ => ((Real.log r₀ : ℝ) : ℂ), isDerivLog_dilation hr₀ H, fun z _ => ?_⟩
      show (0 : ℝ) = (((Real.log r₀ : ℝ) : ℂ)).im
      rw [Complex.ofReal_im]
    · simp only [hω, ↓reduceIte]
      obtain ⟨L, hL1, hL2⟩ := hLd ω
      refine ⟨fun z => L z + ((2 * π * (n ω : ℝ) : ℝ) : ℂ) * Complex.I, ⟨hL1.1.add_const _, fun z hz => ?_⟩,
        fun z hz => ?_⟩
      · have h2π : Complex.exp (((2 * π * (n ω : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
          have e2 : (((2 * π * (n ω : ℝ) : ℝ) : ℂ) * Complex.I) = (n ω : ℂ) * (2 * π * Complex.I) := by
            push_cast
            ring
          rw [e2, Complex.exp_int_mul_two_pi_mul_I]
        rw [Complex.exp_add, h2π, mul_one]
        exact hL1.2 z hz
      · show (scaledChart e Np cw (toWallPair (β ω) (α ω))).2.2 z + 2 * Real.pi * (n ω : ℝ) =
          (L z + ((2 * π * (n ω : ℝ) : ℝ) : ℂ) * Complex.I).im
        rw [hL2 z hz, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
          Complex.I_re, mul_one, zero_mul, add_zero]
  -- the pin
  · refine ⟨fun ω => if ω ∈ N then ∅ else β ω '' Icc 0 (J ω : ℝ≥0), fun k ω => if ω ∈ N then Nb₀ else Nz' k ω,
      fun p q => ?_, fun ω => ?_, fun ω => ?_,
      fun k => Measurable.ite hN𝓐 measurable_const ((hNz'm k).mono hle𝓐 le_rfl), fun k ω => ?_, fun k ω => ?_,
      fun ω => ?_⟩
    · have key : MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ⊔ Ito.nullSets P]
          (Nᶜ ∩ {ω | (Restart.dyadicSquare p q ∩ β ω '' Icc 0 (J ω : ℝ≥0)).Nonempty}) :=
        hN𝓐.compl.inter (hle𝓐 _ (hKm p q))
      convert key using 1
      ext ω
      by_cases hω : ω ∈ N <;> simp [hω]
    · by_cases hω : ω ∈ N
      · simp only [hω, ↓reduceIte]
        exact isCompact_empty
      · simp only [hω, ↓reduceIte]
        exact isCompact_Icc.image (hβ62.1 ω)
    · by_cases hω : ω ∈ N
      · simp only [hω, ↓reduceIte]
        rw [empty_union]
        exact (convex_halfSpace_le (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected
      · simp only [hω, ↓reduceIte]
        exact Restart.isPreconnected_image_union_lowerHalf (hβ62.1 ω).continuousOn (by rw [hβ62.2.1 ω]; simp)
    · by_cases hω : ω ∈ N
      · simp only [hω, ↓reduceIte]
        exact hNb₀H
      · simp only [hω, ↓reduceIte]
        exact hNz'C k ω
    · by_cases hω : ω ∈ N
      · simp only [hω, ↓reduceIte]
        rw [fillH_empty, sdiff_empty]
        exact hNb₀H
      · simp only [hω, ↓reduceIte]
        obtain ⟨⟨Ψ, a', b', hF, -⟩, hbr, htrβ, htrα⟩ := hgoodN ω hω
        exact (hpin ω ⟨Ψ, a', b', hF⟩ hbr htrβ htrα).1 k
    · by_cases hω : ω ∈ N
      · simp only [hω, ↓reduceIte]
        have h1 : (Restart.canonDerivLog (fillH (∅ : Set ℂ)) (e Nb₀)).im = 0 := by
          rw [fillH_empty, canonDerivLog_empty_eqOn hNb₀H, Pi.zero_apply, Complex.zero_im]
        have h2 : (Chart.dilation r₀).2.2 (e Nb₀) = 0 := rfl
        simp only [h1, h2, sub_zero]
        exact tendsto_const_nhds
      · simp only [hω, ↓reduceIte]
        obtain ⟨⟨Ψ, a', b', hF, -⟩, hbr, htrβ, htrα⟩ := hgoodN ω hω
        exact (hpin ω ⟨Ψ, a', b', hF⟩ hbr htrβ htrα).2
  -- the segment points
  · exact Measurable.ite hNm ((hγ'mΩ u).div_const _) (measurable_cayleyInv.comp
      (measurable_segPt (fun ω => (hC ω).1) (fun ω => (hC ω).2.2.2) (fun z => h₀ _ (hCmem₀ z)) he hγ62.1
        hγ62.2.2.2.1 u))
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [closure_H]
        show 0 ≤ (γ' ω u / (r₀ : ℂ)).im
        rw [Complex.div_ofReal_im]
        exact div_nonneg ((hseg ω).2.2.1 hu) hr₀.le
      · have hcont : Tendsto (fun z => (r₀ : ℂ) * z) (𝓝 (γ' ω u / (r₀ : ℂ)))
            (𝓝 ((r₀ : ℂ) * (γ' ω u / (r₀ : ℂ)))) := (continuous_const.mul continuous_id).tendsto _
        rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 hr₀.ne')] at hcont
        exact hcont.mono_left nhdsWithin_le_nhds
    · simp only [hω, ↓reduceIte]
      obtain ⟨⟨Ψ, a', b', hF, hsg⟩, -, -, -⟩ := hgoodN ω hω
      obtain ⟨hp, hγ'eq⟩ := hsg u hu
      have hp1 : segPt (γ ω) (closure (cayley '' Cw (toWallPair (β ω) (α ω)))) u ≠ 1 := fun h1 =>
        hF.one_notMem (h1 ▸ hp)
      have hCS : cayley '' Cw (toWallPair (β ω) (α ω)) ⊆
          closure (cayley '' Cw (toWallPair (β ω) (α ω))) \ {wallPt (α ω) b'} := fun x hx =>
        ⟨subset_closure hx, fun hb => hF.closePt_notMem (mem_singleton_iff.1 hb ▸ hx)⟩
      have key := tendsto_fwd_cayleyInv hF.subset_H hF.hΨe hCS (hF.hΨc _ hp) hp1 hp.1
      rw [← hγ'eq] at key
      exact key
  -- the clause
  · have hcc : ∀ᵐ ω ∂P, (if ω ∈ N then Chart.dilation r₀ else
        shiftLift (scaledChart e Np cw (toWallPair (β ω) (α ω))) (n ω)) =
          shiftLift (scaledChart e Np cw (toWallPair (β ω) (α ω))) (n ω) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hNP] with ω hω
      simp only [hω, ↓reduceIte]
    exact isChartCouplingCharFunConst_sup_nullSets h₀ hpm hh hcc hcf

/-- **`Lemma71F.Lemma71PocketPinStatement`** from the named inputs of the three-curve space and PROVE-LEMMA71P's
deterministic `Lemma71P.MidRealOffStatement` (`Lemma71P.middleLandingStatement_of_midRealOff`). Conditional helper. -/
theorem lemma71PocketPinStatement_of_midRealOff (href : Lemma71H.Cond44ReferenceStatement.{v})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{v}) (hMD : Lemma71I.Lemma613ContactStatement.{v})
    (hoff : Lemma71P.MidRealOffStatement) : Lemma71F.Lemma71PocketPinStatement.{v} :=
  lemma71PocketPinStatement_of_middleLanding href h55 hMD (Lemma71P.middleLandingStatement_of_midRealOff hoff)

end InteractingSLE.Sec7.Lemma71S
