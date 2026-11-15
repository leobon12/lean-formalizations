/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCKDisint
import InteractingSLE.Spec.Sec7.Lemma76FChart
import InteractingSLE.Spec.Supplement.Lemma716

/-!
# Lemma G8: the assembly of the disintegration

Packet PROVE-RLC-K. Source: proof of Lemma G8 (supplement pp. 499–501). The reference is Proposition 7.4's complete
ordered pair for the data `−a` on `ℝ₋`, `C` on `ℝ₊` (`a = 2λ + θ₂χ`; `Prop74RefStatement`); the positivity input gives
cutoffs and a positive-probability event of the retained histories on which the pair is ordinary with a good frame
(`G8PositivityStatement`); G7, conditionally on the retained histories (`RetainedPairRestartCondStatement`), gives the
conditional chart pair; Lemma G9 (`G9LiftStatement`) makes the chart prefixes completable pathwise on that event; and
`exists_good_datum` chooses one datum. Its seed germs come from the retained word (RLC-B's
`exists_wordGerm_of_retChart`, the bad-seed exclusion as in RLC-F's `RLCFAvg`), and its untouched height `C` beyond the
junction from the untouched word (`IsUntouchedWord`).

* **`g8DatumStatement_of_parts`**, **`g8FrameStatement_of_parts`** (with Lemma 7.5).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Theorem15D5 Sec2.Assembly Supp7 Supp9D Restart

/-- **`G8DatumStatement` from Proposition 7.4's complete ordered reference, G7 conditionally on the retained
histories, G8's positivity and Lemma G9.** -/
theorem g8DatumStatement_of_parts (href : Sec7.Prop74Order.Prop74RefStatement.{u})
    (hR : RetainedPairRestartCondStatement.{u}) (hPos : G8PositivityStatement.{u}) (hL : G9LiftStatement) :
    G8DatumStatement.{0} := by
  intro κ hκ hκ4 θ₁ θ₂ C ε hθ hε hr₁ hr₂
  have hlam := Sec4.sleLambda_pos hκ
  have hchi := Sec4.chiC_pos hκ hκ4
  have hb1 : -(sleLambda κ + C) / QuantumZipper.chiC κ < θ₁ := by
    have h1 : -2 < (C + θ₁ * QuantumZipper.chiC κ) / sleLambda κ - 1 := hr₁
    have h2 : -1 < (C + θ₁ * QuantumZipper.chiC κ) / sleLambda κ := by linarith
    rw [lt_div_iff₀ hlam] at h2
    rw [div_lt_iff₀ hchi]
    linarith
  have hb2 : θ₂ < (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ + sleLambda κ) / QuantumZipper.chiC κ := by
    rw [lt_div_iff₀ hchi]; linarith
  obtain ⟨Ω, mΩ, P, hP, h, α, β, ζα, ζβ, hh, hα, hβ, hord⟩ :=
    href κ hκ hκ4 (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ) C θ₁ θ₂ hθ hb1 hb2
  have hh' := Sec7.Prop74Order.isGFFWithBoundaryData_coe_singleton hh
  have hbpc := Sec7.isPiecewiseConstant_prop74Data (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ) C
  obtain ⟨u, r, hpos⟩ := hPos κ hκ hκ4 θ₁ θ₂ C hθ hr₁ hr₂ P h hh' α β ζα ζβ hα hβ hord (ε / 2) (half_pos hε)
  obtain ⟨d, hd, hu, hr, hag⟩ := exists_retData_of_isFlowLine hκ hκ4 hα hβ u r
  obtain ⟨B, hBm, hBpos, hBgood⟩ := hpos d hd hu hr hag
  subst hu hr
  obtain ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, βd, X, K, hco, hM, hβd, hX, hK, hlaw, hker, hpath, hcond⟩ :=
    hR κ hκ hκ4 _ _ hbpc 0 0 θ₁ θ₂ le_rfl hθ P h hh' α β ζα ζβ hα hβ d hd hag
  have := hK
  obtain ⟨-, hU₁m, hU₂m, hΓ₁m, hΓ₂m, hΓ₁c, hΓ₂c⟩ := hco
  have hHist : histSigma d ≤ mΩ := by
    refine sup_le ?_ ?_
    · have hm : Measurable (retHistStop d) :=
        (measurable_pi_iff.2 fun t => hd.meas₁ _).prodMk (measurable_pi_iff.2 fun t => hd.meas₂ _)
      exact hm.comap_le
    · refine MeasurableSpace.generateFrom_le ?_
      rintro s hs
      rw [mem_singleton_iff] at hs
      subst hs
      exact hd.measurableSet_G
  have hBm' : MeasurableSet B := hHist _ hBm
  -- (1) the chart position of the first tip is positive
  have F1 : ∀ᵐ ω ∂P, ω ∈ M → 0 < (βd ω).2 :=
    (ae_restrict_iff' hM).1 (ae_of_ae_map hβd.aemeasurable (hker.mono fun c hc => hc.1))
  -- (2) the chart seeds
  have F2 : ∀ᵐ ω ∂P, ω ∈ M → Γ₁ (X ω) 0 = ((βd ω).2 : ℂ) := by
    have hE : MeasurableSet {p : (BoundaryWord × ℝ) × S | Γ₁ p.2 0 = (p.1.2 : ℂ)} :=
      measurableSet_eq_fun ((hΓ₁m 0).comp measurable_snd)
        (Complex.measurable_ofReal.comp (measurable_snd.comp measurable_fst))
    exact ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβd hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE)
      (hker.mono fun c hc => Supp9.ae_apply_zero_of_isFlowLine hc.2.2.1)
  have F3 : ∀ᵐ ω ∂P, ω ∈ M → Γ₂ (X ω) 0 = ((0 : ℝ) : ℂ) := by
    have hE : MeasurableSet {p : (BoundaryWord × ℝ) × S | Γ₂ p.2 0 = ((0 : ℝ) : ℂ)} :=
      measurableSet_eq_fun ((hΓ₂m 0).comp measurable_snd) measurable_const
    exact ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβd hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE)
      (hker.mono fun c hc => Supp9.ae_apply_zero_of_isFlowLine hc.2.2.2)
  -- (3) a wrong side at the first tip kills the first continuation
  have F4 : ∀ᵐ ω ∂P, ω ∈ M → (βd ω ∈ BadSeed κ θ₁ → U₁ (X ω) = 0) := by
    have hE : MeasurableSet {p : (BoundaryWord × ℝ) × S | p.1 ∈ BadSeed κ θ₁ → U₁ p.2 = 0} := by
      have e : {p : (BoundaryWord × ℝ) × S | p.1 ∈ BadSeed κ θ₁ → U₁ p.2 = 0} =
          (Prod.fst ⁻¹' BadSeed κ θ₁)ᶜ ∪ {p | U₁ p.2 = 0} := by
        ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
      rw [e]
      exact ((measurableSet_badSeed κ θ₁).preimage measurable_fst).compl.union
        (measurableSet_eq_fun (hU₁m.comp measurable_snd) measurable_const)
    refine ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβd hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE)
      (hker.mono fun c hc => ?_)
    by_cases hcb : c ∈ BadSeed κ θ₁
    · filter_upwards [ae_eq_zero_of_mem_badSeed hκ hcb hc.2.2.1] with s hs _ using hs
    · exact Eventually.of_forall fun s h' => absurd h' hcb
  -- (4) the chart paths stay in `ℍ̄` before their lifetimes
  have F6 : ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞), (∀ t, Measurable fun x => Γ x t) → Measurable U →
      (∀ᵐ c ∂(P.restrict M).map βd, ∀ᵐ s ∂(K c), ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U s → 0 ≤ (Γ s t).im) →
      ∀ᵐ ω ∂P, ω ∈ M → ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < U (X ω) → 0 ≤ (Γ (X ω) (dyad n k)).im := by
    intro Γ U hΓm hUm hae
    have hE : MeasurableSet {p : (BoundaryWord × ℝ) × S |
        ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < U p.2 → 0 ≤ (Γ p.2 (dyad n k)).im} :=
      measurableSet_setOfPred.mpr (Measurable.forall fun n => Measurable.forall fun k =>
        (measurableSet_setOfPred.mp (measurableSet_lt measurable_const (hUm.comp measurable_snd))).imp
          (measurableSet_setOfPred.mp (measurableSet_le measurable_const
            (Complex.measurable_im.comp ((hΓm (dyad n k)).comp measurable_snd)))))
    exact ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβd hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE)
      (hae.mono fun c hc => hc.mono fun s hs n k hnk => hs _ hnk.le)
  have F6₁ := F6 Γ₁ U₁ hΓ₁m hU₁m (hker.mono fun c hc => Supp7.ae_im_nonneg_of_isFlowLine hc.2.2.1)
  have F6₂ := F6 Γ₂ U₂ hΓ₂m hU₂m (hker.mono fun c hc => Supp7.ae_im_nonneg_of_isFlowLine hc.2.2.2)
  -- the event and the datum property
  set v₀ : BoundaryWord × ℝ → ℝ := fun c => c.2 + ε / 2 * c.2 with hv₀
  set E : Set ((BoundaryWord × ℝ) × S) := {p | ∀ q : ℚ, v₀ p.1 < q →
    RefC q (encC (Γ₁ p.2)) (U₁ p.2) (encC (Γ₂ p.2)) (U₂ p.2)} with hEdef
  have hencm₁ : Measurable fun x : S => encC (Γ₁ x) :=
    measurable_pi_iff.mpr fun n => measurable_pi_iff.mpr fun k => hΓ₁m (dyad n k)
  have hencm₂ : Measurable fun x : S => encC (Γ₂ x) :=
    measurable_pi_iff.mpr fun n => measurable_pi_iff.mpr fun k => hΓ₂m (dyad n k)
  have hEu : LQGMetric.UMeasurableSet E := by
    have hmap : Measurable fun p : (BoundaryWord × ℝ) × S =>
        ((encC (Γ₁ p.2), U₁ p.2), (encC (Γ₂ p.2), U₂ p.2)) :=
      ((hencm₁.comp measurable_snd).prodMk (hU₁m.comp measurable_snd)).prodMk
        ((hencm₂.comp measurable_snd).prodMk (hU₂m.comp measurable_snd))
    have hv : Measurable fun p : (BoundaryWord × ℝ) × S => v₀ p.1 :=
      (measurable_snd.comp measurable_fst).add (measurable_const.mul (measurable_snd.comp measurable_fst))
    exact uMeasurableSet_setOf_forall fun q =>
      uMeasurableSet_setOf_imp (measurableSet_lt hv measurable_const) ((uMeasurableSet_refC q).preimage hmap)
  set Dat : BoundaryWord × ℝ → Prop := fun c => c ∈ HasSeedGerms κ θ₁ θ₂ ∧
    ∀ y : ℝ, v₀ c < y → y ∉ c.1.jumps ∧ c.1.fn y = C with hDat
  -- the rational real points off the first curve (Lemma 7.16)
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < (q : ℝ) → ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζα ω → α ω t ≠ ((q : ℝ) : ℂ) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < (q : ℝ)
    · have hlim : PiecewiseConstantBoundaryData.rightLim
          (Sec7.prop74Data (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ) C) (q : ℝ) = C :=
        Sec4.rightLim_eq_of_forall (a := (q : ℝ) + 1) (by linarith) fun t ht => by
          simp only [Sec7.prop74Data, not_lt.2 (hq.trans ht.1).le, ↓reduceIte]
      filter_upwards [Lemma716.ae_flowLine_ne_right hκ hκ4 hbpc hq (by rw [hlim]; exact hr₁) P h hh' α ζα hα]
        with ω hω _ t ht
      exact hω t ht
    · exact Eventually.of_forall fun ω h' => absurd h' hq
  -- the pathwise facts on the good event
  have key : ∀ᵐ ω ∂P, ω ∈ B → Dat (βd ω) ∧ (βd ω, X ω) ∈ E := by
    filter_upwards [hBgood, hpath, hag, hord, F1, F2, F3, F4, F6₁, F6₂, Sec7.ae_continuousOn_of_isFlowLine hα,
      Sec7.ae_continuousOn_of_isFlowLine hβ, Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hα,
      Supp9.ae_apply_zero_of_isFlowLine hα, Supp9.ae_apply_zero_of_isFlowLine hβ, hrat,
      ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hα,
      ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hβ]
      with ω hBω hpω hagω hordω f1 f2 f3 f4 f6₁ f6₂ k₁ k₂ i₁ z₁ z₂ hratω pg₁ pg₂ hωB
    obtain ⟨hO, hGF⟩ := hBω hωB
    obtain ⟨hζα, hζβ, hcomp⟩ := hordω
    obtain ⟨hMω, -, hk₁, hk₂, hword, huw⟩ := hpω hO
    obtain ⟨hG, ha₁, ha₂⟩ := hagω hO.1 hO.2.1
    have hE := hd.mem_E_of_ordinary hG ha₁ ha₂ hO
    have hg := hd.good ω (RetData.E_subset_G hE)
    obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hE
    have e₁ : EqOn (d.η₁ ω) (α ω) (Icc 0 d.u) := fun s hs => ha₁ s hs.2
    have e₂ : EqOn (d.η₂ ω) (β ω) (Icc 0 d.r) := fun t ht => ha₂ t ht.2
    have htip : d.η₂ ω d.r = β ω d.r := ha₂ d.r le_rfl
    have htip₁ : d.η₁ ω d.u = α ω d.u := ha₁ d.u le_rfl
    obtain ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, hpth₁, hH₁⟩ := id hk₁
    have hc₁0 : c₁ 0 = d.u := clock_zero hO.1.le hmono₁ himg₁
    have h00 : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ₁ := by simp
    have hψW : d.inv ω ((βd ω).2 : ℂ) = α ω d.u := by
      rw [← hc₁0, hpth₁ 0 h00, f2 hMω]
    have hW0 : 0 < (βd ω).2 := f1 hMω
    -- the seed germs of the datum
    have hB : IsClosed (β ω '' Icc 0 d.r) :=
      (isCompact_Icc.image_of_continuousOn (k₂.mono fun t ht =>
        (ENNReal.coe_le_coe.2 ht.2).trans hO.2.1.le)).isClosed
    have hU₁pos : 0 < U₁ (X ω) :=
      lt_of_lt_of_le (pos_of_isClock hO.1 k₁ i₁ hB hO.2.2.2.2.2.1 hmono₁ himg₁) hσ₁
    have hnb : βd ω ∉ BadSeed κ θ₁ := fun hb' => (ne_of_gt hU₁pos) (f4 hMω hb')
    have hi : InjOn (d.η₁ ω) (Icc 0 d.u) :=
      (i₁.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hO.1.le).congr e₁.symm
    have hpH : d.η₂ ω d.r ∈ H := by rw [htip]; exact hO.2.2.2.1
    have hp : d.η₂ ω d.r ∉ d.η₁ ω '' Icc 0 d.u := by rw [htip, e₁.image_eq]; exact hO.2.2.2.2.1
    have hqH : d.η₁ ω d.u ∈ H := by rw [htip₁]; exact hO.2.2.1
    have hq : d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r := by rw [htip₁, e₂.image_eq]; exact hO.2.2.2.2.2.1
    have hψW' : d.inv ω ((βd ω).2 : ℂ) = d.η₁ ω d.u := by rw [htip₁]; exact hψW
    obtain ⟨δ, hδ, h0g, hWg⟩ := exists_wordGerm_of_retChart hC hg.1 hg.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 hpH hp
      hg.2.2.2.2.2.2 hqH hq hi hψW' (isRetainedWord_congr e₁.symm e₂.symm hword)
    have hgerm : βd ω ∈ HasSeedGerms κ θ₁ θ₂ := by
      have := mem_hasSeedGerms_of_wordGerm (θ₂ := θ₂) hW0 hδ h0g hWg (by rwa [Prod.mk.eta])
      rwa [Prod.mk.eta] at this
    -- the untouched height beyond the junction
    have hunt : ∀ y : ℝ, v₀ (βd ω) < y → y ∉ (βd ω).1.jumps ∧ (βd ω).1.fn y = C := by
      intro y hy
      obtain ⟨hy0, hyre, hyA⟩ := hGF _ hψW y hy
      have hre : (d.inv ω y).re ∉ ((({0} : Finset ℝ)) : Set ℝ) := by
        simp only [Finset.coe_singleton, mem_singleton_iff]; exact ne_of_gt hyre
      obtain ⟨hj, hfn⟩ := huw y hy0 hyA hre
      refine ⟨hj, ?_⟩
      rw [hfn]
      simp only [Sec7.prop74Data, not_lt.2 hyre.le, ↓reduceIte]
    refine ⟨⟨hgerm, hunt⟩, ?_⟩
    -- Lemma G9 at this retained pair
    have hO' := hO
    rw [hζα, hζβ] at hO'
    have hC' := (Sec7.Lemma76F.isRetChart_congr ha₁ ha₂).1 hC
    have hk₁' := hk₁
    have hk₂' := hk₂
    rw [hζα] at hk₁'
    rw [hζβ] at hk₂'
    have hz₁ : α ω 0 = 0 := by rw [z₁]; simp
    have hz₂ : β ω 0 = 0 := by rw [z₂]; simp
    have hΓ20 : Γ₂ (X ω) 0 = 0 := by rw [f3 hMω]; simp
    have pg₁' : Restart.IsPathGood (α ω) ⊤ 0 := by rw [← hζα]; exact pg₁
    have pg₂' : Restart.IsPathGood (β ω) ⊤ 0 := by rw [← hζβ]; exact pg₂
    have hφ : ∃ x₀ : ℝ, ∀ z, d.fwd ω z =
        ConformalImage.mapOut (fillH (Restart.prefixSet (α ω) d.u (β ω) d.r)) z - x₀ :=
      ⟨x₀, fun z => by
        show d.g ω z - d.shift ω = _
        rw [hx₀, RetData.g, RetData.K_of_mem hE, prefixSet_congr_Icc e₁ e₂]⟩
    have hRC := hL (α ω) (β ω) d.u d.r (d.fwd ω) (d.inv ω) (d.lift ω) (βd ω).2 (v₀ (βd ω)) (Γ₁ (X ω)) (Γ₂ (X ω))
      (U₁ (X ω)) (U₂ (X ω)) hcomp hz₁ hz₂ pg₁' pg₂'
      (fun q hq ⟨t, ht⟩ => hratω q hq t (by rw [hζα]; exact le_top) ht) hO' hC' hφ hψW hW0
      (fun y hy => hGF _ hψW y hy) hk₁' hk₂' (f2 hMω) hΓ20
      (hΓ₁c (X ω)) (hΓ₂c (X ω)) (mem_Hbar_of_dyad (hΓ₁c (X ω)) (f6₁ hMω)) (mem_Hbar_of_dyad (hΓ₂c (X ω)) (f6₂ hMω))
    intro q hq
    exact (refCompletable_iff (hΓ₁c (X ω)) (hΓ₂c (X ω)) (fun t ht => mem_Hbar_of_dyad (hΓ₁c (X ω)) (f6₁ hMω) t ht)
      (fun t ht => mem_Hbar_of_dyad (hΓ₂c (X ω)) (f6₂ hMω) t ht)).1 (hRC.mono (Ioi_subset_Ioi hq.le))
  have hBM : ∀ᵐ ω ∂P, ω ∈ B → ω ∈ M := by
    filter_upwards [hBgood, hpath] with ω hBω hpω hωB
    exact (hpω (hBω hωB).1).1
  have hlawB := hcond B hBm (hBgood.mono fun ω h hωB => (h hωB).1)
  obtain ⟨c, ⟨hc0, hgff, hfl₁, hfl₂⟩, ⟨hgerm, hunt⟩, hEc⟩ := exists_good_datum hBm' hβd hX hlawB hBM hBpos hker
    (key.mono fun ω h hωB => (h hωB).1) hEu (key.mono fun ω h hωB => (h hωB).2)
  -- the rational junction
  have hv₀c : v₀ c < c.2 + ε * c.2 := by
    simp only [hv₀]; nlinarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hv₀c
  obtain ⟨q₀, q₁, q₂, hSG⟩ := hgerm
  obtain ⟨hδ0, hcol⟩ := seedCollars_of_seedGerm hκ hSG
  have hwq : c.2 < (q : ℝ) := by
    have : c.2 < v₀ c := by simp only [hv₀]; nlinarith
    linarith
  refine ⟨c.1.fn, c.1.jumps, c.2, q, _, hc0, hwq, hq2, hδ0, c.1.isPiecewiseConstantBoundaryData, hcol,
    fun x hx => ⟨(hunt x (hq1.trans hx)).2, (hunt x (hq1.trans hx)).1⟩, S, mS, K c, inferInstance, H₀, Γ₁, Γ₂,
    U₁, U₂, hgff, hfl₁, hfl₂, ?_⟩
  filter_upwards [hEc, Supp7.ae_im_nonneg_of_isFlowLine hfl₁, Supp7.ae_im_nonneg_of_isFlowLine hfl₂]
    with s hs m₁ m₂
  exact (refCompletable_iff (hΓ₁c s) (hΓ₂c s) (fun t ht => m₁ t ht.le) (fun t ht => m₂ t ht.le)).2 (hs q hq1)

/-- **Lemma G8 (with G9)**, `G8FrameStatement`, from Lemma 7.5, Proposition 7.4's complete ordered reference, G7
conditionally on the retained histories, G8's positivity and Lemma G9. -/
theorem g8FrameStatement_of_parts (h75 : Theorem15.Lemma75Statement.{0})
    (href : Sec7.Prop74Order.Prop74RefStatement.{u}) (hR : RetainedPairRestartCondStatement.{u})
    (hPos : G8PositivityStatement.{u}) (hL : G9LiftStatement) : G8FrameStatement.{0} :=
  g8FrameStatement_of_datum h75 (g8DatumStatement_of_parts href hR hPos hL)

end RLC

end InteractingSLE
