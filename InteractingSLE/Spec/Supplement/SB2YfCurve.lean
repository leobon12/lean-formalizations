/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YfTrace
import InteractingSLE.Spec.Supplement.SB2YfSide
import InteractingSLE.Spec.Supplement.SB2BqHull
import InteractingSLE.Spec.Supplement.SB2BqPath

/-!
# The curve half of `IsStageS2`

Packet PROVE-T14-SB2LIFT (round 32; `IsStageS2`). Given the chart package (`SB2YePkg`: the retained path `q` from `0`,
the left entry chart `cr` of `R` at `0` with boundary map `g`) and

* the relative data: a continuous driver `Wr`, `Wr 0 = 0`, with global Loewner trace `ηr`, and a continuous strictly
  increasing clock `τ` on `[0, sB]` from `0` to `u`, with `ηr ∘ τ` in `ℍ̄`;
* B's reflected stage piece: the global trace `η` of the reflected stopped driver, injective on `[0, sB]`, with no real
  arc there, and the link `g (ηr (τ r)) = η r` on `[0, sB]`;

**`stageCurvePkg`** gives the curve fields of `Om.IsStageS2`: `γ = relCurve` (`SB2YfTrace`), `β' = g ∘ γ`, both proper
from `0`; S1 (`subset_closedRightSide_of_arc`); the relative chain with driver `Wr` (`Bq.isSB2RelChain_of_core_bridge`
over `relChainCore_relCurve`) on `[0, sB]`; no real arc of `β'` on `(0, sB + 1)`; `β' = η` on `[0, sB]`, the hull of
the stopped driver at `sB` and `capClock γ sB = u`.
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open scoped NNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.Supp9B

namespace InteractingSLE.Theorem14.SB.Sx

/-- `realMin` of a set containing `0` whose real points are nonnegative is `0`. -/
theorem realMin_eq_zero {A : Set ℂ} (h0 : (0 : ℂ) ∈ A) (hA : ∀ y : ℝ, (y : ℂ) ∈ A → 0 ≤ y) : realMin A = 0 := by
  have hleast : IsLeast {x : ℝ | (x : ℂ) ∈ A} 0 := ⟨by simpa using h0, fun y hy => hA y hy⟩
  exact hleast.csInf_eq

/-- An open set of reals inside `A ∪ {a}`, with `A` of empty interior, is empty. -/
theorem interior_union_singleton_eq_empty {A : Set ℝ} (hA : interior A = ∅) (a : ℝ) :
    interior (A ∪ {a}) = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hsub : ball x ε \ {a} ⊆ A := fun y hy => by
    rcases interior_subset (hball hy.1) with h | h
    · exact h
    · exact absurd h hy.2
  have hopen : IsOpen (ball x ε \ {a}) := isOpen_ball.sdiff isClosed_singleton
  have hnemp : (ball x ε \ {a}).Nonempty := by
    by_cases hxa : x = a
    · refine ⟨x + ε / 2, ?_, ?_⟩
      · rw [mem_ball, Real.dist_eq]; rw [abs_of_pos (by linarith : 0 < x + ε / 2 - x)]; linarith
      · intro h; rw [mem_singleton_iff, ← hxa] at h; linarith
    · exact ⟨x, mem_ball_self hε, hxa⟩
  obtain ⟨y, hy⟩ := hnemp
  have : y ∈ interior A := interior_maximal hsub hopen hy
  rw [hA] at this
  exact this

variable {R : Set ℂ} {cr : Chart} {g : ℂ → ℂ} {q : ℝ → ℂ} {C : ℝ}
  {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {τ : ℝ → ℝ} {sB u : ℝ} {wB : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The curve half of `IsStageS2`** (deterministic, one sample). -/
theorem stageCurvePkg (hqc : ContinuousOn q (Icc 0 1)) (hq0 : q 0 = 0)
    (hqR : ∀ y : ℝ, (y : ℂ) ∈ q '' Icc 0 1 → 0 ≤ y) (hRq : fillH R = fillH (q '' Icc 0 1))
    (hcr : IsLeftEntryChart R 0 cr) (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g cr.2.1 H)
    (hgm : ∀ p ∈ Hbar, g p ∈ Hbar) (hgb : ∀ p ∈ Hbar, ‖g p - p‖ ≤ C)
    {K : ℝ} (hK : 0 ≤ K) (hqg : ∀ s ∈ Icc (0 : ℝ) 1, q s = g ((K * s : ℝ) : ℂ))
    (hreal : ∀ y : ℝ, g y ∈ H → g y ∈ fillH R)
    (hWc : Continuous Wr) (hW0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hsB : 0 < sB) (hu : 0 < u)
    (hτc : ContinuousOn τ (Icc 0 sB)) (hτm : StrictMonoOn τ (Icc 0 sB)) (hτ0 : τ 0 = 0) (hτs : τ sB = u)
    (hηrH : ∀ r ∈ Icc (0 : ℝ) sB, 0 ≤ (ηr (τ r)).im)
    (hη : IsLoewnerTrace (fun r => -wB r) η) (hηinj : InjOn η (Icc 0 sB))
    (hnoarc : interior {r ∈ Ioo (0 : ℝ) sB | (η r).im = 0} = ∅)
    (hlink : ∀ r ∈ Icc (0 : ℝ) sB, g (ηr (τ r)) = η r) :
    ∃ (β' γ : ℝ≥0 → ℂ) (S₀ Sm : ℝ),
      IsProperCurve β' ∧ β' 0 = 0 ∧ q '' Icc 0 1 ⊆ closedRightSide β' ∧
      IsProperCurve γ ∧ γ 0 = 0 ∧ (∀ s, g (γ s) = β' s) ∧
      FinRel.IsSB2RelChain R cr β' γ 0 S₀ Wr ηr ∧ S₀ < Sm ∧
      interior {r ∈ Ioo (0 : ℝ) Sm | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} = ∅ ∧
      sB ∈ Ioc 0 S₀ ∧ fwdHull (fun r => -wB r) sB = fillH (β' '' Icc 0 sB.toNNReal) ∧
      (∀ r ∈ Icc (0 : ℝ) sB, η r = β' r.toNNReal) ∧
      Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) sB = u := by
  set γ := relCurve Wr ηr τ sB u hsB.le with hγdef
  set β' : ℝ≥0 → ℂ := fun s => g (γ s) with hβdef
  have hγc : Continuous γ := continuous_relCurve hsB hWc hW0 hηr hu.le hτc hτm.monotoneOn hτ0
  have hγ0 : γ 0 = 0 := relCurve_zero hsB hηr hτm.monotoneOn hτs hτ0
  have hγle : ∀ s : ℝ≥0, (s : ℝ) ≤ sB → γ s = ηr (τ s) := fun s hs =>
    relCurve_of_le hsB hτm.monotoneOn hτs hs
  have hγgt : ∀ s : ℝ≥0, sB < (s : ℝ) → γ s ∈ H \ fwdHull Wr u := fun s hs => by
    obtain ⟨h1, h2⟩ := relCurve_of_gt hsB hWc hW0 hu.le hτs hs
    show relCurve Wr ηr τ sB u hsB.le s ∈ _
    rw [h1]; exact h2
  have hγH : ∀ s, 0 ≤ (γ s).im := fun s => by
    by_cases hs : (s : ℝ) ≤ sB
    · rw [hγle s hs]; exact hηrH s ⟨NNReal.coe_nonneg s, hs⟩
    · exact le_of_lt (hγgt s (not_le.1 hs)).1
  have hβlink : ∀ s : ℝ≥0, (s : ℝ) ≤ sB → β' s = η s := fun s hs => by
    simp only [hβdef]; rw [hγle s hs]; exact hlink s ⟨NNReal.coe_nonneg s, hs⟩
  have hgH : InjOn g H := fun a ha b hb hab => by
    rw [hgi ha, hgi hb] at hab; exact hcr.1.1.injOn ha hb hab
  have hgdom : ∀ w ∈ H, g w ∈ H \ fillH R := fun w hw => by
    rw [hgi hw]; exact hcr.1.inv_mem hw
  -- `β'` is injective
  have hβinj : Function.Injective β' := by
    have hcross : ∀ s t : ℝ≥0, (s : ℝ) ≤ sB → sB < (t : ℝ) → β' s ≠ β' t := by
      intro s t hs ht he
      have htH := hγgt t ht
      by_cases hsH : γ s ∈ H
      · have hsK : γ s ∈ fwdHull Wr u := by
          rw [hγle s hs] at hsH ⊢
          rw [hηr.2.2 u hu.le]
          have hτsu : τ s ≤ u := hτs ▸ hτm.monotoneOn ⟨NNReal.coe_nonneg s, hs⟩ ⟨hsB.le, le_rfl⟩ hs
          exact mem_fillH_of_mem_closure hsH (subset_closure ⟨τ s, ⟨hτ0 ▸ hτm.monotoneOn ⟨le_rfl, hsB.le⟩
            ⟨NNReal.coe_nonneg s, hs⟩ (NNReal.coe_nonneg s), hτsu⟩, rfl⟩)
        have := hgH hsH htH.1 he
        rw [this] at hsK
        exact htH.2 hsK
      · have hsR : (γ s).im = 0 := le_antisymm (not_lt.1 hsH) (hγH s)
        have hγeq : ((γ s).re : ℂ) = γ s := Complex.ext (by simp) (by simp [hsR])
        have hd : β' t ∈ H \ fillH R := hgdom _ htH.1
        rw [← he] at hd
        have := hreal (γ s).re (by rw [hγeq]; exact hd.1)
        rw [hγeq] at this
        exact hd.2 this
    intro s t he
    by_cases hs : (s : ℝ) ≤ sB <;> by_cases ht : (t : ℝ) ≤ sB
    · rw [hβlink s hs, hβlink t ht] at he
      exact NNReal.coe_injective (hηinj ⟨NNReal.coe_nonneg s, hs⟩ ⟨NNReal.coe_nonneg t, ht⟩ he)
    · exact absurd he (hcross s t hs (not_le.1 ht))
    · exact absurd he.symm (hcross t s ht (not_le.1 hs))
    · have hsH := hγgt s (not_le.1 hs)
      have htH := hγgt t (not_le.1 ht)
      have hγe := hgH hsH.1 htH.1 he
      obtain ⟨e1, -⟩ := relCurve_of_gt hsB hWc hW0 hu.le hτs (not_le.1 hs)
      obtain ⟨e2, -⟩ := relCurve_of_gt hsB hWc hW0 hu.le hτs (not_le.1 ht)
      have hwH : ∀ v : ℝ≥0, sB < (v : ℝ) → (((2 * Real.sqrt ((v : ℝ) - sB) : ℝ) : ℂ) * I) ∈ H := fun v hv => by
        show (0 : ℝ) < ((((2 * Real.sqrt ((v : ℝ) - sB) : ℝ) : ℂ) * I)).im
        simpa using Real.sqrt_pos.2 (sub_pos.2 hv)
      have h3 := QuantumZipper.RS.injOn_fwdMapInv_H hWc hW0 hu.le (hwH s (not_le.1 hs)) (hwH t (not_le.1 ht))
        (by rw [← e1, ← e2]; exact hγe)
      have h4 : Real.sqrt ((s : ℝ) - sB) = Real.sqrt ((t : ℝ) - sB) := by
        have := congrArg Complex.im h3
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one,
          mul_zero, add_zero] at this
        linarith
      have h5 := (Real.sqrt_inj (by linarith [not_le.1 hs]) (by linarith [not_le.1 ht])).1 h4
      exact NNReal.coe_injective (by linarith)
  have hβc : Continuous β' := hgc.comp_continuous hγc hγH
  have hβm : ∀ s, 0 ≤ (β' s).im := fun s => hgm _ (hγH s)
  have hβt : Tendsto (fun s => ‖β' s‖) atTop atTop := by
    refine tendsto_atTop_mono' _ (Eventually.of_forall fun s => ?_)
      (tendsto_atTop_add_const_right _ (-C) (tendsto_norm_relCurve (ηr := ηr) hsB hWc hW0 hu.le hτs))
    have h1 := hgb (γ s) (hγH s)
    have h2 : ‖γ s‖ ≤ ‖β' s‖ + ‖g (γ s) - γ s‖ := by
      calc ‖γ s‖ = ‖g (γ s) - (g (γ s) - γ s)‖ := by ring_nf
        _ ≤ ‖g (γ s)‖ + ‖g (γ s) - γ s‖ := norm_sub_le _ _
    linarith
  have hβP : IsProperCurve β' := ⟨hβc, hβinj, hβm, hβt⟩
  have hγinj : Function.Injective γ := fun s t he => hβinj (by simp only [hβdef, he])
  have hγP : IsProperCurve γ := ⟨hγc, hγinj, hγH, tendsto_norm_relCurve (ηr := ηr) hsB hWc hW0 hu.le hτs⟩
  have hβ0 : β' 0 = 0 := by
    rw [hβlink 0 (by simpa using hsB.le)]; simpa using hη.1
  -- S1 from the relative picture
  have h0q : (0 : ℂ) ∈ q '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, hq0⟩
  have hmin : realMin (q '' Icc 0 1) = 0 := realMin_eq_zero h0q hqR
  have hcq : IsLeftEntryChart (q '' Icc 0 1) (realMin (q '' Icc 0 1)) cr := by
    rw [hmin]; exact (Bq.isLeftEntryChart_congr_fillH hRq).1 hcr
  obtain ⟨N, hN⟩ : ∃ N, ∀ s : ℝ≥0, (s : ℝ) ≤ sB → ‖β' s‖ ≤ N := by
    have hcpt : IsCompact (β' '' Icc 0 sB.toNNReal) := isCompact_Icc.image hβc
    obtain ⟨N, hN⟩ := hcpt.isBounded.exists_norm_le
    refine ⟨N, fun s hs => hN _ ⟨s, ⟨zero_le, ?_⟩, rfl⟩⟩
    exact Real.le_toNNReal_iff_coe_le hsB.le |>.2 hs
  have hfree : ∃ x : ℝ, 0 < x ∧ realMax (q '' Icc 0 1) < x ∧ (x : ℂ) ∉ range β' := by
    refine ⟨max (realMax (q '' Icc 0 1)) (|N|) + 1, by positivity,
      by linarith [le_max_left (realMax (q '' Icc 0 1)) (|N|)], ?_⟩
    rintro ⟨s, hs⟩
    by_cases hsB' : (s : ℝ) ≤ sB
    · have h1 := hN s hsB'
      rw [hs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
      linarith [le_max_right (realMax (q '' Icc 0 1)) (|N|), le_abs_self N]
    · have h2 := (hgdom _ (hγgt s (not_le.1 hsB')).1).1
      have : (0 : ℝ) < (β' s).im := h2
      rw [hs] at this
      simp at this
  have hS1 := subset_closedRightSide_of_arc hK hqg hqc hq0 hβP hβ0 hcq hgc hgi hγP hγ0 (fun s => rfl) hfree
  -- the chain
  have hcore := relChainCore_relCurve hsB hτc hτm hτ0 hτs hWc hW0 hηr
  have hchain : FinRel.IsSB2RelChain R cr β' γ 0 sB Wr ηr :=
    Bq.isSB2RelChain_of_core_bridge hcore hqc hq0 le_rfl hRq hcr.1 hcr.2.2.1 hgc hgi le_rfl
      hβc.continuousOn hβ0 hγc.continuousOn (fun s _ => hγH s) (fun s _ => rfl)
  -- no real arc
  have hnoarc' : interior {r ∈ Ioo (0 : ℝ) (sB + 1) | β' r.toNNReal ∈ {z : ℂ | z.im = 0}} = ∅ := by
    refine eq_empty_of_subset_empty ((interior_mono ?_).trans
      (interior_union_singleton_eq_empty hnoarc sB).subset)
    rintro r ⟨⟨hr0, hr1⟩, hrz⟩
    have hrr : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr0.le
    rcases lt_trichotomy r sB with hlt | heq | hgt
    · refine Or.inl ⟨⟨hr0, hlt⟩, ?_⟩
      have := hβlink r.toNNReal (by rw [hrr]; exact hlt.le)
      rw [this, hrr] at hrz
      exact hrz
    · exact Or.inr heq
    · exfalso
      have h2 := (hgdom _ (hγgt r.toNNReal (by rw [hrr]; exact hgt)).1).1
      have : (0 : ℝ) < (β' r.toNNReal).im := h2
      rw [show (β' r.toNNReal).im = 0 from hrz] at this
      exact lt_irrefl _ this
  refine ⟨β', γ, sB, sB + 1, hβP, hβ0, hS1, hγP, hγ0, fun s => rfl, hchain, by linarith, hnoarc', ⟨hsB, le_rfl⟩,
    ?_, fun r hr => ?_, ?_⟩
  · rw [hη.2.2 sB hsB.le, ← Mn.image_toNNReal_Icc _ hsB.le]
    congr 1
    refine image_congr fun r hr => ?_
    have hrr : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr.1
    rw [hβlink r.toNNReal (by rw [hrr]; exact hr.2), hrr]
  · have hrr : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr.1
    rw [hβlink r.toNNReal (by rw [hrr]; exact hr.2), hrr]
  · rw [capClock_relCurve hsB hτc hτm hτ0 hτs hWc hηr ⟨hsB.le, le_rfl⟩, hτs]

end InteractingSLE.Theorem14.SB.Sx
