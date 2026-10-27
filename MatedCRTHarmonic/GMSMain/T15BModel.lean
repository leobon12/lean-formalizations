import MatedCRTHarmonic.GMSMain.T15BWiring
import MatedCRTHarmonic.GMSMain.T15CTheorem39
import MatedCRTHarmonic.GMSMain.T15AModel
import MatedCRTHarmonic.BundleSec4.MesoModelFinal
import MatedCRTHarmonic.RouteM.BPointConnected
import MatedCRTHarmonic.MoTInput.CurveAdapters
import MatedCRTHarmonic.GMSMain.EpsALemma27
import MatedCRTHarmonic.GMSLemma27.Consumers
import MatedCRTHarmonic.MoTInput.Segments
import MatedCRTHarmonic.MoTInput.AreaDominates
import MatedCRTHarmonic.GMCFacts.LowerTail
import MatedCRTHarmonic.Implementation.MatedCRTGraphConnected

/-!
# [18] Theorem 1.5 for the embedded mated-CRT map of every frozen coupling

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18],
Theorem 1.5, display (1.9), for a mating-of-trees coupling: stated for every frozen
coupling `D : MatedCRT.IsMatingOfTreesCoupling γ P …` with `γ ∈ (0, 2)` on a standard Borel space.

* **`theorem15_family_of_coupling`** (dyadic meshes `ε = 2⁻ᵏ`, **no premise**): on the bundle's mesh family (`(MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family`: the mated-CRT multigraphs at
  mesh `2⁻ᵏ` of the repaired path `bundleBM` with the cells `bundleCurve([2⁻ᵏ(x − 1), 2⁻ᵏx])`, a.s. equal to the
  bundle's `bm`, `η`), with `η(x) = bundleCurve(2⁻ᵏx)`. Inputs: the `lemma311Bad_of_coupling_all`
  ((3.35) at `ρ' = (1 + ρ)/2`), (LC), (3.31′), and Lemma 2.7.
* **`theorem15_coupling_real_core`**, **`theorem15_coupling_real`** (every real `ε ∈ (0, 1)`; on the
  bundle's own `G^ε = MatedCRT.graph ε (bm ω) h` and cells `η([ε(x − 1), εx])`, `η(x) = η(εx)`, the setting of the
  draft anchor `matedCRT_holder_of_matingOfTrees`): conditional on ONE named input, [18] (3.35) at real `ε` in T15A's
  shape (`T15A.Lemma311Holds`). The other inputs are landed: the real-mesh Lemma 2.7
  (`epsA_lemma27_coupling`), the bundle's Peanosphere (`MoTInput.ae_peanosphere`) for (LC) (TF2's Theorem B), and
  T15C's (3.31′) on the same good event. `theorem15_coupling_real` has the draft anchor's binder order and hypotheses
  (`α` before `ρ` when the input's `α` is uniform in `ρ`; `IsConnected D`, `IsConnected Dᶜ`; `HolderOnWith`);
  `theorem15_coupling_real_perRho` is the variant for an input whose `α` depends on `ρ`.

The good events assert (1.9) for EVERY discrete harmonic extension `g` of the (1.6) data (T15B's
`IsHarmonicExtension`, `sSup` form; the draft's `IsLUB` form implies it); existence of `g` is T16D's
(`T16D.ae_harmonicExtension`). Interior estimate (3.30′): `interior_estimate`; boundary estimate (3.31′): T15C.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.T15B

open MatedCRTHarmonic

/-! ### Lemma 2.7's exponent -/

/-- The parameter `q = 1/(2 + γ)²` of Lemma 2.7 used here (`q < 2/(2 + γ)²`, `q ≤ 1`). -/
def lemma27Param (γ : ℝ) : ℝ := 1 / (2 + γ) ^ 2

/-- The rate `α₂ = α(q, γ)/2` of Lemma 2.7 at `q = lemma27Param γ`. -/
def lemma27Rate (γ : ℝ) : ℝ := GMSLemma27.lemma27Exponent (lemma27Param γ) γ / 2

theorem lemma27Param_facts {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    0 < lemma27Param γ ∧ lemma27Param γ < 2 / (2 + γ) ^ 2 ∧ lemma27Param γ ≤ 1 := by
  have h2 : (0 : ℝ) < 2 + γ := by linarith [hγ.1]
  have hden : 4 < (2 + γ) ^ 2 := by nlinarith [hγ.1]
  refine ⟨by unfold lemma27Param; positivity, ?_, ?_⟩
  · unfold lemma27Param
    exact div_lt_div_of_pos_right (by norm_num) (by positivity)
  · unfold lemma27Param
    rw [div_le_one (by positivity)]
    linarith

theorem lemma27Rate_pos {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) : 0 < lemma27Rate γ := by
  obtain ⟨hq0, hq', -⟩ := lemma27Param_facts hγ
  have := GMSLemma27.lemma27Exponent_pos hγ.1 hq0 hq'
  unfold lemma27Rate
  linarith

theorem lemma27Rate_lt {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    lemma27Rate γ < GMSLemma27.lemma27Exponent (lemma27Param γ) γ := by
  have := lemma27Rate_pos hγ
  unfold lemma27Rate at this ⊢
  linarith

/-! ### Dyadic meshes: the bundle's mesh family -/

section Dyadic

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

end Dyadic

/-! ### Every real mesh `ε ∈ (0, 1)`: the bundle's own `G^ε`, conditional on (3.35) at real `ε` -/

section Real

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] (3.35) at a real mesh `ε` for a frozen coupling** (the named input of the real-`ε` Theorem 1.5): the event that `G^ε` is locally finite, its cells `η([ε(x − 1), εx])` form a cellular embedding `H`, and
(3.35) holds on `H` at ambient radius `ρ'` with constants `β, p`. -/
def Lemma311GoodAt (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ)) (ε ρ' β p : ℝ) : Set Ω :=
  {ω | ∃ h : MatedCRT.IsLocallyFinite ε (bm ω), ∃ H : CellularEmbedding (MatedCRT.graph ε (bm ω) h) 0,
    H.cell = (fun x : ℤ => η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧ T15A.Lemma311Holds H ε ρ' β p}

/-- The bad event of (1.9) at a real mesh `ε` on the bundle's own `G^ε` (every discrete harmonic extension;
existence of one is T16D's `ae_harmonicExtension`). -/
def HolderBadAt (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ)) (Dom : Set ℂ) (f : ℂ → ℝ) (A₀ ξ ε : ℝ) : Set Ω :=
  {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω), ∀ g : ℤ → ℝ,
    IsHarmonicExtension (MatedCRT.graph ε (bm ω) h)
      (fun x : ℤ => η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) Dom f g →
    ∀ x ∈ verticesMeeting (fun x : ℤ => η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) Dom,
    ∀ y ∈ verticesMeeting (fun x : ℤ => η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) Dom,
      |g x - g y| ≤ A₀ * max ε (dist (η ω (ε * x)) (η ω (ε * y))) ^ ξ}

/-- **[18] Theorem 1.5 at every real mesh, core form** (fixed `ρ < ρ' < 1`). If (3.35) at ambient
radius `ρ'` (`Lemma311GoodAt`) fails with probability `≤ C₁ ε^{α₁}` at every `ε ∈ (0, 1)`, then for every `χ > 0`
there is `ξ > 0` such that for every open `Dom ⊆ B_ρ(0)` with `ℂ \ Dom` preconnected and every `f` that is `χ`-Hölder
on `∂Dom` there are `A₀ > 0` and `C` with `P[HolderBadAt … ε] ≤ C ε^{min α₁ α₂}` for every `ε ∈ (0, 1)`, where
`α₂ = lemma27Rate γ` (Lemma 2.7's rate, depending only on `γ`). -/
theorem theorem15_coupling_real_core
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (hρ'1 : ρ' < 1) {α₁ β p C₁ : ℝ} (hβ : 0 < β) (hp : 0 < p)
    (h311 : ∀ ε : ℝ, 0 < ε → ε < 1 → P (Lemma311GoodAt bm η ε ρ' β p)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ α₁)) :
    ∀ χ : ℝ, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → IsPreconnected Domᶜ →
      ∀ f : ℂ → ℝ, (∃ Cf : ℝ, ∀ z ∈ frontier Dom, ∀ w ∈ frontier Dom, |f z - f w| ≤ Cf * dist z w ^ χ) →
      ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        P (HolderBadAt bm η Dom f A₀ ξ ε) ≤ ENNReal.ofReal (C * ε ^ min α₁ (lemma27Rate γ)) := by
  obtain ⟨hq0, hq', hq1⟩ := lemma27Param_facts hγ
  set q := lemma27Param γ with hqdef
  set α₂ := lemma27Rate γ with hα₂def
  have hα₂ : 0 < α₂ := lemma27Rate_pos hγ
  set β' := min β q with hβ'def
  have hβ' : 0 < β' := lt_min hβ hq0
  intro χ hχ
  set ξ := theorem15Exponent (probParam p) (boundaryExponent p) β' q χ with hξdef
  refine ⟨ξ, theorem15Exponent_pos (probParam_pos hp) (boundaryExponent_pos hp) hβ' hq0 hχ,
    fun Dom hDo hDρ hDc f hfH => ?_⟩
  obtain ⟨Cf₀, hCf₀⟩ := hfH
  set Cf := max Cf₀ 0 with hCfdef
  have hCf : 0 ≤ Cf := le_max_right _ _
  have hf : ∀ z ∈ frontier Dom, ∀ w ∈ frontier Dom, |f z - f w| ≤ Cf * dist z w ^ χ := fun z hz w hw =>
    (hCf₀ z hz w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
  have hDb : Bornology.IsBounded Dom := isBounded_ball.subset hDρ
  obtain ⟨Mf, hMf, hfM⟩ := exists_abs_le_of_holder hDb hCf hχ hf
  set A₀ := max (theorem15Const (probParam p) (boundaryConst p ρ ρ') (boundaryExponent p) β' q χ Cf Mf) 1
    with hA₀def
  obtain ⟨C₂, -, hC₂⟩ := epsA_lemma27_coupling D hstd hγ hq0 hq' ⟨hρ, lt_trans hρρ' hρ'1⟩
    (lemma27Rate_lt hγ)
  refine ⟨A₀, lt_of_lt_of_le one_pos (le_max_right _ _), |C₁| + |C₂|, fun ε hε0 hε1 => ?_⟩
  set cells : Ω → ℤ → Set ℂ := fun ω x => η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) with hcellsdef
  set Bad27 : Set Ω := {ω | ∀ x : ℤ, (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ≤ ε ^ q}ᶜ with hBad27
  set BadP : Set Ω := {ω | ¬ RouteM.Peanosphere (bm ω) (η ω)} with hBadP
  -- the bad event is covered by the bad events of the inputs
  have hsub : HolderBadAt bm η Dom f A₀ ξ ε ⊆ ((Lemma311GoodAt bm η ε ρ' β p)ᶜ ∪ Bad27) ∪ BadP := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or, hBad27, hBadP, mem_compl_iff, mem_ofPred_eq, not_not] at hcon
    obtain ⟨⟨⟨h, H, hcell, hL⟩, h27ω⟩, hPω⟩ := hcon
    apply hω
    refine ⟨h, fun g hg x hx y hy => ?_⟩
    have hconn := Implementation.matedCRT_graph_connected_impl ε (bm ω) h
    have hLC : H.PointConnected := RouteM.pointConnected_of_peanosphere_holds hPω H hcell
    have hpt : ∀ v : ℤ, η ω (ε * v) ∈ H.cell v := by
      intro v
      rw [hcell]
      exact ⟨ε * v, ⟨by nlinarith, le_rfl⟩, rfl⟩
    have hcellsH : ∀ v, (H.cell v ∩ ball (0 : ℂ) ρ).Nonempty → diam (H.cell v) ≤ ε ^ q := by
      rw [hcell]
      exact h27ω
    rw [← hcell] at hg hx hy
    have hmain := theorem15_of_lemma311Holds hconn hLC (fun v => η ω (ε * v)) hpt hε0 hε1.le hρ hρρ' hβ'
      (min_le_right _ _) hq1 hp (T15A.Lemma311Holds.mono hL hε0 hε1.le le_rfl (min_le_left _ _) le_rfl)
      hcellsH hDo hDρ hDc hCf hχ hMf hf hfM hg x hx y hy
    exact hmain.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (le_max_of_le_left hε0.le) _))
  have hNP : P BadP = 0 := ae_iff.mp (MoTInput.ae_peanosphere D)
  have hpow : ∀ a : ℝ, min α₁ α₂ ≤ a → ε ^ a ≤ ε ^ min α₁ α₂ := fun a ha =>
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le ha
  have hle : ∀ (C a : ℝ), min α₁ α₂ ≤ a →
      ENNReal.ofReal (C * ε ^ a) ≤ ENNReal.ofReal (|C| * ε ^ min α₁ α₂) := fun C a ha =>
    ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hε0.le _)).trans
      (mul_le_mul_of_nonneg_left (hpow a ha) (abs_nonneg C)))
  calc P (HolderBadAt bm η Dom f A₀ ξ ε)
      ≤ P (((Lemma311GoodAt bm η ε ρ' β p)ᶜ ∪ Bad27) ∪ BadP) := measure_mono hsub
    _ ≤ (P (Lemma311GoodAt bm η ε ρ' β p)ᶜ + P Bad27) + P BadP :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (ENNReal.ofReal (|C₁| * ε ^ min α₁ α₂) + ENNReal.ofReal (|C₂| * ε ^ min α₁ α₂)) + 0 := by
        rw [hNP]
        exact add_le_add (add_le_add ((h311 ε hε0 hε1).trans (hle C₁ α₁ (min_le_left _ _)))
          ((hC₂ ε ⟨hε0, hε1⟩).trans (hle C₂ α₂ (min_le_right _ _)))) le_rfl
    _ = ENNReal.ofReal ((|C₁| + |C₂|) * ε ^ min α₁ α₂) := by
        have hr := Real.rpow_nonneg hε0.le (min α₁ α₂)
        rw [add_zero, ← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) hr)
          (mul_nonneg (abs_nonneg _) hr), add_mul]

/-- A `HolderOnWith K χ` function on `∂Dom` satisfies the real Hölder bound `|f z − f w| ≤ K |z − w|^χ` there. -/
theorem holder_of_holderOnWith {Dom : Set ℂ} {f : ℂ → ℝ} {K χ : ℝ≥0} (h : HolderOnWith K χ f (frontier Dom)) :
    ∀ z ∈ frontier Dom, ∀ w ∈ frontier Dom, |f z - f w| ≤ (K : ℝ) * dist z w ^ (χ : ℝ) := fun z hz w hw => by
  rw [← Real.dist_eq]
  exact h.dist_le hz hw

/-- **[18] Theorem 1.5 for the embedded mated-CRT map of every frozen coupling, every real mesh `ε ∈ (0, 1)`**
(`[18]`, (1.9); main form), in the binder order and with the hypotheses of the
draft anchor `matedCRT_holder_of_matingOfTrees` (good event: (1.9) for every discrete harmonic extension), CONDITIONAL
on ONE named input: [18] (3.35) at every real `ε` with a rate `α₁` uniform in the ambient radius.
There is `α > 0` (`α = min α₁ α₂`, `α₂` Lemma 2.7's rate) such that for every `ρ ∈ (0, 1)` and `χ > 0` there is
`ξ > 0` such that for every open connected `Dom ⊆ B_ρ(0)` with `ℂ \ Dom` connected and every `f` that is `χ`-Hölder on
`∂Dom` there are `A₀ > 0` and `C` with `P[HolderBadAt bm η Dom f A₀ ξ ε] ≤ C ε^α` for every `ε ∈ (0, 1)`. -/
theorem theorem15_coupling_real
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (h311 : ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C₁ : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (Lemma311GoodAt bm η ε ρ' β p)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ α₁)) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → IsConnected Dom → IsConnected Domᶜ →
      ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier Dom)) →
      ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        P (HolderBadAt bm η Dom f A₀ ξ ε) ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨α₁, hα₁, h311'⟩ := h311
  refine ⟨min α₁ (lemma27Rate γ), lt_min hα₁ (lemma27Rate_pos hγ), fun ρ hρ hρ1 χ hχ => ?_⟩
  obtain ⟨β, hβ, p, hp, C₁, hC₁⟩ := h311' ((1 + ρ) / 2) (by linarith) (by linarith)
  obtain ⟨ξ, hξ, hD⟩ := theorem15_coupling_real_core D hstd hγ hρ (by linarith : ρ < (1 + ρ) / 2)
    (by linarith) hβ hp hC₁ χ (NNReal.coe_pos.mpr hχ)
  refine ⟨ξ, hξ, fun Dom hDo hDρ _ hDc f ⟨K, hK⟩ => ?_⟩
  exact hD Dom hDo hDρ hDc.isPreconnected f ⟨K, holder_of_holderOnWith hK⟩

/-- **[18] Theorem 1.5 at every real mesh, for an input whose rate depends on the radius**: as
`theorem15_coupling_real`, with the input (3.35) at each ambient radius `ρ'` with its own rate `α₁(ρ')`; then `α`
is chosen after `ρ` (it is `min α₁((1+ρ)/2) α₂`). -/
theorem theorem15_coupling_real_perRho
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (h311 : ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∃ α₁ : ℝ, 0 < α₁ ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C₁ : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (Lemma311GoodAt bm η ε ρ' β p)ᶜ ≤ ENNReal.ofReal (C₁ * ε ^ α₁)) :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ α : ℝ, 0 < α ∧ ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → IsConnected Dom → IsConnected Domᶜ →
      ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier Dom)) →
      ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        P (HolderBadAt bm η Dom f A₀ ξ ε) ≤ ENNReal.ofReal (C * ε ^ α) := by
  intro ρ hρ hρ1
  obtain ⟨α₁, hα₁, β, hβ, p, hp, C₁, hC₁⟩ := h311 ((1 + ρ) / 2) (by linarith) (by linarith)
  refine ⟨min α₁ (lemma27Rate γ), lt_min hα₁ (lemma27Rate_pos hγ), fun χ hχ => ?_⟩
  obtain ⟨ξ, hξ, hD⟩ := theorem15_coupling_real_core D hstd hγ hρ (by linarith : ρ < (1 + ρ) / 2)
    (by linarith) hβ hp hC₁ χ (NNReal.coe_pos.mpr hχ)
  refine ⟨ξ, hξ, fun Dom hDo hDρ _ hDc f ⟨K, hK⟩ => ?_⟩
  exact hD Dom hDo hDρ hDc.isPreconnected f ⟨K, holder_of_holderOnWith hK⟩

end Real

end MatedCRTHarmonic.GMSMain.T15B
