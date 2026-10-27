import MatedCRTHarmonic.GMSMain.MainResultsAdapters

/-!
# Inputs to the main results of [18] and their adapters

The draft anchors of surface v5 (`MainResultsStatements`) are proved in `MainResultsAnchors` from **three** named inputs, one for each result needed at every real mesh `ε ∈ (0, 1)`. Each input quantifies
over every frozen mating-of-trees coupling (every witness of `MatedCRT.MatingOfTreesInput γ`, `γ ∈ (0, 2)`), with the
explicit `hγ : γ ∈ Ioo 0 2` and `hstd : StandardBorelSpace Ω` of the per-coupling theorems, so that a theorem `foo D hstd hγ` discharges it as `fun γ hγ Ω _ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D => foo D hstd hγ`.

* `Theorem32Input` — [18] Theorem 3.2 at every real `ε`, using the energy and Green-function vocabulary (`RawEnergyGood`, the
  `T13RawEnergyGood` event of `GMSMain/T13Raw.lean` with the additive error `ε^α` of (3.10): cellular embedding with
  the curve cells, `IsGMSDirichletSolution`, `GMS3.energy` on `vFin`, `GMS3.eucEnergy`, `BoundedConvexityWith`).
  The real-mesh proof uses `epsA_prop210At` and `lemma27_cellAt`.
* `Theorem14GreenInput` — [18] Theorem 1.4 (1.8) at every real `ε`, using the energy and Green-function vocabulary (`RawGreenGood` =
  the body of `T13RawGreenGood`, `GMS3.green` on `vFin`, `log ε⁻¹/A · deg(0) ≤ Gr`). The same real-mesh inputs apply.
* `Theorem15Input` — [18] Theorem 1.5 (main form, (a)) at every real `ε`, in the draft's vocabulary (= the
  hypothesis `h15` of T16D's `corollary16_tendsto_of_theorem15`, for every coupling). The proof uses the real-mesh estimate (3.35). `theorem15Input_of_sSup` accepts T15B's `sSup` form of (1.6) instead.

Adapters (per coupling, every `ω`, deterministic): `rawEnergyGood_imp` / `theorem32Body_of_raw` and
`rawGreenGood_imp` / `theorem14GreenBody_of_raw` turn the input events into the stated good events
(`MainResultsAdapters`: `energyOn = ofReal ∘ GMS3.energy`, `exitGreen = GMS3.green`, (1.8) normalization, existence of
`f_ε` from T16D's Dirichlet layer).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.MainResults

open MatedCRTHarmonic GMS3

/-! ### Input events -/

/-- **The event (3.10) of [18] Theorem 3.2 using the corresponding definitions** at mesh `ε` for the mated-CRT map of the Brownian
path `b` with the cells `c([ε(x−1), εx])`: `MatedCRT.graph ε b` is locally finite and has the cellular embedding with
these cells, and every `f_ε` with the boundary data (1.6), discrete harmonic on `V(D) \ V(∂D)`, has
`Energy(f_ε; G^ε(D)) ≤ A Energy(f; D) + tol`. With `tol = 0` this is T13I's `T13RawEnergyGood`. -/
def RawEnergyGood (ε : ℝ) (b : MatedCRT.Path2) (c : C(ℝ, ℂ)) (Dom : Set ℂ) (f : ℂ → ℝ) (A tol : ℝ) : Prop :=
  ∃ (h : MatedCRT.IsLocallyFinite ε b) (H : CellularEmbedding (MatedCRT.graph ε b h) 0),
    (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
      ∀ fε : ℤ → ℝ, GMSMain.IsGMSDirichletSolution H Dom f fε →
        ENNReal.ofReal (energy (MatedCRT.graph ε b h) (vFin H Dom) fε) ≤
          ENNReal.ofReal A * eucEnergy f Dom + ENNReal.ofReal tol

/-- **The event (1.8) of [18] Theorem 1.4 using the corresponding definitions** (the body of T13I's `T13RawGreenGood`, for every real
`ε`): `Gr_τ(0, 0) ≥ (1/A) log(ε⁻¹) deg(0)`, `τ` the exit time from `V(B_ρ(0))`. -/
def RawGreenGood (ε ρ A : ℝ) (b : MatedCRT.Path2) (c : C(ℝ, ℂ)) : Prop :=
  ∃ (h : MatedCRT.IsLocallyFinite ε b) (H : CellularEmbedding (MatedCRT.graph ε b h) 0),
    (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
      ENNReal.ofReal (Real.log ε⁻¹ / A * (MatedCRT.graph ε b h).deg 0) ≤
        green (MatedCRT.graph ε b h) 0 (vFin H (ball 0 ρ))

variable {Ω : Type} [MeasurableSpace Ω]

/-- **[18] Theorem 3.2 at every real `ε` for one coupling, using the corresponding definitions** (same quantifier order and
hypotheses as the draft anchor `matedCRT_energy_le_add_of_matingOfTrees`). -/
def Theorem32RawBody (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ C : ℝ, 1 ≤ C →
    ∃ A : ℝ, 0 < A ∧ ∃ Cr : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ →
      (∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier D)) ≤ ENNReal.ofReal (C * r)) →
      GMSMain.BoundedConvexityWith C D →
      ∀ f : ℂ → ℝ, DifferentiableOn ℝ f D →
        (∀ z ∈ D, ∀ w ∈ D, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ ε ^ (-β) * dist z w) →
        (∀ z ∈ D, |f z| ≤ ε ^ (-β)) → (∀ z ∈ D, ‖fderiv ℝ f z‖ ≤ ε ^ (-β)) →
        ContinuousOn f (closure D) →
          P {ω | ¬ RawEnergyGood ε (bm ω) (η ω) D f A (ε ^ α)} ≤ ENNReal.ofReal (Cr * ε ^ α)

/-- **[18] Theorem 1.4 (1.8) at every real `ε` for one coupling, using the corresponding definitions** (T13I's
`t13_theorem14_green_raw` with `∀ ε ∈ (0, 1)` in place of `∀ k, ε = 2^{-k}`). -/
def Theorem14GreenRawBody (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ,
    ∀ ε : ℝ, 0 < ε → ε < 1 → P {ω | ¬ RawGreenGood ε ρ A (bm ω) (η ω)} ≤ ENNReal.ofReal (C * ε ^ α)

/-- **[18] Theorem 1.5 at every real `ε` for one coupling, in the `sSup` form of (1.6)** (otherwise the draft's
`Theorem15Body`). -/
def Theorem15SSupBody (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
    ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → IsConnected D → IsConnected Dᶜ →
    ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier D)) →
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
        (∃ g : ℤ → ℝ,
          T15B.IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g) ∧
        ∀ g : ℤ → ℝ,
          T15B.IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g →
          ∀ x ∈ verticesMeeting (cell ε (η ω)) D,
            ∀ y ∈ verticesMeeting (cell ε (η ω)) D,
              |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
        ENNReal.ofReal (C * ε ^ α)

/-! ### The three named inputs (every coupling) -/

/-- **Named input 1: [18] Theorem 3.2 at every real `ε ∈ (0, 1)`**, for every frozen coupling. -/
def Theorem32Input : Prop :=
  ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 2 → ∀ (Ω : Type) [MeasurableSpace Ω], StandardBorelSpace Ω →
    ∀ (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
      MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm → Theorem32RawBody P η bm

/-- **Named input 2: [18] Theorem 1.4 (1.8) at every real `ε ∈ (0, 1)`**, for every frozen coupling. -/
def Theorem14GreenInput : Prop :=
  ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 2 → ∀ (Ω : Type) [MeasurableSpace Ω], StandardBorelSpace Ω →
    ∀ (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
      MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm → Theorem14GreenRawBody P η bm

/-- **Named input 3: [18] Theorem 1.5 (main form, (a)) at every real `ε ∈ (0, 1)`**, for every
frozen coupling, in the draft's vocabulary (T16D's hypothesis `h15`). -/
def Theorem15Input : Prop :=
  ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 2 → ∀ (Ω : Type) [MeasurableSpace Ω], StandardBorelSpace Ω →
    ∀ (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
      MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm → Theorem15Body P η bm

/-- Input 3 in the `sSup` form. -/
def Theorem15SSupInput : Prop :=
  ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 2 → ∀ (Ω : Type) [MeasurableSpace Ω], StandardBorelSpace Ω →
    ∀ (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
      MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm → Theorem15SSupBody P η bm

/-! ### Adapters from input events to the stated good events -/

/-- **T13I's (3.10) event gives the draft's good event of Theorem 3.2** (every `ω`; `D` bounded, `f` continuous on
`∂D`): local finiteness, existence of `f_ε` (T16D's walk solution), and the energy bound for every `f_ε` of the draft
(1.6) (`isGMSDirichletSolution_of_isHarmonicExtension`, `energyOn_verticesMeeting`). -/
theorem rawEnergyGood_imp {ε : ℝ} {b : MatedCRT.Path2} {c : C(ℝ, ℂ)} {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D)
    {f : ℂ → ℝ} (hfc : ContinuousOn f (frontier D)) (hf : DifferentiableOn ℝ f D) {A tol : ℝ}
    (hraw : RawEnergyGood ε b c D f A tol) :
    ∃ h : MatedCRT.IsLocallyFinite ε b,
      (∃ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε b h) (cell ε c) D f g) ∧
      ∀ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε b h) (cell ε c) D f g →
        energyOn (MatedCRT.graph ε b h) (verticesMeeting (cell ε c) D) g ≤
          ENNReal.ofReal A * dirichletEnergy f D hDo hf + ENNReal.ofReal tol := by
  obtain ⟨h, H, hcell, hb⟩ := hraw
  have hHc : H.cell = cell ε c := funext hcell
  refine ⟨h, ?_, fun g hg => ?_⟩
  · rw [← hHc]
    exact ⟨_, T16D.isHarmonicExtension_dirichletSol H hDb hfc⟩
  · rw [← hHc] at hg ⊢
    rw [energyOn_verticesMeeting H hDb]
    exact hb g (isGMSDirichletSolution_of_isHarmonicExtension H hDb hg)

/-- **T13I's (1.8) event gives the draft's good event of Theorem 1.4 (1.8)** (every `ω`). -/
theorem rawGreenGood_imp {ε ρ A : ℝ} {b : MatedCRT.Path2} {c : C(ℝ, ℂ)} (hraw : RawGreenGood ε ρ A b c) :
    ∃ h : MatedCRT.IsLocallyFinite ε b,
      ENNReal.ofReal (1 / A * Real.log ε⁻¹) ≤
        exitGreen (MatedCRT.graph ε b h) (verticesMeeting (cell ε c) (ball (0 : ℂ) ρ)) 0 0 /
          ((MatedCRT.graph ε b h).deg 0 : ℝ≥0∞) := by
  obtain ⟨h, H, hcell, hg⟩ := hraw
  have hHc : H.cell = cell ε c := funext hcell
  refine ⟨h, ?_⟩
  rw [← hHc, exitGreen_verticesMeeting H isBounded_ball]
  exact ofReal_le_div_deg (deg_ne_zero' _ 0) hg

/-- **Theorem 3.2: T13I's form ⇒ the draft body** (one coupling). -/
theorem theorem32Body_of_raw {P : Measure Ω} {η : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (h32 : Theorem32RawBody P η bm) : Theorem32Body P η bm := by
  obtain ⟨α, hα, β, hβ, h32⟩ := h32
  refine ⟨α, hα, β, hβ, fun ρ hρ0 hρ1 C hC => ?_⟩
  obtain ⟨A, hA, Cr, h32⟩ := h32 ρ hρ0 hρ1 C hC
  refine ⟨A, hA, Cr, fun ε hε0 hε1 D hDo hDsub hbdry hbc f hf hL hfM hdfM hfc => ?_⟩
  refine le_trans (measure_mono ?_) (h32 ε hε0 hε1 D hDo hDsub hbdry hbc f hf hL hfM hdfM hfc)
  intro ω hω hraw
  exact hω (rawEnergyGood_imp hDo (isBounded_ball.subset hDsub) (hfc.mono frontier_subset_closure) hf hraw)

/-- **Theorem 1.4 (1.8): T13I's form ⇒ the draft body** (one coupling). -/
theorem theorem14GreenBody_of_raw {P : Measure Ω} {η : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (h14 : Theorem14GreenRawBody P η bm) : Theorem14GreenBody P η bm := by
  obtain ⟨α, hα, h14⟩ := h14
  refine ⟨α, hα, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨A, hA, C, h14⟩ := h14 ρ hρ0 hρ1
  refine ⟨A, hA, C, fun ε hε0 hε1 => le_trans (measure_mono ?_) (h14 ε hε0 hε1)⟩
  intro ω hω hraw
  exact hω (rawGreenGood_imp hraw)

/-- **Theorem 1.5: T15B's `sSup` form ⇒ the draft body** (one coupling; the cells are compact and a Hölder `f` is
continuous on `∂D`, so the two forms of (1.6) agree at every `ω`). -/
theorem theorem15Body_of_sSup {P : Measure Ω} {η : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (h15 : Theorem15SSupBody P η bm) : Theorem15Body P η bm := by
  obtain ⟨α, hα, h15⟩ := h15
  refine ⟨α, hα, fun ρ hρ0 hρ1 χ hχ => ?_⟩
  obtain ⟨ξ, hξ, h15⟩ := h15 ρ hρ0 hρ1 χ hχ
  refine ⟨ξ, hξ, fun D hDo hDsub hDc hDcc f hfH => ?_⟩
  obtain ⟨A₀, hA₀, C, h15⟩ := h15 D hDo hDsub hDc hDcc f hfH
  obtain ⟨K, hK⟩ := hfH
  have hfc : ContinuousOn f (frontier D) := hK.continuousOn hχ
  refine ⟨A₀, hA₀, C, fun ε hε0 hε1 => le_trans (measure_mono ?_) (h15 ε hε0 hε1)⟩
  intro ω hω hgood
  apply hω
  obtain ⟨h, ⟨g, hg⟩, hall⟩ := hgood
  have hiff := fun g => isHarmonicExtension_iff_t15b (MatedCRT.graph ε (bm ω) h)
    (isCompact_cell ε (η ω)) hfc g
  exact ⟨h, ⟨g, (hiff g).mpr hg⟩, fun g' hg' => hall g' ((hiff g').mp hg')⟩

end MatedCRTHarmonic.GMSMain.MainResults
