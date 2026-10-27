import MatedCRTHarmonic.GMSMain.T16DSurface
import MatedCRTHarmonic.GMSMain.EpsALemma27
import MatedCRTHarmonic.Implementation.MatedCRTGraphConnected

/-!
# The embedded mated-CRT map of a frozen coupling at every real mesh `ε`

Instantiation of the Dirichlet and Tutte layers at the cell model of every frozen mating-of-trees coupling
`D : MatedCRT.IsMatingOfTreesCoupling γ P …` (input `MatedCRT.MatingOfTreesInput γ`),
at **every real mesh `ε > 0`**, using the graph `G^ε = MatedCRT.graph ε (bm ω) h` ([18] (1.1)) and the cells `H^ε_x = η([ε(x − 1), εx])` of the bundle's area-parametrized space-filling curve
`η` ([18] (1.3); `cellAt`, a local copy of the draft `MatedCRT.cell`), with `η(x) := η(εx) ∈ H^ε_x`.

* `ae_cellularEmbeddingAt`: for every fixed `ε > 0`, almost surely `G^ε` is locally finite and the cells form a
  cellular embedding of it by `GMSMain.epsA_ae_exists_cellularEmbedding`
  (from MTC's `MoTInput.cellularEmbeddingOfCurveAt` and the Brownian facts at mesh `ε`).
* **`ae_harmonicExtension`** (target 1 at the model): for every `ε > 0`, almost surely, for every bounded open `D` and
  every `f` continuous on `∂D`: `V(G^ε(D))` is finite, the function `f_ε` of [18] (1.6) exists and is unique on
  `V(G^ε(D))`, the walk from `V(G^ε(D))` hits `V(G^ε(∂D))` almost surely, `f_ε(x) = E_x[f_ε(X_τ)]`,
  `inf_{∂D} f ≤ f_ε ≤ sup_{∂D} f` on `V(G^ε(D))`, and interior vertices have all their neighbours in `V(G^ε(D))`.
* **`ae_tutteEmbedding`** (target 2 at the model): almost surely the Tutte embedding with identity boundary data
  exists, is unique on `V(G^ε(D))`, and `‖Φ^ε(x) − η(εx)‖ ≤ 2 diam(H^ε_x)` at the vertices whose cells meet `∂D`.
* **`lemma27_cellAt`**: [18] Lemma 2.7 for these cells at every real `ε ∈ (0, 1)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.T16D

open MatedCRTHarmonic GMS3 Markov

/-- **The cells of [18] (1.3)** at mesh `ε`: `H^ε_x = η([ε(x − 1), εx])` for the vertex `x : ℤ` (standing for `εx`);
local copy of the draft v5 definition `MatedCRT.cell` (with the same body). -/
def cellAt (ε : ℝ) (η : C(ℝ, ℂ)) (x : ℤ) : Set ℂ := η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)

/-- `η(x) = η(εx) ∈ H^ε_x`. -/
theorem mem_cellAt_self {ε : ℝ} (hε : 0 ≤ ε) (η : C(ℝ, ℂ)) (x : ℤ) : η (ε * x) ∈ cellAt ε η x :=
  ⟨ε * x, ⟨by nlinarith, le_rfl⟩, rfl⟩

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
  (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)

include D in
/-- **The cellular embedding at a fixed real mesh**: for `ε > 0`, almost surely `G^ε` is locally finite and the cells
`η([ε(x−1), εx])` form a cellular embedding of `MatedCRT.graph ε (bm ω)` rooted at `0`. -/
theorem ae_cellularEmbeddingAt {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
      ∃ H : CellularEmbedding (MatedCRT.graph ε (bm ω) h) 0, H.cell = cellAt ε (η ω) := by
  filter_upwards [GMSMain.epsA_ae_exists_cellularEmbedding D hε] with ω ⟨hlf, H, hH⟩
  exact ⟨hlf, H, funext hH⟩

include D in
/-- **The function `f_ε` of [18] (1.6) for the embedded mated-CRT map of a frozen coupling, at every real mesh**
(target 1 at the model). For `ε > 0`, almost surely, for every bounded open `Dom ⊂ ℂ` and every `f` continuous on
`∂Dom`: `V(G^ε(Dom))` is finite; a function `f_ε` with the defining properties of (1.6) exists, and any two agree on
`V(G^ε(Dom))`; the walk from `x ∈ V(G^ε(Dom))` hits `V(G^ε(∂Dom))` almost surely; every `f_ε` satisfies
`f_ε(x) = E_x[f_ε(X_τ)]` and `inf_{∂Dom} f ≤ f_ε ≤ sup_{∂Dom} f` on `V(G^ε(Dom))`; and every interior vertex
(cell meeting `Dom` but not `∂Dom`) has all its neighbours in `V(G^ε(Dom))`. -/
theorem ae_harmonicExtension {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∃ h : MatedCRT.IsLocallyFinite ε (bm ω), ∀ Dom : Set ℂ, IsOpen Dom →
      Bornology.IsBounded Dom → ∀ f : ℂ → ℝ, ContinuousOn f (frontier Dom) →
        (verticesMeeting (cellAt ε (η ω)) Dom).Finite ∧
        (∃ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g) ∧
        (∀ g₁ g₂ : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g₁ →
          IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g₂ →
          ∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom, g₁ x = g₂ x) ∧
        (∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom,
          (MatedCRT.graph ε (bm ω) h).walkLaw x
            {ξ | hitTime (verticesMeeting (cellAt ε (η ω)) (frontier Dom))
              ((MatedCRT.graph ε (bm ω) h).vertexPath ξ) ≠ ⊤} = 1) ∧
        (∀ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g →
          ∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom,
            g x = ∫ ξ, g (hitVertex (MatedCRT.graph ε (bm ω) h)
              (verticesMeeting (cellAt ε (η ω)) (frontier Dom)) ξ) ∂(MatedCRT.graph ε (bm ω) h).walkLaw x) ∧
        (∀ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g →
          ∀ m M : ℝ, (∀ z ∈ frontier Dom, m ≤ f z ∧ f z ≤ M) →
            ∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom, m ≤ g x ∧ g x ≤ M) ∧
        (∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom, x ∉ verticesMeeting (cellAt ε (η ω)) (frontier Dom) →
          ∀ y, (MatedCRT.graph ε (bm ω) h).adj.Adj x y → y ∈ verticesMeeting (cellAt ε (η ω)) Dom) := by
  filter_upwards [ae_cellularEmbeddingAt D hε] with ω ⟨h, H, hH⟩
  refine ⟨h, fun Dom hDo hDb f hf => ?_⟩
  have hconn := Implementation.matedCRT_graph_connected_impl ε (bm ω) h
  rw [← hH]
  refine ⟨finite_verticesMeeting H hDb, ⟨_, isHarmonicExtension_dirichletSol H hDb hf⟩,
    fun g₁ g₂ h₁ h₂ => isHarmonicExtension_eqOn H hconn hDo hDb hf h₁ h₂,
    fun x hx => cellDirichlet_walkLaw_hitTime_eq_one H hconn hDo hDb ((mem_vFin H hDb).mpr hx),
    fun g hg x hx => isHarmonicExtension_eq_integral H hconn hDo hDb hf hg hx,
    fun g hg m M hmM x hx => ⟨isHarmonicExtension_ge H hconn hDo hDb hf hg (fun z hz => (hmM z hz).1) x hx,
      isHarmonicExtension_le H hconn hDo hDb hf hg (fun z hz => (hmM z hz).2) x hx⟩,
    fun x hx hxB y hxy => (mem_vFin H hDb).mp (mem_vFin_of_adj_of_interior H hDo hDb ((mem_vFin H hDb).mpr hx)
      (fun h' => hxB ((mem_vBd H hDb).mp h')) hxy)⟩

include D in
/-- **The Tutte embedding with identity boundary data for the embedded mated-CRT map of a frozen coupling, at every
real mesh** (target 2 at the model). For `ε > 0`, almost surely, for every bounded open `Dom`: a Tutte embedding
`Φ^ε` exists, any two agree on `V(G^ε(Dom))`, and every one approximates `x ↦ η(εx)` on the vertices of
`V(G^ε(Dom))` whose cells meet `∂Dom`: `‖Φ^ε(x) − η(εx)‖ ≤ 2 diam(H^ε_x)`. -/
theorem ae_tutteEmbedding {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∃ h : MatedCRT.IsLocallyFinite ε (bm ω), ∀ Dom : Set ℂ, IsOpen Dom →
      Bornology.IsBounded Dom →
        (∃ Φ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ) ∧
        (∀ Φ₁ Φ₂ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ₁ →
          IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ₂ →
          ∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom, Φ₁ x = Φ₂ x) ∧
        (∀ Φ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ →
          ∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom, (cellAt ε (η ω) x ∩ frontier Dom).Nonempty →
            ‖Φ x - η ω (ε * x)‖ ≤ 2 * diam (cellAt ε (η ω) x)) := by
  filter_upwards [ae_cellularEmbeddingAt D hε] with ω ⟨h, H, hH⟩
  refine ⟨h, fun Dom hDo hDb => ?_⟩
  have hconn := Implementation.matedCRT_graph_connected_impl ε (bm ω) h
  rw [← hH]
  refine ⟨⟨_, isTutteEmbedding_tutte H hDb⟩, fun Φ₁ Φ₂ h₁ h₂ x hx => ?_, fun Φ hΦ x hx hxB => ?_⟩
  · rw [isTutteEmbedding_eqOn H hconn hDo hDb h₁ x hx, isTutteEmbedding_eqOn H hconn hDo hDb h₂ x hx]
  · rw [isTutteEmbedding_eqOn H hconn hDo hDb hΦ x hx]
    exact norm_tutte_sub_le H hDb hxB (by rw [hH]; exact mem_cellAt_self hε.le (η ω) x)

include D in
/-- **[18] Lemma 2.7 at every real mesh** for the cells `η([ε(x−1), εx])` of a frozen coupling: for
`q ∈ (0, 2/(2+γ)²)`, `ρ ∈ (0, 1)` and `α < α(q, γ)` there is `C ≥ 0` such that for every `ε ∈ (0, 1)`, outside an
event of probability at most `C ε^α`, every cell meeting `B_ρ(0)` has diameter at most `ε^q`. -/
theorem lemma27_cellAt (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ρ α : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hα : α < GMSLemma27.lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ∀ x : ℤ, (cellAt ε (η ω) x ∩ ball (0 : ℂ) ρ).Nonempty → diam (cellAt ε (η ω) x) ≤ ε ^ q}ᶜ ≤
        ENNReal.ofReal (C * ε ^ α) :=
  GMSMain.epsA_lemma27_coupling D hstd hγ hq hq' hρ hα

end MatedCRTHarmonic.GMSMain.T16D
