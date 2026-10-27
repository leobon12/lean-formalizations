import MatedCRTHarmonic.GMSMain.T16DTutte

/-!
# The (1.6) predicates of the draft surface v5, and their bridges to the Dirichlet layer

The draft frozen surface v5 does not
define `f_ε` or `Φ^ε` as objects; its good events assert that a function with the defining properties of [18] (1.6)
exists and that every such function satisfies the bound (disclosure 9 of the guide). This file mirrors its two predicates
with the **same bodies and argument order** (local copies in the namespace `GMSMain.T16D`, to be replaced by the frozen
names `LFMultigraph.IsHarmonicExtension`, `LFMultigraph.IsTutteEmbedding` once frozen, by `rfl`):

* `IsHarmonicExtension G J D f g` — `g` has the boundary values (1.6) (as `IsLUB`) on `V(D) ∩ V(∂D)` and is discrete
  harmonic on `V(D) \ V(∂D)`, for the cell map `J : V → Set ℂ`;
* `IsTutteEmbedding G J D Φ` — both coordinates of `Φ : V → ℂ` are such functions for `f = Re`, `f = Im`.

`isHarmonicExtension_iff_sSup`: for compact cells and `f` continuous on `∂D`, the `IsLUB` form is the `sSup` form (the
body `T15B.IsHarmonicExtension`).

Bridges, for a cellular embedding `H` of `G` (`H.cell = J`), a bounded `D` and `f` continuous on `∂D`:

* `isLUB_bdryVal`: the value (1.6) is the least upper bound of `f` on `H_x ∩ ∂D`;
* `isHarmonicExtension_iff`: `IsHarmonicExtension G H.cell D f g ↔ IsCellDirichletSolution H D (bdryVal H D f) g`;
* `isHarmonicExtension_dirichletSol` (existence), `isHarmonicExtension_eqOn` (uniqueness on `V(D)`, `G` connected,
  `D` open), `isHarmonicExtension_eq_integral` (walk representation), `isHarmonicExtension_le`,
  `isHarmonicExtension_ge` (**maximum principle** `inf_{∂D} f ≤ f_ε ≤ sup_{∂D} f` on `V(D)`);
* `isTutteEmbedding_tutte` (existence), `isTutteEmbedding_eqOn` (uniqueness on `V(D)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMSMain.T16D

open LFMultigraph Harmonic HarmonicInfinity Markov GMS3

variable {V E : Type*}

/-- **[18] (1.6): `g` is the discrete harmonic function `f_ε` with boundary data `f`**, for a
multigraph `G` whose vertex `x` carries the cell `J x` (local copy of the draft v5 definition
`LFMultigraph.IsHarmonicExtension`, S0V; same body): at every `x ∈ V(D) = verticesMeeting J D`, if `J x` meets `∂D`
then `g(x)` is the least upper bound of `f` on `J x ∩ ∂D`, and otherwise `∑_{d leaves x} (g(x) − g(head d)) = 0`
(`= GMS3.lap G g x`). -/
def IsHarmonicExtension (G : LFMultigraph V E) (J : V → Set ℂ) (D : Set ℂ) (f : ℂ → ℝ) (g : V → ℝ) : Prop :=
  ∀ x ∈ verticesMeeting J D,
    (x ∈ verticesMeeting J (frontier D) → IsLUB (f '' (J x ∩ frontier D)) (g x)) ∧
      (x ∉ verticesMeeting J (frontier D) → ∑ d ∈ G.outDarts x, (g x - g (G.dtgt d)) = 0)

/-- **The Tutte embedding with identity boundary data** ([18]; local copy of the draft v5 definition
`LFMultigraph.IsTutteEmbedding`, S0V; same body): both coordinates of `Φ : V → ℂ ≅ ℝ²` are functions `f_ε` of (1.6),
for `f(z) = Re z` and `f(z) = Im z`. -/
def IsTutteEmbedding (G : LFMultigraph V E) (J : V → Set ℂ) (D : Set ℂ) (Φ : V → ℂ) : Prop :=
  IsHarmonicExtension G J D (fun z => z.re) (fun x => (Φ x).re) ∧
    IsHarmonicExtension G J D (fun z => z.im) (fun x => (Φ x).im)

/-- For compact cells and `f` continuous on `∂D`, the `IsLUB` form of (1.6) is the `sSup` form (the predicate
T15B's `T15B.IsHarmonicExtension`, `GMSMain/T15BStatement.lean`). -/
theorem isHarmonicExtension_iff_sSup {G : LFMultigraph V E} {J : V → Set ℂ} (hJ : ∀ x, IsCompact (J x))
    {D : Set ℂ} {f : ℂ → ℝ} (hf : ContinuousOn f (frontier D)) (g : V → ℝ) :
    IsHarmonicExtension G J D f g ↔
      (∀ x ∈ verticesMeeting J D, x ∈ verticesMeeting J (frontier D) → g x = sSup (f '' (J x ∩ frontier D))) ∧
        ∀ x ∈ verticesMeeting J D, x ∉ verticesMeeting J (frontier D) → GMS3.lap G g x = 0 := by
  have hlub : ∀ x, x ∈ verticesMeeting J (frontier D) →
      IsLUB (f '' (J x ∩ frontier D)) (sSup (f '' (J x ∩ frontier D))) := fun x hx =>
    isLUB_csSup (hx.image f) (((hJ x).inter_right isClosed_frontier).bddAbove_image
      (hf.mono Set.inter_subset_right))
  constructor
  · intro h
    exact ⟨fun x hx hxB => ((h x hx).1 hxB).unique (hlub x hxB), fun x hx hxB => (h x hx).2 hxB⟩
  · rintro ⟨hbd, hharm⟩ x hx
    exact ⟨fun hxB => hbd x hx hxB ▸ hlub x hxB, fun hxB => hharm x hx hxB⟩

variable {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- For `f` continuous on `∂D` and `H_x ∩ ∂D ≠ ∅`, the value (1.6) is the least upper bound of `f` on `H_x ∩ ∂D`. -/
theorem isLUB_bdryVal {D : Set ℂ} {f : ℂ → ℝ} (hf : ContinuousOn f (frontier D)) {x : V}
    (hx : (H.cell x ∩ frontier D).Nonempty) :
    IsLUB (f '' (H.cell x ∩ frontier D)) (bdryVal H D f x) := by
  obtain ⟨z, hz, hval, hmax⟩ := exists_bdryVal_eq H hf hx
  rw [hval]
  exact IsGreatest.isLUB ⟨Set.mem_image_of_mem f hz, by rintro _ ⟨w, hw, rfl⟩; exact hmax w hw⟩

/-- **The predicate (1.6) of the draft surface is the cell Dirichlet problem with the boundary values `bdryVal`.** -/
theorem isHarmonicExtension_iff {D : Set ℂ} (hDb : Bornology.IsBounded D) {f : ℂ → ℝ}
    (hf : ContinuousOn f (frontier D)) (g : V → ℝ) :
    IsHarmonicExtension G H.cell D f g ↔ IsCellDirichletSolution H D (bdryVal H D f) g := by
  constructor
  · intro h
    refine ⟨fun x hx hxB => ?_, fun x hx hxB => ?_⟩
    · have hx' : x ∈ verticesMeeting H.cell D := (mem_vFin H hDb).mp hx
      have hxB' : x ∉ verticesMeeting H.cell (frontier D) := fun h' => hxB ((mem_vBd H hDb).mpr h')
      exact (h x hx').2 hxB'
    · have hx' : x ∈ verticesMeeting H.cell D := (mem_vFin H hDb).mp hx
      have hxB' : x ∈ verticesMeeting H.cell (frontier D) := (mem_vBd H hDb).mp hxB
      exact ((h x hx').1 hxB').unique (isLUB_bdryVal H hf hxB')
  · rintro ⟨hharm, hbd⟩ x hx
    have hx' : x ∈ vFin H D := (mem_vFin H hDb).mpr hx
    refine ⟨fun hxB => ?_, fun hxB => ?_⟩
    · rw [hbd x hx' ((mem_vBd H hDb).mpr hxB)]
      exact isLUB_bdryVal H hf hxB
    · exact hharm x hx' (fun h' => hxB ((mem_vBd H hDb).mp h'))

/-- **Existence**: the walk solution is a function `f_ε` of (1.6) (bounded `D`, `f` continuous on `∂D`). -/
theorem isHarmonicExtension_dirichletSol {D : Set ℂ} (hDb : Bornology.IsBounded D) {f : ℂ → ℝ}
    (hf : ContinuousOn f (frontier D)) :
    IsHarmonicExtension G H.cell D f (dirichletSol G (vBd H D) (bdryVal H D f)) :=
  (isHarmonicExtension_iff H hDb hf _).mpr (isCellDirichletSolution_dirichletSol H D _)

/-- **Uniqueness**: two functions `f_ε` of (1.6) agree on `V(D)` (connected `G`, bounded open `D`). -/
theorem isHarmonicExtension_eqOn (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {f : ℂ → ℝ} (hf : ContinuousOn f (frontier D)) {g₁ g₂ : V → ℝ}
    (h₁ : IsHarmonicExtension G H.cell D f g₁) (h₂ : IsHarmonicExtension G H.cell D f g₂) :
    ∀ x ∈ verticesMeeting H.cell D, g₁ x = g₂ x := fun x hx =>
  cellDirichlet_eqOn H hconn hDo hDb ((isHarmonicExtension_iff H hDb hf g₁).mp h₁)
    ((isHarmonicExtension_iff H hDb hf g₂).mp h₂) x ((mem_vFin H hDb).mpr hx)

/-- **Walk representation**: `f_ε(x) = E_x[f_ε(X_τ)]`, `τ` the hitting time of `V(∂D)`. -/
theorem isHarmonicExtension_eq_integral (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {f : ℂ → ℝ} (hf : ContinuousOn f (frontier D)) {g : V → ℝ}
    (hg : IsHarmonicExtension G H.cell D f g) {x : V} (hx : x ∈ verticesMeeting H.cell D) :
    g x = ∫ ω, g (hitVertex G (verticesMeeting H.cell (frontier D)) ω) ∂G.walkLaw x :=
  cellDirichlet_eq_integral H hconn hDo hDb ((isHarmonicExtension_iff H hDb hf g).mp hg)
    ((mem_vFin H hDb).mpr hx)

/-- **Maximum principle**: if `f ≤ M` on `∂D`, then `f_ε ≤ M` on `V(D)`. -/
theorem isHarmonicExtension_le (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {f : ℂ → ℝ} (hf : ContinuousOn f (frontier D)) {g : V → ℝ}
    (hg : IsHarmonicExtension G H.cell D f g) {M : ℝ} (hM : ∀ z ∈ frontier D, f z ≤ M) :
    ∀ x ∈ verticesMeeting H.cell D, g x ≤ M := by
  intro x hx
  refine cellDirichlet_le H hconn hDo hDb ((isHarmonicExtension_iff H hDb hf g).mp hg)
    (fun y _ hyB => ?_) x ((mem_vFin H hDb).mpr hx)
  obtain ⟨z, hz, hval, -⟩ := exists_bdryVal_eq H hf ((mem_vBd H hDb).mp hyB)
  rw [hval]
  exact hM z hz.2

/-- **Minimum principle**: if `m ≤ f` on `∂D`, then `m ≤ f_ε` on `V(D)`. -/
theorem isHarmonicExtension_ge (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {f : ℂ → ℝ} (hf : ContinuousOn f (frontier D)) {g : V → ℝ}
    (hg : IsHarmonicExtension G H.cell D f g) {m : ℝ} (hm : ∀ z ∈ frontier D, m ≤ f z) :
    ∀ x ∈ verticesMeeting H.cell D, m ≤ g x := by
  intro x hx
  refine cellDirichlet_ge H hconn hDo hDb ((isHarmonicExtension_iff H hDb hf g).mp hg)
    (fun y hy hyB => ?_) x ((mem_vFin H hDb).mpr hx)
  obtain ⟨z, hz, hval, hmax⟩ := exists_bdryVal_eq H hf ((mem_vBd H hDb).mp hyB)
  rw [hval]
  exact hm z hz.2

/-- **Existence of the Tutte embedding**: `tutte H D` is a Tutte embedding with identity boundary data (bounded
`D`). -/
theorem isTutteEmbedding_tutte {D : Set ℂ} (hDb : Bornology.IsBounded D) :
    IsTutteEmbedding G H.cell D (tutte H D) :=
  ⟨isHarmonicExtension_dirichletSol H hDb Complex.continuous_re.continuousOn,
    isHarmonicExtension_dirichletSol H hDb Complex.continuous_im.continuousOn⟩

/-- **Uniqueness of the Tutte embedding** on `V(D)` (connected `G`, bounded open `D`). -/
theorem isTutteEmbedding_eqOn (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {Φ : V → ℂ} (hΦ : IsTutteEmbedding G H.cell D Φ) :
    ∀ x ∈ verticesMeeting H.cell D, Φ x = tutte H D x := by
  intro x hx
  obtain ⟨hT₁, hT₂⟩ := isTutteEmbedding_tutte H hDb
  apply Complex.ext
  · exact isHarmonicExtension_eqOn H hconn hDo hDb Complex.continuous_re.continuousOn hΦ.1 hT₁ x hx
  · exact isHarmonicExtension_eqOn H hconn hDo hDb Complex.continuous_im.continuousOn hΦ.2 hT₂ x hx

end MatedCRTHarmonic.GMSMain.T16D
