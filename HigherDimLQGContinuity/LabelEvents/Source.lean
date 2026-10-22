import HigherDimLQGContinuity.LabelEvents.ArcSpace
import HigherDimLQGContinuity.Witness.Refs
import HigherDimLQGContinuity.Norm.ScalingSets
import HigherDimLQGContinuity.Events.Connector
import HigherDimLQGContinuity.Events.RefsProb

/-!
# Source validity of a label, its locality and realizable labels (packet Q5)

Source: blueprint Part B `b:def-source` ((4.10) with internal distances in the seed inspection and the first-exit
clause), `b:lem-src-meas`(b) (locality in `B`), `b:def-label` (realizable labels), `b:thm-sitecert`(iv) ("the arcs of
(V2) satisfy the geometric predicates"); [C] (4.10), p. 14, l. 724–734; planning audit NA2, items 12–14, R8 (separation
statements for realizable labels; source events), Details (d)12; rulings N9, N13, N20.

The concrete site data and labels of Part B (`SiteData`, `EdgeLabel`, cells, leads, `siteConsts`) are owned by the
producer packets Q3/Q4 and enter here only through what source validity reads from a label: for every tree edge `e`
the seed of its trial (centre `c e = m_e`, radius `r e = s_{e,j}`) and its **geometric predicate** `Geo e` on arcs
(`b:def-label`: covered-and-hit cells, lead clearances, lead tips), so that `SiteSource` instantiates Part B's
`SiteSource_ℓ` for every label `ℓ` (packet Q7).

* `srcSeedA c r = c + r·A` and `srcSeedK c r = c + r·K`: seed inspection and seed shell (Part B (F5); the same sets
  as `SiteData.seedA`/`seedK` of packet Q3, written `(fun x => c + r • x) '' siteA d`); for `r > 0` they are the
  annuli `ann c (r/2) (7r/2)` and `annCl c (3r/4) r`.
* `EdgeSource` ((V2) for one edge) and `SiteSource` ((V1) `SiteRefs` and (V2) for every edge).
* `siteSource_local` (`b:lem-src-meas`(b)): if `D, D₂` and `E, E₂` have the same internal metric on `B = B₄`, then
  `SiteSource D E ↔ SiteSource D₂ E₂` (any continuous metrics), because every clause reads internal metrics in open
  subsets of `B` only, and an internal metric on `W ⊆ U` is determined by the one on `U`
  (`ContMetric.internalWith_internal`, BBI Prop. 2.3.12).
* `siteRefs_of_siteSource`, `IsArcRealizable`, `isArcRealizable_of_siteSource` (every label accepted by a source
  event is realizable), `isCompact_realizingArcs`.
* Closedness of geometric predicates (the inputs of `b:lem-src-meas`(a) for the concrete labels):
  `isClosed_setOf_witExt_image_subset` (covered), `isClosed_setOf_witExt_image_inter_nonempty` (hit),
  `isClosed_setOf_forall_le_dist_witExt` (lead clearance), `isClosed_setOf_dist_apply_le` (lead tip).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-! ## Seed sets -/

/-- The seed inspection `c + r·A` of a trial (Part B (F5): `A_{e,j} = m_e + s_{e,j} A`). -/
def srcSeedA (c : Rd d) (r : ℝ) : Set (Rd d) := (fun x : Rd d => c + r • x) '' siteA d

/-- The seed shell `c + r·K` of a trial (Part B (F5): `K_{e,j} = m_e + s_{e,j} K`). -/
def srcSeedK (c : Rd d) (r : ℝ) : Set (Rd d) := (fun x : Rd d => c + r • x) '' annK d

theorem q5_affine_comm (c : Rd d) (r : ℝ) :
    (fun x : Rd d => c + r • x) = fun x => r • x + c :=
  funext fun x => add_comm c (r • x)

theorem srcSeedA_eq (c : Rd d) {r : ℝ} (hr : 0 < r) : srcSeedA c r = ann c (r / 2) (7 * r / 2) := by
  rw [srcSeedA, q5_affine_comm, siteA]
  exact p5b_image_annA hr c

theorem srcSeedK_eq (c : Rd d) {r : ℝ} (hr : 0 < r) : srcSeedK c r = annCl c (3 * r / 4) r := by
  rw [srcSeedK, q5_affine_comm, annK, p2_image_affine_annCl hr, smul_zero, zero_add]
  congr 1 <;> ring

theorem isOpen_srcSeedA (c : Rd d) {r : ℝ} (hr : 0 < r) : IsOpen (srcSeedA c r) := by
  rw [srcSeedA_eq c hr]
  exact isOpen_ann _ _ _

theorem isCompact_srcSeedK (c : Rd d) (r : ℝ) : IsCompact (srcSeedK c r) :=
  p5b_isCompact_annK.image (continuous_const.add (continuous_const_smul r))

theorem srcSeedK_subset_srcSeedA (c : Rd d) {r : ℝ} (hr : 0 < r) : srcSeedK c r ⊆ srcSeedA c r := by
  rw [srcSeedK_eq c hr, srcSeedA_eq c hr]
  exact p5b_annCl_subset_ann hr c

/-- The first-exit sphere of radius `r/8` around a point of the seed shell lies in the seed inspection. -/
theorem mem_srcSeedA_of_norm_sub {c : Rd d} {r : ℝ} (hr : 0 < r) {u w : Rd d} (hu : u ∈ srcSeedK c r)
    (hw : ‖w - u‖ = r / 8) : w ∈ srcSeedA c r := by
  rw [srcSeedK_eq c hr] at hu
  rw [srcSeedA_eq c hr]
  obtain ⟨hu1, hu2⟩ := hu
  have h1 : ‖w - c‖ ≤ ‖w - u‖ + ‖u - c‖ := by
    calc ‖w - c‖ = ‖(w - u) + (u - c)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖w - u‖ + ‖u - c‖ := norm_add_le _ _
  have h2 : ‖u - c‖ ≤ ‖u - w‖ + ‖w - c‖ := by
    calc ‖u - c‖ = ‖(u - w) + (w - c)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖u - w‖ + ‖w - c‖ := norm_add_le _ _
  rw [norm_sub_rev u w] at h2
  constructor <;> linarith

/-- The seed inspection lies in the closed ball of radius `7r/2` about its centre. -/
theorem srcSeedA_subset_closedBall (c : Rd d) {r : ℝ} (hr : 0 < r) :
    srcSeedA c r ⊆ closedBall c (7 * r / 2) := by
  rw [srcSeedA_eq c hr]
  intro x hx
  rw [mem_closedBall, dist_eq_norm]
  exact hx.2.le

/-- The affine image `s U + z` of an open set is open (`s ≠ 0`). -/
theorem q5_isOpen_affine_image {s : ℝ} (hs : s ≠ 0) (z : Rd d) {U : Set (Rd d)} (hU : IsOpen U) :
    IsOpen ((fun u => s • u + z) '' U) := by
  rw [p2_image_affine hs]
  exact hU.preimage ((continuous_id.sub continuous_const).const_smul s⁻¹)

/-- `x ↦ s x + z` is injective (`s ≠ 0`). -/
theorem q5_affine_injective {s : ℝ} (hs : s ≠ 0) (z : Rd d) : Function.Injective fun u : Rd d => s • u + z :=
  fun _ _ h => smul_right_injective (Rd d) hs (add_right_cancel h)

/-! ## Source validity -/

/-- **Source validity of one edge** (Part B `b:def-source` (V2)) at the seed `(c, r)` of the edge's trial, with the
secondary doubled-ball constants `(HE, sE)`, the arc constants `(A, α, β)`, the own-length interval `[ℓ₀, ℓ₁]`, the
unit-pair bound `d₀`, the tolerance `v` and the geometric predicate `Geo` of the edge label: `DUp(E, A_e, HE, sE)`
and an arc `γ` of the arc space of the seed shell with an own length `λ ∈ [ℓ₀, ℓ₁]` such that
(a) `E(γ s, γ t; A_e) = λ|s - t|`, (b) `d₀ ≤ D(γ 0, γ 1; A_e)`, (c) `λ ≤ (1 + 4v) D(γ 0, γ 1; A_e)`,
(d) (first exit) `D(γ 0, γ 1; A_e) ≤ D(γ 0, w; A_e)` for `|w - γ 0| = r/8`, (e) `Geo γ`. -/
def EdgeSource (HE sE A α β ℓ₀ ℓ₁ d₀ v : ℝ) (c : Rd d) (r : ℝ) (Geo : C(unitInterval, Rd d) → Prop)
    (D E : ContMetric d) : Prop :=
  DUpper E (srcSeedA c r) HE sE ∧
    ∃ γ ∈ ArcSpace (srcSeedK c r) A α β, ∃ lam ∈ Icc ℓ₀ ℓ₁,
      (∀ s t : unitInterval,
        E.internal (srcSeedA c r) (γ s) (γ t) = ENNReal.ofReal (lam * |(s : ℝ) - t|)) ∧
      ENNReal.ofReal d₀ ≤ D.internal (srcSeedA c r) (γ 0) (γ 1) ∧
      ENNReal.ofReal lam ≤ ENNReal.ofReal (1 + 4 * v) * D.internal (srcSeedA c r) (γ 0) (γ 1) ∧
      (∀ w : Rd d, ‖w - γ 0‖ = r / 8 →
        D.internal (srcSeedA c r) (γ 0) (γ 1) ≤ D.internal (srcSeedA c r) (γ 0) w) ∧
      Geo γ

/-- **Source validity of a label** (Part B `b:def-source`): (V1) the site references `SiteRefs` of the primary metric
(constants (F1)) and (V2) `EdgeSource` on every tree edge `e`, at the seed `(c e, r e)` of the edge's trial and with
the geometric predicate `Geo e` of the edge label. Both metrics are in site coordinates and primary site units. -/
def SiteSource (Hup s Hlo b mc A0 HE sE A α β ℓ₀ ℓ₁ d₀ v : ℝ) {Edge : Type*} (c : Edge → Rd d)
    (r : Edge → ℝ) (Geo : Edge → C(unitInterval, Rd d) → Prop) (D E : ContMetric d) : Prop :=
  SiteRefs Hup s Hlo b mc A0 D ∧ ∀ e, EdgeSource HE sE A α β ℓ₀ ℓ₁ d₀ v (c e) (r e) (Geo e) D E

/-- Validity contains the primary site references (part of (ii) of `SiteCertOfLabel`). -/
theorem siteRefs_of_siteSource {Hup s Hlo b mc A0 HE sE A α β ℓ₀ ℓ₁ d₀ v : ℝ} {Edge : Type*}
    {c : Edge → Rd d} {r : Edge → ℝ} {Geo : Edge → C(unitInterval, Rd d) → Prop} {D E : ContMetric d}
    (h : SiteSource Hup s Hlo b mc A0 HE sE A α β ℓ₀ ℓ₁ d₀ v c r Geo D E) :
    SiteRefs Hup s Hlo b mc A0 D :=
  h.1

/-! ## Realizable labels -/

/-- **Realizability** (Part B `b:def-label`): every edge has an arc of the arc space of its seed shell satisfying
its geometric predicate. A deterministic property of the label. -/
def IsArcRealizable (A α β : ℝ) {Edge : Type*} (c : Edge → Rd d) (r : Edge → ℝ)
    (Geo : Edge → C(unitInterval, Rd d) → Prop) : Prop :=
  ∀ e, ∃ γ ∈ ArcSpace (srcSeedK (c e) (r e)) A α β, Geo e γ

/-- **Every label accepted by a source event is realizable** (Part B `b:def-label`, remark; `b:thm-sitecert`(iv)):
the arcs of (V2) satisfy the geometric predicates. -/
theorem isArcRealizable_of_siteSource {Hup s Hlo b mc A0 HE sE A α β ℓ₀ ℓ₁ d₀ v : ℝ} {Edge : Type*}
    {c : Edge → Rd d} {r : Edge → ℝ} {Geo : Edge → C(unitInterval, Rd d) → Prop} {D E : ContMetric d}
    (h : SiteSource Hup s Hlo b mc A0 HE sE A α β ℓ₀ ℓ₁ d₀ v c r Geo D E) :
    IsArcRealizable A α β c r Geo := by
  intro e
  obtain ⟨-, γ, hγ, -, -, -, -, -, -, hgeo⟩ := h.2 e
  exact ⟨γ, hγ, hgeo⟩

/-- The arcs realizing a closed geometric predicate form a compact set (so realizability is the nonemptiness of a
compact set of arcs). -/
theorem isCompact_realizingArcs (c : Rd d) (r : ℝ) {A α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {Geo : C(unitInterval, Rd d) → Prop} (hGeo : IsClosed {γ | Geo γ}) :
    IsCompact {γ | γ ∈ ArcSpace (srcSeedK c r) A α β ∧ Geo γ} :=
  (isCompact_arcSpace (isCompact_srcSeedK c r) hα hβ).inter_right hGeo

/-! ## Closedness of geometric predicates -/

/-- `γ` maps `[a, b]` into a closed set: a closed condition on the arc (the "covered" half of `CoveredHit`). -/
theorem isClosed_setOf_witExt_image_subset (a b : ℝ) {C : Set (Rd d)} (hC : IsClosed C) :
    IsClosed {γ : C(unitInterval, Rd d) | witExt γ '' Icc a b ⊆ C} := by
  have e : {γ : C(unitInterval, Rd d) | witExt γ '' Icc a b ⊆ C} =
      ⋂ t ∈ Icc a b, {γ | γ (projIcc 0 1 zero_le_one t) ∈ C} := by
    ext γ
    simp only [image_subset_iff, mem_iInter, mem_ofPred_eq]
    rfl
  rw [e]
  exact isClosed_biInter fun t _ => hC.preimage (continuous_eval_const _)

/-- `γ([a, b])` meets a closed set: a closed condition on the arc (the "hit" half of `CoveredHit`; projection along
the compact time interval). -/
theorem isClosed_setOf_witExt_image_inter_nonempty (a b : ℝ) {F : Set (Rd d)} (hF : IsClosed F) :
    IsClosed {γ : C(unitInterval, Rd d) | (witExt γ '' Icc a b ∩ F).Nonempty} := by
  have : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let ev : C(unitInterval, Rd d) × Icc a b → Rd d := fun p => p.1 (projIcc (0 : ℝ) 1 zero_le_one p.2)
  have hev : Continuous ev :=
    continuous_eval.comp (continuous_fst.prodMk
      ((continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).comp
        (continuous_subtype_val.comp continuous_snd)))
  have e : {γ : C(unitInterval, Rd d) | (witExt γ '' Icc a b ∩ F).Nonempty} = Prod.fst '' (ev ⁻¹' F) := by
    ext γ
    constructor
    · rintro ⟨x, ⟨t, ht, rfl⟩, hxF⟩
      exact ⟨(γ, ⟨t, ht⟩), hxF, rfl⟩
    · rintro ⟨⟨γ', t⟩, hF', rfl⟩
      exact ⟨ev (γ', t), ⟨t.1, t.2, rfl⟩, hF'⟩
  rw [e]
  exact isClosedMap_fst_of_compactSpace _ (hF.preimage hev)

/-- Clearance `ρ ≤ |x - γ t|` for all `x ∈ L`, `t ∈ [a, b]`: a closed condition on the arc. -/
theorem isClosed_setOf_forall_le_dist_witExt (L : Set (Rd d)) (a b ρ : ℝ) :
    IsClosed {γ : C(unitInterval, Rd d) | ∀ x ∈ L, ∀ t ∈ Icc a b, ρ ≤ dist x (witExt γ t)} := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_iInter fun t => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_const.dist (continuous_eval_const _))

/-- Lead tip `|a - γ t| ≤ ρ`: a closed condition on the arc. -/
theorem isClosed_setOf_dist_apply_le (a : Rd d) (t : unitInterval) (ρ : ℝ) :
    IsClosed {γ : C(unitInterval, Rd d) | dist a (γ t) ≤ ρ} :=
  isClosed_le (continuous_const.dist (continuous_eval_const t)) continuous_const

/-! ## Locality in `B` (`b:lem-src-meas`(b)) -/

/-- An internal metric on `W ⊆ U` is determined by the internal metric on `U` (BBI Prop. 2.3.12). -/
theorem q5_internal_eq_of_subset {G G₂ : ContMetric d} {U W : Set (Rd d)} (hWU : W ⊆ U)
    (h : ∀ x y, G.internal U x y = G₂.internal U x y) (x y : Rd d) :
    G.internal W x y = G₂.internal W x y := by
  have hU : G.internal U = G₂.internal U := funext fun a => funext fun b => h a b
  rw [← G.internalWith_internal hWU, ← G₂.internalWith_internal hWU, hU]

/-- `DUp` transfers between metrics with the same internal metrics on every subset of `U ⊇ W`. -/
theorem q5_dUpper_of_internal_eq {G G₂ : ContMetric d} {U W : Set (Rd d)} (hWU : W ⊆ U)
    (h : ∀ x y, G.internal U x y = G₂.internal U x y) {H σ : ℝ} (hG : DUpper G W H σ) :
    DUpper G₂ W H σ := by
  intro z ρ hρ hball
  have hsub : ball z (2 * ρ) ⊆ U := (ball_subset_closedBall.trans hball).trans hWU
  rw [diamIn_congr_internal (G := G) (G' := G₂) fun x _ y _ =>
    (q5_internal_eq_of_subset hsub h x y).symm]
  exact hG z ρ hρ hball

/-- The site references are local in `B`. -/
theorem q5_siteRefs_of_internal_eq {G G₂ : ContMetric d}
    (h : ∀ x y, G.internal (siteB d) x y = G₂.internal (siteB d) x y) {Hup s Hlo b mc A0 : ℝ}
    (hG : SiteRefs Hup s Hlo b mc A0 G) : SiteRefs Hup s Hlo b mc A0 G₂ := by
  have hAB : siteA d ⊆ siteB d := by
    intro x hx
    rw [siteA, mem_annA_iff] at hx
    rw [siteB, mem_ball, dist_zero_right]
    linarith [hx.2]
  have hA : ∀ x y, G.internal (siteA d) x y = G₂.internal (siteA d) x y :=
    q5_internal_eq_of_subset hAB h
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG
  refine ⟨q5_dUpper_of_internal_eq hAB h h1, fun x hx y hy => ?_, ?_, ?_, ?_⟩
  · rw [← hA x y]
    exact h2 x hx y hy
  · rw [setDistIn_congr_internal (G := G) fun x _ y _ => (hA x y).symm]
    exact h3
  · rw [setDistIn_congr_internal (G := G) fun x _ y _ => (hA x y).symm]
    exact h4
  · rw [diamIn_congr_internal (G := G) fun x _ y _ => (hA x y).symm]
    exact h5

/-- One edge's validity is local in any `U` containing its seed inspection. -/
theorem q5_edgeSource_of_internal_eq {D E D₂ E₂ : ContMetric d} {U : Set (Rd d)}
    {HE sE A α β ℓ₀ ℓ₁ d₀ v : ℝ} {c : Rd d} {r : ℝ} {Geo : C(unitInterval, Rd d) → Prop}
    (hAU : srcSeedA c r ⊆ U) (hD : ∀ x y, D.internal U x y = D₂.internal U x y)
    (hE : ∀ x y, E.internal U x y = E₂.internal U x y)
    (h : EdgeSource HE sE A α β ℓ₀ ℓ₁ d₀ v c r Geo D E) :
    EdgeSource HE sE A α β ℓ₀ ℓ₁ d₀ v c r Geo D₂ E₂ := by
  have hDA := q5_internal_eq_of_subset hAU hD
  have hEA := q5_internal_eq_of_subset hAU hE
  obtain ⟨hup, γ, hγ, lam, hlam, ha, hb, hc, hd, he⟩ := h
  refine ⟨q5_dUpper_of_internal_eq hAU hE hup, γ, hγ, lam, hlam, fun s t => ?_, ?_, ?_, fun w hw => ?_, he⟩
  · rw [← hEA]
    exact ha s t
  · rw [← hDA]
    exact hb
  · rw [← hDA]
    exact hc
  · rw [← hDA, ← hDA]
    exact hd w hw

/-- **Locality of source validity** (`b:lem-src-meas`(b)): if the seed inspections lie in `B = B₄`, and `D, D₂` and
`E, E₂` have the same internal metrics on `B`, then `SiteSource D E ↔ SiteSource D₂ E₂` (any continuous metrics). -/
theorem siteSource_local {Hup s Hlo b mc A0 HE sE A α β ℓ₀ ℓ₁ d₀ v : ℝ} {Edge : Type*}
    {c : Edge → Rd d} {r : Edge → ℝ} {Geo : Edge → C(unitInterval, Rd d) → Prop}
    (hAB : ∀ e, srcSeedA (c e) (r e) ⊆ siteB d) {D E D₂ E₂ : ContMetric d}
    (hD : ∀ x y, D.internal (siteB d) x y = D₂.internal (siteB d) x y)
    (hE : ∀ x y, E.internal (siteB d) x y = E₂.internal (siteB d) x y) :
    SiteSource Hup s Hlo b mc A0 HE sE A α β ℓ₀ ℓ₁ d₀ v c r Geo D E ↔
      SiteSource Hup s Hlo b mc A0 HE sE A α β ℓ₀ ℓ₁ d₀ v c r Geo D₂ E₂ := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨q5_siteRefs_of_internal_eq hD h1, fun e => q5_edgeSource_of_internal_eq (hAB e) hD hE (h2 e)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨q5_siteRefs_of_internal_eq (fun x y => (hD x y).symm) h1,
      fun e => q5_edgeSource_of_internal_eq (hAB e) (fun x y => (hD x y).symm) (fun x y => (hE x y).symm)
        (h2 e)⟩

/-- The seed inspection lies in `B = B₄` when the closed ball of radius `7r/2` about its centre does. -/
theorem srcSeedA_subset_siteB {c : Rd d} {r : ℝ} (hr : 0 < r) (h : closedBall c (7 * r / 2) ⊆ siteB d) :
    srcSeedA c r ⊆ siteB d :=
  (srcSeedA_subset_closedBall c hr).trans h

end HigherDimLQGContinuity
