import HigherDimLQGContinuity.Labels.SiteGeometry

/-!
# Finite geometric codes for site labels

The ambient integer boxes are finite. Geometric admissibility of a code is a
predicate on that finite type. This keeps realizability deterministic and
separate from field events.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- A finite box of integer vectors. -/
def labelIndexFinset (d K : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(K : ℤ)) K

/-- An integer vector in a fixed finite box. -/
abbrev LabelIndex (d K : ℕ) := ↑(labelIndexFinset d K)

/-- A bounded code for a polygonal lead on the `ν` grid. Only entries through
`last` are used; the later entries are padding of this fixed finite product. -/
structure LeadCode (d K N : ℕ) where
  last : Fin (N + 1)
  grid : Fin (N + 1) → LabelIndex d K
deriving Fintype

/-- The actual point of a grid code at a valid sequence position. -/
def LeadCode.point {d K N : ℕ} (P : LeadCode d K N) (ν : ℝ)
    (j : Fin (N + 1)) : Rd d :=
  WithLp.toLp 2 fun i => ν * ((P.grid j).1 i : ℝ)

/-- The part of a lead up to its final coded vertex. -/
def LeadCode.trace {d K N : ℕ} (P : LeadCode d K N) (ν : ℝ) : Set (Rd d) :=
  ⋃ j : Fin N, if (j : ℕ) < P.last then
    segment ℝ (P.point ν j.castSucc) (P.point ν j.succ) else ∅

/-- The deterministic geometric conditions (L3)–(L4) on one lead code. -/
def LeadCode.Geometry {d K N : ℕ} (P : LeadCode d K N) (ν r c₁ : ℝ)
    (m : Rd d) (L : ℝ) (p : Rd d) : Prop :=
  2 ≤ P.last.val ∧ P.point ν 0 = p ∧
  (∀ j : Fin (N + 1), j ≤ P.last →
    (∀ i, |(P.point ν j) i - m i| ≤ L) ∧
    (1 ≤ j.val → ∀ i, |(P.point ν j) i - m i| + r / (4 * Real.sqrt d) ≤ L)) ∧
  (∀ j j' : Fin (N + 1), j ≤ P.last → j' ≤ P.last →
    P.point ν j = P.point ν j' → j = j') ∧
  (∀ j j' : Fin N, j.val + 2 ≤ j'.val → j'.val < P.last.val →
    ∀ x ∈ segment ℝ (P.point ν j.castSucc) (P.point ν j.succ),
    ∀ y ∈ segment ℝ (P.point ν j'.castSucc) (P.point ν j'.succ),
      c₁ * ν ^ 3 ≤ dist x y) ∧
  (∀ j : Fin N, ∀ h : j.val + 1 < P.last.val,
    segment ℝ (P.point ν j.castSucc) (P.point ν j.succ) ∩
      segment ℝ (P.point ν j.succ)
        (P.point ν ⟨j.val + 2, by have := P.last.isLt; omega⟩) = {P.point ν j.succ})

/-- Raw finite edge-label data: trial, three cell-index sets, and two leads. -/
structure EdgeLabelCode {d : ℕ} (S : SiteData d) (Kc Kl N : ℕ) where
  trial : Fin S.Ntr
  chamber : Finset (LabelIndex d Kc)
  gate0 : Finset (LabelIndex d Kc)
  gate1 : Finset (LabelIndex d Kc)
  lead0 : LeadCode d Kl N
  lead1 : LeadCode d Kl N
deriving Fintype

/-- Forget the finite box certificate of a cell index. -/
def labelCellIndices {d K : ℕ} (Q : Finset (LabelIndex d K)) :
    Finset (Fin d → ℤ) := Q.image Subtype.val

/-- The exact deterministic admissibility conditions of one edge label. -/
def EdgeLabelCode.Geometry {d : ℕ} (S : SiteData d) (e : S.Edge)
    {Kc Kl N : ℕ} (E : EdgeLabelCode S Kc Kl N)
    (μ ν r c₁ : ℝ) : Prop :=
  (∀ k ∈ labelCellIndices E.chamber,
    cell μ (S.edgeCenter e) k ⊆ S.box e) ∧
  (∀ k ∈ labelCellIndices E.gate0,
    cell μ (S.edgeCenter e) k ⊆ S.box e) ∧
  (∀ k ∈ labelCellIndices E.gate1,
    cell μ (S.edgeCenter e) k ⊆ S.box e) ∧
  E.lead0.Geometry ν r c₁ (S.edgeCenter e) S.boxHalfSide (S.port e 0) ∧
  E.lead1.Geometry ν r c₁ (S.edgeCenter e) S.boxHalfSide (S.port e 1) ∧
  (∀ j j' : Fin N, j.val < E.lead0.last.val → j'.val < E.lead1.last.val →
    ∀ x ∈ segment ℝ (E.lead0.point ν j.castSucc) (E.lead0.point ν j.succ),
    ∀ y ∈ segment ℝ (E.lead1.point ν j'.castSucc) (E.lead1.point ν j'.succ),
      c₁ * ν ^ 3 ≤ dist x y)

/-- A geometrically admissible label for one tree edge. -/
abbrev EdgeLabel {d : ℕ} (S : SiteData d) (e : S.Edge)
    (Kc Kl N : ℕ) (μ ν r c₁ : ℝ) :=
  {E : EdgeLabelCode S Kc Kl N // E.Geometry S e μ ν r c₁}

/-- A site label assigns one admissible edge label to every edge of the fixed
spanning tree. -/
abbrev SiteLabel {d : ℕ} (S : SiteData d) (Kc Kl N : ℕ)
    (μ ν r c₁ : ℝ) :=
  ∀ e : S.Edge, EdgeLabel S e Kc Kl N μ ν r c₁

/-- The full finite catalogue, before realizability is imposed. -/
def labelCatalogue {d : ℕ} (S : SiteData d) (Kc Kl N : ℕ)
    (μ ν r c₁ : ℝ) : Finset (SiteLabel S Kc Kl N μ ν r c₁) := by
  classical
  letI : Fintype S.Vertex := (siteMesh_vertices_finite S.mesh.δm_pos).fintype
  letI : Fintype S.Edge := Fintype.ofFinite S.Edge
  letI : ∀ e : S.Edge, Fintype (EdgeLabel S e Kc Kl N μ ν r c₁) :=
    fun _ => Fintype.ofFinite _
  exact Finset.univ

end HigherDimLQGContinuity
