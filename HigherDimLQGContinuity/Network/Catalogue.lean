import HigherDimLQGContinuity.Labels.LabelDefs

/-! # Finite counting of site labels -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGContinuity

/-- The explicit size of the index box used by all label codes. -/
theorem labelIndex_card (d K : ℕ) :
    Fintype.card (LabelIndex d K) = (2 * K + 1) ^ d := by
  classical
  change Fintype.card (↑(labelIndexFinset d K) : Type) = _
  rw [Fintype.card_coe]
  unfold labelIndexFinset
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc]
  have hK : (((K : ℤ) + 1 - -(K : ℤ)).toNat) = 2 * K + 1 := by
    omega
  simp only [hK, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The number of polygonal lead codes is bounded by the choices of its last
index and its padded grid tuple. -/
private theorem leadCode_card_le (d Kl N : ℕ) :
    Fintype.card (LeadCode d Kl N) ≤
      (N + 1) * Fintype.card (LabelIndex d Kl) ^ (N + 1) := by
  let f : LeadCode d Kl N → Fin (N + 1) ×
      (Fin (N + 1) → LabelIndex d Kl) := fun P => (P.last, P.grid)
  have hf : Function.Injective f := by
    intro P Q h
    cases P with
    | mk lastP gridP =>
      cases Q with
      | mk lastQ gridQ =>
        simp only [f, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rfl
  simpa only [Fintype.card_prod, Fintype.card_fin,
    Fintype.card_pi_const] using Fintype.card_le_of_injective f hf

/-- Counting raw codes also bounds the geometrically admissible subtype. -/
private theorem edgeLabel_card_le {d : ℕ} (S : SiteData d) (Kc Kl N : ℕ)
    (μ ν r c₁ : ℝ) (e : S.Edge) :
    Nat.card (EdgeLabel S e Kc Kl N μ ν r c₁) ≤
      S.Ntr * (2 ^ Fintype.card (LabelIndex d Kc)) ^ 3 *
        ((N + 1) * Fintype.card (LabelIndex d Kl) ^ (N + 1)) ^ 2 := by
  let B := Fintype.card (LabelIndex d Kc)
  let L := (N + 1) * Fintype.card (LabelIndex d Kl) ^ (N + 1)
  letI : Fintype (EdgeLabel S e Kc Kl N μ ν r c₁) := Fintype.ofFinite _
  have hsub : Fintype.card (EdgeLabel S e Kc Kl N μ ν r c₁) ≤
      Fintype.card (EdgeLabelCode S Kc Kl N) :=
    Fintype.card_subtype_le _
  let f : EdgeLabelCode S Kc Kl N →
      Fin S.Ntr × Finset (LabelIndex d Kc) ×
        Finset (LabelIndex d Kc) × Finset (LabelIndex d Kc) ×
          LeadCode d Kl N × LeadCode d Kl N :=
    fun E => (E.trial, E.chamber, E.gate0, E.gate1, E.lead0, E.lead1)
  have hf : Function.Injective f := by
    intro E F h
    cases E with
    | mk trE chE g0E g1E l0E l1E =>
      cases F with
      | mk trF chF g0F g1F l0F l1F =>
        simp only [f, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl
  have hraw := Fintype.card_le_of_injective f hf
  have hlead := leadCode_card_le d Kl N
  have htuple : Fintype.card (EdgeLabelCode S Kc Kl N) ≤
      S.Ntr * (2 ^ B) ^ 3 * L ^ 2 := by
    have hcount : Fintype.card (Fin S.Ntr × Finset (LabelIndex d Kc) ×
        Finset (LabelIndex d Kc) × Finset (LabelIndex d Kc) ×
          LeadCode d Kl N × LeadCode d Kl N) =
        S.Ntr * (2 ^ B) ^ 3 *
          Fintype.card (LeadCode d Kl N) ^ 2 := by
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_finset]
      dsimp [B]
      ring
    rw [hcount] at hraw
    exact hraw.trans (by dsimp [L]; gcongr)
  rw [Nat.card_eq_fintype_card]
  exact hsub.trans (by simpa only [B, L] using htuple)

/-- Exact finite product bound underlying the catalogue estimate (4.9).
The right side records one trial, three cell subsets, and two padded leads per
tree edge. -/
theorem labelCatalogue_card_le {d : ℕ} (S : SiteData d) (Kc Kl N : ℕ)
    (μ ν r c₁ : ℝ) :
    (labelCatalogue S Kc Kl N μ ν r c₁).card ≤
      (S.Ntr * (2 ^ Fintype.card (LabelIndex d Kc)) ^ 3 *
        ((N + 1) * Fintype.card (LabelIndex d Kl) ^ (N + 1)) ^ 2) ^
        Nat.card S.Edge := by
  classical
  letI : Fintype S.Vertex := (siteMesh_vertices_finite S.mesh.δm_pos).fintype
  letI : Fintype S.Edge := Fintype.ofFinite S.Edge
  letI : ∀ e : S.Edge, Fintype (EdgeLabel S e Kc Kl N μ ν r c₁) :=
    fun _ => Fintype.ofFinite _
  let M := S.Ntr * (2 ^ Fintype.card (LabelIndex d Kc)) ^ 3 *
    ((N + 1) * Fintype.card (LabelIndex d Kl) ^ (N + 1)) ^ 2
  have hprod : (∏ e : S.Edge, Fintype.card (EdgeLabel S e Kc Kl N μ ν r c₁)) ≤
      ∏ _e : S.Edge, M :=
    Finset.prod_le_prod (fun e _ => by
      simpa only [Nat.card_eq_fintype_card] using
        edgeLabel_card_le S Kc Kl N μ ν r c₁ e)
  simpa only [labelCatalogue, Finset.card_univ, Fintype.card_pi,
    Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card, M] using hprod

/-- Exact counting input consumed by `q7b_siteCert_of_net`. -/
theorem q4_hcount {d : ℕ} :
    ∀ (S : SiteData d) (Kc Kl N : ℕ) (μ ν r c₁ : ℝ),
      Nat.card (SiteLabel S Kc Kl N μ ν r c₁) ≤
        (S.Ntr * (2 ^ ((2 * Kc + 1) ^ d)) ^ 3 *
          ((N + 1) * ((2 * Kl + 1) ^ d) ^ (N + 1)) ^ 2) ^
          Nat.card S.Edge := by
  intro S Kc Kl N μ ν r c₁
  classical
  letI : Fintype S.Vertex := (siteMesh_vertices_finite S.mesh.δm_pos).fintype
  letI : Fintype S.Edge := Fintype.ofFinite S.Edge
  letI : ∀ e : S.Edge, Fintype (EdgeLabel S e Kc Kl N μ ν r c₁) :=
    fun _ => Fintype.ofFinite _
  have h := labelCatalogue_card_le S Kc Kl N μ ν r c₁
  simpa only [labelCatalogue, Finset.card_univ, labelIndex_card,
    Nat.card_eq_fintype_card] using h

end HigherDimLQGContinuity
