import HigherDimLQGMetric.Sec6.Prop62Geom

/-!
# [S] Proposition 6.2: the finite subcover

Packet S6b. Source: MA3 Details (a) **D-6.2** (*Construction*, last paragraph: "Finite subcover
`𝒩_{κ₁}, …, 𝒩_{κ_J}` of `𝒢`; `N_j := 𝒩_{κ_j}`, `f_j := f_{κ_j}`, `c := min c_{κ_j}`,
`M_f := max ‖f_j‖_∞`, `H := a e^{ξM_f}`. (P): `{∃ j : config ∈ N_j} ⊇ {config ∈ 𝒢}`"), blueprint
Part A §6 (`prop:62`, step (8)).

`s6b_finite_trap_data`: given a compact set `𝒢 ⊆ C(β)` each of whose points carries a stable trap
(a discount `f_κ`, a length constant `c_κ` and a closeness radius `ε_κ`, `S6bStable`), there are
finitely many discounts `f_j`, Borel trap sets `N_j` (`s6bNSet`, radius `ε_κ/2`), a common length
constant `c` and a common bound `M_f` such that every configuration whose continuous version lies in
`𝒢` lies in some `N_j` (this gives (P)), and every configuration of two comparable length metrics in
`N_j` satisfies (T1)–(T4) (this is (T)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter Metric
open _root_.Topology
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- **The finite trap data** (finite subcover of the compact set `𝒢`). -/
theorem s6b_finite_trap_data (hd : 2 ≤ d) {c C : ℝ} {β : ConfigBounds d} {𝒢 : Set (ConfigC d)}
    (h𝒢 : IsCompact 𝒢) (h𝒢C : 𝒢 ⊆ configCompactFamily hd c C β)
    {ξ : ℝ} (hξ : 0 ≤ ξ) {V : Set (Rd d)} (hV : IsOpen V) (hVA : closure V ⊆ ann (0 : Rd d) 1 3)
    {ε₀ b a c' : ℝ} (ha : 0 < a) (hba : b ≤ a) (hε₀ : 3 * ε₀ ≤ a)
    (hstab : ∀ κ ∈ 𝒢, ∃ f : Rd d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      HasCompactSupport f ∧ tsupport f ⊆ ann (0 : Rd d) 1 3 ∧ (∀ x, 0 ≤ f x) ∧
      (∀ x, 0 < f x ↔ x ∈ V) ∧
      ∃ cκ ε : ℝ, 0 < cκ ∧ 0 < ε ∧ ∀ q ∈ configCompactFamily hd c C β, S6bClose q κ ε →
        S6bStable ξ V f ε₀ b cκ c' a q.1 q.2.1) :
    ∃ (J : ℕ) (f : ℕ → C(Rd d, ℝ)) (N : ℕ → Set (Config d)) (c₀ Mf : ℝ),
      (∀ j < J, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j) ∧ HasCompactSupport (f j) ∧
        tsupport (f j) ⊆ ann (0 : Rd d) 1 3 ∧ (∀ x, 0 ≤ f j x) ∧ (∀ x, 0 < f j x ↔ x ∈ V) ∧
        (∀ x, f j x ≤ Mf)) ∧
      0 < c₀ ∧ (∀ j < J, MeasurableSet (N j)) ∧
      (∀ (D₀ Dt₀ : ContMetric d) (hl : D₀.IsLength) (hlt : Dt₀.IsLength) {s r : ℝ}
        (hs : 0 < s) (hr : 0 < r) (z : Rd d),
        configC hd D₀ Dt₀ hl hlt hs hr z ∈ 𝒢 → ∃ j < J, config D₀ Dt₀ s r z ∈ N j) ∧
      (∀ D₀ Dt₀ : ContMetric d, D₀.IsLength → Dt₀.IsLength →
        ∀ (s r : ℝ) (z : Rd d) (j : ℕ), 0 < s → 0 < r → j < J → config D₀ Dt₀ s r z ∈ N j →
          TrapProps ξ V f J a b c₀ a (a * Real.exp (ξ * Mf)) c' D₀ Dt₀ s r z j) := by
  classical
  choose! F hFs hFc hFt hF0 hFV cF εF hcF hεF hFstab using hstab
  obtain ⟨t, ht𝒢, hcov⟩ := h𝒢.elim_nhds_subcover (fun κ => {q | S6bClose q κ (εF κ / 2)})
    (fun κ hκ => s6b_close_mem_nhds κ (half_pos (hεF κ hκ)))
  have hbound : ∀ κ ∈ 𝒢, ∃ M : ℝ, ∀ x, F κ x ≤ M := by
    intro κ hκ
    obtain ⟨M, hM⟩ := (hFc κ hκ).exists_bound_of_continuous (hFs κ hκ).continuous
    exact ⟨M, fun x => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM x)⟩
  choose! MF hMF using hbound
  set J := t.card with hJ
  let κs : ℕ → ConfigC d := fun j =>
    if h : j < J then ((t.equivFin.symm ⟨j, h⟩ : t) : ConfigC d) else 0
  have hκst : ∀ j < J, κs j ∈ t := by
    intro j hj
    simp only [κs, hj, ↓reduceDIte]
    exact (t.equivFin.symm ⟨j, hj⟩).2
  have hκs𝒢 : ∀ j < J, κs j ∈ 𝒢 := fun j hj => ht𝒢 _ (hκst j hj)
  have hsurj : ∀ κ ∈ t, ∃ j < J, κs j = κ := by
    intro κ hκ
    have hlt : ((t.equivFin ⟨κ, hκ⟩ : Fin t.card) : ℕ) < J := (t.equivFin ⟨κ, hκ⟩).2
    refine ⟨t.equivFin ⟨κ, hκ⟩, hlt, ?_⟩
    simp only [κs, hlt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
  let fC : ConfigC d → C(Rd d, ℝ) := fun κ =>
    if hκ : κ ∈ 𝒢 then ⟨F κ, (hFs κ hκ).continuous⟩ else 0
  have hfC : ∀ κ ∈ 𝒢, ⇑(fC κ) = F κ := by
    intro κ hκ
    simp only [fC, hκ, ↓reduceDIte]
    rfl
  set c₀ : ℝ := t.fold min 1 cF with hc₀
  set Mf : ℝ := t.fold max 0 MF with hMf
  have hc₀κ : ∀ κ ∈ t, c₀ ≤ cF κ := fun κ hκ =>
    (Finset.fold_min_le (cF κ)).2 (Or.inr ⟨κ, hκ, le_rfl⟩)
  have hMfκ : ∀ κ ∈ t, MF κ ≤ Mf := fun κ hκ =>
    (Finset.le_fold_max (MF κ)).2 (Or.inr ⟨κ, hκ, le_rfl⟩)
  have hsupp : ∀ i < J, tsupport (fC (κs i)) ⊆ ann (0 : Rd d) 1 3 := by
    intro i hi
    rw [hfC _ (hκs𝒢 i hi)]
    exact hFt _ (hκs𝒢 i hi)
  refine ⟨J, fun j => fC (κs j), fun j => s6bNSet hd c C β (κs j) (εF (κs j) / 2), c₀, Mf,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hκ := hκs𝒢 j hj
    simp only [hfC _ hκ]
    exact ⟨hFs _ hκ, hFc _ hκ, hFt _ hκ, hF0 _ hκ, hFV _ hκ,
      fun x => (hMF _ hκ x).trans (hMfκ _ (hκst j hj))⟩
  · exact (Finset.lt_fold_min 0).2 ⟨zero_lt_one, fun κ hκ => hcF κ (ht𝒢 κ hκ)⟩
  · intro j _
    exact s6b_measurableSet_NSet hd c C β _ _
  · intro D₀ Dt₀ hl hlt s r hs hr z hq
    obtain ⟨κ, hκt, hclose⟩ := mem_iUnion₂.1 (hcov hq)
    obtain ⟨j, hj, rfl⟩ := hsurj κ hκt
    exact ⟨j, hj, s6b_mem_NSet hd hl hlt hs hr z (h𝒢C hq) hclose.closeLe⟩
  · intro D₀ Dt₀ hl hlt s r z j hs hr hj hN
    have hκ := hκs𝒢 j hj
    have hf0 : ∀ x, 0 ≤ fC (κs j) x := by
      rw [hfC _ hκ]
      exact hF0 _ hκ
    have hfV : ∀ x, 0 < fC (κs j) x ↔ x ∈ V := by
      rw [hfC _ hκ]
      exact hFV _ hκ
    have hfM : ∀ x, fC (κs j) x ≤ Mf := by
      rw [hfC _ hκ]
      exact fun x => (hMF _ hκ x).trans (hMfκ _ (hκst j hj))
    have hstabj : ∀ q ∈ configCompactFamily hd c C β, S6bClose q (κs j) (εF (κs j)) →
        S6bStable ξ V (fC (κs j)) ε₀ b (cF (κs j)) c' a q.1 q.2.1 := by
      rw [hfC _ hκ]
      exact hFstab _ hκ
    exact s6b_trapProps_of_mem hd hξ hV hVA hf0 hfV hfM (f' := fun j => fC (κs j)) rfl hsupp
      ha hba (hc₀κ _ (hκst j hj)) hε₀ (half_lt_self (hεF _ hκ)) hstabj hl hlt hs hr z hN

end HigherDimLQGMetric
