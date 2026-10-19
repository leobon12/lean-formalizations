import HigherDimLFPP.Lower.Frames

/-!
# Polygon gluing and Riemann weights for vertex lists in `ℝ^d`

Packet P-L1, target T4 (ruling H6; audit HA4, "Details for later use" D7–D8). Deterministic
list and polygon bookkeeping for the depth-`r` construction of the lower comparison.

* `edges z`: the consecutive pairs of a vertex list; `glueFn m f`: concatenation of `m`
  polygons with matching endpoints (`Junction`); `edges_glueFn`: the edge list of a glued
  polygon is the concatenation of the edge lists. These are generic in the vertex type.
* `ew N g e`, `rcW N z g`: the Riemann weight functional `Σ_e |e| (1/N) Σ_{l<N} g(e(l/N))`;
  `riemannCost ζ N z φ = rcW N z (exp ∘ ζφ)` (HA4's `riemannCostD`), `riemannPts N z` (HA4's
  `riemannPtsD`); linearity in `g`, the point decomposition `rcW_eq_sum_dlt`, `rcW_dlt`.
* `rcW_map_app`: for a similarity `S : SimD d`,
  `rcW N (z.map S.app) g = |r| rcW N z (g ∘ S.app)`; `ew_edge_pt`, `riemannPts_map_app`.
* `riemannCost_nonneg`, `riemannCost_congr`, `riemannCost_le_exp_mul`, and continuity of the
  cost in the finitely many field values (`continuous_riemannCost_extS`).

2D source: `LQGDimension/LFPP/BlockConstructionAux1.lean` (`edges_*`, `glueFn`, `Junction`,
`edges_glueFn`, `ew`, `rcW`, `rcW_glueFn`, `rcW_eq_sum_dlt`, `rcW_map_app`, `app`, `comp`) and
`LQGDimension/LFPP/LowerAssemblyAux1.lean` (`riemannCost_nonneg`, `riemannCost_congr`,
`riemannCost_le_exp_mul`, `extS`, `continuous_riemannCost_extS`), with `List ℂ` replaced by
lists in a real normed space and complex-affine maps `z ↦ αz + β` by `SimD`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace HigherDimLFPP.Lower

/-! ## Edges of a vertex list -/

section Lists

variable {α : Type*}

/-- The edges `(z₀,z₁), (z₁,z₂), …` of a vertex list. -/
def edges (z : List α) : List (α × α) := z.zip z.tail

theorem edges_nil : edges ([] : List α) = [] := rfl

theorem edges_single (x : α) : edges [x] = [] := rfl

theorem edges_cons_cons (x y : α) (l : List α) :
    edges (x :: y :: l) = (x, y) :: edges (y :: l) := rfl

theorem edges_map {β : Type*} (f : α → β) (z : List α) :
    edges (z.map f) = (edges z).map fun e => (f e.1, f e.2) := by
  unfold edges
  rw [← List.map_tail, List.zip_map]
  rfl

/-- `edges (P ++ R.tail) = edges P ++ edges R` when `R` starts where `P` ends. -/
theorem edges_append_tail : ∀ (P R : List α), P ≠ [] → R.head? = P.getLast? →
    edges (P ++ R.tail) = edges P ++ edges R
  | [], _, h, _ => absurd rfl h
  | [x], R, _, hR => by
    cases R with
    | nil => simp at hR
    | cons y R' =>
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hR
      subst hR
      simp [edges_single]
  | x :: y :: P, R, _, hR => by
    have ih := edges_append_tail (y :: P) R (List.cons_ne_nil _ _) (by
      rw [hR, List.getLast?_cons_cons])
    rw [List.cons_append, List.cons_append, edges_cons_cons, ← List.cons_append, ih,
      edges_cons_cons, List.cons_append]

theorem getLast?_append_tail (P R : List α) (hR : R ≠ []) (h : R.head? = P.getLast?) :
    (P ++ R.tail).getLast? = R.getLast? := by
  cases R with
  | nil => exact absurd rfl hR
  | cons y R' =>
    cases R' with
    | nil =>
      simp only [List.head?_cons] at h
      simp [h]
    | cons y' R'' =>
      rw [List.getLast?_append, List.tail_cons,
        List.getLast?_eq_some_getLast (List.cons_ne_nil y' R''), Option.some_or,
        List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil y' R'')]

/-- The edges of `[v 0, …, v K]` are `(v i, v (i+1))`, `i < K`. -/
theorem edges_range_map : ∀ (K : ℕ) (v : ℕ → α),
    edges ((List.range (K + 1)).map v) = (List.range K).map fun i => (v i, v (i + 1))
  | 0, v => by simp [edges_single]
  | K + 1, v => by
    have ih := edges_range_map K (fun i => v (i + 1))
    have e1 : (List.range (K + 1 + 1)).map v =
        v 0 :: (List.range (K + 1)).map (fun i => v (i + 1)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl
    have e2 : (List.range (K + 1)).map (fun i => v (i + 1)) =
        v 1 :: (List.range K).map (fun i => v (i + 1 + 1)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl
    have e3 : (List.range (K + 1)).map (fun i => (v i, v (i + 1))) =
        (v 0, v 1) :: (List.range K).map (fun i => (v (i + 1), v (i + 1 + 1))) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl
    rw [e1, e2, edges_cons_cons, ← e2, ih, e3]

/-! ## Gluing polygons -/

/-- Concatenation of the polygons `f 0, …, f (m-1)` (consecutive ones share an endpoint). -/
def glueFn : (m : ℕ) → (Fin m → List α) → List α
  | 0, _ => []
  | m + 1, f => f 0 ++ (glueFn m fun i => f i.succ).tail

theorem head?_glueFn (m : ℕ) (f : Fin (m + 1) → List α) (h0 : f 0 ≠ []) :
    (glueFn (m + 1) f).head? = (f 0).head? := by
  simp only [glueFn]
  exact List.head?_append_of_ne_nil _ h0

theorem mem_glueFn : ∀ (m : ℕ) (f : Fin m → List α) (v : α), v ∈ glueFn m f → ∃ i, v ∈ f i
  | 0, _, _, h => by simp [glueFn] at h
  | m + 1, f, v, h => by
    simp only [glueFn, List.mem_append] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨i, hi⟩ := mem_glueFn m _ v (List.mem_of_mem_tail h)
      exact ⟨i.succ, hi⟩

/-- Junction condition: consecutive polygons share an endpoint. -/
def Junction (m : ℕ) (f : Fin m → List α) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < m), (f ⟨i, by omega⟩).getLast? = (f ⟨i + 1, h⟩).head?

theorem Junction.succ {m : ℕ} {f : Fin (m + 1) → List α} (h : Junction (m + 1) f) :
    Junction m fun i => f i.succ := by
  intro i hi
  exact h (i + 1) (by omega)

theorem getLast?_glueFn : ∀ (m : ℕ) (f : Fin (m + 1) → List α), (∀ i, f i ≠ []) →
    Junction (m + 1) f → (glueFn (m + 1) f).getLast? = (f (Fin.last m)).getLast?
  | 0, f, _, _ => by simp [glueFn]
  | m + 1, f, hne, hJ => by
    have ih := getLast?_glueFn m (fun i => f i.succ) (fun i => hne _) hJ.succ
    have hB : glueFn (m + 1) (fun i => f i.succ) ≠ [] := by
      intro hc
      have := head?_glueFn m (fun i => f i.succ) (hne _)
      rw [hc] at this
      simp only [List.head?_nil] at this
      cases hf : f (0 : Fin (m + 1)).succ with
      | nil => exact hne _ hf
      | cons a l => rw [hf] at this; simp at this
    have hh : (glueFn (m + 1) (fun i => f i.succ)).head? = (f 0).getLast? := by
      rw [head?_glueFn m _ (hne _)]
      exact (hJ 0 (by omega)).symm
    change (f 0 ++ (glueFn (m + 1) fun i => f i.succ).tail).getLast? = _
    rw [getLast?_append_tail _ _ hB hh, ih]
    rfl

theorem edges_glueFn : ∀ (m : ℕ) (f : Fin m → List α), (∀ i, f i ≠ []) → Junction m f →
    edges (glueFn m f) = (List.ofFn fun i => edges (f i)).flatten
  | 0, _, _, _ => rfl
  | m + 1, f, hne, hJ => by
    rw [List.ofFn_succ, List.flatten_cons]
    cases m with
    | zero =>
      simp [glueFn]
    | succ m =>
      have ih := edges_glueFn (m + 1) (fun i => f i.succ) (fun i => hne _) hJ.succ
      have hh : (glueFn (m + 1) (fun i => f i.succ)).head? = (f 0).getLast? := by
        rw [head?_glueFn m _ (hne _)]
        exact (hJ 0 (by omega)).symm
      change edges (f 0 ++ (glueFn (m + 1) fun i => f i.succ).tail) = _
      rw [edges_append_tail _ _ (hne 0) hh, ih]

theorem mem_edges_glueFn (m : ℕ) (f : Fin m → List α) (hne : ∀ i, f i ≠ []) (hJ : Junction m f)
    (e : α × α) (he : e ∈ edges (glueFn m f)) : ∃ i, e ∈ edges (f i) := by
  rw [edges_glueFn m f hne hJ, List.mem_flatten] at he
  obtain ⟨l, hl, he⟩ := he
  rw [List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  exact ⟨i, he⟩

end Lists

/-! ## The Riemann weight functional -/

section Riemann

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Riemann weight of one edge: `|e| (1/N) Σ_{l<N} g(e(l/N))`. -/
def ew (N : ℕ) (g : E → ℝ) (e : E × E) : ℝ :=
  ‖e.2 - e.1‖ * ((1 : ℝ) / N) * ∑ l ∈ Finset.range N, g (e.1 + ((l : ℝ) / N) • (e.2 - e.1))

/-- Riemann weight functional of a polygon. -/
def rcW (N : ℕ) (z : List E) (g : E → ℝ) : ℝ := ((edges z).map (ew N g)).sum

/-- Riemann-sum LFPP cost of a polygon with `N` equally spaced left points per edge:
`Σ_e |e| (1/N) Σ_{l<N} exp(ζ φ(e(l/N)))` (HA4's `riemannCostD`). -/
def riemannCost (ζ : ℝ) (N : ℕ) (z : List E) (φ : E → ℝ) : ℝ :=
  ((edges z).map fun e => ‖e.2 - e.1‖ * ((1 : ℝ) / N) *
    ∑ l ∈ Finset.range N, Real.exp (ζ * φ (e.1 + ((l : ℝ) / N) • (e.2 - e.1)))).sum

/-- The points read by `riemannCost` (HA4's `riemannPtsD`). -/
def riemannPts (N : ℕ) (z : List E) : Set E :=
  {p | ∃ e ∈ edges z, ∃ l < N, p = e.1 + ((l : ℝ) / N) • (e.2 - e.1)}

theorem riemannCost_eq_rcW (ζ : ℝ) (N : ℕ) (z : List E) (φ : E → ℝ) :
    riemannCost ζ N z φ = rcW N z (fun w => Real.exp (ζ * φ w)) := rfl

theorem rcW_glueFn (N : ℕ) (m : ℕ) (f : Fin m → List E) (hne : ∀ i, f i ≠ [])
    (hJ : Junction m f) (g : E → ℝ) : rcW N (glueFn m f) g = ∑ i, rcW N (f i) g := by
  unfold rcW
  rw [edges_glueFn m f hne hJ, List.map_flatten, List.sum_flatten]
  simp only [List.map_ofFn, List.sum_ofFn]
  rfl

theorem list_sum_map_finset_sum {β ι : Type*} (l : List β) (s : Finset ι) (F : ι → β → ℝ) :
    (l.map fun a => ∑ i ∈ s, F i a).sum = ∑ i ∈ s, (l.map (F i)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

theorem rcW_congr (N : ℕ) (z : List E) {g h : E → ℝ}
    (hgh : ∀ p ∈ riemannPts N z, g p = h p) : rcW N z g = rcW N z h := by
  unfold rcW
  congr 1
  refine List.map_congr_left fun e he => ?_
  unfold ew
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  exact hgh _ ⟨e, he, l, Finset.mem_range.1 hl, rfl⟩

theorem ew_finset_sum {ι : Type*} (N : ℕ) (s : Finset ι) (G : ι → E → ℝ) (e : E × E) :
    ew N (fun w => ∑ i ∈ s, G i w) e = ∑ i ∈ s, ew N (G i) e := by
  unfold ew
  rw [Finset.sum_comm, Finset.mul_sum]

theorem rcW_finset_sum {ι : Type*} (N : ℕ) (z : List E) (s : Finset ι) (G : ι → E → ℝ) :
    rcW N z (fun w => ∑ i ∈ s, G i w) = ∑ i ∈ s, rcW N z (G i) := by
  unfold rcW
  rw [show ew N (fun w => ∑ i ∈ s, G i w) = fun e => ∑ i ∈ s, ew N (G i) e from
    funext (ew_finset_sum N s G)]
  exact list_sum_map_finset_sum _ _ _

theorem rcW_const_mul (N : ℕ) (z : List E) (c : ℝ) (g : E → ℝ) :
    rcW N z (fun w => c * g w) = c * rcW N z g := by
  unfold rcW ew
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  rw [← Finset.mul_sum]
  ring

theorem ew_nonneg (N : ℕ) {g : E → ℝ} (hg : ∀ w, 0 ≤ g w) (e : E × E) : 0 ≤ ew N g e :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (by positivity)) (Finset.sum_nonneg fun _ _ => hg _)

theorem rcW_nonneg (N : ℕ) (z : List E) {g : E → ℝ} (hg : ∀ w, 0 ≤ g w) : 0 ≤ rcW N z g :=
  List.sum_nonneg fun x hx => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
    exact ew_nonneg N hg e

theorem ew_mono (N : ℕ) {g h : E → ℝ} (hgh : ∀ w, g w ≤ h w) (e : E × E) :
    ew N g e ≤ ew N h e :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ => hgh _)
    (mul_nonneg (norm_nonneg _) (by positivity))

theorem rcW_mono (N : ℕ) (z : List E) {g h : E → ℝ} (hgh : ∀ w, g w ≤ h w) :
    rcW N z g ≤ rcW N z h := by
  unfold rcW
  exact List.sum_le_sum fun e _ => ew_mono N hgh e

/-! ### Point decomposition -/

variable [DecidableEq E]

/-- `g` restricted to the point `p`. -/
def dlt (p : E) (g : E → ℝ) : E → ℝ := fun w => if w = p then g w else 0

theorem rcW_eq_sum_dlt (N : ℕ) (z : List E) (S : Finset E) (hS : riemannPts N z ⊆ ↑S)
    (g : E → ℝ) : rcW N z g = ∑ p ∈ S, rcW N z (dlt p g) := by
  rw [← rcW_finset_sum]
  refine rcW_congr N z fun w hw => ?_
  have hwS : w ∈ S := hS hw
  simp only [dlt]
  rw [Finset.sum_ite_eq]
  simp [hwS]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem dlt_eq_mul (p : E) (g : E → ℝ) : dlt p g = fun w => g p * dlt p (fun _ => 1) w := by
  funext w
  simp only [dlt]
  split_ifs with h
  · subst h; ring
  · ring

theorem rcW_dlt (N : ℕ) (z : List E) (p : E) (g : E → ℝ) :
    rcW N z (dlt p g) = g p * rcW N z (dlt p fun _ => 1) := by
  rw [dlt_eq_mul p g, rcW_const_mul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem dlt_one_nonneg (p w : E) : 0 ≤ dlt p (fun _ => (1 : ℝ)) w := by
  simp only [dlt]
  split_ifs <;> norm_num

end Riemann

/-! ## Riemann costs (from `LowerAssemblyAux1`) -/

section Cost

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem riemannCost_nonneg (ζ : ℝ) (N : ℕ) (z : List E) (φ : E → ℝ) :
    0 ≤ riemannCost ζ N z φ := by
  rw [riemannCost_eq_rcW]
  exact rcW_nonneg N z fun _ => (Real.exp_pos _).le

theorem riemannCost_congr (ζ : ℝ) (N : ℕ) (z : List E) {φ ψ : E → ℝ}
    (h : ∀ p ∈ riemannPts N z, φ p = ψ p) : riemannCost ζ N z φ = riemannCost ζ N z ψ := by
  rw [riemannCost_eq_rcW, riemannCost_eq_rcW]
  exact rcW_congr N z fun p hp => by rw [h p hp]

theorem riemannCost_le_exp_mul (ζ : ℝ) (hζ : 0 ≤ ζ) (N : ℕ) (z : List E) {φ ψ : E → ℝ}
    (T : ℝ) (h : ∀ p ∈ riemannPts N z, φ p ≤ ψ p + T) :
    riemannCost ζ N z φ ≤ Real.exp (ζ * T) * riemannCost ζ N z ψ := by
  unfold riemannCost
  rw [← List.sum_map_mul_left]
  refine List.sum_le_sum fun e he => ?_
  have hterm : ∀ l ∈ Finset.range N,
      Real.exp (ζ * φ (e.1 + ((l : ℝ) / N) • (e.2 - e.1))) ≤
        Real.exp (ζ * T) * Real.exp (ζ * ψ (e.1 + ((l : ℝ) / N) • (e.2 - e.1))) := by
    intro l hl
    rw [← Real.exp_add, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_left (h _ ⟨e, he, l, Finset.mem_range.1 hl, rfl⟩) hζ
    linarith
  calc ‖e.2 - e.1‖ * ((1 : ℝ) / N) *
        ∑ l ∈ Finset.range N, Real.exp (ζ * φ (e.1 + ((l : ℝ) / N) • (e.2 - e.1)))
      ≤ ‖e.2 - e.1‖ * ((1 : ℝ) / N) * ∑ l ∈ Finset.range N,
          Real.exp (ζ * T) * Real.exp (ζ * ψ (e.1 + ((l : ℝ) / N) • (e.2 - e.1))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
          (mul_nonneg (norm_nonneg _) (by positivity))
    _ = Real.exp (ζ * T) * (‖e.2 - e.1‖ * ((1 : ℝ) / N) * ∑ l ∈ Finset.range N,
          Real.exp (ζ * ψ (e.1 + ((l : ℝ) / N) • (e.2 - e.1)))) := by
        rw [← Finset.mul_sum]
        ring

variable [DecidableEq E]

/-- Extension by zero of a vector indexed by a finite set of points. -/
def extS (S : Finset E) (v : S → ℝ) (z : E) : ℝ :=
  if hz : z ∈ S then v ⟨z, hz⟩ else 0

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem extS_of_mem {S : Finset E} (v : S → ℝ) {z : E} (hz : z ∈ S) :
    extS S v z = v ⟨z, hz⟩ := by
  simp [extS, hz]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem continuous_extS_apply (S : Finset E) (z : E) :
    Continuous fun v : S → ℝ => extS S v z := by
  by_cases hz : z ∈ S
  · simp only [extS, hz, dite_true]
    exact continuous_apply _
  · simp only [extS, hz, dite_false]
    exact continuous_const

/-- The Riemann cost is continuous in the finitely many field values it reads. -/
theorem continuous_riemannCost_extS (ζ : ℝ) (N : ℕ) (z : List E) (S : Finset E) :
    Continuous fun v : S → ℝ => riemannCost ζ N z (extS S v) := by
  unfold riemannCost
  refine continuous_list_sum _ fun e _ => ?_
  refine continuous_const.mul (continuous_finsetSum _ fun l _ => ?_)
  exact (continuous_const.mul (continuous_extS_apply S _)).rexp

end Cost

/-! ## Similarities -/

section Sim

variable {d : ℕ}

theorem ew_app (N : ℕ) (g : Rd d → ℝ) (S : SimD d) (e : Rd d × Rd d) :
    ew N g (S.app e.1, S.app e.2) = |S.r| * ew N (fun w => g (S.app w)) e := by
  unfold ew
  simp only
  rw [SimD.norm_app_sub]
  have h : ∀ l : ℕ, S.app e.1 + ((l : ℝ) / N) • (S.app e.2 - S.app e.1) =
      S.app (e.1 + ((l : ℝ) / N) • (e.2 - e.1)) := fun l =>
    (SimD.app_add_smul_sub S e.1 e.2 _).symm
  simp_rw [h]
  ring

/-- `rcW N (S z) g = |r| rcW N z (g ∘ S)`. -/
theorem rcW_map_app (N : ℕ) (z : List (Rd d)) (S : SimD d) (g : Rd d → ℝ) :
    rcW N (z.map S.app) g = |S.r| * rcW N z (fun w => g (S.app w)) := by
  unfold rcW
  rw [edges_map, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  exact ew_app N g S e

/-- Riemann points of the edge `(S 0, S e₁)` are the points `S((l/N) e₁)`. -/
theorem ew_edge_pt (S : SimD d) (N l : ℕ) :
    S.app 0 + ((l : ℝ) / N) • (S.app (e₁ d) - S.app 0) = S.app (((l : ℝ) / N) • e₁ d) := by
  have := SimD.app_add_smul_sub S 0 (e₁ d) ((l : ℝ) / N)
  rw [zero_add, sub_zero] at this
  exact this.symm

theorem riemannPts_map_app (N : ℕ) (z : List (Rd d)) (S : SimD d) :
    riemannPts N (z.map S.app) = S.app '' riemannPts N z := by
  ext p
  constructor
  · rintro ⟨e', he', l, hl, rfl⟩
    rw [edges_map, List.mem_map] at he'
    obtain ⟨e, he, rfl⟩ := he'
    exact ⟨e.1 + ((l : ℝ) / N) • (e.2 - e.1), ⟨e, he, l, hl, rfl⟩,
      (SimD.app_add_smul_sub S e.1 e.2 _)⟩
  · rintro ⟨q, ⟨e, he, l, hl, rfl⟩, rfl⟩
    refine ⟨(S.app e.1, S.app e.2), ?_, l, hl, (SimD.app_add_smul_sub S e.1 e.2 _)⟩
    rw [edges_map, List.mem_map]
    exact ⟨e, he, rfl⟩

end Sim

end HigherDimLFPP.Lower
