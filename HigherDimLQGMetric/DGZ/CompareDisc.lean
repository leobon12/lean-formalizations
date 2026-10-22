import HigherDimLQGMetric.DGZ.Bypass
import HigherDimLQGMetric.DGZ.Discretize

/-!
# DGZ Lemma 5.12(1): lengths outside the cover (packet L4c)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 5.12(1) (TeX l. 2602–2668), as corrected
by the planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) **D-5.12** (gap G13)
and blueprint Part C, `r2:lem:512`.

**Statement** (`lemma512`, deterministic). Let `s > 0` with `s N = 2` (`N ∈ ℕ`), `U` an open set
that is *saturated* on the lattice `s ℤ^d` (a lattice point of `U` carries its whole open `s`-box
inside `U`), and assume, at every lattice point `w` with `B_s(w) ⊆ B₂(0)` and `w ∉ U`:
(A″) `|φ - φ'| ≤ L + 1` on `B̄_{2s}(w)`, and (C) `T < D[ψ - φ](across B̄_{2s}(w) \ B_s(w))`.
Then every piecewise `C¹` path `γ` in `B₂(0)` from `x` to `y` with `y ∉ B̄_{4s}(x)` can be
replaced by a polygonal path `γ'` in `B₂(0)` with the same endpoints and
`len_{B₂(0) \ U}(γ'; φ) ≤ C_L (s/T) len(γ; ψ)`, `C_L = 4√d·41^d e^{2ξ(L+1)}` (`lemma512Const`).

In DGZ's application `s = 2^{-n}`, `φ = h_n`, `ψ = h_{n+k}`, `T = L⁻¹ 2^{-n-(1-ξQ+ε)k}` and `U = 𝒰`
is the cover of Proposition 5.10, so `s/T = L 2^{(1-ξQ+ε)k}`.

**Proof** (D-5.12, one global discretization; G13). (b) L3a2's discretization (open variant,
mesh `s`, box `B₂(0)`) gives a loop-free L-path of sites `f 0, …, f (M-1)` whose open `s`-boxes
lie in `B₂(0)` and meet `γ`, with `γ 0 ∈ B_s(s f 0)`, `γ 1 ∈ B_s(s f (M-1))`; `γ'` is the
polygon `x, s f 0, …, s f (M-1), y`. (a), (c) An edge all of whose end sites lie in `U` lies in `U`
(saturation, and an edge between L-adjacent sites lies in the two open boxes); any other edge lies
in `B̄_s(c)` for an end site `c ∉ U`, where `φ ≤ φ(c) + L + 1` (A″), so its `φ`-length is
`≤ 2√d s e^{ξ(φ(c)+L+1)}`; every site is an end of two edges. (d) At a site `c ∉ U`, `γ` meets
`B_s(c)` and leaves `B_{2s}(c)` (its endpoints are `> 4s` apart), so it crosses the shell
`B̄_{2s}(c) \ B_s(c)`: by (A″) and (C), `e^{ξ(φ(c)-L-1)} T ≤ len_{shell}(γ; ψ)`; the shells of
distinct sites cover each point at most `41^d` times (L4b2's packing lemma).

This differs from the blueprint's constant `(2+√d)5^d L e^{2ξ(L+1)}` only by the bookkeeping
(edge lengths `≤ 2√d s`, multiplicity `41^d`); the constant is internal to packet L4c.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## Geometry of boxes and edges -/

/-- Closed `ℓ^∞` boxes are convex. -/
theorem cmp_convex_cbox (c : Rd d) (r : ℝ) : Convex ℝ (cbox c r) := by
  intro z hz w hw a b ha hb hab i
  have e : (a • z + b • w) i - c i = a * (z i - c i) + b * (w i - c i) := by
    have : (a • z + b • w) i = a * z i + b * w i := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [this]
    have hc : c i = (a + b) * c i := by rw [hab, one_mul]
    linarith [hc]
  show |(a • z + b • w) i - c i| ≤ r
  rw [e]
  calc |a * (z i - c i) + b * (w i - c i)| ≤ |a * (z i - c i)| + |b * (w i - c i)| :=
        abs_add_le _ _
    _ = a * |z i - c i| + b * |w i - c i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * r + b * r :=
        add_le_add (mul_le_mul_of_nonneg_left (hz i) ha) (mul_le_mul_of_nonneg_left (hw i) hb)
    _ = r := by rw [← add_mul, hab, one_mul]

/-- A point of the edge `[a, b]` with `|b - a|_∞ ≤ s` lies in `B_s(a)` or equals `b`. -/
theorem cmp_segPath_mem_obox_or_eq {a b : Rd d} {s : ℝ} (hs : 0 < s)
    (hab : ∀ k, |b k - a k| ≤ s) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    segPath a b u ∈ obox a s ∨ segPath a b u = b := by
  rcases hu.2.lt_or_eq with hu1 | hu1
  · left
    intro k
    have e : (segPath a b u) k - a k = u * (b k - a k) := by
      simp only [segPath, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      ring
    rw [e, abs_mul, abs_of_nonneg hu.1]
    calc u * |b k - a k| ≤ u * s := mul_le_mul_of_nonneg_left (hab k) hu.1
      _ < s := mul_lt_of_lt_one_left hs hu1
  · right
    rw [hu1, segPath_one]

/-- Two L-adjacent lattice points are within `s` of each other in every coordinate. -/
theorem cmp_abs_latPt_sub_le_of_lAdj {s : ℝ} (hs : 0 ≤ s) {u v : Zd d} (h : LAdj u v) (k : Fin d) :
    |latPt s v k - latPt s u k| ≤ s := by
  have h1 : |(v k : ℝ) - u k| ≤ 1 := by
    have := (HigherDimLFPP.Perc.LAdj.withinInf h) k
    rw [abs_sub_comm] at this
    exact_mod_cast this
  rw [latPt_apply, latPt_apply, ← mul_sub, abs_mul, abs_of_nonneg hs]
  calc s * |(v k : ℝ) - u k| ≤ s * 1 := mul_le_mul_of_nonneg_left h1 hs
    _ = s := mul_one s

/-- Distinct lattice points are at `ℓ^∞` distance at least `s`, hence not within `s/10`. -/
theorem cmp_latPt_not_mem_cbox {s : ℝ} (hs : 0 < s) {u v : Zd d} (h : u ≠ v) :
    latPt s v ∉ cbox (latPt s u) (s / 10) := by
  intro hv
  apply h
  funext k
  have hk := hv k
  rw [latPt_apply, latPt_apply, ← mul_sub, abs_mul, abs_of_pos hs] at hk
  have h1 : |(v k : ℝ) - u k| < 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h2 : |v k - u k| < 1 := by exact_mod_cast h1
  have h3 : v k - u k = 0 := by
    rcases abs_lt.1 h2 with ⟨h4, h5⟩
    omega
  omega

/-! ## The discretization in function form -/

/-- **D-DISC in function form** (L3a2's `exists_discretization` with `c = 0`): a loop-free
L-path of sites `f 0, …, f (M-1)` whose open `s`-boxes lie in `B_{sN}(0)` and meet `γ`, the
first containing `γ 0` and the last `γ 1`. -/
theorem cmp_exists_disc {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) {γ : ℝ → Rd d}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγB : MapsTo γ (Icc 0 1) (obox (0 : Rd d) (s * N))) :
    ∃ (M : ℕ) (f : ℕ → Zd d), 1 ≤ M ∧ (∀ i < M, ∀ j < M, f i = f j → i = j) ∧
      (∀ i, i + 1 < M → LAdj (f i) (f (i + 1))) ∧
      γ 0 ∈ obox (latPt s (f 0)) s ∧ γ 1 ∈ obox (latPt s (f (M - 1))) s ∧
      ∀ i < M, obox (latPt s (f i)) s ⊆ obox (0 : Rd d) (s * N) ∧
        ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ obox (latPt s (f i)) s := by
  have hB' : MapsTo γ (Icc 0 1) (obox (latPt s (0 : Zd d)) (s * N)) := by
    rwa [HigherDimLFPP.DGZ.latPt_zero]
  obtain ⟨l, x₀, x₁, hnd, hch, hhd, hlast, h0, h1, hl⟩ :=
    exists_discretization hs 0 hN zero_le_one hγc hB'
  have hne : l ≠ [] := by
    rintro rfl
    simp at hhd
  have hlen : 0 < l.length := List.length_pos_of_ne_nil hne
  have hx₀ : l.getD 0 0 = x₀ := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_some_iff] at hhd
    obtain ⟨h, hx⟩ := hhd
    rw [List.getD_eq_getElem _ _ h, hx]
  have hx₁ : l.getD (l.length - 1) 0 = x₁ := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_some_iff] at hlast
    obtain ⟨h, hx⟩ := hlast
    rw [List.getD_eq_getElem _ _ h, hx]
  refine ⟨l.length, fun i => l.getD i 0, hlen, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    simp only at hij
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at hij
    exact hnd.getElem_inj_iff.1 hij
  · intro i hi
    simp only
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
    exact List.isChain_iff_getElem.1 hch i hi
  · simp only
    rw [hx₀]
    exact h0
  · simp only
    rw [hx₁]
    exact h1
  · intro i hi
    have hmem : l.getD i 0 ∈ l := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    obtain ⟨-, hsub, t, ht, hγt⟩ := hl _ hmem
    rw [HigherDimLFPP.DGZ.latPt_zero] at hsub
    exact ⟨hsub, t, ht, hγt⟩

/-! ## One edge -/

/-- **(c) of D-5.12 for one edge**: an edge `[a, b]` inside `B̄_s(c)`, where (A″) holds on
`B̄_{2s}(c)`, has (restricted) `φ`-length at most `2√d s e^{ξ(φ(c) + L + 1)}`. -/
theorem cmp_edge_le {ξ : ℝ} (hξ : 0 ≤ ξ) {φ : Rd d → ℝ} (hφ : Continuous φ) {s L : ℝ}
    (hs : 0 ≤ s) {c a b : Rd d} (ha : a ∈ cbox c s) (hb : b ∈ cbox c s)
    (hA : ∀ v ∈ cbox c (2 * s), ∀ v' ∈ cbox c (2 * s), |φ v - φ v'| ≤ L + 1)
    (S : Set (Rd d)) :
    lfppLengthIn ξ φ (segPath a b) S ≤ 2 * √d * s * Real.exp (ξ * (φ c + L + 1)) := by
  have hsub : cbox c s ⊆ cbox c (2 * s) := fun z hz i => (hz i).trans (by linarith)
  have hc : c ∈ cbox c (2 * s) := fun i => by
    show |c i - c i| ≤ 2 * s
    rw [sub_self, abs_zero]
    linarith
  have hB : ∀ u ∈ Icc (0 : ℝ) 1,
      Real.exp (ξ * φ (segPath a b u)) ≤ Real.exp (ξ * (φ c + L + 1)) := by
    intro u hu
    have hmem : segPath a b u ∈ cbox c s :=
      mapsTo_segPath (cmp_convex_cbox c s) ha hb hu
    have h1 := hA _ (hsub hmem) c hc
    have h2 : φ (segPath a b u) ≤ φ c + L + 1 := by
      have := le_abs_self (φ (segPath a b u) - φ c)
      linarith
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h2 hξ)
  have hnorm : ‖b - a‖ ≤ √d * (2 * s) := norm_sub_le_of_mem_cbox hb ha
  calc lfppLengthIn ξ φ (segPath a b) S ≤ lfppLength ξ φ (segPath a b) :=
        lfppLengthIn_le_lfppLength hφ (isPcwC1Path_segPath a b)
    _ ≤ Real.exp (ξ * (φ c + L + 1)) * ‖b - a‖ := lfppLength_segPath_le hφ a b hB
    _ ≤ Real.exp (ξ * (φ c + L + 1)) * (√d * (2 * s)) :=
        mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
    _ = 2 * √d * s * Real.exp (ξ * (φ c + L + 1)) := by ring

/-- An edge inside `U` has zero length in `B₂(0) \ U`. -/
theorem cmp_edge_zero {ξ : ℝ} {φ : Rd d → ℝ} {V U : Set (Rd d)} {a b : Rd d}
    (h : MapsTo (segPath a b) (Icc 0 1) U) : lfppLengthIn ξ φ (segPath a b) (V \ U) = 0 :=
  lfppLengthIn_eq_zero_of_mapsTo_compl fun _u hu hmem => hmem.2 (h hu)

/-! ## One site -/

/-- **(d) of D-5.12 at one site**: if `γ` meets `B̄_s(c)` and leaves `B_{2s}(c)`, then
`e^{ξ(φ(c) - L - 1)} T ≤ len_{B̄_{2s}(c) \ B_s(c)}(γ; ψ)`, by (A″) on `B̄_{2s}(c)` and (C). -/
theorem cmp_site_le {ξ : ℝ} (hξ : 0 ≤ ξ) {φ ψ : Rd d → ℝ} (hφ : Continuous φ)
    (hψ : Continuous ψ) {s L T : ℝ} (hs : 0 < s) {c : Rd d}
    (hA : ∀ v ∈ cbox c (2 * s), ∀ v' ∈ cbox c (2 * s), |φ v - φ v'| ≤ L + 1)
    (hC : T < acrossDist ξ (fun v => ψ v - φ v) c (2 * s) s)
    {γ : ℝ → Rd d} {x y : Rd d} (hγ : IsPcwC1Path γ x y) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hin : γ a ∈ cbox c s) (hout : γ b ∉ obox c (2 * s)) :
    Real.exp (ξ * (φ c - L - 1)) * T ≤ lfppLengthIn ξ ψ γ (cbox c (2 * s) \ obox c s) := by
  have hψφ : Continuous fun v => ψ v - φ v := hψ.sub hφ
  have hshell : MeasurableSet (cbox c (2 * s) \ obox c s) :=
    (HigherDimLFPP.DGZ.isClosed_cbox c (2 * s)).measurableSet.diff
      (HigherDimLFPP.DGZ.isOpen_obox c s).measurableSet
  have hc : c ∈ cbox c (2 * s) := fun i => by
    show |c i - c i| ≤ 2 * s
    rw [sub_self, abs_zero]
    linarith
  have h1 : acrossDist ξ (fun v => ψ v - φ v) c (2 * s) s ≤
      lfppLengthIn ξ (fun v => ψ v - φ v) γ (cbox c (2 * s) \ obox c s) :=
    acrossDist_le_of_crossing (φ := fun v => ψ v - φ v) hψφ (by linarith) hγ ha hb hin hout
  have h2 : lfppLengthIn ξ (fun v => ψ v - φ v) γ (cbox c (2 * s) \ obox c s) ≤
      Real.exp (-(ξ * (φ c - L - 1))) * lfppLengthIn ξ ψ γ (cbox c (2 * s) \ obox c s) := by
    refine lfppLengthIn_le_mul_of_exp_le (φ := fun v => ψ v - φ v) hψφ hψ hγ hshell ?_
    intro z hz
    have hA' := hA z hz.1 c hc
    have h3 : φ c - φ z ≤ L + 1 := by
      have := neg_abs_le (φ z - φ c)
      linarith
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h4 : ξ * (φ c - φ z) ≤ ξ * (L + 1) := mul_le_mul_of_nonneg_left h3 hξ
    nlinarith
  have hT : T ≤ Real.exp (-(ξ * (φ c - L - 1))) * lfppLengthIn ξ ψ γ (cbox c (2 * s) \ obox c s) :=
    (hC.le.trans h1).trans h2
  have hE : 0 < Real.exp (ξ * (φ c - L - 1)) := Real.exp_pos _
  calc Real.exp (ξ * (φ c - L - 1)) * T ≤ Real.exp (ξ * (φ c - L - 1)) *
        (Real.exp (-(ξ * (φ c - L - 1))) * lfppLengthIn ξ ψ γ (cbox c (2 * s) \ obox c s)) :=
        mul_le_mul_of_nonneg_left hT hE.le
    _ = lfppLengthIn ξ ψ γ (cbox c (2 * s) \ obox c s) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-! ## The polygon through the sites -/

/-- The vertices `x, c 0, …, c (M-1), y` of the discretized path (`i = 0, 1, …, M + 1`). -/
def cmpVertex (x y : Rd d) (c : ℕ → Rd d) (M i : ℕ) : Rd d :=
  if i = 0 then x else if i ≤ M then c (i - 1) else y

theorem cmpVertex_zero (x y : Rd d) (c : ℕ → Rd d) (M : ℕ) : cmpVertex x y c M 0 = x := by
  simp [cmpVertex]

theorem cmpVertex_of_le (x y : Rd d) (c : ℕ → Rd d) {M i : ℕ} (hi : 1 ≤ i) (hiM : i ≤ M) :
    cmpVertex x y c M i = c (i - 1) := by
  unfold cmpVertex
  rw [ite_eq_right (by omega), ite_eq_left hiM]

theorem cmpVertex_succ (x y : Rd d) (c : ℕ → Rd d) (M : ℕ) : cmpVertex x y c M (M + 1) = y := by
  unfold cmpVertex
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The charge of the site `j`: `e^{ξ(φ(c j) + L + 1)}` if `j < M` and `c j ∉ U`, else `0`. -/
def cmpCharge (ξ : ℝ) (φ : Rd d → ℝ) (L : ℝ) (U : Set (Rd d)) (c : ℕ → Rd d) (M : ℕ) : ℕ → ℝ :=
  Set.indicator {j : ℕ | j < M ∧ c j ∉ U} fun j => Real.exp (ξ * (φ (c j) + L + 1))

theorem cmpCharge_nonneg (ξ : ℝ) (φ : Rd d → ℝ) (L : ℝ) (U : Set (Rd d)) (c : ℕ → Rd d)
    (M j : ℕ) : 0 ≤ cmpCharge ξ φ L U c M j :=
  Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) j

theorem cmpCharge_of_mem {ξ : ℝ} {φ : Rd d → ℝ} {L : ℝ} {U : Set (Rd d)} {c : ℕ → Rd d}
    {M j : ℕ} (hj : j < M) (hc : c j ∉ U) :
    cmpCharge ξ φ L U c M j = Real.exp (ξ * (φ (c j) + L + 1)) :=
  Set.indicator_of_mem (show j ∈ {j : ℕ | j < M ∧ c j ∉ U} from ⟨hj, hc⟩) _

theorem cmpCharge_of_ge {ξ : ℝ} {φ : Rd d → ℝ} {L : ℝ} {U : Set (Rd d)} {c : ℕ → Rd d}
    {M j : ℕ} (hj : M ≤ j) : cmpCharge ξ φ L U c M j = 0 :=
  Set.indicator_of_notMem (show j ∉ {j : ℕ | j < M ∧ c j ∉ U} from fun h => by
    have := h.1
    omega) _

theorem cmpCharge_of_mem_U {ξ : ℝ} {φ : Rd d → ℝ} {L : ℝ} {U : Set (Rd d)} {c : ℕ → Rd d}
    {M j : ℕ} (hc : c j ∈ U) : cmpCharge ξ φ L U c M j = 0 :=
  Set.indicator_of_notMem (show j ∉ {j : ℕ | j < M ∧ c j ∉ U} from fun h => h.2 hc) _

/-- **One edge of the polygon** (D-5.12 (a), (c)): edge `i` of `x, c 0, …, c (M-1), y` has
restricted length at most `2√d s (g(i-1) + g(i))`, `g` the charges (`g(-1) := 0`). -/
theorem cmp_edge_poly_le {ξ : ℝ} (hξ : 0 ≤ ξ) {φ : Rd d → ℝ} (hφ : Continuous φ) {s L : ℝ}
    (hs : 0 < s) {U V : Set (Rd d)} {x y : Rd d} {c : ℕ → Rd d} {M : ℕ} (hM : 1 ≤ M)
    (hx : x ∈ obox (c 0) s) (hy : y ∈ obox (c (M - 1)) s)
    (hadj : ∀ j, j + 1 < M → ∀ k, |c (j + 1) k - c j k| ≤ s)
    (hU : ∀ j < M, c j ∈ U → obox (c j) s ⊆ U)
    (hA : ∀ j < M, c j ∉ U →
      ∀ v ∈ cbox (c j) (2 * s), ∀ v' ∈ cbox (c j) (2 * s), |φ v - φ v'| ≤ L + 1)
    {i : ℕ} (hi : i < M + 1) :
    lfppLengthIn ξ φ (segPath (cmpVertex x y c M i) (cmpVertex x y c M (i + 1))) (V \ U) ≤
      2 * √d * s * ((if i = 0 then 0 else cmpCharge ξ φ L U c M (i - 1)) +
        cmpCharge ξ φ L U c M i) := by
  have hB : 0 ≤ 2 * √d * s := by positivity
  have hg : ∀ j, 0 ≤ cmpCharge ξ φ L U c M j := cmpCharge_nonneg ξ φ L U c M
  have hcen : ∀ j, c j ∈ obox (c j) s := fun j => HigherDimLFPP.DGZ.mem_obox_self _ hs
  have hocb : ∀ j, obox (c j) s ⊆ cbox (c j) s := fun j => HigherDimLFPP.DGZ.obox_subset_cbox _ _
  have hRHS : 0 ≤ 2 * √d * s * ((if i = 0 then 0 else cmpCharge ξ φ L U c M (i - 1)) +
      cmpCharge ξ φ L U c M i) := by
    refine mul_nonneg hB (add_nonneg ?_ (hg i))
    split_ifs
    · exact le_rfl
    · exact hg _
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · -- the first edge `[x, c 0]`
    rw [cmpVertex_zero, zero_add, cmpVertex_of_le x y c le_rfl hM, Nat.sub_self]
    simp only [ite_true, zero_add]
    by_cases hc0 : c 0 ∈ U
    · have hseg : MapsTo (segPath x (c 0)) (Icc 0 1) U :=
        (mapsTo_segPath (HigherDimLFPP.DGZ.convex_obox (c 0) s) hx (hcen 0)).mono_right
          (hU 0 (by omega) hc0)
      rw [cmp_edge_zero hseg]
      exact mul_nonneg hB (hg 0)
    · rw [cmpCharge_of_mem (by omega) hc0]
      exact cmp_edge_le hξ hφ hs.le (hocb 0 hx) (hocb 0 (hcen 0)) (hA 0 (by omega) hc0) _
  · rw [ite_eq_right (by omega)]
    rcases Nat.lt_or_ge i M with hiM | hiM
    · -- an inner edge `[c (i-1), c i]`
      rw [cmpVertex_of_le x y c hipos hiM.le, cmpVertex_of_le x y c (by omega) (by omega),
        Nat.add_sub_cancel]
      have hadj' : ∀ k, |c i k - c (i - 1) k| ≤ s := by
        have := hadj (i - 1) (by omega)
        rwa [Nat.sub_add_cancel hipos] at this
      have hadj'' : ∀ k, |c (i - 1) k - c i k| ≤ s := fun k => by
        rw [abs_sub_comm]
        exact hadj' k
      have hci : c i ∈ cbox (c (i - 1)) s := fun k => hadj' k
      have hci' : c (i - 1) ∈ cbox (c i) s := fun k => hadj'' k
      by_cases hl : c (i - 1) ∈ U
      · by_cases hr : c i ∈ U
        · have hseg : MapsTo (segPath (c (i - 1)) (c i)) (Icc 0 1) U := by
            intro u hu
            rcases cmp_segPath_mem_obox_or_eq hs hadj' hu with h | h
            · exact hU (i - 1) (by omega) hl h
            · rw [h]
              exact hr
          rw [cmp_edge_zero hseg]
          exact mul_nonneg hB (add_nonneg (hg _) (hg _))
        · calc _ ≤ 2 * √d * s * Real.exp (ξ * (φ (c i) + L + 1)) :=
                cmp_edge_le hξ hφ hs.le hci' (hocb i (hcen i)) (hA i hiM hr) _
            _ = 2 * √d * s * cmpCharge ξ φ L U c M i := by rw [cmpCharge_of_mem hiM hr]
            _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hg _)) hB
      · calc _ ≤ 2 * √d * s * Real.exp (ξ * (φ (c (i - 1)) + L + 1)) :=
              cmp_edge_le hξ hφ hs.le (hocb _ (hcen _)) hci (hA (i - 1) (by omega) hl) _
          _ = 2 * √d * s * cmpCharge ξ φ L U c M (i - 1) := by
              rw [cmpCharge_of_mem (by omega) hl]
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hg _)) hB
    · -- the last edge `[c (M-1), y]`
      have hiM' : i = M := by omega
      subst hiM'
      rw [cmpVertex_of_le x y c hipos le_rfl, cmpVertex_succ, cmpCharge_of_ge (le_refl i),
        add_zero]
      by_cases hc : c (i - 1) ∈ U
      · have hseg : MapsTo (segPath (c (i - 1)) y) (Icc 0 1) U :=
          (mapsTo_segPath (HigherDimLFPP.DGZ.convex_obox (c (i - 1)) s) (hcen _) hy).mono_right
            (hU (i - 1) (by omega) hc)
        rw [cmp_edge_zero hseg]
        exact mul_nonneg hB (hg _)
      · rw [cmpCharge_of_mem (by omega) hc]
        exact cmp_edge_le hξ hφ hs.le (hocb _ (hcen _)) (hocb _ hy) (hA (i - 1) (by omega) hc) _

/-- **The edges together** (D-5.12 (c)): the restricted length of the polygon is at most
`4√d s Σ_{j<M} g(j)`. -/
theorem cmp_polygon_le {ξ : ℝ} (hξ : 0 ≤ ξ) {φ : Rd d → ℝ} (hφ : Continuous φ) {s L : ℝ}
    (hs : 0 < s) {U V : Set (Rd d)} (hUV : MeasurableSet (V \ U)) {x y : Rd d} {c : ℕ → Rd d}
    {M : ℕ} (hM : 1 ≤ M) (hx : x ∈ obox (c 0) s) (hy : y ∈ obox (c (M - 1)) s)
    (hadj : ∀ j, j + 1 < M → ∀ k, |c (j + 1) k - c j k| ≤ s)
    (hU : ∀ j < M, c j ∈ U → obox (c j) s ⊆ U)
    (hA : ∀ j < M, c j ∉ U →
      ∀ v ∈ cbox (c j) (2 * s), ∀ v' ∈ cbox (c j) (2 * s), |φ v - φ v'| ≤ L + 1) :
    lfppLengthIn ξ φ (polygonPath (cmpVertex x y c M) (M + 1)) (V \ U) ≤
      4 * √d * s * ∑ j ∈ Finset.range M, cmpCharge ξ φ L U c M j := by
  rw [lfppLengthIn_polygonPath hφ hUV]
  have hsum := Finset.sum_le_sum fun i (hi : i ∈ Finset.range (M + 1)) =>
    cmp_edge_poly_le hξ hφ hs (V := V) hM hx hy hadj hU hA (Finset.mem_range.1 hi)
  refine hsum.trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_range_succ',
    Finset.sum_range_succ (fun i => cmpCharge ξ φ L U c M i), cmpCharge_of_ge (le_refl M)]
  simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, ite_true, add_zero]
  ring

/-! ## The sites -/

/-- **(d) of D-5.12 summed over the sites**: `Σ_{j<M} g(j) ≤ 41^d e^{2ξ(L+1)} T⁻¹ len(γ; ψ)`. -/
theorem cmp_sites_le {ξ : ℝ} (hξ : 0 ≤ ξ) {φ ψ : Rd d → ℝ} (hφ : Continuous φ)
    (hψ : Continuous ψ) {s L T : ℝ} (hs : 0 < s) (hT : 0 < T) {U : Set (Rd d)} {M : ℕ}
    {f : ℕ → Zd d} (hinj : ∀ i < M, ∀ j < M, f i = f j → i = j)
    (hA : ∀ j < M, latPt s (f j) ∉ U →
      (∀ v ∈ cbox (latPt s (f j)) (2 * s), ∀ v' ∈ cbox (latPt s (f j)) (2 * s),
        |φ v - φ v'| ≤ L + 1) ∧
      T < acrossDist ξ (fun v => ψ v - φ v) (latPt s (f j)) (2 * s) s)
    {γ : ℝ → Rd d} {x y : Rd d} (hγ : IsPcwC1Path γ x y)
    (hmeet : ∀ j < M, ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ obox (latPt s (f j)) s)
    (hxy : y ∉ cbox x (4 * s)) :
    ∑ j ∈ Finset.range M, cmpCharge ξ φ L U (fun j => latPt s (f j)) M j ≤
      (41 : ℝ) ^ d * Real.exp (2 * ξ * (L + 1)) / T * lfppLength ξ ψ γ := by
  classical
  set c : ℕ → Rd d := fun j => latPt s (f j) with hcdef
  set S : ℕ → Set (Rd d) := fun j => cbox (c j) (2 * s) \ obox (c j) s with hSdef
  have hE : 0 ≤ Real.exp (2 * ξ * (L + 1)) / T := (div_pos (Real.exp_pos _) hT).le
  -- each charge is controlled by the length of `γ` in the shell of its site
  have hsite : ∀ j ∈ Finset.range M, cmpCharge ξ φ L U c M j ≤
      Real.exp (2 * ξ * (L + 1)) / T * lfppLengthIn ξ ψ γ (S j) := by
    intro j hj
    have hjM := Finset.mem_range.1 hj
    by_cases hcU : c j ∈ U
    · rw [cmpCharge_of_mem_U hcU]
      exact mul_nonneg hE (lfppLengthIn_nonneg _ _ _ _)
    · rw [cmpCharge_of_mem hjM hcU]
      obtain ⟨hA'', hC⟩ := hA j hjM hcU
      obtain ⟨t, ht, hγt⟩ := hmeet j hjM
      have hout : γ 0 ∉ obox (c j) (2 * s) ∨ γ 1 ∉ obox (c j) (2 * s) := by
        by_contra hcon
        push Not at hcon
        obtain ⟨h0, h1⟩ := hcon
        rw [hγ.source] at h0
        rw [hγ.target] at h1
        refine hxy fun k => ?_
        have e1 := h0 k
        have e2 := h1 k
        calc |y k - x k| = |(y k - c j k) - (x k - c j k)| := by ring_nf
          _ ≤ |y k - c j k| + |x k - c j k| := abs_sub _ _
          _ ≤ 4 * s := by linarith
      have hin : γ t ∈ cbox (c j) s := HigherDimLFPP.DGZ.obox_subset_cbox _ _ hγt
      have key : Real.exp (ξ * (φ (c j) - L - 1)) * T ≤ lfppLengthIn ξ ψ γ (S j) := by
        rcases hout with hb | hb
        · exact cmp_site_le hξ hφ hψ hs hA'' hC hγ ht ⟨le_rfl, zero_le_one⟩ hin hb
        · exact cmp_site_le hξ hφ hψ hs hA'' hC hγ ht ⟨zero_le_one, le_rfl⟩ hin hb
      have e : Real.exp (ξ * (φ (c j) + L + 1)) =
          Real.exp (2 * ξ * (L + 1)) * Real.exp (ξ * (φ (c j) - L - 1)) := by
        rw [← Real.exp_add]
        ring_nf
      rw [e, div_mul_eq_mul_div, le_div_iff₀ hT, mul_assoc]
      exact mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
  -- the shells of distinct sites overlap at most `41^d` times
  have hmult : ∑ j ∈ Finset.range M, lfppLengthIn ξ ψ γ (S j) ≤
      ((41 ^ d : ℕ) : ℝ) * lfppLength ξ ψ γ := by
    refine sum_lfppLengthIn_le_mul hψ hγ (Finset.range M) S (fun j _ =>
      (HigherDimLFPP.DGZ.isClosed_cbox _ _).measurableSet.diff
        (HigherDimLFPP.DGZ.isOpen_obox _ _).measurableSet) fun z => ?_
    refine card_le_forty_one_pow _ c (p := z) (a := s / 10) (by positivity) ?_ ?_
    · intro i hi i' hi' hii'
      simp only [Finset.mem_filter, Finset.mem_range] at hi hi'
      exact cmp_latPt_not_mem_cbox hs fun h => hii' (hinj i hi.1 i' hi'.1 h)
    · intro i hi
      simp only [Finset.mem_filter] at hi
      have hz' : z ∈ cbox (c i) (2 * s) := hi.2.1
      have : c i ∈ cbox z (2 * s) := mem_cbox_swap.1 hz'
      rwa [show 20 * (s / 10) = 2 * s by ring]
  calc ∑ j ∈ Finset.range M, cmpCharge ξ φ L U c M j
      ≤ ∑ j ∈ Finset.range M, Real.exp (2 * ξ * (L + 1)) / T * lfppLengthIn ξ ψ γ (S j) :=
        Finset.sum_le_sum hsite
    _ = Real.exp (2 * ξ * (L + 1)) / T * ∑ j ∈ Finset.range M, lfppLengthIn ξ ψ γ (S j) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (2 * ξ * (L + 1)) / T * (((41 ^ d : ℕ) : ℝ) * lfppLength ξ ψ γ) :=
        mul_le_mul_of_nonneg_left hmult hE
    _ = (41 : ℝ) ^ d * Real.exp (2 * ξ * (L + 1)) / T * lfppLength ξ ψ γ := by
        push_cast
        ring

/-! ## Lemma 5.12(1) -/

/-- The constant of Lemma 5.12(1) in the form proved here: `4√d·41^d·e^{2ξ(L+1)}`. -/
def lemma512Const (d : ℕ) (ξ L : ℝ) : ℝ := 4 * √(d : ℝ) * (41 : ℝ) ^ d * Real.exp (2 * ξ * (L + 1))

theorem lemma512Const_nonneg (d : ℕ) (ξ L : ℝ) : 0 ≤ lemma512Const d ξ L := by
  unfold lemma512Const
  positivity

/-- **DGZ Lemma 5.12(1)** (MA7 D-5.12, gap G13; blueprint `r2:lem:512`), deterministic: with the
site conditions (A″), (C) outside a lattice-saturated open set `U`, every piecewise `C¹` path `γ`
in `B₂(0)` from `x` to `y`, `y ∉ B̄_{4s}(x)`, is replaced by a polygonal path in `B₂(0)` with the
same endpoints whose `φ`-length outside `U` is at most `C_L (s/T) len(γ; ψ)`. -/
theorem lemma512 {ξ : ℝ} (hξ : 0 ≤ ξ) {φ ψ : Rd d → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) (hsN : s * N = 2)
    {U : Set (Rd d)} (hUo : IsOpen U) (hU : ∀ x : Zd d, latPt s x ∈ U → obox (latPt s x) s ⊆ U)
    {L T : ℝ} (hT : 0 < T)
    (hA : ∀ w : Zd d, obox (latPt s w) s ⊆ obox (0 : Rd d) 2 → latPt s w ∉ U →
      (∀ v ∈ cbox (latPt s w) (2 * s), ∀ v' ∈ cbox (latPt s w) (2 * s), |φ v - φ v'| ≤ L + 1) ∧
        T < acrossDist ξ (fun v => ψ v - φ v) (latPt s w) (2 * s) s)
    {γ : ℝ → Rd d} {x y : Rd d} (hγ : IsPcwC1Path γ x y)
    (hγB : MapsTo γ (Icc 0 1) (obox (0 : Rd d) 2)) (hxy : y ∉ cbox x (4 * s)) :
    ∃ γ' : ℝ → Rd d, IsPcwC1Path γ' x y ∧ MapsTo γ' (Icc 0 1) (obox (0 : Rd d) 2) ∧
      lfppLengthIn ξ φ γ' (obox (0 : Rd d) 2 \ U) ≤
        lemma512Const d ξ L * (s / T) * lfppLength ξ ψ γ := by
  have hγB' : MapsTo γ (Icc 0 1) (obox (0 : Rd d) (s * N)) := by
    rw [hsN]
    exact hγB
  obtain ⟨M, f, hM, hinj, hadj, h0, h1, hf⟩ := cmp_exists_disc hs hN hγ.continuousOn hγB'
  rw [hγ.source] at h0
  rw [hγ.target] at h1
  have hfB : ∀ j < M, obox (latPt s (f j)) s ⊆ obox (0 : Rd d) 2 := fun j hj => by
    have := (hf j hj).1
    rwa [hsN] at this
  set c : ℕ → Rd d := fun j => latPt s (f j) with hcdef
  have hadj' : ∀ j, j + 1 < M → ∀ k, |c (j + 1) k - c j k| ≤ s := fun j hj k =>
    cmp_abs_latPt_sub_le_of_lAdj hs.le (hadj j hj) k
  have hU' : ∀ j < M, c j ∈ U → obox (c j) s ⊆ U := fun j _ hc => hU (f j) hc
  have hA' : ∀ j < M, c j ∉ U →
      ∀ v ∈ cbox (c j) (2 * s), ∀ v' ∈ cbox (c j) (2 * s), |φ v - φ v'| ≤ L + 1 :=
    fun j hj hc => (hA (f j) (hfB j hj) hc).1
  have hUV : MeasurableSet (obox (0 : Rd d) 2 \ U) :=
    (HigherDimLFPP.DGZ.isOpen_obox _ _).measurableSet.diff hUo.measurableSet
  -- the vertices lie in `B₂(0)`
  have hx0 : x ∈ obox (0 : Rd d) 2 := by
    have := hγB ⟨le_rfl, zero_le_one⟩
    rwa [hγ.source] at this
  have hy0 : y ∈ obox (0 : Rd d) 2 := by
    have := hγB ⟨zero_le_one, le_rfl⟩
    rwa [hγ.target] at this
  have hvB : ∀ i, cmpVertex x y c M i ∈ obox (0 : Rd d) 2 := by
    intro i
    unfold cmpVertex
    split_ifs with h0' h1'
    · exact hx0
    · exact hfB (i - 1) (by omega) (HigherDimLFPP.DGZ.mem_obox_self _ hs)
    · exact hy0
  refine ⟨polygonPath (cmpVertex x y c M) (M + 1), ?_, ?_, ?_⟩
  · have := isPcwC1Path_polygonPath (cmpVertex x y c M) (M + 1)
    rwa [cmpVertex_zero, cmpVertex_succ] at this
  · exact mapsTo_polygonPath _ _ (hvB 0) fun i _ =>
      mapsTo_segPath (HigherDimLFPP.DGZ.convex_obox 0 2) (hvB i) (hvB (i + 1))
  · have hpoly := cmp_polygon_le hξ hφ hs hUV hM h0 h1 hadj' hU' hA'
    have hsites := cmp_sites_le hξ hφ hψ hs hT (U := U) hinj (fun j hj hc => hA (f j) (hfB j hj) hc)
      hγ (fun j hj => (hf j hj).2) hxy
    calc lfppLengthIn ξ φ (polygonPath (cmpVertex x y c M) (M + 1)) (obox (0 : Rd d) 2 \ U)
        ≤ 4 * √d * s * ∑ j ∈ Finset.range M, cmpCharge ξ φ L U c M j := hpoly
      _ ≤ 4 * √d * s * ((41 : ℝ) ^ d * Real.exp (2 * ξ * (L + 1)) / T * lfppLength ξ ψ γ) :=
          mul_le_mul_of_nonneg_left hsites (by positivity)
      _ = lemma512Const d ξ L * (s / T) * lfppLength ξ ψ γ := by
          unfold lemma512Const
          ring

end DGZ

end HigherDimLQGMetric
