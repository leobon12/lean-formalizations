import HigherDimLFPP.Paths.Measurable
import HigherDimLFPP.Exist.Sites

/-!
# LFPP functionals for DGZ §§4–6: definitions and basic API (packet L3b1)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), §§4–6; planning audit
`planning/audits/MA7-ref2-sections-4-6.md`, §1.1 (conventions), Details (b) (Lean infrastructure)
and Details (c) §C. The nine definitions below are copied **verbatim** (names, binders, bodies and
docstrings) from the type-checked statement surface `planning/audits/statements/MA7Statements.lean.txt`
§C, with the namespace `MA7Scratch` replaced by `HigherDimLQGMetric.DGZ`.

Definitions:
* `lfppMetric ξ φ x y` — the whole-space LFPP metric `D^ξ(φ)(x, y)`;
* `lfppSetDist ξ φ V A B` — the set-to-set internal distance `D(A, B; V)`;
* `lsph c r` — the `ℓ^∞` sphere `∂B_r(c) = B̄_r(c) \ B_r(c)`;
* `acrossDist ξ φ c r₁ r₂` — `D(across B_{r₁}(c) \ B_{r₂}(c)) = D(∂B_{r₂}(c), ∂B_{r₁}(c))`;
* `lfppDiam ξ φ U V` — the internal diameter `Diam(U; V)`;
* `selfDiam ξ φ c r` — the self-internal diameter `Diam(B_r(c); B_r(c))` of an open box;
* `lfppLengthIn ξ φ γ S` — `len(γ|_S)`, the LFPP length of the part of `γ` inside `S`;
* `IsShellCrossing c r₁ r₂ B γ` — a piecewise `C¹` crossing of the closed shell inside `B`;
* `AroundGood ξ φ c r₁ r₂ B t` — the deterministic around-good property.

Basic API proved here:
* boxes and spheres: `mem_lsph`, `isClosed_lsph`, `isCompact_cbox`, `cbox_subset_obox`,
  `lsph_nonempty`, `norm_sub_le_of_forall_abs_le`, `norm_sub_le_of_mem_cbox`;
* set distances: `lfppSetDist_nonneg`, `lfppSetDist_le`, `le_lfppSetDist`, `exists_lfppDistOn_lt`,
  `lfppSetDist_comm`, `lfppSetDist_anti`, `lfppSetDist_mono_domain`, `lfppSetDist_singleton`;
* diameters: `lfppDiam_nonneg`, `lfppDistOn_le_lfppDiam`, `lfppDiam_le`, `lfppDiam_anti_domain`;
* the self-internal diameter: `bddAbove_selfDiam`, `lfppDistOn_le_selfDiam`,
  `lfppDistOn_le_selfDiam_of_subset`, `selfDiam_le`, `selfDiam_pos`, `selfDiam_le_exp_mul_norm`;
  field comparison `selfDiam_le_mul_of_exp_le`, `selfDiam_le_exp_mul`, `selfDiam_mono_field`,
  `selfDiam_congr` and the log-Lipschitz bound **`abs_log_selfDiam_sub_le`** (MA7 D-4.6, D-4.7s);
* the whole-space metric: `lfppMetric_nonneg`, `lfppMetric_self`, `lfppMetric_comm`,
  `lfppMetric_triangle`, `lfppMetric_le_lfppDistOn`, `lfppMetric_le_lfppLength`, `lfppMetric_pos`,
  `lfppMetric_le_exp_mul`, `abs_log_lfppMetric_sub_le`;
* `AroundGood.mono`, `AroundGood.of_exp_le`, `AroundGood.congr`, `AroundGood.mono_field`.

Junk values. `lfppDistOn` is `0` for points that are not joined in the domain; in `ℝ`,
`sInf ∅ = sSup ∅ = 0` and the `sSup` of a set that is not bounded above is `0`
(`Real.sSup_of_not_bddAbove`). The lemmas therefore carry the nonemptiness, joinability or
boundedness hypotheses they need; for continuous fields boundedness is proved here
(`bddAbove_selfDiam`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-! ## Definitions (MA7 Details (c) §C, verbatim) -/

/-- the whole-space LFPP metric `D^ξ(φ)(x, y)` -/
def lfppMetric (ξ : ℝ) (φ : Rd d → ℝ) (x y : Rd d) : ℝ := lfppDistOn ξ φ univ x y

/-- set-to-set internal distance `D(A, B; V) = inf_{x ∈ A, y ∈ B} D(x, y; V)` -/
def lfppSetDist (ξ : ℝ) (φ : Rd d → ℝ) (V A B : Set (Rd d)) : ℝ :=
  sInf ((fun p : Rd d × Rd d => lfppDistOn ξ φ V p.1 p.2) '' (A ×ˢ B))

/-- the `ℓ^∞` sphere `∂B_r(c)` -/
def lsph (c : Rd d) (r : ℝ) : Set (Rd d) := cbox c r \ obox c r

/-- `D(across B_{r₁}(c) \ B_{r₂}(c)) = D(∂B_{r₂}(c), ∂B_{r₁}(c))` (DGZ (4.19)) -/
def acrossDist (ξ : ℝ) (φ : Rd d → ℝ) (c : Rd d) (r₁ r₂ : ℝ) : ℝ :=
  lfppSetDist ξ φ univ (lsph c r₂) (lsph c r₁)

/-- internal diameter `Diam(U; V) = sup_{x, y ∈ U} D(x, y; V)` (DGZ (4.1)) -/
def lfppDiam (ξ : ℝ) (φ : Rd d → ℝ) (U V : Set (Rd d)) : ℝ :=
  sSup ((fun p : Rd d × Rd d => lfppDistOn ξ φ V p.1 p.2) '' (U ×ˢ U))

/-- the self-internal diameter `Diam(B_r(c); B_r(c))` of an open box (MA7: replaces DGZ's
clipped diameters, footnotes to (4.22) and Lemma 5.12) -/
def selfDiam (ξ : ℝ) (φ : Rd d → ℝ) (c : Rd d) (r : ℝ) : ℝ :=
  lfppDiam ξ φ (obox c r) (obox c r)

/-- `len(γ|_S)`: LFPP length of the part of a path `γ : [0,1] → ℝ^d` inside `S` (MA7: DGZ (2.3)
for piecewise-`C¹` paths, as a set integral) -/
def lfppLengthIn (ξ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) (S : Set (Rd d)) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1 ∩ γ ⁻¹' S, Real.exp (ξ * φ (γ t)) * ‖deriv γ t‖

/-- `γ` is a piecewise-`C¹` crossing of the closed shell `cbox c r₁ \ obox c r₂`, inside `B` -/
structure IsShellCrossing (c : Rd d) (r₁ r₂ : ℝ) (B : Set (Rd d)) (γ : ℝ → Rd d) : Prop where
  pcw : IsPcwC1Path γ (γ 0) (γ 1)
  start : γ 0 ∈ lsph c r₂
  stop : γ 1 ∈ lsph c r₁
  inShell : MapsTo γ (Icc 0 1) (cbox c r₁ \ obox c r₂)
  inB : MapsTo γ (Icc 0 1) B

/-- **around-good** (MA7 D-AR; replaces DGZ's random variable `D(around A)` (4.27) with `B` fixed):
any two crossings of the shell inside `B` are joined inside `(cbox c r₁ \ obox c r₂) ∩ B` by a
piecewise-`C¹` path of `φ`-length `≤ t` -/
def AroundGood (ξ : ℝ) (φ : Rd d → ℝ) (c : Rd d) (r₁ r₂ : ℝ) (B : Set (Rd d)) (t : ℝ) : Prop :=
  ∀ γ₁ γ₂ : ℝ → Rd d, IsShellCrossing c r₁ r₂ B γ₁ → IsShellCrossing c r₁ r₂ B γ₂ →
    ∃ s₁ ∈ Icc (0 : ℝ) 1, ∃ s₂ ∈ Icc (0 : ℝ) 1,
      PcwJoined ((cbox c r₁ \ obox c r₂) ∩ B) (γ₁ s₁) (γ₂ s₂) ∧
      lfppDistOn ξ φ ((cbox c r₁ \ obox c r₂) ∩ B) (γ₁ s₁) (γ₂ s₂) ≤ t

/-! ## `ℓ^∞` boxes and spheres -/

section Boxes

theorem mem_cbox {c z : Rd d} {r : ℝ} : z ∈ cbox c r ↔ ∀ i, |z i - c i| ≤ r := Iff.rfl

theorem mem_obox {c z : Rd d} {r : ℝ} : z ∈ obox c r ↔ ∀ i, |z i - c i| < r := Iff.rfl

theorem mem_lsph {c z : Rd d} {r : ℝ} : z ∈ lsph c r ↔ z ∈ cbox c r ∧ z ∉ obox c r := Iff.rfl

theorem lsph_subset_cbox (c : Rd d) (r : ℝ) : lsph c r ⊆ cbox c r := sdiff_subset

theorem isClosed_lsph (c : Rd d) (r : ℝ) : IsClosed (lsph c r) :=
  (HigherDimLFPP.DGZ.isClosed_cbox c r).sdiff (HigherDimLFPP.DGZ.isOpen_obox c r)

theorem cbox_subset_obox {c : Rd d} {r r' : ℝ} (h : r < r') : cbox c r ⊆ obox c r' :=
  fun _ hz i => (hz i).trans_lt h

theorem cbox_mono {c : Rd d} {r r' : ℝ} (h : r ≤ r') : cbox c r ⊆ cbox c r' :=
  fun _ hz i => (hz i).trans h

theorem obox_mono {c : Rd d} {r r' : ℝ} (h : r ≤ r') : obox c r ⊆ obox c r' :=
  fun _ hz i => (hz i).trans_le h

/-- The closed box is the image of a product of closed intervals. -/
theorem cbox_eq_image (c : Rd d) (r : ℝ) :
    cbox c r = (WithLp.toLp 2 : (Fin d → ℝ) → Rd d) ''
      (Set.pi univ fun i => Icc (c i - r) (c i + r)) := by
  ext z
  constructor
  · intro hz
    refine ⟨WithLp.ofLp z, fun i _ => ?_, WithLp.toLp_ofLp 2 z⟩
    have h := abs_le.1 (hz i)
    exact ⟨by dsimp only; linarith [h.1], by dsimp only; linarith [h.2]⟩
  · rintro ⟨f, hf, rfl⟩ i
    have h := hf i (mem_univ i)
    rw [abs_le]
    exact ⟨by dsimp only; linarith [h.1], by dsimp only; linarith [h.2]⟩

theorem isCompact_cbox (c : Rd d) (r : ℝ) : IsCompact (cbox c r) := by
  rw [cbox_eq_image]
  exact (isCompact_univ_pi fun i => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

theorem isBounded_obox (c : Rd d) (r : ℝ) : Bornology.IsBounded (obox c r) :=
  (isCompact_cbox c r).isBounded.subset (HigherDimLFPP.DGZ.obox_subset_cbox c r)

/-- `‖x - y‖ ≤ √d · s` when all coordinates of `x - y` are at most `s` in absolute value. -/
theorem norm_sub_le_of_forall_abs_le {x y : Rd d} {s : ℝ} (h : ∀ i, |x i - y i| ≤ s) :
    ‖x - y‖ ≤ Real.sqrt d * s := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : x - y = 0 := Subsingleton.elim _ _
    rw [this, norm_zero]
    simp
  have hs : 0 ≤ s := (abs_nonneg _).trans (h ⟨0, hd⟩)
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin d, ‖(x - y) i‖ ^ 2 ≤ d * s ^ 2 := by
    calc ∑ i : Fin d, ‖(x - y) i‖ ^ 2 ≤ ∑ _i : Fin d, s ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [PiLp.sub_apply, Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = d * s ^ 2 := by simp
  calc Real.sqrt (∑ i : Fin d, ‖(x - y) i‖ ^ 2) ≤ Real.sqrt (d * s ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * s := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hs]

theorem norm_sub_le_of_mem_cbox {c x y : Rd d} {r : ℝ} (hx : x ∈ cbox c r) (hy : y ∈ cbox c r) :
    ‖x - y‖ ≤ Real.sqrt d * (2 * r) := by
  refine norm_sub_le_of_forall_abs_le fun i => ?_
  have h1 := hx i
  have h2 := hy i
  calc |x i - y i| = |(x i - c i) - (y i - c i)| := by ring_nf
    _ ≤ |x i - c i| + |y i - c i| := abs_sub _ _
    _ ≤ 2 * r := by linarith

/-- For `d ≥ 1` and `r ≥ 0`, the sphere `lsph c r` is nonempty (it contains `c + r e₀`). -/
theorem lsph_nonempty (hd : 0 < d) (c : Rd d) {r : ℝ} (hr : 0 ≤ r) : (lsph c r).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun i => if (i : ℕ) = 0 then c i + r else c i), fun i => ?_, fun h => ?_⟩
  · dsimp only
    split_ifs
    · rw [add_sub_cancel_left, abs_of_nonneg hr]
    · rw [sub_self, abs_zero]; exact hr
  · have h0 := h ⟨0, hd⟩
    simp only [ite_true, add_sub_cancel_left, abs_of_nonneg hr] at h0
    exact lt_irrefl r h0

theorem obox_nonempty (c : Rd d) {r : ℝ} (hr : 0 < r) : (obox c r).Nonempty :=
  ⟨c, HigherDimLFPP.DGZ.mem_obox_self c hr⟩

end Boxes

/-! ## Set distances -/

section SetDist

variable {ξ : ℝ} {φ : Rd d → ℝ} {V W A B A' B' : Set (Rd d)} {x y : Rd d}

theorem bddBelow_lfppSetDist (ξ : ℝ) (φ : Rd d → ℝ) (V A B : Set (Rd d)) :
    BddBelow ((fun p : Rd d × Rd d => lfppDistOn ξ φ V p.1 p.2) '' (A ×ˢ B)) :=
  ⟨0, by rintro _ ⟨p, -, rfl⟩; exact lfppDistOn_nonneg ξ φ V p.1 p.2⟩

theorem lfppSetDist_nonneg (ξ : ℝ) (φ : Rd d → ℝ) (V A B : Set (Rd d)) :
    0 ≤ lfppSetDist ξ φ V A B :=
  Real.sInf_nonneg (by rintro _ ⟨p, -, rfl⟩; exact lfppDistOn_nonneg ξ φ V p.1 p.2)

/-- The set distance is at most the distance of any pair. -/
theorem lfppSetDist_le (hx : x ∈ A) (hy : y ∈ B) :
    lfppSetDist ξ φ V A B ≤ lfppDistOn ξ φ V x y :=
  csInf_le (bddBelow_lfppSetDist ξ φ V A B) ⟨(x, y), ⟨hx, hy⟩, rfl⟩

/-- A lower bound for all pairs bounds the set distance (nonempty sets). -/
theorem le_lfppSetDist (hA : A.Nonempty) (hB : B.Nonempty) {c : ℝ}
    (h : ∀ x ∈ A, ∀ y ∈ B, c ≤ lfppDistOn ξ φ V x y) : c ≤ lfppSetDist ξ φ V A B :=
  le_csInf ((hA.prod hB).image _) (by rintro _ ⟨p, hp, rfl⟩; exact h p.1 hp.1 p.2 hp.2)

/-- Near-optimal pairs exist (nonempty sets). -/
theorem exists_lfppDistOn_lt (hA : A.Nonempty) (hB : B.Nonempty) {c : ℝ}
    (h : lfppSetDist ξ φ V A B < c) : ∃ x ∈ A, ∃ y ∈ B, lfppDistOn ξ φ V x y < c := by
  obtain ⟨_, ⟨p, hp, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt ((hA.prod hB).image _) h
  exact ⟨p.1, hp.1, p.2, hp.2, hlt⟩

theorem lfppSetDist_comm (ξ : ℝ) (φ : Rd d → ℝ) (V A B : Set (Rd d)) :
    lfppSetDist ξ φ V A B = lfppSetDist ξ φ V B A := by
  unfold lfppSetDist
  congr 1
  ext t
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.2, p.1), ⟨hp.2, hp.1⟩, lfppDistOn_comm ξ φ V p.2 p.1⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.2, p.1), ⟨hp.2, hp.1⟩, lfppDistOn_comm ξ φ V p.2 p.1⟩

/-- Antitonicity in the two sets (nonempty smaller sets). -/
theorem lfppSetDist_anti (hA : A.Nonempty) (hB : B.Nonempty) (hAA' : A ⊆ A') (hBB' : B ⊆ B') :
    lfppSetDist ξ φ V A' B' ≤ lfppSetDist ξ φ V A B :=
  le_lfppSetDist hA hB fun _ hx _ hy => lfppSetDist_le (hAA' hx) (hBB' hy)

/-- Monotonicity in the domain: `D(A, B; W) ≤ D(A, B; V)` for `V ⊆ W` when all pairs are joined
in `V`. -/
theorem lfppSetDist_mono_domain (hA : A.Nonempty) (hB : B.Nonempty) (hVW : V ⊆ W)
    (hj : ∀ x ∈ A, ∀ y ∈ B, PcwJoined V x y) :
    lfppSetDist ξ φ W A B ≤ lfppSetDist ξ φ V A B :=
  le_lfppSetDist hA hB fun x hx y hy =>
    (lfppSetDist_le hx hy).trans (lfppDistOn_mono hVW (hj x hx y hy))

theorem lfppSetDist_singleton (ξ : ℝ) (φ : Rd d → ℝ) (V : Set (Rd d)) (x y : Rd d) :
    lfppSetDist ξ φ V {x} {y} = lfppDistOn ξ φ V x y := by
  unfold lfppSetDist
  rw [singleton_prod_singleton, image_singleton, csInf_singleton]

end SetDist

/-! ## Internal diameters -/

section Diam

variable {ξ : ℝ} {φ : Rd d → ℝ} {U U' V W : Set (Rd d)} {x y : Rd d}

theorem lfppDiam_nonneg (ξ : ℝ) (φ : Rd d → ℝ) (U V : Set (Rd d)) : 0 ≤ lfppDiam ξ φ U V :=
  Real.sSup_nonneg (by rintro _ ⟨p, -, rfl⟩; exact lfppDistOn_nonneg ξ φ V p.1 p.2)

/-- The diameter dominates the distance of any pair, once the family is bounded above. -/
theorem lfppDistOn_le_lfppDiam
    (hbdd : BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ φ V p.1 p.2) '' (U ×ˢ U)))
    (hx : x ∈ U) (hy : y ∈ U) : lfppDistOn ξ φ V x y ≤ lfppDiam ξ φ U V :=
  le_csSup hbdd ⟨(x, y), ⟨hx, hy⟩, rfl⟩

/-- An upper bound `c ≥ 0` for all pairs bounds the diameter. -/
theorem lfppDiam_le {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ U, ∀ y ∈ U, lfppDistOn ξ φ V x y ≤ c) :
    lfppDiam ξ φ U V ≤ c :=
  Real.sSup_le (by rintro _ ⟨p, hp, rfl⟩; exact h p.1 hp.1 p.2 hp.2) hc

theorem bddAbove_lfppDiam_of_le {c : ℝ} (h : ∀ x ∈ U, ∀ y ∈ U, lfppDistOn ξ φ V x y ≤ c) :
    BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ φ V p.1 p.2) '' (U ×ˢ U)) :=
  ⟨c, by rintro _ ⟨p, hp, rfl⟩; exact h p.1 hp.1 p.2 hp.2⟩

/-- Antitonicity in the domain for a bounded family: `Diam(U; W) ≤ Diam(U; V)` for `V ⊆ W` when
all pairs of `U` are joined in `V`. -/
theorem lfppDiam_anti_domain (hVW : V ⊆ W) (hj : ∀ x ∈ U, ∀ y ∈ U, PcwJoined V x y)
    (hbdd : BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ φ V p.1 p.2) '' (U ×ˢ U))) :
    lfppDiam ξ φ U W ≤ lfppDiam ξ φ U V :=
  lfppDiam_le (lfppDiam_nonneg ξ φ U V) fun x hx y hy =>
    (lfppDistOn_mono hVW (hj x hx y hy)).trans (lfppDistOn_le_lfppDiam hbdd hx hy)

/-- **Crude upper bound in a convex set**: if `ξ φ ≤ M` on the convex set `V ∋ x, y`, then
`D_V(x, y) ≤ e^M ‖y - x‖`. -/
theorem lfppDistOn_le_exp_mul_norm_of_convex (hφ : Continuous φ) (hV : Convex ℝ V) (hx : x ∈ V)
    (hy : y ∈ V) {M : ℝ} (hM : ∀ z ∈ V, ξ * φ z ≤ M) :
    lfppDistOn ξ φ V x y ≤ Real.exp M * ‖y - x‖ :=
  lfppDistOn_le_of_segment hφ (mapsTo_segPath hV hx hy) fun _ hu =>
    Real.exp_le_exp.2 (hM _ (segPath_mem_of_convex hV hx hy hu))

end Diam

/-! ## The self-internal diameter of an open box -/

section SelfDiam

variable {ξ : ℝ} {φ ψ : Rd d → ℝ} {c : Rd d} {r : ℝ} {V : Set (Rd d)} {x y : Rd d}

theorem selfDiam_nonneg (ξ : ℝ) (φ : Rd d → ℝ) (c : Rd d) (r : ℝ) : 0 ≤ selfDiam ξ φ c r :=
  lfppDiam_nonneg ξ φ _ _

/-- A bound for `ξ φ` on the closed box, from compactness. -/
theorem exists_mul_le_on_cbox (hφ : Continuous φ) (ξ : ℝ) (c : Rd d) (r : ℝ) :
    ∃ M : ℝ, ∀ z ∈ cbox c r, ξ * φ z ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_cbox c r).bddAbove_image
    (continuous_const.mul hφ).continuousOn
  exact ⟨M, fun z hz => hM ⟨z, hz, rfl⟩⟩

/-- **Crude bound**: if `ξ φ ≤ M` on the box, `D_{B_r(c)}(x, y) ≤ e^M √d · 2r` for `x, y` in it. -/
theorem lfppDistOn_obox_le (hφ : Continuous φ) {M : ℝ} (hM : ∀ z ∈ obox c r, ξ * φ z ≤ M)
    (hx : x ∈ obox c r) (hy : y ∈ obox c r) :
    lfppDistOn ξ φ (obox c r) x y ≤ Real.exp M * (Real.sqrt d * (2 * r)) := by
  refine (lfppDistOn_le_exp_mul_norm_of_convex hφ (HigherDimLFPP.DGZ.convex_obox c r) hx hy
    hM).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos M).le)
  exact norm_sub_le_of_mem_cbox (HigherDimLFPP.DGZ.obox_subset_cbox c r hy)
    (HigherDimLFPP.DGZ.obox_subset_cbox c r hx)

/-- For a continuous field the family defining `selfDiam` is bounded above. -/
theorem bddAbove_selfDiam (hφ : Continuous φ) (ξ : ℝ) (c : Rd d) (r : ℝ) :
    BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ φ (obox c r) p.1 p.2) ''
      (obox c r ×ˢ obox c r)) := by
  obtain ⟨M, hM⟩ := exists_mul_le_on_cbox hφ ξ c r
  exact bddAbove_lfppDiam_of_le fun x hx y hy =>
    lfppDistOn_obox_le hφ (fun z hz => hM z (HigherDimLFPP.DGZ.obox_subset_cbox c r hz)) hx hy

/-- Distances inside the box are at most its self-internal diameter. -/
theorem lfppDistOn_le_selfDiam (hφ : Continuous φ) (hx : x ∈ obox c r) (hy : y ∈ obox c r) :
    lfppDistOn ξ φ (obox c r) x y ≤ selfDiam ξ φ c r :=
  lfppDistOn_le_lfppDiam (bddAbove_selfDiam hφ ξ c r) hx hy

/-- Distances in any domain containing the box are at most its self-internal diameter. -/
theorem lfppDistOn_le_selfDiam_of_subset (hφ : Continuous φ) (hV : obox c r ⊆ V)
    (hx : x ∈ obox c r) (hy : y ∈ obox c r) : lfppDistOn ξ φ V x y ≤ selfDiam ξ φ c r :=
  (lfppDistOn_mono hV (PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox c r) hx hy)).trans
    (lfppDistOn_le_selfDiam hφ hx hy)

/-- An upper bound `C ≥ 0` for all pairs bounds the self-internal diameter. -/
theorem selfDiam_le {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ obox c r, ∀ y ∈ obox c r, lfppDistOn ξ φ (obox c r) x y ≤ C) :
    selfDiam ξ φ c r ≤ C :=
  lfppDiam_le hC h

/-- **Crude bound**: `selfDiam ≤ e^M √d · 2r` if `ξ φ ≤ M` on the box (`r ≥ 0`). -/
theorem selfDiam_le_exp_mul_norm (hφ : Continuous φ) (hr : 0 ≤ r) {M : ℝ}
    (hM : ∀ z ∈ obox c r, ξ * φ z ≤ M) :
    selfDiam ξ φ c r ≤ Real.exp M * (Real.sqrt d * (2 * r)) :=
  selfDiam_le (by positivity) fun _ hx _ hy => lfppDistOn_obox_le hφ hM hx hy

/-- **Positivity** of the self-internal diameter (`d ≥ 1`, `r > 0`, continuous field). -/
theorem selfDiam_pos (hd : 0 < d) (hφ : Continuous φ) (hr : 0 < r) : 0 < selfDiam ξ φ c r := by
  set y : Rd d := WithLp.toLp 2 (fun i => if (i : ℕ) = 0 then c i + r / 2 else c i) with hy
  have hyb : y ∈ obox c r := fun i => by
    simp only [hy, PiLp.toLp_apply]
    split_ifs
    · rw [add_sub_cancel_left, abs_of_pos (half_pos hr)]; linarith
    · rw [sub_self, abs_zero]; exact hr
  have hne : c ≠ y := by
    intro h
    have h0 : c ⟨0, hd⟩ = y ⟨0, hd⟩ := by rw [h]
    simp only [hy, PiLp.toLp_apply, ite_true] at h0
    linarith
  have hcb := HigherDimLFPP.DGZ.mem_obox_self c hr
  exact (lfppDistOn_pos hφ hne (PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox c r) hcb
    hyb)).trans_le (lfppDistOn_le_selfDiam hφ hcb hyb)

/-- **Field comparison**: if `e^{ξ φ} ≤ C e^{ξ ψ}` on the box (`C ≥ 0`), then
`selfDiam(φ) ≤ C selfDiam(ψ)`. -/
theorem selfDiam_le_mul_of_exp_le (hφ : Continuous φ) (hψ : Continuous ψ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z ∈ obox c r, Real.exp (ξ * φ z) ≤ C * Real.exp (ξ * ψ z)) :
    selfDiam ξ φ c r ≤ C * selfDiam ξ ψ c r :=
  selfDiam_le (mul_nonneg hC (selfDiam_nonneg ξ ψ c r)) fun _ hx _ hy =>
    (lfppDistOn_le_mul_of_exp_le hφ hψ hC h).trans
      (mul_le_mul_of_nonneg_left (lfppDistOn_le_selfDiam hψ hx hy) hC)

/-- **Field comparison**: if `|φ - ψ| ≤ M` on the box, `selfDiam(φ) ≤ e^{|ξ| M} selfDiam(ψ)`. -/
theorem selfDiam_le_exp_mul (hφ : Continuous φ) (hψ : Continuous ψ) {M : ℝ}
    (hM : ∀ z ∈ obox c r, |φ z - ψ z| ≤ M) :
    selfDiam ξ φ c r ≤ Real.exp (|ξ| * M) * selfDiam ξ ψ c r :=
  selfDiam_le_mul_of_exp_le hφ hψ (Real.exp_pos _).le fun z hz =>
    exp_mul_le_exp_abs_mul (hM z hz)

/-- **Log-Lipschitz bound** (MA7 D-4.6, D-4.7s): if `|φ - ψ| ≤ M` on the open box `B_r(c)`
(`r > 0`), then `|log selfDiam(φ) - log selfDiam(ψ)| ≤ |ξ| M`. -/
theorem abs_log_selfDiam_sub_le (hφ : Continuous φ) (hψ : Continuous ψ) (hr : 0 < r) {M : ℝ}
    (hM : ∀ z ∈ obox c r, |φ z - ψ z| ≤ M) :
    |Real.log (selfDiam ξ φ c r) - Real.log (selfDiam ξ ψ c r)| ≤ |ξ| * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c (HigherDimLFPP.DGZ.mem_obox_self c hr))
  refine abs_log_sub_le_of_le_exp_mul (selfDiam_nonneg ξ φ c r) (selfDiam_nonneg ξ ψ c r)
    (mul_nonneg (abs_nonneg ξ) hM0) (selfDiam_le_exp_mul hφ hψ hM)
    (selfDiam_le_exp_mul hψ hφ fun z hz => ?_)
  rw [abs_sub_comm]
  exact hM z hz

/-- **Monotonicity in the field** (`ξ ≥ 0`). -/
theorem selfDiam_mono_field (hξ : 0 ≤ ξ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ z ∈ obox c r, φ z ≤ ψ z) : selfDiam ξ φ c r ≤ selfDiam ξ ψ c r := by
  have := selfDiam_le_mul_of_exp_le (ξ := ξ) (c := c) (r := r) hφ hψ zero_le_one fun z hz => by
    rw [one_mul, Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (h z hz) hξ
  rwa [one_mul] at this

/-- **Locality**: the self-internal diameter only depends on the field on the open box. -/
theorem selfDiam_congr (h : ∀ z ∈ obox c r, φ z = ψ z) : selfDiam ξ φ c r = selfDiam ξ ψ c r := by
  unfold selfDiam lfppDiam
  congr 1
  refine image_congr fun p _ => ?_
  exact HigherDimLFPP.DGZ.lfppDistOn_congr h p.1 p.2

end SelfDiam

/-! ## The whole-space metric -/

section Metric

variable {ξ : ℝ} {φ ψ : Rd d → ℝ} {V : Set (Rd d)} {x y z : Rd d}

theorem pcwJoined_univ (x y : Rd d) : PcwJoined univ x y :=
  PcwJoined.of_convex convex_univ (mem_univ x) (mem_univ y)

theorem lfppMetric_nonneg (ξ : ℝ) (φ : Rd d → ℝ) (x y : Rd d) : 0 ≤ lfppMetric ξ φ x y :=
  lfppDistOn_nonneg ξ φ univ x y

theorem lfppMetric_self (ξ : ℝ) (φ : Rd d → ℝ) (x : Rd d) : lfppMetric ξ φ x x = 0 :=
  lfppDistOn_self ξ φ univ x

theorem lfppMetric_comm (ξ : ℝ) (φ : Rd d → ℝ) (x y : Rd d) :
    lfppMetric ξ φ x y = lfppMetric ξ φ y x :=
  lfppDistOn_comm ξ φ univ x y

theorem lfppMetric_triangle (hφ : Continuous φ) (x y z : Rd d) :
    lfppMetric ξ φ x z ≤ lfppMetric ξ φ x y + lfppMetric ξ φ y z :=
  lfppDistOn_triangle hφ (pcwJoined_univ x y) (pcwJoined_univ y z)

/-- The whole-space metric is at most every internal distance between joined points. -/
theorem lfppMetric_le_lfppDistOn (hj : PcwJoined V x y) :
    lfppMetric ξ φ x y ≤ lfppDistOn ξ φ V x y :=
  lfppDistOn_mono (subset_univ V) hj

theorem lfppMetric_le_lfppLength {γ : ℝ → Rd d} (hγ : IsPcwC1Path γ x y) :
    lfppMetric ξ φ x y ≤ lfppLength ξ φ γ :=
  lfppDistOn_le_lfppLength hγ (mapsTo_univ _ _)

theorem lfppMetric_pos (hφ : Continuous φ) (hxy : x ≠ y) : 0 < lfppMetric ξ φ x y :=
  lfppDistOn_pos hφ hxy (pcwJoined_univ x y)

/-- **Weight comparison**: if `|φ - ψ| ≤ M` everywhere, `D^ξ(φ) ≤ e^{|ξ| M} D^ξ(ψ)`. -/
theorem lfppMetric_le_exp_mul (hφ : Continuous φ) (hψ : Continuous ψ) {M : ℝ}
    (hM : ∀ z, |φ z - ψ z| ≤ M) :
    lfppMetric ξ φ x y ≤ Real.exp (|ξ| * M) * lfppMetric ξ ψ x y :=
  lfppDistOn_le_exp_mul hφ hψ fun z _ => hM z

theorem abs_log_lfppMetric_sub_le (hφ : Continuous φ) (hψ : Continuous ψ) {M : ℝ}
    (hM : ∀ z, |φ z - ψ z| ≤ M) :
    |Real.log (lfppMetric ξ φ x y) - Real.log (lfppMetric ξ ψ x y)| ≤ |ξ| * M :=
  abs_log_lfppDistOn_sub_le hφ hψ (mem_univ x) fun z _ => hM z

end Metric

/-! ## The around-good property: monotonicity and field comparison -/

section Around

variable {ξ : ℝ} {φ ψ : Rd d → ℝ} {c : Rd d} {r₁ r₂ : ℝ} {B : Set (Rd d)} {t t' : ℝ}

/-- `AroundGood` is monotone in the threshold. -/
theorem AroundGood.mono (h : AroundGood ξ φ c r₁ r₂ B t) (htt' : t ≤ t') :
    AroundGood ξ φ c r₁ r₂ B t' := by
  intro γ₁ γ₂ h₁ h₂
  obtain ⟨s₁, hs₁, s₂, hs₂, hj, hle⟩ := h γ₁ γ₂ h₁ h₂
  exact ⟨s₁, hs₁, s₂, hs₂, hj, hle.trans htt'⟩

/-- **Field comparison for `AroundGood`**: if `e^{ξ ψ} ≤ C e^{ξ φ}` on the region
`(cbox c r₁ \ obox c r₂) ∩ B` (`C ≥ 0`), the threshold is multiplied by `C`. -/
theorem AroundGood.of_exp_le (h : AroundGood ξ φ c r₁ r₂ B t) (hφ : Continuous φ)
    (hψ : Continuous ψ) {C : ℝ} (hC : 0 ≤ C)
    (hcomp : ∀ z ∈ (cbox c r₁ \ obox c r₂) ∩ B, Real.exp (ξ * ψ z) ≤ C * Real.exp (ξ * φ z)) :
    AroundGood ξ ψ c r₁ r₂ B (C * t) := by
  intro γ₁ γ₂ h₁ h₂
  obtain ⟨s₁, hs₁, s₂, hs₂, hj, hle⟩ := h γ₁ γ₂ h₁ h₂
  exact ⟨s₁, hs₁, s₂, hs₂, hj, (lfppDistOn_le_mul_of_exp_le hψ hφ hC hcomp).trans
    (mul_le_mul_of_nonneg_left hle hC)⟩

/-- **Locality of `AroundGood`**: it only depends on the field on the region
`(cbox c r₁ \ obox c r₂) ∩ B`. -/
theorem AroundGood.congr (h : AroundGood ξ φ c r₁ r₂ B t)
    (hφψ : ∀ z ∈ (cbox c r₁ \ obox c r₂) ∩ B, φ z = ψ z) : AroundGood ξ ψ c r₁ r₂ B t := by
  intro γ₁ γ₂ h₁ h₂
  obtain ⟨s₁, hs₁, s₂, hs₂, hj, hle⟩ := h γ₁ γ₂ h₁ h₂
  refine ⟨s₁, hs₁, s₂, hs₂, hj, ?_⟩
  rwa [← HigherDimLFPP.DGZ.lfppDistOn_congr hφψ]

/-- **Monotonicity of `AroundGood` in the field** (`ξ ≥ 0`): if `ψ ≤ φ + M` on the region, the
threshold is multiplied by `e^{ξ M}`. -/
theorem AroundGood.mono_field (h : AroundGood ξ φ c r₁ r₂ B t) (hξ : 0 ≤ ξ) (hφ : Continuous φ)
    (hψ : Continuous ψ) {M : ℝ} (hM : ∀ z ∈ (cbox c r₁ \ obox c r₂) ∩ B, ψ z ≤ φ z + M) :
    AroundGood ξ ψ c r₁ r₂ B (Real.exp (ξ * M) * t) :=
  h.of_exp_le hφ hψ (Real.exp_pos _).le fun z hz => by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [hM z hz]

end Around

end HigherDimLQGMetric.DGZ
