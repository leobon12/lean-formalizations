import HigherDimLQGMetric.Frozen.ContMetricInternal
import HigherDimLQGMetric.Frozen.ContMetricIsLength
import LQGMetric.Metric.InternalOps
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Continuous metrics on `ℝ^d`: metric axioms, the Euclidean topology, lengths of curves

Packet M1 (Phase A, block A2). Port of LQGMetric's ℂ-typed files `Metric/InternalC.lean` (first
part: `ContMetric.continuous_pt`, `unpt`, `continuous_unpt`, `ptHomeomorph`, `isOpen_image_pt`,
`mem_image_pt`), `Metric/InternalLimitC.lean` (`edist_pt`, `nonneg`), `Metric/WeylCont.lean`
(`isClosed_pt_image_compl`) and `Metric/WeylScaling.lean` (`ContMetric.smul`, `ContMetric.affine`)
from `ℂ` to `Rd d = EuclideanSpace ℝ (Fin d)` (ruling M10), on top of the frozen definitions
`ContMetric`, `ContMetric.Space`, `ContMetric.pt`, `ContMetric.instMetricSpace`.

* Metric axioms for `D.1`: `nonneg`, `apply_self`, `apply_comm`, `apply_triangle`,
  `eq_of_apply_eq_zero`, `apply_eq_zero_iff`, `apply_pos`; `dist_pt`, `edist_pt`.
* The frozen topology: the identity `ℝ^d → D.Space` is a homeomorphism (`ptHomeomorph`), i.e. the
  topology of the metric space `(ℝ^d, D)` is the Euclidean one (`induced_pt`); consequences for
  images of open/closed/compact sets, closures and frontiers, and for continuity of curves
  (`continuousOn_pt_comp_iff`).
* The topology of `ContMetric d` (subspace of the compact-open topology): convergence is locally
  uniform convergence (`tendsto_iff_tendstoLocallyUniformly`).
* `len D P a b`, the `D`-length of `P` on `[a, b]` (MA0's `ContMetric.len`, not frozen), with
  additivity, monotonicity and `D(P a, P b) ≤ len`.
* `smul` (`C·D`, `C > 0`) and `affine` (`D(r · + a, r · + a)`, `r ≠ 0`).

Standard facts; proofs as in the 2D layer (own elementary arguments).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

namespace ContMetric

variable {d : ℕ}

/-! ### Metric axioms -/

theorem dist_pt (D : ContMetric d) (z w : Rd d) : dist (D.pt z) (D.pt w) = D.1 (z, w) := rfl

theorem edist_pt (D : ContMetric d) (z w : Rd d) :
    edist (D.pt z) (D.pt w) = ENNReal.ofReal (D.1 (z, w)) := edist_dist _ _

theorem nonneg (D : ContMetric d) (z w : Rd d) : 0 ≤ D.1 (z, w) :=
  (dist_nonneg : 0 ≤ dist (D.pt z) (D.pt w))

theorem apply_self (D : ContMetric d) (z : Rd d) : D.1 (z, z) = 0 := D.2.self_eq_zero z

theorem apply_comm (D : ContMetric d) (z w : Rd d) : D.1 (z, w) = D.1 (w, z) := D.2.symm z w

theorem apply_triangle (D : ContMetric d) (x y z : Rd d) :
    D.1 (x, z) ≤ D.1 (x, y) + D.1 (y, z) :=
  D.2.triangle x y z

theorem eq_of_apply_eq_zero (D : ContMetric d) {z w : Rd d} (h : D.1 (z, w) = 0) : z = w :=
  D.2.eq_of_eq_zero z w h

theorem apply_eq_zero_iff (D : ContMetric d) {z w : Rd d} : D.1 (z, w) = 0 ↔ z = w :=
  ⟨D.eq_of_apply_eq_zero, fun h => h ▸ D.apply_self z⟩

theorem apply_pos (D : ContMetric d) {z w : Rd d} (h : z ≠ w) : 0 < D.1 (z, w) :=
  (D.nonneg z w).lt_of_ne fun h' => h (D.eq_of_apply_eq_zero h'.symm)

theorem continuous_apply (D : ContMetric d) : Continuous fun p : Rd d × Rd d => D.1 p :=
  D.1.continuous

theorem edist_pt_ne_top (D : ContMetric d) (z w : Rd d) : edist (D.pt z) (D.pt w) ≠ ∞ :=
  edist_ne_top _ _

/-! ### The Euclidean topology -/

/-- The identity `ℝ^d → D.Space` is continuous. -/
theorem continuous_pt (D : ContMetric d) : Continuous D.pt := by
  refine Metric.continuous_iff.2 fun x ε hε => ?_
  have hc : Continuous fun y : Rd d => D.1 (y, x) :=
    D.1.continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hc x ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h' := h y hy
  rw [D.2.self_eq_zero x, Real.dist_eq, sub_zero] at h'
  exact (le_abs_self _).trans_lt h'

/-- The identity `D.Space → ℝ^d`. -/
def unpt (D : ContMetric d) : D.Space → Rd d := id

@[simp] theorem unpt_pt (D : ContMetric d) (z : Rd d) : D.unpt (D.pt z) = z := rfl

@[simp] theorem pt_unpt (D : ContMetric d) (x : D.Space) : D.pt (D.unpt x) = x := rfl

theorem pt_injective (D : ContMetric d) : Function.Injective D.pt := fun _ _ h => h

/-- The identity `D.Space → ℝ^d` is continuous (small `D`-balls are Euclidean-small). -/
theorem continuous_unpt (D : ContMetric d) : Continuous D.unpt := by
  refine Metric.continuous_iff.2 fun b ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := D.2.euclidean_of_small b ε hε
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have ha' : D.1 (b, a) < δ := lt_of_eq_of_lt (D.2.symm b a) ha
  rw [dist_eq_norm, norm_sub_rev]
  exact h a ha'

/-- **The frozen topology is Euclidean**: the identity `ℝ^d ≃ₜ D.Space`. -/
def ptHomeomorph (D : ContMetric d) : Rd d ≃ₜ D.Space where
  toFun := D.pt
  invFun := D.unpt
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := D.continuous_pt
  continuous_invFun := D.continuous_unpt

@[simp] theorem ptHomeomorph_apply (D : ContMetric d) (z : Rd d) : D.ptHomeomorph z = D.pt z :=
  rfl

@[simp] theorem ptHomeomorph_symm_apply (D : ContMetric d) (x : D.Space) :
    D.ptHomeomorph.symm x = D.unpt x :=
  rfl

/-- The topology of `(ℝ^d, D)` pulled back to `ℝ^d` is the Euclidean topology. -/
theorem induced_pt (D : ContMetric d) :
    TopologicalSpace.induced D.pt (inferInstance : TopologicalSpace D.Space) =
      (inferInstance : TopologicalSpace (Rd d)) :=
  D.ptHomeomorph.isInducing.eq_induced.symm

theorem mem_image_pt (D : ContMetric d) {V : Set (Rd d)} {z : Rd d} :
    D.pt z ∈ D.pt '' V ↔ z ∈ V :=
  ⟨fun ⟨w, hw, h⟩ => (show w = z from h) ▸ hw, fun h => ⟨z, h, rfl⟩⟩

theorem image_pt_eq_preimage_unpt (D : ContMetric d) (V : Set (Rd d)) :
    D.pt '' V = D.unpt ⁻¹' V := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨x, hx, rfl⟩

theorem image_pt_compl (D : ContMetric d) (V : Set (Rd d)) : D.pt '' Vᶜ = (D.pt '' V)ᶜ := by
  rw [image_pt_eq_preimage_unpt, image_pt_eq_preimage_unpt, preimage_compl]

theorem isOpen_image_pt (D : ContMetric d) {V : Set (Rd d)} (hV : IsOpen V) :
    IsOpen (D.pt '' V) :=
  D.ptHomeomorph.isOpenMap V hV

theorem isOpen_image_pt_iff (D : ContMetric d) {V : Set (Rd d)} :
    IsOpen (D.pt '' V) ↔ IsOpen V :=
  ⟨fun h => by
    have := h.preimage D.continuous_pt
    rwa [preimage_image_eq _ D.pt_injective] at this, D.isOpen_image_pt⟩

theorem isClosed_image_pt (D : ContMetric d) {V : Set (Rd d)} (hV : IsClosed V) :
    IsClosed (D.pt '' V) :=
  D.ptHomeomorph.isClosedMap V hV

theorem isClosed_pt_image_compl (D : ContMetric d) {V : Set (Rd d)} (hV : IsOpen V) :
    IsClosed (D.pt '' Vᶜ) :=
  D.isClosed_image_pt hV.isClosed_compl

theorem isCompact_image_pt (D : ContMetric d) {K : Set (Rd d)} (hK : IsCompact K) :
    IsCompact (D.pt '' K) :=
  hK.image D.continuous_pt

theorem image_pt_closure (D : ContMetric d) (V : Set (Rd d)) :
    D.pt '' closure V = closure (D.pt '' V) :=
  D.ptHomeomorph.image_closure V

theorem image_pt_frontier (D : ContMetric d) (V : Set (Rd d)) :
    D.pt '' frontier V = frontier (D.pt '' V) :=
  D.ptHomeomorph.image_frontier V

theorem continuousOn_pt_comp_iff (D : ContMetric d) {α : Type*} [TopologicalSpace α]
    {P : α → Rd d} {s : Set α} : ContinuousOn (D.pt ∘ P) s ↔ ContinuousOn P s :=
  ⟨fun h => D.continuous_unpt.comp_continuousOn h, fun h => D.continuous_pt.comp_continuousOn h⟩

theorem continuous_pt_comp_iff (D : ContMetric d) {α : Type*} [TopologicalSpace α]
    {P : α → Rd d} : Continuous (D.pt ∘ P) ↔ Continuous P :=
  ⟨fun h => D.continuous_unpt.comp h, fun h => D.continuous_pt.comp h⟩

theorem continuousOn_unpt_comp_iff (D : ContMetric d) {α : Type*} [TopologicalSpace α]
    {P : α → D.Space} {s : Set α} : ContinuousOn (D.unpt ∘ P) s ↔ ContinuousOn P s :=
  ⟨fun h => D.continuous_pt.comp_continuousOn h, fun h => D.continuous_unpt.comp_continuousOn h⟩

/-! ### The topology of `ContMetric d` -/

/-- Convergence in `ContMetric d` (subspace of the compact-open topology of `C(ℝ^d × ℝ^d, ℝ)`) is
locally uniform convergence of the distance functions. -/
theorem tendsto_iff_tendstoLocallyUniformly {ι : Type*} {l : Filter ι} {F : ι → ContMetric d}
    {D : ContMetric d} :
    Tendsto F l (𝓝 D) ↔ TendstoLocallyUniformly (fun i => ⇑(F i).1) (⇑D.1) l := by
  rw [← ContinuousMap.tendsto_iff_tendstoLocallyUniformly, tendsto_subtype_rng]

/-! ### Lengths of curves -/

/-- `len(P; D)` on `[a, b]`: the length of `P : ℝ → ℝ^d` for the metric `D`. -/
def len (D : ContMetric d) (P : ℝ → Rd d) (a b : ℝ) : ℝ≥0∞ :=
  curveLength (D.pt ∘ P) a b

theorem len_def (D : ContMetric d) (P : ℝ → Rd d) (a b : ℝ) :
    D.len P a b = curveLength (D.pt ∘ P) a b := rfl

theorem len_add (D : ContMetric d) (P : ℝ → Rd d) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    D.len P a b + D.len P b c = D.len P a c :=
  curveLength_add _ hab hbc

theorem ofReal_le_len (D : ContMetric d) (P : ℝ → Rd d) {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal (D.1 (P a, P b)) ≤ D.len P a b := by
  rw [← edist_pt]
  exact edist_le_curveLength (D.pt ∘ P) hab

theorem len_mono (D : ContMetric d) (P : ℝ → Rd d) {a b c e : ℝ} (hca : c ≤ a) (hbe : b ≤ e) :
    D.len P a b ≤ D.len P c e :=
  curveLength_mono _ hca hbe

theorem len_congr (D : ContMetric d) {P Q : ℝ → Rd d} {a b : ℝ} (h : EqOn P Q (Icc a b)) :
    D.len P a b = D.len Q a b :=
  curveLength_congr fun _ ht => congrArg D.pt (h ht)

theorem len_of_ge (D : ContMetric d) (P : ℝ → Rd d) {a b : ℝ} (hba : b ≤ a) : D.len P a b = 0 :=
  curveLength_of_ge _ hba

/-! ### `C D` and `D(r · + a, r · + a)` -/

/-- `C D` for `C > 0`. -/
def smul (C : ℝ) (hC : 0 < C) (D : ContMetric d) : ContMetric d :=
  ⟨C • D.1,
    { self_eq_zero := fun x => by simp [D.2.self_eq_zero x]
      eq_of_eq_zero := fun x y h => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_eq_zero, hC.ne', false_or] at h
        exact D.2.eq_of_eq_zero x y h
      symm := fun x y => by simp [D.2.symm x y]
      triangle := fun x y z => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, ← mul_add]
        exact mul_le_mul_of_nonneg_left (D.2.triangle x y z) hC.le
      euclidean_of_small := fun x ε hε => by
        obtain ⟨δ, hδ, h⟩ := D.2.euclidean_of_small x ε hε
        refine ⟨C * δ, mul_pos hC hδ, fun y hy => h y ?_⟩
        simp only [ContinuousMap.smul_apply, smul_eq_mul] at hy
        exact lt_of_mul_lt_mul_left hy hC.le }⟩

theorem smul_apply (C : ℝ) (hC : 0 < C) (D : ContMetric d) (p : Rd d × Rd d) :
    (D.smul C hC).1 p = C * D.1 p := rfl

theorem edist_smul (C : ℝ) (hC : 0 < C) (D : ContMetric d) (x y : Rd d) :
    edist ((D.smul C hC).pt x) ((D.smul C hC).pt y) =
      ENNReal.ofReal C * edist (D.pt x) (D.pt y) := by
  rw [edist_pt, edist_pt, smul_apply, ENNReal.ofReal_mul hC.le]

/-- `D(r x + a, r y + a)` for real `r ≠ 0` and `a ∈ ℝ^d`. -/
def affine (r : ℝ) (hr : r ≠ 0) (a : Rd d) (D : ContMetric d) : ContMetric d :=
  ⟨D.1.comp ⟨fun p => (r • p.1 + a, r • p.2 + a), by fun_prop⟩,
    { self_eq_zero := fun x => D.2.self_eq_zero _
      eq_of_eq_zero := fun x y h => by
        have h' := D.2.eq_of_eq_zero _ _ h
        simp only [add_left_inj] at h'
        exact smul_right_injective (Rd d) hr h'
      symm := fun x y => D.2.symm _ _
      triangle := fun x y z => D.2.triangle _ _ _
      euclidean_of_small := fun x ε hε => by
        obtain ⟨δ, hδ, h⟩ := D.2.euclidean_of_small (r • x + a) (ε * |r|)
          (mul_pos hε (abs_pos.2 hr))
        refine ⟨δ, hδ, fun y hy => ?_⟩
        have h' := h (r • y + a) hy
        rw [add_sub_add_right_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, mul_comm] at h'
        exact lt_of_mul_lt_mul_right h' (abs_nonneg r) }⟩

theorem affine_apply (r : ℝ) (hr : r ≠ 0) (a : Rd d) (D : ContMetric d) (p : Rd d × Rd d) :
    (D.affine r hr a).1 p = D.1 (r • p.1 + a, r • p.2 + a) := rfl

theorem edist_affine {r : ℝ} (hr : r ≠ 0) (a : Rd d) (D : ContMetric d) (x y : Rd d) :
    edist ((D.affine r hr a).pt x) ((D.affine r hr a).pt y) =
      edist (D.pt (r • x + a)) (D.pt (r • y + a)) := by
  rw [edist_pt, edist_pt, affine_apply]

end ContMetric

end HigherDimLQGMetric
