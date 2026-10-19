import GaussianLQG.Uniform.InterfacesLFPP
import LQGMetric.Papers.DDDF.S6P28U1Sum

/-!
# U12, deterministic part I: boxes, offset unit squares and translations

Phase B, packet PB-U12 (ledger `blueprint/phaseB/uniform-ledger.tex`, U12 and Finding `fd:U12`;
audit B-0b, finding S-2). The chaining templates of `LQGMetric` (`S6P28U.chain_restr`,
`LQGMetric/Papers/DDDF/S6P28U1Geo.lean`) work on the unit square `[0,1]²`. A general domain is
handled by covering it with translated unit squares `c + [0,1]²`, `c ∈ A` (`ChainGeom`): two points
whose coordinates differ by less than `1/2` lie in a common square, and the template is applied to
the translated field `f(· + c)` (`lfppDOn_translate`, `len21_translate`).

* `ChainGeom A Q T P`: the covering data (offsets `A`, the box `Q` carrying the squares and the
  supremum of the field, the pair set `T`, the number `P` of pieces for far pairs).
* `chainGeom_unit`: one square, `A = {0}`, `Q = T = [0,1]²` (ledger U12a, audit S-2 (i)).
* `chainGeom_box`: the half-integer offsets `(-N + i/2, -N + j/2)`, `Q = [-N,N]²`,
  `T = [-R,R]² = boxIn R`, `N = ⌈R⌉₊` (ledger U12, audit S-2 (ii)).
* `famH`, `famS` with motions `jH`, `jS`: the halves of the dyadic squares (`S6D.hm`) and the
  shifted squares (`S6P28U.hmS`) of all offset squares; `jH_sub`, `jS_sub`: they lie in `Q`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform
namespace Holder

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.Blueprint

/-! ### Elementary facts on `[0,1]²` and the boxes -/

lemma mem_closedUnitSquare_iff {z : ℂ} :
    z ∈ closedUnitSquare ↔ 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1 := Iff.rfl

lemma boxIn_eq_reProdIm (R : ℝ) : boxIn R = Icc (-R) R ×ℂ Icc (-R) R := by
  ext z
  simp only [boxIn, mem_ofPred_eq, Complex.mem_reProdIm, mem_Icc, abs_le]

lemma isCompact_boxIn (R : ℝ) : IsCompact (boxIn R) := by
  rw [boxIn_eq_reProdIm]
  exact Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))

lemma convex_boxIn (R : ℝ) : Convex ℝ (boxIn R) := by
  have e : boxIn R = Complex.reLm ⁻¹' Icc (-R) R ∩ Complex.imLm ⁻¹' Icc (-R) R := by
    ext z
    simp only [boxIn, mem_ofPred_eq, mem_inter_iff, mem_preimage, Complex.reLm_coe,
      Complex.imLm_coe, mem_Icc, abs_le]
  rw [e]
  exact ((convex_Icc _ _).linear_preimage _).inter ((convex_Icc _ _).linear_preimage _)

lemma isCompact_closedUnitSquare' : IsCompact closedUnitSquare := by
  have e : closedUnitSquare = Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := by
    ext z
    simp only [closedUnitSquare, mem_ofPred_eq, Complex.mem_reProdIm, mem_Icc, and_assoc]
  rw [e]
  exact Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))

lemma boxIn_mono {R R' : ℝ} (h : R ≤ R') : boxIn R ⊆ boxIn R' :=
  fun _ hz => ⟨hz.1.trans h, hz.2.trans h⟩

lemma boxIn_sub_boxOut (R : ℝ) {N : ℝ} (hN : N ≤ R + 1) : boxIn N ⊆ boxOut R :=
  fun _ hz => ⟨hz.1.trans hN, hz.2.trans hN⟩

/-! ### Translations of the LFPP distances -/

/-- the internal distance as a crossing length between singletons -/
lemma crossLenIn_singleton' (ξ : ℝ) (f : ℂ → ℝ) (S : Set ℂ) (x y : ℂ) :
    crossLenIn ξ f S {x} {y} = lfppDOn ξ f S x y := by
  simp only [crossLenIn, Set.mem_singleton_iff, iInf_iInf_eq_left]; rfl

/-- the internal distance decreases when the domain grows -/
lemma lfppDOn_anti {ξ : ℝ} {φ : ℂ → ℝ} {S T : Set ℂ} (hST : S ⊆ T) (x y : ℂ) :
    lfppDOn ξ φ T x y ≤ lfppDOn ξ φ S x y :=
  le_iInf fun P => iInf_le_of_le ⟨P.1, P.2.1, fun t ht => hST (P.2.2 t ht)⟩ le_rfl

/-- crossing lengths of the translated field (`crossLenIn_image_motion` at `u = 1`) -/
lemma crossLenIn_translate (ξ : ℝ) (f : ℂ → ℝ) (U A B : Set ℂ) (c : ℂ) :
    crossLenIn ξ (fun z => f (z + c)) U A B =
      crossLenIn ξ f ((· + c) '' U) ((· + c) '' A) ((· + c) '' B) := by
  have h := crossLenIn_image_motion ξ f U A B 1 c
  simp only [Circle.coe_one, one_mul] at h
  exact h.symm

/-- internal distances of the translated field -/
lemma lfppDOn_translate (ξ : ℝ) (f : ℂ → ℝ) (S : Set ℂ) (x y c : ℂ) :
    lfppDOn ξ (fun z => f (z + c)) S x y = lfppDOn ξ f ((· + c) '' S) (x + c) (y + c) := by
  rw [← crossLenIn_singleton', ← crossLenIn_singleton', crossLenIn_translate, image_singleton,
    image_singleton]

lemma mot_add (K : ℕ) (u : Circle) (c' c x : ℂ) :
    T20B.mot K u (c' + c) x = T20B.mot K u c' x + c := by
  simp only [T20B.mot]; ring

lemma image_mot_add (K : ℕ) (u : Circle) (c' c : ℂ) (X : Set ℂ) :
    (· + c) '' (T20B.mot K u c' '' X) = T20B.mot K u (c' + c) '' X := by
  rw [image_image]
  congr 1
  funext x
  rw [mot_add]

/-- crossings of moved `2^{-K} R_{2,1}` for the translated field -/
lemma len21_translate (ξ : ℝ) (f : ℂ → ℝ) (K : ℕ) (j : Circle × ℂ) (c : ℂ) :
    S6D.len21 ξ (fun z => f (z + c)) K j = S6D.len21 ξ f K (j.1, j.2 + c) := by
  unfold S6D.len21
  rw [crossLenIn_translate, image_mot_add, image_mot_add, image_mot_add]

/-- the segment bound with the weight bounded on a convex set containing the segment (copy of
`S6P28.lfppDOn_le_of_bound_on`, `LQGMetric/Papers/DDDF/S6P28Up2.lean`, whose imports are heavy) -/
lemma lfppDOn_le_bound {ξ : ℝ} {φ : ℂ → ℝ} {S : Set ℂ} (hS : Convex ℝ S) {z w : ℂ}
    (hz : z ∈ S) (hw : w ∈ S) {B : ℝ} (hB : ∀ x ∈ S, Real.exp (ξ * φ x) ≤ B) :
    lfppDOn ξ φ S z w ≤ ENNReal.ofReal (B * ‖w - z‖) := by
  refine (lfppDOn_le_segCost hS hz hw).trans ?_
  rw [segCost, lfppLen_eq]
  calc ∫⁻ t in Icc (0 : ℝ) 1, lenDens ξ φ (segPath z w) t
      ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (B * ‖w - z‖) := by
        refine setLIntegral_mono measurable_const fun u hu => ?_
        rw [lenDens_segPath]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (hB _ (segPath_mem hS hz hw hu)) (norm_nonneg _))
    _ = ENNReal.ofReal (B * ‖w - z‖) := by simp

/-- the segment bound with `|φ| ≤ M` on a convex set, `ξ ≥ 0` -/
lemma lfppDOn_le_exp {ξ : ℝ} (hξ : 0 ≤ ξ) {φ : ℂ → ℝ} {S : Set ℂ} (hS : Convex ℝ S) {M : ℝ}
    (hM : ∀ x ∈ S, |φ x| ≤ M) {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) :
    lfppDOn ξ φ S z w ≤ ENNReal.ofReal (Real.exp (ξ * M) * ‖w - z‖) :=
  lfppDOn_le_bound hS hz hw fun x hx =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM x hx)) hξ)

/-! ### The covering data -/

/-- **Covering data** for the chaining on a general domain: offsets `A` of unit squares
`c + [0,1]² ⊆ Q`, which cover `Q`; every two points of the pair set `T ⊆ Q` whose coordinates
differ by less than `1/2` lie in a common square; `T` is convex and its coordinate differences are
`< P/2`, so the segment between two points of `T` is cut into `P` pieces of the first kind. -/
structure ChainGeom (A : Finset ℂ) (Q T : Set ℂ) (P : ℕ) : Prop where
  convex_Q : Convex ℝ Q
  compact_Q : IsCompact Q
  sq_sub : ∀ c ∈ A, ∀ z ∈ closedUnitSquare, z + c ∈ Q
  coverQ : ∀ x ∈ Q, ∃ c ∈ A, x - c ∈ closedUnitSquare
  T_sub : T ⊆ Q
  convex_T : Convex ℝ T
  cover : ∀ x ∈ T, ∀ y ∈ T, |x.re - y.re| < 1 / 2 → |x.im - y.im| < 1 / 2 →
    ∃ c ∈ A, x - c ∈ closedUnitSquare ∧ y - c ∈ closedUnitSquare
  P_pos : 0 < P
  pieces : ∀ x ∈ T, ∀ y ∈ T, |x.re - y.re| < P / 2 ∧ |x.im - y.im| < P / 2

lemma ChainGeom.nonempty_A {A : Finset ℂ} {Q T : Set ℂ} {P : ℕ} (G : ChainGeom A Q T P)
    {x : ℂ} (hx : x ∈ Q) : A.Nonempty := by
  obtain ⟨c, hc, -⟩ := G.coverQ x hx
  exact ⟨c, hc⟩

/-- the unit square: one offset -/
theorem chainGeom_unit : ChainGeom {0} closedUnitSquare closedUnitSquare 3 where
  convex_Q := LFPP.convex_closedUnitSquare
  compact_Q := isCompact_closedUnitSquare'
  sq_sub := fun c hc z hz => by
    rw [Finset.mem_singleton] at hc
    rw [hc, add_zero]; exact hz
  coverQ := fun x hx => ⟨0, Finset.mem_singleton_self 0, by rw [sub_zero]; exact hx⟩
  T_sub := subset_rfl
  convex_T := LFPP.convex_closedUnitSquare
  cover := fun x hx y hy _ _ =>
    ⟨0, Finset.mem_singleton_self 0, by rw [sub_zero]; exact hx, by rw [sub_zero]; exact hy⟩
  P_pos := by norm_num
  pieces := fun x hx y hy => by
    obtain ⟨a1, a2, a3, a4⟩ := hx
    obtain ⟨b1, b2, b3, b4⟩ := hy
    have h1 : |x.re - y.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have h2 : |x.im - y.im| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    constructor <;> push_cast <;> linarith

/-! ### The half-integer offsets of `[-N, N]²` -/

/-- the lower-left corner `(-N + i/2, -N + j/2)` of the offset square `(i, j)` -/
def cOff (N i j : ℕ) : ℂ := ⟨-(N : ℝ) + i / 2, -(N : ℝ) + j / 2⟩

/-- the offsets of `[-N, N]²`: `i, j < 4N - 1` -/
def offBox (N : ℕ) : Finset ℂ :=
  (Finset.range (4 * N - 1) ×ˢ Finset.range (4 * N - 1)).image fun ij => cOff N ij.1 ij.2

lemma card_offBox_le (N : ℕ) : ((offBox N).card : ℝ) ≤ (4 * N) ^ 2 := by
  have h1 : (offBox N).card ≤ (4 * N - 1) * (4 * N - 1) := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Finset.card_range]
  have h2 : (4 * N - 1) * (4 * N - 1) ≤ (4 * N) * (4 * N) :=
    Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have h3 : ((offBox N).card : ℝ) ≤ ((4 * N * (4 * N) : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
  rw [sq]; push_cast at h3; exact h3

/-- one coordinate: two close points of `[-N, N]` lie in a common `[-N + i/2, -N + i/2 + 1]` -/
lemma exists_half_idx {N : ℕ} (hN : 1 ≤ N) {s t : ℝ} (hs : |s| ≤ N) (ht : |t| ≤ N)
    (hst : |s - t| < 1 / 2) :
    ∃ i : ℕ, i < 4 * N - 1 ∧ (-(N : ℝ) + i / 2 ≤ s ∧ s ≤ -(N : ℝ) + i / 2 + 1) ∧
      (-(N : ℝ) + i / 2 ≤ t ∧ t ≤ -(N : ℝ) + i / 2 + 1) := by
  set m := min s t with hm
  have hms : m ≤ s := min_le_left _ _
  have hmt : m ≤ t := min_le_right _ _
  obtain ⟨hst1, hst2⟩ := abs_lt.1 hst
  have hsm : s < m + 1 / 2 := by
    rcases min_choice s t with h | h <;> rw [hm, h] <;> linarith
  have htm : t < m + 1 / 2 := by
    rcases min_choice s t with h | h <;> rw [hm, h] <;> linarith
  have hsN := abs_le.1 hs
  have htN := abs_le.1 ht
  have hu : 0 ≤ 2 * (m + N) := by
    rcases min_choice s t with h | h <;> rw [hm, h] <;> linarith
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases le_total ⌊2 * (m + N)⌋₊ (4 * N - 2) with hle | hle
  · refine ⟨⌊2 * (m + N)⌋₊, by omega, ?_⟩
    have h1 : (⌊2 * (m + N)⌋₊ : ℝ) ≤ 2 * (m + N) := Nat.floor_le hu
    have h2 : 2 * (m + N) < ⌊2 * (m + N)⌋₊ + 1 := Nat.lt_floor_add_one _
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · refine ⟨4 * N - 2, by omega, ?_⟩
    have hc : ((4 * N - 2 : ℕ) : ℝ) = 4 * N - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have h1 : ((4 * N - 2 : ℕ) : ℝ) ≤ 2 * (m + N) :=
      (Nat.cast_le.2 hle).trans (Nat.floor_le hu)
    rw [hc] at h1 ⊢
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma add_cOff_mem {N i j : ℕ} (hi : i < 4 * N - 1) (hj : j < 4 * N - 1) {z : ℂ}
    (hz : z ∈ closedUnitSquare) : z + cOff N i j ∈ boxIn (N : ℝ) := by
  obtain ⟨a1, a2, a3, a4⟩ := hz
  have hi' : (i : ℝ) + 2 ≤ 4 * N := by
    have : i + 2 ≤ 4 * N := by omega
    exact_mod_cast this
  have hj' : (j : ℝ) + 2 ≤ 4 * N := by
    have : j + 2 ≤ 4 * N := by omega
    exact_mod_cast this
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩⟩ <;>
    simp only [cOff, Complex.add_re, Complex.add_im] <;> linarith

/-- `[-N, N]²` with the half-integer offsets, pairs in `[-R, R]²`, `R ≤ N` -/
theorem chainGeom_box {N : ℕ} (hN : 1 ≤ N) {R : ℝ} (hRN : R ≤ N) :
    ChainGeom (offBox N) (boxIn (N : ℝ)) (boxIn R) (4 * N + 1) where
  convex_Q := convex_boxIn _
  compact_Q := isCompact_boxIn _
  sq_sub := fun c hc z hz => by
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.1 hc
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hij
    exact add_cOff_mem hij.1 hij.2 hz
  coverQ := fun x hx => by
    obtain ⟨i, hi, hx1, -⟩ := exists_half_idx hN hx.1 hx.1 (by simp)
    obtain ⟨j, hj, hy1, -⟩ := exists_half_idx hN hx.2 hx.2 (by simp)
    refine ⟨cOff N i j, Finset.mem_image.2 ⟨(i, j), by simp [hi, hj], rfl⟩, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [cOff, Complex.sub_re, Complex.sub_im] <;> linarith
  T_sub := boxIn_mono hRN
  convex_T := convex_boxIn _
  cover := fun x hx y hy hre him => by
    have hx' := boxIn_mono hRN hx
    have hy' := boxIn_mono hRN hy
    obtain ⟨i, hi, hx1, hy1⟩ := exists_half_idx hN hx'.1 hy'.1 hre
    obtain ⟨j, hj, hx2, hy2⟩ := exists_half_idx hN hx'.2 hy'.2 him
    refine ⟨cOff N i j, Finset.mem_image.2 ⟨(i, j), by simp [hi, hj], rfl⟩, ?_, ?_⟩ <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [cOff, Complex.sub_re, Complex.sub_im] <;> linarith
  P_pos := by omega
  pieces := fun x hx y hy => by
    have h1 := abs_le.1 hx.1
    have h2 := abs_le.1 hx.2
    have h3 := abs_le.1 hy.1
    have h4 := abs_le.1 hy.2
    have hN' : (R : ℝ) ≤ N := hRN
    constructor <;> rw [abs_lt] <;> push_cast <;> constructor <;> linarith

/-! ### The families of rectangles -/

/-- the halves of the dyadic squares of level `k` of all offset squares -/
def famH (A : Finset ℂ) (k : ℕ) : Finset (ℂ × ((ℕ × ℕ) × Fin 4)) := A ×ˢ S6D.idxSet k

/-- the motion of a half: `S6D.hm` moved by the offset -/
def jH (k : ℕ) (r : ℂ × ((ℕ × ℕ) × Fin 4)) : Circle × ℂ :=
  ((S6D.hm k r.2.1.1 r.2.1.2 r.2.2).1, (S6D.hm k r.2.1.1 r.2.1.2 r.2.2).2 + r.1)

/-- the shifted squares of scale `K` of all offset squares -/
def famS (A : Finset ℂ) (K : ℕ) : Finset (ℂ × ((ℕ × ℕ) × Fin 4)) := A ×ˢ S6P28U.idxS K

/-- the motion of a shifted square: `S6P28U.hmS` moved by the offset -/
def jS (K : ℕ) (r : ℂ × ((ℕ × ℕ) × Fin 4)) : Circle × ℂ :=
  ((S6P28U.hmS K r.2.1.1 r.2.1.2 r.2.2).1, (S6P28U.hmS K r.2.1.1 r.2.1.2 r.2.2).2 + r.1)

lemma card_famH (A : Finset ℂ) (k : ℕ) : ((famH A k).card : ℝ) = A.card * 4 ^ (k + 1) := by
  have h : (S6D.idxSet k).card = 4 ^ (k + 1) := by
    simp only [S6D.idxSet, Finset.card_product, Finset.card_range, Finset.card_univ,
      Fintype.card_fin]
    rw [← mul_pow, pow_succ]; norm_num
  rw [famH, Finset.card_product, h]; push_cast; ring

lemma card_famS_le (A : Finset ℂ) (K : ℕ) : ((famS A K).card : ℝ) ≤ A.card * 4 ^ (K + 1) := by
  rw [famS, Finset.card_product, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left (S6P28U.card_idxS_le K) (Nat.cast_nonneg _)

lemma jH_sub {A : Finset ℂ} {Q T : Set ℂ} {P : ℕ} (G : ChainGeom A Q T P) {k : ℕ}
    {r : ℂ × ((ℕ × ℕ) × Fin 4)} (hr : r ∈ famH A k) :
    T20B.mot (k + 1) (jH k r).1 (jH k r).2 '' (rectAB 2 1).toSet ⊆ Q := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [famH, S6D.idxSet, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
    and_true] at hr
  have hmem := S6D.hm_sub hr.2.1 hr.2.2 r.2.2 ⟨x, hx, rfl⟩
  simp only [jH]
  rw [mot_add]
  exact G.sq_sub r.1 hr.1 _ hmem

lemma jS_sub {A : Finset ℂ} {Q T : Set ℂ} {P : ℕ} (G : ChainGeom A Q T P) {K : ℕ}
    {r : ℂ × ((ℕ × ℕ) × Fin 4)} (hr : r ∈ famS A K) :
    T20B.mot K (jS K r).1 (jS K r).2 '' (rectAB 2 1).toSet ⊆ Q := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [famS, S6P28U.idxS, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
    and_true] at hr
  have hmem := S6P28U.hmS_sub (K := K) (i := r.2.1.1) (j := r.2.1.2) (by omega) (by omega) r.2.2
    ⟨x, hx, rfl⟩
  simp only [jS]
  rw [mot_add]
  exact G.sq_sub r.1 hr.1 _ hmem

end Holder
end Uniform
end GaussianLQG
