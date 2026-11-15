/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLuDense
import InteractingSLE.Spec.Supplement.SBLyPath
import InteractingSLE.Spec.Supplement.SBLvPinchUse
import InteractingSLE.Spec.Supplement.SBLwChart
import InteractingSLE.Spec.Supplement.GW1WalkFinishTip
import InteractingSLE.Spec.Supplement.GW2aConnMove

/-!
# SB3's stage input (I5) without the counterflow: retained prefixes are paths with finite fibres

Packet PROVE-T14-SBLEAVES6. In the counterflow setting (I5) is `Ly.ae_isPrefixPath_of_cf`, through GW1's piece
simplicity (each new piece meets the old union only at its seed). Without the counterflow a piece may bounce off the old
union, but (I5) asks only for a path with **finite fibres**. It is built by joining paths:

* `IsFFPath`, `isPrefixPath_join`: a path with finite fibres from a point of the image of a prefix path is appended,
  going back along the prefix path to that point first (`backPath`); `PInv` (a prefix path, or the single point `u`)
  is stable under such joins (`PInv.join`, `PInv.union_of_subset`);
* `segPath`: connectors are segments;
* **`pinv_prefix_walk`** (deterministic): along a boundary walk with regular launches, injective traces and the tip
  coordinates (GW1's `WalkTipCoordinates`), the physical set after `n` instructions with the bridge `[u, 0]` satisfies
  `PInv` while the run is not finished, and the current point lies in the physical set. A new piece is the path
  `t ↦ g(α(tζ))`: `α` injective, `g` (the boundary map of the launch chart) with finite fibres by pinch-finiteness
  (`finite_fibre_of_isDomainChart`, applied to the path of the old union), started at the seed `g(0)`, the current
  point; a connector is a segment from the current point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.SB.LuM

open Lx Exist.Staged Exist.StagedLaw

/-! ### Paths with finite fibres -/

/-- A path on `[0, 1]` in `ℍ̄` with finite fibres. -/
def IsFFPath (q : ℝ → ℂ) : Prop :=
  ContinuousOn q (Icc 0 1) ∧ (∀ z, (q ⁻¹' {z} ∩ Icc 0 1).Finite) ∧ ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (q s).im

theorem IsPrefixPath.isFFPath {p : ℝ → ℂ} {u : ℝ} {A : Set ℂ} (hp : IsPrefixPath p u A) : IsFFPath p :=
  ⟨hp.1, hp.2.2.1, hp.2.2.2.1⟩

/-- The path `p` run backwards from `p 1` to `p s₀`. -/
def backPath (p : ℝ → ℂ) (s₀ t : ℝ) : ℂ := p (1 - t * (1 - s₀))

theorem mem_Icc_back {s₀ t : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    1 - t * (1 - s₀) ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hs₀
  obtain ⟨t0, t1⟩ := ht
  constructor <;> nlinarith

theorem isFFPath_backPath {p : ℝ → ℂ} (hp : IsFFPath p) {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) (hlt : s₀ < 1) :
    IsFFPath (backPath p s₀) := by
  obtain ⟨hc, hf, hH⟩ := hp
  refine ⟨hc.comp (by fun_prop) fun t ht => mem_Icc_back hs₀ ht, fun z => ?_, fun t ht => hH _ (mem_Icc_back hs₀ ht)⟩
  refine ((hf z).image fun s => (1 - s) / (1 - s₀)).subset ?_
  rintro t ⟨htz, ht⟩
  refine ⟨1 - t * (1 - s₀), ⟨htz, mem_Icc_back hs₀ ht⟩, ?_⟩
  have : (1 : ℝ) - s₀ ≠ 0 := by linarith
  field_simp
  ring

theorem image_backPath_subset {p : ℝ → ℂ} {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) :
    backPath p s₀ '' Icc 0 1 ⊆ p '' Icc 0 1 := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨_, mem_Icc_back hs₀ ht, rfl⟩

/-- The concatenation of two paths with finite fibres. -/
theorem isFFPath_concat {p q : ℝ → ℂ} (hp : IsFFPath p) (hq : IsFFPath q) (hj : p 1 = q 0) :
    IsFFPath (Lw.concatPath p q) ∧ Lw.concatPath p q '' Icc 0 1 = p '' Icc 0 1 ∪ q '' Icc 0 1 := by
  have himg := Lw.image_concatPath hj
  refine ⟨⟨Lw.continuousOn_concatPath hp.1 hq.1 hj, Lw.finite_fibre_concatPath hj hp.2.1 hq.2.1, fun s hs => ?_⟩,
    himg⟩
  have hmem : Lw.concatPath p q s ∈ Lw.concatPath p q '' Icc 0 1 := mem_image_of_mem _ hs
  rw [himg] at hmem
  rcases hmem with ⟨t, ht, e⟩ | ⟨t, ht, e⟩
  · rw [← e]; exact hp.2.2 t ht
  · rw [← e]; exact hq.2.2 t ht

/-- **Joining a path at a point of a prefix path.** -/
theorem isPrefixPath_join {p q : ℝ → ℂ} {u : ℝ} {A : Set ℂ} (hp : IsPrefixPath p u A) (hq : IsFFPath q)
    (hq0 : q 0 ∈ A) : ∃ r, IsPrefixPath r u (A ∪ q '' Icc 0 1) := by
  have hpf := IsPrefixPath.isFFPath hp
  obtain ⟨-, hp0, -, -, hpA⟩ := hp
  rw [← hpA] at hq0 ⊢
  obtain ⟨s₀, hs₀, hps₀⟩ := hq0
  rcases hs₀.2.lt_or_eq with hlt | heq
  · have hpb := isFFPath_backPath hpf hs₀ hlt
    have hj2 : backPath p s₀ 1 = q 0 := by simp [backPath, hps₀]
    obtain ⟨hbq, hbqi⟩ := isFFPath_concat hpb hq hj2
    have hj1 : p 1 = Lw.concatPath (backPath p s₀) q 0 := by
      rw [Lw.concatPath_zero]; simp [backPath]
    obtain ⟨hr, hri⟩ := isFFPath_concat hpf hbq hj1
    refine ⟨Lw.concatPath p (Lw.concatPath (backPath p s₀) q), hr.1, by rw [Lw.concatPath_zero, hp0], hr.2.1,
      hr.2.2, ?_⟩
    rw [hri, hbqi, ← union_assoc, union_eq_left.2 (image_backPath_subset hs₀)]
  · subst heq
    obtain ⟨hr, hri⟩ := isFFPath_concat hpf hq hps₀
    exact ⟨Lw.concatPath p q, hr.1, by rw [Lw.concatPath_zero, hp0], hr.2.1, hr.2.2, hri⟩

/-- **The induction state**: a prefix path from `u`, or the single point `u`. -/
def PInv (u : ℝ) (A : Set ℂ) : Prop := A = {(u : ℂ)} ∨ ∃ p, IsPrefixPath p u A

theorem PInv.join {u : ℝ} {A : Set ℂ} (hA : PInv u A) {q : ℝ → ℂ} (hq : IsFFPath q) (hq0 : q 0 ∈ A) :
    PInv u (A ∪ q '' Icc 0 1) := by
  rcases hA with rfl | ⟨p, hp⟩
  · rw [mem_singleton_iff] at hq0
    have e : ({(u : ℂ)} : Set ℂ) ∪ q '' Icc 0 1 = q '' Icc 0 1 :=
      union_eq_right.2 (singleton_subset_iff.2 ⟨0, ⟨le_rfl, zero_le_one⟩, hq0⟩)
    rw [e]
    exact Or.inr ⟨q, hq.1, hq0, hq.2.1, hq.2.2, rfl⟩
  · exact Or.inr (isPrefixPath_join hp hq hq0)

theorem PInv.union_of_subset {u : ℝ} {A B : Set ℂ} (hA : PInv u A) (hB : B ⊆ A) : PInv u (A ∪ B) := by
  rwa [union_eq_left.2 hB]

/-! ### Segments -/

/-- The segment from `a` to `c` on the real line. -/
def segPath (a c t : ℝ) : ℂ := ((a + t * (c - a) : ℝ) : ℂ)

theorem segPath_zero (a c : ℝ) : segPath a c 0 = a := by simp [segPath]

theorem isFFPath_segPath {a c : ℝ} (h : a ≠ c) : IsFFPath (segPath a c) := by
  refine ⟨(Complex.continuous_ofReal.comp (by fun_prop)).continuousOn, fun z => ?_, fun s _ => by simp [segPath]⟩
  refine Lw.finite_fibre_of_injOn (fun s _ t _ hst => ?_) z
  have e := Complex.ofReal_injective hst
  have hca : c - a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  exact mul_right_cancel₀ hca (by linarith)

theorem image_segPath {a c : ℝ} (h : a ≠ c) :
    segPath a c '' Icc 0 1 = ((↑) : ℝ → ℂ) '' Icc (min a c) (max a c) := by
  ext z
  constructor
  · rintro ⟨t, ⟨t0, t1⟩, rfl⟩
    refine ⟨a + t * (c - a), ⟨?_, ?_⟩, rfl⟩
    · rcases le_total a c with hac | hac
      · rw [min_eq_left hac]; nlinarith
      · rw [min_eq_right hac]; nlinarith
    · rcases le_total a c with hac | hac
      · rw [max_eq_right hac]; nlinarith
      · rw [max_eq_left hac]; nlinarith
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    have hca : c - a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    refine ⟨(x - a) / (c - a), ⟨?_, ?_⟩, ?_⟩
    · rcases lt_or_gt_of_ne h with hac | hac
      · rw [min_eq_left hac.le] at hx1
        exact div_nonneg (by linarith) (by linarith)
      · rw [max_eq_left hac.le] at hx2
        exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · rcases lt_or_gt_of_ne h with hac | hac
      · rw [max_eq_right hac.le] at hx2
        rw [div_le_one (by linarith)]; linarith
      · rw [min_eq_right hac.le] at hx1
        rw [div_le_one_of_neg (by linarith)]; linarith
    · simp only [segPath]
      congr 1
      field_simp
      ring

/-! ### Steps of a walk -/

section Steps

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

theorem arcs_moveAlong_append (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    (ExplState.moveAlong s r x m).2.1 = s.2.1 ++ [if r then Icc (stPt s) x else Icc x (stPt s)] := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ', recR, recL⟩ := s
  rfl

/-- **A boundary continuation** keeps the connectors and the current point, moves along a connector away from the
current point, or follows the boundary to the end. -/
theorem contStep_four_cases (s : ExplState) (vStop : Option ℝ) (pref : Bool) :
    ((ExplState.contStep κ b jumps s vStop pref).2.1 = s.2.1 ∧
        stPt (ExplState.contStep κ b jumps s vStop pref) = stPt s) ∨
      (∃ (x : ℝ) (mk : Bool), ExplState.contStep κ b jumps s vStop pref = ExplState.moveAlong s true x mk ∧
        stPt s < x) ∨
      (∃ (x : ℝ) (mk : Bool), ExplState.contStep κ b jumps s vStop pref = ExplState.moveAlong s false x mk ∧
        x < stPt s) ∨
      ∃ r : Bool, ExplState.contStep κ b jumps s vStop pref = ExplState.moveToEnd s r := by
  rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) s vStop pref with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩
  · rw [e]; exact Or.inl ⟨rfl, rfl⟩
  · rw [e]; exact Or.inl ⟨rfl, rfl⟩
  · have hne : (ExplState.contStep κ b jumps s vStop pref).2.1 ≠ s.2.1 := by
      rw [e, arcs_moveAlong_append]
      intro h
      have := congrArg List.length h
      simp at this
    rcases GW2aConn.contStep_arc_cases (κ := κ) (b := b) (jumps := jumps) s vStop pref hne with
      ⟨-, e'⟩ | ⟨-, e'⟩
    · rcases GW2aConn.rMove_rBranch (κ := κ) (b := b) (jumps := jumps) s vStop with
        ⟨x', mk, e'', hlt, -⟩ | ⟨e'', -⟩
      · exact Or.inr (Or.inl ⟨x', mk, e'.trans e'', hlt⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨true, e'.trans e''⟩))
    · rcases GW2aConn.lMove_lBranch (κ := κ) (b := b) (jumps := jumps) s vStop with
        ⟨x', mk, e'', hlt, -⟩ | ⟨e'', -⟩
      · exact Or.inr (Or.inr (Or.inl ⟨x', mk, e'.trans e'', hlt⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨false, e'.trans e''⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨r, e⟩))

/-- **A step without launch** keeps the connectors and the current point, moves along a connector away from the
current point, or follows the boundary to the end. -/
theorem run_succ_noLaunch_cases (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ}
    (hnone : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n = none) :
    ((ExplState.run κ b jumps spec D (n + 1)).2.1 = (ExplState.run κ b jumps spec D n).2.1 ∧
        stPt (ExplState.run κ b jumps spec D (n + 1)) = stPt (ExplState.run κ b jumps spec D n)) ∨
      (∃ (x : ℝ) (mk : Bool), ExplState.run κ b jumps spec D (n + 1) =
        ExplState.moveAlong (ExplState.run κ b jumps spec D n) true x mk ∧
          stPt (ExplState.run κ b jumps spec D n) < x) ∨
      (∃ (x : ℝ) (mk : Bool), ExplState.run κ b jumps spec D (n + 1) =
        ExplState.moveAlong (ExplState.run κ b jumps spec D n) false x mk ∧
          x < stPt (ExplState.run κ b jumps spec D n)) ∨
      ∃ r : Bool, ExplState.run κ b jumps spec D (n + 1) =
        ExplState.moveToEnd (ExplState.run κ b jumps spec D n) r := by
  set s := ExplState.run κ b jumps spec D n with hs
  have hrun := run_succ (κ := κ) (b := b) (jumps := jumps) spec D n
  rw [← hs] at hrun
  rw [hrun] at hnone ⊢
  cases hk : spec.2.2[n]? with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some ins =>
    rw [hk] at hnone
    simp only at hnone ⊢
    rcases ins with ⟨θ', t⟩ | pref | ⟨v, pref⟩
    · have e0 : ExplState.step κ b jumps spec.2.1 D s (Sum.inl (θ', t), n) =
          ExplState.flowStep κ b spec.2.1 s n (D n) θ' t := rfl
      rw [e0] at hnone ⊢
      rcases flowStep_trichotomy (κ := κ) (b := b) spec.2.1 s n (D n) θ' t with e | e | e <;> rw [e] at hnone ⊢
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · rw [launches_launch, Function.update_self] at hnone
        exact absurd hnone (Option.some_ne_none _)
    · exact contStep_four_cases s none pref
    · exact contStep_four_cases s (some v) pref

end Steps

/-! ### Reparametrized pieces -/

/-- A path on `[0, T]`, `T > 0`, with finite fibres, reparametrized by `[0, 1]`. -/
theorem isFFPath_reparam {φ : ℝ≥0 → ℂ} {T : ℝ≥0} (hT : 0 < T) (hc : ContinuousOn φ (Iic T))
    (hf : ∀ z, {s | s ≤ T ∧ φ s = z}.Finite) (hH : ∀ s ≤ T, 0 ≤ (φ s).im) :
    IsFFPath (fun t : ℝ => φ (t * T).toNNReal) ∧ (fun t : ℝ => φ (t * T).toNNReal) '' Icc 0 1 = φ '' Iic T := by
  have hTr : (0 : ℝ) < T := hT
  have hmaps : ∀ t ∈ Icc (0 : ℝ) 1, (t * T).toNNReal ≤ T := fun t ht => by
    rw [Real.toNNReal_le_iff_le_coe]
    nlinarith [ht.2, ht.1]
  have hcoe : ∀ t ∈ Icc (0 : ℝ) 1, (((t * T).toNNReal : ℝ≥0) : ℝ) = t * T := fun t ht =>
    Real.coe_toNNReal _ (mul_nonneg ht.1 hTr.le)
  refine ⟨⟨hc.comp (continuous_real_toNNReal.comp (continuous_id.mul continuous_const)).continuousOn hmaps,
    fun z => ?_, fun t ht => hH _ (hmaps t ht)⟩, ?_⟩
  · refine ((hf z).image fun s : ℝ≥0 => (s : ℝ) / T).subset ?_
    rintro t ⟨htz, ht⟩
    refine ⟨(t * T).toNNReal, ⟨hmaps t ht, htz⟩, ?_⟩
    simp only
    rw [hcoe t ht]
    field_simp
  · ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, hmaps t ht, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨(s : ℝ) / T, ⟨div_nonneg s.coe_nonneg hTr.le, (div_le_one hTr).2 hs⟩, ?_⟩
      simp only
      congr 1
      rw [div_mul_cancel₀ _ hTr.ne', Real.toNNReal_coe]

/-! ### The physical set of a walk with regular launches is a prefix path -/

section Walk

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- **The seed and the end of a launched piece** are the current points before and after the launch (GW1's tip
coordinates), read through the boundary values of the launch chart. -/
theorem bdVal_tip_walk {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (htip : GW1WalkChain.WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps θ right) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n ≠ none) :
    bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) (trOf (D n) 0) =
        stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) ∧
      ((D n).2 ≠ ⊤ → bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n))
        (trOf (D n) (D n).2.toNNReal) =
          stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1))) := by
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  have ht := Lx.instrTime_boundaryWalk_of_launch hcθ
  obtain ⟨-, -, hc⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hcθ
  have hcc := isConformal_runChart_of_reg (boundaryWalkSpec b jumps θ right) hP n
  have hcb := (GW1P.isClosed_pieces_run (boundaryWalkSpec b jumps θ right) D hP n).1
  obtain ⟨g, -, -, -, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
  have hαH : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ (D n).2 → 0 ≤ (trOf (D n) s).im := fun s hs =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 hs
  have key : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → ∀ z : ℂ,
      (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).tipAt
        (fun r : ℝ≥0 => (D n).1 (min (r : ℝ≥0∞) (D n).2).toNNReal) t z →
      bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) (trOf (D n) t) = z := by
    intro t htζ z hz
    have h1 := CounterflowRange.tendsto_tip_stopped_of_tendsto
      (c := stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) (f := g) hα hPR.2.1
      hPR.1 htζ (hgt _ (hαH t htζ))
    rw [bdVal_eq_of_tendsto (hαH t htζ) (hgt _ (hαH t htζ))]
    exact tendsto_nhds_unique h1 hz
  have h := htip n c θ' hcθ
  simp only [ht, min_top_left] at h
  obtain ⟨h0, h1⟩ := h
  rw [hc] at h0 h1
  exact ⟨key 0 (by simp) _ h0, fun hf => key _ ENNReal.coe_toNNReal_le_self _ (h1 hf)⟩

/-- The fill of a real set is the fill of the empty set. -/
theorem fillH_ofReal (T : Set ℝ) : fillH (((↑) : ℝ → ℂ) '' T) = fillH ∅ := by
  simpa using Lw.fillH_union_real ∅ T

/-- **Pinch-finiteness at the run chart**: while the run is not finished and its physical set with the bridge
satisfies `PInv`, the boundary map of the run chart has finite fibres on `ℍ̄`. -/
theorem finite_fibre_bdry_walk {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) {n : ℕ}
    (hnot : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) ≠ GW1Conn.stDone) {u : ℝ}
    (hA : PInv u (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0))
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).2.1 H)
    (hgb : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂) :
    ∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite := by
  obtain ⟨p, hpc, hpf, hfill⟩ : ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ (∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) ∧
      fillH (p '' Icc 0 1) = fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n) := by
    rcases hA with hA | ⟨p, hp⟩
    · have h0 : (0 : ℂ) ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n :=
        Or.inl (Or.inl (by simp [boundaryWalkSpec]))
      have hsub : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n ⊆ {(u : ℂ)} :=
        hA ▸ subset_union_left
      have hu0 : (u : ℂ) = 0 := (mem_singleton_iff.1 (hsub h0)).symm
      have hP0 : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n = ((↑) : ℝ → ℂ) '' {0} := by
        rw [image_singleton, Complex.ofReal_zero]
        exact Subset.antisymm (hu0 ▸ hsub) (singleton_subset_iff.2 h0)
      refine ⟨segPath 0 1, (isFFPath_segPath zero_ne_one).1, (isFFPath_segPath zero_ne_one).2.1, ?_⟩
      rw [image_segPath zero_ne_one, hP0, fillH_ofReal, fillH_ofReal]
    · exact ⟨p, hp.1, hp.2.2.1, by rw [hp.2.2.2.2, Lw.fillH_union_real]⟩
  have hD := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) _ D hP n hnot
  rw [← hfill] at hD
  obtain ⟨C₁, C₂, -, hb⟩ := hgb
  have hM : 0 < max C₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hinf : Tendsto g (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ) := by
    refine tendsto_norm_atTop_iff_cobounded.1 (tendsto_atTop_mono' _ ?_
      ((Tendsto.atTop_div_const hM (tendsto_atTop_add_const_right _ (-C₂)
        tendsto_norm_cobounded_atTop)).mono_left inf_le_left))
    refine eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
    have h1 := hb w (le_of_lt (show (0 : ℝ) < w.im from hw))
    have h2 : C₁ * ‖g w‖ ≤ max C₁ 1 * ‖g w‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    rw [div_le_iff₀ hM]
    linarith
  exact Lv.finite_fibre_of_isDomainChart hpc hpf hD hgc hgi hinf

/-- At a launch of a walk no connector is recorded. -/
theorem arcAt_eq_empty_of_launch {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n ≠ none) :
    GW2aCont.arcAt κ b jumps (boundaryWalkSpec b jumps θ right) D n = ∅ := by
  rw [GW2aCont.arcAt_eq_newArc, GW1W.launch_walk hl]
  exact GW2aCont.newArc_of_arcs_eq (GW2aCont.arcs_launch _ _ _ _ _)

theorem stStatus_moveToEnd (s : ExplState) (r : Bool) : stStatus (ExplState.moveToEnd s r) = GW1Conn.stDone := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ', recR, recL⟩ := s
  rfl

theorem stPt_moveAlong (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) : stPt (ExplState.moveAlong s r x m) = x := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ', recR, recL⟩ := s
  rfl

/-- **The physical set of a walk with regular launches, injective traces and GW1's tip coordinates is a prefix
path** (with the bridge `[u, 0]`; or the single point `u = 0`) while the run is not finished, and the current point
lies in it. -/
theorem pinv_prefix_walk {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hinj : ∀ j, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j ≠ none →
      InjOn (trOf (D j)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D j).2})
    (htip : GW1WalkChain.WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps θ right) D) {u : ℝ}
    (hu : u ≤ 0) :
    ∀ n, stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) ≠ GW1Conn.stDone →
      PInv u (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0) ∧
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) : ℂ) ∈
          SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n
  | 0, _ => by
    have e0 : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D 0 = {0} := by
      simp [SB.prefixPhysSet, ExplState.run, ExplState.init, boundaryWalkSpec]
    have hpt : stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D 0) = 0 := by
      simp [ExplState.run, ExplState.init, boundaryWalkSpec]
    rw [e0, hpt]
    refine ⟨?_, by simp⟩
    rw [union_eq_right.2 (singleton_subset_iff.2
      (show (0 : ℂ) ∈ ((↑) : ℝ → ℂ) '' Icc u 0 from ⟨0, ⟨hu, le_rfl⟩, by simp⟩))]
    rcases hu.lt_or_eq with hu' | rfl
    · exact Or.inr (Ly.exists_isPrefixPath_segment hu')
    · left
      simp
  | n + 1, hnd => by
    set A := SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n with hAdef
    set U := ((↑) : ℝ → ℂ) '' Icc u 0 with hU
    have hnd' : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) ≠ GW1Conn.stDone := fun h =>
      hnd (by rw [GW1WalkFinish.done_run_succ _ D h]; exact h)
    obtain ⟨ih, ihpt⟩ := pinv_prefix_walk hP hinj htip hu n hnd'
    rw [prefixPhysSet_succ_walk hP n]
    have e : A ∪ newPiece κ b jumps θ right D n ∪ ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b jumps
        (boundaryWalkSpec b jumps θ right) D n ∪ U = (A ∪ U) ∪ newPiece κ b jumps θ right D n ∪
        ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b jumps (boundaryWalkSpec b jumps θ right) D n := by
      ext z; simp only [mem_union]; tauto
    rw [e]
    by_cases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n ≠ none
    · rw [arcAt_eq_empty_of_launch hl, image_empty, union_empty]
      obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
      have hPR := pieceRegular_of_launch hP hl
      have hα := isGeneratingTrace_trOf hPR
      have hζ : (D n).2 ≠ ⊤ := fun hD => hnd (Lx.stStatus_run_succ_of_launch_top _ D hcθ
        (Lx.instrTime_boundaryWalk_of_launch hcθ) hD)
      obtain ⟨htip0, htipT⟩ := bdVal_tip_walk hP htip hl
      rw [hα.1] at htip0
      have htipT' := htipT hζ
      set T := (D n).2.toNNReal with hT
      have hζT : (D n).2 = (T : ℝ≥0∞) := (ENNReal.coe_toNNReal hζ).symm
      set φ : ℝ≥0 → ℂ := fun s => bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n))
        (trOf (D n) s) with hφ
      have hNP : newPiece κ b jumps θ right D n = φ '' Iic T := by
        ext z
        simp only [newPiece, mem_ofPred_eq, mem_image, mem_Iic, hφ, hζT, ENNReal.coe_le_coe]
        exact ⟨fun h => h.2, fun h => ⟨hl, h⟩⟩
      have hTmem : φ T ∈ newPiece κ b jumps θ right D n := by rw [hNP]; exact ⟨T, mem_Iic.2 le_rfl, rfl⟩
      have hφ0 : φ 0 = stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) := by
        simp only [hφ, hα.1]; exact htip0
      refine ⟨?_, Or.inl (Or.inr (htipT' ▸ hTmem))⟩
      rcases eq_or_ne T 0 with hT0 | hT0
      · refine ih.union_of_subset ?_
        rw [hNP, hT0]
        rintro _ ⟨s, hs, rfl⟩
        rw [nonpos_iff_eq_zero.1 (mem_Iic.1 hs), hφ0]
        exact Or.inl ihpt
      · have hcc := isConformal_runChart_of_reg (boundaryWalkSpec b jumps θ right) hP n
        have hcb := (GW1P.isClosed_pieces_run (boundaryWalkSpec b jumps θ right) D hP n).1
        obtain ⟨g, hgc, hgi, hgb, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
        have hfib := finite_fibre_bdry_walk hP hnd' ih hgc hgi hgb
        have hαH : ∀ s ≤ T, 0 ≤ (trOf (D n) s).im := fun s hs =>
          im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 (by rw [hζT]; exact ENNReal.coe_le_coe.2 hs)
        have hφg : ∀ s ≤ T, φ s = g (trOf (D n) s) := fun s hs =>
          bdVal_eq_of_tendsto (hαH s hs) (hgt _ (hαH s hs))
        have hcont : ContinuousOn φ (Iic T) := by
          have h := (ptSet_eq_and_continuousOn hP hl (d := 0) (by simp)).2
          rw [hζT] at h
          refine h.mono fun s hs => ?_
          exact ENNReal.coe_le_coe.2 hs
        have hf : ∀ z, {s | s ≤ T ∧ φ s = z}.Finite := by
          intro z
          refine Finite.of_finite_image ((hfib z).subset ?_) ((hinj n hl).mono fun s hs => ?_)
          · rintro _ ⟨s, ⟨hs, hsz⟩, rfl⟩
            exact ⟨show g (trOf (D n) s) = z by rw [← hφg s hs]; exact hsz, hαH s hs⟩
          · show (s : ℝ≥0∞) ≤ (D n).2
            rw [hζT]; exact ENNReal.coe_le_coe.2 hs.1
        have hH : ∀ s ≤ T, 0 ≤ (φ s).im := fun s hs => by
          rw [hφg s hs]
          exact GW1P.mem_Hbar_of_tendsto (hαH s hs) hcc.2.1 (hgt _ (hαH s hs))
        obtain ⟨hq, hqi⟩ := isFFPath_reparam (pos_iff_ne_zero.2 hT0) hcont hf hH
        have hq0 : (fun t : ℝ => φ (t * T).toNNReal) 0 ∈ A ∪ U := by
          simp only [zero_mul, Real.toNNReal_zero]
          rw [hφ0]
          exact Or.inl ihpt
        have := ih.join hq hq0
        rwa [hqi, ← hNP] at this
    · have hnone : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n = none := by
        simpa using hl
      have hnp : newPiece κ b jumps θ right D n = ∅ := by
        ext z
        simp only [newPiece, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd hnone h
      rw [hnp, union_empty]
      rcases run_succ_noLaunch_cases (κ := κ) (b := b) (jumps := jumps) _ D hnone with
        ⟨ha, hp⟩ | ⟨x, mk, he, hlt⟩ | ⟨x, mk, he, hlt⟩ | ⟨r, he⟩
      · rw [GW2aCont.arcAt_of_arcs_eq ha, image_empty, union_empty]
        refine ⟨ih, ?_⟩
        rw [hp]
        exact Or.inl (Or.inl ihpt)
      · have harc : GW2aCont.arcAt κ b jumps (boundaryWalkSpec b jumps θ right) D n =
            Icc (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) x := by
          rw [GW2aCont.arcAt_eq_newArc, he, GW2aCont.newArc_moveAlong]; rfl
        have hseg := image_segPath (ne_of_lt hlt)
        rw [min_eq_left hlt.le, max_eq_right hlt.le] at hseg
        refine ⟨?_, ?_⟩
        · rw [harc, ← hseg]
          exact ih.join (isFFPath_segPath (ne_of_lt hlt)) (by rw [segPath_zero]; exact Or.inl ihpt)
        · rw [harc, he, stPt_moveAlong]
          exact Or.inr ⟨x, ⟨hlt.le, le_rfl⟩, rfl⟩
      · have harc : GW2aCont.arcAt κ b jumps (boundaryWalkSpec b jumps θ right) D n =
            Icc x (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) := by
          rw [GW2aCont.arcAt_eq_newArc, he, GW2aCont.newArc_moveAlong]; rfl
        have hseg := image_segPath (ne_of_gt hlt)
        rw [min_eq_right hlt.le, max_eq_left hlt.le] at hseg
        refine ⟨?_, ?_⟩
        · rw [harc, ← hseg]
          exact ih.join (isFFPath_segPath (ne_of_gt hlt)) (by rw [segPath_zero]; exact Or.inl ihpt)
        · rw [harc, he, stPt_moveAlong]
          exact Or.inr ⟨x, ⟨le_rfl, hlt.le⟩, rfl⟩
      · exact absurd (by rw [he]; exact stStatus_moveToEnd _ r) hnd

end Walk

end InteractingSLE.Theorem14.SB.LuM
