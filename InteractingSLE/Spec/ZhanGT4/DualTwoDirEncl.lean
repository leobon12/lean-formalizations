/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualTwoDir

/-!
# The two-view data from protected enclosures

Packet PROVE-ZHAN-GT4-A15. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L300–L407, R38).

The hypotheses `TwoViewRect` and `TwoViewMarks` of `DualD6`/`DualTwoDir` are discharged here from the enclosure data
of A14's `martingale_colProd_frozen` (separated enclosures `H₁ j`, `H₂ j` containing the hulls up to the exit times,
a protected point and protected marks), for the **canonical selection** of image data at every height `y`: the data of
A6's `OwnData` up to the staircase width `stairH S₂ S₁ y` (the deterministic form of A14's `frzImgSel`). The positive
heights use A9's `exists_twoCurveD9` (tip and marks alive for every image chain); height `0` (empty frozen hull,
chart the identity) is handled directly.

## Main results

* `imgSelD`, `imgSelD_spec`: the deterministic selection.
* `exists_eq_stairH`: the staircase width at a height under some rectangle is attained.
* `ownView_of_encl`: one view (either orientation), every height `v ≤ S_frozen i`.
-/

set_option autoImplicit false

noncomputable section

open Finset Set Complex Metric Filter Topology

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

/-! ### The deterministic selection of image data -/

open scoped Classical in
/-- **The image data at height `y`** (deterministic form of A14's `frzImgSel`): a choice of `(a, W')` with
`OwnData W K_V(y) g_{V,y} w a W'` (the growing driver `W` up to the width `w`, the frozen hull of `V` at height `y`),
`(0, 0)` if there is none. -/
def imgSelD (W V : ℝ → ℝ) (w y : ℝ) : (ℝ → ℝ) × (ℝ → ℝ) :=
  if h : ∃ a W', OwnData W (fwdHull V y) (frzChart V y) w a W' then (h.choose, h.choose_spec.choose) else (0, 0)

theorem imgSelD_spec {W V : ℝ → ℝ} {w y : ℝ} (h : ∃ a W', OwnData W (fwdHull V y) (frzChart V y) w a W') :
    OwnData W (fwdHull V y) (frzChart V y) w (imgSelD W V w y).1 (imgSelD W V w y).2 := by
  classical
  unfold imgSelD
  split_ifs
  exact h.choose_spec.choose_spec

/-! ### The staircase width -/

section Width

variable {ι : Type*} [Fintype ι]

/-- **The staircase width at a height under some rectangle is attained** by a rectangle above that height. -/
theorem exists_eq_stairH {S₁ S₂ : ι → ℝ} (hS₂ : ∀ i, 0 ≤ S₂ i) {c : ℝ} {i : ι} (hi : c ≤ S₁ i) :
    ∃ j, c ≤ S₁ j ∧ stairH S₁ S₂ c = S₂ j := by
  have h : stairH S₁ S₂ c ∈ insert 0 ((univ.filter fun i => c ≤ S₁ i).image S₂) := max'_mem _ _
  rcases mem_insert.1 h with h0 | h1
  · have h2 := le_stairH (S₂ := S₂) hi
    rw [h0] at h2
    exact ⟨i, hi, by rw [h0]; linarith [hS₂ i]⟩
  · obtain ⟨j, hj, he⟩ := mem_image.1 h1
    exact ⟨j, (mem_filter.1 hj).2, he.symm⟩

end Width

/-! ### Points near a protected set -/

/-- A point of `closure F` is at distance `≥ 2δ` from `G` when `F` and `G` are `2δ`-separated. -/
theorem le_norm_of_mem_closure {F G : Set ℂ} {δ : ℝ} (hsep : ∀ a ∈ F, ∀ z ∈ G, 2 * δ ≤ ‖a - z‖) {x : ℂ}
    (hx : x ∈ closure F) {z : ℂ} (hz : z ∈ G) : 2 * δ ≤ ‖x - z‖ := by
  have hcl : IsClosed {a : ℂ | 2 * δ ≤ ‖a - z‖} :=
    isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  exact closure_minimal (fun a ha => hsep a ha z hz) hcl hx

/-- A ball disjoint from `F` excludes `closure F`'s points from its centre. -/
theorem ne_of_mem_closure_of_disjoint_ball {F : Set ℂ} {x : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : Disjoint (ball x r) F) {y : ℂ} (hy : y ∈ closure F) : y ≠ x := by
  rintro rfl
  obtain ⟨z, hzF, hz⟩ := Metric.mem_closure_iff.1 hy r hr
  exact Set.disjoint_left.1 hF (by rwa [mem_ball, dist_comm]) hzF

/-! ### One view at every height -/

/-- At height `0` the frozen hull is empty and the chart is the identity on `ℍ`. -/
theorem frzChart_zero_eq {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ} (hz : z ∈ H) : frzChart V 0 z = z := by
  have hK : z ∉ fwdHull V 0 := by rw [QuantumZipper.RS.fwdHull_zero_eq_empty hV]; exact Set.notMem_empty z
  simp only [frzChart, fwdMap_zero_gen hV hz hK, sub_add_cancel]

/-- At height `0` a real point other than the start is its own mark. -/
theorem frzMarks_zero_eq {V : ℝ → ℝ} (hV : Continuous V) {n : ℕ} {p : Fin n → ℝ} {m : Fin n} {r : ℝ} (hr : 0 < r)
    (hpV : p m ≠ V 0) : frzMarks V p 0 m = p m := by
  have hdisj : Disjoint (ball ((p m : ℝ) : ℂ) r) (fwdHull V 0) := by
    rw [QuantumZipper.RS.fwdHull_zero_eq_empty hV]; exact Set.disjoint_empty _
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_disjoint_ball_gen hV hpV le_rfl hr hdisj
  have h1 := InteractingSLE.fwdMap_eq_of_isForwardSol hV hu ⟨le_rfl, le_rfl⟩
  have h2 := QuantumZipper.F1.isForwardSol_zero hu le_rfl
  simp only [frzMarks, h1, h2, sub_re, ofReal_re]
  ring

section View

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- **One view at every height, from protected enclosures.** Curve `W` (from `0`) grows inside `G j` up to `SG j`,
the frozen curve `V` stays in `F j` up to `SF j` and starts in `closure (F j)`; the enclosures are `2δ`-separated and
the marks are protected. Then at every height `v ≤ SF i` the canonical image data up to the staircase width
`w = stairH SF SG v ≥ SG i` exist (`OwnData`), the frozen tip `V v` is alive for the image chain up to `a(w)`, and
every image mark is alive at every time `≤ SG i`. The positive heights use `hD9` (A9's `exists_twoCurveD9` or its left
form); height `0` is direct. -/
theorem ownView_of_encl {W V : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (hV : Continuous V)
    {G F : ι → Set ℂ} {δ d : ι → ℝ} (hδ : ∀ j, 0 < δ j) (hsep : ∀ j, ∀ a ∈ F j, ∀ z ∈ G j, 2 * δ j ≤ ‖a - z‖)
    (hd : ∀ j, 0 < d j) {p : Fin n → ℝ} (hpH : ∀ j m, Disjoint (ball (p m : ℂ) (2 * d j)) (G j ∪ F j))
    (hV0F : ∀ j, ((V 0 : ℝ) : ℂ) ∈ closure (F j)) (hV0 : V 0 ≠ 0)
    {SG SF : ι → ℝ} (hSG : ∀ j, 0 < SG j) {Tm : ℝ} (hSGm : ∀ j, SG j ≤ Tm) (hSFm : ∀ j, SF j ≤ Tm)
    (hKG : ∀ j, fwdHull W (SG j) ⊆ G j) (hKF : ∀ j, fwdHull V (SF j) ⊆ F j)
    (hD9 : ∀ j, ∀ (t₂ T : ℝ) (a W' : ℝ → ℝ), OwnData W (fwdHull V t₂) (frzChart V t₂) T a W' → 0 < t₂ →
      t₂ ≤ Tm → T ≤ Tm → fwdHull W T ⊆ G j → fwdHull V t₂ ⊆ F j →
      (∃ x, IsForwardSol W' ((V t₂ : ℝ) : ℂ) (a T) x) ∧
        ∀ m, ∃ x, IsForwardSol W' ((frzMarks V p t₂ m : ℝ) : ℂ) (a T) x)
    (i : ι) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (SF i)) :
    SG i ≤ stairH SF SG v ∧
      OwnData W (fwdHull V v) (frzChart V v) (stairH SF SG v) (imgSelD W V (stairH SF SG v) v).1
        (imgSelD W V (stairH SF SG v) v).2 ∧
      (∃ x, IsForwardSol (imgSelD W V (stairH SF SG v) v).2 ((V v : ℝ) : ℂ)
        ((imgSelD W V (stairH SF SG v) v).1 (stairH SF SG v)) x) ∧
      ∀ u ∈ Icc (0 : ℝ) (SG i), ∀ m, ∃ x, IsForwardSol (imgSelD W V (stairH SF SG v) v).2
        ((frzMarks V p v m : ℝ) : ℂ) ((imgSelD W V (stairH SF SG v) v).1 u) x := by
  obtain ⟨j, hvj, hwj⟩ := exists_eq_stairH (S₁ := SF) (S₂ := SG) (fun j => (hSG j).le) hv.2
  set w := stairH SF SG v with hw
  have hiw : SG i ≤ w := le_stairH hv.2
  have hwpos : 0 < w := by rw [hwj]; exact hSG j
  have hKw : fwdHull W w ⊆ G j := by rw [hwj]; exact hKG j
  have hKv : fwdHull V v ⊆ F j := ((QuantumZipper.fwdHull_mono).1 hvj).trans (hKF j)
  have hdisj : Disjoint (closure (fwdHull V v)) (closure (fwdHull W w)) :=
    disjoint_closure_of_le_norm (by linarith [hδ j] : 0 < 2 * δ j) fun a ha z hz => hsep j a (hKv ha) z (hKw hz)
  have hown := imgSelD_spec (exists_ownData hW hW0 hwpos (isHPHull_fwdHull hV hv.1) (isMapOut_fwdMap_gen hV hv.1)
    hdisj)
  refine ⟨hiw, hown, ?_⟩
  set a := (imgSelD W V w v).1 with ha
  set W' := (imgSelD W V w v).2 with hW'
  have hclock : ∀ u ∈ Icc (0 : ℝ) (SG i), a u ∈ Icc (0 : ℝ) (a w) := fun u hu =>
    hown.toImgData.mapsTo_clock_Icc ⟨hu.1, hu.2.trans hiw⟩
  rcases hv.1.eq_or_lt with h0 | hpos
  · -- height `0`: empty frozen hull, identity chart
    subst h0
    have hwmem : w ∈ Icc (0 : ℝ) w := ⟨hwpos.le, le_rfl⟩
    have himg : fwdHull W' (a w) = fwdHull W w := by
      rw [hown.img w hwmem]
      refine (Set.image_congr fun z hz => ?_).trans (Set.image_id _)
      exact frzChart_zero_eq hV ((QuantumZipper.fwdHull_mono).2 w hz)
    have hlim : Tendsto (frzChart V 0) (𝓝[H] ((W 0 : ℝ) : ℂ)) (𝓝 0) := by
      rw [hW0, ofReal_zero]
      refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz using (frzChart_zero_eq hV hz).symm
    have hW'0 : (W' 0 : ℂ) = 0 := hown.toImgData.W'_zero_eq hlim
    have hW'0r : W' 0 = 0 := by exact_mod_cast hW'0
    have hmono : ∀ u ∈ Icc (0 : ℝ) (SG i), fwdHull W' (a u) ⊆ G j := fun u hu =>
      ((QuantumZipper.fwdHull_mono).1 (hclock u hu).2).trans (himg ▸ hKw)
    -- `0` is not a mark and not the frozen start
    have h0G : ((0 : ℝ) : ℂ) ∈ closure (G j) := by
      have := start_mem_closure_fwdHull hW (hSG j)
      rw [hW0] at this
      exact closure_mono (hKG j) this
    have hballG : Disjoint (ball ((V 0 : ℝ) : ℂ) (δ j)) (G j) := Set.disjoint_left.2 fun z hz hzG => by
      have h1 := le_norm_of_mem_closure (hsep j) (hV0F j) hzG
      rw [mem_ball, dist_eq_norm] at hz
      rw [norm_sub_rev] at h1
      linarith [hδ j]
    have hd2 : 0 < 2 * d j := by linarith [hd j]
    refine ⟨?_, fun u hu m => ?_⟩
    · have hne : V 0 ≠ W' 0 := by rw [hW'0r]; exact hV0
      exact exists_isForwardSol_of_disjoint_ball_gen hown.contW' hne
        (hown.toImgData.mapsTo_clock_Icc hwmem).1 (hδ j) (hballG.mono_right (himg ▸ hKw))
    · have hpV : p m ≠ V 0 := fun h => ne_of_mem_closure_of_disjoint_ball hd2
        ((hpH j m).mono_right Set.subset_union_right) (hV0F j) (by rw [h])
      have hp0 : p m ≠ W' 0 := fun h => ne_of_mem_closure_of_disjoint_ball hd2
        ((hpH j m).mono_right Set.subset_union_left) h0G (by rw [h, hW'0r])
      rw [frzMarks_zero_eq hV hd2 hpV]
      exact exists_isForwardSol_of_disjoint_ball_gen hown.contW' hp0 (hclock u hu).1 hd2
        (((hpH j m).mono_right Set.subset_union_left).mono_right (hmono u hu))
  · -- positive height: A9
    obtain ⟨htip, hmk⟩ := hD9 j v w a W' hown hpos (hv.2.trans (hSFm i)) (by rw [hwj]; exact hSGm j) hKw hKv
    refine ⟨htip, fun u hu m => ?_⟩
    obtain ⟨x, hx⟩ := hmk m
    exact ⟨x, Ito.isForwardSol_of_le hx (hclock u hu).1 (hclock u hu).2⟩

end View

/-! ### Translated enclosures -/

/-- Translation of a set by the real `x`. -/
def transl (x : ℝ) (S : Set ℂ) : Set ℂ := (fun z => z + (x : ℂ)) '' S

theorem mem_transl_iff {x : ℝ} {S : Set ℂ} {w : ℂ} : w ∈ transl x S ↔ w - x ∈ S := by
  constructor
  · rintro ⟨z, hz, rfl⟩; simpa using hz
  · intro h; exact ⟨w - x, h, by ring⟩

theorem isHPHull_transl {S : Set ℂ} (hS : IsHPHull S) (x : ℝ) : IsHPHull (transl x S) := by
  have h := hS.image_affHomeo (r := 1) (x := x) one_pos
  have e : affHomeo 1 one_pos x '' S = transl x S := by
    congr 1; funext z; exact ConformalImageFull.affHomeo_one_apply x z
  rwa [e] at h

theorem sep_transl {F G : Set ℂ} {δ : ℝ} (h : ∀ a ∈ F, ∀ z ∈ G, 2 * δ ≤ ‖a - z‖) (x : ℝ) :
    ∀ a ∈ transl x F, ∀ z ∈ transl x G, 2 * δ ≤ ‖a - z‖ := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨z, hz, rfl⟩
  have := h a ha z hz
  simpa using this

theorem disjoint_ball_transl {c : ℝ} {r : ℝ} {S : Set ℂ} (h : Disjoint (ball (c : ℂ) r) S) (x : ℝ) :
    Disjoint (ball ((c + x : ℝ) : ℂ) r) (transl x S) := by
  rw [Set.disjoint_left]
  intro w hw hwS
  rw [mem_transl_iff] at hwS
  refine Set.disjoint_left.1 h ?_ hwS
  rw [mem_ball, dist_eq_norm] at hw ⊢
  convert hw using 2; push_cast; ring

theorem mem_closure_transl {S : Set ℂ} {w : ℂ} (h : w ∈ closure S) (x : ℝ) : w + x ∈ closure (transl x S) :=
  image_closure_subset_closure_image (continuous_id.add continuous_const) ⟨w, h, rfl⟩

theorem fwdHull_sub_const_subset {W : ℝ → ℝ} {c t : ℝ} {S : Set ℂ} (h : fwdHull W t ⊆ S) :
    fwdHull (fun u => W u - c) t ⊆ transl (-c) S := by
  rw [fwdHull_sub_const]
  exact Set.image_mono h

/-! ### The enclosure data of a two-curve configuration -/

/-- **Protected enclosures for finitely many rectangles** (the hypotheses of A14's `martingale_colProd_frozen`, for a
fixed path of each curve): curve `1` (`W₁ 0 = 0`) stays in `H₁ j` up to `S₁ j`, curve `2` stays in `H₂ j` up to
`S₂ j` and starts in `closure (H₂ j)` to the right of a protected point `q j > 0`; the enclosures are `2δ`-separated,
and the point `q j` and the marks are protected. -/
structure TwoEncl {ι : Type*} {n : ℕ} (W₁ W₂ : ℝ → ℝ) (S₁ S₂ : ι → ℝ) (H₁ H₂ : ι → Set ℂ) (δ q d : ι → ℝ)
    (p : Fin n → ℝ) (Tm : ℝ) : Prop where
  cont₁ : Continuous W₁
  cont₂ : Continuous W₂
  zero₁ : W₁ 0 = 0
  hull₁ : ∀ j, IsHPHull (H₁ j)
  hull₂ : ∀ j, IsHPHull (H₂ j)
  δpos : ∀ j, 0 < δ j
  sep : ∀ j, ∀ a ∈ H₂ j, ∀ z ∈ H₁ j, 2 * δ j ≤ ‖a - z‖
  dpos : ∀ j, 0 < d j
  qpos : ∀ j, 0 < q j
  qH : ∀ j, Disjoint (ball (q j : ℂ) (2 * d j)) (H₁ j ∪ H₂ j)
  pH : ∀ j m, Disjoint (ball (p m : ℂ) (2 * d j)) (H₁ j ∪ H₂ j)
  pinj : Function.Injective p
  start₂ : ∀ j, ((W₂ 0 : ℝ) : ℂ) ∈ closure (H₂ j)
  qW : ∀ j, q j < W₂ 0
  S₁pos : ∀ j, 0 < S₁ j
  S₂pos : ∀ j, 0 < S₂ j
  S₁le : ∀ j, S₁ j ≤ Tm
  S₂le : ∀ j, S₂ j ≤ Tm
  K₁ : ∀ j, fwdHull W₁ (S₁ j) ⊆ H₁ j
  K₂ : ∀ j, fwdHull W₂ (S₂ j) ⊆ H₂ j

/-- The canonical `s`-view clock at height `v`. -/
def sSelA {ι : Type*} [Fintype ι] (W₁ W₂ : ℝ → ℝ) (S₁ S₂ : ι → ℝ) (v : ℝ) : ℝ → ℝ :=
  (imgSelD W₁ W₂ (stairH S₂ S₁ v) v).1

/-- The canonical `s`-view image driver at height `v`. -/
def sSelW {ι : Type*} [Fintype ι] (W₁ W₂ : ℝ → ℝ) (S₁ S₂ : ι → ℝ) (v : ℝ) : ℝ → ℝ :=
  (imgSelD W₁ W₂ (stairH S₂ S₁ v) v).2

/-- The canonical `t`-view clock at height `u` (translated coordinates). -/
def tSelA {ι : Type*} [Fintype ι] (W₁ W₂ : ℝ → ℝ) (S₁ S₂ : ι → ℝ) (u : ℝ) : ℝ → ℝ :=
  (imgSelD (fun s => W₂ s - W₂ 0) (fun s => W₁ s - W₂ 0) (stairH S₁ S₂ u) u).1

/-- The canonical `t`-view image driver at height `u` (translated coordinates). -/
def tSelW {ι : Type*} [Fintype ι] (W₁ W₂ : ℝ → ℝ) (S₁ S₂ : ι → ℝ) (u : ℝ) : ℝ → ℝ :=
  (imgSelD (fun s => W₂ s - W₂ 0) (fun s => W₁ s - W₂ 0) (stairH S₁ S₂ u) u).2

namespace TwoEncl

variable {ι : Type*} [Fintype ι] {n : ℕ} {W₁ W₂ : ℝ → ℝ} {S₁ S₂ : ι → ℝ} {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ}
  {p : Fin n → ℝ} {Tm : ℝ} (h : TwoEncl W₁ W₂ S₁ S₂ H₁ H₂ δ q d p Tm)
include h

omit [Fintype ι] in
theorem zero_mem_closure (j : ι) : ((0 : ℝ) : ℂ) ∈ closure (H₁ j) := by
  have := start_mem_closure_fwdHull h.cont₁ (h.S₁pos j)
  rw [h.zero₁] at this
  exact closure_mono (h.K₁ j) this

omit [Fintype ι] in
theorem W₂_zero_pos (j : ι) : 0 < W₂ 0 := (h.qpos j).trans (h.qW j)

/-- **The `s`-view at every height of rectangle `i`** (`ownView_of_encl` with A9's `exists_twoCurveD9`). -/
theorem sView_encl (i : ι) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (S₂ i)) :
    S₁ i ≤ stairH S₂ S₁ v ∧
      OwnData W₁ (fwdHull W₂ v) (frzChart W₂ v) (stairH S₂ S₁ v) (sSelA W₁ W₂ S₁ S₂ v) (sSelW W₁ W₂ S₁ S₂ v) ∧
      (∃ x, IsForwardSol (sSelW W₁ W₂ S₁ S₂ v) ((W₂ v : ℝ) : ℂ) (sSelA W₁ W₂ S₁ S₂ v (stairH S₂ S₁ v)) x) ∧
      ∀ u ∈ Icc (0 : ℝ) (S₁ i), ∀ m, ∃ x, IsForwardSol (sSelW W₁ W₂ S₁ S₂ v)
        ((frzMarks W₂ p v m : ℝ) : ℂ) (sSelA W₁ W₂ S₁ S₂ v u) x := by
  have hc := fun j => exists_twoCurveD9 (h.hull₁ j) (h.hull₂ j) (h.δpos j) (h.sep j) (h.dpos j) (h.qpos j) (h.qH j)
    (h.pH j) h.pinj Tm
  choose r a₀ γ Γ lam hr ha hγ hmain using hc
  exact ownView_of_encl h.cont₁ h.zero₁ h.cont₂ h.δpos h.sep h.dpos h.pH h.start₂ (h.W₂_zero_pos i).ne' h.S₁pos
    h.S₁le h.S₂le h.K₁ h.K₂ (fun j t₂ T a W' hown ht₂ ht₂m hTm hKT hKt₂ =>
      let hT := hmain j W₁ W₂ t₂ T a W' 1 (fun _ => 0) hown h.cont₂ (h.start₂ j) (h.qW j) ht₂ ht₂m hTm hKT hKt₂
      ⟨hT.alive₀, hT.alive⟩) i hv

/-- **The `t`-view at every height of rectangle `i`**, in coordinates translated by `−c`, `c = W₂ 0`
(`ownView_of_encl` for the translated curves and enclosures, with A9's `exists_twoCurveD9_left`: the frozen curve `1`
starts at `−c` to the left of the protected point `q − c < 0`). -/
theorem tView_encl (i : ι) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (S₁ i)) :
    S₂ i ≤ stairH S₁ S₂ u ∧
      OwnData (fun s => W₂ s - W₂ 0) (fwdHull (fun s => W₁ s - W₂ 0) u) (frzChart (fun s => W₁ s - W₂ 0) u)
        (stairH S₁ S₂ u) (tSelA W₁ W₂ S₁ S₂ u) (tSelW W₁ W₂ S₁ S₂ u) ∧
      (∃ x, IsForwardSol (tSelW W₁ W₂ S₁ S₂ u) ((W₁ u - W₂ 0 : ℝ) : ℂ) (tSelA W₁ W₂ S₁ S₂ u (stairH S₁ S₂ u)) x) ∧
      ∀ v ∈ Icc (0 : ℝ) (S₂ i), ∀ m, ∃ x, IsForwardSol (tSelW W₁ W₂ S₁ S₂ u)
        ((frzMarks (fun s => W₁ s - W₂ 0) (fun m => p m - W₂ 0) u m : ℝ) : ℂ) (tSelA W₁ W₂ S₁ S₂ u v) x := by
  set c := W₂ 0 with hc
  have hc0 : 0 < c := h.W₂_zero_pos i
  -- the translated enclosures: curve `2` grows in `G`, curve `1` is frozen in `F`
  set G : ι → Set ℂ := fun j => transl (-c) (H₂ j) with hG
  set F : ι → Set ℂ := fun j => transl (-c) (H₁ j) with hF
  have hsep' : ∀ j, ∀ a ∈ F j, ∀ z ∈ G j, 2 * δ j ≤ ‖a - z‖ := fun j =>
    sep_transl (fun a ha z hz => by rw [norm_sub_rev]; exact h.sep j z hz a ha) (-c)
  have hunion : ∀ j, transl (-c) (H₁ j ∪ H₂ j) = G j ∪ F j := fun j => by
    simp only [hG, hF, transl, Set.image_union, Set.union_comm]
  have hpH' : ∀ j m, Disjoint (ball (((fun m => p m - c) m : ℝ) : ℂ) (2 * d j)) (G j ∪ F j) := fun j m => by
    have := disjoint_ball_transl (h.pH j m) (-c)
    rw [hunion j] at this
    simpa [sub_eq_add_neg] using this
  have hqH' : ∀ j, Disjoint (ball ((q j - c : ℝ) : ℂ) (2 * d j)) (G j ∪ F j) := fun j => by
    have := disjoint_ball_transl (h.qH j) (-c)
    rw [hunion j] at this
    simpa [sub_eq_add_neg] using this
  have hpinj' : Function.Injective (fun m => p m - c) := fun m k hmk => h.pinj (by simpa using hmk)
  have hV0F : ∀ j, (((fun s => W₁ s - c) 0 : ℝ) : ℂ) ∈ closure (F j) := fun j => by
    have := mem_closure_transl (h.zero_mem_closure j) (-c)
    simpa [h.zero₁] using this
  have hc' := fun j => exists_twoCurveD9_left (isHPHull_transl (h.hull₂ j) (-c)) (isHPHull_transl (h.hull₁ j) (-c))
    (h.δpos j) (hsep' j) (h.dpos j) (by linarith [h.qW j] : q j - c < 0) (hqH' j) (hpH' j) hpinj' Tm
  choose r a₀ γ Γ lam hr ha hγ hmain using hc'
  have hU₂ : Continuous fun s => W₂ s - c := h.cont₂.sub continuous_const
  have hU₁ : Continuous fun s => W₁ s - c := h.cont₁.sub continuous_const
  exact ownView_of_encl (W := fun s => W₂ s - c) (V := fun s => W₁ s - c) (G := G) (F := F) hU₂ (by simp [hc])
    hU₁ h.δpos hsep' h.dpos hpH' hV0F (by simp [h.zero₁]; exact hc0.ne') h.S₂pos h.S₂le h.S₁le
    (fun j => fwdHull_sub_const_subset (h.K₂ j)) (fun j => fwdHull_sub_const_subset (h.K₁ j))
    (fun j t₂ T a W' hown ht₂ ht₂m hTm hKT hKt₂ =>
      let hT := hmain j (fun s => W₂ s - c) (fun s => W₁ s - c) t₂ T a W' 1 (fun _ => 0) hown hU₁ (hV0F j)
        (by simp [h.zero₁]; linarith [h.qpos j]) ht₂ ht₂m hTm hKT hKt₂
      ⟨hT.alive₀, hT.alive⟩) i hu

/-- **The two-view hypotheses on every rectangle, from the enclosures**, for the canonical selections. -/
theorem twoViewRect (i : ι) :
    TwoViewRect W₁ W₂ (S₁ i) (S₂ i) (sSelA W₁ W₂ S₁ S₂) (sSelW W₁ W₂ S₁ S₂) (tSelA W₁ W₂ S₁ S₂)
      (tSelW W₁ W₂ S₁ S₂) where
  nonneg_X := (h.S₁pos i).le
  nonneg_Y := (h.S₂pos i).le
  sOwn v hv := by
    obtain ⟨hw, hown, htip, -⟩ := h.sView_encl i hv
    exact ⟨_, hw, hown, htip⟩
  tOwn u hu := by
    obtain ⟨hw, hown, htip, -⟩ := h.tView_encl i hu
    exact ⟨_, hw, hown, htip⟩

/-- **The mark hypotheses on every rectangle, from the enclosures.** -/
theorem twoViewMarks (i : ι) :
    TwoViewMarks W₁ W₂ (S₁ i) (S₂ i) (sSelA W₁ W₂ S₁ S₂) (sSelW W₁ W₂ S₁ S₂) (tSelA W₁ W₂ S₁ S₂)
      (tSelW W₁ W₂ S₁ S₂) p where
  alive₁ m := by
    have hd2 : 0 < 2 * d i := by linarith [h.dpos i]
    refine exists_isForwardSol_of_disjoint_ball_gen h.cont₁ ?_ (h.S₁pos i).le hd2
      (((h.pH i m).mono_right Set.subset_union_left).mono_right (h.K₁ i))
    intro hp
    exact ne_of_mem_closure_of_disjoint_ball hd2 ((h.pH i m).mono_right Set.subset_union_left)
      (h.zero_mem_closure i) (by rw [hp, h.zero₁])
  alive₂ m := by
    have hd2 : 0 < 2 * d i := by linarith [h.dpos i]
    refine exists_isForwardSol_of_disjoint_ball_gen h.cont₂ ?_ (h.S₂pos i).le hd2
      (((h.pH i m).mono_right Set.subset_union_right).mono_right (h.K₂ i))
    intro hp
    exact ne_of_mem_closure_of_disjoint_ball hd2 ((h.pH i m).mono_right Set.subset_union_right)
      (h.start₂ i) (by rw [hp])
  aliveS v hv u hu m := (h.sView_encl i hv).2.2.2 u hu m
  aliveT u hu v hv m := (h.tView_encl i hu).2.2.2 v hv m

end TwoEncl

end InteractingSLE.ZhanGT4
