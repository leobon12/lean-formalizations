import InteractingSLE.Foundations.Loewner.ConformalImageSmallHull
import QuantumZipper.Proofs.Thm18.LWFarCondFlow

/-!
# Continuously growing families of hulls are Loewner chains after a capacity time change

Packet GEO-LOC (`planning/INFRA-GEO.md` §4), fourth layer: [Law05] §4.1, pp. 79–80 ("continuously
increasing hulls correspond to generalized Loewner chains"), Proposition 4.3 and Lemma 4.2.

`IsContinuouslyGrowing B U T`: `(B t)_{t ∈ [0,T]}` is an increasing, strictly increasing family of
compact `ℍ`-hulls with `B 0 = ∅`, and the increments `g_{B s}(B t \ B s)` lie, uniformly in `s`, in
small closed balls around `U s`, with `U` continuous on `[0, T]`.

Main result `IsContinuouslyGrowing.exists_loewner`: with the capacity clock
`a(t) = hcap(B t)/2` (continuous, strictly increasing, `a 0 = 0`), there is a continuous
`W̃ : ℝ → ℝ` with `W̃(a t) = U t` such that for every `t ∈ [0, T]` the QuantumZipper Loewner hull
of `W̃` at time `a t` is `B t`, and `g_{B t} = f̃_{a t} + W̃(a t)` off `B t`.

Proof: the increments are small hulls near `U s`, so [Law05] Proposition 3.46
(`IsMapOut.norm_sub_sub_hcap_div_le`) gives `g_{B t}(w) − g_{B s}(w) = (hcap(B t) − hcap(B s)) /
(g_{B s}(w) − U s) + o(hcap(B t) − hcap(B s))`; in the clock `σ = a(t)` this is the right
derivative `2/(Y σ − W̃ σ)` of `Y σ = g_{B τ(σ)}(w)`. Equality of right derivatives
(`eq_of_has_deriv_right_eq`, [Law05] Lemma 4.2) gives the integral form of the Loewner equation,
i.e. a QuantumZipper forward solution; uniqueness identifies `fwdMap`, and the swallowing times
identify the hulls.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace ConformalImage

/-- A canonical mapping-out function of a hull (any choice: they agree off the hull). -/
def mapOut (B : Set ℂ) : ℂ → ℂ :=
  open scoped Classical in if h : IsHPHull B then h.exists_isMapOut.choose else id

theorem isMapOut_mapOut {B : Set ℂ} (h : IsHPHull B) : IsMapOut B (mapOut B) := by
  unfold mapOut
  split_ifs
  exact h.exists_isMapOut.choose_spec

/-- The half-plane capacity of a set that is a hull (`0` otherwise; only used on hulls). -/
def hcapSet (B : Set ℂ) : ℝ :=
  open scoped Classical in if h : IsHPHull B then HPHull.hcap ⟨B, h⟩ else 0

theorem hcapSet_eq {B : Set ℂ} (h : IsHPHull B) : hcapSet B = HPHull.hcap ⟨B, h⟩ := by
  unfold hcapSet
  split_ifs
  rfl

/-- `(B t)_{t ∈ [0,T]}` is a **continuously growing family of hulls with driving function `U`**
([Law05] §4.1, p. 79: right continuous at each `t` with limit point `U t`, uniformly in `t`). -/
structure IsContinuouslyGrowing (B : ℝ → Set ℂ) (U : ℝ → ℝ) (T : ℝ) : Prop where
  isHPHull : ∀ t ∈ Icc (0 : ℝ) T, IsHPHull (B t)
  zero : B 0 = ∅
  mono : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t → B s ⊆ B t
  strict : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s < t → (B t \ B s).Nonempty
  continuousOn : ContinuousOn U (Icc 0 T)
  growth : ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t → t - s ≤ δ →
    mapOut (B s) '' (B t \ B s) ⊆ closedBall (U s : ℂ) ε

/-- The increment hull `g_{B s}(B t \ B s)`. -/
def inc (B : ℝ → Set ℂ) (s t : ℝ) : Set ℂ := mapOut (B s) '' (B t \ B s)

/-- The capacity clock `a(t) = hcap(B t)/2`. -/
def cap (B : ℝ → Set ℂ) (t : ℝ) : ℝ := hcapSet (B t) / 2

namespace IsContinuouslyGrowing

variable {B : ℝ → Set ℂ} {U : ℝ → ℝ} {T : ℝ}

theorem isHPHull_inc (h : IsContinuouslyGrowing B U T) {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) (hst : s ≤ t) : IsHPHull (inc B s t) :=
  (isMapOut_mapOut (h.isHPHull s hs)).isHPHull_image (h.isHPHull s hs) (h.isHPHull t ht)
    (h.mono s hs t ht hst)

theorem hcapSet_eq_add (h : IsContinuouslyGrowing B U T) {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    hcapSet (B t) = hcapSet (inc B s t) + hcapSet (B s) := by
  rw [hcapSet_eq (h.isHPHull t ht), hcapSet_eq (h.isHPHull s hs),
    hcapSet_eq (h.isHPHull_inc hs ht hst)]
  exact HPHull.hcap_eq_add (A := ⟨B s, h.isHPHull s hs⟩) (B := ⟨B t, h.isHPHull t ht⟩)
    (h.mono s hs t ht hst) (isMapOut_mapOut (h.isHPHull s hs))

/-- `g_{B t} = g_{inc s t} ∘ g_{B s}` off `B t`. -/
theorem eqOn_mapOut (h : IsContinuouslyGrowing B U T) {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    EqOn (mapOut (B t)) (mapOut (inc B s t) ∘ mapOut (B s)) (H \ B t) :=
  (isMapOut_mapOut (h.isHPHull t ht)).eqOn (h.isHPHull t ht)
    ((isMapOut_mapOut (h.isHPHull s hs)).comp (h.isHPHull s hs) (h.isHPHull t ht)
      (h.mono s hs t ht hst) (isMapOut_mapOut (h.isHPHull_inc hs ht hst)))

theorem hcapSet_inc_le (h : IsContinuouslyGrowing B U T) {s t ε : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) (hst : s ≤ t) (hsub : inc B s t ⊆ closedBall (U s : ℂ) ε) :
    hcapSet (inc B s t) ≤ ε ^ 2 := by
  rw [hcapSet_eq (h.isHPHull_inc hs ht hst)]
  exact HPHull.hcap_le_rad_sq _ hsub

theorem hcapSet_inc_pos (h : IsContinuouslyGrowing B U T) {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) (hst : s < t) : 0 < hcapSet (inc B s t) := by
  rw [hcapSet_eq (h.isHPHull_inc hs ht hst.le)]
  refine lt_of_le_of_ne (HPHull.hcap_nonneg _) (Ne.symm fun h0 => ?_)
  have := (HPHull.hcap_eq_zero_iff _).1 h0
  obtain ⟨z, hz⟩ := h.strict s hs t ht hst
  have hmem : mapOut (B s) z ∈ inc B s t := ⟨z, hz, rfl⟩
  rw [show inc B s t = (⟨inc B s t, h.isHPHull_inc hs ht hst.le⟩ : HPHull).1 from rfl, this] at hmem
  exact hmem

theorem cap_zero (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) : cap B 0 = 0 := by
  have h0 := h.isHPHull 0 ⟨le_rfl, hT⟩
  rw [cap, hcapSet_eq h0, ((HPHull.hcap_eq_zero_iff ⟨B 0, h0⟩).2 h.zero)]
  simp

theorem cap_sub_eq (h : IsContinuouslyGrowing B U T) {s t : ℝ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) (hst : s ≤ t) : cap B t - cap B s = hcapSet (inc B s t) / 2 := by
  rw [cap, cap, h.hcapSet_eq_add hs ht hst]
  ring

theorem strictMonoOn_cap (h : IsContinuouslyGrowing B U T) : StrictMonoOn (cap B) (Icc 0 T) := by
  intro s hs t ht hst
  have := h.cap_sub_eq hs ht hst.le
  have := h.hcapSet_inc_pos hs ht hst
  linarith

theorem continuousOn_cap (h : IsContinuouslyGrowing B U T) : ContinuousOn (cap B) (Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨δ, hδ, hgr⟩ := h.growth (Real.sqrt ε) (Real.sqrt_pos.2 hε)
  refine ⟨δ, hδ, fun s hs hst => ?_⟩
  rw [Real.dist_eq] at hst ⊢
  have hle : ∀ {p q : ℝ}, p ∈ Icc 0 T → q ∈ Icc 0 T → p ≤ q → q - p < δ →
      cap B q - cap B p < ε := by
    intro p q hp hq hpq hd
    rw [h.cap_sub_eq hp hq hpq]
    have := h.hcapSet_inc_le hp hq hpq (hgr p hp q hq hpq hd.le)
    rw [Real.sq_sqrt hε.le] at this
    linarith
  rcases le_total s t with hst' | hst'
  · have := h.strictMonoOn_cap.monotoneOn hs ht hst'
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact hle hs ht hst' (by rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hst; linarith)
  · have := h.strictMonoOn_cap.monotoneOn ht hs hst'
    rw [abs_of_nonneg (by linarith)]
    exact hle ht hs hst' (by rw [abs_of_nonneg (by linarith)] at hst; exact hst)

/-! ### The inverse clock -/

/-- The inverse `τ` of the capacity clock on `[0, a T]`. -/
def invCap (B : ℝ → Set ℂ) (T : ℝ) (σ : ℝ) : ℝ := Function.invFunOn (cap B) (Icc 0 T) σ

theorem exists_cap_eq (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) {σ : ℝ}
    (hσ : σ ∈ Icc 0 (cap B T)) : ∃ t ∈ Icc 0 T, cap B t = σ := by
  have := intermediate_value_Icc hT h.continuousOn_cap
  rw [h.cap_zero hT] at this
  exact this hσ

theorem invCap_mem (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) {σ : ℝ}
    (hσ : σ ∈ Icc 0 (cap B T)) : invCap B T σ ∈ Icc 0 T :=
  Function.invFunOn_mem (h.exists_cap_eq hT hσ)

theorem cap_invCap (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) {σ : ℝ}
    (hσ : σ ∈ Icc 0 (cap B T)) : cap B (invCap B T σ) = σ :=
  Function.invFunOn_eq (h.exists_cap_eq hT hσ)

theorem invCap_cap (h : IsContinuouslyGrowing B U T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    invCap B T (cap B t) = t :=
  h.strictMonoOn_cap.injOn (Function.invFunOn_mem ⟨t, ht, rfl⟩) ht
    (Function.invFunOn_eq ⟨t, ht, rfl⟩)

theorem cap_mem (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    cap B t ∈ Icc 0 (cap B T) := by
  refine ⟨?_, h.strictMonoOn_cap.monotoneOn ht ⟨hT, le_rfl⟩ ht.2⟩
  rw [← h.cap_zero hT]
  exact h.strictMonoOn_cap.monotoneOn ⟨le_rfl, hT⟩ ht ht.1

theorem cap_nonneg (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    0 ≤ cap B t := (h.cap_mem hT ht).1

theorem lt_invCap_of_cap_lt (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) {σ t : ℝ}
    (hσ : σ ∈ Icc 0 (cap B T)) (ht : t ∈ Icc 0 T) (hlt : cap B t < σ) : t < invCap B T σ := by
  by_contra hle
  rw [not_lt] at hle
  have := h.strictMonoOn_cap.monotoneOn (h.invCap_mem hT hσ) ht hle
  rw [h.cap_invCap hT hσ] at this
  linarith

theorem invCap_lt_of_lt_cap (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) {σ t : ℝ}
    (hσ : σ ∈ Icc 0 (cap B T)) (ht : t ∈ Icc 0 T) (hlt : σ < cap B t) : invCap B T σ < t := by
  by_contra hle
  rw [not_lt] at hle
  have := h.strictMonoOn_cap.monotoneOn ht (h.invCap_mem hT hσ) hle
  rw [h.cap_invCap hT hσ] at this
  linarith

theorem monotoneOn_invCap (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) :
    MonotoneOn (invCap B T) (Icc 0 (cap B T)) := by
  intro σ hσ σ' hσ' hle
  by_contra hlt
  rw [not_le] at hlt
  have := h.strictMonoOn_cap (h.invCap_mem hT hσ') (h.invCap_mem hT hσ) hlt
  rw [h.cap_invCap hT hσ, h.cap_invCap hT hσ'] at this
  linarith

/-- The inverse clock is continuous on `[0, a T]`. -/
theorem continuousOn_invCap (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) :
    ContinuousOn (invCap B T) (Icc 0 (cap B T)) := by
  rw [Metric.continuousOn_iff]
  intro σ₀ hσ₀ ε hε
  set t₀ := invCap B T σ₀ with ht₀
  have ht₀m := h.invCap_mem hT hσ₀
  set t₁ := max (t₀ - ε / 2) 0 with ht₁
  set t₂ := min (t₀ + ε / 2) T with ht₂
  have ht₁m : t₁ ∈ Icc 0 T := ⟨le_max_right _ _, max_le (by linarith [ht₀m.2]) hT⟩
  have ht₂m : t₂ ∈ Icc 0 T := ⟨le_min (by linarith [ht₀m.1]) hT, min_le_right _ _⟩
  -- lower and upper margins
  obtain ⟨δ₁, hδ₁, hlow⟩ : ∃ δ₁ > 0, ∀ σ ∈ Icc 0 (cap B T), σ₀ - δ₁ < σ →
      t₀ - ε / 2 ≤ invCap B T σ := by
    by_cases hc : t₁ < t₀
    · have hlt : cap B t₁ < σ₀ := by
        have := h.strictMonoOn_cap ht₁m ht₀m hc
        rwa [h.cap_invCap hT hσ₀] at this
      refine ⟨σ₀ - cap B t₁, by linarith, fun σ hσ hσσ => ?_⟩
      have := h.lt_invCap_of_cap_lt hT hσ ht₁m (by linarith)
      linarith [le_max_left (t₀ - ε / 2) 0]
    · refine ⟨1, one_pos, fun σ hσ _ => ?_⟩
      have h1 : t₁ = t₀ := le_antisymm (max_le (by linarith) ht₀m.1) (not_lt.1 hc)
      have h2 : t₀ - ε / 2 ≤ 0 := by
        by_contra h3
        rw [not_le] at h3
        rw [ht₁, max_eq_left h3.le] at h1
        linarith
      linarith [(h.invCap_mem hT hσ).1]
  obtain ⟨δ₂, hδ₂, hup⟩ : ∃ δ₂ > 0, ∀ σ ∈ Icc 0 (cap B T), σ < σ₀ + δ₂ →
      invCap B T σ ≤ t₀ + ε / 2 := by
    by_cases hc : t₀ < t₂
    · have hlt : σ₀ < cap B t₂ := by
        have := h.strictMonoOn_cap ht₀m ht₂m hc
        rwa [h.cap_invCap hT hσ₀] at this
      refine ⟨cap B t₂ - σ₀, by linarith, fun σ hσ hσσ => ?_⟩
      have := h.invCap_lt_of_lt_cap hT hσ ht₂m (by linarith)
      linarith [min_le_left (t₀ + ε / 2) T]
    · refine ⟨1, one_pos, fun σ hσ _ => ?_⟩
      have h1 : t₂ = t₀ := le_antisymm (not_lt.1 hc) (le_min (by linarith) ht₀m.2)
      have h2 : T ≤ t₀ + ε / 2 := by
        by_contra h3
        rw [not_le] at h3
        rw [ht₂, min_eq_left h3.le] at h1
        linarith
      linarith [(h.invCap_mem hT hσ).2]
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun σ hσ hd => ?_⟩
  rw [Real.dist_eq, abs_lt] at hd ⊢
  have h1 := hlow σ hσ (by linarith [min_le_left δ₁ δ₂])
  have h2 := hup σ hσ (by linarith [min_le_right δ₁ δ₂])
  constructor <;> linarith

/-! ### The flow of a point -/

theorem mem_H_diff_of_le (h : IsContinuouslyGrowing B U T) {s t₀ : ℝ} {w : ℂ} (hs : s ∈ Icc 0 T)
    (ht₀ : t₀ ∈ Icc 0 T) (hst : s ≤ t₀) (hw : w ∈ H \ B t₀) : w ∈ H \ B s :=
  ⟨hw.1, fun hws => hw.2 (h.mono s hs t₀ ht₀ hst hws)⟩

theorem mapOut_mem_H_diff_inc (h : IsContinuouslyGrowing B U T) {s t : ℝ} {w : ℂ}
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) (hw : w ∈ H \ B t) :
    mapOut (B s) w ∈ H \ inc B s t := by
  have hws := h.mem_H_diff_of_le hs ht hst hw
  have hG := isMapOut_mapOut (h.isHPHull s hs)
  refine ⟨hG.1.2.mapsTo hws, ?_⟩
  rintro ⟨z, hz, hzw⟩
  have := hG.1.2.injOn ⟨(h.isHPHull t ht).1 hz.1, hz.2⟩ hws hzw
  exact hw.2 (this ▸ hz.1)

theorem im_mapOut_le (h : IsContinuouslyGrowing B U T) {s t : ℝ} {w : ℂ} (hs : s ∈ Icc 0 T)
    (ht : t ∈ Icc 0 T) (hst : s ≤ t) (hw : w ∈ H \ B t) :
    (mapOut (B t) w).im ≤ (mapOut (B s) w).im := by
  rw [h.eqOn_mapOut hs ht hst hw, Function.comp_apply]
  exact (isMapOut_mapOut (h.isHPHull_inc hs ht hst)).im_le (h.isHPHull_inc hs ht hst)
    (h.mapOut_mem_H_diff_inc hs ht hst hw)

theorem im_mapOut_pos (h : IsContinuouslyGrowing B U T) {t : ℝ} {w : ℂ} (ht : t ∈ Icc 0 T)
    (hw : w ∈ H \ B t) : 0 < (mapOut (B t) w).im :=
  (isMapOut_mapOut (h.isHPHull t ht)).1.2.mapsTo hw

theorem le_norm_mapOut_sub (h : IsContinuouslyGrowing B U T) {s t₀ : ℝ} {w : ℂ}
    (hs : s ∈ Icc 0 T) (ht₀ : t₀ ∈ Icc 0 T) (hst : s ≤ t₀) (hw : w ∈ H \ B t₀) :
    (mapOut (B t₀) w).im ≤ ‖mapOut (B s) w - U s‖ :=
  calc (mapOut (B t₀) w).im ≤ (mapOut (B s) w).im := h.im_mapOut_le hs ht₀ hst hw
    _ = (mapOut (B s) w - U s).im := by simp
    _ ≤ ‖mapOut (B s) w - U s‖ := (le_abs_self _).trans (abs_im_le_norm _)

/-- **One step** ([Law05] Proposition 3.46 for the increment hull). -/
theorem norm_step_le (h : IsContinuouslyGrowing B U T) {ε s t t₀ : ℝ} {w : ℂ} (hε : 0 < ε)
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (ht₀ : t₀ ∈ Icc 0 T) (hst : s ≤ t) (htt₀ : t ≤ t₀)
    (hw : w ∈ H \ B t₀) (hsub : inc B s t ⊆ closedBall (U s : ℂ) ε)
    (h4 : 4 * ε ≤ (mapOut (B t₀) w).im) :
    ‖mapOut (B t) w - mapOut (B s) w - (hcapSet (inc B s t) : ℂ) / (mapOut (B s) w - U s)‖ ≤
      12 * ε * hcapSet (inc B s t) / ‖mapOut (B s) w - U s‖ ^ 2 := by
  have hwt : w ∈ H \ B t := h.mem_H_diff_of_le ht ht₀ htt₀ hw
  rw [h.eqOn_mapOut hs ht hst hwt, Function.comp_apply, hcapSet_eq (h.isHPHull_inc hs ht hst)]
  have hG := h.mapOut_mem_H_diff_inc hs ht hst hwt
  exact (isMapOut_mapOut (h.isHPHull_inc hs ht hst)).norm_sub_sub_hcap_div_le
    (h.isHPHull_inc hs ht hst) hε hsub hG.1
    (h4.trans (h.le_norm_mapOut_sub hs ht₀ (hst.trans htt₀) hw))

/-- Each step moves a point by at most `ε` when the increment lies in `B̄(U s, ε)`. -/
theorem norm_mapOut_sub_le (h : IsContinuouslyGrowing B U T) {ε s t t₀ : ℝ} {w : ℂ}
    (hε : 0 < ε) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (ht₀ : t₀ ∈ Icc 0 T) (hst : s ≤ t)
    (htt₀ : t ≤ t₀) (hw : w ∈ H \ B t₀) (hsub : inc B s t ⊆ closedBall (U s : ℂ) ε)
    (h4 : 4 * ε ≤ (mapOut (B t₀) w).im) :
    ‖mapOut (B t) w - mapOut (B s) w‖ ≤ ε := by
  have hstep := h.norm_step_le hε hs ht ht₀ hst htt₀ hw hsub h4
  have hcap := h.hcapSet_inc_le hs ht hst hsub
  have hcap0 : 0 ≤ hcapSet (inc B s t) := by
    rw [hcapSet_eq (h.isHPHull_inc hs ht hst)]; exact HPHull.hcap_nonneg _
  set D := ‖mapOut (B s) w - U s‖ with hD
  have hD4 : 4 * ε ≤ D := h4.trans (h.le_norm_mapOut_sub hs ht₀ (hst.trans htt₀) hw)
  have hDpos : 0 < D := by linarith
  have h1 : ‖(hcapSet (inc B s t) : ℂ) / (mapOut (B s) w - U s)‖ ≤ ε / 4 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcap0, ← hD,
      div_le_iff₀ hDpos]
    nlinarith
  have h2 : 12 * ε * hcapSet (inc B s t) / D ^ 2 ≤ 3 * ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have : ε ^ 2 * 16 ≤ D ^ 2 := by nlinarith
    nlinarith
  calc ‖mapOut (B t) w - mapOut (B s) w‖
      = ‖(mapOut (B t) w - mapOut (B s) w - (hcapSet (inc B s t) : ℂ) / (mapOut (B s) w - U s))
        + (hcapSet (inc B s t) : ℂ) / (mapOut (B s) w - U s)‖ := by rw [sub_add_cancel]
    _ ≤ ‖mapOut (B t) w - mapOut (B s) w - (hcapSet (inc B s t) : ℂ) / (mapOut (B s) w - U s)‖
        + ‖(hcapSet (inc B s t) : ℂ) / (mapOut (B s) w - U s)‖ := norm_add_le _ _
    _ ≤ 3 * ε / 4 + ε / 4 := add_le_add (hstep.trans h2) h1
    _ = ε := by ring

/-- **Continuity of the flow** `s ↦ g_{B s}(w)` on `[0, t₀]` for `w ∉ B t₀`. -/
theorem continuousOn_mapOut_apply (h : IsContinuouslyGrowing B U T) {t₀ : ℝ} {w : ℂ}
    (ht₀ : t₀ ∈ Icc 0 T) (hw : w ∈ H \ B t₀) :
    ContinuousOn (fun s => mapOut (B s) w) (Icc 0 t₀) := by
  have hsub : Icc 0 t₀ ⊆ Icc 0 T := Icc_subset_Icc_right ht₀.2
  rw [Metric.continuousOn_iff]
  intro s hs ε hε
  have him := h.im_mapOut_pos ht₀ hw
  set ε' := min (ε / 2) ((mapOut (B t₀) w).im / 4) with hε'
  have hε'pos : 0 < ε' := lt_min (half_pos hε) (by positivity)
  have h4 : 4 * ε' ≤ (mapOut (B t₀) w).im := by
    have := min_le_right (ε / 2) ((mapOut (B t₀) w).im / 4); linarith
  obtain ⟨δ, hδ, hgr⟩ := h.growth ε' hε'pos
  refine ⟨δ, hδ, fun s' hs' hd => ?_⟩
  rw [Real.dist_eq] at hd
  rw [dist_eq_norm]
  have hlt : ε' < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hd1 : s' - s ≤ δ := by linarith [le_abs_self (s' - s)]
  have hd2 : s - s' ≤ δ := by linarith [neg_abs_le (s' - s)]
  rcases le_total s s' with hle | hle
  · exact lt_of_le_of_lt (h.norm_mapOut_sub_le hε'pos (hsub hs) (hsub hs') ht₀ hle hs'.2 hw
      (hgr s (hsub hs) s' (hsub hs') hle hd1) h4) hlt
  · rw [← norm_neg, neg_sub]
    exact lt_of_le_of_lt (h.norm_mapOut_sub_le hε'pos (hsub hs') (hsub hs) ht₀ hle hs.2 hw
      (hgr s' (hsub hs') s (hsub hs) hle hd2) h4) hlt

/-- **Right derivative in the capacity clock** ([Law05] Proposition 4.3): with
`Y σ = g_{B τ(σ)}(w)`, `∂⁺_σ Y = 2/(Y σ − U(τ σ))` on `[0, a t₀)`. -/
theorem hasDerivWithinAt_flow (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) {t₀ : ℝ} {w : ℂ}
    (ht₀ : t₀ ∈ Icc 0 T) (hw : w ∈ H \ B t₀) {σ : ℝ} (hσ : σ ∈ Ico 0 (cap B t₀)) :
    HasDerivWithinAt (fun σ => mapOut (B (invCap B T σ)) w)
      (2 / (mapOut (B (invCap B T σ)) w - U (invCap B T σ))) (Ici σ) σ := by
  have hcapT := (h.cap_mem hT ht₀).2
  have hσm : σ ∈ Icc 0 (cap B T) := ⟨hσ.1, hσ.2.le.trans hcapT⟩
  set s := invCap B T σ with hs
  have hsm : s ∈ Icc 0 T := h.invCap_mem hT hσm
  have hst₀ : s < t₀ := h.invCap_lt_of_lt_cap hT hσm ht₀ hσ.2
  set D := ‖mapOut (B s) w - U s‖ with hD
  have him := h.im_mapOut_pos ht₀ hw
  have hDge := h.le_norm_mapOut_sub hsm ht₀ hst₀.le hw
  have hDpos : 0 < D := lt_of_lt_of_le him hDge
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set ε := min ((mapOut (B t₀) w).im / 4) (c * D ^ 2 / 24) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  have h4 : 4 * ε ≤ (mapOut (B t₀) w).im := by
    have := min_le_left ((mapOut (B t₀) w).im / 4) (c * D ^ 2 / 24); linarith
  have hεc : ε ≤ c * D ^ 2 / 24 := min_le_right _ _
  obtain ⟨δ, hδ, hgr⟩ := h.growth ε hεpos
  have hτc := (h.continuousOn_invCap hT).continuousWithinAt hσm
  rw [Metric.continuousWithinAt_iff] at hτc
  obtain ⟨η, hη, hτη⟩ := hτc δ hδ
  have hev1 : ∀ᶠ σ' in 𝓝[Ici σ] σ, σ' < cap B t₀ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hσ.2)
  have hev2 : ∀ᶠ σ' in 𝓝[Ici σ] σ, dist σ' σ < η :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds σ hη)
  filter_upwards [self_mem_nhdsWithin, hev1, hev2] with σ' hσ' h1 h2
  have hσ'm : σ' ∈ Icc 0 (cap B T) := ⟨hσ.1.trans hσ', h1.le.trans hcapT⟩
  set t := invCap B T σ' with ht
  have htm : t ∈ Icc 0 T := h.invCap_mem hT hσ'm
  have hst : s ≤ t := h.monotoneOn_invCap hT hσm hσ'm hσ'
  have htt₀ : t ≤ t₀ := (h.invCap_lt_of_lt_cap hT hσ'm ht₀ h1).le
  have hdist : t - s ≤ δ := by
    have := hτη hσ'm h2
    rw [Real.dist_eq] at this
    linarith [le_abs_self (t - s)]
  have hsub := hgr s hsm t htm hst hdist
  have hcapeq : hcapSet (inc B s t) = 2 * (σ' - σ) := by
    have := h.cap_sub_eq hsm htm hst
    rw [ht, hs, h.cap_invCap hT hσ'm, h.cap_invCap hT hσm] at this
    linarith
  have hstep := h.norm_step_le hεpos hsm htm ht₀ hst htt₀ hw hsub h4
  rw [hcapeq] at hstep
  have hσσ : 0 ≤ σ' - σ := sub_nonneg.2 hσ'
  have heq : mapOut (B t) w - mapOut (B s) w - (σ' - σ) • (2 / (mapOut (B s) w - U s)) =
      mapOut (B t) w - mapOut (B s) w - (((2 * (σ' - σ) : ℝ)) : ℂ) / (mapOut (B s) w - U s) := by
    rw [real_smul]; push_cast; ring
  simp only [← hs]
  rw [heq, Real.norm_eq_abs, abs_of_nonneg hσσ]
  calc _ ≤ 12 * ε * (2 * (σ' - σ)) / D ^ 2 := hstep
    _ ≤ 12 * (c * D ^ 2 / 24) * (2 * (σ' - σ)) / D ^ 2 := by gcongr
    _ = c * (σ' - σ) := by field_simp; ring

/-! ### The integral equation -/

theorem isMapOut_id_empty : IsMapOut ∅ id := by
  refine ⟨⟨differentiableOn_id, ?_⟩, ?_⟩
  · rw [sdiff_empty]; exact bijOn_id H
  · simp only [id_eq, sub_self]; exact tendsto_const_nhds

theorem mapOut_zero_apply (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) {w : ℂ} (hw : w ∈ H) :
    mapOut (B 0) w = w := by
  have h0 := h.isHPHull 0 ⟨le_rfl, hT⟩
  rw [h.zero] at h0 ⊢
  exact (isMapOut_mapOut h0).eqOn h0 isMapOut_id_empty ⟨hw, Set.notMem_empty w⟩

theorem invCap_zero (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) : invCap B T 0 = 0 := by
  have := h.invCap_cap (t := 0) ⟨le_rfl, hT⟩
  rwa [h.cap_zero hT] at this

/-- The driving function of the time-changed chain: `W̃ σ = U(τ σ)`, clamped to `[0, a T]`. -/
def drv (B : ℝ → Set ℂ) (U : ℝ → ℝ) (T : ℝ) (σ : ℝ) : ℝ :=
  U (invCap B T (max 0 (min σ (cap B T))))

theorem drv_eq (B : ℝ → Set ℂ) (U : ℝ → ℝ) (T : ℝ) {σ : ℝ} (hσ : σ ∈ Icc 0 (cap B T)) :
    drv B U T σ = U (invCap B T σ) := by
  rw [drv, min_eq_left hσ.2, max_eq_right hσ.1]

theorem continuous_drv (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) : Continuous (drv B U T) := by
  have h0 := h.cap_nonneg hT ⟨hT, le_rfl⟩
  have hcl : Continuous fun σ : ℝ => max 0 (min σ (cap B T)) := by fun_prop
  have hmaps : ∀ σ : ℝ, max 0 (min σ (cap B T)) ∈ Icc 0 (cap B T) := fun σ =>
    ⟨le_max_left _ _, max_le h0 (min_le_right _ _)⟩
  have hinv : ContinuousOn (fun σ => U (invCap B T σ)) (Icc 0 (cap B T)) :=
    h.continuousOn.comp (h.continuousOn_invCap hT) fun σ hσ => h.invCap_mem hT hσ
  exact hinv.comp_continuous hcl hmaps

theorem invCap_mem_Icc_of_le (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) {t₀ σ : ℝ}
    (ht₀ : t₀ ∈ Icc 0 T) (hσ : σ ∈ Icc 0 (cap B t₀)) : invCap B T σ ∈ Icc 0 t₀ := by
  have hσm : σ ∈ Icc 0 (cap B T) := ⟨hσ.1, hσ.2.trans (h.cap_mem hT ht₀).2⟩
  refine ⟨(h.invCap_mem hT hσm).1, ?_⟩
  have := h.monotoneOn_invCap hT hσm (h.cap_mem hT ht₀) hσ.2
  rwa [h.invCap_cap ht₀] at this

/-- **The flow of a point is a QuantumZipper forward solution** for the driver `W̃`
(integral form of the Loewner equation in the capacity clock). -/
theorem isForwardSol_flow (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) {t₀ : ℝ} {w : ℂ}
    (ht₀ : t₀ ∈ Icc 0 T) (hw : w ∈ H \ B t₀) :
    QuantumZipper.IsForwardSol (drv B U T) w (cap B t₀)
      (fun σ => mapOut (B (invCap B T σ)) w - drv B U T σ) := by
  set a₀ := cap B t₀ with ha₀
  have ha₀T : a₀ ≤ cap B T := (h.cap_mem hT ht₀).2
  have hsubT : Icc 0 a₀ ⊆ Icc 0 (cap B T) := Icc_subset_Icc_right ha₀T
  set Y : ℝ → ℂ := fun σ => mapOut (B (invCap B T σ)) w with hY
  set Ut : ℝ → ℂ := fun σ => (U (invCap B T σ) : ℂ) with hUt
  have hmem : ∀ σ ∈ Icc 0 a₀, invCap B T σ ∈ Icc 0 t₀ := fun σ hσ =>
    h.invCap_mem_Icc_of_le hT ht₀ hσ
  have hmemT : ∀ σ ∈ Icc 0 a₀, invCap B T σ ∈ Icc 0 T := fun σ hσ =>
    Icc_subset_Icc_right ht₀.2 (hmem σ hσ)
  have hwσ : ∀ σ ∈ Icc 0 a₀, w ∈ H \ B (invCap B T σ) := fun σ hσ =>
    h.mem_H_diff_of_le (hmemT σ hσ) ht₀ (hmem σ hσ).2 hw
  have hYc : ContinuousOn Y (Icc 0 a₀) :=
    (h.continuousOn_mapOut_apply ht₀ hw).comp ((h.continuousOn_invCap hT).mono hsubT) hmem
  have hUc : ContinuousOn Ut (Icc 0 a₀) :=
    continuous_ofReal.comp_continuousOn
      (h.continuousOn.comp ((h.continuousOn_invCap hT).mono hsubT) hmemT)
  have hne : ∀ σ ∈ Icc 0 a₀, Y σ - Ut σ ≠ 0 := by
    intro σ hσ h0
    have := h.im_mapOut_pos (hmemT σ hσ) (hwσ σ hσ)
    have h1 := congrArg Complex.im h0
    simp only [hY, hUt, sub_im, ofReal_im, sub_zero, zero_im] at h1
    linarith
  set φ : ℝ → ℂ := fun σ => 2 / (Y σ - Ut σ) with hφ
  have hφc : ContinuousOn φ (Icc 0 a₀) :=
    continuousOn_const.div (hYc.sub hUc) hne
  have ha₀0 : 0 ≤ a₀ := h.cap_nonneg hT ht₀
  set cl : ℝ → ℝ := fun σ => max 0 (min σ a₀) with hcl
  have hclm : ∀ σ, cl σ ∈ Icc 0 a₀ := fun σ => ⟨le_max_left _ _, max_le ha₀0 (min_le_right _ _)⟩
  have hcleq : ∀ σ ∈ Icc 0 a₀, cl σ = σ := fun σ hσ => by
    simp only [hcl, min_eq_left hσ.2, max_eq_right hσ.1]
  set φ' : ℝ → ℂ := fun σ => φ (cl σ) with hφ'
  have hφ'c : Continuous φ' := hφc.comp_continuous (by fun_prop) hclm
  set Fw : ℝ → ℂ := fun σ => w + ∫ r in (0 : ℝ)..σ, φ' r with hFw
  have hF : ∀ σ, HasDerivAt Fw (φ' σ) σ := fun σ =>
    ((hφ'c.integral_hasStrictDerivAt 0 σ).hasDerivAt).const_add w
  have hYF : ∀ σ ∈ Icc 0 a₀, Y σ = Fw σ := by
    refine eq_of_has_deriv_right_eq (f' := φ) (fun σ hσ => ?_) (fun σ hσ => ?_) hYc
      (fun σ _ => (hF σ).continuousAt.continuousWithinAt) ?_
    · exact h.hasDerivWithinAt_flow hT ht₀ hw hσ
    · have := (hF σ).hasDerivWithinAt (s := Ici σ)
      have he : φ' σ = φ σ := by simp only [hφ', hcleq σ (Ico_subset_Icc_self hσ)]
      rwa [he] at this
    · simp only [hY, hFw, intervalIntegral.integral_same, add_zero, h.invCap_zero hT]
      exact h.mapOut_zero_apply hT hw.1
  refine ⟨?_, fun σ hσ => ⟨?_, ?_⟩⟩
  · refine (hYc.sub (continuous_ofReal.comp_continuousOn ?_))
    exact ((continuous_drv h hT).continuousOn)
  · have := hne σ hσ
    simp only [hY, hUt] at this
    simp only [drv_eq B U T (hsubT hσ)]
    exact this
  · have hint : ∫ r in (0 : ℝ)..σ, 2 / (mapOut (B (invCap B T r)) w - drv B U T r) =
        ∫ r in (0 : ℝ)..σ, φ' r := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hσ.1] at hr
      have hra : r ∈ Icc 0 a₀ := ⟨hr.1, hr.2.trans hσ.2⟩
      simp only [hφ', hcleq r hra, hφ, hY, hUt, drv_eq B U T (hsubT hra)]
    rw [hint]
    have := hYF σ hσ
    simp only [hY, hFw] at this
    show mapOut (B (invCap B T σ)) w - _ = _
    rw [this]
    ring

/-! ### Identification of the hulls -/

/-- **Right continuity**: a point not in `B t` (`t < T`) is not in `B t'` for some `t' > t`. -/
theorem exists_notMem_of_notMem (h : IsContinuouslyGrowing B U T) {t : ℝ} {w : ℂ}
    (ht : t ∈ Icc 0 T) (htT : t < T) (hw : w ∈ H \ B t) :
    ∃ t' ∈ Icc 0 T, t < t' ∧ w ∉ B t' := by
  by_contra hcon
  push Not at hcon
  have him := h.im_mapOut_pos ht hw
  obtain ⟨δ, hδ, hgr⟩ := h.growth ((mapOut (B t) w).im / 2) (by positivity)
  set t' := min (t + δ) T with ht'
  have htt' : t < t' := lt_min (by linarith) htT
  have ht'm : t' ∈ Icc 0 T := ⟨by linarith [ht.1], min_le_right _ _⟩
  have hwt' := hcon t' ht'm htt'
  have hmem : mapOut (B t) w ∈ inc B t t' := ⟨w, ⟨hwt', hw.2⟩, rfl⟩
  have := hgr t ht t' ht'm htt'.le (by linarith [min_le_left (t + δ) T]) hmem
  rw [mem_closedBall, dist_eq_norm] at this
  have h2 : (mapOut (B t) w).im ≤ ‖mapOut (B t) w - U t‖ := by
    calc (mapOut (B t) w).im = (mapOut (B t) w - U t).im := by simp
      _ ≤ ‖mapOut (B t) w - U t‖ := (le_abs_self _).trans (abs_im_le_norm _)
  linarith

/-- **[Law05] §4.1: a continuously growing family of hulls is a Loewner chain after the capacity
time change** `a(t) = hcap(B t)/2`: for the continuous driver `W̃ = drv B U T`,
`W̃(a t) = U t`, the QuantumZipper hull of `W̃` at time `a t` is `B t`, and
`f̃_{a t} + W̃(a t) = g_{B t}` off `B t`. -/
theorem loewner (h : IsContinuouslyGrowing B U T) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    drv B U T (cap B t) = U t ∧ QuantumZipper.fwdHull (drv B U T) (cap B t) = B t ∧
      ∀ w ∈ H \ B t, QuantumZipper.fwdMap (drv B U T) (cap B t) w + drv B U T (cap B t) =
        mapOut (B t) w := by
  have hW := h.continuous_drv hT
  have hcapm := h.cap_mem hT ht
  have hdrv : drv B U T (cap B t) = U t := by rw [drv_eq B U T hcapm, h.invCap_cap ht]
  refine ⟨hdrv, ?_, fun w hw => ?_⟩
  · ext z
    constructor
    · intro hz
      by_contra hzB
      exact QuantumZipper.Thm18Asm.LWFar.lwc_notMem_fwdHull_of_sol hW hz.1
        (h.cap_nonneg hT ht) (h.isForwardSol_flow hT ht ⟨hz.1, hzB⟩) hz
    · intro hzB
      have hzH : z ∈ H := (h.isHPHull t ht).1 hzB
      refine ⟨hzH, ?_⟩
      refine sSup_le ?_
      rintro _ ⟨S, ⟨hS0, v, hv⟩, rfl⟩
      refine ENNReal.ofReal_le_ofReal (le_of_not_gt fun hSt => ?_)
      -- the last time before `z` is swallowed
      set S₀ := {s ∈ Icc (0 : ℝ) T | z ∉ B s} with hS₀
      have h0S : (0 : ℝ) ∈ S₀ := ⟨⟨le_rfl, hT⟩, by rw [h.zero]; exact Set.notMem_empty z⟩
      have hS₀le : ∀ s ∈ S₀, s < t := fun s hs => by
        by_contra hle
        rw [not_lt] at hle
        exact hs.2 (h.mono t ht s hs.1 hle hzB)
      have hbdd : BddAbove S₀ := ⟨t, fun s hs => (hS₀le s hs).le⟩
      set s₀ := sSup S₀ with hs₀
      have hs₀t : s₀ ≤ t := csSup_le ⟨0, h0S⟩ fun s hs => (hS₀le s hs).le
      have hs₀0 : 0 ≤ s₀ := le_csSup hbdd h0S
      have hs₀m : s₀ ∈ Icc 0 T := ⟨hs₀0, hs₀t.trans ht.2⟩
      have hzs₀ : z ∈ B s₀ := by
        by_contra hzs
        have hs₀S : s₀ ∈ S₀ := ⟨hs₀m, hzs⟩
        obtain ⟨t', ht'm, hlt, hzt'⟩ :=
          h.exists_notMem_of_notMem hs₀m ((hS₀le s₀ hs₀S).trans_le ht.2) ⟨hzH, hzs⟩
        exact absurd (le_csSup hbdd ⟨ht'm, hzt'⟩) (not_le.2 hlt)
      -- `v` is bounded below on `[0, a s₀]`
      have hcs₀ : cap B s₀ ≤ cap B t := h.strictMonoOn_cap.monotoneOn hs₀m ht hs₀t
      have hsub : Icc 0 (cap B s₀) ⊆ Icc 0 S := Icc_subset_Icc_right (by linarith)
      obtain ⟨σm, hσm, hmin⟩ := isCompact_Icc.exists_isMinOn
        (nonempty_Icc.2 (h.cap_nonneg hT hs₀m)) ((hv.1.mono hsub).norm)
      set c := ‖v σm‖ with hc
      have hcpos : 0 < c := norm_pos_iff.2 (hv.2 σm (hsub hσm)).1
      obtain ⟨δ, hδ, hgr⟩ := h.growth (c / 2) (half_pos hcpos)
      obtain ⟨s, hsS, hslt⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ (show s₀ - δ < s₀ by linarith)
      have hss₀ : s ≤ s₀ := le_csSup hbdd hsS
      have hmem : mapOut (B s) z ∈ inc B s s₀ := ⟨z, ⟨hzs₀, hsS.2⟩, rfl⟩
      have hball := hgr s hsS.1 s₀ hs₀m hss₀ (by linarith) hmem
      rw [mem_closedBall, dist_eq_norm] at hball
      -- the flow solution at time `a s` agrees with `v`
      have hsol := h.isForwardSol_flow hT hsS.1 ⟨hzH, hsS.2⟩
      have hcs : cap B s ≤ cap B s₀ := h.strictMonoOn_cap.monotoneOn hsS.1 hs₀m hss₀
      have hvs : QuantumZipper.IsForwardSol (drv B U T) z (cap B s) v :=
        QuantumZipper.isForwardSol_restrict hv (h.cap_nonneg hT hsS.1) (by linarith)
      have heq := QuantumZipper.isForwardSol_unique hW hzH hvs hsol
        ⟨h.cap_nonneg hT hsS.1, le_rfl⟩
      rw [drv_eq B U T (h.cap_mem hT hsS.1), h.invCap_cap hsS.1] at heq
      have hle : ‖v σm‖ ≤ ‖v (cap B s)‖ := hmin ⟨h.cap_nonneg hT hsS.1, hcs⟩
      rw [heq] at hle
      linarith
  · have hsol := h.isForwardSol_flow hT ht hw
    rw [QuantumZipper.fwdMap_eq hW hw.1 hsol ⟨h.cap_nonneg hT ht, le_rfl⟩]
    simp only [h.invCap_cap ht]
    ring

end IsContinuouslyGrowing

end ConformalImage

end InteractingSLE
