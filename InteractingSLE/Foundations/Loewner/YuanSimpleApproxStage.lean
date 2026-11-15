import InteractingSLE.Foundations.Loewner.YuanSimpleApproxConf
import InteractingSLE.Foundations.Loewner.YuanSimpleApproxTime

/-!
# Simple approximations of Loewner traces, V: the stage curves

Fix a continuous Loewner trace `η` of `W`, cut times `t n` (`t 0 = 0`, the others distinct cut
times of `η`, `IsCutTime`), slit lengths `h n > 0` with `∑ h n < ∞`, and cut heights `c n > 0`.
The **stage-`N` curve** `stageCurve W t h c N` lives on the stretched time `s ≥ 0`: the cuts
`0, …, N − 1` are inserted (each in the chart of the original trace at its time, see
`YuanSimpleApproxConf`), the later ones are halted:

  `stageCurve W t h c N s =
    conf W 0 [(t n, c n · slitFrac n s) | n < N, sorted by t n] (origTime s)`.

This is the analogue of Yuan's `γ^N` ([Yua22] §4, `TraceTopology.tex` L499–L511).

## Main results

* `continuousOn_stageCurve`, `stageCurve_mem_Hbar`, `stageCurve_zero_time`, `stageCurve_zero`,
  `le_im_stageCurve`: continuity, values, the start `0`, the halted trace at stage `0`, and the
  initial push into `ℍ` (the cut `0` at time `0`);
* `exists_stageCurve_succ_repr`: **inserting the cut `N`**: after the original time `t N`, the
  stage-`(N+1)` curve is `Φ(x · frac · i + z)` and the stage-`N` curve is `Φ(z)`, for a map `Φ`
  holomorphic and injective on `ℍ` and a continuous `z` (both independent of the new height `x`);
  before the cut nothing changes;
* `stageCurve_succ_ne`: **the new cut separates** the stage-`(N+1)` curve before the slit
  interval `I_N` from the curve after it;
* `injOn_stageCurve_succ`: the stage-`(N+1)` curve is injective on `I_N`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Function

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace YuanSimpleApprox

/-! ### The sorted list of active cuts -/

/-- The cuts `0, …, N − 1`, sorted by their times `t n`. -/
def actList (t : ℕ → ℝ) : ℕ → List ℕ
  | 0 => []
  | N + 1 => (actList t N).orderedInsert (fun i j => t i ≤ t j) N

variable {t h : ℕ → ℝ}

theorem mem_actList {N n : ℕ} : n ∈ actList t N ↔ n < N := by
  induction N with
  | zero => simp [actList]
  | succ N ih => rw [actList, List.mem_orderedInsert, ih]; omega

theorem pairwise_actList (ht : Injective t) (N : ℕ) :
    (actList t N).Pairwise (fun i j => t i < t j) := by
  have hle : ∀ N, (actList t N).Pairwise (fun i j => t i ≤ t j) := by
    have : Std.Total (fun i j : ℕ => t i ≤ t j) := ⟨fun i j => le_total _ _⟩
    have : IsTrans ℕ (fun i j : ℕ => t i ≤ t j) := ⟨fun _ _ _ => le_trans⟩
    intro N
    induction N with
    | zero => exact List.Pairwise.nil
    | succ N ih => exact ih.orderedInsert _ _
  have hnd : ∀ N, (actList t N).Nodup := by
    intro N
    induction N with
    | zero => exact List.nodup_nil
    | succ N ih =>
      rw [actList]
      exact (List.perm_orderedInsert _ N _).nodup_iff.2
        (List.nodup_cons.2 ⟨fun h' => lt_irrefl N (mem_actList.1 h'), ih⟩)
  exact ((hle N).and (hnd N)).imp fun h' => lt_of_le_of_ne h'.1 fun e => h'.2 (ht e)

/-- Inserting the cut `N` splits the active cuts into those before and after `t N`. -/
theorem exists_actList_split (ht : Injective t) (N : ℕ) :
    ∃ L₁ L₂ : List ℕ, actList t N = L₁ ++ L₂ ∧ actList t (N + 1) = L₁ ++ N :: L₂ ∧
      (∀ m ∈ L₁, t m < t N) ∧ ∀ m ∈ L₂, t N < t m := by
  have hins := List.orderedInsert_eq_take_drop (fun i j : ℕ => t i ≤ t j) N (actList t N)
  refine ⟨(actList t N).takeWhile (fun b => decide ¬t N ≤ t b),
    (actList t N).dropWhile (fun b => decide ¬t N ≤ t b),
    List.takeWhile_append_dropWhile.symm, ?_, ?_, ?_⟩
  · rw [actList]; exact hins
  · intro m hm
    have := List.all_eq_true.1 List.all_takeWhile m hm
    simpa using this
  · intro m hm
    have hp := pairwise_actList ht (N + 1)
    rw [actList, hins, List.pairwise_append] at hp
    exact (List.pairwise_cons.1 hp.2.1).1 m hm

/-! ### Cut data -/

/-- **Cut data** for the trace `η`: injective cut times with `t 0 = 0`, the others positive cut
times of `η` below `S`, positive summable slit lengths. -/
structure IsCutData (η : ℝ → ℂ) (S : ℝ) (t h : ℕ → ℝ) : Prop where
  inj : Injective t
  zero : t 0 = 0
  pos : ∀ n, n ≠ 0 → 0 < t n
  lt : ∀ n, t n < S
  cut : ∀ n, n ≠ 0 → IsCutTime η (t n)
  hpos : ∀ n, 0 < h n
  summable : Summable h

theorem IsCutData.nonneg {η : ℝ → ℂ} {S : ℝ} (hd : IsCutData η S t h) (n : ℕ) : 0 ≤ t n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact hd.zero.ge
  · exact (hd.pos n hn).le

theorem IsCutData.origTime_nonneg {η : ℝ → ℂ} {S : ℝ} (hd : IsCutData η S t h) {s : ℝ}
    (hs : 0 ≤ s) : 0 ≤ origTime t h s := by
  have := monotone_origTime hd.hpos hd.summable hd.inj hs
  rwa [origTime_zero hd.hpos hd.nonneg] at this

theorem IsCutData.slitBefore_zero {η : ℝ → ℂ} {S : ℝ} (hd : IsCutData η S t h) :
    slitBefore t h 0 = 0 := by
  refine (tsum_congr fun m => ?_).trans tsum_zero
  simp [not_lt.2 (hd.nonneg m)]

theorem IsCutData.slitStart_zero {η : ℝ → ℂ} {S : ℝ} (hd : IsCutData η S t h) :
    slitStart t h 0 = 0 := by
  rw [slitStart, hd.zero, hd.slitBefore_zero, add_zero]

/-- The head of the active list is the cut `0` at time `0`. -/
theorem IsCutData.actList_eq_cons {η : ℝ → ℂ} {S : ℝ} (hd : IsCutData η S t h) {N : ℕ}
    (hN : 1 ≤ N) : ∃ rest, actList t N = 0 :: rest := by
  have h0 : 0 ∈ actList t N := mem_actList.2 hN
  rcases hl : actList t N with _ | ⟨a, rest⟩
  · rw [hl] at h0; exact absurd h0 List.not_mem_nil
  · refine ⟨rest, ?_⟩
    by_contra hne
    have ha : a ≠ 0 := fun e => hne (by rw [e])
    have h0r : 0 ∈ rest := by
      rw [hl, List.mem_cons] at h0
      exact h0.resolve_left (Ne.symm ha)
    have hp := pairwise_actList hd.inj N
    rw [hl, List.pairwise_cons] at hp
    have := hp.1 0 h0r
    rw [hd.zero] at this
    exact absurd (hd.pos a ha) (not_lt.2 this.le)

/-! ### The stage curves -/

/-- Heights of the cuts at the stretched time `s`: `c n` times the traversed fraction. -/
def heights (t h c : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ := c n * slitFrac t h n s

/-- The **stage-`N` curve**: cuts `0, …, N − 1` inserted. -/
def stageCurve (W : ℝ → ℝ) (t h c : ℕ → ℝ) (N : ℕ) (s : ℝ) : ℂ :=
  conf W 0 (cfg t (heights t h c s) (actList t N)) (origTime t h s)

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {S : ℝ} {c : ℕ → ℝ}

theorem stageCurve_congr {c c' : ℕ → ℝ} {N : ℕ} (hcc : ∀ m < N, c m = c' m) (s : ℝ) :
    stageCurve W t h c N s = stageCurve W t h c' N s := by
  have : cfg t (heights t h c s) (actList t N) = cfg t (heights t h c' s) (actList t N) :=
    List.map_congr_left fun m hm => by rw [heights, heights, hcc m (mem_actList.1 hm)]
  unfold stageCurve
  rw [this]

theorem heights_nonneg (hc : ∀ n, 0 < c n) (s : ℝ) (n : ℕ) : 0 ≤ heights t h c s n :=
  mul_nonneg (hc n).le (slitFrac_nonneg n s)

theorem heights_le (hc : ∀ n, 0 < c n) (s : ℝ) (n : ℕ) : heights t h c s n ≤ c n :=
  mul_le_of_le_one_right (hc n).le (slitFrac_le_one n s)

theorem heights_of_lt (hd : IsCutData η S t h) {s : ℝ} {n : ℕ} (hs : t n < origTime t h s) :
    heights t h c s n = c n := by
  rw [heights, slitFrac_eq_one_of_lt_origTime hd.hpos hd.summable hd.inj hs, mul_one]

theorem heights_of_gt (hd : IsCutData η S t h) {s : ℝ} {n : ℕ} (hs : origTime t h s < t n) :
    heights t h c s n = 0 := by
  rw [heights, slitFrac_eq_zero_of_origTime_lt hd.hpos hd.summable hd.inj hs, mul_zero]

theorem stageCurve_zero_time (hW : Continuous W) (hd : IsCutData η S t h) (N : ℕ) :
    stageCurve W t h c N 0 = 0 := by
  unfold stageCurve
  rw [origTime_zero hd.hpos hd.nonneg]
  refine conf_eq_zero hW (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨m, -, rfl⟩ := mem_cfg.1 hp; exact hd.nonneg m
  · obtain ⟨m, -, rfl⟩ := mem_cfg.1 hp
    rw [heights, (slitFrac_eq_zero_iff hd.hpos).2 (slitStart_nonneg hd.hpos hd.nonneg m),
      mul_zero]

/-- At stage `0` the curve is the trace, halted on the slit intervals. -/
theorem stageCurve_zero (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hd : IsCutData η S t h) {s : ℝ} (hs : 0 ≤ s) :
    stageCurve W t h c 0 s = η (origTime t h s) := by
  show trMap W 0 (origTime t h s) 0 = _
  rw [trMap_zero_left hW0]
  exact hη.loewnerTip_eq hW hW0 (hd.origTime_nonneg hs)

theorem cfg_append (E : ℕ → ℝ) (L₁ L₂ : List ℕ) :
    cfg t E (L₁ ++ L₂) = cfg t E L₁ ++ cfg t E L₂ := List.map_append

theorem cfg_cons (E : ℕ → ℝ) (n : ℕ) (L : List ℕ) :
    cfg t E (n :: L) = (t n, E n) :: cfg t E L := rfl

theorem cfg_congr {E E' : ℕ → ℝ} {L : List ℕ} (hE : ∀ m ∈ L, E m = E' m) :
    cfg t E L = cfg t E' L :=
  List.map_congr_left fun m hm => by rw [hE m hm]

/-- With positive heights, the layer maps are injective on all of `ℍ̄`. -/
theorem layers_injOn_Hbar (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {a τ : ℝ} (ha : 0 ≤ a) (haτ : a ≤ τ) {L : List (ℝ × ℝ)} (hL : Adm a L)
    (hpos : ∀ p ∈ L, 0 < p.2) : InjOn (layers W a L τ) Hbar := by
  induction L generalizing a with
  | nil => exact injOn_id _
  | cons p L ih =>
    have hmem : p ∈ p :: L := List.mem_cons_self ..
    have hm : a ≤ min p.1 τ := le_min (hL.2.1 p hmem) haτ
    have hL' : Adm (min p.1 τ) L := hL.tail (min_le_left _ _)
    intro w hw w' hw' heq
    have h1 := layers_mem_Hbar hη hW hW0 (ha.trans hm) (min_le_right _ _) hL' hw
    have h2 := layers_mem_Hbar hη hW hW0 (ha.trans hm) (min_le_right _ _) hL' hw'
    have := trMap_injOn hη hW hW0 ha hm (add_mem_H_of_pos (hpos p hmem) h1)
      (add_mem_H_of_pos (hpos p hmem) h2) heq
    exact ih (ha.trans hm) (min_le_right _ _) hL' (fun q hq => hpos q (List.mem_cons_of_mem _ hq))
      hw hw' (add_left_cancel this)

section Trace

variable (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
  (hd : IsCutData η S t h) (hc : ∀ n, 0 < c n)
include hη hW hW0 hd hc

omit hη hW hW0 hd in
theorem adm_cfg_actList {a : ℝ} (s : ℝ) {L : List ℕ} (hL : L.Pairwise (fun i j => t i < t j))
    (hge : ∀ m ∈ L, a ≤ t m) : Adm a (cfg t (heights t h c s) L) :=
  adm_cfg hL hge fun m _ => heights_nonneg hc s m

theorem continuousOn_stageCurve (N : ℕ) : ContinuousOn (stageCurve W t h c N) (Ici 0) :=
  continuousOn_conf hη hW hW0 le_rfl (E := fun n s => heights t h c s n)
    (pairwise_actList hd.inj N) (fun n _ => hd.nonneg n)
    (fun n _ => continuous_const.mul (continuous_slitFrac n))
    (fun n _ s => heights_nonneg hc s n) isClosed_Ici
    (continuous_origTime hd.hpos hd.summable).continuousOn
    (fun _ hs => hd.origTime_nonneg hs)
    (fun _ _ _ _ hlt => heights_of_gt hd hlt)

theorem stageCurve_mem_Hbar (N : ℕ) {s : ℝ} (hs : 0 ≤ s) : stageCurve W t h c N s ∈ Hbar :=
  conf_mem_Hbar hη hW hW0 le_rfl (hd.origTime_nonneg hs)
    (adm_cfg_actList hc s (pairwise_actList hd.inj N) fun n _ => hd.nonneg n)

/-- **The initial push**: from stage `1` on, the curve is lifted by the cut at time `0`. -/
theorem le_im_stageCurve {N : ℕ} (hN : 1 ≤ N) {s : ℝ} (hs : 0 ≤ s) :
    c 0 * slitFrac t h 0 s ≤ (stageCurve W t h c N s).im := by
  obtain ⟨rest, hrest⟩ := hd.actList_eq_cons hN
  have hp := pairwise_actList hd.inj N
  rw [hrest, List.pairwise_cons] at hp
  have hτ := hd.origTime_nonneg hs
  unfold stageCurve
  rw [hrest, show cfg t (heights t h c s) (0 :: rest) =
    (t 0, heights t h c s 0) :: cfg t (heights t h c s) rest from rfl, conf_cons, hd.zero,
    min_eq_left hτ]
  have hin : conf W 0 (cfg t (heights t h c s) rest) (origTime t h s) ∈ Hbar :=
    conf_mem_Hbar hη hW hW0 le_rfl hτ
      (adm_cfg_actList hc s hp.2 fun m _ => hd.nonneg m)
  rw [trMap_self hW 0 (add_mem_Hbar (heights_nonneg hc s 0) hin),
    im_ofReal_mul_I_add]
  have : (0 : ℝ) ≤ (conf W 0 (cfg t (heights t h c s) rest) (origTime t h s)).im := hin
  rw [heights]
  linarith

theorem im_stageCurve_pos {N : ℕ} (hN : 1 ≤ N) {s : ℝ} (hs : 0 < s) :
    0 < (stageCurve W t h c N s).im := by
  have hfrac : 0 < slitFrac t h 0 s := by
    rcases (slitFrac_nonneg (t := t) (h := h) 0 s).lt_or_eq with h' | h'
    · exact h'
    · have := (slitFrac_eq_zero_iff hd.hpos).1 h'.symm
      rw [hd.slitStart_zero] at this
      linarith
  exact lt_of_lt_of_le (mul_pos (hc 0) hfrac) (le_im_stageCurve hη hW hW0 hd hc hN hs.le)

/-- **Inserting the cut `N`.** There are a map `Φ` (holomorphic and injective on `ℍ`, continuous
on `ℍ̄`, injective on the vertical half-line) and a continuous `z` such that, after the original
time `t N`, the stage-`N` curve is `Φ ∘ z` and the stage-`(N+1)` curve with any new height `x` is
`Φ(x · frac_N · i + z)`; where the slit `N` is not yet started, nothing changes. `Φ` and `z` do
not depend on the new height. On the cut segment `z = 0`, and at later cut times `z ∈ ℍ`. -/
theorem exists_stageCurve_succ_repr (N : ℕ) :
    ∃ Φ : ℂ → ℂ, ∃ z : ℝ → ℂ,
      ContinuousOn Φ Hbar ∧ MapsTo Φ Hbar Hbar ∧ DifferentiableOn ℂ Φ H ∧ InjOn Φ H ∧
      (∀ θ θ' : ℝ, 0 ≤ θ → 0 ≤ θ' → Φ (θ * I) = Φ (θ' * I) → θ = θ') ∧
      ContinuousOn z {s | 0 ≤ s ∧ t N ≤ origTime t h s} ∧
      (∀ s, 0 ≤ s → t N ≤ origTime t h s → z s ∈ Hbar) ∧
      (∀ s, 0 ≤ s → ∀ k, k ≠ 0 → t N < t k → origTime t h s = t k → z s ∈ H) ∧
      (∀ s, origTime t h s = t N → z s = 0) ∧
      (∀ s, 0 ≤ s → t N ≤ origTime t h s → stageCurve W t h c N s = Φ (z s)) ∧
      ∀ x : ℝ, 0 < x → ∀ s, 0 ≤ s →
        (t N ≤ origTime t h s → stageCurve W t h (update c N x) (N + 1) s =
          Φ (((x * slitFrac t h N s : ℝ) : ℂ) * I + z s)) ∧
        (slitFrac t h N s = 0 →
          stageCurve W t h (update c N x) (N + 1) s = stageCurve W t h c N s) := by
  obtain ⟨L₁, L₂, hsplit, hsplit', hL₁, hL₂⟩ := exists_actList_split hd.inj N
  have hpw := pairwise_actList hd.inj (N + 1)
  rw [hsplit', List.pairwise_append] at hpw
  have hpw₁ := hpw.1
  have hpw₂ := (List.pairwise_cons.1 hpw.2.1).2
  have hmem₁ : ∀ m ∈ L₁, m < N := fun m hm =>
    mem_actList.1 (hsplit ▸ List.mem_append_left _ hm)
  have hmem₂ : ∀ m ∈ L₂, m < N := fun m hm =>
    mem_actList.1 (hsplit ▸ List.mem_append_right _ hm)
  have htN := hd.nonneg N
  have hadm₁ : Adm 0 (cfg t c L₁) := adm_cfg hpw₁ (fun m _ => hd.nonneg m) fun m _ => (hc m).le
  set b := lastBase 0 (cfg t c L₁) (t N) with hb
  have hb0 : 0 ≤ b := lastBase_nonneg le_rfl htN hadm₁
  have hbN : b ≤ t N := lastBase_le htN _
  set Φ : ℂ → ℂ := fun w => layers W 0 (cfg t c L₁) (t N) (trMap W b (t N) w) with hΦ
  set z : ℝ → ℂ := fun s => conf W (t N) (cfg t (heights t h c s) L₂) (origTime t h s) with hz
  have hadm₂ : ∀ s, Adm (t N) (cfg t (heights t h c s) L₂) := fun s =>
    adm_cfg_actList hc s hpw₂ fun m hm => (hL₂ m hm).le
  have hΦc : ContinuousOn Φ Hbar :=
    (layers_continuousOn hη hW hW0 le_rfl htN hadm₁).comp
      (trMap_continuousOn hη hW hW0 hb0 hbN) (trMap_mapsTo_Hbar hη hW hW0 hb0 hbN)
  have hΦm : MapsTo Φ Hbar Hbar := fun w hw =>
    layers_mem_Hbar hη hW hW0 le_rfl htN hadm₁ (trMap_mapsTo_Hbar hη hW hW0 hb0 hbN hw)
  -- the outer layers on the cuts before `t N`, at later times
  have houter : ∀ s, t N ≤ origTime t h s →
      cfg t (heights t h c s) L₁ = cfg t c L₁ ∧
      layers W 0 (cfg t c L₁) (origTime t h s) = layers W 0 (cfg t c L₁) (t N) ∧
      lastBase 0 (cfg t c L₁) (origTime t h s) = b := by
    intro s hs
    have hle : ∀ p ∈ cfg t c L₁, p.1 ≤ t N := fun p hp => by
      obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp; exact (hL₁ m hm).le
    obtain ⟨e1, e2⟩ := layers_congr_time (W := W) (a := 0) (fun p hp => (hle p hp).trans hs) hle
    exact ⟨cfg_congr fun m hm => heights_of_lt hd (lt_of_lt_of_le (hL₁ m hm) hs), e1, e2⟩
  have hcN : ∀ x : ℝ, ∀ m, m < N → update c N x m = c m := fun x m hm =>
    update_of_ne (Nat.ne_of_lt hm) _ _
  refine ⟨Φ, z, hΦc, hΦm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (layers_differentiableOn hη hW hW0 le_rfl htN hadm₁).comp
      (trMap_differentiableOn hη hW hW0 hb0 hbN) fun w hw => trMap_mem_H hW hbN hw
  · exact (layers_injOn hη hW hW0 le_rfl htN hadm₁).comp (trMap_injOn hη hW hW0 hb0 hbN)
      fun w hw => trMap_mem_H hW hbN hw
  · intro θ θ' hθ hθ' heq
    have hlay := layers_injOn_Hbar hη hW hW0 le_rfl htN hadm₁ (fun p hp => by
      obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp; exact hc m)
    have hI : ∀ r : ℝ, 0 ≤ r → (r : ℂ) * I ∈ Hbar := fun r hr =>
      show 0 ≤ ((r : ℂ) * I).im by simpa using hr
    have heq' := hlay (trMap_mapsTo_Hbar hη hW hW0 hb0 hbN (hI θ hθ))
      (trMap_mapsTo_Hbar hη hW hW0 hb0 hbN (hI θ' hθ')) heq
    have hfib := (trMap_fiber_hyps hη hW hW0 hb0 hbN).2.2.2
    have hIH : ∀ r : ℝ, 0 < r → (r : ℂ) * I ∈ H := fun r hr =>
      show 0 < ((r : ℂ) * I).im by simpa using hr
    rcases hθ.lt_or_eq with hθp | hθ0 <;> rcases hθ'.lt_or_eq with hθ'p | hθ'0
    · have := trMap_injOn hη hW hW0 hb0 hbN (hIH θ hθp) (hIH θ' hθ'p) heq'
      simpa using congrArg Complex.im this
    · exfalso
      rw [← hθ'0, Complex.ofReal_zero, zero_mul] at heq'
      exact hfib 0 (by simp) ⟨_, hIH θ hθp, heq'⟩
    · exfalso
      rw [← hθ0, Complex.ofReal_zero, zero_mul] at heq'
      exact hfib 0 (by simp) ⟨_, hIH θ' hθ'p, heq'.symm⟩
    · rw [← hθ0, ← hθ'0]
  · refine continuousOn_conf hη hW hW0 htN (E := fun n s => heights t h c s n) hpw₂
      (fun m hm => (hL₂ m hm).le) (fun n _ => continuous_const.mul (continuous_slitFrac n))
      (fun n _ s => heights_nonneg hc s n)
      ((isClosed_le continuous_const continuous_id).inter
        (isClosed_le continuous_const (continuous_origTime hd.hpos hd.summable)))
      (continuous_origTime hd.hpos hd.summable).continuousOn (fun s hs => hs.2)
      (fun _ _ _ _ hlt => heights_of_gt hd hlt)
  · intro s _ hs
    exact conf_mem_Hbar hη hW hW0 htN hs (hadm₂ s)
  · intro s _ k hk hNk hτ
    have := conf_mem_H hη hW hW0 (hd.cut k hk) htN hNk (hadm₂ s) (fun p hp hlt => ?_)
      (fun p hp hlt => ?_)
    · show conf W (t N) (cfg t (heights t h c s) L₂) (origTime t h s) ∈ H
      rw [hτ]; exact this
    · obtain ⟨m, -, rfl⟩ := mem_cfg.1 hp
      rw [heights_of_lt hd (hτ ▸ hlt)]; exact hc m
    · obtain ⟨m, -, rfl⟩ := mem_cfg.1 hp
      exact heights_of_gt hd (hτ ▸ hlt)
  · intro s hτ
    show conf W (t N) (cfg t (heights t h c s) L₂) (origTime t h s) = 0
    rw [hτ]
    refine conf_eq_zero hW (fun p hp => ?_) (fun p hp => ?_)
    · obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp; exact (hL₂ m hm).le
    · obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp
      exact heights_of_gt hd (hτ ▸ hL₂ m hm)
  · intro s _ hs
    obtain ⟨e0, e1, e2⟩ := houter s hs
    unfold stageCurve
    rw [hsplit, cfg_append, conf_append, e0, e1, e2,
      ← trMap_conf hη hW hW0 hb0 hbN hs (hadm₂ s)]
  · intro x _ s hs0
    have hτ0 := hd.origTime_nonneg hs0
    have hcong : ∀ m, m ≠ N → heights t h (update c N x) s m = heights t h c s m := fun m hm => by
      rw [heights, heights, update_of_ne hm]
    have hcN' : heights t h (update c N x) s N = x * slitFrac t h N s := by
      rw [heights, update_self]
    have hlist : cfg t (heights t h (update c N x) s) (actList t (N + 1)) =
        cfg t (heights t h c s) L₁ ++ (t N, x * slitFrac t h N s) ::
          cfg t (heights t h c s) L₂ := by
      rw [hsplit', cfg_append, cfg_cons, hcN',
        cfg_congr fun m hm => hcong m (Nat.ne_of_lt (hmem₁ m hm)),
        cfg_congr (L := L₂) fun m hm => hcong m (Nat.ne_of_lt (hmem₂ m hm))]
    refine ⟨fun hs => ?_, fun hfr => ?_⟩
    · obtain ⟨e0, e1, e2⟩ := houter s hs
      unfold stageCurve
      rw [hlist, conf_append, e0, e1, e2, conf_cons, min_eq_left hs]
    · unfold stageCurve
      rw [hlist, hfr, mul_zero]
      have hadm : Adm 0 (cfg t (heights t h c s) L₁ ++ (t N, (0 : ℝ)) ::
          cfg t (heights t h c s) L₂) := by
        have hE : ∀ m ∈ actList t (N + 1), 0 ≤ (fun m => if m = N then (0 : ℝ) else
            heights t h c s m) m := fun m _ => by
          by_cases hm : m = N
          · simp [hm]
          · simp only [hm, ite_false]; exact heights_nonneg hc s m
        have := adm_cfg (pairwise_actList hd.inj (N + 1)) (fun m _ => hd.nonneg m) hE (a := 0)
        rw [hsplit', cfg_append, cfg_cons] at this
        simp only [ite_true] at this
        rwa [cfg_congr (L := L₁) (E := fun m => if m = N then (0 : ℝ) else heights t h c s m)
          (E' := heights t h c s) (fun m hm => by simp [Nat.ne_of_lt (hmem₁ m hm)]),
          cfg_congr (L := L₂) (E := fun m => if m = N then (0 : ℝ) else heights t h c s m)
          (E' := heights t h c s) (fun m hm => by simp [Nat.ne_of_lt (hmem₂ m hm)])] at this
      rw [conf_append_cons_zero hη hW hW0 le_rfl hτ0 hadm, ← cfg_append, ← hsplit]

omit hη hW hW0 hc in
theorem origTime_le_of_le_slitStart {N : ℕ} {s : ℝ} (hs : s ≤ slitStart t h N) :
    origTime t h s ≤ t N := by
  have := monotone_origTime hd.hpos hd.summable hd.inj hs
  rwa [origTime_eq_of_mem hd.hpos hd.summable hd.inj ⟨le_rfl, by linarith [hd.hpos N]⟩] at this

omit hη hW hW0 hc in
theorem le_origTime_of_le {N : ℕ} {s : ℝ} (hs : slitStart t h N + h N ≤ s) :
    t N ≤ origTime t h s := by
  have := monotone_origTime hd.hpos hd.summable hd.inj hs
  rwa [origTime_eq_of_mem hd.hpos hd.summable hd.inj ⟨by linarith [hd.hpos N], le_rfl⟩] at this

/-- **The new cut separates**: the stage-`(N+1)` curve before the slit interval `I_N` and after it
have no common point. -/
theorem stageCurve_succ_ne (N : ℕ) {s s' : ℝ} (hs0 : 0 ≤ s) (hsN : s ≤ slitStart t h N)
    (hs' : slitStart t h N + h N ≤ s') :
    stageCurve W t h c (N + 1) s ≠ stageCurve W t h c (N + 1) s' := by
  obtain ⟨L₁, L₂, hsplit, hsplit', hL₁, hL₂⟩ := exists_actList_split hd.inj N
  have hpw := pairwise_actList hd.inj (N + 1)
  rw [hsplit', List.pairwise_append] at hpw
  have hpw₁ := hpw.1
  have hpw₂ := (List.pairwise_cons.1 hpw.2.1).2
  have htN := hd.nonneg N
  have hτ0 := hd.origTime_nonneg hs0
  have hτN : origTime t h s ≤ t N := origTime_le_of_le_slitStart hd hsN
  have hτ'N : t N ≤ origTime t h s' := le_origTime_of_le hd hs'
  have hfr : slitFrac t h N s = 0 := (slitFrac_eq_zero_iff hd.hpos).2 hsN
  have hfr' : slitFrac t h N s' = 1 := (slitFrac_eq_one_iff hd.hpos).2 hs'
  have hadm₁ : Adm 0 (cfg t c L₁) := adm_cfg hpw₁ (fun m _ => hd.nonneg m) fun m _ => (hc m).le
  -- before the cut
  have hbefore : stageCurve W t h c (N + 1) s =
      conf W 0 (cfg t (heights t h c s) L₁) (origTime t h s) := by
    unfold stageCurve
    rw [hsplit', cfg_append, cfg_cons, show heights t h c s N = 0 by rw [heights, hfr, mul_zero]]
    have hadm : Adm 0 (cfg t (heights t h c s) L₁ ++ (t N, (0 : ℝ)) ::
        cfg t (heights t h c s) L₂) := by
      have := adm_cfg (pairwise_actList hd.inj (N + 1)) (fun m _ => hd.nonneg m)
        (fun m _ => heights_nonneg hc s m) (a := 0) (E := heights t h c s)
      rwa [hsplit', cfg_append, cfg_cons, show heights t h c s N = 0 by
        rw [heights, hfr, mul_zero]] at this
    rw [conf_append_cons_zero hη hW hW0 le_rfl hτ0 hadm, conf_append_of_forall hη hW hW0 le_rfl hτ0
      (by rw [← cfg_append]; exact adm_cfg_actList hc s (List.pairwise_append.2
        ⟨hpw₁, hpw₂, fun a ha b hb => (hL₁ a ha).trans (hL₂ b hb)⟩) fun m _ => hd.nonneg m)]
    · intro p hp
      obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp; exact hτN.trans (hL₂ m hm).le
    · intro p hp
      obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp; exact heights_of_gt hd (lt_of_le_of_lt hτN (hL₂ m hm))
  -- after the cut
  have hafter : stageCurve W t h c (N + 1) s' =
      layers W 0 (cfg t c L₁ ++ [(t N, c N)]) (t N)
        (conf W (t N) (cfg t (heights t h c s') L₂) (origTime t h s')) := by
    have hle : ∀ p ∈ cfg t c L₁, p.1 ≤ t N := fun p hp => by
      obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp; exact (hL₁ m hm).le
    obtain ⟨e1, e2⟩ := layers_congr_time (W := W) (a := 0) (fun p hp => (hle p hp).trans hτ'N) hle
    unfold stageCurve
    rw [hsplit', cfg_append, cfg_cons, cfg_congr (L := L₁) (E' := c)
      (fun m hm => heights_of_lt hd (lt_of_lt_of_le (hL₁ m hm) hτ'N)),
      show heights t h c s' N = c N by rw [heights, hfr', mul_one], conf_append, e1, e2,
      layers_append, conf_cons, min_eq_left hτ'N, layers_cons, layers_nil, min_self]
  rw [hbefore, hafter]
  exact conf_ne_layers hη hW hW0 le_rfl hpw₁ (fun m _ => hd.nonneg m) hL₁ (fun m _ => hc m) (hc N)
    (fun m _ => heights_nonneg hc s m) (fun m _ => heights_le hc s m)
    (fun m _ hlt => heights_of_lt hd hlt) (fun m _ hlt => heights_of_gt hd hlt) hτ0 hτN le_rfl
    (conf_mem_Hbar hη hW hW0 htN hτ'N
      (adm_cfg_actList hc s' hpw₂ fun m hm => (hL₂ m hm).le))

/-- **The new cut segment is simple**: the stage-`(N+1)` curve is injective on `I_N`. -/
theorem injOn_stageCurve_succ (N : ℕ) :
    InjOn (stageCurve W t h c (N + 1)) (Icc (slitStart t h N) (slitStart t h N + h N)) := by
  obtain ⟨Φ, z, -, -, -, -, hθ, -, -, -, hz0, -, hrep⟩ :=
    exists_stageCurve_succ_repr hη hW hW0 hd hc N
  have hcc : update c N (c N) = c := update_eq_self N c
  intro s hs s' hs' heq
  have hs0 : 0 ≤ s := (slitStart_nonneg hd.hpos hd.nonneg N).trans hs.1
  have hs'0 : 0 ≤ s' := (slitStart_nonneg hd.hpos hd.nonneg N).trans hs'.1
  have hτ := origTime_eq_of_mem hd.hpos hd.summable hd.inj hs
  have hτ' := origTime_eq_of_mem hd.hpos hd.summable hd.inj hs'
  have e1 := (hrep (c N) (hc N) s hs0).1 hτ.ge
  have e2 := (hrep (c N) (hc N) s' hs'0).1 hτ'.ge
  rw [hcc] at e1 e2
  rw [e1, e2, hz0 s hτ, hz0 s' hτ', add_zero, add_zero] at heq
  have := hθ _ _ (mul_nonneg (hc N).le (slitFrac_nonneg N s))
    (mul_nonneg (hc N).le (slitFrac_nonneg N s')) heq
  have hfr : slitFrac t h N s = slitFrac t h N s' := mul_left_cancel₀ (hc N).ne' this
  exact (strictMonoOn_slitFrac hd.hpos N).injOn hs hs' hfr

end Trace

end YuanSimpleApprox

end InteractingSLE
