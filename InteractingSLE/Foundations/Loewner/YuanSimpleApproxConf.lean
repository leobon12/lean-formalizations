import InteractingSLE.Foundations.Loewner.YuanSimpleApproxTrans

/-!
# Simple approximations of Loewner traces, III: inserting cuts in the charts of the trace

Yuan's construction ([Yua22] §4, `TraceTopology.tex` L467–L583) inserts a vertical "cut segment"
at a dense set of times and pushes the future of the curve up by the height of the segment. Here
every cut is inserted in the chart of the **original** trace at its time, so that all maps involved
are the transition maps `F̄_{a,b} = trMap W a b` of the original trace (continuous on `ℍ̄` by
[Yua22] Corollary 1.3). Yuan instead inserts each new cut in the chart of the current approximant;
the two constructions differ, but they have the same three properties that Yuan's proof uses.

A **configuration** is a list `L` of pairs `(τ, e)` (cut time, height), sorted by time. Its curve
point at time `t` is (with clamped times `τ' = min τ t`)

  `conf a L t = F̄_{a,τ₁'}(i e₁ + F̄_{τ₁',τ₂'}(i e₂ + ⋯ F̄_{τ_k',t}(0)))`,

the base point of the chart of time `t` (the tip, `0`), pushed up by `i eⱼ` in the chart of each
cut and transported back to the chart of time `a`. A cut with height `0` changes nothing
(`conf_append_cons_zero`); a cut after `t` with height `0` is invisible
(`conf_append_of_forall`).

## Main results

* `conf_mem_Hbar`, `layers_mem_H`, `layers_differentiableOn`, `layers_injOn`: values in `ℍ̄`; the
  layer maps are holomorphic and injective on `ℍ`;
* `conf_append`, `trMap_conf`, `conf_append_cons_zero`, `conf_append_of_forall`: algebra of
  configurations;
* `continuousOn_conf`: the curve point depends continuously on the time and the heights, as long
  as cuts after the current time have height `0`;
* `conf_ne_layers`: **separation by a cut**: a point produced before a cut of positive height
  differs from every point produced after it;
* `conf_mem_H`: at a cut time the curve point lies in `ℍ` in the chart of any earlier time.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace YuanSimpleApprox

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-! ### Definitions -/

/-- The **layer map** of a configuration: `w ↦ F̄_{a,τ₁'}(i e₁ + ⋯ F̄_{τ_{k-1}',τ_k'}(i e_k + w))`,
with `τⱼ' = min τⱼ t`. -/
def layers (W : ℝ → ℝ) : ℝ → List (ℝ × ℝ) → ℝ → ℂ → ℂ
  | _, [], _, w => w
  | a, p :: L, t, w => trMap W a (min p.1 t) ((p.2 : ℂ) * I + layers W (min p.1 t) L t w)

/-- The chart time after the last layer: `min τ_k t` (or `a` for the empty configuration). -/
def lastBase : ℝ → List (ℝ × ℝ) → ℝ → ℝ
  | a, [], _ => a
  | _, p :: L, t => lastBase (min p.1 t) L t

/-- The **curve point** of a configuration at time `t` in the chart of time `a`. -/
def conf (W : ℝ → ℝ) (a : ℝ) (L : List (ℝ × ℝ)) (t : ℝ) : ℂ :=
  layers W a L t (trMap W (lastBase a L t) t 0)

@[simp] theorem layers_nil (a t : ℝ) (w : ℂ) : layers W a [] t w = w := rfl

@[simp] theorem layers_cons (a t : ℝ) (p : ℝ × ℝ) (L : List (ℝ × ℝ)) (w : ℂ) :
    layers W a (p :: L) t w =
      trMap W a (min p.1 t) ((p.2 : ℂ) * I + layers W (min p.1 t) L t w) := rfl

@[simp] theorem lastBase_nil (a t : ℝ) : lastBase a [] t = a := rfl

@[simp] theorem lastBase_cons (a t : ℝ) (p : ℝ × ℝ) (L : List (ℝ × ℝ)) :
    lastBase a (p :: L) t = lastBase (min p.1 t) L t := rfl

@[simp] theorem conf_nil (a t : ℝ) : conf W a [] t = trMap W a t 0 := rfl

theorem conf_cons (a t : ℝ) (p : ℝ × ℝ) (L : List (ℝ × ℝ)) :
    conf W a (p :: L) t = trMap W a (min p.1 t) ((p.2 : ℂ) * I + conf W (min p.1 t) L t) := rfl

theorem layers_append (a t : ℝ) (L₁ L₂ : List (ℝ × ℝ)) (w : ℂ) :
    layers W a (L₁ ++ L₂) t w = layers W a L₁ t (layers W (lastBase a L₁ t) L₂ t w) := by
  induction L₁ generalizing a with
  | nil => rfl
  | cons p L ih => simp only [List.cons_append, layers_cons, lastBase_cons, ih]

theorem lastBase_append (a t : ℝ) (L₁ L₂ : List (ℝ × ℝ)) :
    lastBase a (L₁ ++ L₂) t = lastBase (lastBase a L₁ t) L₂ t := by
  induction L₁ generalizing a with
  | nil => rfl
  | cons p L ih => simp only [List.cons_append, lastBase_cons, ih]

theorem conf_append (a t : ℝ) (L₁ L₂ : List (ℝ × ℝ)) :
    conf W a (L₁ ++ L₂) t = layers W a L₁ t (conf W (lastBase a L₁ t) L₂ t) := by
  simp only [conf, layers_append, lastBase_append]

/-! ### Sorted configurations -/

/-- A configuration is **admissible from `a`**: times strictly increasing, all at least `a`,
heights nonnegative. -/
def Adm (a : ℝ) (L : List (ℝ × ℝ)) : Prop :=
  L.Pairwise (fun p q => p.1 < q.1) ∧ (∀ p ∈ L, a ≤ p.1) ∧ ∀ p ∈ L, 0 ≤ p.2

theorem Adm.tail {a : ℝ} {p : ℝ × ℝ} {L : List (ℝ × ℝ)} (h : Adm a (p :: L)) {b : ℝ}
    (hb : b ≤ p.1) : Adm b L := by
  obtain ⟨hs, hge, hpos⟩ := h
  rw [List.pairwise_cons] at hs
  exact ⟨hs.2, fun q hq => hb.trans (hs.1 q hq).le, fun q hq => hpos q (List.mem_cons_of_mem _ hq)⟩

theorem Adm.mono {a b : ℝ} {L : List (ℝ × ℝ)} (h : Adm a L) (hba : b ≤ a) : Adm b L :=
  ⟨h.1, fun p hp => hba.trans (h.2.1 p hp), h.2.2⟩

theorem Adm.append_left {a : ℝ} {L₁ L₂ : List (ℝ × ℝ)} (h : Adm a (L₁ ++ L₂)) : Adm a L₁ :=
  ⟨(List.pairwise_append.1 h.1).1, fun p hp => h.2.1 p (List.mem_append_left _ hp),
    fun p hp => h.2.2 p (List.mem_append_left _ hp)⟩

theorem le_lastBase {a t : ℝ} (hat : a ≤ t) {L : List (ℝ × ℝ)} (hL : Adm a L) :
    a ≤ lastBase a L t := by
  induction L generalizing a with
  | nil => exact le_rfl
  | cons p L ih =>
    have h1 : a ≤ min p.1 t := le_min (hL.2.1 p (List.mem_cons_self ..)) hat
    exact h1.trans (ih (min_le_right _ _) (hL.tail (min_le_left _ _)))

theorem lastBase_le {a t : ℝ} (hat : a ≤ t) (L : List (ℝ × ℝ)) : lastBase a L t ≤ t := by
  induction L generalizing a with
  | nil => exact hat
  | cons p L ih => exact ih (min_le_right _ _)

theorem lastBase_le_of_forall {a t σ : ℝ} (haσ : a ≤ σ) {L : List (ℝ × ℝ)}
    (hL : ∀ p ∈ L, p.1 ≤ σ) : lastBase a L t ≤ σ := by
  induction L generalizing a with
  | nil => exact haσ
  | cons p L ih =>
    exact ih ((min_le_left _ _).trans (hL p (List.mem_cons_self ..)))
      fun q hq => hL q (List.mem_cons_of_mem _ hq)

theorem lastBase_nonneg {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) {L : List (ℝ × ℝ)} (hL : Adm a L) :
    0 ≤ lastBase a L t :=
  ha.trans (le_lastBase hat hL)

/-! ### Pushing up -/

theorem im_ofReal_mul_I_add (e : ℝ) (w : ℂ) : ((e : ℂ) * I + w).im = e + w.im := by simp

theorem add_mem_Hbar {e : ℝ} (he : 0 ≤ e) {w : ℂ} (hw : w ∈ Hbar) : (e : ℂ) * I + w ∈ Hbar :=
  show 0 ≤ ((e : ℂ) * I + w).im by
    rw [im_ofReal_mul_I_add]; exact add_nonneg he hw

theorem add_mem_H_of_pos {e : ℝ} (he : 0 < e) {w : ℂ} (hw : w ∈ Hbar) : (e : ℂ) * I + w ∈ H :=
  show 0 < ((e : ℂ) * I + w).im by
    rw [im_ofReal_mul_I_add]; exact add_pos_of_pos_of_nonneg he hw

theorem add_mem_H {e : ℝ} (he : 0 ≤ e) {w : ℂ} (hw : w ∈ H) : (e : ℂ) * I + w ∈ H :=
  show 0 < ((e : ℂ) * I + w).im by
    rw [im_ofReal_mul_I_add]; exact add_pos_of_nonneg_of_pos he hw

/-! ### Values, holomorphy and injectivity of the layer maps -/

section Trace

variable (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
include hη hW hW0

theorem layers_mem_Hbar {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) {L : List (ℝ × ℝ)} (hL : Adm a L)
    {w : ℂ} (hw : w ∈ Hbar) : layers W a L t w ∈ Hbar := by
  induction L generalizing a with
  | nil => exact hw
  | cons p L ih =>
    have hm : a ≤ min p.1 t := le_min (hL.2.1 p (List.mem_cons_self ..)) hat
    have h1 := ih (ha.trans hm) (min_le_right _ _) (hL.tail (min_le_left _ _))
    exact trMap_mapsTo_Hbar hη hW hW0 ha hm (add_mem_Hbar (hL.2.2 p (List.mem_cons_self ..)) h1)

omit hη hW0 in
theorem layers_mem_H {a t : ℝ} (hat : a ≤ t) {L : List (ℝ × ℝ)} (hL : Adm a L)
    {w : ℂ} (hw : w ∈ H) : layers W a L t w ∈ H := by
  induction L generalizing a with
  | nil => exact hw
  | cons p L ih =>
    have hm : a ≤ min p.1 t := le_min (hL.2.1 p (List.mem_cons_self ..)) hat
    have h1 := ih (min_le_right _ _) (hL.tail (min_le_left _ _))
    exact trMap_mem_H hW hm (add_mem_H (hL.2.2 p (List.mem_cons_self ..)) h1)

theorem conf_mem_Hbar {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) {L : List (ℝ × ℝ)} (hL : Adm a L) :
    conf W a L t ∈ Hbar :=
  layers_mem_Hbar hη hW hW0 ha hat hL
    (trMap_zero_mem_Hbar hη hW hW0 (lastBase_nonneg ha hat hL) (lastBase_le hat L))

theorem layers_differentiableOn {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) {L : List (ℝ × ℝ)}
    (hL : Adm a L) : DifferentiableOn ℂ (layers W a L t) H := by
  induction L generalizing a with
  | nil => exact differentiableOn_id
  | cons p L ih =>
    have hm : a ≤ min p.1 t := le_min (hL.2.1 p (List.mem_cons_self ..)) hat
    have hL' : Adm (min p.1 t) L := hL.tail (min_le_left _ _)
    show DifferentiableOn ℂ
      (fun w => trMap W a (min p.1 t) ((p.2 : ℂ) * I + layers W (min p.1 t) L t w)) H
    refine (trMap_differentiableOn hη hW hW0 ha hm).comp
      ((differentiableOn_const _).add (ih (ha.trans hm) (min_le_right _ _) hL')) ?_
    exact fun w hw => add_mem_H (hL.2.2 p (List.mem_cons_self ..))
      (layers_mem_H hW (min_le_right _ _) hL' hw)

theorem layers_injOn {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) {L : List (ℝ × ℝ)} (hL : Adm a L) :
    InjOn (layers W a L t) H := by
  induction L generalizing a with
  | nil => exact injOn_id _
  | cons p L ih =>
    have hm : a ≤ min p.1 t := le_min (hL.2.1 p (List.mem_cons_self ..)) hat
    have hL' : Adm (min p.1 t) L := hL.tail (min_le_left _ _)
    show InjOn (fun w => trMap W a (min p.1 t) ((p.2 : ℂ) * I + layers W (min p.1 t) L t w)) H
    have hmaps : MapsTo (fun w => (p.2 : ℂ) * I + layers W (min p.1 t) L t w) H H :=
      fun w hw => add_mem_H (hL.2.2 p (List.mem_cons_self ..))
        (layers_mem_H hW (min_le_right _ _) hL' hw)
    refine (trMap_injOn hη hW hW0 ha hm).comp ?_ hmaps
    intro w hw w' hw' heq
    exact ih (ha.trans hm) (min_le_right _ _) hL' hw hw' (add_left_cancel heq)

theorem layers_continuousOn {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) {L : List (ℝ × ℝ)}
    (hL : Adm a L) : ContinuousOn (layers W a L t) Hbar := by
  induction L generalizing a with
  | nil => exact continuousOn_id
  | cons p L ih =>
    have hm : a ≤ min p.1 t := le_min (hL.2.1 p (List.mem_cons_self ..)) hat
    have hL' : Adm (min p.1 t) L := hL.tail (min_le_left _ _)
    show ContinuousOn
      (fun w => trMap W a (min p.1 t) ((p.2 : ℂ) * I + layers W (min p.1 t) L t w)) Hbar
    refine (trMap_continuousOn hη hW hW0 ha hm).comp
      (continuousOn_const.add (ih (ha.trans hm) (min_le_right _ _) hL')) ?_
    exact fun w hw => add_mem_Hbar (hL.2.2 p (List.mem_cons_self ..))
      (layers_mem_Hbar hη hW hW0 (ha.trans hm) (min_le_right _ _) hL' hw)

/-! ### Algebra of configurations -/

/-- Transporting a curve point to an earlier chart before the first cut. -/
theorem trMap_conf {b m t : ℝ} (hb : 0 ≤ b) (hbm : b ≤ m) (hmt : m ≤ t) {L : List (ℝ × ℝ)}
    (hL : Adm m L) : trMap W b m (conf W m L t) = conf W b L t := by
  cases L with
  | nil => exact trMap_trMap hη hW hW0 hb hbm hmt zero_mem_Hbar
  | cons p L =>
    have hm : m ≤ min p.1 t := le_min (hL.2.1 p (List.mem_cons_self ..)) hmt
    rw [conf_cons, conf_cons]
    refine trMap_trMap hη hW hW0 hb hbm hm (add_mem_Hbar (hL.2.2 p (List.mem_cons_self ..)) ?_)
    exact conf_mem_Hbar hη hW hW0 (hb.trans (hbm.trans hm)) (min_le_right _ _)
      (hL.tail (min_le_left _ _))

/-- A cut of height `0` changes nothing. -/
theorem conf_cons_zero {b t σ : ℝ} (hb : 0 ≤ b) (hbt : b ≤ t) {L : List (ℝ × ℝ)}
    (hL : Adm b ((σ, 0) :: L)) : conf W b ((σ, 0) :: L) t = conf W b L t := by
  rw [conf_cons]
  simp only [Complex.ofReal_zero, zero_mul, zero_add]
  have hbσ : b ≤ σ := hL.2.1 (σ, 0) (List.mem_cons_self ..)
  exact trMap_conf hη hW hW0 hb (le_min hbσ hbt) (min_le_right _ _) (hL.tail (min_le_left _ _))

theorem conf_append_cons_zero {a t σ : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) {L₁ L₂ : List (ℝ × ℝ)}
    (hL : Adm a (L₁ ++ (σ, 0) :: L₂)) :
    conf W a (L₁ ++ (σ, 0) :: L₂) t = conf W a (L₁ ++ L₂) t := by
  rw [conf_append, conf_append]
  congr 1
  have hL₁ : Adm a L₁ := hL.append_left
  have hpw := List.pairwise_append.1 hL.1
  have hb0 := lastBase_nonneg ha hat hL₁
  have haσ : a ≤ σ := hL.2.1 (σ, 0) (List.mem_append_right _ (List.mem_cons_self ..))
  have hbσ : lastBase a L₁ t ≤ σ :=
    lastBase_le_of_forall haσ fun p hp => (hpw.2.2 p hp (σ, 0) (List.mem_cons_self ..)).le
  refine conf_cons_zero hη hW hW0 hb0 (lastBase_le hat L₁) ⟨hpw.2.1, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact hbσ
    · exact hbσ.trans ((List.pairwise_cons.1 hpw.2.1).1 p hp').le
  · exact fun p hp => hL.2.2 p (List.mem_append_right _ hp)

omit hη hW0 in
theorem conf_eq_zero {t : ℝ} {L : List (ℝ × ℝ)} (hL : ∀ p ∈ L, t ≤ p.1)
    (hz : ∀ p ∈ L, p.2 = 0) : conf W t L t = 0 := by
  induction L with
  | nil => exact trMap_self hW t zero_mem_Hbar
  | cons p L ih =>
    rw [conf_cons, min_eq_right (hL p (List.mem_cons_self ..)),
      ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
        (fun q hq => hz q (List.mem_cons_of_mem _ hq)),
      hz p (List.mem_cons_self ..)]
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    exact trMap_self hW t zero_mem_Hbar

/-- Cuts after the current time with height `0` are invisible. -/
theorem conf_append_of_forall {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) {L₁ L₂ : List (ℝ × ℝ)}
    (hL : Adm a (L₁ ++ L₂)) (hfut : ∀ p ∈ L₂, t ≤ p.1) (hz : ∀ p ∈ L₂, p.2 = 0) :
    conf W a (L₁ ++ L₂) t = conf W a L₁ t := by
  have hL₁ : Adm a L₁ := hL.append_left
  have hb0 := lastBase_nonneg ha hat hL₁
  have hbt := lastBase_le hat L₁
  conv_rhs => rw [← List.append_nil L₁]
  rw [conf_append, conf_append]
  congr 1
  have hL₂ : Adm t L₂ := ⟨(List.pairwise_append.1 hL.1).2.1, hfut,
    fun p hp => hL.2.2 p (List.mem_append_right _ hp)⟩
  rw [← trMap_conf hη hW hW0 hb0 hbt le_rfl hL₂, conf_eq_zero hW hfut hz]
  rfl

omit hη hW hW0 in
/-- When every cut is before both times, the layer maps and the last base do not see the time. -/
theorem layers_congr_time {a t t' : ℝ} {L : List (ℝ × ℝ)} (ht : ∀ p ∈ L, p.1 ≤ t)
    (ht' : ∀ p ∈ L, p.1 ≤ t') :
    layers W a L t = layers W a L t' ∧ lastBase a L t = lastBase a L t' := by
  induction L generalizing a with
  | nil => exact ⟨rfl, rfl⟩
  | cons p L ih =>
    have h1 : min p.1 t = p.1 := min_eq_left (ht p (List.mem_cons_self ..))
    have h2 : min p.1 t' = p.1 := min_eq_left (ht' p (List.mem_cons_self ..))
    obtain ⟨ih1, ih2⟩ := ih (a := p.1) (fun q hq => ht q (List.mem_cons_of_mem _ hq))
      (fun q hq => ht' q (List.mem_cons_of_mem _ hq))
    refine ⟨?_, ?_⟩
    · funext w
      simp only [layers_cons, h1, h2, ih1]
    · simp only [lastBase_cons, h1, h2, ih2]

end Trace

/-! ### Configurations indexed by cuts -/

/-- The configuration of the cuts `ns` with times `tt` and heights `E`. -/
def cfg (tt E : ℕ → ℝ) (ns : List ℕ) : List (ℝ × ℝ) := ns.map fun n => (tt n, E n)

theorem mem_cfg {tt E : ℕ → ℝ} {ns : List ℕ} {p : ℝ × ℝ} :
    p ∈ cfg tt E ns ↔ ∃ n ∈ ns, (tt n, E n) = p := List.mem_map

theorem adm_cfg {a : ℝ} {tt E : ℕ → ℝ} {ns : List ℕ}
    (hsort : ns.Pairwise (fun i j => tt i < tt j)) (hge : ∀ n ∈ ns, a ≤ tt n)
    (hE : ∀ n ∈ ns, 0 ≤ E n) : Adm a (cfg tt E ns) := by
  refine ⟨List.pairwise_map.2 hsort, fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨n, hn, rfl⟩ := mem_cfg.1 hp; exact hge n hn
  · obtain ⟨n, hn, rfl⟩ := mem_cfg.1 hp; exact hE n hn

theorem conf_cfg_cons (a t : ℝ) (tt E : ℕ → ℝ) (n : ℕ) (ns : List ℕ) :
    conf W a (cfg tt E (n :: ns)) t =
      trMap W a (min (tt n) t) ((E n : ℂ) * I + conf W (min (tt n) t) (cfg tt E ns) t) := rfl

theorem layers_cfg_cons_append (a t : ℝ) (tt E : ℕ → ℝ) (n : ℕ) (ns : List ℕ)
    (L : List (ℝ × ℝ)) (w : ℂ) :
    layers W a (cfg tt E (n :: ns) ++ L) t w =
      trMap W a (min (tt n) t) ((E n : ℂ) * I + layers W (min (tt n) t) (cfg tt E ns ++ L) t w) :=
  rfl

section Trace

variable (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
include hη hW hW0

/-- **Separation by a cut** (the cut segments of [Yua22] §4 separate the past from the future).
Let `σ` be a cut of height `cσ > 0` after the cuts `ns` (heights `c n > 0`). A curve point at a
time `t ≤ σ` with heights `E` (full for the cuts before `t`, zero for those after `t`, partial
at `t`) differs from every point `layers … t' Y` produced after the cut `σ` (full heights,
`Y ∈ ℍ̄`). -/
theorem conf_ne_layers {a σ cσ t t' : ℝ} (ha : 0 ≤ a) {tt E c : ℕ → ℝ} {ns : List ℕ}
    (hsort : ns.Pairwise (fun i j => tt i < tt j)) (hge : ∀ n ∈ ns, a ≤ tt n)
    (hlt : ∀ n ∈ ns, tt n < σ) (hc : ∀ n ∈ ns, 0 < c n) (hcσ : 0 < cσ)
    (hE0 : ∀ n ∈ ns, 0 ≤ E n) (hEc : ∀ n ∈ ns, E n ≤ c n)
    (hEpast : ∀ n ∈ ns, tt n < t → E n = c n) (hEfut : ∀ n ∈ ns, t < tt n → E n = 0)
    (hat : a ≤ t) (htσ : t ≤ σ) (hσt' : σ ≤ t') {Y : ℂ} (hY : Y ∈ Hbar) :
    conf W a (cfg tt E ns) t ≠ layers W a (cfg tt c ns ++ [(σ, cσ)]) t' Y := by
  induction ns generalizing a with
  | nil =>
    show trMap W a t 0 ≠ trMap W a (min σ t') ((cσ : ℂ) * I + Y)
    rw [min_eq_left hσt']
    intro heq
    exact trMap_zero_notMem_image hη hW hW0 ha hat htσ ⟨_, add_mem_H_of_pos hcσ hY, heq.symm⟩
  | cons n ns ih =>
    have hs := List.pairwise_cons.1 hsort
    have hmem : n ∈ n :: ns := List.mem_cons_self ..
    have hτa : a ≤ tt n := hge n hmem
    have hτσ : tt n < σ := hlt n hmem
    have hτ0 : 0 ≤ tt n := ha.trans hτa
    have hgt : ∀ m ∈ ns, tt n < tt m := hs.1
    have hsub : ∀ m ∈ ns, m ∈ n :: ns := fun m hm => List.mem_cons_of_mem _ hm
    rw [conf_cfg_cons, layers_cfg_cons_append, min_eq_left (hτσ.le.trans hσt')]
    -- the point after the cut, in the chart of `tt n`
    have hadm : Adm (tt n) (cfg tt c ns ++ [(σ, cσ)]) := by
      refine ⟨List.pairwise_append.2 ⟨List.pairwise_map.2 hs.2, List.pairwise_singleton _ _,
        fun p hp q hq => ?_⟩, fun p hp => ?_, fun p hp => ?_⟩
      · obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp
        rw [List.mem_singleton] at hq; rw [hq]; exact hlt m (hsub m hm)
      · rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp; exact (hgt m hm).le
        · rw [List.mem_singleton] at hp; rw [hp]; exact hτσ.le
      · rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp; exact (hc m (hsub m hm)).le
        · rw [List.mem_singleton] at hp; rw [hp]; exact hcσ.le
    have hV : layers W (tt n) (cfg tt c ns ++ [(σ, cσ)]) t' Y ∈ Hbar :=
      layers_mem_Hbar hη hW hW0 hτ0 (hτσ.le.trans hσt') hadm hY
    have hVH := add_mem_H_of_pos (hc n hmem) hV
    rcases lt_or_ge t (tt n) with htτ | hτt
    · -- `t` before the cut `n`: the point is the tip `F̄_{a,t}(0)`
      have hEn : E n = 0 := hEfut n hmem htτ
      have h0 : conf W t (cfg tt E ns) t = 0 := by
        refine conf_eq_zero hW (fun p hp => ?_) (fun p hp => ?_)
        · obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp; exact (htτ.trans (hgt m hm)).le
        · obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp; exact hEfut m (hsub m hm) (htτ.trans (hgt m hm))
      rw [min_eq_right htτ.le, h0, hEn]
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      intro heq
      exact trMap_zero_notMem_image hη hW hW0 ha hat htτ.le ⟨_, hVH, heq.symm⟩
    · rw [min_eq_left hτt]
      have hadmE : Adm (tt n) (cfg tt E ns) :=
        adm_cfg hs.2 (fun m hm => (hgt m hm).le) (fun m hm => hE0 m (hsub m hm))
      have hU : (E n : ℂ) * I + conf W (tt n) (cfg tt E ns) t ∈ Hbar :=
        add_mem_Hbar (hE0 n hmem) (conf_mem_Hbar hη hW hW0 hτ0 hτt hadmE)
      intro heq
      by_cases hUH : (E n : ℂ) * I + conf W (tt n) (cfg tt E ns) t ∈ H
      · have hUV := trMap_injOn hη hW hW0 ha hτa hUH hVH heq
        rcases (hEc n hmem).lt_or_eq with hEn | hEn
        · -- partial height: `t` is the cut time and the point is on the cut segment
          have htτ : t = tt n := le_antisymm (not_lt.1 fun h => hEn.ne (hEpast n hmem h)) hτt
          have h0 : conf W (tt n) (cfg tt E ns) t = 0 := by
            rw [htτ]
            refine conf_eq_zero hW (fun p hp => ?_) (fun p hp => ?_)
            · obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp; exact (hgt m hm).le
            · obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp
              exact hEfut m (hsub m hm) (htτ ▸ hgt m hm)
          rw [h0] at hUV
          have him := congrArg Complex.im hUV
          rw [im_ofReal_mul_I_add, im_ofReal_mul_I_add, Complex.zero_im] at him
          have : (0 : ℝ) ≤ (layers W (tt n) (cfg tt c ns ++ [(σ, cσ)]) t' Y).im := hV
          linarith
        · rw [hEn] at hUV
          exact ih hτ0 hs.2 (fun m hm => (hgt m hm).le) (fun m hm => hlt m (hsub m hm))
            (fun m hm => hc m (hsub m hm)) (fun m hm => hE0 m (hsub m hm))
            (fun m hm => hEc m (hsub m hm)) (fun m hm => hEpast m (hsub m hm))
            (fun m hm => hEfut m (hsub m hm)) hτt (add_left_cancel hUV)
      · have him : ((E n : ℂ) * I + conf W (tt n) (cfg tt E ns) t).im = 0 :=
          le_antisymm (not_lt.1 hUH) hU
        exact (trMap_fiber_hyps hη hW hW0 ha hτa).2.2.2 _ him ⟨_, hVH, heq.symm⟩

/-- At a cut time `t > a` the curve point lies in `ℍ` in the chart of `a`, provided the cuts before
`t` have positive height and those after `t` height `0`. -/
theorem conf_mem_H {a t : ℝ} (hcut : IsCutTime η t) (ha : 0 ≤ a) (hat : a < t)
    {L : List (ℝ × ℝ)} (hL : Adm a L) (hpast : ∀ p ∈ L, p.1 < t → 0 < p.2)
    (hfut : ∀ p ∈ L, t < p.1 → p.2 = 0) : conf W a L t ∈ H := by
  cases L with
  | nil => exact hcut.trMap_zero_mem_H hη hW hW0 ha hat
  | cons p L =>
    have hmem : p ∈ p :: L := List.mem_cons_self ..
    have hpa : a ≤ p.1 := hL.2.1 p hmem
    rw [conf_cons]
    rcases lt_or_ge p.1 t with hpt | htp
    · rw [min_eq_left hpt.le]
      exact trMap_mem_H hW hpa (add_mem_H_of_pos (hpast p hmem hpt)
        (conf_mem_Hbar hη hW hW0 (ha.trans hpa) hpt.le (hL.tail le_rfl)))
    · rw [min_eq_right htp]
      have hgt : ∀ q ∈ L, p.1 < q.1 := (List.pairwise_cons.1 hL.1).1
      have h0 : conf W t L t = 0 :=
        conf_eq_zero hW (fun q hq => htp.trans (hgt q hq).le)
          (fun q hq => hfut q (List.mem_cons_of_mem _ hq) (lt_of_le_of_lt htp (hgt q hq)))
      rw [h0, add_zero]
      rcases (hL.2.2 p hmem).lt_or_eq with hp | hp
      · exact trMap_mem_H hW hat.le (show 0 < ((p.2 : ℂ) * I).im by simpa using hp)
      · rw [← hp, Complex.ofReal_zero, zero_mul]
        exact hcut.trMap_zero_mem_H hη hW hW0 ha hat

/-- The tip in the chart of `a` along a time path. -/
theorem continuousOn_trMap_zero_comp {a : ℝ} (ha : 0 ≤ a) {T : ℝ → ℝ} {U : Set ℝ}
    (hT : ContinuousOn T U) (hTa : ∀ s ∈ U, a ≤ T s) :
    ContinuousOn (fun s => trMap W a (T s) 0) U :=
  (continuousOn_trMap_zero hη hW hW0 ha).comp hT fun s hs => hTa s hs

/-- On a cut segment: if the height `E n` vanishes whenever the time `T` is before the cut time
`tt n`, then `s ↦ F̄_{a, T s}(i E n s)` is continuous where `T ≤ tt n`. -/
theorem continuousOn_trMap_segment {a τ : ℝ} (ha : 0 ≤ a) (haτ : a ≤ τ) {e : ℝ → ℝ}
    (he : Continuous e) (he0 : ∀ s, 0 ≤ e s) {T : ℝ → ℝ} {U : Set ℝ} (hUc : IsClosed U)
    (hT : ContinuousOn T U) (hTa : ∀ s ∈ U, a ≤ T s) (hTτ : ∀ s ∈ U, T s ≤ τ)
    (hfut : ∀ s ∈ U, T s < τ → e s = 0) :
    ContinuousOn (fun s => trMap W a (T s) ((e s : ℂ) * I)) U := by
  have hg0 := continuousOn_trMap_zero_comp hη hW hW0 ha hT hTa
  have hgτ : ContinuousOn (fun s => trMap W a τ ((e s : ℂ) * I)) U :=
    (trMap_continuousOn hη hW hW0 ha haτ).comp
      ((Complex.continuous_ofReal.comp he).mul continuous_const).continuousOn
      fun s _ => add_zero ((e s : ℂ) * I) ▸ add_mem_Hbar (he0 s) zero_mem_Hbar
  intro s₀ hs₀
  set A := U ∩ {s | T s < τ} with hA
  set B := U ∩ {s | T s = τ} with hB
  have hU : U = A ∪ B := by
    ext s
    constructor
    · intro hs
      rcases (hTτ s hs).lt_or_eq with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have heqA : ∀ s ∈ A, trMap W a (T s) ((e s : ℂ) * I) = trMap W a (T s) 0 := fun s hs => by
    rw [hfut s hs.1 hs.2, Complex.ofReal_zero, zero_mul]
  have heqB : ∀ s ∈ B, trMap W a (T s) ((e s : ℂ) * I) = trMap W a τ ((e s : ℂ) * I) :=
    fun s hs => by rw [hs.2]
  rw [hU]
  refine ContinuousWithinAt.union ?_ ?_
  · by_cases hcl : s₀ ∈ closure A
    · -- the height vanishes at `s₀`
      have hcl' : s₀ ∈ closure {s | e s = 0} :=
        closure_mono (fun s hs => hfut s hs.1 hs.2) hcl
      rw [(isClosed_eq he continuous_const).closure_eq] at hcl'
      have hval : trMap W a (T s₀) ((e s₀ : ℂ) * I) = trMap W a (T s₀) 0 := by
        rw [show e s₀ = 0 from hcl', Complex.ofReal_zero, zero_mul]
      refine ((hg0 s₀ hs₀).mono inter_subset_left).congr (fun s hs => heqA s hs) hval
    · exact continuousWithinAt_of_notMem_closure hcl
  · by_cases hs₀B : s₀ ∈ B
    · exact ((hgτ s₀ hs₀).mono inter_subset_left).congr (fun s hs => heqB s hs) (heqB s₀ hs₀B)
    · have hBc : IsClosed B := hT.preimage_isClosed_of_isClosed hUc isClosed_singleton
      exact continuousWithinAt_of_notMem_closure (by rwa [hBc.closure_eq])

/-- **Continuity of the curve point** in the time `T s` and the heights `E n s`, as long as cuts
after the current time have height `0`. -/
theorem continuousOn_conf {a : ℝ} (ha : 0 ≤ a) {tt : ℕ → ℝ} {E : ℕ → ℝ → ℝ} {ns : List ℕ}
    (hsort : ns.Pairwise (fun i j => tt i < tt j)) (hge : ∀ n ∈ ns, a ≤ tt n)
    (hE : ∀ n ∈ ns, Continuous (E n)) (hE0 : ∀ n ∈ ns, ∀ s, 0 ≤ E n s)
    {T : ℝ → ℝ} {U : Set ℝ} (hUc : IsClosed U) (hT : ContinuousOn T U)
    (hTa : ∀ s ∈ U, a ≤ T s) (hfut : ∀ n ∈ ns, ∀ s ∈ U, T s < tt n → E n s = 0) :
    ContinuousOn (fun s => conf W a (cfg tt (fun n => E n s) ns) (T s)) U := by
  induction ns generalizing a U with
  | nil => exact continuousOn_trMap_zero_comp hη hW hW0 ha hT hTa
  | cons n ns ih =>
    have hs := List.pairwise_cons.1 hsort
    have hmem : n ∈ n :: ns := List.mem_cons_self ..
    have hsub : ∀ m ∈ ns, m ∈ n :: ns := fun m hm => List.mem_cons_of_mem _ hm
    have hgt : ∀ m ∈ ns, tt n < tt m := hs.1
    have hτa : a ≤ tt n := hge n hmem
    have hτ0 : 0 ≤ tt n := ha.trans hτa
    set U₁ := U ∩ T ⁻¹' Iic (tt n) with hU₁
    set U₂ := U ∩ T ⁻¹' Ici (tt n) with hU₂
    have hU₁c : IsClosed U₁ := hT.preimage_isClosed_of_isClosed hUc isClosed_Iic
    have hU₂c : IsClosed U₂ := hT.preimage_isClosed_of_isClosed hUc isClosed_Ici
    have hUU : U = U₁ ∪ U₂ := by
      ext s
      refine ⟨fun hs => ?_, fun hs => hs.elim (fun h => h.1) (fun h => h.1)⟩
      rcases le_total (T s) (tt n) with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, h⟩
    have hfeq : ∀ s, conf W a (cfg tt (fun n => E n s) (n :: ns)) (T s) =
        trMap W a (min (tt n) (T s)) ((E n s : ℂ) * I +
          conf W (min (tt n) (T s)) (cfg tt (fun n => E n s) ns) (T s)) := fun s => rfl
    rw [hUU]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hU₁c hU₂c
    · -- before (or at) the cut `n`: the later cuts are invisible
      have hcongr : ∀ s ∈ U₁, conf W a (cfg tt (fun n => E n s) (n :: ns)) (T s) =
          trMap W a (T s) ((E n s : ℂ) * I) := by
        intro s hs
        rw [hfeq, min_eq_right hs.2]
        have h0 : conf W (T s) (cfg tt (fun n => E n s) ns) (T s) = 0 := by
          refine conf_eq_zero hW (fun p hp => ?_) (fun p hp => ?_)
          · obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp
            exact (show T s ≤ tt n from hs.2).trans (hgt m hm).le
          · obtain ⟨m, hm, rfl⟩ := mem_cfg.1 hp
            exact hfut m (hsub m hm) s hs.1
              (lt_of_le_of_lt (show T s ≤ tt n from hs.2) (hgt m hm))
        rw [h0, add_zero]
      refine (continuousOn_trMap_segment hη hW hW0 ha hτa (hE n hmem) (hE0 n hmem) hU₁c
        (hT.mono inter_subset_left) (fun s hs => hTa s hs.1) (fun s hs => hs.2)
        (fun s hs h => hfut n hmem s hs.1 h)).congr hcongr
    · -- after the cut `n`
      have hcongr : ∀ s ∈ U₂, conf W a (cfg tt (fun n => E n s) (n :: ns)) (T s) =
          trMap W a (tt n)
            ((E n s : ℂ) * I + conf W (tt n) (cfg tt (fun n => E n s) ns) (T s)) := by
        intro s hs
        rw [hfeq, min_eq_left hs.2]
      have hin : ContinuousOn (fun s => conf W (tt n) (cfg tt (fun n => E n s) ns) (T s)) U₂ :=
        ih hτ0 hs.2 (fun m hm => (hgt m hm).le) (fun m hm => hE m (hsub m hm))
          (fun m hm => hE0 m (hsub m hm)) hU₂c (hT.mono inter_subset_left)
          (fun s hs => hs.2) (fun m hm s hs => hfut m (hsub m hm) s hs.1)
      refine ((trMap_continuousOn hη hW hW0 ha hτa).comp
        (((Complex.continuous_ofReal.comp (hE n hmem)).mul continuous_const).continuousOn.add hin)
        fun s hs => ?_).congr hcongr
      exact add_mem_Hbar (hE0 n hmem s) (conf_mem_Hbar hη hW hW0 hτ0 hs.2
        (adm_cfg (List.pairwise_cons.1 hsort).2 (fun m hm => (hgt m hm).le)
          (fun m hm => hE0 m (hsub m hm) s)))

end Trace

end YuanSimpleApprox

end InteractingSLE
