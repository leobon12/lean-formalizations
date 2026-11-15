/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoDetourIntervals
import InteractingSLE.Spec.Sec5.Prop51HGateWind

/-!
# Completed excursion crosscuts in the counterflow chart and their closed loops

Packet PROVE-PROP51H-TOPO2 (ruling R71; Astra's follow-up 4, §1.7 "Exterior intervals are proper crosscuts").
Let `η` be a proper arc, `D = ℍ ∖ R(K_s)` the complement of the counterflow hull and `Ψ = revChart w s` its chart.
Every excursion of `η` in `D` (a component `C` of `excursionTimes η w s`, bounded or terminal) completes to a
**chart crosscut** `ExcursionChartCut η w s C`: a path `cut` on `[0, 1]` with real ends `start`, `finish`, equal to
`Ψ ∘ η ∘ time` on `(0, 1)` for an increasing reparametrization `time` of `C`. Under the western-end property
(`Prop51HTopo.HasWesternExcursionEnds`, supplied by the rational barriers) the finishing gate is negative.

The **closed loop** `ExcursionChartCut.loop` runs along `cut` and back along the real segment from `finish` to
`start`; its winding numbers are the bookkeeping device of the separation argument.

* `nonempty_excursionChartCut`: every excursion component has a completed chart crosscut (the terminal component
  through the reparametrization `a + t/(1 − t)`);
* `exists_tendsto_revChart_start`: the incoming prime-end limit of an excursion (also at the seed);
* `ExcursionChartCut.injOn_cut`, `image_cut_subset_closure`, `loop_mem`: injectivity in the interior, the range in
  the closure of the chart flow set, and the shape of the loop.

Deterministic; nothing here replaces a source theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Prop51HGate

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G Prop51HTopo

/-- **A completed excursion crosscut in the counterflow chart.** `cut` is continuous on `[0, 1]` with real ends
`start` and `finish < 0`, and on `(0, 1)` it is `Ψ ∘ η ∘ time` for a strictly increasing `time` from `(0, 1)` onto
the excursion component `C`. -/
structure ExcursionChartCut (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ) (C : Set ℝ) where
  cut : ℝ → ℂ
  cont : ContinuousOn cut (Icc 0 1)
  start : ℝ
  finish : ℝ
  cut_zero : cut 0 = start
  cut_one : cut 1 = finish
  finish_neg : finish < 0
  time : ℝ → ℝ
  time_strictMono : StrictMonoOn time (Ioo 0 1)
  time_mem : MapsTo time (Ioo 0 1) C
  time_surj : C ⊆ time '' Ioo 0 1
  sub : C ⊆ excursionTimes η w s
  cut_eq : ∀ t ∈ Ioo (0 : ℝ) 1, cut t = revChart w s (η (time t))

namespace ExcursionChartCut

variable {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ} {C : Set ℝ} (κ : ExcursionChartCut η w s C)

/-- The closed loop of a chart crosscut: along `cut` from `start` to `finish`, then back along the real
segment. -/
def loop : ℝ → ℂ := fun t =>
  if t ≤ 1 / 2 then κ.cut (2 * t) else ((κ.finish + (2 * t - 1) * (κ.start - κ.finish) : ℝ) : ℂ)

theorem loop_of_le {t : ℝ} (ht : t ≤ 1 / 2) : κ.loop t = κ.cut (2 * t) := by
  simp only [loop, ht, ↓reduceIte]

theorem loop_of_ge {t : ℝ} (ht : 1 / 2 ≤ t) :
    κ.loop t = ((κ.finish + (2 * t - 1) * (κ.start - κ.finish) : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, loop_of_le κ le_rfl, show (2 : ℝ) * (1 / 2) = 1 by norm_num, κ.cut_one]
    congr 1
    ring
  · simp only [loop, not_le.2 h, ↓reduceIte]

theorem continuousOn_loop : ContinuousOn κ.loop (Icc 0 1) := by
  have h1 : ContinuousOn κ.loop (Icc 0 (1 / 2)) := by
    refine ContinuousOn.congr (f := fun t => κ.cut (2 * t)) ?_ fun t ht => κ.loop_of_le ht.2
    exact κ.cont.comp (continuous_const.mul continuous_id).continuousOn fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 : ContinuousOn κ.loop (Icc (1 / 2) 1) :=
    ContinuousOn.congr (f := fun t => ((κ.finish + (2 * t - 1) * (κ.start - κ.finish) : ℝ) : ℂ))
      (by fun_prop) fun t ht => κ.loop_of_ge ht.1
  have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at this

theorem loop_closed : κ.loop 0 = κ.loop 1 := by
  rw [κ.loop_of_le (by norm_num), κ.loop_of_ge (by norm_num), mul_zero, κ.cut_zero]
  congr 1
  ring

theorem time_mem_excursionTimes {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : κ.time t ∈ excursionTimes η w s :=
  κ.sub (κ.time_mem ht)

theorem time_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < κ.time t := (κ.time_mem_excursionTimes ht).1

theorem eta_time_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : η (κ.time t) ∈ H \ cfHullQ w s :=
  (κ.time_mem_excursionTimes ht).2

theorem cut_mem_H (hw : Continuous w) (hs : 0 ≤ s) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    κ.cut t ∈ H := by
  rw [κ.cut_eq t ht]
  exact revChart_mem_H hw hs (κ.eta_time_mem ht)

theorem cut_mem_chartFlowSet {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : κ.cut t ∈ chartFlowSet η w s := by
  rw [κ.cut_eq t ht]
  exact ⟨η (κ.time t), ⟨⟨κ.time t, mem_Ici.2 (κ.time_pos ht).le, rfl⟩, κ.eta_time_mem ht⟩, rfl⟩

theorem revChartInv_cut (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : revChartInv w s (κ.cut t) = η (κ.time t) := by
  rw [κ.cut_eq t ht]
  exact revChartInv_revChart hw hw0 hs (κ.eta_time_mem ht)

/-- The crosscut is injective on the open parameter interval. -/
theorem injOn_cut (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) :
    InjOn κ.cut (Ioo 0 1) := by
  intro u hu v hv he
  have h := congrArg (revChartInv w s) he
  rw [κ.revChartInv_cut hw hw0 hs hu, κ.revChartInv_cut hw hw0 hs hv] at h
  exact κ.time_strictMono.injOn hu hv (hη.inj (κ.time_pos hu).le (κ.time_pos hv).le h)

/-- The completed crosscut lies in the closure of the chart flow set. -/
theorem image_cut_subset_closure : κ.cut '' Icc 0 1 ⊆ closure (chartFlowSet η w s) := by
  have hcl : closure (Ioo (0 : ℝ) 1) = Icc 0 1 := closure_Ioo zero_ne_one
  have hc : ContinuousOn κ.cut (closure (Ioo 0 1)) := hcl ▸ κ.cont
  have h1 := hc.image_closure
  rw [hcl] at h1
  exact h1.trans (closure_mono (image_subset_iff.2 fun t ht => κ.cut_mem_chartFlowSet ht))

theorem start_mem_closure : (κ.start : ℂ) ∈ closure (chartFlowSet η w s) :=
  κ.cut_zero ▸ κ.image_cut_subset_closure ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩

theorem finish_mem_closure : (κ.finish : ℂ) ∈ closure (chartFlowSet η w s) :=
  κ.cut_one ▸ κ.image_cut_subset_closure ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩

/-- The two pieces of the loop: the crosscut, and real points between its two ends. -/
theorem loop_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∃ u ∈ Icc (0 : ℝ) 1, κ.loop t = κ.cut u) ∨
      ∃ y : ℝ, κ.loop t = y ∧ min κ.start κ.finish ≤ y ∧ y ≤ max κ.start κ.finish := by
  rcases le_total t (1 / 2) with h | h
  · exact Or.inl ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, κ.loop_of_le h⟩
  · refine Or.inr ⟨κ.finish + (2 * t - 1) * (κ.start - κ.finish), κ.loop_of_ge h, ?_, ?_⟩
    · rcases le_total κ.start κ.finish with h' | h'
      · rw [min_eq_left h']; nlinarith [ht.2]
      · rw [min_eq_right h']; nlinarith [ht.2]
    · rcases le_total κ.start κ.finish with h' | h'
      · rw [max_eq_right h']; nlinarith [ht.2]
      · rw [max_eq_left h']; nlinarith [ht.2]

/-- A point of the loop in `ℍ` is an interior point of the crosscut. -/
theorem exists_of_loop_mem_H {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hH : κ.loop t ∈ H) :
    ∃ u ∈ Ioo (0 : ℝ) 1, κ.loop t = κ.cut u := by
  have hreal : ∀ y : ℝ, (y : ℂ) ∉ H := fun y h => lt_irrefl _ (show (0 : ℝ) < (y : ℂ).im from h)
  rcases κ.loop_mem ht with ⟨u, hu, he⟩ | ⟨y, he, -⟩
  · rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hu with rfl | rfl | hu'
    · rw [he, κ.cut_zero] at hH; exact absurd hH (hreal _)
    · rw [he, κ.cut_one] at hH; exact absurd hH (hreal _)
    · exact ⟨u, hu', he⟩
  · rw [he] at hH; exact absurd hH (hreal _)

/-- The loop lies in any ball containing the closure of the chart flow set. -/
theorem norm_loop_lt {R : ℝ} (hR : closure (chartFlowSet η w s) ⊆ ball 0 R) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖κ.loop t‖ < R := by
  have hball : ∀ z ∈ closure (chartFlowSet η w s), ‖z‖ < R := fun z hz => mem_ball_zero_iff.1 (hR hz)
  rcases κ.loop_mem ht with ⟨u, hu, he⟩ | ⟨y, he, hy₁, hy₂⟩
  · rw [he]; exact hball _ (κ.image_cut_subset_closure ⟨u, hu, rfl⟩)
  · rw [he, norm_real, Real.norm_eq_abs, abs_lt]
    have hs₁ := hball _ κ.start_mem_closure
    have hf₁ := hball _ κ.finish_mem_closure
    rw [norm_real, Real.norm_eq_abs, abs_lt] at hs₁ hf₁
    constructor
    · exact lt_of_lt_of_le (lt_min hs₁.1 hf₁.1) hy₁
    · exact lt_of_le_of_lt hy₂ (max_lt hs₁.2 hf₁.2)

end ExcursionChartCut

/-! ### The incoming limit and the terminal interval -/

/-- **The incoming prime-end limit of an excursion** (at the seed it is the chart's `0`). -/
theorem exists_tendsto_revChart_start {η β : ℝ → ℂ} {w : ℝ → ℝ} {s a b : ℝ}
    (hη : IsProperArc η) (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (htip : negInv (β s) ∉ arcRange η) (ha : 0 ≤ a) (hab : a < b)
    (hD : MapsTo η (Ioo a b) (H \ cfHullQ w s)) (haD : η a ∉ H \ cfHullQ w s) :
    ∃ x : ℝ, Tendsto (fun t => revChart w s (η t)) (𝓝[>] a) (𝓝 (x : ℂ)) := by
  rcases ha.eq_or_lt with rfl | ha'
  · have hη0 : Tendsto η (𝓝[>] 0) (𝓝[H \ cfHullQ w s] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h := (hη.cont 0 (mem_Ici.2 le_rfl)).tendsto.mono_left
          (nhdsWithin_mono _ Ioi_subset_Ici_self)
        rwa [hη.zero] at h
      · have he : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 b := Ioo_mem_nhdsGT hab
        exact he.mono fun _ hu => hD hu
    refine ⟨0, ?_⟩
    have h := (tendsto_revChart_zero hw hw0 hs).comp hη0
    rw [ofReal_zero]
    exact h
  · let α : ℝ → ℂ := fun t => negInv (η t)
    let m : ℝ := (a + b) / 2
    have ham : a < m := by dsimp [m]; linarith
    have hmb : m < b := by dsimp [m]; linarith
    have hαc : ContinuousOn α (Icc a m) := continuousOn_negInv.comp
      (hη.cont.mono fun t ht => ha'.le.trans ht.1)
      (fun t ht => hη.mem_H t (ha'.trans_le ht.1))
    have hαD : MapsTo α (Ioc a m) (H \ fwdHull w s) :=
      fun _ ht => negInv_notMem_fwdHull (hD ⟨ht.1, ht.2.trans_lt hmb⟩)
    have hαa : α a ∉ H \ fwdHull w s := by
      intro hn
      apply haD
      refine ⟨hη.mem_H a ha', ?_⟩
      rintro ⟨z, hz, he⟩
      apply hn.2
      change negInv (η a) ∈ fwdHull w s
      rw [← he, negInv_negInv']
      exact hz
    obtain ⟨q, hq, hlim⟩ := exists_tendsto_fwdMap_right hβ hw hw0 hs ham hαc hαD hαa
    have hq0 : (q : ℂ) ≠ 0 := by
      intro h0
      rw [h0, extendFrom_zero hβ hw hw0 hs] at hq
      have heq : negInv (β s) = η a := by
        simpa only [α, negInv_negInv'] using congrArg negInv hq
      exact htip ⟨a, mem_Ici.2 ha'.le, heq.symm⟩
    refine ⟨-q⁻¹, ?_⟩
    have h := ((continuousAt_negInv hq0).tendsto).comp hlim
    have hval : negInv (q : ℂ) = ((-q⁻¹ : ℝ) : ℂ) := by simp [negInv]
    rw [hval] at h
    exact h

/-- **The terminal excursion interval**: a component of the excursion times that is not bounded above is a ray
`(a, ∞)` whose start is not in `D` (it is the seed or a contact). -/
theorem exists_eq_Ioi_of_not_bddAbove {η : ℝ → ℂ} {w : ℝ → ℝ} {s u : ℝ}
    (hη : IsProperArc η) (hw : Continuous w) (hs : 0 ≤ s) (hu : u ∈ excursionTimes η w s)
    (hnb : ¬ BddAbove (connectedComponentIn (excursionTimes η w s) u)) :
    ∃ a : ℝ, 0 ≤ a ∧ connectedComponentIn (excursionTimes η w s) u = Ioi a ∧
      η a ∉ H \ cfHullQ w s := by
  set C := connectedComponentIn (excursionTimes η w s) u with hCdef
  have htC : u ∈ C := mem_connectedComponentIn hu
  have hCU : C ⊆ excursionTimes η w s := connectedComponentIn_subset _ _
  have hCo : IsOpen C := (isOpen_excursionTimes hη hw hs).connectedComponentIn
  have hCc : IsConnected C := isConnected_connectedComponentIn_iff.2 hu
  have hbelow : BddBelow C := ⟨0, fun _ hy => (hCU hy).1.le⟩
  have hstrict : ∀ y ∈ C, sInf C < y := by
    intro y hy
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 hCo y hy
    have hminus : y - ε / 2 ∈ C := hb (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith)
    exact (csInf_le hbelow hminus).trans_lt (by linarith)
  have hCeq : C = Ioi (sInf C) := by
    refine Subset.antisymm (fun y hy => hstrict y hy) fun y hy => ?_
    obtain ⟨c, hcC, hcy⟩ := exists_lt_of_csInf_lt ⟨u, htC⟩ (mem_Ioi.1 hy)
    obtain ⟨d, hdC, hyd⟩ := not_bddAbove_iff.1 hnb y
    exact hCc.isPreconnected.Icc_subset hcC hdC ⟨hcy.le, hyd.le⟩
  have h0 : 0 ≤ sInf C := le_csInf ⟨u, htC⟩ fun _ hy => (hCU hy).1.le
  refine ⟨sInf C, h0, hCeq, fun hD => ?_⟩
  have hpos : 0 < sInf C := by
    rcases h0.eq_or_lt with he | he
    · have hH := hD.1
      rw [← he, hη.zero] at hH
      exact absurd rfl (ne_zero_of_mem_H hH)
    · exact he
  have hmem : sInf C ∈ excursionTimes η w s := ⟨hpos, hD⟩
  have hcl : sInf C ∈ closure C := csInf_mem_closure ⟨u, htC⟩ hbelow
  have hinsert : IsPreconnected (insert (sInf C) C) := hCc.isPreconnected.subset_closure
    (subset_insert _ C) (insert_subset hcl subset_closure)
  have hsub : insert (sInf C) C ⊆ C := hinsert.subset_connectedComponentIn
    (mem_insert_of_mem _ htC) (insert_subset hmem hCU)
  exact lt_irrefl _ (hstrict _ (hsub (mem_insert _ C)))

/-! ### Construction of the chart crosscuts -/

/-- A chart crosscut from a reparametrization with the two endpoint limits. -/
theorem ExcursionChartCut.nonempty_of_limits {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ} {C : Set ℝ}
    (hη : IsProperArc η) (hw : Continuous w) (hs : 0 ≤ s) (hsub : C ⊆ excursionTimes η w s)
    (time : ℝ → ℝ) (htc : ContinuousOn time (Ioo 0 1)) (htm : StrictMonoOn time (Ioo 0 1))
    (hmem : MapsTo time (Ioo 0 1) C) (hsurj : C ⊆ time '' Ioo 0 1) {xs xf : ℝ}
    (hxs : Tendsto (fun t => revChart w s (η (time t))) (𝓝[>] 0) (𝓝 (xs : ℂ)))
    (hxf : Tendsto (fun t => revChart w s (η (time t))) (𝓝[<] 1) (𝓝 (xf : ℂ))) (hneg : xf < 0) :
    Nonempty (ExcursionChartCut η w s C) := by
  let G : ℝ → ℂ := fun t => revChart w s (η (time t))
  have hGc : ContinuousOn G (Ioo 0 1) :=
    (continuousOn_revChart hw hs).comp (hη.cont.comp htc fun t ht => mem_Ici.2 (hsub (hmem ht)).1.le)
      fun t ht => (hsub (hmem ht)).2
  have hγc : ContinuousOn (extendFrom (Ioo 0 1) G) (Icc 0 1) :=
    continuousOn_Icc_extendFrom_Ioo hGc hxs hxf
  have hγ₀ : extendFrom (Ioo 0 1) G 0 = (xs : ℂ) := eq_lim_at_left_extendFrom_Ioo zero_lt_one hxs
  have hγ₁ : extendFrom (Ioo 0 1) G 1 = (xf : ℂ) := eq_lim_at_right_extendFrom_Ioo zero_lt_one hxf
  have hγG : EqOn (extendFrom (Ioo 0 1) G) G (Ioo 0 1) := extendFrom_extends hGc
  exact ⟨⟨extendFrom (Ioo 0 1) G, hγc, xs, xf, hγ₀, hγ₁, hneg, time, htm, hmem, hsurj, hsub,
    fun t ht => hγG ht⟩⟩

/-- **Every excursion completes to a chart crosscut** with a negative finishing gate, under the western-end
property. The terminal excursion is reparametrized by `t ↦ a + t/(1 − t)`. -/
theorem nonempty_excursionChartCut {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}
    (hη : IsProperArc η) (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (htip : negInv (β s) ∉ arcRange η) (hends : HasWesternExcursionEnds η w s) {u : ℝ}
    (hu : u ∈ excursionTimes η w s) :
    Nonempty (ExcursionChartCut η w s (connectedComponentIn (excursionTimes η w s) u)) := by
  have hsub : connectedComponentIn (excursionTimes η w s) u ⊆ excursionTimes η w s :=
    connectedComponentIn_subset _ _
  by_cases hb : BddAbove (connectedComponentIn (excursionTimes η w s) u)
  · obtain ⟨e⟩ := exists_boundedExcursionInterval_of_bddAbove hη hw hs hu hb
    set a := e.start
    set b := e.finish
    have hab : a < b := e.start_lt.trans e.lt_finish
    have hba : 0 < b - a := sub_pos.2 hab
    have hD := e.mapsTo
    obtain ⟨xs, hxs⟩ := exists_tendsto_revChart_start hη hβ hw hw0 hs htip e.start_nonneg hab hD
      e.start_outside
    have hm0 : 0 < (a + b) / 2 := by linarith [e.start_nonneg]
    obtain ⟨xf, hxf, hlimf⟩ := hends.1 ((a + b) / 2) b hm0 (by linarith)
      (fun t ht => hD ⟨by linarith [ht.1], ht.2⟩) e.finish_outside
    have htime0 : Tendsto (fun t : ℝ => a + t * (b - a)) (𝓝[>] 0) (𝓝[>] a) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h : Tendsto (fun t : ℝ => a + t * (b - a)) (𝓝 0) (𝓝 (a + 0 * (b - a))) :=
          (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
        rw [zero_mul, add_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        change a < a + t * (b - a)
        nlinarith [mem_Ioi.1 ht]
    have htime1 : Tendsto (fun t : ℝ => a + t * (b - a)) (𝓝[<] 1) (𝓝[<] b) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h : Tendsto (fun t : ℝ => a + t * (b - a)) (𝓝 1) (𝓝 (a + 1 * (b - a))) :=
          (continuous_const.add (continuous_id.mul continuous_const)).tendsto 1
        rw [one_mul, add_sub_cancel] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        change a + t * (b - a) < b
        nlinarith [mem_Iio.1 ht]
    refine ExcursionChartCut.nonempty_of_limits hη hw hs hsub (fun t => a + t * (b - a))
      (by fun_prop) (fun t _ t' _ htt => by nlinarith) (fun t ht => ?_) (fun y hy => ?_)
      (hxs.comp htime0) (hlimf.comp htime1) hxf
    · rw [e.component_eq]
      exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    · rw [e.component_eq] at hy
      refine ⟨(y - a) / (b - a), ⟨div_pos (by linarith [hy.1]) hba, (div_lt_one hba).2 (by linarith [hy.2])⟩,
        ?_⟩
      field_simp
      ring
  · obtain ⟨a, ha0, hCeq, haD⟩ := exists_eq_Ioi_of_not_bddAbove hη hw hs hu hb
    have hDt : ∀ t ∈ Ioi a, η t ∈ H \ cfHullQ w s := fun t ht => (hsub (hCeq ▸ ht)).2
    obtain ⟨xs, hxs⟩ := exists_tendsto_revChart_start hη hβ hw hw0 hs htip ha0 (lt_add_one a)
      (fun t ht => hDt t ht.1) haD
    obtain ⟨xf, hxf, hlimf⟩ := hends.2 a ha0 hDt
    have harc0 : ContinuousAt arcTime 0 :=
      continuousOn_arcTime.continuousAt (Iio_mem_nhds (by norm_num))
    have htime0 : Tendsto (fun t : ℝ => a + arcTime t) (𝓝[>] 0) (𝓝[>] a) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h := (continuousAt_const (y := a)).add harc0
        have h0 : arcTime 0 = 0 := by simp [arcTime]
        have h' : Tendsto (fun t : ℝ => a + arcTime t) (𝓝 0) (𝓝 (a + arcTime 0)) := h.tendsto
        rw [h0, add_zero] at h'
        exact h'.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
        change a < a + arcTime t
        linarith [arcTime_pos ht]
    have htime1 : Tendsto (fun t : ℝ => a + arcTime t) (𝓝[<] 1) atTop :=
      tendsto_atTop_add_const_left _ a tendsto_arcTime
    refine ExcursionChartCut.nonempty_of_limits hη hw hs hsub (fun t => a + arcTime t)
      (continuousOn_const.add (continuousOn_arcTime.mono fun t ht => ht.2))
      (fun t ht t' ht' htt => by
        have := strictMonoOn_arcTime ⟨ht.1.le, ht.2⟩ ⟨ht'.1.le, ht'.2⟩ htt
        dsimp only; linarith)
      (fun t ht => ?_) (fun y hy => ?_) (hxs.comp htime0) (hlimf.comp htime1) hxf
    · rw [hCeq]
      change a < a + arcTime t
      linarith [arcTime_pos ht]
    · rw [hCeq] at hy
      have hy' : 0 < y - a := sub_pos.2 hy
      refine ⟨discTime (y - a), ⟨?_, (discTime_mem_Ico hy'.le).2⟩, ?_⟩
      · rw [discTime]; positivity
      · dsimp only
        rw [arcTime_discTime hy'.le]
        ring

end InteractingSLE.Sec5.Prop51HGate
