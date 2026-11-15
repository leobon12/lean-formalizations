/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NeRel
import InteractingSLE.Spec.Restart.RetEndLimit
import InteractingSLE.Spec.Supplement.GW2BtContact

/-!
# The canonical relative driver when the explored curve never touches the retained prefix

Packet PROVE-GW2-NEARIMG2, decision D56 (`UncEndStatement`), one sample. Setting of `GW2NeRel`: no root-`x` contact,
the retained tip `α(s) ≠ 0`, and the explored curve transient (`‖γ t‖ → ∞`).

* **the relative trace converges** (`exists_tendsto_relTr`): `relBdry(x + γ t) − relBdry(x)` has a limit `ℓ`
  (`tendsto_relBdry_of_transient`: in the sphere picture `x + γ` tends to the retained base, not to the tip);
* **the clock is bounded** (`exists_clock_bound`): the relative trace is bounded by some `B`, so every hull of the glued
  driver lies in `B̄(0, B)` (it fills the trace) and `2 a(t) ≤ B²`;
* **the canonical driver** (`exists_canon_of_noContact`): with `L = sup a`, the glued driver has the generating trace
  `ηc` on `[0, L]` (`ηc(a t) = relBdry(x + γ t) − relBdry(x)`, `ηc(L) = ℓ`), hence a limit at `L`
  (`Restart.RetEnd.exists_tendsto_driver_of_isGeneratingTrace`, [Yua22] Theorem 1.1 (ii) ⇒ (i)); freezing it there
  gives a continuous driver `Wc` with the re-centred relative hulls at every clock value, a generating trace living to
  the root-`x` relative life `L`, and the clock bounded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Ni

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.ReadD GW2TipSystem GW2Rz

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
  (hT : firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = ⊤)

include hα hW hW0 hζ hx harc hwc hw0 hγ hT in
/-- **The relative trace converges** along a transient explored curve that never touches the retained prefix. -/
theorem exists_tendsto_relTr (hαs : α s ≠ 0) (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    ∃ ℓ : ℂ, Tendsto (fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x) atTop (𝓝 ℓ) := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  set U : ℝ → ℝ := Ito.rpath (W · ω) with hUdef
  have hU : Continuous U := hW.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simp only [hUdef, Ito.rpath, Real.toNNReal_zero, hW0]
  have hαS : IsGeneratingTrace (W · ω) (s : ℝ≥0∞) α :=
    ⟨hα.1, hα.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top, fun t ht => hα.2.2 t (ht.trans_le le_top)⟩
  obtain ⟨hB, htip⟩ := LoewnerConcat.prefix_boundary hW hW0 hαS
  have hR : ∀ p : ℂ, p.im = 0 → extendFrom H (fwdMapInv U s) p ∉ extendFrom H (fwdMapInv U s) '' H := by
    rintro p hp ⟨q, hq, hpq⟩
    refine LoewnerConcat.extendFrom_real_notMem_bdry hW hW0 hαS hp ?_
    rw [← hpq, extendFrom_fwdMapInv_eq hU hU0 s.coe_nonneg hq]
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 s.coe_nonneg hq
  have htip' : extendFrom H (fwdMapInv U s) 0 ≠ 0 := by rw [htip]; exact hαs
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hPc : Continuous fun t => (x : ℂ) + γ t := continuous_const.add hγc
  have hP : ∀ t, (x : ℂ) + γ t ∈ relSafe U s := fun t => by
    have h := RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ (lt_min_of_noContact hT t) le_rfl
    rw [GW2Bh.relSafe_record_eq s hW0 hW hζ] at h
    exact h
  have htrP : Tendsto (fun t => ‖(x : ℂ) + γ t‖) atTop atTop := by
    refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-‖(x : ℂ)‖) htr)
    have h := norm_sub_le ((x : ℂ) + γ t) (x : ℂ)
    rw [add_sub_cancel_left] at h
    linarith
  obtain ⟨ξ, -, hξ⟩ := tendsto_relBdry_of_transient hU hU0 s.coe_nonneg hB hR htip' hPc hP htrP
  refine ⟨ξ - relBdry (rdrv (cfRec s W ζ ω)) s x, ?_⟩
  have e := GW2Bh.relBdry_record_eq s hW0 hW hζ (W := W) (ζ := ζ) (ω := ω)
  rw [e]
  exact hξ.sub_const _

include hα hW hW0 hζ hx harc hwc hw0 hγ hT in
/-- **The relative trace is bounded** (continuous, with a limit at `∞`). -/
theorem exists_relTr_bound (hαs : α s ≠ 0) (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ≥0, ‖relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x‖ ≤ B := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  obtain ⟨ℓ, hρ⟩ := exists_tendsto_relTr W ζ ω hα hW hW0 hζ hx harc hwc hw0 hγ hT hαs htr
  set ρ := fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) - relBdry (rdrv (cfRec s W ζ ω)) s x
    with hρdef
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hρc : Continuous ρ :=
    ((continuousOn_relBdry (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg).comp_continuous
      (continuous_const.add hγc) fun t =>
        RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ (lt_min_of_noContact hT t) le_rfl).sub
      continuous_const
  obtain ⟨T, hT'⟩ := eventually_atTop.1 (hρ.eventually (closedBall_mem_nhds ℓ one_pos))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn hρc.continuousOn
  refine ⟨max (max C (‖ℓ‖ + 1)) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun t => ?_⟩
  rcases le_total t T with h | h
  · exact (hC t ⟨zero_le, h⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have h1 := hT' t h
    rw [dist_eq_norm] at h1
    have h2 := norm_le_norm_add_norm_sub' (ρ t) ℓ
    refine le_trans ?_ ((le_max_right _ _).trans (le_max_left _ _))
    change ‖ρ t‖ ≤ ‖ℓ‖ + 1
    linarith

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The root-`x` clock is bounded** along a transient explored curve that never touches the retained prefix. -/
theorem exists_clock_bound (hαs : α s ≠ 0) (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    ∃ M : ℝ, ∀ t : ℝ≥0, gClk x s (cfRec s W ζ ω) w t ≤ M := by
  obtain ⟨h0, hm, hc⟩ := gClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  obtain ⟨B, hB, hρB⟩ := exists_relTr_bound W ζ ω hα hW hW0 hζ hx harc hwc hw0 hγ hT hαs htr
  set a := gClk x s (cfRec s W ζ ω) w with hadef
  refine ⟨B ^ 2 / 2, fun t => ?_⟩
  set v : ℝ≥0 := t + 1 with hv
  have htv : t < v := lt_add_one t
  have hat : 0 ≤ a t := h0 ▸ hm.monotone zero_le
  have hatv : a t < a v := hm htv
  have hgen := isGeneratingTrace_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT v
  set u : ℝ≥0 := (a t).toNNReal with hudef
  have hu : (u : ℝ) = a t := Real.coe_toNNReal _ hat
  have hulv : (u : ℝ≥0∞) < ENNReal.ofReal (a v) := by rw [ENNReal.coe_lt_ofReal, hu]; exact hatv
  have hfill := hgen.2.2 u hulv
  set tip := fun u' => RootI30.capacityTipRead x s v u' (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) with htipdef
  have hsub : tip '' Icc 0 u ⊆ closedBall ((0 : ℝ) : ℂ) B := by
    rintro _ ⟨u', hu', rfl⟩
    have hmem : (u' : ℝ) ∈ Icc (a 0) (a t) := by
      rw [h0]
      exact ⟨u'.coe_nonneg, hu ▸ NNReal.coe_le_coe.2 hu'.2⟩
    obtain ⟨t', ht', hat'⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t) hc.continuousOn hmem
    have hu'eq : u' = (a t').toNNReal := by rw [hat', Real.toNNReal_coe]
    rw [mem_closedBall, Complex.ofReal_zero, dist_zero_right, htipdef]
    dsimp only
    rw [hu'eq, tip_eq W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT (ht'.2.trans htv.le)]
    exact hρB t'
  have hcpt : IsCompact (tip '' Icc 0 u) := by
    refine isCompact_Icc.image_of_continuousOn (hgen.2.1.mono fun u' hu' => ?_)
    show (u' : ℝ≥0∞) ≤ ENNReal.ofReal (a v)
    exact (ENNReal.coe_le_coe.2 hu'.2).trans hulv.le
  have hK := Gm.subset_closedBall_of_isFilling (fun _ hz => hz.1) hcpt hfill hsub
  rw [Complex.ofReal_zero, hu] at hK
  obtain ⟨R, hRc, hR0, -, hReq⟩ := exists_chain_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
    (add_pos_of_nonneg_of_pos zero_le one_pos : (0 : ℝ≥0) < v)
  have h1 : fwdHull (fun r : ℝ => gDrv x s (cfRec s W ζ ω) w r.toNNReal) (a t) =
      fwdHull (fun r : ℝ => R r.toNNReal) (a t) := by
    refine InteractingSLE.fwdHull_eq_of_eqOn hat (show a t < (a t + a v) / 2 by linarith) fun r hr => ?_
    refine hReq _ ?_
    rw [Real.coe_toNNReal _ hr.1]
    linarith [hr.2]
  rw [h1] at hK
  have h2 := QuantumZipper.TipXE.two_mul_le_sq_of_fwdHull_subset (A := fun r : ℝ => R r.toNNReal)
    (hRc.comp continuous_real_toNNReal) (by simp only [Real.toNNReal_zero, hR0]) hat hB hK
  linarith

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The canonical relative driver without contact** (one sample): a continuous driver from `0` with the re-centred
relative hulls at every clock value, a generating trace living to the root-`x` relative life, and the clock bounded. -/
theorem exists_canon_of_noContact (hαs : α s ≠ 0) (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    ∃ Wc : ℝ≥0 → ℝ, Continuous Wc ∧ Wc 0 = 0 ∧
      (∀ t : ℝ≥0, fwdHull (fun q : ℝ => Wc q.toNNReal) (gClk x s (cfRec s W ζ ω) w t) =
        (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
          RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤))) ∧
      (∃ (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), IsGeneratingTrace Wc ζc ηc ∧
        ENNReal.ofReal (GW2Bh.contactLifeX x s (cfRec s W ζ ω) w γ α) ≤ ζc) ∧
      ∃ M : ℝ, ∀ t : ℝ≥0, gClk x s (cfRec s W ζ ω) w t ≤ M := by
  obtain ⟨h0, hm, hc⟩ := gClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  obtain ⟨ℓ, hρ⟩ := exists_tendsto_relTr W ζ ω hα hW hW0 hζ hx harc hwc hw0 hγ hT hαs htr
  obtain ⟨M, hM⟩ := exists_clock_bound W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hαs htr
  set a := gClk x s (cfRec s W ζ ω) w with hadef
  set D := gDrv x s (cfRec s W ζ ω) w with hDdef
  set ρ := fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) - relBdry (rdrv (cfRec s W ζ ω)) s x
    with hρdef
  have hD0 : D 0 = 0 := gDrv_zero W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  have hann : ∀ t, 0 ≤ a t := fun t => h0 ▸ hm.monotone zero_le
  -- the relative life `L = sup a`
  have hbdd : BddAbove (range a) := ⟨M, by rintro _ ⟨t, rfl⟩; exact hM t⟩
  set L := sSup (range a) with hLdef
  have haL : ∀ t, a t < L := fun t => (hm (lt_add_one t)).trans_le (le_csSup hbdd ⟨t + 1, rfl⟩)
  have hLex : ∀ y : ℝ, y < L → ∃ t, y < a t := fun y hy => by
    obtain ⟨_, ⟨t, rfl⟩, h⟩ := exists_lt_of_lt_csSup (range_nonempty a) hy
    exact ⟨t, h⟩
  have hL0 : 0 < L := h0 ▸ haL 0
  set L' : ℝ≥0 := L.toNNReal with hL'def
  have hL'0 : 0 < L' := Real.toNNReal_pos.2 hL0
  have hlt : ∀ u : ℝ≥0, u < L' ↔ (u : ℝ) < L := fun u => Real.lt_toNNReal_iff_coe_lt
  have hcontD : ∀ u : ℝ≥0, u < L' → ContinuousAt D u := fun u hu => by
    obtain ⟨v, hv⟩ := hLex u ((hlt u).1 hu)
    exact continuousAt_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hv
  -- the relative trace on `[0, L]`
  set ηc : ℝ≥0 → ℂ := fun u => if u < L' then LP.traceAt u D else ℓ with hηdef
  set tip := fun (v u : ℝ≥0) => RootI30.capacityTipRead x s v u (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))
    with htipdef
  have hgen : ∀ v, IsGeneratingTrace D (ENNReal.ofReal (a v)) (tip v) := fun v =>
    isGeneratingTrace_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT v
  have hηeq : ∀ v u : ℝ≥0, (u : ℝ) < a v → ηc u = tip v u := fun v u hu => by
    have huL : u < L' := (hlt u).2 (hu.trans (haL v))
    simp only [hηdef, huL, ↓reduceIte]
    exact LP.traceAt_eq_of_isGeneratingTrace (hgen v)
      (continuousOn_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT v) hD0 (ENNReal.coe_lt_ofReal.2 hu)
  have hηρ : ∀ t, ηc (a t).toNNReal = ρ t := fun t => by
    have htL : (a t).toNNReal < L' := (hlt _).2 (by rw [Real.coe_toNNReal _ (hann t)]; exact haL t)
    simp only [hηdef, htL, ↓reduceIte]
    exact traceAt_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT t
  have hη0 : ηc 0 = 0 := by
    have h := hηρ 0
    rw [h0, Real.toNNReal_zero] at h
    rw [h]
    simp only [hρdef, hγ.1, add_zero, sub_self]
  have hηlim : Tendsto ηc (𝓝[<] L') (𝓝 ℓ) := by
    refine tendsto_iff_forall_eventually_mem.2 fun V hV => ?_
    obtain ⟨T, hT'⟩ := eventually_atTop.1 (hρ.eventually hV)
    have hmem : Ioo (a T).toNNReal L' ∈ 𝓝[<] L' :=
      Ioo_mem_nhdsLT ((hlt _).2 (by rw [Real.coe_toNNReal _ (hann T)]; exact haL T))
    filter_upwards [hmem] with u hu
    obtain ⟨t₁, ht₁⟩ := hLex u ((hlt u).1 hu.2)
    have hTu : a T < u := (Real.toNNReal_lt_iff_lt_coe (hann T)).1 hu.1
    have hTt₁ : T ≤ t₁ := (hm.lt_iff_lt.1 (hTu.trans ht₁)).le
    obtain ⟨t, ht, hat⟩ := intermediate_value_Icc hTt₁ hc.continuousOn ⟨hTu.le, ht₁.le⟩
    have hueq : u = (a t).toNNReal := by rw [hat, Real.toNNReal_coe]
    rw [hueq, hηρ]
    exact hT' t ht.1
  have hgenD : IsGeneratingTrace D (L' : ℝ≥0∞) ηc := by
    refine ⟨hη0, fun u hu => ?_, fun u hu => ?_⟩
    · rcases lt_or_eq_of_le (ENNReal.coe_le_coe.1 hu) with h | h
      · obtain ⟨v, hv⟩ := hLex u ((hlt u).1 h)
        have hnhds : {u' : ℝ≥0 | (u' : ℝ) < a v} ∈ 𝓝 u :=
          (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds hv
        have hct : ContinuousAt (tip v) u := by
          refine ((hgen v).2.1.mono fun u' hu' => ?_).continuousAt hnhds
          exact (ENNReal.coe_lt_ofReal.2 hu').le
        exact (hct.congr (Filter.eventually_of_mem hnhds fun u' hu' => (hηeq v u' hu').symm)).continuousWithinAt
      · subst h
        have hset : {u : ℝ≥0 | (u : ℝ≥0∞) ≤ (L' : ℝ≥0∞)} = Iic L' := by
          ext u
          simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Iic]
        rw [hset]
        refine continuousWithinAt_Iio_iff_Iic.1 ?_
        have hηL : ηc L' = ℓ := by simp only [hηdef, lt_irrefl, ↓reduceIte]
        show Tendsto ηc (𝓝[<] L') (𝓝 (ηc L'))
        rw [hηL]
        exact hηlim
    · have huL : u < L' := ENNReal.coe_lt_coe.1 hu
      obtain ⟨v, hv⟩ := hLex u ((hlt u).1 huL)
      have hfill := (hgen v).2.2 u (ENNReal.coe_lt_ofReal.2 hv)
      have himg : ηc '' Icc 0 u = tip v '' Icc 0 u :=
        image_congr fun u' hu' => hηeq v u' ((NNReal.coe_le_coe.2 hu'.2).trans_lt hv)
      rw [himg]
      exact hfill
  -- the driver limit at `L`, and the frozen driver
  obtain ⟨cL, hcL⟩ := RetEnd.exists_tendsto_driver_of_isGeneratingTrace hgenD
    (fun u hu => (hcontD u (ENNReal.coe_lt_coe.1 hu)).continuousWithinAt) hD0 hL'0
  set Wc : ℝ≥0 → ℝ := fun u => if u < L' then D u else cL with hWcdef
  have hWcD : ∀ u, u < L' → Wc u = D u := fun u hu => by simp only [hWcdef, hu, ↓reduceIte]
  have hWcc : ∀ u, L' ≤ u → Wc u = cL := fun u hu => by simp only [hWcdef, not_lt.2 hu, ↓reduceIte]
  have hWcont : Continuous Wc := by
    refine continuous_iff_continuousAt.2 fun u => ?_
    rcases lt_trichotomy u L' with h | h | h
    · exact (hcontD u h).congr (Filter.eventually_of_mem (Iio_mem_nhds h) fun u' hu' => (hWcD u' hu').symm)
    · subst h
      refine continuousAt_iff_continuous_left_right.2 ⟨continuousWithinAt_Iio_iff_Iic.1 ?_, ?_⟩
      · show Tendsto Wc (𝓝[<] L') (𝓝 (Wc L'))
        rw [hWcc L' le_rfl]
        exact hcL.congr' (eventually_nhdsWithin_of_forall fun u' hu' => (hWcD u' hu').symm)
      · exact continuousWithinAt_const.congr (fun y hy => hWcc y hy) (hWcc L' le_rfl)
    · exact continuousAt_const.congr
        (Filter.eventually_of_mem (Ioi_mem_nhds h) fun u' hu' => (hWcc u' (le_of_lt hu')).symm)
  have hhullWc : ∀ q : ℝ, 0 ≤ q → q < L →
      fwdHull (fun r : ℝ => Wc r.toNNReal) q = fwdHull (fun r : ℝ => D r.toNNReal) q := fun q hq hqL => by
    refine InteractingSLE.fwdHull_eq_of_eqOn hq (show q < (q + L) / 2 by linarith) fun r hr => ?_
    refine hWcD _ ((hlt _).2 ?_)
    rw [Real.coe_toNNReal _ hr.1]
    linarith [hr.2]
  refine ⟨Wc, hWcont, by rw [hWcD 0 hL'0, hD0], fun t => ?_, ⟨L', ηc, ?_, ?_⟩, M, hM⟩
  · rw [hhullWc _ (hann t) (haL t)]
    exact hull_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT t
  · refine ⟨hgenD.1, hgenD.2.1, fun u hu => ?_⟩
    rw [hhullWc _ u.coe_nonneg ((hlt u).1 (ENNReal.coe_lt_coe.1 hu))]
    exact hgenD.2.2 u hu
  · have hcl : GW2Bh.contactLifeX x s (cfRec s W ζ ω) w γ α = L := by
      unfold GW2Bh.contactLifeX
      rw [hT]
      simp only [ENNReal.coe_lt_top, ofPred_true, image_univ]
      rfl
    rw [hcl]
    exact le_rfl

end Sample

end InteractingSLE.Theorem14.GW2Ni
