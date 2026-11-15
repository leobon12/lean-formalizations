/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RefBridge
import InteractingSLE.Spec.ZhanGT4.MTildeFrozen
import InteractingSLE.Spec.ZhanGT4.FrozenMeas
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.Foundations.Loewner.ConformalImageUnion

/-!
# The canonical image of A.1 through countably many frozen-hull quantities (deterministic part)

Packet PROVE-A1-MARG (R76), for the measurability clauses (m3)–(m4) of `A1Core.IsRectImageCore`. The canonical image
(`A1Ref.imgClk`, `A1Ref.imgDrv`, `A1Ref.imgLife`, PROVE-ZHAN-A1REF) of curve `j` (start `xj`, driver `wj`) in the
chart `g_τ` of curve `k` (start `xk`, driver `wk`) is choice-defined. Here it is expressed, pathwise, through objects
whose measurability is known (`FrzMeasR`, A13):

* **translation** (`contactTime_sub`, `imgClk_sub`, `imgLife_sub`, `isImgDrvOn_add`): the canonical image of curve `j`
  started at `xj` is that of curve `j` started at `0` against `K_k(τ) − xj`, shifted by `xj`;
* **`ownData_bridge`**: with A.1's own-time data (`OwnData`, Aux. lemma 8) for the driver of curve `j` stopped beyond
  the horizon, the clock is the canonical clock and the image driver is canonical;
* **`imgClk_eq_hcap`**: `imgClk d = (hcap(E_d) + 2d − 2τ)/2` with `E_d = g^{(j)}_d(K_k(τ))` the image of the frozen
  hull (capacity additivity, `HPHull.hcap_add_hcap_image_eq`), and `tendsto_hcapSet`: `hcap(E) = lim n(n − Im R_E(in))`;
* **`ofReal_lt_contactTime_iff`**: a countable criterion for `d < contactTime`;
* `imgLife_eq_iSup_rat`, `imgDrv_eq_zero_of_le`: the lifetime is a countable supremum, the driver vanishes beyond it;
* **`tendsto_dySearch`**: inversion of a continuous strictly increasing clock by a dyadic search (`dySearch`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Marg

open QuantumZipper (H)
open A2X A1Ref ConformalImage

/-! ### Translation to the frame of curve `j` -/

section Translate

theorem image_sub_physHull (x c : ℝ) (w : ℝ → ℝ) (s : ℝ) :
    (fun z : ℂ => z - c) '' physHull x w s = physHull (x - c) w s := by
  simp only [physHull, image_image]
  refine image_congr fun z _ => ?_
  push_cast; ring

theorem physMap_sub (x c : ℝ) (w : ℝ → ℝ) (τ : ℝ) (z : ℂ) :
    physMap (x - c) w τ (z - c) = physMap x w τ z - c := by
  have e : z - (c : ℂ) - ((x - c : ℝ) : ℂ) = z - x := by push_cast; ring
  rw [physMap, physMap, e]
  push_cast; ring

/-- Half-plane capacity is invariant under real translations. -/
theorem hcapSet_image_sub (B : Set ℂ) (c : ℝ) : hcapSet ((fun z : ℂ => z - c) '' B) = hcapSet B := by
  have e : ∀ c' : ℝ, (fun z : ℂ => z - c') '' B = affHomeo 1 one_pos (-c') '' B := fun c' =>
    image_congr fun z _ => by rw [ConformalImageFull.affHomeo_one_apply]; push_cast; ring
  rw [e]
  by_cases hB : IsHPHull B
  · rw [hcapSet_eq (hB.image_affHomeo one_pos), hcapSet_eq hB]
    have h1 := HPHull.hcap_affHomeo (x := -c) ⟨B, hB⟩ one_pos
    rw [one_pow, one_mul] at h1
    exact h1
  · have hB' : ¬ IsHPHull (affHomeo 1 one_pos (-c) '' B) := fun h => hB (by
      have h2 := h.image_affHomeo one_pos (x := c)
      rwa [image_image, image_congr (fun z _ => by
        rw [ConformalImageFull.affHomeo_one_apply, ConformalImageFull.affHomeo_one_apply, id]; push_cast; ring :
          ∀ z ∈ B, affHomeo 1 one_pos c (affHomeo 1 one_pos (-c) z) = id z), image_id] at h2)
    simp [hcapSet, hB, hB']

/-- Real translations preserve the meeting of closures. -/
theorem closure_inter_nonempty_sub (A B : Set ℂ) (c : ℝ) :
    (closure ((fun z : ℂ => z - c) '' A) ∩ closure ((fun z : ℂ => z - c) '' B)).Nonempty ↔
      (closure A ∩ closure B).Nonempty := by
  set h : ℂ ≃ₜ ℂ := Homeomorph.addRight (-(c : ℂ)) with hh
  have hcoe : (fun z : ℂ => z - c) = h := by funext z; simp [hh, sub_eq_add_neg]
  rw [hcoe, ← h.image_closure, ← h.image_closure, ← image_inter h.injective, image_nonempty]

theorem contactTime_sub (xj : ℝ) (wj : ℝ → ℝ) (ζj : ℝ≥0∞) (xk : ℝ) (wk : ℝ → ℝ) (τ : ℝ) :
    contactTime xj wj ζj xk wk τ = contactTime 0 wj ζj (xk - xj) wk τ := by
  unfold contactTime
  congr 1
  refine iInf_congr fun s => iInf_congr_Prop ?_ fun _ => rfl
  rw [← closure_inter_nonempty_sub _ _ xj, image_sub_physHull, image_sub_physHull, sub_self]

theorem imgClk_sub (xj : ℝ) (wj : ℝ → ℝ) (xk : ℝ) (wk : ℝ → ℝ) (τ s : ℝ) :
    imgClk xj wj xk wk τ s = imgClk 0 wj (xk - xj) wk τ s := by
  unfold imgClk
  split_ifs with hs
  · congr 1
    rw [← hcapSet_image_sub _ xj, image_image]
    congr 1
    rw [← sub_self xj, ← image_sub_physHull xj xj wj s, image_image]
    exact image_congr fun z _ => (physMap_sub xk xj wk τ z).symm
  · rfl

theorem imgLife_sub (xj : ℝ) (wj : ℝ → ℝ) (ζj : ℝ≥0∞) (xk : ℝ) (wk : ℝ → ℝ) (τ : ℝ) :
    imgLife xj wj ζj xk wk τ = imgLife 0 wj ζj (xk - xj) wk τ := by
  unfold imgLife
  simp only [contactTime_sub xj wj ζj xk wk τ, imgClk_sub xj wj xk wk τ]

theorem isGoodTime_sub {xj : ℝ} {wj : ℝ → ℝ} {ζj : ℝ≥0∞} {xk : ℝ} {wk : ℝ → ℝ} {τ T : ℝ} :
    IsGoodTime xj wj ζj xk wk τ T ↔ IsGoodTime 0 wj ζj (xk - xj) wk τ T := by
  unfold IsGoodTime
  rw [contactTime_sub]

/-- **An image driver in the frame of curve `j`, shifted by `xj`, is an image driver of curve `j` started at `xj`.** -/
theorem isImgDrvOn_add {xj : ℝ} {wj : ℝ → ℝ} {xk : ℝ} {wk : ℝ → ℝ} {τ T : ℝ} {W'' : ℝ → ℝ}
    (h : IsImgDrvOn 0 wj (xk - xj) wk τ T W'') : IsImgDrvOn xj wj xk wk τ T (fun σ => W'' σ + xj) := by
  obtain ⟨hc, hlim, hhull⟩ := h
  refine ⟨hc.add continuous_const, ?_, fun t ht => ?_⟩
  · have hT : Tendsto (fun z : ℂ => z - xj) (𝓝[H] (xj : ℂ)) (𝓝[H] ((0 : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
      · have : Tendsto (fun z : ℂ => z - xj) (𝓝 (xj : ℂ)) (𝓝 ((xj : ℂ) - xj)) :=
          (continuous_id.sub continuous_const).tendsto _
        rw [sub_self] at this
        simpa using this.mono_left nhdsWithin_le_nhds
      · show 0 < (z - (xj : ℂ)).im
        have hz' : 0 < z.im := hz
        simpa using hz'
    have h2 := (hlim.comp hT).add_const (xj : ℂ)
    have e : ((((fun σ => W'' σ + xj) 0 : ℝ)) : ℂ) = (W'' 0 : ℂ) + xj := by push_cast; ring
    rw [e]
    refine h2.congr' (Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply]
    rw [physMap_sub, sub_add_cancel]
  · rw [ConformalImageFull.fwdHull_add_const, imgClk_sub, hhull t ht, image_image, ← sub_self xj,
      ← image_sub_physHull xj xj wj t, image_image]
    refine image_congr fun z _ => ?_
    rw [physMap_sub, sub_add_cancel]

end Translate

/-! ### The own-time data of A.1 are the canonical image (frame of curve `j`) -/

section Bridge

theorem physHull_mono (x : ℝ) (w : ℝ → ℝ) {s t : ℝ} (hst : s ≤ t) : physHull x w s ⊆ physHull x w t :=
  image_mono (QuantumZipper.fwdHull_mono.1 hst)

/-- The hull of curve `k` at `τ` has capacity `2τ` (driver continuous slightly beyond `τ`). -/
theorem hcapSet_physHull {x : ℝ} {w : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hk : ∃ τ', τ < τ' ∧ ContinuousOn w (Icc 0 τ')) : hcapSet (physHull x w τ) = 2 * τ := by
  obtain ⟨τ', hττ', hw⟩ := hk
  rw [physHull_congr hτ hττ' (stopDrv_eqOn w τ').symm]
  have e : physHull x (stopDrv w τ') τ = (fun z : ℂ => z - ((-x : ℝ) : ℂ)) '' QuantumZipper.fwdHull (stopDrv w τ') τ :=
    image_congr fun z _ => by push_cast; ring
  rw [e, hcapSet_image_sub, hcapSet_fwdHull (continuous_stopDrv hw (hτ.trans hττ'.le)) hτ]

/-- **Bridge**: the own-time data of curve `j` (started at `0`, driver stopped at `T₂ > T`) against the frozen hull
`K_k(τ)` is an image driver on `[0, T]` and its clock is the canonical clock there. -/
theorem ownData_bridge {wj wk : ℝ → ℝ} {xk τ T T₂ : ℝ} {a W' : ℝ → ℝ} (hTT : T < T₂)
    (h : OwnData (stopDrv wj T₂) (physHull xk wk τ) (physMap xk wk τ) T a W') :
    IsImgDrvOn 0 wj xk wk τ T W' ∧ ∀ t ∈ Icc (0 : ℝ) T, a t = imgClk 0 wj xk wk τ t := by
  obtain ⟨hW', hEq⟩ := isImgDrvOn_of_ownData h
  have hph : ∀ t ∈ Icc (0 : ℝ) T, physHull 0 (stopDrv wj T₂) t = physHull 0 wj t := fun t ht =>
    physHull_congr ht.1 (ht.2.trans_lt hTT) (stopDrv_eqOn wj T₂)
  have hc : ∀ t ∈ Icc (0 : ℝ) T, imgClk 0 (stopDrv wj T₂) xk wk τ t = imgClk 0 wj xk wk τ t := fun t ht => by
    unfold imgClk; rw [hph t ht]
  refine ⟨⟨hW'.1, hW'.2.1, fun t ht => ?_⟩, fun t ht => (hEq ht).trans (hc t ht)⟩
  rw [← hc t ht, hW'.2.2 t ht, hph t ht]

/-- **The canonical clock through the capacity of the image of the frozen hull**: for `0 < d ≤ T`,
`imgClk d = (hcap(g^{(j)}_d(K_k(τ))) + 2d − 2τ)/2` (capacity additivity). -/
theorem imgClk_eq_hcap {wj wk : ℝ → ℝ} {xk τ T T₂ d : ℝ} {a W' : ℝ → ℝ} (hτ : 0 ≤ τ)
    (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hTT : T < T₂)
    (h : OwnData (stopDrv wj T₂) (physHull xk wk τ) (physMap xk wk τ) T a W') (hd : d ∈ Icc (0 : ℝ) T)
    (hd0 : 0 < d) :
    imgClk 0 wj xk wk τ d =
      (hcapSet (imgHull (stopDrv wj T₂) (physHull xk wk τ) d) + 2 * d - 2 * τ) / 2 := by
  set W := stopDrv wj T₂ with hWdef
  set A := physHull xk wk τ with hA
  have hcongr : physHull 0 wj d = QuantumZipper.fwdHull W d := by
    rw [← physHull_congr hd.1 (hd.2.trans_lt hTT) (stopDrv_eqOn wj T₂), physHull_zero]
  simp only [imgClk, hd0, ↓reduceIte]
  rw [hcongr]
  have hK := isHPHull_fwdHull h.cont hd.1
  have hg := isMapOut_fwdMap h.cont h.zero hd.1
  have hdisj : Disjoint (closure A) (closure (QuantumZipper.fwdHull W d)) :=
    h.disj.mono_right (closure_mono (QuantumZipper.fwdHull_mono.1 hd.2))
  have key := HPHull.hcap_add_hcap_image_eq h.hull hK hdisj h.mapOut hg
  rw [← hcapSet_eq, ← hcapSet_eq, ← hcapSet_eq, ← hcapSet_eq] at key
  rw [hA, hcapSet_physHull hτ hk, hcapSet_fwdHull h.cont hd.1] at key
  have e : hcapSet (imgHull W (physHull xk wk τ) d) =
      hcapSet ((fun z => QuantumZipper.fwdMap W d z + (W d : ℂ)) '' physHull xk wk τ) := rfl
  rw [e]
  linarith

/-- `hcap(E) = lim n (n − Im R_E(i n))` along the integers. -/
theorem tendsto_hcapSet {E : Set ℂ} (hE : IsHPHull E) :
    Tendsto (fun n : ℕ => (n : ℝ) * ((n : ℝ) - (ConformalImage.mapOut E ((n : ℝ) * I)).im)) atTop (𝓝 (hcapSet E)) := by
  rw [hcapSet_eq hE]
  exact (HPHull.tendsto_mul_sub_im ⟨E, hE⟩ (ConformalImage.isMapOut_mapOut hE)).comp tendsto_natCast_atTop_atTop

end Bridge

/-! ### The contact time, the lifetime and the driver beyond it -/

section Contact

variable {xj : ℝ} {wj : ℝ → ℝ} {ζj : ℝ≥0∞} {xk : ℝ} {wk : ℝ → ℝ} {τ : ℝ}

/-- **A countable criterion for `d < contactTime`**: some rational `q > d` before `ζj` at which the two closed hulls
are still disjoint. -/
theorem ofReal_lt_contactTime_iff {d : ℝ} (hd : 0 ≤ d) :
    ENNReal.ofReal d < contactTime xj wj ζj xk wk τ ↔ ∃ q : ℚ, d < q ∧ ENNReal.ofReal q < ζj ∧
      ¬ (closure (physHull xj wj q) ∩ closure (physHull xk wk τ)).Nonempty := by
  constructor
  · intro h
    obtain ⟨q, hq0, hdq, hqc⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
    have hdq' : ENNReal.ofReal d < ENNReal.ofReal q := hdq
    have hqc' : ENNReal.ofReal q < contactTime xj wj ζj xk wk τ := hqc
    have hq0' : (0 : ℝ) ≤ q := by exact_mod_cast hq0
    refine ⟨q, ((ENNReal.ofReal_lt_ofReal_iff').1 hdq').1, (lt_min_iff.1 hqc').1, fun hne => ?_⟩
    have hle : (⨅ (s : ℝ≥0) (_ : (closure (physHull xj wj s) ∩ closure (physHull xk wk τ)).Nonempty),
        (s : ℝ≥0∞)) ≤ ENNReal.ofReal q :=
      iInf₂_le (Real.toNNReal q) (by rwa [Real.coe_toNNReal _ hq0'])
    exact absurd ((lt_min_iff.1 hqc').2.trans_le hle) (lt_irrefl _)
  · rintro ⟨q, hdq, hqζ, hne⟩
    have hq0 : (0 : ℝ) < q := hd.trans_lt hdq
    refine lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hq0).2 hdq) (le_min hqζ.le (le_iInf₂ fun s hs => ?_))
    by_contra hlt
    rw [not_le, ← ENNReal.ofReal_coe_nnreal] at hlt
    have hsq : (s : ℝ) ≤ q := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1.le
    obtain ⟨z, hz1, hz2⟩ := hs
    exact hne ⟨z, closure_mono (physHull_mono xj wj hsq) hz1, hz2⟩

/-- **The lifetime is a countable supremum** (strictly increasing clock). -/
theorem imgLife_eq_iSup_rat
    (hmono : StrictMonoOn (imgClk xj wj xk wk τ) {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj wj ζj xk wk τ}) :
    imgLife xj wj ζj xk wk τ = ⨆ q : ℚ, ⨆ (_ : 0 ≤ (q : ℝ) ∧ ENNReal.ofReal q < contactTime xj wj ζj xk wk τ),
      ENNReal.ofReal (imgClk xj wj xk wk τ q) := by
  apply le_antisymm
  · refine iSup₂_le fun s hs => ?_
    obtain ⟨q, hq0, hsq, hqc⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hs
    have hq0' : (0 : ℝ) ≤ q := by exact_mod_cast hq0
    have hqc' : ENNReal.ofReal q < contactTime xj wj ζj xk wk τ := hqc
    have hsq' : (s : ℝ) ≤ q := by
      have : ENNReal.ofReal (s : ℝ) < ENNReal.ofReal q := by rw [ENNReal.ofReal_coe_nnreal]; exact hsq
      exact ((ENNReal.ofReal_lt_ofReal_iff').1 this).1.le
    have hsI : (s : ℝ) ∈ {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj wj ζj xk wk τ} :=
      ⟨s.coe_nonneg, by rw [ENNReal.ofReal_coe_nnreal]; exact hs⟩
    exact le_iSup₂_of_le (f := fun (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ ENNReal.ofReal q < contactTime xj wj ζj xk wk τ) =>
      ENNReal.ofReal (imgClk xj wj xk wk τ q)) q ⟨hq0', hqc'⟩
      (ENNReal.ofReal_le_ofReal (hmono.monotoneOn hsI ⟨hq0', hqc'⟩ hsq'))
  · refine iSup₂_le fun q hq => ?_
    refine le_iSup₂_of_le (f := fun (s : ℝ≥0) (_ : (s : ℝ≥0∞) < contactTime xj wj ζj xk wk τ) =>
      ENNReal.ofReal (imgClk xj wj xk wk τ s)) (Real.toNNReal q) ?_ ?_
    · rw [← ENNReal.ofReal]; exact hq.2
    · rw [Real.coe_toNNReal _ hq.1]

/-- **The canonical driver vanishes beyond the canonical lifetime.** -/
theorem imgDrv_eq_zero_of_le
    (hmono : StrictMonoOn (imgClk xj wj xk wk τ) {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj wj ζj xk wk τ})
    {σ : ℝ} (hσ : imgLife xj wj ζj xk wk τ ≤ ENNReal.ofReal σ) : imgDrv xj wj ζj xk wk τ σ = 0 := by
  have hne : ¬ ∃ T : ℝ, IsGoodTime xj wj ζj xk wk τ T ∧ σ ≤ imgClk xj wj xk wk τ T ∧
      ∃ W' : ℝ → ℝ, IsImgDrvOn xj wj xk wk τ T W' := by
    rintro ⟨T, hT, hσT, -⟩
    obtain ⟨T', hT', hTT'⟩ := exists_isGoodTime hT.1.le hT.2
    have hTI : T ∈ {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj wj ζj xk wk τ} := ⟨hT.1.le, hT.2⟩
    have hT'I : T' ∈ {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj wj ζj xk wk τ} := ⟨hT'.1.le, hT'.2⟩
    have hlt := hmono hTI hT'I hTT'
    have h0I : (0 : ℝ) ∈ {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj wj ζj xk wk τ} :=
      ⟨le_rfl, (ENNReal.ofReal_le_ofReal hT.1.le).trans_lt hT.2⟩
    have h0 : imgClk xj wj xk wk τ 0 ≤ imgClk xj wj xk wk τ T := hmono.monotoneOn h0I hTI hT.1.le
    rw [imgClk_zero] at h0
    have hle : ENNReal.ofReal (imgClk xj wj xk wk τ T') ≤ imgLife xj wj ζj xk wk τ :=
      le_iSup₂_of_le (f := fun (s : ℝ≥0) (_ : (s : ℝ≥0∞) < contactTime xj wj ζj xk wk τ) =>
        ENNReal.ofReal (imgClk xj wj xk wk τ s)) (Real.toNNReal T')
        (by rw [← ENNReal.ofReal]; exact hT'.2) (by rw [Real.coe_toNNReal _ hT'.1.le])
    have h1 : ENNReal.ofReal σ < ENNReal.ofReal (imgClk xj wj xk wk τ T') :=
      (ENNReal.ofReal_le_ofReal hσT).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (h0.trans_lt hlt)).2 hlt)
    exact absurd (h1.trans_le (hle.trans hσ)) (lt_irrefl _)
  rw [imgDrv, dite_eq_right_of_eq_false (eq_false hne)]

end Contact

/-! ### Inverting the clock by a dyadic search -/

section Search

/-- The `n`-th dyadic test: `k/2ⁿ` precedes `c` and its clock reaches `σ`. -/
def DyGood (c : ℝ≥0∞) (clk : ℝ → ℝ) (σ : ℝ) (n k : ℕ) : Prop :=
  ENNReal.ofReal ((k : ℝ) / 2 ^ n) < c ∧ σ ≤ clk ((k : ℝ) / 2 ^ n)

theorem exists_dyGood_or (c : ℝ≥0∞) (clk : ℝ → ℝ) (σ : ℝ) (n : ℕ) :
    ∃ k, DyGood c clk σ n k ∨ ∀ j, ¬ DyGood c clk σ n j := by
  by_cases h : ∃ k, DyGood c clk σ n k
  · obtain ⟨k, hk⟩ := h; exact ⟨k, Or.inl hk⟩
  · exact ⟨0, Or.inr (not_exists.1 h)⟩

open scoped Classical in
/-- The least dyadic index of level `n` passing the test (`0` if none). -/
def dySearch (c : ℝ≥0∞) (clk : ℝ → ℝ) (σ : ℝ) (n : ℕ) : ℕ := Nat.find (exists_dyGood_or c clk σ n)

/-- **Inverting a continuous strictly increasing clock by a dyadic search**: if the clock (`0` at `0`) reaches above
`σ ≥ 0` before `c`, the dyadic searches converge to the time `t₀` with `clk t₀ = σ`, and any function continuous before
`c` converges along them to its value at `t₀`. -/
theorem tendsto_dySearch {c : ℝ≥0∞} {clk F : ℝ → ℝ} {σ : ℝ}
    (hcont : ContinuousOn clk {s | 0 ≤ s ∧ ENNReal.ofReal s < c})
    (hmono : StrictMonoOn clk {s | 0 ≤ s ∧ ENNReal.ofReal s < c}) (h0 : clk 0 = 0) (hσ : 0 ≤ σ)
    (hF : ContinuousOn F {s | 0 ≤ s ∧ ENNReal.ofReal s < c}) {s₁ : ℝ}
    (hs₁ : 0 ≤ s₁ ∧ ENNReal.ofReal s₁ < c) (hσs₁ : σ < clk s₁) :
    ∃ t₀, (0 ≤ t₀ ∧ ENNReal.ofReal t₀ < c) ∧ clk t₀ = σ ∧
      Tendsto (fun n : ℕ => F ((dySearch c clk σ n : ℝ) / 2 ^ n)) atTop (𝓝 (F t₀)) ∧
      ∀ᶠ n : ℕ in atTop, DyGood c clk σ n (dySearch c clk σ n) := by
  classical
  set I := {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < c} with hI
  have hsub : Icc 0 s₁ ⊆ I := fun s hs => ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt hs₁.2⟩
  obtain ⟨t₀, ht₀, hct⟩ : σ ∈ clk '' Icc 0 s₁ :=
    intermediate_value_Icc hs₁.1 (hcont.mono hsub) ⟨by rw [h0]; exact hσ, hσs₁.le⟩
  have ht₀I : t₀ ∈ I := hsub ht₀
  have ht₀s₁ : t₀ < s₁ := lt_of_le_of_ne ht₀.2 fun h => by rw [h] at hct; linarith
  have key : ∀ r ∈ I, σ ≤ clk r ↔ t₀ ≤ r := fun r hr => by rw [← hct]; exact hmono.le_iff_le ht₀I hr
  set m : ℕ → ℕ := fun n => ⌈t₀ * 2 ^ n⌉₊ with hm
  have hpow : ∀ n : ℕ, (0 : ℝ) < 2 ^ n := fun n => by positivity
  have hm1 : ∀ n, t₀ ≤ (m n : ℝ) / 2 ^ n := fun n => by
    rw [le_div_iff₀ (hpow n)]; exact Nat.le_ceil _
  have hm2 : ∀ n, (m n : ℝ) / 2 ^ n < t₀ + 1 / 2 ^ n := fun n => by
    rw [div_lt_iff₀ (hpow n), add_mul, one_div_mul_cancel (hpow n).ne']
    exact Nat.ceil_lt_add_one (mul_nonneg ht₀I.1 (hpow n).le)
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / (2 : ℝ) ^ n < s₁ - t₀ := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    filter_upwards [h.eventually (gt_mem_nhds (sub_pos.2 ht₀s₁))] with n hn
    rwa [one_div_pow] at hn
  have hmI : ∀ᶠ n : ℕ in atTop, (m n : ℝ) / 2 ^ n ∈ I := by
    filter_upwards [hsmall] with n hn
    exact hsub ⟨ht₀I.1.trans (hm1 n), by linarith [hm2 n]⟩
  have hfind : ∀ᶠ n : ℕ in atTop, dySearch c clk σ n = m n := by
    filter_upwards [hmI] with n hn
    have hgood : DyGood c clk σ n (m n) := ⟨hn.2, (key _ hn).2 (hm1 n)⟩
    unfold dySearch
    rw [Nat.find_eq_iff]
    refine ⟨Or.inl hgood, fun j hj hP => ?_⟩
    rcases hP with hP | hP
    · have hjI : (j : ℝ) / 2 ^ n ∈ I := ⟨by positivity, hP.1⟩
      have ht := (key _ hjI).1 hP.2
      rw [le_div_iff₀ (hpow n)] at ht
      exact absurd (Nat.ceil_le.2 ht) (not_le.2 hj)
    · exact hP _ hgood
  have hconv : Tendsto (fun n : ℕ => (m n : ℝ) / 2 ^ n) atTop (𝓝 t₀) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have h' : Tendsto (fun n : ℕ => t₀ + 1 / (2 : ℝ) ^ n) atTop (𝓝 t₀) := by
      simpa [one_div_pow] using (tendsto_const_nhds (x := t₀)).add h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h' hm1 fun n => (hm2 n).le
  have hgoodev : ∀ᶠ n : ℕ in atTop, DyGood c clk σ n (dySearch c clk σ n) := by
    filter_upwards [hfind, hmI] with n hn hnI
    rw [hn]
    exact ⟨hnI.2, (key _ hnI).2 (hm1 n)⟩
  refine ⟨t₀, ht₀I, hct, ?_, hgoodev⟩
  have hw : Tendsto (fun n : ℕ => (m n : ℝ) / 2 ^ n) atTop (𝓝[I] t₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hconv, hmI⟩
  refine ((hF t₀ ht₀I).tendsto.comp hw).congr' ?_
  filter_upwards [hfind] with n hn
  simp only [Function.comp_apply, hn]

end Search

end InteractingSLE.ZhanGT4.A1Marg
