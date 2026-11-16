/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermSample
import InteractingSLE.Spec.Supplement.AStopPathMono
import InteractingSLE.Spec.Supplement.LP3Flow

/-!
# The boundary correspondence of the chart of the completed second path

Packet PROVE-RC-TERM, second run (ruling R124). The chart-boundary facts `RLC.AStopPath.IsAChart` and the
monotonicity `RLC.AStopPath.IsAMono` (the inputs of Lemma G7's threshold analysis) for the boundary inverse of the
chart of the completed second path, at a boundary seed:

* **`re_fwdMap_lt_of_alive`**: the real Loewner flow preserves the strict order of alive real points
  (`QuantumZipper.FwdHolo.sol_sub_eq`);
* `IsEntryData.entryExt_entryInv` (`entryExt ∘ entryInv = id` on `ℍ̄`), `IsEntryData.isFreeAt_of_mem_closure`
  (a point of the closure of the domain off the path is free), `IsEntryData.entryExt_ofReal` (the extension at a free
  real point is the real flow), `re_entryExt_neg`, `re_entryExt_pos` (the sides of the seed are kept);
* `IsEntryData.entryInv_untouched` (an untouched real chart point has a real image on the same side of the seed) and
  `IsEntryData.re_entryInv_lt` (the boundary inverse is increasing on untouched real chart points);
* **`IsKSample.isAChart`**, **`IsKSample.isAMono`**: the two structures for `v ↦ kInv v + x₁` and any closed set `Kp`
  which is the completed second path with the first seed, in the original orientation.

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.RealContact

namespace Term

open LP (reflectC)
open HalfPlaneSep Restart
open Exist.StagedLaw (markPos markPosL)

/-- **The real Loewner flow preserves the strict order of alive real points.** -/
theorem re_fwdMap_lt_of_alive {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {a b : ℝ} (hab : a < b)
    (ha : ∃ u, IsForwardSol W (a : ℂ) T u) (hb : ∃ v, IsForwardSol W (b : ℂ) T v) :
    (fwdMap W T (a : ℂ)).re < (fwdMap W T (b : ℂ)).re := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  have hTT : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  rw [QuantumZipper.F1.fwdMap_eq_of_isForwardSol hu hTT, QuantumZipper.F1.fwdMap_eq_of_isForwardSol hv hTT]
  have e := QuantumZipper.FwdHolo.sol_sub_eq hu hv T hTT
  have hint : (∫ s in (0 : ℝ)..T, (2 : ℂ) / (v s * u s)) =
      ((∫ s in (0 : ℝ)..T, 2 / ((v s).re * (u s).re) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hT] at hs
    obtain ⟨x, hx⟩ : ∃ x : ℝ, v s = x := ⟨_, LP.LP3.eq_ofReal_re_of_isForwardSol hW hv hs⟩
    obtain ⟨y, hy⟩ : ∃ y : ℝ, u s = y := ⟨_, LP.LP3.eq_ofReal_re_of_isForwardSol hW hu hs⟩
    simp only [hx, hy, ofReal_re]
    push_cast
    rfl
  rw [hint, ← ofReal_neg, ← ofReal_exp, ← ofReal_sub, ← ofReal_mul] at e
  have hre := congrArg Complex.re e
  rw [sub_re, ofReal_re] at hre
  have hpos : 0 < (b - a) * Real.exp (-∫ s in (0 : ℝ)..T, 2 / ((v s).re * (u s).re)) :=
    mul_pos (sub_pos.2 hab) (Real.exp_pos _)
  linarith

section Builder

variable {V : ℝ → ℝ} {T : ℝ} {ξ : ℝ → ℂ} {p d : ℝ}

/-- **The forward extension inverts the boundary inverse** on the closed half-plane. -/
theorem IsEntryData.entryExt_entryInv (h : IsEntryData V T ξ p d) {v : ℂ} (hv : 0 ≤ v.im) :
    entryExt V ξ T d (entryInv V T d v) = v := by
  have hne : (𝓝[H] v).NeBot := neBot_nhdsWithin_H_of_im_nonneg hv
  have hDc := h.isDomainChart'
  have h1 : Tendsto (entryChart V T d).2.1 (𝓝[H] v) (𝓝[entryDom ξ T d] (entryInv V T d v)) :=
    tendsto_nhdsWithin_iff.2 ⟨h.tendsto_inv hv, eventually_nhdsWithin_of_forall fun w hw => hDc.inv_mem hw⟩
  have h2 := (h.tendsto_entryExt (h.entryInv_mem_closure hv)).comp h1
  have h3 : Tendsto (fun w : ℂ => w) (𝓝[H] v) (𝓝 (entryExt V ξ T d (entryInv V T d v))) :=
    h2.congr' (eventually_nhdsWithin_of_forall fun w hw => hDc.fwd_inv hw)
  exact tendsto_nhds_unique h3 (tendsto_id.mono_left nhdsWithin_le_nhds)

/-- A point of the closure of the domain off the path is free. -/
theorem IsEntryData.isFreeAt_of_mem_closure (h : IsEntryData V T ξ p d) {z : ℂ}
    (hz : z ∈ closure (entryDom ξ T d)) (hzK : z ∉ entryPath ξ T d '' Icc 0 1) :
    IsFreeAt (entryPath ξ T d '' Icc 0 1) z := by
  rcases isFreeAt_or_isTrappedAt h.isCompact_path.isClosed hzK with hf | ⟨ε, hε, hdis⟩
  · exact hf
  · exfalso
    obtain ⟨w, hw, hwz⟩ := Metric.mem_closure_iff.1 hz ε hε
    exact Set.disjoint_left.1 hdis (by rwa [mem_ball, dist_comm]) hw

/-- **The extension at a free real point is the real flow.** -/
theorem IsEntryData.entryExt_ofReal (h : IsEntryData V T ξ p d) {x : ℝ} (hxd : x ≠ d)
    (hf : IsFreeAt (entryPath ξ T d '' Icc 0 1) (x : ℂ)) :
    (∃ u, IsForwardSol V ((x - d : ℝ) : ℂ) T u) ∧ entryExt V ξ T d (x : ℂ) =
      (((fwdMap V T ((x - d : ℝ) : ℂ)).re - markPosL V T (-d) : ℝ) : ℂ) := by
  have hxd' : (x : ℂ) ≠ (d : ℂ) := fun he => hxd (by exact_mod_cast he)
  obtain ⟨u, hu⟩ := h.alive_of_isFreeAt (by rw [ofReal_im]) hxd' hf
  rw [← ofReal_sub] at hu
  refine ⟨⟨u, hu⟩, ?_⟩
  rw [h.entryExt_of_isFreeAt (by rw [ofReal_im]) hxd' hf, entryChart_fst, ← ofReal_sub]
  have e := fwdMap_ofReal_real h.tip.cont h.tip.pos.le ⟨u, hu⟩
  calc fwdMap V T ((x - d : ℝ) : ℂ) - (markPosL V T (-d) : ℂ)
      = ((fwdMap V T ((x - d : ℝ) : ℂ)).re : ℂ) - (markPosL V T (-d) : ℂ) := by rw [← e]
    _ = _ := by push_cast; rfl

/-- The chart keeps the left of the seed on the left. -/
theorem IsEntryData.re_entryExt_neg (h : IsEntryData V T ξ p d) {x : ℝ} (hx : x < 0) :
    (entryExt V ξ T d (x : ℂ)).re < 0 := by
  have hV := h.tip.cont
  have hT := h.tip.pos.le
  set F : ℝ → ℝ := fun y => (fwdMap V T ((y - d : ℝ) : ℂ)).re - markPosL V T (-d) with hF
  have hmono : ∀ y z : ℝ, y < z → z < 0 → F y < F z := by
    intro y z hyz hz
    have h1 := re_fwdMap_lt_of_alive hV hT (a := y - d) (b := z - d) (by linarith)
      (h.alive_of_lt (by linarith [h.seed])) (h.alive_of_lt (by linarith [h.seed]))
    simp only [hF]
    linarith
  have hle : F (x / 2) ≤ 0 := by
    refine ge_of_tendsto h.tendsto_entry_zero ?_
    have hmem : Ioo (x / 2) 0 ∈ 𝓝[<] (0 : ℝ) := Ioo_mem_nhdsLT (by linarith)
    filter_upwards [hmem] with y hy
    exact (hmono (x / 2) y hy.1 hy.2).le
  have hlt := hmono x (x / 2) (by linarith) (by linarith)
  have hxd : x ≠ d := fun he => by linarith [h.seed]
  rw [(h.entryExt_ofReal hxd (h.isFreeAt_of_neg hx)).2, ofReal_re]
  exact lt_of_lt_of_le hlt hle

/-- The chart keeps the free points right of the seed on the right. -/
theorem IsEntryData.re_entryExt_pos (h : IsEntryData V T ξ p d) {x : ℝ} (hx : 0 < x) (hxd : x ≠ d)
    (hf : IsFreeAt (entryPath ξ T d '' Icc 0 1) (x : ℂ)) : 0 < (entryExt V ξ T d (x : ℂ)).re := by
  have hV := h.tip.cont
  have hT := h.tip.pos.le
  obtain ⟨hal, he⟩ := h.entryExt_ofReal hxd hf
  have hge : 0 ≤ (fwdMap V T ((x - d : ℝ) : ℂ)).re - markPosL V T (-d) := by
    refine le_of_tendsto h.tendsto_entry_zero ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < 0)
    have h1 := re_fwdMap_lt_of_alive hV hT (a := y - d) (b := x - d) (by linarith)
      (h.alive_of_lt (by linarith [h.seed])) hal
    linarith
  rw [he, ofReal_re]
  refine lt_of_le_of_ne hge fun h0 => ?_
  have hz : entryExt V ξ T d (x : ℂ) = 0 := by rw [he, ← h0, ofReal_zero]
  have h1 := h.entryInv_entryExt (mem_closure_entryDom_of_isFreeAt (by rw [ofReal_im]) hf)
  have h2 := h.entryInv_entryExt h.zero_mem_closure
  rw [hz] at h1
  rw [h.entryExt_zero, h1] at h2
  have : x = 0 := by exact_mod_cast h2
  linarith

/-- **An untouched real chart point has a free real image off the retained seed.** -/
theorem IsEntryData.entryInv_untouched (h : IsEntryData V T ξ p d) {v : ℝ}
    (hK : entryInv V T d (v : ℂ) ∉ entryPath ξ T d '' Icc 0 1) :
    ∃ x : ℝ, entryInv V T d (v : ℂ) = x ∧ x ≠ d ∧ IsFreeAt (entryPath ξ T d '' Icc 0 1) (x : ℂ) ∧
      entryExt V ξ T d (x : ℂ) = v := by
  have hv : 0 ≤ ((v : ℝ) : ℂ).im := by rw [ofReal_im]
  set z := entryInv V T d (v : ℂ) with hz
  have hcl := h.entryInv_mem_closure hv
  have hnot := h.entryInv_real_notMem v
  have hfr : z ∈ frontier (entryDom ξ T d) := by
    rw [h.isDomainChart'.isOpen.frontier_eq]
    exact ⟨hcl, hnot⟩
  have hsub := frontier_H_diff_fillH_subset h.isCompact_path.isBounded hfr
  rw [h.isCompact_path.isClosed.closure_eq] at hsub
  have him : z.im = 0 := hsub.resolve_right hK
  have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  refine ⟨z.re, hzr, fun hd => hK ?_, ?_, ?_⟩
  · rw [hzr, hd]
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, h.entryPath_zero⟩
  · rw [← hzr]
    exact h.isFreeAt_of_mem_closure hcl hK
  · rw [← hzr]
    exact h.entryExt_entryInv hv

/-- **The sides of the seed at an untouched real chart point.** -/
theorem IsEntryData.entryInv_sign (h : IsEntryData V T ξ p d) {v : ℝ}
    (hK : entryInv V T d (v : ℂ) ∉ entryPath ξ T d '' Icc 0 1) (h0 : entryInv V T d (v : ℂ) ≠ 0) :
    (entryInv V T d (v : ℂ)).im = 0 ∧ (v < 0 → (entryInv V T d (v : ℂ)).re < 0) ∧
      (0 < v → 0 < (entryInv V T d (v : ℂ)).re) := by
  obtain ⟨x, hx, hxd, hf, he⟩ := h.entryInv_untouched hK
  have hx0 : x ≠ 0 := fun h' => h0 (by rw [hx, h', ofReal_zero])
  rw [hx, ofReal_im, ofReal_re]
  refine ⟨rfl, fun hv => ?_, fun hv => ?_⟩
  · by_contra hcon
    have hpos : 0 < x := lt_of_le_of_ne (not_lt.1 hcon) (Ne.symm hx0)
    have := h.re_entryExt_pos hpos hxd hf
    rw [he, ofReal_re] at this
    linarith
  · by_contra hcon
    have hneg : x < 0 := lt_of_le_of_ne (not_lt.1 hcon) hx0
    have := h.re_entryExt_neg hneg
    rw [he, ofReal_re] at this
    linarith

/-- **The boundary inverse is increasing on untouched real chart points.** -/
theorem IsEntryData.re_entryInv_lt (h : IsEntryData V T ξ p d) {v₁ v₂ : ℝ} (h12 : v₁ < v₂)
    (hK₁ : entryInv V T d (v₁ : ℂ) ∉ entryPath ξ T d '' Icc 0 1)
    (hK₂ : entryInv V T d (v₂ : ℂ) ∉ entryPath ξ T d '' Icc 0 1) :
    (entryInv V T d (v₁ : ℂ)).re < (entryInv V T d (v₂ : ℂ)).re := by
  obtain ⟨x₁, hx₁, hxd₁, hf₁, he₁⟩ := h.entryInv_untouched hK₁
  obtain ⟨x₂, hx₂, hxd₂, hf₂, he₂⟩ := h.entryInv_untouched hK₂
  obtain ⟨hal₁, hF₁⟩ := h.entryExt_ofReal hxd₁ hf₁
  obtain ⟨hal₂, hF₂⟩ := h.entryExt_ofReal hxd₂ hf₂
  rw [hx₁, hx₂, ofReal_re, ofReal_re]
  have e₁ : v₁ = (fwdMap V T ((x₁ - d : ℝ) : ℂ)).re - markPosL V T (-d) := by
    have := he₁.symm.trans hF₁
    exact_mod_cast this
  have e₂ : v₂ = (fwdMap V T ((x₂ - d : ℝ) : ℂ)).re - markPosL V T (-d) := by
    have := he₂.symm.trans hF₂
    exact_mod_cast this
  by_contra hcon
  rcases (not_lt.1 hcon).lt_or_eq with hlt | heq
  · have := re_fwdMap_lt_of_alive h.tip.cont h.tip.pos.le (a := x₂ - d) (b := x₁ - d) (by linarith) hal₂ hal₁
    linarith
  · rw [heq] at e₂
    linarith

end Builder

/-! ### The original orientation -/

/-- **The reflected recentred second path contains the reflection of a recentred point exactly at the points of the
second path.** -/
theorem mem_retSet_iff' (η₂ : ℝ≥0 → ℂ) (x₁ x₂ : ℝ) (T : ℝ≥0) (z : ℂ) :
    reflectC (z - (x₁ : ℂ)) ∈ retSet (fun s : ℝ => reflectC (η₂ s.toNNReal - (x₂ : ℂ))) T (x₁ - x₂) ↔
      z ∈ η₂ '' Icc 0 T := by
  have key : ∀ t : ℝ≥0, reflectC (η₂ (t : ℝ).toNNReal - (x₂ : ℂ)) + ((x₁ - x₂ : ℝ) : ℂ) =
      reflectC (z - (x₁ : ℂ)) ↔ η₂ t = z := by
    intro t
    rw [Real.toNNReal_coe]
    have e : reflectC (η₂ t - (x₂ : ℂ)) + ((x₁ - x₂ : ℝ) : ℂ) = reflectC (η₂ t - (x₁ : ℂ)) := by
      apply Complex.ext
      · simp [reflectC]
      · simp [reflectC]
    rw [e]
    constructor
    · intro he
      have h2 := congrArg reflectC he
      rw [LP.reflectC_reflectC, LP.reflectC_reflectC] at h2
      exact sub_left_injective h2
    · intro he
      rw [he]
  constructor
  · rintro ⟨t, ht, hte⟩
    exact ⟨t, ht, (key t).1 hte⟩
  · rintro ⟨t, ht, hte⟩
    exact ⟨t, ht, (key t).2 hte⟩

namespace IsKSample

variable {U : ℝ → ℝ} {T : ℝ≥0} {ρ₂ : ℝ → ℂ} {q d : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {ρ₁ : ℝ≥0 → ℂ}
  (h : IsKSample U T ρ₂ q d w ζ ρ₁)
include h

/-- The boundary inverse of the seed is the seed. -/
theorem kInv_zero : kInv U (T : ℝ) d 0 = 0 := by
  have hE := IsPathSample.entry h
  have h1 := hE.entryInv_entryExt hE.zero_mem_closure
  rw [hE.entryExt_zero] at h1
  unfold kInv
  have e : reflectC (0 : ℂ) = 0 := by simp [reflectC]
  rw [e, h1, e]

/-- **The chart-boundary facts** for the boundary inverse in the original coordinates (first seed at `x₁`), for
any closed set `Kp` which is the completed second path together with the first seed. -/
theorem isAChart (x₁ : ℝ) {Kp : Set ℂ} (hKc : IsClosed Kp)
    (hK : ∀ z : ℂ, z ∈ Kp ↔
      reflectC (z - (x₁ : ℂ)) ∈ retSet (fun s => reflectC (ρ₂ s)) T d ∨ z = (x₁ : ℂ)) :
    RLC.AStopPath.IsAChart (fun v => kInv U (T : ℝ) d v + (x₁ : ℂ)) Kp x₁ := by
  have hE := IsPathSample.entry h
  have hret := retSet_eq (IsPathSample.tpos h) (fun s => reflectC (ρ₂ s)) d
  have hkey : ∀ r : ℝ, kInv U (T : ℝ) d (r : ℂ) + (x₁ : ℂ) ∉ Kp →
      entryInv (-U) (T : ℝ) d ((-r : ℝ) : ℂ) ∉ entryPath (fun s => reflectC (ρ₂ s)) (T : ℝ) d '' Icc 0 1 ∧
        entryInv (-U) (T : ℝ) d ((-r : ℝ) : ℂ) ≠ 0 := by
    intro r hr
    have e1 : kInv U (T : ℝ) d (r : ℂ) + (x₁ : ℂ) - (x₁ : ℂ) = kInv U (T : ℝ) d (r : ℂ) := by ring
    have e2 : reflectC (kInv U (T : ℝ) d (r : ℂ)) = entryInv (-U) (T : ℝ) d ((-r : ℝ) : ℂ) := by
      unfold kInv
      rw [LP.reflectC_reflectC, reflectC_ofReal']
    constructor
    · intro hmem
      refine hr ((hK _).2 (Or.inl ?_))
      rw [e1, e2, hret]
      exact hmem
    · intro h0
      refine hr ((hK _).2 (Or.inr ?_))
      have : kInv U (T : ℝ) d (r : ℂ) = 0 := by
        have h1 := congrArg reflectC e2
        rw [LP.reflectC_reflectC, h0] at h1
        rw [h1]
        simp [reflectC]
      rw [this, zero_add]
  have hre : ∀ r : ℝ, (kInv U (T : ℝ) d (r : ℂ) + (x₁ : ℂ)).re =
      -(entryInv (-U) (T : ℝ) d ((-r : ℝ) : ℂ)).re + x₁ := by
    intro r
    unfold kInv
    rw [reflectC_ofReal']
    simp [reflectC]
  have him : ∀ r : ℝ, (kInv U (T : ℝ) d (r : ℂ) + (x₁ : ℂ)).im =
      (entryInv (-U) (T : ℝ) d ((-r : ℝ) : ℂ)).im := by
    intro r
    unfold kInv
    rw [reflectC_ofReal']
    simp [reflectC]
  refine ⟨h.continuousOn_kInv.add continuousOn_const, hKc, fun r hr => ?_, fun r hr hr0 => ?_,
    fun r hr hr0 => ?_⟩
  · obtain ⟨h1, h2⟩ := hkey r hr
    rw [him]
    exact (hE.entryInv_sign h1 h2).1
  · obtain ⟨h1, h2⟩ := hkey r hr
    rw [hre]
    have := (hE.entryInv_sign h1 h2).2.2 (by linarith : (0 : ℝ) < -r)
    linarith
  · obtain ⟨h1, h2⟩ := hkey r hr
    rw [hre]
    have := (hE.entryInv_sign h1 h2).2.1 (by linarith : -r < (0 : ℝ))
    linarith

/-- **The boundary inverse is increasing along untouched real chart points.** -/
theorem isAMono (x₁ : ℝ) {Kp : Set ℂ}
    (hK : ∀ z : ℂ, z ∈ Kp ↔
      reflectC (z - (x₁ : ℂ)) ∈ retSet (fun s => reflectC (ρ₂ s)) T d ∨ z = (x₁ : ℂ)) :
    RLC.AStopPath.IsAMono (fun v => kInv U (T : ℝ) d v + (x₁ : ℂ)) Kp := by
  have hE := IsPathSample.entry h
  have hret := retSet_eq (IsPathSample.tpos h) (fun s => reflectC (ρ₂ s)) d
  have hkey : ∀ r : ℝ, kInv U (T : ℝ) d (r : ℂ) + (x₁ : ℂ) ∉ Kp →
      entryInv (-U) (T : ℝ) d ((-r : ℝ) : ℂ) ∉ entryPath (fun s => reflectC (ρ₂ s)) (T : ℝ) d '' Icc 0 1 := by
    intro r hr hmem
    refine hr ((hK _).2 (Or.inl ?_))
    have e1 : kInv U (T : ℝ) d (r : ℂ) + (x₁ : ℂ) - (x₁ : ℂ) = kInv U (T : ℝ) d (r : ℂ) := by ring
    have e2 : reflectC (kInv U (T : ℝ) d (r : ℂ)) = entryInv (-U) (T : ℝ) d ((-r : ℝ) : ℂ) := by
      unfold kInv
      rw [LP.reflectC_reflectC, reflectC_ofReal']
    rw [e1, e2, hret]
    exact hmem
  have hre : ∀ r : ℝ, (kInv U (T : ℝ) d (r : ℂ) + (x₁ : ℂ)).re =
      -(entryInv (-U) (T : ℝ) d ((-r : ℝ) : ℂ)).re + x₁ := by
    intro r
    unfold kInv
    rw [reflectC_ofReal']
    simp [reflectC]
  intro r₁ r₂ h12 hoff
  have h1 := hkey r₁ (hoff r₁ ⟨le_rfl, h12.le⟩)
  have h2 := hkey r₂ (hoff r₂ ⟨h12.le, le_rfl⟩)
  have := hE.re_entryInv_lt (by linarith : -r₂ < -r₁) h2 h1
  show (kInv U (T : ℝ) d (r₁ : ℂ) + (x₁ : ℂ)).re < (kInv U (T : ℝ) d (r₂ : ℂ) + (x₁ : ℂ)).re
  rw [hre, hre]
  linarith

end IsKSample

end Term

end InteractingSLE.RealContact
