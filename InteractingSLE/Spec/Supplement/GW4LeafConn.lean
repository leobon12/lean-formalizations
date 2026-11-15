/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4LeafRun
import InteractingSLE.Spec.Supplement.G12RemSwallow
import InteractingSLE.Spec.ZhanGT4.A2TipSepGeom

/-!
# Real points are first visited from the far end inwards (deterministic)

Packet PROVE-T14-GW4REG. GW1's walks contain original-boundary connectors (GW4's proof, p. 637: "every
original-real connector is itself visited"). Along a connector moving away from the target `0`, the counterflow
(coming from `∞`) first visits the points in strict reverse order. This is a deterministic fact about Loewner chains
(the "swallowing" of real points; G12's remainder, supplement p. 506: "a trace-free upper half-neighborhood inside that
filled hull … cannot subsequently be visited from the active domain"):

* `exists_isForwardSol_of_lt_of_isForwardSol`: for `0 < x < y`, if `x` is alive on `[0, T]` so is `y` (comparison of
  real Loewner flows; `SwallowReal`);
* `trace_ne_of_real_swallowed`: if the trace is at a real point `a` at time `T`, a real point `b` strictly between `0`
  and `a` not visited by time `T` is never visited (it is not alive at `T`, so a half-disc around it lies in `K_T`);
* **`firstVisit_lt_of_real_farther`**: in physical coordinates (`p = −1/γ`), a visited real point farther from `0`
  than a real point `p` on the same side is first visited strictly before `p`;
* **`connVisitOK_of_real`**: hence the first-visit data `ConnVisitOK` of a real connector moving away from `0` all of
  whose points are visited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull IsForwardSol fwdMap)

namespace InteractingSLE

namespace Theorem14

namespace GW4Leaf

/-! ### Comparison of real flows -/

/-- **A real point farther from the driver stays alive longer** (positive side): for `0 < x < y`, if `x` is alive on
`[0, T]` then so is `y`. -/
theorem exists_isForwardSol_of_lt_of_isForwardSol {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {x y T : ℝ} (hx : 0 < x) (hxy : x < y) (hT : 0 ≤ T) (halive : ∃ v, IsForwardSol W (x : ℂ) T v) :
    ∃ v, IsForwardSol W (y : ℂ) T v := by
  by_contra hdead
  obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt hW hW0 (hx.trans hxy) hT hdead
  obtain ⟨v, hv⟩ := halive
  obtain ⟨c, hc, hcle⟩ := exists_pos_le_re_of_isForwardSol hW hW0 hx hT hv
  apply hsw.2.2
  refine exists_isForwardSol_of_forall_lt hW hW0 hsw.1 hsw.2.1 hc fun s hs => ?_
  obtain ⟨w, hw⟩ := hsw.2.1 s hs
  have hsT : s ≤ T := hs.2.le.trans hσ.2
  have hvs : IsForwardSol W (x : ℂ) s v := QuantumZipper.isForwardSol_restrict hv hs.1 hsT
  have hlt := re_lt_of_isForwardSol hW hW0 hx hxy hvs hw s ⟨hs.1, le_rfl⟩
  rw [fwdMap_eq_of_isForwardSol hW hw ⟨hs.1, le_rfl⟩]
  have := hcle s ⟨hs.1, hsT⟩
  linarith

/-- The mirror comparison (negative side): for `y < x < 0`, if `x` is alive on `[0, T]` so is `y`. -/
theorem exists_isForwardSol_of_lt_of_isForwardSol_neg {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {x y T : ℝ} (hx : x < 0) (hyx : y < x) (hT : 0 ≤ T) (halive : ∃ v, IsForwardSol W (x : ℂ) T v) :
    ∃ v, IsForwardSol W (y : ℂ) T v := by
  have hW' : Continuous fun t => -W t := hW.neg
  have hW0' : (fun t => -W t) 0 = 0 := by simp [hW0]
  rw [← exists_isForwardSol_neg_iff] at halive ⊢
  exact exists_isForwardSol_of_lt_of_isForwardSol hW' hW0' (neg_pos.2 hx) (neg_lt_neg hyx) hT halive

/-! ### A swallowed real point is never visited -/

/-- **A real point swallowed off the trace is never visited.** If the generating trace `γ` (of a continuous driver
from `0`, on `[0, ∞)`) is at the real point `a` at time `T`, and `b` lies strictly between `0` and `a` and is not on
`γ([0, T])`, then `γ` never visits `b`. -/
theorem trace_ne_of_real_swallowed {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hγ : IsGeneratingTrace W ⊤ γ) {T : ℝ≥0} {a b : ℝ} (ha : γ T = a)
    (hab : (a < b ∧ b < 0) ∨ (0 < b ∧ b < a)) (hoff : ∀ s : ℝ≥0, s ≤ T → γ s ≠ b) :
    ∀ t : ℝ≥0, γ t ≠ b := by
  intro t ht
  have hTt : T < t := by
    by_contra h
    exact hoff t (not_lt.1 h) ht
  set U : ℝ → ℝ := fun s => W s.toNNReal with hUdef
  have hU : Continuous U := hW.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simp [U, hW0]
  have ha0 : a ≠ 0 := by
    rcases hab with h | h
    · exact (h.1.trans h.2).ne
    · exact (h.1.trans h.2).ne'
  have hb0 : b ≠ 0 := by
    rcases hab with h | h
    · exact h.2.ne
    · exact h.1.ne'
  have hγ0 : γ 0 = 0 := by simpa using hγ.1
  have hT0 : (0 : ℝ) < T := by
    refine NNReal.coe_pos.2 (pos_iff_ne_zero.2 fun h => ha0 ?_)
    rw [h, hγ0] at ha
    exact_mod_cast ha.symm
  have hT2 : (T : ℝ) < (t : ℝ) + 1 := by
    have : (T : ℝ) < t := hTt
    linarith
  have hL : InteractingSLE.IsLoewnerTraceLT U (((t + 1 : ℝ≥0) : ℝ)) (fun s : ℝ => γ s.toNNReal) :=
    GB7a.isLoewnerTraceLT_of_agree hγ le_top fun s _ _ => rfl
  have hT2' : (T : ℝ) < ((t + 1 : ℝ≥0) : ℝ) := by rw [NNReal.coe_add, NNReal.coe_one]; exact hT2
  -- `a` is not alive at `T`
  have hacl : (a : ℂ) ∈ closure (fwdHull U T) := by
    have h := Supp7.G12.trace_mem_closure_fwdHull hU hU0 hL hT0 hT2'
    simpa [Real.toNNReal_coe, ha] using h
  have hadead : ¬ ∃ v, IsForwardSol U (a : ℂ) T v := fun ⟨v, hv⟩ =>
    ZhanGT4.A2TipSep.not_mem_closure_fwdHull_of_isForwardSol hU T.coe_nonneg hv hacl
  -- so is `b`
  have hbdead : ¬ ∃ v, IsForwardSol U (b : ℂ) T v := by
    intro hb
    apply hadead
    rcases hab with h | h
    · exact exists_isForwardSol_of_lt_of_isForwardSol_neg hU hU0 h.2 h.1 T.coe_nonneg hb
    · exact exists_isForwardSol_of_lt_of_isForwardSol hU hU0 h.1 h.2 T.coe_nonneg hb
  -- a half-disc around `b` lies in `K_T`
  have hbη : (b : ℂ) ∉ (fun s : ℝ => γ s.toNNReal) '' Icc 0 (T : ℝ) := by
    rintro ⟨s, hs, hse⟩
    exact hoff s.toNNReal (Real.toNNReal_le_iff_le_coe.2 hs.2) hse
  have hcl : (b : ℂ) ∉ closure (H \ fwdHull U T) := fun hcl =>
    hbdead (GB7a.exists_isForwardSol_of_mem_closure hU hU0 hL T.coe_nonneg hT2' hb0 hbη hcl)
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ z ∈ H \ fwdHull U T, r ≤ dist (b : ℂ) z := by
    by_contra hne
    push Not at hne
    exact hcl (Metric.mem_closure_iff.2 fun ε hε => by
      obtain ⟨z, hz, hzd⟩ := hne ε hε
      exact ⟨z, hz, hzd⟩)
  refine Supp7.G11.false_of_hull_stable hγ hW.continuousOn hW0 (lt_of_le_of_lt zero_le hTt) le_top
    (U := ball (b : ℂ) r) isOpen_ball (by rw [ht]; exact mem_ball_self hr)
    (ε := (t : ℝ) - T) (by have : (T : ℝ) < t := hTt; linarith) fun s₁ s₂ hs₁ _ _ z hz => ?_
  have hzH : z ∈ H := (QuantumZipper.fwdHull_mono.2 _) hz.2
  have hzK : z ∈ fwdHull U T := by
    by_contra hzK
    have := hball z ⟨hzH, hzK⟩
    have hz1 := hz.1
    rw [mem_ball, dist_comm] at hz1
    linarith
  exact QuantumZipper.fwdHull_mono.1 (show (T : ℝ) ≤ s₁ by linarith) hzK

/-! ### Physical coordinates -/

theorem eq_neg_inv_of_neg_inv_eq {z w : ℂ} (h : -z⁻¹ = w) : z = -w⁻¹ := by
  rw [← h, inv_neg, inv_inv, neg_neg]

/-- **A visited real point farther from the target is first visited earlier**: for real `p, p'` on the same side of
`0` with `p'` strictly farther from `0` (`0 ≤ p < p'` or `p' < p ≤ 0`), if the physical counterflow `−1/γ` visits `p'`,
it first visits `p'` strictly before `p`. -/
theorem firstVisit_lt_of_real_farther {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hγ : IsGeneratingTrace W ⊤ γ) {p p' : ℝ} (hp : (0 ≤ p ∧ p < p') ∨ (p' < p ∧ p ≤ 0))
    (hvis : ∃ t, γ t ≠ 0 ∧ -(γ t)⁻¹ = (p' : ℂ)) :
    GB11.firstVisit γ (p' : ℂ) < GB11.firstVisit γ (p : ℂ) := by
  have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
  obtain ⟨t₁, ht₁0, ht₁⟩ := hvis
  have hfin : GB11.firstVisit γ (p' : ℂ) < ⊤ :=
    lt_of_le_of_lt (ht₁ ▸ GB11.firstVisit_le ht₁0) ENNReal.coe_lt_top
  by_cases hpv : GB11.firstVisit γ (p : ℂ) = ⊤
  · rw [hpv]; exact hfin
  obtain ⟨T, hT, hγT0, hγT⟩ := GW4Reg.exists_eq_firstVisit hγc (lt_top_iff_ne_top.2 hpv)
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, Complex.ofReal_zero, neg_eq_zero, inv_eq_zero] at hγT
    exact hγT0 hγT
  set a : ℝ := -p⁻¹ with hadef
  set b : ℝ := -p'⁻¹ with hbdef
  have haT : γ T = a := by rw [eq_neg_inv_of_neg_inv_eq hγT, hadef]; push_cast; ring
  have hbt : γ t₁ = b := by rw [eq_neg_inv_of_neg_inv_eq ht₁, hbdef]; push_cast; ring
  have hab : (a < b ∧ b < 0) ∨ (0 < b ∧ b < a) := by
    rcases hp with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · have hp0' : 0 < p := lt_of_le_of_ne h0 (Ne.symm hp0)
      have hp'0 : 0 < p' := hp0'.trans h1
      refine Or.inl ⟨?_, ?_⟩
      · simp only [hadef, hbdef, neg_lt_neg_iff]
        exact inv_strictAnti₀ hp0' h1
      · simp only [hbdef, neg_lt_zero, inv_pos]; exact hp'0
    · have hp0' : p < 0 := lt_of_le_of_ne h0 hp0
      have hp'0 : p' < 0 := h1.trans hp0'
      refine Or.inr ⟨?_, ?_⟩
      · simp only [hbdef, neg_pos, inv_lt_zero]; exact hp'0
      · simp only [hadef, hbdef, neg_lt_neg_iff]
        exact (inv_lt_inv_of_neg hp0' hp'0).2 h1
  rw [← hT]
  by_contra hle
  push Not at hle
  have hoff : ∀ s : ℝ≥0, s ≤ T → γ s ≠ b := by
    intro s hs hsb
    have hs0 : γ s ≠ 0 := by
      rw [hsb]
      exact_mod_cast (hab.elim (fun h => h.2.ne) (fun h => h.1.ne'))
    have hvs : -(γ s)⁻¹ = (p' : ℂ) := by
      rw [hsb, hbdef]; push_cast; rw [inv_neg, inv_inv, neg_neg]
    have h1 : GB11.firstVisit γ (p' : ℂ) ≤ s := hvs ▸ GB11.firstVisit_le hs0
    rcases hs.lt_or_eq with hs' | hs'
    · exact absurd (lt_of_le_of_lt h1 (ENNReal.coe_lt_coe.2 hs')) (not_lt.2 hle)
    · rw [hs', haT] at hsb
      have := Complex.ofReal_injective hsb
      rcases hab with h | h
      · exact h.1.ne this
      · exact h.2.ne' this
  exact trace_ne_of_real_swallowed hW hW0 hγ haT hab hoff t₁ hbt

/-! ### The first-visit data of a real connector -/

/-- **A real connector moving away from `0`, all of whose points are visited, has its first-visit data.** -/
theorem connVisitOK_of_real {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hγ : IsGeneratingTrace W ⊤ γ) {q : ℝ} {φ : ℝ≥0 → ℝ} {S : ℝ≥0∞} (hφ0 : φ 0 = q)
    (hdir : (0 ≤ q ∧ ∀ t t' : ℝ≥0, t < t' → (t' : ℝ≥0∞) ≤ S → φ t < φ t') ∨
      (q ≤ 0 ∧ ∀ t t' : ℝ≥0, t < t' → (t' : ℝ≥0∞) ≤ S → φ t' < φ t))
    (hvis : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → ∃ s, γ s ≠ 0 ∧ -(γ s)⁻¹ = ((φ t : ℝ) : ℂ)) :
    ConnVisitOK γ q (fun t => ((φ t : ℝ) : ℂ)) S := by
  refine ⟨fun t t' ht htt ht' => ?_, fun t ht htS => ?_⟩
  · have htS : (t : ℝ≥0∞) ≤ S := le_trans (ENNReal.coe_le_coe.2 htt.le) ht'
    apply firstVisit_lt_of_real_farther hW hW0 hγ _ (hvis t' (ht.trans htt) ht')
    rcases hdir with ⟨hq, hm⟩ | ⟨hq, hm⟩
    · have h0 : q < φ t := by rw [← hφ0]; exact hm 0 t ht htS
      exact Or.inl ⟨hq.trans h0.le, hm t t' htt ht'⟩
    · have h0 : φ t < q := by rw [← hφ0]; exact hm 0 t ht htS
      exact Or.inr ⟨hm t t' htt ht', h0.le.trans hq⟩
  · apply firstVisit_lt_of_real_farther hW hW0 hγ _ (hvis t ht htS)
    rcases hdir with ⟨hq, hm⟩ | ⟨hq, hm⟩
    · have h0 : q < φ t := by rw [← hφ0]; exact hm 0 t ht htS
      exact Or.inl ⟨hq, h0⟩
    · have h0 : φ t < q := by rw [← hφ0]; exact hm 0 t ht htS
      exact Or.inr ⟨h0, hq⟩

open GW1WalkChain in
theorem realArc_eq (q x : ℝ) (t : ℝ≥0) :
    realArc q x t = (((q + (t : ℝ) * (x - q) : ℝ)) : ℂ) := by
  change ((AffineMap.lineMap q x (t : ℝ) : ℝ) : ℂ) = _
  rw [AffineMap.lineMap_apply_ring']
  congr 1
  ring

open GW1WalkChain in
/-- **The first-visit data of a finite real connector** from `q ≥ 0` rightwards or from `q ≤ 0` leftwards, all of
whose points after `q` are visited. -/
theorem connVisitOK_realArc {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hγ : IsGeneratingTrace W ⊤ γ) {q x : ℝ} (hdir : (0 ≤ q ∧ q < x) ∨ (q ≤ 0 ∧ x < q))
    (hvis : ∀ t : ℝ≥0, 0 < t → t ≤ 1 → ∃ s, γ s ≠ 0 ∧ -(γ s)⁻¹ = realArc q x t) :
    ConnVisitOK γ q (realArc q x) 1 := by
  have hfun : realArc q x = fun t : ℝ≥0 => (((q + (t : ℝ) * (x - q) : ℝ)) : ℂ) := funext (realArc_eq q x)
  rw [hfun]
  refine connVisitOK_of_real hW hW0 hγ (by simp) ?_ fun t ht ht1 => ?_
  · rcases hdir with ⟨hq, hqx⟩ | ⟨hq, hxq⟩
    · refine Or.inl ⟨hq, fun t t' htt _ => ?_⟩
      have : (t : ℝ) < t' := htt
      nlinarith
    · refine Or.inr ⟨hq, fun t t' htt _ => ?_⟩
      have : (t : ℝ) < t' := htt
      nlinarith
  · obtain ⟨s, hs0, hs⟩ := hvis t ht (by exact_mod_cast ht1)
    exact ⟨s, hs0, hs.trans (realArc_eq q x t)⟩

open GW1WalkChain in
/-- **The first-visit data of a terminal real ray** from `q ≥ 0` rightwards or from `q ≤ 0` leftwards, all of whose
points after `q` are visited. -/
theorem connVisitOK_realRay {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hγ : IsGeneratingTrace W ⊤ γ) {q : ℝ} {right : Bool} (hdir : (right = true ∧ 0 ≤ q) ∨ (right = false ∧ q ≤ 0))
    (hvis : ∀ t : ℝ≥0, 0 < t → ∃ s, γ s ≠ 0 ∧ -(γ s)⁻¹ = realRay right q t) :
    ConnVisitOK γ q (realRay right q) ⊤ := by
  rcases hdir with ⟨rfl, hq⟩ | ⟨rfl, hq⟩
  · have hfun : realRay true q = fun t : ℝ≥0 => (((q + (t : ℝ) : ℝ)) : ℂ) := by
      funext t; simp [realRay]
    rw [hfun]
    refine connVisitOK_of_real hW hW0 hγ (by simp) (Or.inl ⟨hq, fun t t' htt _ => ?_⟩) fun t ht _ => ?_
    · have : (t : ℝ) < t' := htt
      linarith
    · obtain ⟨s, hs0, hs⟩ := hvis t ht
      exact ⟨s, hs0, by rw [hs]; simp [realRay]⟩
  · have hfun : realRay false q = fun t : ℝ≥0 => (((q - (t : ℝ) : ℝ)) : ℂ) := by
      funext t; simp [realRay]
    rw [hfun]
    refine connVisitOK_of_real hW hW0 hγ (by simp) (Or.inr ⟨hq, fun t t' htt _ => ?_⟩) fun t ht _ => ?_
    · have : (t : ℝ) < t' := htt
      linarith
    · obtain ⟨s, hs0, hs⟩ := hvis t ht
      exact ⟨s, hs0, by rw [hs]; simp [realRay]⟩

end GW4Leaf

end Theorem14

end InteractingSLE
