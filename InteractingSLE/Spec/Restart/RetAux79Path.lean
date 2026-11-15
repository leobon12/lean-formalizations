/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7Restart
import InteractingSLE.Spec.Sec6.DrivingCriterion
import InteractingSLE.Foundations.Loewner.HullFilling
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# The chart-path facts of the canonical retained continuation (pathwise)

Packet PROVE-RETAUX79B (PROVE-RETAUX79's "What remains" R2). The later-line facts (`RetAux79.retLine_facts`) take the
continuation's chart path `γ` in capacity time with a **globally continuous** driver `W`, `IsGeneratingTrace W ζc γ`,
`γ` simple, and, at physical time `t`, the capacity `Q = C(t)` with `ψ(γ([0, Q])) = η([a, a + t])` and
`ψ(γ(Q)) = η(a + t)`. This file proves them for the canonical retained clock `Supp7.canonRetPath` (chart translation
`0`) of a retained continuation (`Supp7.IsRetCont`):

* generic (`exists_driver_of_windows`): a clock `C` on `[0, V]` (`Restart.IsClockOn`) and a continuous path `Γ` whose
  hulls `fill Γ([0, t])` are generated, on every window `[0, S] ⊆ [0, V]`, by some continuous driver at the times
  `C(t)`, have one continuous driver on `ℝ≥0` generating all of them (on `V = ∞` the window drivers agree on their
  common windows, `Sec6.eqOn_of_fwdHull_eq`, and are glued);
* `isGeneratingTrace_invClock`, `image_invClock_Icc`, `injOn_invClock`: the path read in the inverse clock is then a
  generating trace up to `capLife C V`, its initial pieces are those of `Γ`, and it is simple if `Γ` is;
* **`canonRetPath_facts`**: for a retained continuation, the canonical retained clock has a continuous driver
  with `W 0 = 0`, is a simple generating trace up to `canonRetLife`, and at every continuation time `t ≤ V` its
  capacity time `Q = C(t)` satisfies `Q ≤ canonRetLife` (`<` if `t < V`), `0 < Q` if `0 < t`,
  `ψ(γ([0, Q])) = η([a, a + t])` and `ψ(γ(Q)) = η(a + t)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE

namespace Restart.RetAux79

open Supp7

/-! ### A path read in an inverse clock -/

section Clock

variable {C : ℝ≥0 → ℝ} {V : ℝ≥0∞} {Γ : ℝ≥0 → ℂ}

/-- The initial pieces of a path read in the inverse clock are those of the path. -/
theorem image_invClock_Icc (hC : IsClockOn C V) {u : ℝ≥0} (hu : (u : ℝ≥0∞) ≤ capLife C V) :
    (fun s => Γ (invClock C V s)) '' Icc 0 u = Γ '' Icc 0 (invClock C V u) := by
  obtain ⟨hrV, hCr⟩ := hC.invClock_spec hu
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    have hsu : (s : ℝ≥0∞) ≤ capLife C V := (ENNReal.coe_le_coe.2 hs.2).trans hu
    exact ⟨invClock C V s, ⟨zero_le, hC.strictMonoOn_invClock.monotoneOn hsu hu hs.2⟩, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    have hr'V : (r : ℝ≥0∞) ≤ V := (ENNReal.coe_le_coe.2 hr.2).trans hrV
    refine ⟨(C r).toNNReal, ⟨zero_le, ?_⟩, by show Γ (invClock C V (C r).toNNReal) = Γ r; rw [hC.invClock_apply hr'V]⟩
    have h1 : C r ≤ C (invClock C V u) := hC.strictMonoOn.monotoneOn hr'V hrV hr.2
    rw [hCr] at h1
    exact (Real.toNNReal_le_iff_le_coe).2 h1

/-- A simple path read in the inverse clock is simple up to the capacity lifetime. -/
theorem injOn_invClock (hC : IsClockOn C V) (hΓ : InjOn Γ {r | (r : ℝ≥0∞) ≤ V}) :
    InjOn (fun s => Γ (invClock C V s)) {s | (s : ℝ≥0∞) ≤ capLife C V} := fun _ hs _ hs' he =>
  hC.strictMonoOn_invClock.injOn hs hs' (hΓ (hC.invClock_spec hs).1 (hC.invClock_spec hs').1 he)

theorem invClock_zero (hC : IsClockOn C V) : invClock C V 0 = 0 := by
  have h := hC.invClock_apply (r := 0) (by simp)
  rwa [hC.zero, Real.toNNReal_zero] at h

/-- **The path read in the inverse clock is a generating trace** up to the capacity lifetime, for a driver generating
the
hulls `fill Γ([0, r])` at the times `C(r)`. -/
theorem isGeneratingTrace_invClock (hC : IsClockOn C V) (hΓc : Continuous Γ) (hΓ0 : Γ 0 = 0) {W : ℝ≥0 → ℝ}
    (hW : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ V → fwdHull (fun s : ℝ => W s.toNNReal) (C r) = fillH (Γ '' Icc 0 r)) :
    IsGeneratingTrace W (capLife C V) (fun s => Γ (invClock C V s)) := by
  refine ⟨by simp only [invClock_zero hC, hΓ0], hΓc.comp_continuousOn hC.continuousOn_invClock, fun u hu => ?_⟩
  obtain ⟨hrV, hCr⟩ := hC.invClock_spec hu.le
  have hA : IsCompact ((fun s => Γ (invClock C V s)) '' Icc 0 u) := by
    rw [image_invClock_Icc hC hu.le]
    exact isCompact_Icc.image hΓc
  rw [fillH_eq_iff_isFilling_of_isClosed hA.isBounded hA.isClosed ((QuantumZipper.fwdHull_mono).2 _),
    image_invClock_Icc hC hu.le, ← hW _ hrV, hCr]

end Clock

/-! ### One driver from window drivers -/

section Glue

variable {C : ℝ≥0 → ℝ} {V : ℝ≥0∞} {Γ : ℝ≥0 → ℂ}

/-- Two drivers generating the same hulls at the clock times of a window agree on the clock range of the window. -/
theorem eqOn_of_windows (hC : IsClockOn C V) {S : ℝ≥0} (hSV : (S : ℝ≥0∞) ≤ V) {W W' : ℝ → ℝ} (hW : Continuous W)
    (hW' : Continuous W') (hW0 : W 0 = 0) (hW0' : W' 0 = 0)
    (h : ∀ t ∈ Icc 0 S, fwdHull W (C t) = fillH (Γ '' Icc 0 t))
    (h' : ∀ t ∈ Icc 0 S, fwdHull W' (C t) = fillH (Γ '' Icc 0 t)) : EqOn W W' (Icc 0 (C S)) := by
  have hcS : ContinuousOn C (Icc 0 S) :=
    hC.continuousOn.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hSV
  refine Sec6.eqOn_of_fwdHull_eq hW hW' hW0 hW0' (hC.nonneg hSV) fun s hs => ?_
  have hs' : s ∈ Icc (C 0) (C S) := by rw [hC.zero]; exact hs
  obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ S) hcS hs'
  rw [h t ht, h' t ht]

/-- **One continuous driver from window drivers**: if on every window `[0, S] ⊆ [0, V]`, `0 < S`, some continuous
driver vanishing at `0` generates the hulls `fill Γ([0, t])` at the clock times `C(t)`, then a single continuous driver
on `ℝ≥0` does so for every `t ≤ V`. -/
theorem exists_driver_of_windows (hC : IsClockOn C V) (hV : 0 < V)
    (hwin : ∀ S : ℝ≥0, 0 < S → (S : ℝ≥0∞) ≤ V → ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
      ∀ t ∈ Icc 0 S, fwdHull W (C t) = fillH (Γ '' Icc 0 t)) :
    ∃ W : ℝ≥0 → ℝ, Continuous W ∧ W 0 = 0 ∧
      ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ V → fwdHull (fun s : ℝ => W s.toNNReal) (C r) = fillH (Γ '' Icc 0 r) := by
  -- the driver read on `ℝ≥0` generates the same hulls as the driver on `ℝ`
  have hread : ∀ {W : ℝ → ℝ} (t : ℝ), 0 ≤ t →
      fwdHull (fun s : ℝ => (fun s : ℝ≥0 => W s) s.toNNReal) t = fwdHull W t := fun t ht =>
    fwdHull_eq_of_eqOn ht (lt_add_one t) fun r hr => by simp [Real.coe_toNNReal _ hr.1]
  by_cases hVt : V = ⊤
  · have hall : ∀ r : ℝ≥0, r ∈ {r : ℝ≥0 | (r : ℝ≥0∞) ≤ V} := fun r => by simp [hVt]
    -- glue the drivers of the windows `[0, n + 1]`
    have hwin' : ∀ n : ℕ, ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
        ∀ t ∈ Icc 0 ((n : ℝ≥0) + 1), fwdHull W (C t) = fillH (Γ '' Icc 0 t) := fun n =>
      hwin _ (by positivity) (by rw [hVt]; exact le_top)
    choose Wn hWnc hWn0 hWn using hwin'
    have hagree : ∀ n m : ℕ, n ≤ m → EqOn (Wn n) (Wn m) (Icc 0 (C ((n : ℝ≥0) + 1))) := fun n m hnm =>
      eqOn_of_windows hC (by rw [hVt]; exact le_top) (hWnc n) (hWnc m) (hWn0 n) (hWn0 m) (hWn n)
        fun t ht => hWn m t ⟨ht.1, ht.2.trans (by exact_mod_cast Nat.add_le_add_right hnm 1)⟩
    have hex : ∀ s : ℝ, ∃ n : ℕ, s < C ((n : ℝ≥0) + 1) := fun s => by
      obtain ⟨r, hr⟩ := hC.unbounded hVt (s + 1)
      obtain ⟨n, hn⟩ := exists_nat_ge (r : ℝ)
      have hrn : r ≤ (n : ℝ≥0) + 1 := by
        rw [← NNReal.coe_le_coe]; push_cast; linarith
      have := hC.strictMonoOn.monotoneOn (hall _) (hall _) hrn
      exact ⟨n, by linarith⟩
    classical
    set N : ℝ → ℕ := fun s => Nat.find (hex s) with hN
    have hNspec : ∀ s, s < C ((N s : ℝ≥0) + 1) := fun s => Nat.find_spec (hex s)
    -- near any point the glued driver is one window driver
    have hloc : ∀ s : ℝ, 0 ≤ s → ∀ n : ℕ, s < C ((n : ℝ≥0) + 1) → Wn (N s) s = Wn n s := by
      intro s hs n hn
      rcases le_total (N s) n with h | h
      · exact hagree _ _ h ⟨hs, (hNspec s).le⟩
      · exact (hagree _ _ h ⟨hs, hn.le⟩).symm
    set Wg : ℝ → ℝ := fun s => Wn (N s) s with hWg
    have hWgc : ContinuousOn Wg (Ici 0) := by
      intro s₀ hs₀
      have hev : Wg =ᶠ[𝓝[Ici 0] s₀] Wn (N s₀) := by
        have h1 : ∀ᶠ s in 𝓝 s₀, s < C ((N s₀ : ℝ≥0) + 1) := gt_mem_nhds (hNspec s₀)
        filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with s hs hs0
        exact hloc s hs0 _ hs
      exact ((hWnc (N s₀)).continuousWithinAt).congr_of_eventuallyEq hev (hev.eq_of_nhdsWithin hs₀)
    refine ⟨fun s => Wg s, ?_, ?_, fun r _ => ?_⟩
    · exact hWgc.comp_continuous NNReal.continuous_coe fun s => s.2
    · show Wn (N 0) 0 = 0
      exact hWn0 _
    · have hr0 : 0 ≤ C r := hC.nonneg (hall r)
      obtain ⟨n, hn⟩ := exists_nat_gt (r : ℝ)
      have hrn : r < (n : ℝ≥0) + 1 := by
        rw [← NNReal.coe_lt_coe]; push_cast; linarith
      have hCr : C r < C ((n : ℝ≥0) + 1) :=
        hC.strictMonoOn (hall _) (hall _) hrn
      have ht₂ : C r < (C r + C ((n : ℝ≥0) + 1)) / 2 := by linarith
      rw [fwdHull_eq_of_eqOn (W' := Wn n) hr0 ht₂ fun x hx => ?_, hWn n r ⟨zero_le, hrn.le⟩]
      show Wg ((x.toNNReal : ℝ≥0) : ℝ) = Wn n x
      rw [Real.coe_toNNReal _ hx.1]
      exact hloc x hx.1 n (by linarith [hx.2])
  · -- one window `[0, V]`
    have hS : 0 < V.toNNReal := ENNReal.toNNReal_pos hV.ne' hVt
    obtain ⟨W₀, hW₀c, hW₀0, hW₀⟩ := hwin _ hS (by rw [ENNReal.coe_toNNReal hVt])
    refine ⟨fun s => W₀ s, hW₀c.comp NNReal.continuous_coe, by simpa using hW₀0, fun r hr => ?_⟩
    rw [hread (C r) (hC.nonneg hr)]
    exact hW₀ r ⟨zero_le, IsClockOn.le_toNNReal hVt hr⟩

end Glue

/-! ### The canonical retained clock -/

section Canon

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {a : ℝ≥0} {O : Set ℂ} {φ ψ : ℂ → ℂ}

/-- **The chart-path facts of the canonical retained clock** (translation `0`) of a retained continuation: a continuous
driver `W` with `W 0 = 0` generating it up to `canonRetLife`; it is simple there; and at every continuation time
`t ≤ V` its capacity time `Q = C(t)` (`C` the relative capacity clock of the chart path) is at most `canonRetLife`
(strictly below if `t < V`), positive if `t` is, and `ψ ∘ γ` traces `η([a, a + t])` on `[0, Q]`, ending at
`η(a + t)`. -/
theorem canonRetPath_facts (hR : IsRetCont η ζ x a O φ ψ) :
    ∃ W : ℝ≥0 → ℝ, Continuous W ∧ W 0 = 0 ∧
      IsGeneratingTrace W (canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0)
        (canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0) ∧
      InjOn (canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0)
        {s | (s : ℝ≥0∞) ≤ canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ contLife η ζ a (O ∪ η '' Icc 0 a) →
        (((chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a))) t).toNNReal :
          ℝ≥0) : ℝ≥0∞) ≤ canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 ∧
        ((t : ℝ≥0∞) < contLife η ζ a (O ∪ η '' Icc 0 a) →
          (((chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a
            (contLife η ζ a (O ∪ η '' Icc 0 a))) t).toNNReal : ℝ≥0) : ℝ≥0∞) <
            canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0) ∧
        (0 < t → 0 < (chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a
            (contLife η ζ a (O ∪ η '' Icc 0 a))) t).toNNReal) ∧
        (fun s => ψ (canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 s)) ''
            Icc 0 (chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a
              (contLife η ζ a (O ∪ η '' Icc 0 a))) t).toNNReal = η '' Icc a (a + t) ∧
        ψ (canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0
          (chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a
            (contLife η ζ a (O ∪ η '' Icc 0 a))) t).toNNReal) = η (a + t) := by
  set K := O ∪ η '' Icc 0 a with hK
  set V := contLife η ζ a K with hVdef
  set Γ := contPath (H \ fillH K) φ η a V with hΓdef
  set C := chartClock Γ with hCdef
  have hC : IsClockOn C V := hR.isClockOn
  have hΓc : Continuous Γ := hR.continuous_contPath
  have hΓ0 : Γ 0 = 0 := hR.contPath_zero
  have hV : 0 < V := hR.pos_contLife
  have hwin : ∀ S : ℝ≥0, 0 < S → (S : ℝ≥0∞) ≤ V → ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
      ∀ t ∈ Icc 0 S, fwdHull W (C t) = fillH (Γ '' Icc 0 t) := fun S hS hSV => by
    obtain ⟨-, -, -, W, hW, hW0, hWK⟩ := hR.chartClock_spec hS hSV
    exact ⟨W, hW, hW0, fun t ht => (hWK t ht).2⟩
  obtain ⟨W, hWc, hW0, hWK⟩ := exists_driver_of_windows hC hV hwin
  have hstop : (a : ℝ≥0∞) ≤ contStop η ζ a K := hR.lt_contStop.le
  have hspec : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ V → ψ (Γ r) = η (a + r) := fun r hr => (hR.contPath_spec hr).2
  have hΓi : InjOn Γ {r | (r : ℝ≥0∞) ≤ V} := by
    intro r hr r' hr' he
    have h1 := hspec r hr
    have h2 := hspec r' hr'
    have hζ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V → ((a + s : ℝ≥0) : ℝ≥0∞) ≤ ζ := fun s hs =>
      ((coe_add_le_iff hstop).1 hs).trans contStop_le
    have := hR.path.1 (hζ r hr) (hζ r' hr') (by rw [← h1, ← h2, he])
    exact add_left_cancel this
  rw [canonRetPath_zero, canonRetLife_zero]
  refine ⟨W, hWc, hW0, isGeneratingTrace_invClock hC hΓc hΓ0 hWK, injOn_invClock hC hΓi, fun t ht => ?_⟩
  have hinv : invClock C V (C t).toNNReal = t := hC.invClock_apply ht
  have hQle := hC.coe_toNNReal_le_capLife ht
  refine ⟨hQle, fun htV => ?_, fun ht0 => ?_, ?_, ?_⟩
  · unfold capLife
    split_ifs with hVt
    · exact ENNReal.coe_lt_top
    · have hlt : t < V.toNNReal := by
        rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hVt]; exact htV
      have h1 : C t < C V.toNNReal :=
        hC.strictMonoOn ht (show ((V.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ V by rw [ENNReal.coe_toNNReal hVt]) hlt
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (hC.nonneg ht) h1)).2 h1
  · have h1 : C 0 < C t := hC.strictMonoOn (by simp) ht ht0
    rw [hC.zero] at h1
    exact Real.toNNReal_pos.2 h1
  · show (fun s => ψ (Γ (invClock C V s))) '' Icc 0 (C t).toNNReal = η '' Icc a (a + t)
    rw [← image_image (g := ψ) (f := fun s => Γ (invClock C V s)), image_invClock_Icc hC hQle, hinv]
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      refine ⟨a + r, ⟨le_self_add, add_le_add_right hr.2 a⟩, ?_⟩
      exact (hspec r ((ENNReal.coe_le_coe.2 hr.2).trans ht)).symm
    · rintro _ ⟨s, hs, rfl⟩
      have has : a + (s - a) = s := add_tsub_cancel_of_le hs.1
      have hsa : s - a ≤ t := tsub_le_iff_left.2 hs.2
      refine ⟨Γ (s - a), ⟨s - a, ⟨zero_le, hsa⟩, rfl⟩, ?_⟩
      rw [hspec _ ((ENNReal.coe_le_coe.2 hsa).trans ht), has]
  · show ψ (Γ (invClock C V (C t).toNNReal)) = η (a + t)
    rw [hinv]
    exact hspec t ht

end Canon

end Restart.RetAux79

end InteractingSLE
