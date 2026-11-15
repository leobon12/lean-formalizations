/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61LocLanding

/-!
# Rational windows for a fresh eastern excursion in the counterflow chart (Aux. lemma 64's localization)

Packet PROVE-AUX61-R23, piece R6 (the countable localization). Sources: Aux. lemma 64 (`source/spec/p241-288.md`,
p. 265: "On an outcome with a continuous first endpoint …, that segment, completed by its endpoint, is compact …
countably many rational radius and clearance bounds cover all such segments") and Astra's follow-up 4, Part (1), §1.3
"One density through the endpoint" and §1.6 (`source/external/AstraIG1/ig1_followup4_audited.txt` L215–L224,
L316–L331; ruling R71).

In the counterflow chart `Ψ = revChart w s` of `ℍ ∖ R(K_s)` an (E1)-violation is an `Aux61Loc.IsEastCrosscut`: the
excursion of the flow line `η` from its last contact `τ₀` lands, at its end time `u₀`, at a point `x₁` of the eastern
side `(junR, ∞)`. For a restart time `t ∈ (τ₀, u₀)` this file chooses, **deterministically and from a countable
family**, a window around the completed excursion in the chart `Ψ`:

* `WinCode`: finitely many rational discs, a rational interval `(q₁, q₂)` and a rational clearance `δ`;
* `IsWindow w s η t c`: `0 < δ < t`, `junR < q₁`, the real points of the closed window lie in `(q₁, q₂)`, and the
  closed window is disjoint from the closure of the chart image of the old flow prefix `η([0, t − δ])`
  (`oldChartSet`);
* `WindowExcursion w s η t c u₀`: a contact before `t − δ`, no contact on `[t − δ, t]`, and the excursion runs in
  the window on `(t, u₀)` and lands at a real point as `u ↑ u₀`;
* **`exists_isWindow`**: every `IsEastCrosscut w s η τ₀ u₀` and every `t ∈ (τ₀, u₀)` have such a code.

The proof: the completed excursion `C = Ψ ∘ η([t, u₀)) ∪ {x₁}` is compact; it is disjoint from the closure of the old
chart set (`disjoint_closure_oldChartSet`): an old point accumulating at a point of `C` would, through the inverse
chart (continuous on `ℍ`, `tendsto_of_revChart_tendsto_interior`, and at `x₁` through the continuous boundary
extension of `F_s`, `tendsto_of_revChart_tendsto_end`),
give an old time `v ≤ t − δ` with `η(v) = η(u)`, `u ≥ t`, which injectivity excludes (`notMem_closure_oldChartSet_of`).
The real points of `C` reduce to `x₁`, so a closed thickening of `C` meets `ℝ` only near `x₁`; a finite cover of `C`
by rational discs inside that thickening (`exists_finset_disc_cover`) is the window.

Deterministic; nothing here replaces a source theorem. R48: no Theorem 1.2/1.3 hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Aux61Kernel

open WangWu hiding ratPt exists_ratPt_dist_lt
open CrossCond.Word49 Prop51G Prop51H Prop51I Aux61Loc

/-! ### The right junction is nonnegative -/

/-- **`junR ≥ 0`**: the left image `−rightImg(−w)(0)(s)` of `0⁻` is at most the driver `w s`, so the junction
`junR = −1/(−rightImg(−w)(0)(s) − w s)` is `−1` over a nonpositive number. -/
theorem junR_nonneg {w : ℝ → ℝ} (hw : Continuous w) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ junR w s := by
  have hle : -w s ≤ MartChar.RealFlow.rightImg (fun r => -w r) 0 s :=
    le_csInf (MartChar.RealFlow.imgSet_nonempty hw.neg 0 hs) fun _ ⟨_, _, hy, hg⟩ =>
      hg ▸ (hy.lt_gImg hw.neg ⟨hs, le_rfl⟩).le
  rw [junR]
  exact div_nonneg_of_nonpos (by norm_num) (by linarith)

/-! ### Rational windows -/

/-- **A window code**: a finite set of rational discs `(a, b, r)` (centre `a + b i`, radius `r`), and the rationals
`q₁`, `q₂` (the target interval) and `δ` (the clearance before the restart time). -/
abbrev WinCode : Type := Finset (ℚ × ℚ × ℚ) × ℚ × ℚ × ℚ

/-- The open disc of a rational triple `(a, b, r)`. -/
def ratDisc (d : ℚ × ℚ × ℚ) : Set ℂ := ball (((d.1 : ℝ) : ℂ) + ((d.2.1 : ℝ) : ℂ) * I) (d.2.2 : ℝ)

/-- **The window of a code**: the union of its rational discs. -/
def winSet (c : WinCode) : Set ℂ := ⋃ d ∈ c.1, ratDisc d

theorem isOpen_winSet (c : WinCode) : IsOpen (winSet c) :=
  isOpen_biUnion fun _ _ => isOpen_ball

theorem isBounded_winSet (c : WinCode) : Bornology.IsBounded (winSet c) :=
  (Bornology.isBounded_biUnion c.1.finite_toSet).2 fun _ _ => isBounded_ball

/-- **The chart image of the old flow prefix**: `Ψ(η(v))` for the times `v ∈ [0, r]` with `η(v) ∈ ℍ ∖ R(K_s)`. -/
def oldChartSet (w : ℝ → ℝ) (s : ℝ) (η : ℝ → ℂ) (r : ℝ) : Set ℂ :=
  (fun v => revChart w s (η v)) '' {v | v ∈ Icc 0 r ∧ η v ∈ H \ cfHullQ w s}

/-- **A window for the restart at `t`** (deterministic in the histories up to `t` and the counterflow): the clearance
`δ ∈ (0, t)`, the target interval `(q₁, q₂)` right of the junction, the real points of the closed window in
`(q₁, q₂)`, and the closed window disjoint from the closure of the chart image of `η([0, t − δ])`. -/
structure IsWindow (w : ℝ → ℝ) (s : ℝ) (η : ℝ → ℂ) (t : ℝ) (c : WinCode) : Prop where
  δ_pos : 0 < (c.2.2.2 : ℝ)
  δ_lt : (c.2.2.2 : ℝ) < t
  east : junR w s < c.2.1
  real : ∀ z ∈ closure (winSet c), z.im = 0 → (c.2.1 : ℝ) < z.re ∧ z.re < c.2.2.1
  old : Disjoint (closure (winSet c)) (closure (oldChartSet w s η (t - c.2.2.2)))

/-- **The excursion of the window event**: a contact before `t − δ`, no contact on `[t − δ, t]`, and the excursion
of `η` in `ℍ ∖ R(K_s)` running at `t` stays (in the chart `Ψ`) in the window on `(t, u₀)` and lands at a real point as
`u ↑ u₀`. -/
def WindowExcursion (w : ℝ → ℝ) (s : ℝ) (η : ℝ → ℂ) (t : ℝ) (c : WinCode) (u₀ : ℝ) : Prop :=
  (∃ τ₀ ∈ Ioo 0 (t - c.2.2.2), η τ₀ ∉ H \ cfHullQ w s) ∧
    (∀ v ∈ Icc (t - c.2.2.2) t, η v ∈ H \ cfHullQ w s) ∧ t < u₀ ∧
    (∀ v ∈ Ioo t u₀, η v ∈ H \ cfHullQ w s ∧ revChart w s (η v) ∈ winSet c) ∧
    ∃ x₁ : ℝ, Tendsto (fun u => revChart w s (η u)) (𝓝[<] u₀) (𝓝 (x₁ : ℂ))

/-- The landing point of a window excursion lies in the target interval `(q₁, q₂)`. -/
theorem WindowExcursion.landing_mem {w : ℝ → ℝ} {s : ℝ} {η : ℝ → ℂ} {t u₀ : ℝ} {c : WinCode}
    (hW : IsWindow w s η t c) (hE : WindowExcursion w s η t c u₀) {x₁ : ℝ}
    (hx₁ : Tendsto (fun u => revChart w s (η u)) (𝓝[<] u₀) (𝓝 (x₁ : ℂ))) :
    (c.2.1 : ℝ) < x₁ ∧ x₁ < c.2.2.1 := by
  obtain ⟨-, -, htu, hin, -⟩ := hE
  have hmem : (x₁ : ℂ) ∈ closure (winSet c) := by
    refine mem_closure_of_tendsto hx₁ ?_
    filter_upwards [Ioo_mem_nhdsLT htu] with u hu using (hin u hu).2
  simpa using hW.real _ hmem (by simp)

/-! ### Finite rational disc covers -/

/-- **A compact set of `ℂ` has a finite cover by rational discs inside any thickening of it.** -/
theorem exists_finset_disc_cover {C : Set ℂ} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (ℚ × ℚ × ℚ), C ⊆ ⋃ d ∈ F, ratDisc d ∧ ∀ d ∈ F, ratDisc d ⊆ thickening ε C := by
  classical
  set good : ℚ × ℚ × ℚ → Prop := fun d => ratDisc d ⊆ thickening ε C with hgood
  set U : ℚ × ℚ × ℚ → Set ℂ := fun d => if good d then ratDisc d else ∅ with hU
  have hUo : ∀ d, IsOpen (U d) := fun d => by
    simp only [hU]
    split_ifs
    · exact isOpen_ball
    · exact isOpen_empty
  have hcov : C ⊆ ⋃ d, U d := by
    intro z hz
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - ε / 8 < z.re + ε / 8 by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - ε / 8 < z.im + ε / 8 by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
    have hc : dist (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I) z < ε / 4 := by
      rw [dist_eq_norm]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
      simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, sub_im, add_im, mul_im, zero_add]
      have h1 : |(a : ℝ) - z.re| < ε / 8 := abs_lt.2 ⟨by linarith, by linarith⟩
      have h2 : |(b : ℝ) - z.im| < ε / 8 := abs_lt.2 ⟨by linarith, by linarith⟩
      linarith
    refine mem_iUnion.2 ⟨(a, b, r), ?_⟩
    have hg : good (a, b, r) := by
      intro y hy
      refine mem_thickening_iff.2 ⟨z, hz, ?_⟩
      have hy' : dist y (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I) < r := hy
      linarith [dist_triangle y (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I) z]
    simp only [hU, hg, ↓reduceIte]
    show dist z (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I) < (r : ℝ)
    rw [dist_comm]
    linarith
  obtain ⟨F₀, hF₀⟩ := hC.elim_finite_subcover U hUo hcov
  refine ⟨F₀.filter good, fun z hz => ?_, fun d hd => (Finset.mem_filter.1 hd).2⟩
  obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.1 (hF₀ hz)
  have hg : good d := by
    by_contra hng
    simp only [hU, hng, ↓reduceIte] at hzd
    exact hzd
  simp only [hU, hg, ↓reduceIte] at hzd
  exact mem_iUnion₂.2 ⟨d, Finset.mem_filter.2 ⟨hd, hg⟩, hzd⟩

/-! ### The completed excursion avoids the old chart set -/

section Old

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ} {η : ℝ → ℂ}

/-- **An old chart point cannot accumulate at a point whose physical preimage is a later point of `η`**: if every
sequence of old times `v_n ∈ [0, r]` (with `η(v_n) ∈ ℍ ∖ R(K_s)`) whose chart images tend to `z` has `η(v_n) → η(u')`
for a time `u' > r`, then `z` is not in the closure of the old chart set (compactness of `[0, r]` and injectivity of
the proper arc `η`). -/
theorem notMem_closure_oldChartSet_of (hη : IsProperArc η) {r u' : ℝ} (hru : r < u') {z : ℂ}
    (hz : ∀ v : ℕ → ℝ, (∀ n, v n ∈ Icc 0 r ∧ η (v n) ∈ H \ cfHullQ w s) →
      Tendsto (fun n => revChart w s (η (v n))) atTop (𝓝 z) →
        Tendsto (fun n => η (v n)) atTop (𝓝 (η u'))) :
    z ∉ closure (oldChartSet w s η r) := by
  intro hzc
  obtain ⟨x, hxO, hxlim⟩ := mem_closure_iff_seq_limit.1 hzc
  choose v hv hvx using hxO
  obtain ⟨a, ha, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq fun n => (hv n).1
  have h1 : Tendsto (fun n => η (v (φ n))) atTop (𝓝 (η u')) :=
    hz (v ∘ φ) (fun n => hv (φ n)) ((hxlim.comp hφ.tendsto_atTop).congr fun n => (hvx (φ n)).symm)
  have h2 : Tendsto (fun n => η (v (φ n))) atTop (𝓝 (η a)) :=
    (hη.cont a ha.1).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => (hv (φ n)).1.1⟩)
  have he : η a = η u' := tendsto_nhds_unique h2 h1
  have hau := hη.inj (mem_Ici.2 ha.1) (mem_Ici.2 (ha.1.trans (ha.2.trans hru.le))) he
  linarith [ha.2]

/-- **At an interior point the inverse chart is continuous**: chart images tending to `Ψ(η(u))`, `η(u) ∈ ℍ ∖ R(K_s)`,
come from points tending to `η(u)`. -/
theorem tendsto_of_revChart_tendsto_interior (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {u : ℝ}
    (hu : η u ∈ H \ cfHullQ w s) (v : ℕ → ℝ) (hv : ∀ n, η (v n) ∈ H \ cfHullQ w s)
    (hlim : Tendsto (fun n => revChart w s (η (v n))) atTop (𝓝 (revChart w s (η u)))) :
    Tendsto (fun n => η (v n)) atTop (𝓝 (η u)) := by
  have hzH := revChart_mem_H hw hs hu
  have hc : ContinuousAt (revChartInv w s) (revChart w s (η u)) :=
    (continuousOn_revChartInv hw hw0 hs).continuousAt (QuantumZipper.isOpen_H.mem_nhds hzH)
  have h := hc.tendsto.comp hlim
  rw [revChartInv_revChart hw hw0 hs hu] at h
  exact h.congr fun n => revChartInv_revChart hw hw0 hs (hv n)

/-- **At the landing point the inverse chart is continuous** (through the continuous boundary extension `F` of
`F_s = f_s⁻¹`): if the excursion of `η` in `ℍ ∖ R(K_s)` on `(a, u₀)` lands at the real point `x₁ ≠ 0` of the chart
`Ψ` as `u ↑ u₀`, then chart images of points of `ℍ ∖ R(K_s)` tending to `x₁` come from points tending to `η(u₀)`.
(`Ψ⁻¹ = R ∘ F ∘ R` on `ℍ`; `F(R x₁) ≠ 0`, since otherwise `η(u) → ∞` along the excursion.) -/
theorem tendsto_of_revChart_tendsto_end (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hβ : IsLoewnerTrace w β) (hs : 0 ≤ s) {a u₀ : ℝ} (hau : a < u₀) (ha0 : 0 ≤ a)
    (hD : ∀ u ∈ Ioo a u₀, η u ∈ H \ cfHullQ w s) {x₁ : ℝ} (hx₁ : x₁ ≠ 0)
    (hland : Tendsto (fun u => revChart w s (η u)) (𝓝[<] u₀) (𝓝 (x₁ : ℂ)))
    (v : ℕ → ℝ) (hv : ∀ n, η (v n) ∈ H \ cfHullQ w s)
    (hlim : Tendsto (fun n => revChart w s (η (v n))) atTop (𝓝 (x₁ : ℂ))) :
    Tendsto (fun n => η (v n)) atTop (𝓝 (η u₀)) := by
  obtain ⟨F, hFeq, hFc, -⟩ := hβ.exists_extension hw hw0 hs
  have hinv : ∀ z ∈ H \ cfHullQ w s, z = negInv (F (negInv (revChart w s z))) := fun z hz => by
    have hzH := revChart_mem_H hw hs hz
    rw [hFeq (negInv_mem_H hzH)]
    exact (revChartInv_revChart hw hw0 hs hz).symm
  set ξ := F (negInv (x₁ : ℂ)) with hξ
  have hHb : ∀ {z : ℂ}, z ∈ H → z ∈ Hbar := fun {z} hz => show (0 : ℝ) ≤ z.im from le_of_lt hz
  have hxr : negInv (x₁ : ℂ) ∈ Hbar := by
    show (0 : ℝ) ≤ (negInv (x₁ : ℂ)).im
    simp [negInv]
  have hFlimN : ∀ {g : ℕ → ℂ}, (∀ n, g n ∈ H) → Tendsto g atTop (𝓝 (x₁ : ℂ)) →
      Tendsto (fun n => F (negInv (g n))) atTop (𝓝 ξ) := fun {g} hgH hg => by
    have h1 : Tendsto (fun n => negInv (g n)) atTop (𝓝 (negInv (x₁ : ℂ))) :=
      (continuousAt_negInv (ofReal_ne_zero.2 hx₁)).tendsto.comp hg
    exact (hFc _ hxr).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall fun n => hHb (negInv_mem_H (hgH n))⟩)
  have hev : ∀ᶠ u in 𝓝[<] u₀, η u ∈ H \ cfHullQ w s := mem_of_superset (Ioo_mem_nhdsLT hau) hD
  have hξc : Tendsto (fun u => F (negInv (revChart w s (η u)))) (𝓝[<] u₀) (𝓝 ξ) := by
    have h1 : Tendsto (fun u => negInv (revChart w s (η u))) (𝓝[<] u₀) (𝓝 (negInv (x₁ : ℂ))) :=
      (continuousAt_negInv (ofReal_ne_zero.2 hx₁)).tendsto.comp hland
    exact (hFc _ hxr).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨h1,
      hev.mono fun u hu => hHb (negInv_mem_H (revChart_mem_H hw hs hu))⟩)
  have hηu₀ : Tendsto η (𝓝[<] u₀) (𝓝 (η u₀)) :=
    (hη.cont.continuousAt (Ici_mem_nhds (ha0.trans_lt hau))).tendsto.mono_left nhdsWithin_le_nhds
  have hξ0 : ξ ≠ 0 := by
    intro h0
    have hne : ∀ᶠ u in 𝓝[<] u₀, F (negInv (revChart w s (η u))) ≠ 0 := hev.mono fun u hu => by
      have hH := negInv_mem_H (revChart_mem_H hw hs hu)
      rw [hFeq hH]
      exact ne_zero_of_mem_H' ((isConformalBijection_fwdMapInv hw hw0 hs).2.mapsTo hH).1
    have hcob := tendsto_negInv_cobounded_of_tendsto_zero (h0 ▸ hξc) hne
    have hcob' : Tendsto η (𝓝[<] u₀) (Bornology.cobounded ℂ) :=
      hcob.congr' (hev.mono fun u hu => (hinv _ hu).symm)
    exact not_mapClusterPt_of_tendsto_cobounded hcob' (η u₀) hηu₀.mapClusterPt
  have hξη : negInv ξ = η u₀ := by
    have h1 := ((continuousAt_negInv hξ0).tendsto.comp hξc).congr' (hev.mono fun u hu => (hinv _ hu).symm)
    exact tendsto_nhds_unique h1 hηu₀
  rw [← hξη]
  exact ((continuousAt_negInv hξ0).tendsto.comp
    (hFlimN (fun n => revChart_mem_H hw hs (hv n)) hlim)).congr fun n => (hinv _ (hv n)).symm

/-- **The completed excursion is a continuous curve on `[t, u₀]`**: `Ψ ∘ η` on `[t, u₀)`, completed by its landing
point at `u₀`. -/
theorem continuousOn_extCurve (hη : IsProperArc η) (hw : Continuous w) (hs : 0 ≤ s) {t u₀ : ℝ} (ht : 0 < t)
    (hD : ∀ u ∈ Ico t u₀, η u ∈ H \ cfHullQ w s) {x₁ : ℂ}
    (hland : Tendsto (fun u => revChart w s (η u)) (𝓝[<] u₀) (𝓝 x₁)) :
    ContinuousOn (fun u => if u < u₀ then revChart w s (η u) else x₁) (Icc t u₀) := by
  intro u hu
  rcases lt_or_eq_of_le hu.2 with hlt | rfl
  · have hev : (fun u => revChart w s (η u)) =ᶠ[𝓝 u] fun u => if u < u₀ then revChart w s (η u) else x₁ :=
      Filter.eventually_of_mem (Iio_mem_nhds hlt) fun v hv => by simp only [mem_Iio.1 hv, ↓reduceIte]
    have hc : ContinuousAt (fun u => revChart w s (η u)) u :=
      ContinuousAt.comp (g := revChart w s) (f := η)
        ((continuousOn_revChart hw hs).continuousAt
          ((isOpen_H_diff_negInv_fwdHull hw hs).mem_nhds (hD u ⟨hu.1, hlt⟩)))
        (hη.cont.continuousAt (Ici_mem_nhds (ht.trans_le hu.1)))
    exact (hc.congr hev).continuousWithinAt
  · have hsub : Icc t u ⊆ insert u (Iio u) := fun v hv => by
      rcases lt_or_eq_of_le hv.2 with h | h
      · exact Or.inr h
      · exact Or.inl h
    refine ContinuousWithinAt.mono ?_ hsub
    rw [continuousWithinAt_insert_self]
    show Tendsto _ (𝓝[<] u) (𝓝 (if u < u then revChart w s (η u) else x₁))
    simp only [lt_irrefl, ↓reduceIte]
    exact hland.congr' (eventually_nhdsWithin_of_forall fun v hv => by
      simp only [mem_Iio.1 hv, ↓reduceIte])

end Old

/-! ### The localization -/

section Main

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ} {η : ℝ → ℂ}

/-- **Every eastern chart crosscut has a rational window at every restart time inside it** (Aux. lemma 64's
countable localization, in the counterflow chart). For an `IsEastCrosscut w s η τ₀ u₀` of a proper arc `η` and a
regular counterflow, and `t ∈ (τ₀, u₀)`, there is a window code `c` with `IsWindow w s η t c` whose excursion event
`WindowExcursion w s η t c u₀` holds. -/
theorem exists_isWindow (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hβ : IsLoewnerTrace w β)
    (hs : 0 ≤ s) {τ₀ u₀ t : ℝ} (hc : IsEastCrosscut w s η τ₀ u₀) (ht : t ∈ Ioo τ₀ u₀) :
    ∃ c : WinCode, IsWindow w s η t c ∧ WindowExcursion w s η t c u₀ := by
  obtain ⟨hτ0, -, hτD, -, hexc, -, x₁, hx₁, hland⟩ := hc
  obtain ⟨δ, hδ1, hδ2⟩ := exists_rat_btwn (show (0 : ℝ) < t - τ₀ by linarith [ht.1])
  have hx₁pos : 0 < x₁ := (junR_nonneg hw hs).trans_lt hx₁
  have ht0 : 0 < t := hτ0.trans ht.1
  set r : ℝ := t - δ with hr
  have hτr : τ₀ < r := by linarith
  have hDt : ∀ u ∈ Ico t u₀, η u ∈ H \ cfHullQ w s := fun u hu => hexc u ⟨ht.1.trans_le hu.1, hu.2⟩
  set γ : ℝ → ℂ := fun u => if u < u₀ then revChart w s (η u) else (x₁ : ℂ) with hγ
  set C := γ '' Icc t u₀ with hC
  have hCc : IsCompact C :=
    isCompact_Icc.image_of_continuousOn (continuousOn_extCurve hη hw hs ht0 hDt hland)
  have hCO : Disjoint C (closure (oldChartSet w s η r)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩
    rcases lt_or_eq_of_le hu.2 with hlt | rfl
    · have hγu : γ u = revChart w s (η u) := by simp only [hγ, hlt, ↓reduceIte]
      rw [hγu]
      exact notMem_closure_oldChartSet_of hη (show r < u by linarith [hu.1]) fun v hv hlim =>
        tendsto_of_revChart_tendsto_interior hw hw0 hs (hDt u ⟨hu.1, hlt⟩) v (fun n => (hv n).2) hlim
    · have hγu : γ u = (x₁ : ℂ) := by simp only [hγ, lt_irrefl, ↓reduceIte]
      rw [hγu]
      exact notMem_closure_oldChartSet_of hη (show r < u by linarith [ht.2]) fun v hv hlim =>
        tendsto_of_revChart_tendsto_end hη hw hw0 hβ hs ht.2 ht0.le
          (fun u' hu' => hDt u' ⟨hu'.1.le, hu'.2⟩) hx₁pos.ne' hland v (fun n => (hv n).2) hlim
  obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn hx₁
  obtain ⟨q₂, hq₂a, -⟩ := exists_rat_btwn (lt_add_one x₁)
  set ρ : ℝ := min (x₁ - q₁) (q₂ - x₁) with hρdef
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  set U : Set ℂ := (closure (oldChartSet w s η r))ᶜ ∩ ({z | 0 < z.im} ∪ ball (x₁ : ℂ) ρ) with hUdef
  have hUo : IsOpen U :=
    isClosed_closure.isOpen_compl.inter ((isOpen_lt continuous_const continuous_im).union isOpen_ball)
  have hCU : C ⊆ U := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨Set.disjoint_left.1 hCO ⟨u, hu, rfl⟩, ?_⟩
    rcases lt_or_eq_of_le hu.2 with hlt | rfl
    · left
      simp only [hγ, hlt, ↓reduceIte]
      exact revChart_mem_H hw hs (hDt u ⟨hu.1, hlt⟩)
    · right
      simp only [hγ, lt_irrefl, ↓reduceIte]
      exact mem_ball_self hρ
  obtain ⟨ε, hε, hεU⟩ := hCc.exists_cthickening_subset_open hUo hCU
  obtain ⟨F, hFC, hFε⟩ := exists_finset_disc_cover hCc hε
  set c : WinCode := (F, q₁, q₂, δ) with hcdef
  have hVth : winSet c ⊆ thickening ε C := iUnion₂_subset fun d hd => hFε d hd
  have hVU : closure (winSet c) ⊆ U :=
    ((closure_mono hVth).trans (closure_thickening_subset_cthickening ε C)).trans hεU
  refine ⟨c, ⟨by exact_mod_cast hδ1, by linarith, by exact_mod_cast hq₁a, fun z hz hz0 => ?_, ?_⟩, ?_⟩
  · obtain ⟨-, hz2 | hz2⟩ := hVU hz
    · exact absurd hz2 (by simp [hz0])
    · have hd : |z.re - x₁| < ρ := by
        have h1 := Complex.abs_re_le_norm (z - (x₁ : ℂ))
        rw [mem_ball, dist_eq_norm] at hz2
        simpa using h1.trans_lt hz2
      rw [abs_lt] at hd
      have h1 : ρ ≤ x₁ - q₁ := min_le_left _ _
      have h2 : ρ ≤ q₂ - x₁ := min_le_right _ _
      exact ⟨by linarith, by linarith⟩
  · exact Set.disjoint_left.2 fun z hz hzO => (hVU hz).1 hzO
  · refine ⟨⟨τ₀, ⟨hτ0, hτr⟩, hτD⟩, fun v hv => hexc v ⟨hτr.trans_le hv.1, hv.2.trans_lt ht.2⟩, ht.2,
      fun v hv => ⟨hexc v ⟨ht.1.trans hv.1, hv.2⟩, hFC ⟨v, ⟨hv.1.le, hv.2.le⟩, by
        simp only [hγ, hv.2, ↓reduceIte]⟩⟩, x₁, hland⟩

end Main

end InteractingSLE.Sec5.Aux61Kernel
