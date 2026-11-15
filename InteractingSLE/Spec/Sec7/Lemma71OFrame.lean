/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71OCorner

/-!
# Lemma 7.1's inherited branch: the landing map of the pocket chart

Packet PROVE-LEMMA71O. On a pathwise pocket frame (`Lemma71N.IsPocketFrame`: walls `β` (left), `α` (right), the
pocket `C`, a marked pocket `[a, b]` of `α`, the chart `c` with boundary map `Ψ`), the chart inverse extends
continuously to `ℍ̄` (`land`, the landing map):

* `tendsto_land`, `continuousOn_land`, `injOn_land`: the landing map is continuous and injective on `ℍ̄`;
* `land_zero`: the opening point is the right wall's point `α a'` (`a'` the original time of the disc time `a`), and
  `exists_land_zero_eq`: it is also a point `β s_a` of the left wall;
* `exists_land_neg`, `exists_land_pos`: negative (positive) real points land on the left (right) wall off the other
  wall;
* `exists_gap`: times `a' < q₂ < t` with `α t` in the open contact gap (off `β`) and adherent to the pocket;
* **`subset_H_diff_fillH_prefixSet`**: the pocket lies in the unbounded domain of `β([0, q₁]) ∪ α([0, q₂])` (it escapes
  through the gap point `α t` into the right side of `α`; supplement §2.3: "The pocket `C` lies in `D_p`").

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71O

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71K (IsMarkedPocket wallPt)
open Lemma71N (IsPocketFrame)

/-- The landing map of a chart: the extension of its inverse from `ℍ` to `ℍ̄`. -/
def land (c : Chart) : ℂ → ℂ := extendFrom H c.2.1

namespace PocketFrame

variable {β α : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ}

theorem exists_tendsto (hF : IsPocketFrame β α C c Ψ a b) {q : ℂ} (hq : q ∈ Hbar) :
    ∃ z ∈ closure (cayley '' C) \ {wallPt α b}, Ψ z = q ∧ Tendsto c.2.1 (𝓝[H] q) (𝓝 (cayleyInv z)) :=
  Lemma71M.tendsto_inv_of_ext hF.hc hF.hdom hF.subset_H hF.closePt_notMem hF.hΨc hF.hΨi hF.hΨtop hF.hΨe
    hF.one_notMem (by rw [closure_H]; exact hq)

theorem tendsto_land (hF : IsPocketFrame β α C c Ψ a b) {q : ℂ} (hq : q ∈ Hbar) :
    Tendsto c.2.1 (𝓝[H] q) (𝓝 (land c q)) := by
  obtain ⟨z, -, -, hz⟩ := exists_tendsto hF hq
  rwa [land, extendFrom_eq (by rw [closure_H]; exact hq) hz]

theorem continuousOn_land (hF : IsPocketFrame β α C c Ψ a b) : ContinuousOn (land c) Hbar :=
  continuousOn_extendFrom (by rw [closure_H]) fun q hq => ⟨_, tendsto_land hF hq⟩

/-- The landing point at `q` is `cayleyInv z` for the boundary point `z` with `Ψ z = q`. -/
theorem land_eq (hF : IsPocketFrame β α C c Ψ a b) {q : ℂ} (hq : q ∈ Hbar) {z : ℂ}
    (hz : z ∈ closure (cayley '' C) \ {wallPt α b}) (hΨz : Ψ z = q) : land c q = cayleyInv z := by
  obtain ⟨z', hz', hΨz', hl⟩ := exists_tendsto hF hq
  have hzz : z' = z := hF.hΨi hz' hz (hΨz'.trans hΨz.symm)
  rw [land, extendFrom_eq (by rw [closure_H]; exact hq) hl, hzz]

theorem injOn_land (hF : IsPocketFrame β α C c Ψ a b) : InjOn (land c) Hbar := by
  intro q₁ hq₁ q₂ hq₂ h
  obtain ⟨z₁, hz₁, hΨ₁, -⟩ := exists_tendsto hF hq₁
  obtain ⟨z₂, hz₂, hΨ₂, -⟩ := exists_tendsto hF hq₂
  rw [land_eq hF hq₁ hz₁ hΨ₁, land_eq hF hq₂ hz₂ hΨ₂] at h
  have h1 : z₁ ≠ 1 := fun h => hF.one_notMem (h ▸ hz₁)
  have h2 : z₂ ≠ 1 := fun h => hF.one_notMem (h ▸ hz₂)
  have hz : z₁ = z₂ := by
    rw [← QuantumZipper.CA.cayley_cayleyInv h1, ← QuantumZipper.CA.cayley_cayleyInv h2, h]
  rw [← hΨ₁, ← hΨ₂, hz]

/-- The original time of the opening point on the right wall. -/
def openTime (a : ℝ) : ℝ≥0 := (WangWu.arcTime a).toNNReal

/-- **The opening point**: `0` lands at the right wall's point `α a'`. -/
theorem land_zero (hF : IsPocketFrame β α C c Ψ a b) : land c 0 = α (openTime a) := by
  have ha1 : a < 1 := hF.hM.2.1.trans_le hF.hM.2.2.1
  rw [land_eq hF (show (0 : ℂ) ∈ Hbar from le_refl (0 : ℝ)) (hF.wallPt_mem_K ⟨le_rfl, hF.hM.2.1⟩) hF.hΨ0, wallPt,
    WangWu.toDisc_of_lt ha1,
    WangWu.cayleyInv_cayley_of_mem_Hbar (hF.hα.isProperArc.mem_Hbar (WangWu.arcTime_nonneg ⟨hF.hM.1, ha1⟩))]
  rfl

theorem land_ofReal_neg (hF : IsPocketFrame β α C c Ψ a b) {ξ : ℝ} (hξ : ξ < 0) :
    ∃ s : ℝ≥0, 0 < s ∧ β s ∉ range α ∧ land c ξ = β s := by
  obtain ⟨s, hs0, hsα, hl⟩ := hF.land_neg hξ
  have hξH : ((ξ : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have : (𝓝[H] ((ξ : ℝ) : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hξH)
  exact ⟨s, hs0, hsα, tendsto_nhds_unique (tendsto_land hF hξH) hl⟩

theorem land_ofReal_pos (hF : IsPocketFrame β α C c Ψ a b) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ s : ℝ≥0, 0 < s ∧ α s ∉ range β ∧ land c ξ = α s := by
  obtain ⟨s, hs0, hsβ, hl⟩ := hF.land_pos hξ
  have hξH : ((ξ : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have : (𝓝[H] ((ξ : ℝ) : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hξH)
  exact ⟨s, hs0, hsβ, tendsto_nhds_unique (tendsto_land hF hξH) hl⟩

/-- The landing map along the real line is continuous. -/
theorem continuous_land_ofReal (hF : IsPocketFrame β α C c Ψ a b) : Continuous fun t : ℝ => land c t :=
  continuousOn_univ.1 ((continuousOn_land hF).comp Complex.continuous_ofReal.continuousOn
    fun t _ => show (0 : ℝ) ≤ ((t : ℝ) : ℂ).im by simp)

/-- **The opening point is also a point of the left wall** (a limit of left-wall landing points; the left wall's range
is closed). -/
theorem exists_land_zero_eq (hF : IsPocketFrame β α C c Ψ a b) : ∃ s : ℝ≥0, land c 0 = β s := by
  have hcl : IsClosed (range β) := Lemma71Pin.IsSimpleProper.isClosed_range hF.hβ
  have ht : Tendsto (fun t : ℝ => land c t) (𝓝[<] 0) (𝓝 (land c 0)) := by
    have := ((continuous_land_ofReal hF).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
    simpa using this
  have hmem : land c 0 ∈ range β := hcl.mem_of_tendsto ht (eventually_nhdsWithin_of_forall fun t ht => by
    obtain ⟨s, -, -, hs⟩ := land_ofReal_neg hF (show t < 0 from ht)
    exact ⟨s, hs.symm⟩)
  obtain ⟨s, hs⟩ := hmem
  exact ⟨s, hs.symm⟩

/-- A right-wall point of disc time in `(a, b)` is off the left wall and adherent to the pocket. -/
theorem gap_point (hF : IsPocketFrame β α C c Ψ a b) {t : ℝ≥0} (ht : WangWu.discTime t ∈ Ioo a b) :
    α t ∉ range β ∧ α t ∈ closure C := by
  obtain ⟨hcay, -⟩ := Prop74B.cayley_eq_wallPt (γ := α) t
  have hg := hF.isContactGap
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩
    refine hg.2.2.2 _ ht ⟨⟨ht.1.le.trans' hF.hM.1, (ht.2.trans_le hF.hM.2.2.1).le⟩, ?_⟩
    obtain ⟨hcu, hdu⟩ := Prop74B.cayley_eq_wallPt (γ := β) u
    refine ⟨WangWu.discTime u, ⟨hdu.1, hdu.2.le⟩, ?_⟩
    change wallPt β (WangWu.discTime u) = wallPt α (WangWu.discTime t)
    rw [← hcu, ← hcay, hu]
  · have hmem : wallPt α (WangWu.discTime t) ∈ closure (cayley '' C) := by
      have hI : WangWu.discTime t ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt α s ∈ closure (cayley '' C)} := by
        rw [hF.hM.2.2.2.1]; exact ⟨ht.1.le, ht.2.le⟩
      exact hI.2
    rw [← hcay] at hmem
    have hne : cayley (α t) ≠ 1 := QuantumZipper.CA.cayley_ne_one
      (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (hF.hα.isProperCurve.2.2.1 _))
    have hca : ContinuousAt cayleyInv (cayley (α t)) :=
      QuantumZipper.CA.continuousOn_cayleyInv.continuousAt (isOpen_ne.mem_nhds hne)
    have h := hca.continuousWithinAt.mem_closure_image hmem
    rw [WangWu.cayleyInv_cayley_of_mem_Hbar (hF.hα.isProperCurve.2.2.1 _), image_image] at h
    refine closure_mono (fun w hw => ?_) h
    obtain ⟨z, hz, rfl⟩ := hw
    show cayleyInv (cayley z) ∈ C
    rwa [WangWu.cayleyInv_cayley_of_mem_Hbar (le_of_lt (show (0 : ℝ) < z.im from hF.subset_H hz))]

/-- **Two gap times**: `a' < q₂ < t` with `α t` off the left wall and adherent to the pocket. -/
theorem exists_gap (hF : IsPocketFrame β α C c Ψ a b) :
    ∃ q₂ t : ℝ≥0, openTime a < q₂ ∧ q₂ < t ∧ α t ∉ range β ∧ α t ∈ closure C := by
  have hab := hF.hM.2.1
  have ha0 := hF.hM.1
  have hb1 := hF.hM.2.2.1
  set s₁ := a + (b - a) / 3 with hs₁
  set s₂ := a + 2 * (b - a) / 3 with hs₂
  have h1 : a < s₁ := by rw [hs₁]; linarith
  have h12 : s₁ < s₂ := by rw [hs₁, hs₂]; linarith
  have h2 : s₂ < b := by rw [hs₂]; linarith
  have hmono := WangWu.strictMonoOn_arcTime
  have hI : ∀ s, a ≤ s → s < 1 → s ∈ Ico (0 : ℝ) 1 := fun s hs hs1 => ⟨ha0.trans hs, hs1⟩
  have hs₁I := hI s₁ h1.le (h12.trans h2 |>.trans_le hb1)
  have hs₂I := hI s₂ (h1.trans h12).le (h2.trans_le hb1)
  have haI := hI a le_rfl (hab.trans_le hb1)
  refine ⟨(WangWu.arcTime s₁).toNNReal, (WangWu.arcTime s₂).toNNReal, ?_, ?_, ?_⟩
  · exact Real.toNNReal_lt_toNNReal_iff_of_nonneg (WangWu.arcTime_nonneg haI) |>.2 (hmono haI hs₁I h1)
  · exact Real.toNNReal_lt_toNNReal_iff_of_nonneg (WangWu.arcTime_nonneg hs₁I) |>.2 (hmono hs₁I hs₂I h12)
  · refine gap_point hF ?_
    rw [Real.coe_toNNReal _ (WangWu.arcTime_nonneg hs₂I), WangWu.discTime_arcTime hs₂I.2]
    exact ⟨h1.trans h12, h2⟩

/-- **The pocket lies in the unbounded domain of the two retained prefixes** `β([0, q₁]) ∪ α([0, q₂])`, when the right
prefix stops before a gap point `α t` (supplement §2.3: "The pocket `C` lies in `D_p`"). -/
theorem subset_H_diff_fillH_prefixSet (hF : IsPocketFrame β α C c Ψ a b) {q₂ t : ℝ≥0} (hq₂t : q₂ < t)
    (hαt : α t ∉ range β) (hαtC : α t ∈ closure C) (q₁ : ℝ≥0) :
    C ⊆ H \ fillH (Restart.prefixSet β q₁ α q₂) := by
  have hCsub := Prop74B.subset_of_mem_betweenComponents hF.hC
  have hΓsub : Restart.prefixSet β q₁ α q₂ ⊆ range β ∪ range α := by
    rintro _ (⟨u, -, rfl⟩ | ⟨u, -, rfl⟩)
    · exact Or.inl ⟨u, rfl⟩
    · exact Or.inr ⟨u, rfl⟩
  have hΓc : IsClosed (Restart.prefixSet β q₁ α q₂) :=
    (Restart.isCompact_prefixSet hF.hβ.1.continuousOn hF.hα.1.continuousOn).isClosed
  have hRdisj := Lemma71I.disjoint_rightSideOf_of_subset_closedLeftSide hF.hα.isProperCurve hF.hα.2.2.1 hF.hord
  have hCpc : IsPreconnected C := by
    obtain ⟨z, -, -, -, hCz⟩ := hF.hC
    rw [hCz]; exact isPreconnected_connectedComponentIn
  refine subset_H_diff_fillH_of_escape hΓc hCpc ?_ ?_ ?_
    (Lemma613.not_isBounded_rightSideOf hF.hα) (w₀ := α t) ?_ hαtC (Lemma613.mem_closure_rightSideOf hF.hα t)
  · intro z hz
    refine ⟨(hCsub hz).1, fun hzΓ => (hCsub hz).2 ?_⟩
    rcases hΓsub hzΓ with h | h
    · exact Or.inr h
    · exact Or.inl h
  · have h := hF.hα.isProperArc.isPreconnected_rightSideOf
    rwa [Lemma71I.arcRange_realPath] at h
  · intro z hz
    refine ⟨hz.1.1, fun hzΓ => ?_⟩
    rcases hΓsub hzΓ with h | h
    · exact Set.disjoint_left.1 hRdisj h hz
    · exact hz.1.2 h
  · have ht0 : 0 < t := lt_of_le_of_lt (zero_le (a := q₂)) hq₂t
    refine ⟨hF.hα.2.2.2.1 t ht0, ?_⟩
    rintro (⟨u, -, hu⟩ | ⟨u, hu, hut⟩)
    · exact hαt ⟨u, hu⟩
    · have := hF.hα.2.1 hut
      rw [this] at hu
      exact absurd hu.2 (not_le.2 hq₂t)

end PocketFrame

end InteractingSLE.Sec7.Lemma71O
