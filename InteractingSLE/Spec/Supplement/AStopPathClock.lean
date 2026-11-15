/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetAux79Path

/-!
# The canonical A-stopped clock: positivity, continuation times and the terminal point

Packet PROVE-T15-ASTOP-PATH (item 6 of `RLC.OrdModel.AStopSourceInputs`, supplement p. 497, Lemma G7). For a retained
continuation (`Supp7.IsRetCont`: a good path `η` continued after `a`, stopped at its first new contact with
`K = O ∪ η([0, a])`, in a chart `(φ, ψ)` of `D = ℍ \ fill K`), the canonical retained clock `γ = canonRetPath … 0`
with capacity lifetime `V = canonRetLife … 0` satisfies (deterministically):

* **`canonRetLife_pos`**: `0 < V`;
* **`exists_contTime`**: every capacity time `0 < q < V` is the capacity of a continuation time `0 < s < contLife`,
  with `γ q = Γ s` (`Γ` the chart path in continuation time), so `ψ (γ q) = η (a + s)`;
* **`canonRetLife_ne_top`**: at a finite `V` the continuation life is finite and `γ V = Γ (contLife)`, so
  `ψ (γ V) = η (contStop)`;
* **`mem_K_of_contStop_lt`**: if the continuation ends before the path's lifetime, its end point lies on `K`;
* **`notMem_of_lt_canonRetLife`** / **`mem_of_canonRetLife_ne_top`**: for any set `J` of chart reals over `K`
  (`w ∈ J ↔ w real ∧ ψ w ∈ K`), the canonical path avoids `J` at `0 < q < V`, and at a finite `V` either the end of
  the continuation is the path's lifetime with an end point off `K`, or `γ V ∈ J`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE.RLC.AStopPath

open Supp7 Restart

section Clock

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {a : ℝ≥0} {O : Set ℂ} {φ ψ : ℂ → ℂ}

/-- **The canonical A-stopped capacity lifetime is positive.** -/
theorem canonRetLife_pos (hR : IsRetCont η ζ x a O φ ψ) :
    0 < canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 := by
  obtain ⟨-, -, -, -, -, hf⟩ := RetAux79.canonRetPath_facts hR
  obtain ⟨t, h0, h1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hR.pos_contLife
  obtain ⟨hle, -, hpos, -, -⟩ := hf t h1.le
  exact lt_of_lt_of_le (ENNReal.coe_pos.2 (hpos (ENNReal.coe_pos.1 h0))) hle

/-- **The continuation time of a capacity time** before the capacity lifetime. -/
theorem exists_contTime (hR : IsRetCont η ζ x a O φ ψ) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0) :
    ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < contLife η ζ a (O ∪ η '' Icc 0 a) ∧
      canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 q =
        contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a)) s := by
  have hC := hR.isClockOn
  rw [canonRetLife_zero] at hq
  rw [canonRetPath_zero]
  set V := contLife η ζ a (O ∪ η '' Icc 0 a) with hVdef
  set C := chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a V) with hCdef
  obtain ⟨hsV, hCs⟩ := hC.invClock_spec hq.le
  refine ⟨_, pos_iff_ne_zero.2 fun h => ?_, lt_of_le_of_ne hsV fun h => ?_, rfl⟩
  · rw [h, hC.zero] at hCs
    exact hq0.ne' (by exact_mod_cast hCs.symm)
  · have hV : V ≠ ⊤ := h ▸ ENNReal.coe_ne_top
    have hq' := hq
    have hVn : V.toNNReal = invClock C V q := by
      have h' := congrArg ENNReal.toNNReal h
      rw [ENNReal.toNNReal_coe] at h'
      exact h'.symm
    simp only [capLife, hV, ↓reduceIte, hVn, hCs, ENNReal.ofReal_coe_nnreal] at hq'
    exact lt_irrefl _ hq'

/-- **At a finite capacity lifetime** the continuation life is finite and the canonical path ends at the chart path's
terminal point. -/
theorem canonRetLife_ne_top (hR : IsRetCont η ζ x a O φ ψ)
    (hV : canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 ≠ ⊤) :
    contLife η ζ a (O ∪ η '' Icc 0 a) ≠ ⊤ ∧
      canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0
          (canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0).toNNReal =
        contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a))
          (contLife η ζ a (O ∪ η '' Icc 0 a)).toNNReal := by
  have hC := hR.isClockOn
  rw [canonRetLife_zero] at hV ⊢
  rw [canonRetPath_zero]
  set V := contLife η ζ a (O ∪ η '' Icc 0 a) with hVdef
  set C := chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a V) with hCdef
  have hfin : V ≠ ⊤ := fun h => hV (by simp only [capLife, h, ↓reduceIte])
  refine ⟨hfin, ?_⟩
  have he : (capLife C V).toNNReal = (C V.toNNReal).toNNReal := by
    simp only [capLife, hfin, ↓reduceIte, ENNReal.ofReal, ENNReal.toNNReal_coe]
  show contPath _ φ η a V (invClock C V (capLife C V).toNNReal) = _
  rw [he, hC.invClock_apply (by rw [ENNReal.coe_toNNReal hfin])]

/-- **A continuation that ends before the path's lifetime ends on `K`** (`K` closed, the path continuous). -/
theorem mem_K_of_contStop_lt (hR : IsRetCont η ζ x a O φ ψ)
    (hlt : contStop η ζ a (O ∪ η '' Icc 0 a) < ζ) :
    η (contStop η ζ a (O ∪ η '' Icc 0 a)).toNNReal ∈ O ∪ η '' Icc 0 a := by
  set K := O ∪ η '' Icc 0 a with hK
  set c := contStop η ζ a K with hcdef
  have hcfin : c ≠ ⊤ := ne_top_of_lt hlt
  set c' := c.toNNReal with hc'def
  have hcc : (c' : ℝ≥0∞) = c := ENNReal.coe_toNNReal hcfin
  by_contra hnot
  obtain ⟨w, -, -, hgen⟩ := hR.path.2
  have hcont : ContinuousOn η {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} := by
    have h := hgen.2.1.add (continuousOn_const (c := (x : ℂ)))
    exact h.congr fun t _ => (sub_add_cancel (η t) (x : ℂ)).symm
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hcmem : c' ∈ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := by
    show (c' : ℝ≥0∞) < ζ
    rw [hcc]; exact hlt
  have hca : ContinuousAt η c' :=
    (hcont.mono fun t (ht : (t : ℝ≥0∞) < ζ) => ht.le).continuousAt (hopen.mem_nhds hcmem)
  have hnb : {t : ℝ≥0 | η t ∉ K ∧ (t : ℝ≥0∞) < ζ} ∈ 𝓝 c' :=
    Filter.inter_mem (hca.preimage_mem_nhds (hR.isClosed_K.isOpen_compl.mem_nhds hnot))
      (hopen.mem_nhds hcmem)
  obtain ⟨u, hcu, hsub⟩ := exists_Ico_subset_of_mem_nhds hnb ⟨c' + 1, lt_add_one c'⟩
  obtain ⟨t₁, hct₁, ht₁u⟩ := exists_between hcu
  have ht₁ : t₁ ∈ contSet η ζ a K := by
    have hac : (a : ℝ≥0∞) < c := hR.lt_contStop
    rw [← hcc] at hac
    have hac' : a < c' := ENNReal.coe_lt_coe.1 hac
    refine ⟨(hac'.trans hct₁).le, (hsub ⟨hct₁.le, ht₁u⟩).2.le, fun t' h1 h2 => ?_⟩
    rcases lt_or_ge t' c' with h | h
    · exact notMem_of_lt_contStop (ζ := ζ) h1 (by rw [← hcdef, ← hcc]; exact ENNReal.coe_lt_coe.2 h)
    · exact (hsub ⟨h, h2.trans ht₁u⟩).1
  have hle := le_contStop ht₁
  rw [← hcdef, ← hcc] at hle
  exact absurd (ENNReal.coe_le_coe.1 hle) (not_le.2 hct₁)

/-- **Before the capacity lifetime the canonical path avoids every set of chart points over `K`.** -/
theorem notMem_of_lt_canonRetLife (hR : IsRetCont η ζ x a O φ ψ) {J : Set ℂ}
    (hJ : ∀ w ∈ J, ψ w ∈ O ∪ η '' Icc 0 a) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0) :
    canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 q ∉ J := by
  obtain ⟨s, hs0, hsV, he⟩ := exists_contTime hR hq0 hq
  intro hmem
  rw [he] at hmem
  have hK := hJ _ hmem
  rw [(hR.contPath_spec hsV.le).2] at hK
  exact notMem_of_lt_contStop (lt_add_of_pos_right a hs0) (coe_add_lt_iff.1 hsV) hK

/-- **At a finite capacity lifetime** either the continuation ran to the path's lifetime with an end point off `K`,
or the canonical path ends in every set `J` containing the real chart points over `K`. -/
theorem mem_of_canonRetLife_ne_top (hR : IsRetCont η ζ x a O φ ψ) {J : Set ℂ}
    (hJ : ∀ w : ℂ, w.im = 0 → ψ w ∈ O ∪ η '' Icc 0 a → w ∈ J)
    (hV : canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0 ≠ ⊤) :
    (contStop η ζ a (O ∪ η '' Icc 0 a) = ζ ∧ η ζ.toNNReal ∉ O ∪ η '' Icc 0 a) ∨
      canonRetPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0
        (canonRetLife (H \ fillH (O ∪ η '' Icc 0 a)) φ η ζ a (O ∪ η '' Icc 0 a) 0).toNNReal ∈ J := by
  obtain ⟨hfin, he⟩ := canonRetLife_ne_top hR hV
  set K := O ∪ η '' Icc 0 a with hKdef
  have hLle : ((contLife η ζ a K).toNNReal : ℝ≥0∞) ≤ contLife η ζ a K := by rw [ENNReal.coe_toNNReal hfin]
  obtain ⟨hHb, hψ⟩ := hR.contPath_spec hLle
  have hstop : ((a + (contLife η ζ a K).toNNReal : ℝ≥0) : ℝ≥0∞) = contStop η ζ a K := by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hfin, contLife, add_tsub_cancel_of_le hR.lt_contStop.le]
  have hsfin : contStop η ζ a K ≠ ⊤ := by rw [← hstop]; exact ENNReal.coe_ne_top
  have hst : a + (contLife η ζ a K).toNNReal = (contStop η ζ a K).toNNReal := by
    rw [← ENNReal.toNNReal_coe (a + (contLife η ζ a K).toNNReal), hstop]
  rw [hst] at hψ
  by_cases hmem : η (contStop η ζ a K).toNNReal ∈ K
  · right
    rw [he]
    refine hJ _ ?_ (by rw [hψ]; exact hmem)
    by_contra him
    have hH : contPath (H \ fillH K) φ η a (contLife η ζ a K) (contLife η ζ a K).toNNReal ∈ H :=
      lt_of_le_of_ne hHb (Ne.symm him)
    have hD := hR.chart.bijOn_inv.mapsTo hH
    rw [hψ] at hD
    exact hD.2 ⟨hD.1, Or.inl (subset_closure hmem)⟩
  · left
    rcases lt_or_eq_of_le (contStop_le : contStop η ζ a K ≤ ζ) with hlt | heq
    · exact absurd (mem_K_of_contStop_lt hR hlt) hmem
    · exact ⟨heq, by rw [← heq]; exact hmem⟩

end Clock

end InteractingSLE.RLC.AStopPath
