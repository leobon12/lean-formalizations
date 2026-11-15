/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FmStep
import InteractingSLE.Spec.Supplement.SB2NcX0

/-!
# D34's left heights: F2b′'s chart offset is the entry of the free ray

Worker PROVE-SB2-F3LAW (round 3). NOJUMP's construction of F2b′ (`Nc.exists_stageObj`) takes the chart offset
`x₀ = Nc.entryRead (fill K) (B's point)`. When the hull is free right of the point, this read is the entry of the free
ray (`Fm.entry`, the infimum of the boundary values right of the point), which is the bound the left-height step
`Fm.leftAdm_entry_step` asks for (`x₀ ≤ entry`).

* `tendsto_bdryVal_entry`, **`entryRead_eq_entry`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Fo

open Restart Sec7 Fm

/-- The boundary values tend to the entry at `p⁺`. -/
theorem tendsto_bdryVal_entry {A : Set ℂ} (hA : IsHPHull A) {p : ℝ} (hp : FreeRight A p) :
    Tendsto (bdryVal A) (𝓝[>] p) (𝓝 (entry A p)) := by
  have hmono := strictMonoOn_bdryVal hA hp
  have hle : ∀ x ∈ Ioi p, entry A p ≤ bdryVal A x := fun x hx => entry_le_bdryVal hA hp hx
  have hne : (bdryVal A '' Ioi p).Nonempty := ⟨bdryVal A (p + 1), p + 1, by simp, rfl⟩
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x hx using lt_of_lt_of_le ha (hle x hx)
  · obtain ⟨_, ⟨x₁, hx₁, rfl⟩, hx₁a⟩ := exists_lt_of_csInf_lt hne ha
    filter_upwards [Ioo_mem_nhdsGT hx₁] with x hx
    exact lt_trans (hmono hx.1 hx₁ hx.2) hx₁a

open Classical in
/-- **NOJUMP's entry read is the entry of the free ray** (`Nc.entryRead`, the chart offset of F2b′'s construction). -/
theorem entryRead_eq_entry {A : Set ℂ} (hA : IsHPHull A) {R : ℝ} (hR : FreeRight A R) :
    Nc.entryRead A R = entry A R := by
  have hc := Mo.isConformal_hullChart hA 0
  have hdom := Mo.coe_dom_hullChart hA 0
  have hinner : ∀ n : ℕ, limsup (fun m : ℕ =>
      (if Nc.apprPt R n m ∈ ((Mo.hullChart A 0).dom : Set ℂ) then (Mo.hullChart A 0).1 (Nc.apprPt R n m)
        else 0).re) atTop = bdryVal A (Nc.qApprox R n) := by
    intro n
    obtain ⟨r, hr, hd⟩ := hR _ (Nc.lt_qApprox R n)
    have hT := (tendsto_mapOut_bdryVal hA hr hd).comp (Nc.tendsto_apprPt R n)
    have hev : ∀ᶠ m : ℕ in atTop, Nc.apprPt R n m ∈ H \ A := by
      have h1 := (Nc.tendsto_apprPt R n) (inter_mem_nhdsWithin H (isOpen_ball.mem_nhds (mem_ball_self hr)))
      filter_upwards [h1] with m hm
      exact ⟨hm.1, fun hA' => Set.disjoint_left.1 hd hm.2 hA'⟩
    have h2 : Tendsto (fun m : ℕ =>
        (if Nc.apprPt R n m ∈ ((Mo.hullChart A 0).dom : Set ℂ) then (Mo.hullChart A 0).1 (Nc.apprPt R n m)
          else 0).re) atTop (𝓝 (bdryVal A (Nc.qApprox R n))) := by
      have h3 := (Complex.continuous_re.tendsto _).comp hT
      simp only [Complex.ofReal_re] at h3
      refine h3.congr' ?_
      filter_upwards [hev] with m hm
      have hm' : Nc.apprPt R n m ∈ ((Mo.hullChart A 0).dom : Set ℂ) := by rw [hdom]; exact hm
      simp [hm', Mo.hullChart_fwd]
    exact h2.limsup_eq
  unfold Nc.entryRead
  simp_rw [hinner]
  exact ((tendsto_bdryVal_entry hA hR).comp (Nc.tendsto_qApprox R)).limsup_eq

end InteractingSLE.Theorem14.SB.Fo
