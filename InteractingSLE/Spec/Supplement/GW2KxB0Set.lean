/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxB0Geo
import InteractingSLE.Spec.Supplement.GW2OmxGeo
import InteractingSLE.Spec.Supplement.GW2KbBase

/-!
# The root piece's launch sets at index `0`, at a root `x` (one sample)

Packet PROVE-GW2-GEOM2, round 14 (D49), for the base of Claim(k) at a root `x`.

* `lt_firstTipTime_pt_iff`: before the first tip at `x` iff the counterflow is off `−1/x`;
* `gapPt`, `mem_gapPt_iff`: the event that the counterflow avoids `x` up to `s` (a gap event of
  the counterflow reader, measurable for every σ-algebra carrying the counterflow record);
* **`launch_sets_root0X`**: in the launch chart `recenter x`, the retained hull is BR4a's counterflow hull at the clock
  `t₀` (`ℓ t₀ = s`), and on success the stage union at the root piece's end is that hull with the explored hull.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Kx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule GW2Omx Supp8.GB6LMean GW2Xk GW2Kb
open Supp8.GB6 (relMap gb6Rec relClock)
open Supp8.Q3Rel (invHull)

/-- **Before the first tip at `x` iff the counterflow is off `−1/x`.** -/
theorem lt_firstTipTime_pt_iff {W' : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace W' ⊤ η)
    (hc : Continuous W') (h0 : W' 0 = 0) (x : ℝ) (σ : ℝ≥0) :
    (σ : ℝ≥0∞) < firstTipTime infinitySourceChart W' {(x : ℂ)} ↔ ∀ u ≤ σ, (x : ℂ) * η u + 1 ≠ 0 := by
  refine ⟨den_of_lt_firstTipTime_pt hη hc h0, fun h => ?_⟩
  refine lt_firstTipTime_of_noContact hη hc h0 isCompact_singleton fun t ht hγt hmem => ?_
  apply h t ht
  rw [Set.mem_singleton_iff] at hmem
  rw [← hmem]
  field_simp
  ring

variable {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ)

/-- **The counterflow avoids the root up to `s`** (a gap event of the counterflow reader). -/
def gapPt : Set Ω := gapEvent (cfRead c) (fun _ _ => ((rootPt r.1 : ℝ) : ℂ)) c.s 0

theorem mem_gapPt_iff {ω : Ω} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace (fun u => c.W u ω) ⊤ η)
    (hc : Continuous fun u => c.W u ω) (h0 : c.W 0 ω = 0) (hs : (c.s : ℝ≥0∞) < c.ζ ω) :
    ω ∈ gapPt c r ↔ ∀ u ≤ c.s, ((rootPt r.1 : ℝ) : ℂ) * η u + 1 ≠ 0 := by
  unfold gapPt
  rw [mem_gapEvent_congr (γ' := fun _ => η) (α' := fun _ _ => ((rootPt r.1 : ℝ) : ℂ))
    (fun q hq => cfRead_eq_of_trace c hη hc h0 hs hq) (fun q _ => rfl)]
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  rw [mem_gapEvent_iff (γ := fun _ => η) (α := fun _ _ => ((rootPt r.1 : ℝ) : ℂ)) hηc continuous_const]
  constructor
  · intro h u hu
    rw [mul_comm]
    exact h u ⟨zero_le, hu⟩ 0 ⟨le_rfl, le_rfl⟩
  · intro h t ht u _
    rw [mul_comm]
    exact h t ht.2

/-- **The root piece's launch sets at index `0`** (root `x ≥ 0`, one sample). -/
theorem launch_sets_root0X (hx0 : 0 ≤ rootPt r.1) {ω : Ω} {γ' : ℝ≥0 → ℂ}
    (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0) (hγ' : IsGeneratingTrace (fun u => c.W u ω) ⊤ γ')
    (hsζ : (c.s : ℝ≥0∞) < c.ζ ω) {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} (hWk : Continuous Wk) (hWk0 : Wk 0 = 0)
    (hγk : IsGeneratingTrace Wk ⊤ γk) {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓr : range ℓ = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      {((rootPt r.1 : ℝ) : ℂ)}})
    (hvis : 0 < rootPt r.1 → ∃ τ, (rootPt r.1 : ℂ) * γ' τ + 1 = 0)
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), ((Chart.id.recenter (rootPt r.1)).trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z) {t₀ : ℝ≥0} (ht₀ : ℓ t₀ = c.s) :
    (Chart.id.recenter (rootPt r.1)).1 '' (Supp8.GB6LineL.retSet c.s c.W c.ζ ω ∩
        ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ)) = invHull (fun q : ℝ => Wk q.toNNReal) (t₀ : ℝ) ∧
      (oldSuccess c r [] ω → (Chart.id.recenter (rootPt r.1)).1 '' (GW2Rd.schedUnionX c r [] a
        (historyTime c r []) 0 ω ∩ ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ)) =
          invHull (fun q : ℝ => Wk q.toNNReal) (t₀ : ℝ) ∪
            fwdHull (fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω) (historyTime c r [] : ℝ)) := by
  set x := rootPt r.1 with hx
  set cL := Chart.id.recenter x with hcL
  have hconf : cL.IsConformal := Chart.isConformal_id.recenter x
  have hWkc : Continuous fun r : ℝ => Wk r.toNNReal := hWk.comp continuous_real_toNNReal
  have hc0 : cL.2.1 '' invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) =
      invHull (fun u : ℝ => c.W u.toNNReal ω) c.s := by
    rw [cont_root0X hx0 hWk hWk0 hγk hW' hW'0 hγ' hℓc hℓm hℓr hvis hiff t₀, ht₀]
  refine ⟨?_, fun hold => ?_⟩
  · have hret : Supp8.GB6LineL.retSet c.s c.W c.ζ ω = invHull (fun u : ℝ => c.W u.toNNReal ω) c.s := by
      rw [Supp8.GB6LineL.retSet_of_lt hsζ]
      exact Supp8.RelSafeS.invHull_record_eq hW'0 hW'.continuousOn hsζ
    have hsub : invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) ⊆ H := GW2Shr.invHull_subset_H hWkc t₀.coe_nonneg
    have hsubW : invHull (fun u : ℝ => c.W u.toNNReal ω) c.s ⊆ H :=
      GW2Shr.invHull_subset_H (hW'.comp continuous_real_toNNReal) c.s.coe_nonneg
    rw [hret, coe_dom_recenter_id x, inter_eq_left.2 hsubW, ← hc0, image_image]
    conv_rhs => rw [← image_id (invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ))]
    exact image_congr fun w hw => hconf.2.2 w (hsub hw)
  · have e : GW2Rd.schedUnionX c r [] a (historyTime c r []) 0 ω =
        GW2Rd.schedUnionX c r [] a 0 (historyTime c r []) ω := by
      simp only [GW2Rd.schedUnionX, add_zero, zero_add]
    rw [e]
    exact union_root0X c r a hold hW'0 hW' hsζ hWk hc0 (historyTime c r [])

end InteractingSLE.Theorem14.GW2Kx
