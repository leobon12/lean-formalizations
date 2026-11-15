/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.SeparatedGroups
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Merging two adjacent coincident marks

Packet PROVE-ZHAN-B4. Coincident marks stay coincident (`IsIntegratedSLEPath.vL_eq_of_xL_eq`), so an evolution whose
left marks `j` and `j + 1` start at the same point is an evolution of the word with mark `j + 1` removed and its
weight added to mark `j` (`IsIntegratedSLEEvolution.mergeAdjL`; infinite lifetime almost surely). Repeating this
reduces every ordered word to one whose marks are strictly ordered on each side (the strip words of R36). The right
version follows by reflection (`IsIntegratedSLEEvolution.reflect`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

variable {n nR : ℕ}

/-- The weights after merging mark `j + 1` into mark `j` (indices of `Fin (n + 2)`; the result is indexed by the
remaining marks `j.succ.succAbove`). -/
def mergeAdj (ρ : Fin (n + 2) → ℝ) (j : Fin (n + 1)) : Fin (n + 1) → ℝ := fun k =>
  ρ (j.succ.succAbove k) + if k = j then ρ j.succ else 0

theorem succAbove_succ_self (j : Fin (n + 1)) : j.succ.succAbove j = j.castSucc :=
  Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ (i := j))

/-- Sums against a function that agrees on the merged pair are unchanged by merging. -/
theorem sum_mergeAdj_mul (ρ : Fin (n + 2) → ℝ) (j : Fin (n + 1)) (f : Fin (n + 2) → ℝ)
    (hf : f j.castSucc = f j.succ) :
    ∑ k, mergeAdj ρ j k * f (j.succ.succAbove k) = ∑ i, ρ i * f i := by
  rw [Fin.sum_univ_succAbove (fun i => ρ i * f i) j.succ]
  simp only [mergeAdj, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, succAbove_succ_self, hf]
  ring

theorem sum_mergeAdj (ρ : Fin (n + 2) → ℝ) (j : Fin (n + 1)) : ∑ k, mergeAdj ρ j k = ∑ i, ρ i := by
  simpa using sum_mergeAdj_mul ρ j (fun _ => 1) rfl

/-- **Merging adjacent coincident left marks, pathwise** (infinite lifetime). -/
theorem IsIntegratedSLEPath.mergeAdjL {a : ℝ} {xL ρL : Fin (n + 2) → ℝ} {xR ρR : Fin nR → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin (n + 2) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (j : Fin (n + 1)) (hj : xL j.castSucc = xL j.succ) (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ⊤) :
    IsIntegratedSLEPath a (fun k => xL (j.succ.succAbove k)) xR (mergeAdj ρL j) ρR w
      (fun k => vL (j.succ.succAbove k)) vR b ⊤ := by
  have hco : ∀ t : ℝ≥0, vL j.castSucc t = vL j.succ t := fun t =>
    InteractingSLE.IsIntegratedSLEPath.vL_eq_of_xL_eq h ENNReal.coe_lt_top hj
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -, -⟩ := h
  have hmono : Monotone (j.succ.succAbove) := (Fin.strictMono_succAbove _).monotone
  refine ⟨h1, fun k => h2 _, h3, h4, fun k => h5 _, h6, fun t ht => (h7 t ht).comp_monotone hmono,
    fun t ht k => h8 t ht _, h9, h10, fun t ht k => h11 t ht _, h12, fun t ht => ?_,
    fun t ht k => h14 t ht _, h15, fun k => h16 _, h17, fun t ht hth => ?_,
    fun h => absurd h ENNReal.top_ne_zero, fun T _ hT => absurd hT ENNReal.coe_ne_top⟩
  · rw [h13 t ht]
    congr 2
    have hint : ∀ i ∈ Finset.univ, IntervalIntegrable
        (fun s : ℝ => ρL i / (w s.toNNReal - vL i s.toNNReal)) volume 0 t := fun i _ =>
      ((h11 t ht i).const_mul (ρL i)).congr fun s _ => (div_eq_mul_inv _ _).symm
    have hint' : ∀ k ∈ Finset.univ, IntervalIntegrable
        (fun s : ℝ => mergeAdj ρL j k / (w s.toNNReal - vL (j.succ.succAbove k) s.toNNReal)) volume 0 t :=
      fun k _ => ((h11 t ht _).const_mul (mergeAdj ρL j k)).congr fun s _ => (div_eq_mul_inv _ _).symm
    rw [← intervalIntegral.integral_finsetSum hint, ← intervalIntegral.integral_finsetSum hint']
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [div_eq_mul_inv]
    exact (sum_mergeAdj_mul ρL j (fun i => (w s.toNNReal - vL i s.toNNReal)⁻¹)
      (by simp only [hco])).symm
  · refine h18 t ht (hth.imp (fun hl => ?_) id)
    have e : ∀ (ρ : Fin (n + 2) → ℝ) (v : Fin (n + 2) → ℝ) (x : ℝ),
        (∑ i ∈ Finset.univ.filter (fun i => v i = x), ρ i) = ∑ i, ρ i * (if v i = x then 1 else 0) := by
      intro ρ v x
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    rw [e]
    rw [Finset.sum_filter] at hl
    rw [← sum_mergeAdj_mul ρL j (fun i => if vL i t = w t then 1 else 0) (by simp only [hco])]
    convert hl using 2 with k
    split_ifs <;> simp

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Merging adjacent coincident left marks** (infinite lifetime almost surely). -/
theorem IsIntegratedSLEEvolution.mergeAdjL {xL ρL : Fin (n + 2) → ℝ} {xR ρR : Fin nR → ℝ}
    {VL : Fin (n + 2) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} (j : Fin (n + 1))
    (hj : xL j.castSucc = xL j.succ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    IsIntegratedSLEEvolution κ (fun k => xL (j.succ.succAbove k)) xR (mergeAdj ρL j) ρR P 𝓕 W
      (fun k => VL (j.succ.succAbove k)) VR B ζ := by
  obtain ⟨hB, hW, hVL, hVR, hpath⟩ := hE
  refine ⟨hB, hW, fun k => hVL _, hVR, ?_⟩
  filter_upwards [hpath, hζ] with ω hp hζω
  rw [hζω] at hp ⊢
  exact Zhan.IsIntegratedSLEPath.mergeAdjL j hj hp

/-- **Merging adjacent coincident right marks** (infinite lifetime almost surely), by reflection. -/
theorem IsIntegratedSLEEvolution.mergeAdjR {nL : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin (n + 2) → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (n + 2) → ℝ≥0 → Ω → ℝ} (j : Fin (n + 1))
    (hj : xR j.castSucc = xR j.succ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    IsIntegratedSLEEvolution κ xL (fun k => xR (j.succ.succAbove k)) ρL (mergeAdj ρR j) P 𝓕 W VL
      (fun k => VR (j.succ.succAbove k)) B ζ := by
  have h1 := InteractingSLE.IsIntegratedSLEEvolution.reflect hE
  have h2 := IsIntegratedSLEEvolution.mergeAdjL (xL := -xR) (VL := fun i => -VR i) j
    (by simp only [Pi.neg_apply, hj]) h1 hζ
  have h3 := InteractingSLE.IsIntegratedSLEEvolution.reflect h2
  convert h3 using 1 <;> (funext k; simp only [Pi.neg_apply, neg_neg])

end InteractingSLE.Zhan
