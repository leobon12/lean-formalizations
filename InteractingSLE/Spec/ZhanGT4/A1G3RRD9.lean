/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3RRFrozen
import InteractingSLE.Spec.ZhanGT4.A1LargeDensD9
import InteractingSLE.Spec.ZhanGT4.A1G3IdView

/-!
# Zhan's A.1 (G3): the (D9) facts of the opposite view, uniformly in the large curve

Packet PROVE-A1-G3RECTROW. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L341, (D9): "the
constants depend only on the enclosures and the time bound") and follow-up 4 §2.5 item 1 (R71).

The row of the (G3) seeded field at a fixed small own time `a` is read through A1-EIGHTFIN's opposite view
`eView … a` (curve `2` grows, curve `1` frozen at `a`, the small curve's accesses `V m a − p` as marks). A1-LARGEDENS's
`exists_twoCurveD9_left_marks` gives (D9) facts (`TwoCurveD9`) uniform in the growing curve for frozen-chart marks
**strictly left of the frozen image of a protected point**. The (G3) ordinary mark may sit at the protected point `q`
itself (`x − y ≤ q`), so the protected point used here is `q + dd` (still protected, with half the radius). This file
supplies the hypotheses:

* `exists_pos_le_of_fintype`: a positive lower bound of finitely many positive numbers;
* `G3Setup.marks_le`: the marks at a positive own time lie at most at the image `g_a(q) + W_a` of the protected point;
* **`exists_twoCurveD9_eView`**: for the fixed small curve at `a`, constants `r, a₀, γ, Γ, λ` such that the opposite
  view of every rectangle (`ViewSetup`, any large curve) satisfies `TwoCurveD9` on `[0, Y]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4.A1G3RR

open QuantumZipper (IsForwardSol fwdMap fwdHull)
open A1SeedField A1EightSeed A1EightFin A1G3Calc A1G3Id

/-- A positive lower bound of finitely many positive numbers. -/
theorem exists_pos_le_of_fintype {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ν > (0 : ℝ), ∀ i, ν ≤ f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    exact ⟨f i₀, hf i₀, fun i => hi₀ i (Finset.mem_univ i)⟩

/-- **The marks lie at most at the image of the protected point** at a positive own time, when the left seed lies
left of the driver. -/
theorem G3Setup.marks_le {n : ℕ} {H₁ H₂ : Set ℂ} {δ p q dd Tm : ℝ} {W₁ V₂ : ℝ → ℝ} {S Y : ℝ}
    {Vlo Vhi : ℝ → ℝ} {V : Fin n → ℝ → ℝ} (h : G3Setup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi V) {a : ℝ}
    (ha : a ∈ Ioc (0 : ℝ) S) (hlo : Vlo a ≤ W₁ a) (m : Fin n) : V m a ≤ (fwdMap W₁ a q).re + W₁ a := by
  have haI : a ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self ha
  have hlt : Vlo a < W₁ a := lt_of_le_of_ne hlo (h.view.lo.ne a ha)
  have hW := h.drvE a haI
  have hX : W₁ a ≤ (fwdMap W₁ a q).re + W₁ a := by
    rw [mem_uIcc] at hW
    rcases hW with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact h2
    · linarith
  have hV := h.marks a haI m
  rw [mem_uIcc] at hV
  rcases hV with ⟨-, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · linarith

/-- **The (D9) facts of the opposite view, uniformly in the large curve.** For a protected pair and a fixed small
curve at a positive own time `a ≤ S` (hull in `H₁`), whose marks at `a` lie at most at the image of the protected
point, avoid the driver and are distinct, there are constants `r, a₀, γ, Γ, λ` such that for every parameter, all
charges and every rectangle (`ViewSetup`) with any large curve `V₂` up to any `Y`, the opposite view at `a` satisfies
`TwoCurveD9` on `[0, Y]` with the frozen hull `fwdHull (W₁ − p) a`. -/
theorem exists_twoCurveD9_eView {n : ℕ} {H₁ H₂ : Set ℂ} {δ p q dd Tm : ℝ}
    (hpp : IsProtectedPair H₁ H₂ δ p q dd) {W₁ : ℝ → ℝ} {S a : ℝ} {V : Fin n → ℝ → ℝ} (ha : a ∈ Ioc (0 : ℝ) S)
    (hW₁ : Continuous W₁) (hW₁0 : W₁ 0 = 0) (hSTm : S ≤ Tm) (hK₁ : fwdHull W₁ S ⊆ H₁)
    (hVq : ∀ m, V m a ≤ (fwdMap W₁ a q).re + W₁ a) (hVW : ∀ m, V m a ≠ W₁ a)
    (hVinj : Function.Injective fun m => V m a) :
    ∃ r a₀ γ Γ lam : ℝ, 0 < r ∧ 0 < a₀ ∧ 0 < γ ∧ ∀ (κ : ℝ) (rr : Fin n → ℝ) (V₂ : ℝ → ℝ) (Y : ℝ)
      (Vlo Vhi : ℝ → ℝ), ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi →
      TwoCurveD9 (eView κ rr W₁ V₂ S Y V a) (fwdHull (fun u => W₁ u - p) a) Y r a₀ γ Γ lam := by
  have hd := hpp.rad_pos
  have hq := hpp.prot_pos
  -- the separations of the marks
  obtain ⟨ν₁, hν₁, hν₁le⟩ := exists_pos_le_of_fintype (fun m => |V m a - W₁ a|)
    (fun m => abs_pos.2 (sub_ne_zero.2 (hVW m)))
  obtain ⟨ν₂, hν₂, hν₂le⟩ := exists_pos_le_of_fintype
    (fun mk : Fin n × Fin n => if mk.1 = mk.2 then 1 else |V mk.1 a - V mk.2 a|) (fun mk => by
      by_cases hmk : mk.1 = mk.2
      · simp only [hmk, ↓reduceIte, one_pos]
      · simp only [hmk, ↓reduceIte]
        exact abs_pos.2 (sub_ne_zero.2 fun he => hmk (hVinj he)))
  set M := ∑ m, |V m a - p| with hM
  -- the protected point `q + dd`, in the large curve's frame
  have hqpd : q + dd < p := by
    have hpq := notMem_ball_of_mem_closure (hpp.prot.mono_right subset_union_right) hpp.src
    rw [mem_ball, dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, not_lt,
      abs_of_pos (sub_pos.2 hpp.prot_lt)] at hpq
    linarith
  have hqL : q + dd - p < 0 := by linarith
  have hdL : 0 < dd / 2 := by positivity
  have hball : Disjoint (ball ((q + dd : ℝ) : ℂ) dd) (H₁ ∪ H₂) := hpp.prot.mono_left fun z hz => by
    rw [mem_ball, dist_eq_norm] at hz ⊢
    calc ‖z - (q : ℂ)‖ = ‖(z - ((q + dd : ℝ) : ℂ)) + (dd : ℂ)‖ := by push_cast; ring_nf
      _ ≤ ‖z - ((q + dd : ℝ) : ℂ)‖ + ‖(dd : ℂ)‖ := norm_add_le _ _
      _ < dd + dd := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]; linarith
      _ = 2 * dd := by ring
  have hqH : Disjoint (ball (((q + dd - p : ℝ)) : ℂ) (2 * (dd / 2))) (transl (-p) H₂ ∪ transl (-p) H₁) := by
    have h := disjoint_ball_transl hball (-p)
    rw [show 2 * (dd / 2) = dd by ring, show q + dd - p = q + dd + -p by ring]
    rw [transl, transl, ← Set.image_union, Set.union_comm]
    exact h
  have hsepδ : ∀ a ∈ transl (-p) H₁, ∀ z ∈ transl (-p) H₂, 2 * δ ≤ ‖a - z‖ :=
    sep_transl (fun a ha z hz => by rw [norm_sub_rev]; exact hpp.sep z hz a ha) (-p)
  obtain ⟨r, a₀, γ, Γ, lam, hr, ha₀, hγ, hmain⟩ := A1LargeDens.exists_twoCurveD9_left_marks
    (isHPHull_transl hpp.hull₂ (-p)) (isHPHull_transl hpp.hull₁ (-p)) hpp.sep_pos hsepδ hdL hqL hqH (M := M)
    (lt_min hν₁ hν₂) n Tm
  refine ⟨r, a₀, γ, Γ, lam, hr, ha₀, hγ, fun κ rr V₂ Y Vlo Vhi h => ?_⟩
  have hz : V₂ 0 = p := h.zero₂
  have e : eView κ rr W₁ V₂ S Y V a = ⟨fun u => V₂ u - p, tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) a,
      tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) a, frzChart (fun u => W₁ u - p) a, 16 / κ,
      fun m => -(κ / 4) * rr m, W₁ a - p, fun m => V m a - p⟩ := by
    simp only [eView, hz]
  rw [e]
  have haI : a ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self ha
  obtain ⟨hown, -⟩ := h.tOwn haI
  rw [hz] at hown
  -- the protected points `q`, `q + dd` are alive for the small curve up to `S`
  obtain ⟨uq, huq⟩ := exists_isForwardSol_of_disjoint_ball_gen hW₁ (x := q) (by rw [hW₁0]; exact hq.ne')
    h.pos₁.le (by positivity) ((hpp.prot.mono_right subset_union_left).mono_right hK₁)
  obtain ⟨uqd, huqd⟩ := exists_isForwardSol_of_disjoint_ball_gen hW₁ (x := q + dd)
    (by rw [hW₁0]; linarith) h.pos₁.le hd ((hball.mono_right subset_union_left).mono_right hK₁)
  have hlt := QuantumZipper.F1.isForwardSol_lt_of_lt h.pos₁.le (by linarith : q < q + dd) huq huqd a haI
  have hW0H : ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ := closure_mono hK₁ (start_mem_closure_fwdHull hW₁ h.pos₁)
  refine hmain (fun u => V₂ u - p) (fun u => W₁ u - p) a Y _ _ (16 / κ) (fun m => -(κ / 4) * rr m)
    (fun m => V m a - p) hown (hW₁.sub continuous_const) ?_ ?_ ha.1 (ha.2.trans hSTm) h.le₂
    (fwdHull_sub_const_subset h.K₂) (fwdHull_sub_const_subset (((QuantumZipper.fwdHull_mono).1 ha.2).trans hK₁))
    (fun m => ?_) (fun m => ?_) (fun m => ?_) (fun m k hmk => ?_)
  · have := mem_closure_transl hW0H (-p)
    simpa only [hW₁0, ofReal_zero, zero_add, ofReal_neg, zero_sub] using this
  · simp only [hW₁0]; linarith
  · rw [fwdMap_sub_const, show ((q + dd - p : ℝ) : ℂ) + (p : ℂ) = ((q + dd : ℝ) : ℂ) by push_cast; ring,
      fwdMap_eq_of_isForwardSol hW₁ huqd haI]
    rw [fwdMap_eq_of_isForwardSol hW₁ huq haI] at hVq
    linarith [hVq m]
  · exact Finset.single_le_sum (f := fun m => |V m a - p|) (fun i _ => abs_nonneg _) (Finset.mem_univ m)
  · simp only [sub_sub_sub_cancel_right]
    exact (min_le_left _ _).trans (hν₁le m)
  · simp only [sub_sub_sub_cancel_right]
    have := hν₂le (m, k)
    simp only [hmk, ↓reduceIte] at this
    exact (min_le_right _ _).trans this

end InteractingSLE.ZhanGT4.A1G3RR
