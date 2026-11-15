/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetAux79Zone

/-!
# (III-b) at a later line for arbitrary words: the force data from the transported word and the slit heights

Packet PROVE-T15-ORDDET (Theorem 1.5's leaf 3; PROVE-DOMAINMARKOV8 §2 (III-b)). PROVE-RETAUX79B proved the boundary-data
identity of a later line of Lemma 7.6's retained continuation for the explicit zone words of disjoint pairs
(`RetAux79.forceBoundaryData_eq_zword_add`). Its proof uses the zone words at exactly two places: the transport of the
word along the real flow at alive points, and the side heights on the two images of the new piece. This file states the
assembly for **arbitrary** words `β₀` (stop line) and `βₜ` (later line) with these two facts as hypotheses:

* **(transport)** `βₜ(u(Q)) = β₀(x)` for every real `x` with a forward solution `u` up to `Q` (off the jumps) — proved
  for mean-identified words of every retained pair by `OrdDet.ae_fn_eq_of_trans` (Aux. lemma 79 by nested Proposition
  3.8, `OrdDetLine.lean`);
* **(slit heights)** `βₜ = −λ − θχ` on `(V̂^{0,L}_Q, 0)` and `λ − θχ` on `(0, V̂^{0,R}_Q)` off a finite set (the
  images of the two sides of the new piece carry the canonical new-side heights).

**`forceBoundaryData_eq_add_of_transport`**: off a finite set, the force data of the flow-line word of `β₀` at the
flowed marks equal `βₜ + θχ`. The proof is RETAUX79B's, with the two facts in place of the zone-word lemmas.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE

namespace RLC

namespace OrdDet

open Restart Restart.RetAux79 MartChar.RealFlow

/-- **(III-b) for arbitrary words** (see the module docstring). -/
theorem forceBoundaryData_eq_add_of_transport {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) {W : ℝ≥0 → ℝ} (hWc : Continuous W)
    {Q : ℝ≥0} {β₀ βt : BoundaryWord}
    (htr : ∀ (x : ℝ) (v : ℝ → ℂ), QuantumZipper.IsForwardSol (fun s : ℝ => W s.toNNReal) (x : ℂ) Q v →
      x ∉ β₀.jumps → (v Q).re ∉ βt.jumps → βt.fn (v Q).re = β₀.fn x)
    {S' : Set ℝ} (hS' : S'.Finite)
    (hslitL : ∀ y ∉ S', -rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q < y → y < 0 →
      βt.fn y = -sleLambda κ - θ * QuantumZipper.chiC κ)
    (hslitR : ∀ y ∉ S', 0 < y → y < rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q →
      βt.fn y = sleLambda κ - θ * QuantumZipper.chiC κ) :
    ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
      forceBoundaryData κ (flowLineRhoL κ β₀.fn β₀.jumps 0 θ) (flowLineRhoR κ β₀.fn β₀.jumps 0 θ)
          (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-flowLineXL β₀.fn β₀.jumps 0 i) Q - W Q)
          (fun j => rightImg (fun s : ℝ => W s.toNNReal) (flowLineXR β₀.fn β₀.jumps 0 j) Q - W Q) y =
        βt.fn y + θ * QuantumZipper.chiC κ := by
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  have hw'c : Continuous w' := hWc.comp continuous_real_toNNReal
  have hw'n : Continuous fun s => -w' s := hw'c.neg
  have hQr : (0 : ℝ) ≤ Q := Q.coe_nonneg
  have hwQ : W Q = w' Q := by simp [hw']
  rw [hwQ]
  rw [hwQ] at hslitL hslitR
  set χ := QuantumZipper.chiC κ with hχ
  set xL := flowLineXL β₀.fn β₀.jumps 0 with hxL
  set xR := flowLineXR β₀.fn β₀.jumps 0 with hxR
  set ρL := flowLineRhoL κ β₀.fn β₀.jumps 0 θ with hρL
  set ρR := flowLineRhoR κ β₀.fn β₀.jumps 0 θ with hρR
  set vL : Fin (flowLineNL β₀.fn β₀.jumps 0) → ℝ :=
    fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-xL i) Q - w' Q with hvL
  set ϱ := rightImg w' 0 Q - w' Q with hϱ
  set ℓ := -rightImg (fun s => -w' s) 0 Q - w' Q with hℓ
  set fR : ℝ → ℝ := fun x => gImg w' x Q - w' Q with hfR
  set fL : ℝ → ℝ := fun x => -gImg (fun s => -w' s) (-x) Q - w' Q with hfL
  set S₀ : Set ℝ := (β₀.jumps : Set ℝ) with hS₀
  have hS₀f : S₀.Finite := β₀.jumps.finite_toSet
  refine ⟨{0, ϱ, ℓ} ∪ Set.range vL ∪ fR '' S₀ ∪ fL '' S₀ ∪ (βt.jumps : Set ℝ) ∪ S',
    (((((Set.toFinite _).union (Set.finite_range vL)).union (hS₀f.image fR)).union (hS₀f.image fL)).union
      βt.jumps.finite_toSet).union hS', ?_⟩
  intro y hy
  have hyA : ∀ c ∈ ({0, ϱ, ℓ} : Set ℝ), y ≠ c := fun c hc h =>
    hy (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h ▸ hc))))))
  have hy0 : y ≠ 0 := hyA 0 (by simp)
  have hyϱ : y ≠ ϱ := hyA ϱ (by simp)
  have hyℓ : y ≠ ℓ := hyA ℓ (by simp)
  have hyv : ∀ i, y ≠ vL i := fun i h => hy (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, h.symm⟩)))))
  have hyJ : y ∉ βt.jumps := fun h => hy (Or.inl (Or.inr h))
  have hyS' : y ∉ S' := fun h => hy (Or.inr h)
  have hseed : ∀ x, x ≠ 0 → x ∉ β₀.jumps → forceBoundaryData κ ρL ρR xL xR x = β₀.fn x + θ * χ := by
    intro x hx0 hxJ'
    have h := Exist.forceBoundaryData_flowLine_seed hκ (BoundaryWord.isPiecewiseConstantBoundaryData β₀) 0 θ hx0
      (by rwa [add_zero])
    rwa [add_zero] at h
  have hlam : sleLambda κ = Real.pi / Real.sqrt κ := rfl
  rcases lt_trichotomy y 0 with hyneg | rfl | hypos
  · rcases lt_trichotomy y ℓ with hyl | rfl | hyl
    · -- left of the image of `0⁻`: a flowed alive negative point
      obtain ⟨xt, hxt0, hxta, hxtg⟩ := exists_alive_gImg_eq hw'n hQr (M := -y - w' Q) (by
        have : y < -rightImg (fun s => -w' s) 0 Q - w' Q := hyl
        linarith)
      have hyx : fL (-xt) = y := by
        simp only [hfL, neg_neg]
        rw [hxtg]
        ring
      have hxS : -xt ∉ S₀ := fun hx => hy (Or.inl (Or.inl (Or.inr ⟨-xt, hx, hyx⟩)))
      have hu := WangWu.isForwardSol_neg_of_alive hw'c hxta
      have hu' : QuantumZipper.IsForwardSol w' ((-xt : ℝ) : ℂ) Q
          (fun s => -(cflow (fun s => -w' s) xt s : ℂ)) := by
        rw [Complex.ofReal_neg]; exact hu
      have huQ : (-(cflow (fun s => -w' s) xt Q : ℂ)).re = y := by
        have e : gImg (fun s => -w' s) xt Q = -w' Q + cflow (fun s => -w' s) xt Q := rfl
        simp only [neg_re, ofReal_re]
        linarith
      have hZ := htr (-xt) _ hu' hxS (by rw [huQ]; exact hyJ)
      rw [huQ] at hZ
      have hxL' : ∀ i, -xL i ≠ xt := by
        intro i h
        rcases flowLineXL_eq_zero_or_mem β₀ i with h0 | ⟨-, hm⟩
        · rw [← hxL] at h0
          rw [h0, neg_zero] at h
          exact (lt_irrefl _ (h ▸ hxt0))
        · rw [← hxL] at hm
          have : xL i = -xt := by linarith
          exact hxS (this ▸ hm)
      have hgy : -gImg (fun s => -w' s) xt Q - w' Q = y := by linarith
      have hyv' : ∀ i, -gImg (fun s => -w' s) xt Q - w' Q ≠ -rightImg (fun s => -w' s) (-xL i) Q - w' Q := by
        intro i h
        apply hyv i
        rw [← hgy, h]
      have hF := forceBoundaryData_flow_left ρL ρR (κ := κ) (xR := xR) hw'c hQr hxt0 hxta hxL' hyv'
      rw [hgy] at hF
      have hx0 : -xt ≠ 0 := neg_ne_zero.2 hxt0.ne'
      exact hF.trans ((hseed _ hx0 hxS).trans (by rw [hZ]))
    · exact absurd rfl hyℓ
    · -- the image of the left side of the new piece
      have hF := forceBoundaryData_flow_slit_left ρL ρR (κ := κ) (xR := xR) hw'c hQr
        (fun i => by
          rcases flowLineXL_eq_zero_or_mem β₀ i with h0 | ⟨h0, -⟩
          · exact h0.le
          · exact h0.le) hyneg hyl
      have hw := hslitL y hyS' hyl hyneg
      have hfin : -(Real.pi / Real.sqrt κ) = βt.fn y + θ * χ := by rw [hw, hlam]; ring
      exact hF.trans hfin
  · exact absurd rfl hy0
  · rcases lt_trichotomy y ϱ with hyr | rfl | hyr
    · -- the image of the right side of the new piece
      have hF := forceBoundaryData_flow_slit_right ρL ρR (κ := κ) (xL := xL) hw'c hQr
        (fun j => by
          rcases flowLineXR_eq_zero_or_mem β₀ j with h0 | ⟨h0, -⟩
          · exact h0.ge
          · exact h0.le) hypos.le hyr
      have hw := hslitR y hyS' hypos hyr
      have hfin : Real.pi / Real.sqrt κ = βt.fn y + θ * χ := by rw [hw, hlam]; ring
      exact hF.trans hfin
    · exact absurd rfl hyϱ
    · -- right of the image of `0⁺`: a flowed alive positive point
      obtain ⟨x, hx0, hxa, hxg⟩ := exists_alive_gImg_eq hw'c hQr (M := y + w' Q) (by
        have : rightImg w' 0 Q - w' Q < y := hyr
        linarith)
      have hyx : fR x = y := by
        simp only [hfR]
        rw [hxg]
        ring
      have hxS : x ∉ S₀ := fun hx => hy (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, hx, hyx⟩))))
      have hu := WangWu.isForwardSol_of_alive hw'c hxa
      have huQ : ((cflow w' x Q : ℝ) : ℂ).re = y := by
        have e : gImg w' x Q = w' Q + cflow w' x Q := rfl
        simp only [ofReal_re]
        linarith
      have hZ := htr x _ hu hxS (by rw [huQ]; exact hyJ)
      rw [huQ] at hZ
      have hxR' : ∀ j, xR j ≠ x := by
        intro j h
        rcases flowLineXR_eq_zero_or_mem β₀ j with h0 | ⟨-, hm⟩
        · rw [← hxR] at h0
          rw [h0] at h
          exact (lt_irrefl _ (h ▸ hx0))
        · rw [← hxR] at hm
          exact hxS (h ▸ hm)
      have hF := forceBoundaryData_flow_right ρL ρR (κ := κ) (xL := xL) hw'c hQr hx0 hxa hxR'
      have hgy : gImg w' x Q - w' Q = y := by linarith
      rw [hgy] at hF
      exact hF.trans ((hseed _ hx0.ne' hxS).trans (by rw [hZ]))

end OrdDet

end RLC

end InteractingSLE
