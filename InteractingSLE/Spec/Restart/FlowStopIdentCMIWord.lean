/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Ito.Mean

/-!
# The difference of the explicit means of two flow-line words

Packet PROVE-L1-CMI (Lemma G3's proof, supplement §7.3, pp. 492–493; Aux. lemma 61, (PC1), pp. 261–262: "the
difference of the reference and actual canonical means"). Two flow lines from the same seed `y` at the same angle `θ`
of fields with piecewise constant data `b` and `bR` that agree on an open set `O ∋ y` have force words that agree on
the marks in `O` (same positions, same weights) and on the seed marks. The explicit mean of a word (`Ito.meanHarmonic`,
which every bounded harmonic extension of the force-word boundary data equals, `Ito.eqOn_meanHarmonic`) is an arg sum
over its marks, so the difference of the two means is an arg sum over the marks **off `O`** only:

* `jmp b p = b(p⁺) − b(p⁻)`;
* `sum_flowLineL`, `sum_flowLineR`: a weighted sum over the marks of a flow-line word, as the seed term plus a sum over
  the jump candidates;
* **`meanHarmonic_flowLine_sub`**: for any positions `ΦL`, `ΦR` of the left and right marks (read off the initial
  positions), `meanHarmonic^{bR} − meanHarmonic^{b} = ∑_{p ∈ M} (Δ p · [y < p] − (Δ p / π) arg (w − Φ(p − y)))`, with
  `M` the jump candidates off `O` and `Δ p = jmp bR p − jmp b p`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Finset

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCMI

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-- The jump `b(p⁺) − b(p⁻)`. -/
def jmp (b : ℝ → ℝ) (p : ℝ) : ℝ := rightLim b p - leftLim b p

section Lim

variable {b bR : ℝ → ℝ} {J : Finset ℝ}

/-- Off its jump candidates, piecewise constant data do not jump. -/
theorem jmp_eq_zero_of_notMem (hb : IsPiecewiseConstantBoundaryData b J) {p : ℝ} (hp : p ∉ J) : jmp b p = 0 := by
  have hc := hb p hp
  have h1 : Tendsto b (𝓝[<] p) (𝓝 (b p)) :=
    tendsto_const_nhds.congr' ((hc.filter_mono nhdsWithin_le_nhds).mono fun z hz => hz.symm)
  have h2 : Tendsto b (𝓝[>] p) (𝓝 (b p)) :=
    tendsto_const_nhds.congr' ((hc.filter_mono nhdsWithin_le_nhds).mono fun z hz => hz.symm)
  show limUnder (𝓝[>] p) b - limUnder (𝓝[<] p) b = 0
  rw [h1.limUnder_eq, h2.limUnder_eq, sub_self]

/-- Data agreeing near a point have the same one-sided limits there. -/
theorem leftLim_eq_of_eventuallyEq {p : ℝ} (h : b =ᶠ[𝓝 p] bR) : leftLim b p = leftLim bR p := by
  show limUnder (𝓝[<] p) b = limUnder (𝓝[<] p) bR
  unfold limUnder
  rw [Filter.map_congr (h.filter_mono nhdsWithin_le_nhds)]

theorem rightLim_eq_of_eventuallyEq {p : ℝ} (h : b =ᶠ[𝓝 p] bR) : rightLim b p = rightLim bR p := by
  show limUnder (𝓝[>] p) b = limUnder (𝓝[>] p) bR
  unfold limUnder
  rw [Filter.map_congr (h.filter_mono nhdsWithin_le_nhds)]

theorem eventuallyEq_of_isOpen {O : Set ℝ} (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {p : ℝ} (hp : p ∈ O) :
    b =ᶠ[𝓝 p] bR :=
  Filter.mem_of_superset (hO.mem_nhds hp) fun x hx => hbO x hx

theorem jmp_eq_of_mem {O : Set ℝ} (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {p : ℝ} (hp : p ∈ O) :
    jmp b p = jmp bR p := by
  have h := eventuallyEq_of_isOpen hO hbO hp
  rw [jmp, jmp, leftLim_eq_of_eventuallyEq h, rightLim_eq_of_eventuallyEq h]

/-- A sum over the genuine jumps of `b` is a sum over any finite superset of its jump candidates. -/
theorem sum_jumpSet_filter_eq (hb : IsPiecewiseConstantBoundaryData b J) {K : Finset ℝ} (hJK : J ⊆ K)
    (P : ℝ → Prop) [DecidablePred P] (g : ℝ → ℝ) :
    ∑ p ∈ (jumpSet b J).filter P, jmp b p * g p = ∑ p ∈ K.filter P, jmp b p * g p := by
  refine Finset.sum_subset (fun z hz => ?_) fun z hz hzn => ?_
  · obtain ⟨hzJ, hP⟩ := Finset.mem_filter.1 hz
    exact Finset.mem_filter.2 ⟨hJK (Finset.mem_filter.1 hzJ).1, hP⟩
  · obtain ⟨-, hP⟩ := Finset.mem_filter.1 hz
    by_cases hzJ : z ∈ J
    · have : ¬ (leftLim b z ≠ rightLim b z) := fun hne =>
        hzn (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hzJ, hne⟩, hP⟩)
      rw [not_not] at this
      rw [jmp, this, sub_self, zero_mul]
    · rw [jmp_eq_zero_of_notMem hb hzJ, zero_mul]

end Lim

/-! ### Sums over the marks of a flow-line word -/

section Sums

variable (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (y θ : ℝ)

/-- **A weighted sum over the left marks of a flow-line word**: the seed term plus a sum over the genuine left
jumps. -/
theorem sum_flowLineL (g : ℝ → ℝ) :
    ∑ i, flowLineRhoL κ b J y θ i * g (flowLineXL b J y i) =
      (-(leftLim b y + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) * g 0 +
        ∑ p ∈ (jumpSet b J).filter (· < y), jmp b p * (g (p - y) / sleLambda κ) := by
  unfold flowLineRhoL flowLineXL flowLineNL
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  have h := Sec4.sum_filter_orderEmbOfFin_rev ((jumpSet b J).filter (· < y)) (fun _ => True)
    (fun p => jmp b p * (g (p - y) / sleLambda κ))
  simp only [Finset.filter_true] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [jmp]
  ring

/-- **A weighted sum over the right marks of a flow-line word.** -/
theorem sum_flowLineR (g : ℝ → ℝ) :
    ∑ i, flowLineRhoR κ b J y θ i * g (flowLineXR b J y i) =
      ((rightLim b y + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) * g 0 +
        ∑ p ∈ (jumpSet b J).filter (y < ·), jmp b p * (g (p - y) / sleLambda κ) := by
  unfold flowLineRhoR flowLineXR flowLineNR
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  have h := Sec4.sum_filter_orderEmbOfFin ((jumpSet b J).filter (y < ·)) (fun _ => True)
    (fun p => jmp b p * (g (p - y) / sleLambda κ))
  simp only [Finset.filter_true] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [jmp]
  ring

end Sums

/-! ### The difference of the two explicit means -/

section Diff

variable {κ : ℝ} {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ} {O : Set ℝ}

/-- The marks off `O`: the jump candidates of both data that are not in `O`. -/
def offMarks (J Ĵ : Finset ℝ) (O : Set ℝ) [DecidablePred (· ∈ O)] : Finset ℝ := (J ∪ Ĵ).filter (· ∉ O)

/-- A difference of jump sums over the genuine jumps of `bR` and `b` is a sum over the marks off `O`. -/
theorem sum_jumpSet_sub (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR Ĵ)
    (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) [DecidablePred (· ∈ O)] (P : ℝ → Prop) [DecidablePred P]
    (g : ℝ → ℝ) :
    ∑ p ∈ (jumpSet bR Ĵ).filter P, jmp bR p * g p - ∑ p ∈ (jumpSet b J).filter P, jmp b p * g p =
      ∑ p ∈ (offMarks J Ĵ O).filter P, (jmp bR p - jmp b p) * g p := by
  rw [sum_jumpSet_filter_eq hbR (Finset.subset_union_right (s₁ := J)) P g,
    sum_jumpSet_filter_eq hb (Finset.subset_union_left (s₂ := Ĵ)) P g, ← Finset.sum_sub_distrib]
  have e : ∀ p ∈ (J ∪ Ĵ).filter P, jmp bR p * g p - jmp b p * g p = (jmp bR p - jmp b p) * g p :=
    fun p _ => by ring
  rw [Finset.sum_congr rfl e]
  symm
  refine Finset.sum_subset (fun z hz => ?_) fun z hz hzn => ?_
  · obtain ⟨hzM, hP⟩ := Finset.mem_filter.1 hz
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hzM).1, hP⟩
  · obtain ⟨hzK, hP⟩ := Finset.mem_filter.1 hz
    have hzO : z ∈ O := by
      by_contra hzO
      exact hzn (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hzK, hzO⟩, hP⟩)
    rw [jmp_eq_of_mem hO hbO hzO, sub_self, zero_mul]

/-- **The difference of the explicit means of the two flow-line words is an arg sum over the marks off `O`.** For
any positions `ΦL`, `ΦR` of the left and right marks read off their initial positions (in particular the common marks
in `O` and the seed marks sit at the same positions in both words), and every `w`,
`meanHarmonic^{bR}(w) − meanHarmonic^{b}(w) = ∑_{p ∈ M} (Δ p · [y < p] − (Δ p / π) arg(w − Φ(p − y)))`,
`Δ p = jmp bR p − jmp b p`, `Φ = ΦL` left of the seed and `ΦR` right of it. -/
theorem meanHarmonic_flowLine_sub (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR Ĵ) (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x)
    [DecidablePred (· ∈ O)] {y : ℝ} (hy : y ∈ O) (θ : ℝ) (ΦL ΦR : ℝ → ℝ) (w : ℂ) :
    Ito.meanHarmonic κ (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ)
        (fun i => ΦL (flowLineXL bR Ĵ y i)) (fun j => ΦR (flowLineXR bR Ĵ y j)) w -
      Ito.meanHarmonic κ (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ)
        (fun i => ΦL (flowLineXL b J y i)) (fun j => ΦR (flowLineXR b J y j)) w =
      ∑ p ∈ offMarks J Ĵ O, ((jmp bR p - jmp b p) * (if y < p then 1 else 0) -
        (jmp bR p - jmp b p) / Real.pi *
          Complex.arg (w - (((if p < y then ΦL (p - y) else ΦR (p - y)) : ℝ) : ℂ))) := by
  classical
  set lam := sleLambda κ with hlam
  have hsq : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hlam0 : lam ≠ 0 := by rw [hlam, sleLambda]; positivity
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  set gL : ℝ → ℝ := fun x => Complex.arg (w - ((ΦL x : ℝ) : ℂ)) with hgL
  set gR : ℝ → ℝ := fun x => Complex.arg (w - ((ΦR x : ℝ) : ℂ)) with hgR
  have hyev := eventuallyEq_of_isOpen hO hbO hy
  have hl : leftLim bR y = leftLim b y := (leftLim_eq_of_eventuallyEq hyev).symm
  have hr : rightLim bR y = rightLim b y := (rightLim_eq_of_eventuallyEq hyev).symm
  -- the three sums of each word
  have eL : ∀ (c : ℝ → ℝ) (K : Finset ℝ) (hc : IsPiecewiseConstantBoundaryData c K),
      ∑ i, flowLineRhoL κ c K y θ i * Complex.arg (w - ((ΦL (flowLineXL c K y i) : ℝ) : ℂ)) =
        (-(leftLim c y + θ * QuantumZipper.chiC κ) / lam - 1) * gL 0 +
          ∑ p ∈ (jumpSet c K).filter (· < y), jmp c p * (gL (p - y) / lam) := fun c K _ =>
    sum_flowLineL κ c K y θ gL
  have eR : ∀ (c : ℝ → ℝ) (K : Finset ℝ) (hc : IsPiecewiseConstantBoundaryData c K),
      ∑ i, flowLineRhoR κ c K y θ i * Complex.arg (w - ((ΦR (flowLineXR c K y i) : ℝ) : ℂ)) =
        ((rightLim c y + θ * QuantumZipper.chiC κ) / lam - 1) * gR 0 +
          ∑ p ∈ (jumpSet c K).filter (y < ·), jmp c p * (gR (p - y) / lam) := fun c K _ =>
    sum_flowLineR κ c K y θ gR
  have eS : ∀ (c : ℝ → ℝ) (K : Finset ℝ), ∑ i, flowLineRhoR κ c K y θ i =
      ((rightLim c y + θ * QuantumZipper.chiC κ) / lam - 1) +
        ∑ p ∈ (jumpSet c K).filter (y < ·), jmp c p * (1 / lam) := fun c K => by
    have h := sum_flowLineR κ c K y θ (fun _ => 1)
    simp only [mul_one] at h
    rw [h]
  -- the differences
  have dL := sum_jumpSet_sub hb hbR hO hbO (· < y) fun p => gL (p - y) / lam
  have dR := sum_jumpSet_sub hb hbR hO hbO (y < ·) fun p => gR (p - y) / lam
  have dS := sum_jumpSet_sub hb hbR hO hbO (y < ·) fun _ => 1 / lam
  simp only [Ito.meanHarmonic]
  rw [eL bR Ĵ hbR, eL b J hb, eR bR Ĵ hbR, eR b J hb, eS bR Ĵ, eS b J, hl, hr]
  have split : ∀ (P : ℝ → Prop) [DecidablePred P] (G : ℝ → ℝ),
      ∑ p ∈ (offMarks J Ĵ O).filter P, G p = ∑ p ∈ offMarks J Ĵ O, if P p then G p else 0 :=
    fun P _ G => Finset.sum_filter _ _
  have hne : ∀ p ∈ offMarks J Ĵ O, p ≠ y := fun p hp hpy =>
    (Finset.mem_filter.1 hp).2 (hpy ▸ hy)
  -- express everything as sums over `M`
  have hT : ∑ p ∈ offMarks J Ĵ O, ((jmp bR p - jmp b p) * (if y < p then 1 else 0) -
        (jmp bR p - jmp b p) / Real.pi *
          Complex.arg (w - (((if p < y then ΦL (p - y) else ΦR (p - y)) : ℝ) : ℂ))) =
      1 / Real.sqrt κ * (Real.pi * ∑ p ∈ (offMarks J Ĵ O).filter (y < ·), (jmp bR p - jmp b p) * (1 / lam) -
        ∑ p ∈ (offMarks J Ĵ O).filter (· < y), (jmp bR p - jmp b p) * (gL (p - y) / lam) -
        ∑ p ∈ (offMarks J Ĵ O).filter (y < ·), (jmp bR p - jmp b p) * (gR (p - y) / lam)) := by
    rw [split, split, split, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hlk : 1 / Real.sqrt κ * (1 / lam) = 1 / Real.pi := by
      rw [hlam, sleLambda]; field_simp
    rcases lt_or_gt_of_ne (hne p hp) with hpy | hpy
    · simp only [hpy, not_lt.2 hpy.le, ↓reduceIte, mul_zero, zero_sub, hgL]
      rw [hlam, sleLambda]
      field_simp
      ring
    · simp only [hpy, not_lt.2 hpy.le, ↓reduceIte, mul_one, hgR]
      rw [hlam, sleLambda]
      field_simp
      ring
  rw [hT, ← dL, ← dR, ← dS]
  ring

end Diff

end FlowStopIdentCMI

end Restart

end InteractingSLE
