import QuantumZipper.Proofs.Zipper.ESMLMeas2

/-!
# ESM-LMEAS-3: the path functional for `L⁻_s` and the a.e. identity

Third part of the ESM-LMEAS task (node **E-SM**, obligation `hLad` of
`ESM.lintegral_levelTime_strongMarkov_lenA`, decision D21), after `ESMLMeas` (deterministic
congruence and the reduction to the stopped Brownian path `clampB`) and `ESMLMeas2` (the path
surrogate of the unzipped field and `ae_coordsFull_unzipFieldPath`).

* `fromCoords`, `unzipFieldCoord`: the coordinate reconstruction of the surrogate field, as a
  `FieldSample`-valued function of `(x, f)`.
* `nuSur`: the `BCert`-gated boundary measure of the unzipped field (the gating makes it
  measurable in the field, `E1.M4.measurable_qBoundaryMeasure_bCert`; a.s. the unzipped field
  is certified, so the gate is invisible).
* `lenMinusSur`: the resulting functional for `L⁻_s`.
* `ae_lenMinus_eq_surrogate`: **`L⁻_s = lenMinusSur (X, pathC s B)` a.s.**, from the field
  identity (`ae_coordsFull_unzipFieldPath`, proved), the side images (`hside`: the two side
  images of the stopped driver are `a ∘ pathC s B`; follows from `RS.ae_real_alive` and the
  monotonicity of `x ↦ fwdMap W s x` on alive real points) and the boundary certificate
  (`hgood`: the unzipped field is certified; an instance of `E1.ae_bCert_h0f` at `T = s`).
* `measurable_lenMinus_of_surrogate`: measurability of `L⁻_s` under any σ-algebra making
  `(X, pathC s B)` measurable and containing the `P`-null sets, from measurability of the
  deterministic functional `lenMinusSur` (see the report for the measurability of `lenMinusSur`
  itself: it is built from `B1Full.measurable_unzip_apply`,
  `E1.M4.measurable_qBoundaryMeasure_bCert` and the measurability of `(ν, b) ↦ ν (Icc b 0)`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace ESM

open F1 CoordsFull CharFun

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

open Classical in
/-- The field rebuilt from a coordinate list (value `c i` at the `i`-th dyadic folded circle,
with the least such index; `0` at all other measures). -/
def fromCoords (c : ℕ → ℝ) : FieldSample := fun μ =>
  if h : ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ then c (Nat.find h) else 0

/-- The coordinate reconstruction of the path–surrogate of the unzipped field. -/
def unzipFieldCoord (κ s : ℝ) (hs : 0 ≤ s) :
    FieldSample × C(Icc (0 : ℝ) s, ℝ) → FieldSample :=
  fun p => fromCoords (coordsFull (unzipFieldPath κ s hs p))

theorem coordsFull_unzipFieldCoord (κ s : ℝ) (hs : 0 ≤ s)
    (p : FieldSample × C(Icc (0 : ℝ) s, ℝ)) :
    coordsFull (unzipFieldCoord κ s hs p) = coordsFull (unzipFieldPath κ s hs p) := by
  classical
  funext i
  have h : ∃ j, foldedCircle (fullIndex j).1 (fullIndex j).2 =
      foldedCircle (fullIndex i).1 (fullIndex i).2 := ⟨i, rfl⟩
  simp only [unzipFieldCoord, coordsFull, fromCoords, h, ↓reduceDIte]
  exact congrArg (unzipFieldPath κ s hs p) (Nat.find_spec h)

open Classical in
/-- The `BCert`-gated boundary measure of the coordinate reconstruction of the path–surrogate of
the unzipped field (junk `0` off the certificate `E1.M4.BCert`). -/
def nuSur (κ s : ℝ) (hs : 0 ≤ s) (γ : ℝ) :
    FieldSample × C(Icc (0 : ℝ) s, ℝ) → Measure ℝ :=
  fun p => if E1.M4.BCert γ (unzipFieldCoord κ s hs p) then
    qBoundaryMeasure γ (unzipFieldCoord κ s hs p) else 0

/-- **The path–surrogate of `L⁻_s`** (first component of `unzipLengths`), with the two side
images packaged as a function `a` of the path. -/
def lenMinusSur (κ s : ℝ) (hs : 0 ≤ s) (γ : ℝ)
    (a : C(Icc (0 : ℝ) s, ℝ) → ℝ × ℝ) :
    FieldSample × C(Icc (0 : ℝ) s, ℝ) → ℝ≥0∞ :=
  fun p => nuSur κ s hs γ p (Set.Icc (a p.2).1 0)

/-- **The intrinsic left length is a.s. the deterministic path functional.** -/
theorem ae_lenMinus_eq_surrogate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun u : ℝ≥0 => B u ω) (κ : ℝ)
    (s : ℝ≥0) {a : C(Icc (0 : ℝ) (s : ℝ), ℝ) → ℝ × ℝ}
    (hside : ∀ᵐ ω ∂P, sideImages (drive κ (clampB s B) ω) (s : ℝ) =
      a (pathC (s : ℝ) B hBc ω))
    (hgood : ∀ᵐ ω ∂P, E1.M4.BCert (Real.sqrt κ)
      (unzipFieldCoord κ (s : ℝ) (show (0 : ℝ) ≤ (s : ℝ) from s.2)
        (X ω, pathC (s : ℝ) B hBc ω)))
    (hcoord : ∀ᵐ ω ∂P, coordsFull (coordChange (ofFun (h0rev κ) + X ω)
        (fwdMapInv (drive κ (clampB s B) ω) (s : ℝ)) (Qc (Real.sqrt κ))) =
      coordsFull (unzipFieldPath κ (s : ℝ) (show (0 : ℝ) ≤ (s : ℝ) from s.2)
        (X ω, pathC (s : ℝ) B hBc ω))) :
    lenMinus κ B X s =ᵐ[P]
      fun ω => lenMinusSur κ (s : ℝ) (show (0 : ℝ) ≤ (s : ℝ) from s.2) (Real.sqrt κ) a
        (X ω, pathC (s : ℝ) B hBc ω) := by
  have hs' : (0 : ℝ) ≤ (s : ℝ) := s.2
  have hclamp := ae_lenMinus_eq_clamp (κ := κ) (X := X) (s := s) hB hBc
  filter_upwards [hclamp, hside, hgood, hcoord] with ω hcl hsd hgd hco
  rw [hcl]
  set F : FieldSample := coordChange (ofFun (h0rev κ) + X ω)
    (fwdMapInv (drive κ (clampB s B) ω) (s : ℝ)) (Qc (Real.sqrt κ)) with hFdef
  set Y : FieldSample := unzipFieldCoord κ (s : ℝ) hs' (X ω, pathC (s : ℝ) B hBc ω)
    with hYdef
  have hclampval : lenMinus κ (clampB s B) X s ω =
      (qBoundaryMeasure (Real.sqrt κ) F)
        (Set.Icc (sideImages (drive κ (clampB s B) ω) (s : ℝ)).1 0) := by
    rw [hFdef]
    rfl
  rw [hclampval, hsd]
  have hν : qBoundaryMeasure (Real.sqrt κ) F = qBoundaryMeasure (Real.sqrt κ) Y := by
    rw [hFdef, hYdef]
    refine UnzipFull.qBoundaryMeasure_congr_of_coordsFull (Real.sqrt κ) ?_
    rw [hco, coordsFull_unzipFieldCoord]
  have hnu : nuSur κ (s : ℝ) hs' (Real.sqrt κ) (X ω, pathC (s : ℝ) B hBc ω) =
      qBoundaryMeasure (Real.sqrt κ) Y := by
    rw [hYdef]
    unfold nuSur
    rw [if_pos hgd]
  rw [hν, ← hnu]
  rfl

/-- **Adaptedness of the intrinsic left length** (obligation `hLad` of
`ESM.lintegral_levelTime_strongMarkov_lenA`), from measurability of the deterministic
functional `lenMinusSur` and measurability of `(X, pathC s B)` for the σ-algebra `m`. -/
theorem measurable_lenMinus_of_surrogate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 => B u ω) (κ : ℝ) (s : ℝ≥0)
    {a : C(Icc (0 : ℝ) (s : ℝ), ℝ) → ℝ × ℝ} {m : MeasurableSpace Ω}
    (hX : Measurable[m] X)
    (hp : Measurable[m] fun ω => pathC (s : ℝ) B hBc ω)
    (hnull : ∀ N : Set Ω, P N = 0 → MeasurableSet[m] N)
    (hsur : Measurable (lenMinusSur κ (s : ℝ) (show (0 : ℝ) ≤ (s : ℝ) from s.2)
      (Real.sqrt κ) a))
    (hae : lenMinus κ B X s =ᵐ[P]
      fun ω => lenMinusSur κ (s : ℝ) (show (0 : ℝ) ≤ (s : ℝ) from s.2) (Real.sqrt κ) a
        (X ω, pathC (s : ℝ) B hBc ω)) :
    Measurable[m] (lenMinus κ B X s) := by
  have hs' : (0 : ℝ) ≤ (s : ℝ) := s.2
  set g : Ω → ℝ≥0∞ := fun ω => lenMinusSur κ (s : ℝ) hs' (Real.sqrt κ) a
    (X ω, pathC (s : ℝ) B hBc ω) with hgdef
  have hg : Measurable[m] g := hsur.comp (Measurable.prodMk hX hp)
  have hae' : lenMinus κ B X s =ᵐ[P] g := hae
  intro U hU
  set E : Set Ω := {ω | ¬ lenMinus κ B X s ω = g ω} with hEdef
  have hE : P E = 0 := ae_iff.1 hae'
  have hsplit : (lenMinus κ B X s) ⁻¹' U = (g ⁻¹' U ∩ Eᶜ) ∪ ((lenMinus κ B X s) ⁻¹' U ∩ E) := by
    ext ω
    by_cases h : ω ∈ E
    · simp [h]
    · have hfg' : lenMinus κ B X s ω = g ω := by simpa [hEdef] using h
      simp [h, hfg']
  rw [hsplit]
  exact ((hg hU).inter (hnull E hE).compl).union
    (hnull _ (measure_mono_null inter_subset_right hE))

end ESM
end QuantumZipper
