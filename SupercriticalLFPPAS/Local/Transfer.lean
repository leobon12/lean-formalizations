import SupercriticalLFPPAS.Local.MetricTools

/-!
# Transfer of Lemma 3.2's event between nearby LFPP fields (packet P32)

Planning audit `planning/audits/SB1-sections-1-3.md` A12, step 8 ("Lemma 2.1 transfers this
conclusion to `H_{δ,L}` uniformly in `L`, by first using cutoff `2M` and a smaller additive error",
paper l. 274–275). If two continuous fields differ by at most `σ` on the open annulus
`U₁ = {1/9 < |z| < 17} ⊃ U`, their normalized LFPP internal metrics on every subset of `U₁`
(in particular on `V` and `U`) agree up to the factor `e^{|ξ|σ}`. With `e^{|ξ|σ} ≤ 2` and
`(e^{|ξ|σ} − 1)(M + 1) ≤ ν/4`, Lemma 3.2's event for `(D, Y_φ)` with error `ν/2` and height `2M`
implies the event for `(D, Y_ψ)` with error `ν` and height `M` (`lemma32Event_transfer`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS.Local

/-- The open annulus `U₁ = {1/9 < |z| < 17}`, a neighbourhood of `U`. -/
def nbhdU : Set ℂ := {z | 1 / 9 < ‖z‖ ∧ ‖z‖ < 17}

theorem isOpen_nbhdU : IsOpen nbhdU :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem tgtU_subset_nbhdU : tgtU ⊆ nbhdU := fun z hz =>
  ⟨by linarith [hz.1], by linarith [hz.2]⟩

theorem srcV_subset_tgtU : srcV ⊆ tgtU := fun z hz =>
  ⟨by linarith [hz.1], by linarith [hz.2]⟩

/-- LFPP internal metrics on a subset of an open set where the fields are `K`-close. -/
theorem lfpp_internal_le_of_close (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {φ ψ : C(ℂ, ℝ)}
    {W Y : Set ℂ} (hW : IsOpen W) (hYW : Y ⊆ W) {K : ℝ} (hK : ∀ z ∈ W, |ψ z - φ z| ≤ K)
    (p : Y × Y) :
    (B2.Median.lfppMetric ξ a ψ).internal Y p ≤
      ENNReal.ofReal (Real.exp (|ξ| * K)) * (B2.Median.lfppMetric ξ a φ).internal Y p := by
  have h0 : ENNReal.ofReal (Real.exp (|ξ| * K)) ≠ 0 := by
    simpa using Real.exp_pos (|ξ| * K)
  unfold LSCMetric.internal
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP =>
    le_iInf fun hY => le_iInf fun hs => le_iInf fun ht => ?_
  have hPc := (B2.Polylog.lfppMetric_isCurve_iff ξ a φ).1 hP
  have hP' : (B2.Median.lfppMetric ξ a ψ).IsCurve P s t :=
    (B2.Polylog.lfppMetric_isCurve_iff ξ a ψ).2 hPc
  exact iInf_le_of_le P <| iInf_le_of_le s <| iInf_le_of_le t <| iInf_le_of_le hP' <|
    iInf_le_of_le hY <| iInf_le_of_le hs <| iInf_le_of_le ht <|
      B2.Polylog.lfppMetric_len_le_of_abs_sub_le ξ a hW hK hPc.2 fun u hu => hYW (hY u hu)

/-- LFPP internal set distances on a subset of an open set where the fields are `K`-close. -/
theorem lfpp_internalSetDist_le_of_close (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {φ ψ : C(ℂ, ℝ)}
    {W Y : Set ℂ} (hW : IsOpen W) (hYW : Y ⊆ W) {K : ℝ} (hK : ∀ z ∈ W, |ψ z - φ z| ≤ K)
    (K₁ K₂ : Set Y) :
    (B2.Median.lfppMetric ξ a ψ).internalSetDist Y K₁ K₂ ≤
      ENNReal.ofReal (Real.exp (|ξ| * K)) * (B2.Median.lfppMetric ξ a φ).internalSetDist Y K₁ K₂ := by
  have h0 : ENNReal.ofReal (Real.exp (|ξ| * K)) ≠ 0 := by
    simpa using Real.exp_pos (|ξ| * K)
  unfold LSCMetric.internalSetDist
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  exact le_iInf₂ fun x hx => le_iInf₂ fun y hy => iInf₂_le_of_le x hx (iInf₂_le_of_le y hy
    (lfpp_internal_le_of_close ξ a hW hYW hK (x, y)))

/-- `e · x ≤ x + (e − 1)·c` for `e ≥ 1` and `x ≤ c`, in `ℝ≥0∞`. -/
theorem ofReal_mul_le_add {e c : ℝ} (he : 1 ≤ e) {x : ℝ≥0∞} (hx : x ≤ ENNReal.ofReal c) :
    ENNReal.ofReal e * x ≤ x + ENNReal.ofReal ((e - 1) * c) := by
  have hsplit : ENNReal.ofReal e = 1 + ENNReal.ofReal (e - 1) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]
    congr 1
    ring
  rw [hsplit, add_mul, one_mul, ENNReal.ofReal_mul (by linarith)]
  gcongr

/-- **Transfer of Lemma 3.2's event** between two continuous fields that are `σ`-close on `U₁`. -/
theorem lemma32Event_transfer {ξ : ℝ} (a : Set.Ioi (0 : ℝ)) {φ ψ : C(ℂ, ℝ)} {D : LSCMetric}
    {η ν M σ : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hM : 0 ≤ M) (hσ : 0 ≤ σ)
    (hσ2 : Real.exp (|ξ| * σ) ≤ 2) (hσν : (Real.exp (|ξ| * σ) - 1) * (M + 1) ≤ ν / 4)
    (hclose : ∀ z ∈ nbhdU, |ψ z - φ z| ≤ σ)
    (hE : Lemma32Event D (B2.Median.lfppMetric ξ a φ) η (ν / 2) (2 * M)) :
    Lemma32Event D (B2.Median.lfppMetric ξ a ψ) η ν M := by
  have hclose' : ∀ z ∈ nbhdU, |φ z - ψ z| ≤ σ := fun z hz => by
    rw [abs_sub_comm]; exact hclose z hz
  set e : ℝ := Real.exp (|ξ| * σ) with he_def
  have he1 : 1 ≤ e := Real.one_le_exp (mul_nonneg (abs_nonneg ξ) hσ)
  have hVU : srcV ⊆ nbhdU := srcV_subset_tgtU.trans tgtU_subset_nbhdU
  have hν2 : 0 ≤ ν / 2 := by positivity
  have hν4 : 0 ≤ ν / 4 := by positivity
  have hsum : ∀ x : ℝ≥0∞, x + ENNReal.ofReal (ν / 2) + ENNReal.ofReal (ν / 4) ≤
      x + ENNReal.ofReal ν := by
    intro x
    rw [add_assoc, ← ENNReal.ofReal_add hν2 hν4]
    gcongr
    linarith
  refine ⟨fun u v hu hv hDM => ?_, fun u v hu hv hYM => ?_⟩
  · -- (3.1)
    set s := D.internal srcV (u, v)
    have h1 := hE.1 u v hu hv (hDM.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    have h2 := lfpp_internalSetDist_le_of_close ξ a (φ := φ) (ψ := ψ) isOpen_nbhdU
      tgtU_subset_nbhdU hclose {x | (x : ℂ) ∈ ball (u : ℂ) η} {x | (x : ℂ) ∈ ball (v : ℂ) η}
    have hsν : s + ENNReal.ofReal (ν / 2) ≤ ENNReal.ofReal (M + 1) := by
      calc s + ENNReal.ofReal (ν / 2) ≤ ENNReal.ofReal M + ENNReal.ofReal (ν / 2) := by gcongr
        _ = ENNReal.ofReal (M + ν / 2) := (ENNReal.ofReal_add hM hν2).symm
        _ ≤ ENNReal.ofReal (M + 1) := ENNReal.ofReal_le_ofReal (by linarith)
    calc _ ≤ ENNReal.ofReal e * (B2.Median.lfppMetric ξ a φ).internalSetDist tgtU
          {x | (x : ℂ) ∈ ball (u : ℂ) η} {x | (x : ℂ) ∈ ball (v : ℂ) η} := h2
      _ ≤ ENNReal.ofReal e * (s + ENNReal.ofReal (ν / 2)) := by gcongr
      _ ≤ s + ENNReal.ofReal (ν / 2) + ENNReal.ofReal ((e - 1) * (M + 1)) :=
          ofReal_mul_le_add he1 hsν
      _ ≤ s + ENNReal.ofReal (ν / 2) + ENNReal.ofReal (ν / 4) := by gcongr
      _ ≤ s + ENNReal.ofReal ν := hsum s
  · -- (3.2)
    set t := (B2.Median.lfppMetric ξ a ψ).internal srcV (u, v)
    have h1 := lfpp_internal_le_of_close ξ a (φ := ψ) (ψ := φ) isOpen_nbhdU hVU hclose' (u, v)
    have hφM : (B2.Median.lfppMetric ξ a φ).internal srcV (u, v) ≤ ENNReal.ofReal (2 * M) := by
      calc _ ≤ ENNReal.ofReal e * t := h1
        _ ≤ ENNReal.ofReal e * ENNReal.ofReal M := by gcongr
        _ = ENNReal.ofReal (e * M) := (ENNReal.ofReal_mul (by linarith)).symm
        _ ≤ ENNReal.ofReal (2 * M) := ENNReal.ofReal_le_ofReal (by nlinarith)
    have h2 := hE.2 u v hu hv hφM
    have h3 : ENNReal.ofReal e * t ≤ t + ENNReal.ofReal (ν / 4) := by
      calc ENNReal.ofReal e * t ≤ t + ENNReal.ofReal ((e - 1) * M) := ofReal_mul_le_add he1 hYM
        _ ≤ t + ENNReal.ofReal (ν / 4) := by
            gcongr
            nlinarith
    calc _ ≤ (B2.Median.lfppMetric ξ a φ).internal srcV (u, v) + ENNReal.ofReal (ν / 2) := h2
      _ ≤ ENNReal.ofReal e * t + ENNReal.ofReal (ν / 2) := by gcongr
      _ ≤ t + ENNReal.ofReal (ν / 4) + ENNReal.ofReal (ν / 2) := by gcongr
      _ = t + ENNReal.ofReal (ν / 2) + ENNReal.ofReal (ν / 4) := by
          rw [add_assoc, add_assoc, add_comm (ENNReal.ofReal (ν / 4))]
      _ ≤ t + ENNReal.ofReal ν := hsum t

end SupercriticalLFPPAS.Local
