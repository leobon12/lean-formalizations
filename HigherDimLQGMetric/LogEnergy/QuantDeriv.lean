import HigherDimLQGMetric.LogEnergy.QuantCM
open HigherDimLFPP (Rd)
open scoped LineDeriv Laplacian SchwartzMap
namespace HigherDimLQGMetric
private theorem lineDeriv_cast {d n m : ℕ} (h : n = m) (v : Fin m → Rd d)
    (f : 𝓢(Rd d, ℂ)) : ∂^{v ∘ Fin.cast h} f = ∂^{v} f := by
  subst m
  simp

private theorem lineDeriv_append {d n m : ℕ} (v : Fin n → Rd d) (w : Fin m → Rd d)
    (f : 𝓢(Rd d, ℂ)) :
    ∂^{Fin.append v w} f = ∂^{v} (∂^{w} f) := by
  induction n with
  | zero =>
      rw [Fin.append_left_nil _ _ rfl, lineDeriv_cast,
        LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
      conv_lhs => rw [← Fin.cons_self_tail v]
      simp only [Fin.append_cons]
      rw [lineDeriv_cast]
      simp only [LineDeriv.iteratedLineDerivOp_succ_left]
      simp only [Fin.cons_zero, Fin.tail_cons]
      rw [ih]

private theorem lineDeriv_pair {d n : ℕ} (v : Fin n → Rd d) (i : Rd d)
    (f : 𝓢(Rd d, ℂ)) :
    ∂^{Fin.append v (fun _ : Fin 2 => i)} f =
      ∂^{v} (∂_{i} (∂_{i} f)) := by
  rw [lineDeriv_append]
  rw [LineDeriv.iteratedLineDerivOp_succ_left,
    LineDeriv.iteratedLineDerivOp_succ_left,
    LineDeriv.iteratedLineDerivOp_fin_zero]
  rfl

theorem iterLap_lineDeriv_bound {d : ℕ} (f : 𝓢(Rd d, ℂ)) (m : ℕ) :
    ∀ (n : ℕ) (v : Fin n → Rd d) (x : Rd d),
      (∀ i, ‖v i‖ ≤ 1) →
      ‖∂^{v} (iterLap m f) x‖ ≤
        (Module.finrank ℝ (Rd d) : ℝ) ^ m *
          ‖iteratedFDeriv ℝ (n + 2*m) (f : Rd d → ℂ) x‖ := by
  induction m with
  | zero =>
      intro n v x hv
      simp [iterLap]
      rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
      exact (iteratedFDeriv ℝ n (f : Rd d → ℂ) x).unit_le_opNorm (by
        exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 hv)
  | succ m ih =>
      intro n v x hv
      let b := stdOrthonormalBasis ℝ (Rd d)
      have hterm (i : Fin (Module.finrank ℝ (Rd d))) :
          ‖∂^{v} (∂_{b i} (∂_{b i} (iterLap m f))) x‖ ≤
            (Module.finrank ℝ (Rd d) : ℝ)^m *
              ‖iteratedFDeriv ℝ (n + 2*(m+1)) (f : Rd d → ℂ) x‖ := by
        let w : Fin 2 → Rd d := fun _ => b i
        have hw : ∀ j, ‖Fin.append v w j‖ ≤ 1 := by
          intro j
          refine Fin.addCases (fun k => ?_) (fun k => ?_) j
          · simpa using hv k
          · simp [w, OrthonormalBasis.norm_eq_one]
        have h := ih (n+2) (Fin.append v w) x hw
        rw [lineDeriv_pair] at h
        have heq : n + 2 + 2*m = n + 2*(m+1) := by omega
        rw [heq] at h
        exact h
      change ‖∂^{v} (Δ (iterLap m f)) x‖ ≤ _
      rw [SchwartzMap.laplacian_eq_sum b]
      rw [LineDeriv.iteratedLineDerivOp_sum, sum_apply]
      calc
        ‖∑ i : Fin (Module.finrank ℝ (Rd d)),
            (∂^{v} (∂_{b i} (∂_{b i} (iterLap m f)))) x‖ ≤
          ∑ i : Fin (Module.finrank ℝ (Rd d)),
            ‖(∂^{v} (∂_{b i} (∂_{b i} (iterLap m f)))) x‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin (Module.finrank ℝ (Rd d)),
            (Module.finrank ℝ (Rd d) : ℝ)^m *
              ‖iteratedFDeriv ℝ (n+2*(m+1)) (f : Rd d → ℂ) x‖ := by
          exact Finset.sum_le_sum (fun i _ => hterm i)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_fin,
            nsmul_eq_mul]
          rw [pow_succ]
          ring

/-- Pointwise control of the iterated Laplacian by a full derivative of the
same order, with the exact Euclidean dimension factor. -/
theorem iterLap_norm_le_iteratedFDeriv {d : ℕ} (f : 𝓢(Rd d, ℂ))
    (m : ℕ) (x : Rd d) :
    ‖iterLap m f x‖ ≤ (d : ℝ)^m *
      ‖iteratedFDeriv ℝ (2*m) (f : Rd d → ℂ) x‖ := by
  have h := iterLap_lineDeriv_bound f m 0 (Fin.elim0 : Fin 0 → Rd d) x
    (fun i => i.elim0)
  rw [Nat.zero_add] at h
  simpa [LineDeriv.iteratedLineDerivOp_fin_zero] using h

/-- For a real compact smooth function, the iterated Laplacian of its complex
Schwartz realization is bounded by an ordinary real derivative. -/
theorem iterLap_compactComplexSchwartz_norm_le {d : ℕ} {F : Rd d → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hc : HasCompactSupport F) (m : ℕ) (x : Rd d) :
    ‖iterLap m (compactComplexSchwartz hF hc) x‖ ≤
      (d : ℝ)^m * ‖iteratedFDeriv ℝ (2*m) F x‖ := by
  have h := iterLap_norm_le_iteratedFDeriv (compactComplexSchwartz hF hc) m x
  have heq : (compactComplexSchwartz hF hc : Rd d → ℂ) =
      Complex.ofRealLI ∘ F := by
    funext y
    rfl
  rw [heq, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    (hF.contDiffAt) (by exact WithTop.coe_le_coe.mpr le_top)] at h
  exact h

/-- The quantitative Cameron–Martin estimate in the ordinary derivative
form used for smooth compact parameter families. -/
theorem exists_isCMBounded_quantDeriv {d : ℕ} (hd : 1 ≤ d)
    (S : Set (Rd d)) (hS : MeasurableSet S) (hfin : MeasureTheory.volume S ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {F : Rd d → ℝ}
        (_hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
        (_hc : HasCompactSupport F)
        (_hs : tsupport F ⊆ S)
        {M : ℝ} (_hM : 0 ≤ M)
        (_h0 : ∀ x, |F x| ≤ M)
        (_hm : ∀ x, ‖iteratedFDeriv ℝ (2*(d/2+1)) F x‖ ≤ M),
        IsCMBounded F (C * M) := by
  obtain ⟨C₀, hC₀, hquant⟩ := exists_isCMBounded_quantSup_dim hd S hS hfin
  let m := d/2+1
  let B : ℝ := max 1 ((d : ℝ)^m)
  let C : ℝ := C₀ * B
  have hB1 : 1 ≤ B := le_max_left (1:ℝ) ((d:ℝ)^m)
  have hBd : (d:ℝ)^m ≤ B := le_max_right (1:ℝ) ((d:ℝ)^m)
  have hB : 0 < B := by
    exact lt_of_lt_of_le (show 0 < (1:ℝ) by norm_num)
      hB1
  refine ⟨C, mul_pos hC₀ hB, ?_⟩
  intro F hF hc hs M hM h0 hm
  have hLap : ∀ x, ‖iterLap m (compactComplexSchwartz hF hc) x‖ ≤ B*M := by
    intro x
    calc
      _ ≤ (d : ℝ)^m * ‖iteratedFDeriv ℝ (2*m) F x‖ :=
        iterLap_compactComplexSchwartz_norm_le hF hc m x
      _ ≤ (d : ℝ)^m * M :=
        mul_le_mul_of_nonneg_left (hm x) (by positivity)
      _ ≤ B*M := mul_le_mul_of_nonneg_right hBd hM
  have h0B : ∀ x, |F x| ≤ B*M := by
    intro x
    calc
      _ ≤ M := h0 x
      _ = 1*M := by ring
      _ ≤ B*M := mul_le_mul_of_nonneg_right hB1 hM
  have hbase := hquant hF hc hs (mul_nonneg hB.le hM) h0B hLap
  simpa [C, mul_assoc] using hbase
end HigherDimLQGMetric
