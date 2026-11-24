import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_2.VtvRLinAE
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.VtvRPairBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.VtvFSlice
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4.VtvFlowJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4.VtvEcJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4.VtvFlowCyl

/-!
# `VtvRBoundAE`: a.e. pointwise seminorm bound of `R(r,·)` (source 4610)

For a.e. `r > 0` the slices `f(r,·)` are integrable on every box (`vtvFSlice`, over the countable
cover `(0,∞) = ⋃ₙ [1/(n+1), n+1]`). Fix such `r`, with `K` a bound for the `C^1` data of `v`, `Ec`
at time `r` (`vtvFlowJet`, `vtvEcJet`). For `M > 0` apply `vtvRPairBound` to `ψ = M⁻¹ • φ`, which
satisfies `CkSmall 3 1 ψ`, and use linearity (`vtvRLinAE`) to scale back; `M ≤ 0` is trivial.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- A first-derivative bound from the norm of `iteratedFDeriv 1`. -/
theorem vtvPdBound1 (φ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) (j : Fin 2) (M : ℝ)
    (h : ‖iteratedFDeriv ℝ 1 φ x‖ ≤ M) : |B0579.pd j φ x| ≤ M := by
  rw [norm_iteratedFDeriv_one] at h
  unfold B0579.pd
  calc |fderiv ℝ φ x (B0579.dir j)| = ‖fderiv ℝ φ x (B0579.dir j)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ φ x‖ * ‖B0579.dir j‖ := (fderiv ℝ φ x).le_opNorm _
    _ ≤ M * 1 := mul_le_mul h (norm_dir_le j) (norm_nonneg _) ((norm_nonneg _).trans h)
    _ = M := mul_one M

theorem vtvRBoundAE : VtvRBoundAE := by
  intro ν c μ tr ω g b G f H R
  have hLin := vtvRLinAE ν c μ tr ω g b G f H
  have hFS : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∀ (R' : ℝ) (i : Fin 2),
      IntegrableOn (fun x => f (r, x) i) (vtvBox c R') := by
    have hcov : Ioi (0 : ℝ) = ⋃ n : ℕ, Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) := by
      ext x
      simp only [mem_Ioi, mem_iUnion, mem_Icc]
      constructor
      · intro hx
        have h1 : x + 1 / x ≤ (⌈x + 1 / x⌉₊ : ℝ) := Nat.le_ceil _
        have hinv : 0 < 1 / x := by positivity
        refine ⟨⌈x + 1 / x⌉₊, ?_, ?_⟩
        · rw [div_le_iff₀ (by positivity)]
          have h2 : 1 / x ≤ (⌈x + 1 / x⌉₊ : ℝ) + 1 := by linarith
          have h3 := (div_le_iff₀ hx).1 h2
          nlinarith
        · linarith
      · rintro ⟨n, h1, _⟩
        exact lt_of_lt_of_le (by positivity) h1
    rw [hcov, ae_restrict_iUnion_iff]
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact vtvFSlice ν c μ tr ω g b G f H _ _ hpos
  have hposAE : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [hLin, hFS, hposAE] with r hLinR hfr hrpos
  have hr0 : 0 < r := hrpos
  obtain ⟨KEc, hKE⟩ := vtvEcJet ν c tr H.2.2.1 r r hr0
  obtain ⟨Ak, hA0, hA⟩ := vtvFlowJet ν c tr H.2.2.1 r r hr0
  set K : ℝ := 1 + |Ak| + |KEc| with hKdef
  have hKge1 : 1 ≤ K := by
    have := abs_nonneg Ak
    have := abs_nonneg KEc
    linarith
  have hKA : Ak ≤ K := by
    have := le_abs_self Ak
    have := abs_nonneg KEc
    linarith
  have hKE' : KEc ≤ K := by
    have := le_abs_self KEc
    have := abs_nonneg Ak
    linarith
  refine ⟨3, ‖(r : ℂ) ^ (μ : ℂ)‖ * (K + K * K) * (vtvDB c R b r + vtvDF c R f r), ?_⟩
  intro φ hφband M hM
  obtain ⟨hcyl, hband⟩ : B0579.IsCylTest c φ ∧ ∀ x : ℝ × ℝ, R < |x.2| → φ x = 0 := hφband
  rcases lt_trichotomy M 0 with hMneg | hM0 | hMpos
  · exfalso
    have h0 := hM 0 (Nat.zero_le _) 0
    rw [norm_iteratedFDeriv_zero] at h0
    linarith [norm_nonneg (φ 0)]
  · subst hM0
    have hzero : ∀ x, φ x = 0 := fun x => by
      have h0 := hM 0 (Nat.zero_le _) x
      rw [norm_iteratedFDeriv_zero] at h0
      exact norm_le_zero_iff.1 h0
    have hφ0 : φ = (0 : ℝ) • φ := by
      funext x
      simp [hzero x]
    have hl := (hLinR φ φ hcyl hcyl 0).2
    rw [← hφ0] at hl
    have hl0 : vtvR μ tr ω g b r φ = 0 := by
      rw [hl]
      simp
    rw [hl0, norm_zero, mul_zero]
  · obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ × ℝ → ℝ, ψ = M⁻¹ • φ := ⟨_, rfl⟩
    have hφψ : φ = M • ψ := by
      rw [hψ, smul_smul, mul_inv_cancel₀ hMpos.ne', one_smul]
    have hψcyl : B0579.IsCylTest c ψ := by
      rw [hψ]
      exact cyl_smul M⁻¹ hcyl
    have hψband : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0 := by
      intro x hx
      rw [hψ]
      simp [hband x hx]
    have hψK : ∀ j : ℕ, j ≤ 3 → ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ j ψ x‖ ≤ 1 := by
      intro j hj x
      have hsm : ContDiffAt ℝ (j : WithTop ℕ∞) φ x :=
        ContDiffAt.of_le hcyl.smooth.contDiffAt (by simp)
      rw [hψ, iteratedFDeriv_const_smul_apply hsm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hMpos)]
      calc M⁻¹ * ‖iteratedFDeriv ℝ j φ x‖ ≤ M⁻¹ * M :=
            mul_le_mul_of_nonneg_left (hM j hj x) (inv_nonneg.2 hMpos.le)
        _ = 1 := inv_mul_cancel₀ hMpos.ne'
    have hψ0 : ∀ x, |ψ x| ≤ K := fun x => by
      have h0 := hψK 0 (Nat.zero_le _) x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
      linarith
    have hψ1 : ∀ x j, |B0579.pd j ψ x| ≤ K := fun x j =>
      (vtvPdBound1 ψ x j 1 (hψK 1 (by norm_num) x)).trans hKge1
    have hW : ∀ x j, |B0579.pd j (vtvFlowTest tr r ψ) x| ≤ K := fun x j => by
      have h := hA r (Set.mem_Icc.2 ⟨le_rfl, le_rfl⟩) ψ hψcyl.smooth 1
        (fun x k hk => hψK k hk x) x j
      rw [mul_one] at h
      linarith [le_abs_self Ak, abs_nonneg KEc]
    have hEc : ∀ x j, |B0579.pd j (UnforcedLeray.B0238.Ec tr r) x| ≤ K := fun x j => by
      have h := hKE r (Set.mem_Icc.2 ⟨le_rfl, le_rfl⟩) x j
      linarith [le_abs_self KEc]
    have hKey := vtvRPairBound ν c μ tr ω g b G f H R r hr0 (fun i => hfr R i) ψ hψcyl
      (vtvFlowCyl ν c tr r hr0 ψ hψcyl) hψband K hψ0 hψ1 hW hEc
    have hlin := (hLinR ψ ψ hψcyl hψcyl M).2
    rw [← hφψ] at hlin
    rw [hlin, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
    exact (mul_le_mul_of_nonneg_left hKey hMpos.le).trans_eq (mul_comm _ _)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
