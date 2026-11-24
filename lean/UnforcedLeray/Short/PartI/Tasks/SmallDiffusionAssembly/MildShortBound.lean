import UnforcedLeray.Short.PartI.Sub.PartI_C05
import UnforcedLeray.Units.B0123
import NonUniqueEuler.P.Infra.ODE.Gronwall

/-!


Source of record: `the November 2 reference manuscript`, lines 1055-1058
(short block bound by Gronwall on the Duhamel identity).

Method. Let `M` bound the operator norm of the mild generator
`G_b = L₀ - λ - ℓ(·)q - bκ + b R_f` for `0 ≤ b ≤ 1`. The Duhamel identity (`duhamel` field of
`IsMildComplementEvolution`) together with `‖expD a‖ ≤ 1` (`B0123.norm_expD_le`) gives
`‖U(r,s)x‖ ≤ ‖x‖ + M ∫_s^r ‖U(τ,s)x‖ dτ`. The integral Gronwall inequality
(`NonUniqueEuler.LinODE.int_gronwall`) yields `‖U(t,s)x‖ ≤ e^{M(t-s)} ‖x‖ ≤ e^{MB} ‖x‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Target `PartI:C05/3`** (source lines 1055-1058): uniform short-block bound. -/
theorem mildComplementShortBound : MildComplementShortBound := by
  intro lam q l _hseed qd _hl hq hqd B hB
  set M : ℝ := ‖(Planar.L0 : B0010.XG →L[ℂ] B0010.XG)‖ + ‖lam‖ + ‖l.smulRight q‖ +
    ‖seedKappa l q hq‖ + ‖seedRf l q qd hq hqd‖ with hMdef
  have hM0 : 0 ≤ M := by positivity
  -- operator bound on the generator for `0 ≤ b ≤ 1`
  have hGb : ∀ b : ℝ, 0 ≤ b → b ≤ 1 → ∀ y : B0010.XG,
      ‖(Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q
          - ((b : ℂ) * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG)
          + (b : ℂ) • seedRf l q qd hq hqd) y‖ ≤ M * ‖y‖ := by
    intro b hb0 hb1 y
    have h1 : ‖(1 : B0010.XG →L[ℂ] B0010.XG)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hbc : ‖(b : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg hb0]; exact hb1
    have hA : ‖((b : ℂ) * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG)‖ ≤
        ‖seedKappa l q hq‖ := by
      rw [norm_smul, norm_mul]
      calc ‖(b : ℂ)‖ * ‖seedKappa l q hq‖ * ‖(1 : B0010.XG →L[ℂ] B0010.XG)‖
          ≤ 1 * ‖seedKappa l q hq‖ * 1 := by gcongr
        _ = ‖seedKappa l q hq‖ := by ring
    have hB' : ‖(b : ℂ) • seedRf l q qd hq hqd‖ ≤ ‖seedRf l q qd hq hqd‖ := by
      rw [norm_smul]
      calc ‖(b : ℂ)‖ * ‖seedRf l q qd hq hqd‖ ≤ 1 * ‖seedRf l q qd hq hqd‖ := by gcongr
        _ = ‖seedRf l q qd hq hqd‖ := one_mul _
    have hlam : ‖lam • (1 : B0010.XG →L[ℂ] B0010.XG)‖ ≤ ‖lam‖ := by
      rw [norm_smul]
      calc ‖lam‖ * ‖(1 : B0010.XG →L[ℂ] B0010.XG)‖ ≤ ‖lam‖ * 1 := by gcongr
        _ = ‖lam‖ := mul_one _
    have hP : ‖l.smulRight q‖ = ‖l.smulRight q‖ := rfl
    have t1 := norm_add_le
      ((Planar.L0 : B0010.XG →L[ℂ] B0010.XG) - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q
          - ((b : ℂ) * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG))
      ((b : ℂ) • seedRf l q qd hq hqd)
    have t2 := norm_sub_le
      ((Planar.L0 : B0010.XG →L[ℂ] B0010.XG) - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q)
      (((b : ℂ) * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG))
    have t3 := norm_sub_le
      ((Planar.L0 : B0010.XG →L[ℂ] B0010.XG) - lam • (1 : B0010.XG →L[ℂ] B0010.XG))
      (l.smulRight q)
    have t4 := norm_sub_le (Planar.L0 : B0010.XG →L[ℂ] B0010.XG) (lam • (1 : B0010.XG →L[ℂ] B0010.XG))
    have hop : ‖(Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q
          - ((b : ℂ) * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG)
          + (b : ℂ) • seedRf l q qd hq hqd)‖ ≤ M := by
      rw [hMdef]
      linarith
    calc ‖(Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q
          - ((b : ℂ) * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG)
          + (b : ℂ) • seedRf l q qd hq hqd) y‖
        ≤ ‖(Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q
          - ((b : ℂ) * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG)
          + (b : ℂ) • seedRf l q qd hq hqd)‖ * ‖y‖ :=
          ((Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q
          - ((b : ℂ) * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG)
          + (b : ℂ) • seedRf l q qd hq hqd) : B0010.XG →L[ℂ] B0010.XG).le_opNorm y
      _ ≤ M * ‖y‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)
  refine ⟨Real.exp (M * B), fun β _hβm hβ U hU s t hst hts => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le (fun x => ?_)
  -- pointwise Duhamel bound
  have hcont : ∀ r, ContinuousOn (fun τ => ‖U τ s x‖) (Icc s r) := fun r =>
    ((hU.cont s x).mono Icc_subset_Ici_self).norm
  have hpt : ∀ r ∈ Icc s t, ‖U r s x‖ ≤ ‖x‖ + ∫ τ in s..r, M * ‖U τ s x‖ := by
    intro r hr
    have hsr : s ≤ r := hr.1
    rw [hU.duhamel s r hsr x]
    have hA1 : ‖B0123.expD (∫ u in s..r, β u) x‖ ≤ ‖x‖ := by
      calc ‖B0123.expD (∫ u in s..r, β u) x‖
          ≤ ‖B0123.expD (∫ u in s..r, β u)‖ * ‖x‖ := (B0123.expD _).le_opNorm x
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (B0123.norm_expD_le _) (norm_nonneg _)
        _ = ‖x‖ := one_mul _
    refine (norm_add_le _ _).trans (add_le_add hA1 ?_)
    apply intervalIntegral.norm_integral_le_of_norm_le hsr
    · refine ae_of_all _ (fun τ hτ => ?_)
      refine ((B0123.expD _).le_opNorm _).trans ?_
      refine (mul_le_mul (B0123.norm_expD_le _)
        (hGb _ (hβ τ).1 (hβ τ).2 _) (norm_nonneg _) zero_le_one).trans ?_
      exact le_of_eq (one_mul _)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hsr]
      exact continuousOn_const.mul (hcont r |>.mono (fun τ hτ => ⟨hτ.1, hτ.2⟩))
  -- Gronwall
  have hgr := NonUniqueEuler.LinODE.int_gronwall
    (u := fun τ => ‖U τ s x‖ - ‖x‖) (b := fun _ => M) (c := ‖x‖) (α := s) (β := t)
    (((hU.cont s x).mono Icc_subset_Ici_self).norm.sub continuousOn_const)
    continuousOn_const (fun _ _ => hM0) (norm_nonneg x) (by
      intro r hr
      have hr' := hpt r hr
      have hcongr : ∀ τ, M * (‖x‖ + (‖U τ s x‖ - ‖x‖)) = M * ‖U τ s x‖ :=
        fun τ => by ring
      simp only [hcongr]
      linarith)
  have hfin := hgr t ⟨hst, le_refl t⟩
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hfin
  have hexp : Real.exp ((t - s) * M) ≤ Real.exp (M * B) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hle : ‖U t s x‖ ≤ ‖x‖ * Real.exp ((t - s) * M) := by
    linarith
  calc ‖U t s x‖ ≤ ‖x‖ * Real.exp ((t - s) * M) := hle
    _ ≤ ‖x‖ * Real.exp (M * B) := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    _ = Real.exp (M * B) * ‖x‖ := mul_comm _ _

end UnforcedLeray.Short.PartI
