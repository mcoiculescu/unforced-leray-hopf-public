import UnforcedLeray.Cons.L2.CanonicalBranch.DysonAdjoint

open UnforcedLeray.Cons.G3b
open UnforcedLeray.B0010
open scoped ComplexConjugate

/-! Exact scaled-unitary identity for the inviscid transport limit. -/

theorem canonicalTransportLimitFamily_comp_adjoint_eq_exp
    {a b s t : ℝ} (lam : ℂ) (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s ∘L
        ContinuousLinearMap.adjoint
          ((canonicalTransportLimitFamily (a := a) (b := b) lam).U t s) =
      (Real.exp (-2 * lam.re * (t - s)) : ℂ) • (1 : XG →L[ℂ] XG) := by
  letI : NormedAlgebra ℚ (XG →L[ℂ] XG) :=
    NormedAlgebra.restrictScalars ℚ ℂ (XG →L[ℂ] XG)
  let Δ : ℝ := t - s
  let Δc : ℂ := (t - s : ℝ)
  let G := canonicalTransportLimitGenerator lam
  let T : XG →L[ℂ] XG := UnforcedLeray.B0087.imMulOp
  let Z := Δc • G
  let z := Δc • T
  let w := (-(Δc * lam)) • (1 : XG →L[ℂ] XG)
  let U := NormedSpace.exp z
  let c := Complex.exp (-(Δc * lam))
  have hG : G = T - lam • (1 : XG →L[ℂ] XG) := by
    rfl
  have hZ : Z = z + w := by
    change Δc • (T - lam • (1 : XG →L[ℂ] XG)) =
      Δc • T + (-(Δc * lam)) • (1 : XG →L[ℂ] XG)
    rw [smul_sub, smul_smul, sub_eq_add_neg, ← neg_smul]
  have hcomm : Commute z w := by
    change z * w = w * z
    dsimp [z, w]
    simp only [smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_smul]
    congr 1 <;> ring
  have hexpAdd : NormedSpace.exp Z = U * NormedSpace.exp w := by
    rw [hZ, NormedSpace.exp_add_of_commute hcomm]
  have hw : NormedSpace.exp w = c • (1 : XG →L[ℂ] XG) := by
    dsimp [w, c]
    have h := NormedSpace.algebraMap_exp_comm (𝕂 := ℂ)
      (𝔸 := XG →L[ℂ] XG) (-(Δc * lam))
    change NormedSpace.exp
      (algebraMap ℂ (XG →L[ℂ] XG) (-(Δc * lam))) =
      algebraMap ℂ (XG →L[ℂ] XG) (Complex.exp (-(Δc * lam)))
    rw [Complex.exp_eq_exp_ℂ]
    exact h.symm
  have hVform : NormedSpace.exp Z = c • U := by
    rw [hexpAdd, hw]
    simp [U, mul_smul_comm]
  have hTstar : star T = -T := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact UnforcedLeray.B0087.adjoint_imMulOp
  have hΔstar : star Δc = Δc := by simp [Δc]
  have hzskew : z ∈ skewAdjoint (XG →L[ℂ] XG) := by
    change star (Δc • T) = -(Δc • T)
    rw [star_smul, hΔstar, hTstar, smul_neg]
  have hUunit : U ∈ unitary (XG →L[ℂ] XG) := by
    exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hzskew
  have hUprod : U * star U = 1 := Unitary.mul_star_self_of_mem hUunit
  have hcprod : c * star c = (Real.exp (-2 * lam.re * Δ) : ℂ) := by
    calc
      c * star c = (Complex.normSq c : ℂ) := by simp [Complex.mul_conj]
      _ = (‖c‖ ^ 2 : ℝ) := by exact_mod_cast Complex.normSq_eq_norm_sq c
      _ = Real.exp (-2 * lam.re * Δ) := by
        dsimp [c, Δc, Δ]
        rw [Complex.norm_exp]
        have hre : (-(↑(t - s) * lam)).re = -(t - s) * lam.re := by
          simp [Complex.mul_re]
          ring
        rw [hre]
        rw [pow_two, ← Real.exp_add]
        congr 1 <;> ring_nf
  have hformula :
      (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s = NormedSpace.exp Z := by
    simp only [canonicalTransportLimitFamily,
      UnforcedLeray.Evolution.EvolutionFamily.ofExpSemigroup_U,
      UnforcedLeray.Infra.ExpSemigroup.ofExp_T]
    rfl
  change (canonicalTransportLimitFamily (a := a) (b := b) lam).U t s *
      star ((canonicalTransportLimitFamily (a := a) (b := b) lam).U t s) = _
  rw [hformula, hVform, star_smul]
  calc
    (c • U) * (star c • star U) = (c * star c) • (U * star U) := by
      simp [mul_smul_comm, smul_mul_assoc]
      module
    _ = (Real.exp (-2 * lam.re * Δ) : ℂ) • (1 : XG →L[ℂ] XG) := by rw [hcprod, hUprod]
    _ = (Real.exp (-2 * lam.re * (t - s)) : ℂ) • (1 : XG →L[ℂ] XG) := by simp [Δ]
