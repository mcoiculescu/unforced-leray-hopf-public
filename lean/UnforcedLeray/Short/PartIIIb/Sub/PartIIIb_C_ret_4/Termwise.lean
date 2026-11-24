import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# Termwise identity for `PartIII-b:C/ret/4` (source lines 4991-4994)

Proves `HpTermIdentity ν`: `[V_j, B x_j] = J ∇ [(tr B) ψ_j - (B x_j)·∇ψ_j]` by direct
line-derivative computation of both sides, followed by a componentwise polynomial identity.
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma tw_p1_line (ν : ℝ) (j : ℤ) (x v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => (xj ν j (x + t • v)).1) v.1 0 := by
  have : HasDerivAt (fun t : ℝ => x.1 + t * v.1 - (j : ℝ) * cOf ν) v.1 0 := by
    have h := (((hasDerivAt_id' (0:ℝ)).mul_const v.1).const_add x.1).sub_const ((j : ℝ) * cOf ν)
    simpa using h
  exact this

lemma tw_p2_line (ν : ℝ) (j : ℤ) (x v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => (xj ν j (x + t • v)).2) v.2 0 := by
  have : HasDerivAt (fun t : ℝ => x.2 + t * v.2) v.2 0 := by
    have h := ((hasDerivAt_id' (0:ℝ)).mul_const v.2).const_add x.2
    simpa using h
  exact this

/-- Line derivative of `Q(y) = p·(B p)` with `p = x_j(y)`. -/
lemma tw_Q_line (ν : ℝ) (j : ℤ) (B : Mat3) (x v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => (xj ν j (x + t • v)).1 * (merApply B (xj ν j (x + t • v))).1
        + (xj ν j (x + t • v)).2 * (merApply B (xj ν j (x + t • v))).2)
      (v.1 * (merApply B (xj ν j x)).1 + (xj ν j x).1 * (merApply B v).1
        + (v.2 * (merApply B (xj ν j x)).2 + (xj ν j x).2 * (merApply B v).2)) 0 := by
  have hp1 := tw_p1_line ν j x v
  have hp2 := tw_p2_line ν j x v
  have hu1 : HasDerivAt (fun t : ℝ => (merApply B (xj ν j (x + t • v))).1) (merApply B v).1 0 :=
    ((hp1.const_mul (B 0 0)).add (hp2.const_mul (B 0 2))).congr_deriv (by simp [merApply])
  have hu2 : HasDerivAt (fun t : ℝ => (merApply B (xj ν j (x + t • v))).2) (merApply B v).2 0 :=
    ((hp1.const_mul (B 2 0)).add (hp2.const_mul (B 2 2))).congr_deriv (by simp [merApply])
  refine ((hp1.mul hu1).add (hp2.mul hu2)).congr_deriv ?_
  simp only [zero_smul, add_zero] <;> ring

lemma tw_gjPsi_eq (ν s : ℝ) (j : ℤ) (B : Mat3) (y : ℝ × ℝ) :
    gjPsi ν s B j y = merTrace B * psij ν s j y
      - (-2 * (ageA ν s)⁻¹) * (Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) *
          (-(2 * ((xj ν j y).1 * (merApply B (xj ν j y)).1
            + (xj ν j y).2 * (merApply B (xj ν j y)).2)) / (4 * ageA ν s))) := by
  unfold gjPsi
  rw [gp_fderiv_psij]
  ring

lemma tw_gjPsi_diff (ν s : ℝ) (j : ℤ) (B : Mat3) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (gjPsi ν s B j) x := by
  have hf : gjPsi ν s B j = fun y => merTrace B * psij ν s j y
      - (-2 * (ageA ν s)⁻¹) * (Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s)) *
          (-(2 * ((xj ν j y).1 * (merApply B (xj ν j y)).1
            + (xj ν j y).2 * (merApply B (xj ν j y)).2)) / (4 * ageA ν s))) :=
    funext (tw_gjPsi_eq ν s j B)
  rw [hf]
  unfold psij xj sq2 merApply
  fun_prop

/-- Line derivative of `gjPsi` with the explicit gradient value. -/
lemma tw_gjPsi_line (ν s : ℝ) (j : ℤ) (B : Mat3) (x v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => gjPsi ν s B j (x + t • v))
      ((Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (ageA ν s ^ 2)⁻¹) *
        ((merTrace B + ((xj ν j x).1 * (merApply B (xj ν j x)).1
            + (xj ν j x).2 * (merApply B (xj ν j x)).2) / (2 * ageA ν s))
          * ((xj ν j x).1 * v.1 + (xj ν j x).2 * v.2)
        - (v.1 * (merApply B (xj ν j x)).1 + (xj ν j x).1 * (merApply B v).1
          + (v.2 * (merApply B (xj ν j x)).2 + (xj ν j x).2 * (merApply B v).2)))) 0 := by
  have hE := gp_exp_line ν s j x v
  have hQ := tw_Q_line ν j B x v
  have hQ2 := (hQ.const_mul 2).neg.div_const (4 * ageA ν s)
  have hK := (hE.mul hQ2).const_mul (-2 * (ageA ν s)⁻¹)
  have hmain := ((gp_psij_line ν s j x v).const_mul (merTrace B)).sub hK
  have hfun : (fun t : ℝ => gjPsi ν s B j (x + t • v)) = fun t : ℝ =>
      merTrace B * psij ν s j (x + t • v)
      - (-2 * (ageA ν s)⁻¹) * (Real.exp (-(sq2 (xj ν j (x + t • v))) / (4 * ageA ν s)) *
          (-(2 * ((xj ν j (x + t • v)).1 * (merApply B (xj ν j (x + t • v))).1
            + (xj ν j (x + t • v)).2 * (merApply B (xj ν j (x + t • v))).2)) / (4 * ageA ν s))) := by
    funext t
    rw [tw_gjPsi_eq]
  rw [hfun]
  refine hmain.congr_deriv ?_
  simp only [zero_smul, add_zero, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma tw_fderiv_gjPsi (ν s : ℝ) (j : ℤ) (B : Mat3) (x v : ℝ × ℝ) :
    fderiv ℝ (gjPsi ν s B j) x v =
      (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (ageA ν s ^ 2)⁻¹) *
        ((merTrace B + ((xj ν j x).1 * (merApply B (xj ν j x)).1
            + (xj ν j x).2 * (merApply B (xj ν j x)).2) / (2 * ageA ν s))
          * ((xj ν j x).1 * v.1 + (xj ν j x).2 * v.2)
        - (v.1 * (merApply B (xj ν j x)).1 + (xj ν j x).1 * (merApply B v).1
          + (v.2 * (merApply B (xj ν j x)).2 + (xj ν j x).2 * (merApply B v).2))) := by
  rw [gp_fderiv_line _ x v (tw_gjPsi_diff ν s j B x)]
  exact (tw_gjPsi_line ν s j B x v).deriv

theorem hpTermIdentity_proof (ν : ℝ) : HpTermIdentity ν := by
  intro s j B x
  have h0 : ei 0 = ((1 : ℝ), (0 : ℝ)) := by simp [ei]
  have h1 : ei 1 = ((0 : ℝ), (1 : ℝ)) := by simp [ei]
  unfold mgrad
  rw [tw_fderiv_gjPsi, tw_fderiv_gjPsi, h0, h1, gp_fderiv_Vj]
  ext <;> simp only [Vj, merApply, Jrot, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, merTrace] <;> ring

end UnforcedLeray.Short.PartIIIb.Concrete
