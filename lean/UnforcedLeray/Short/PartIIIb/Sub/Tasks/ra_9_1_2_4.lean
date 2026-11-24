import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.GeoDTasks

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem xj_shift (ν : ℝ) (j : ℤ) (z : ℝ × ℝ) :
    xj ν j (z.1 + cOf ν, z.2) = xj ν (j - 1) z := by
  unfold xj
  congr 1
  push_cast
  ring

theorem Vj_shift (ν s : ℝ) (j : ℤ) (z : ℝ × ℝ) :
    Vj ν s j (z.1 + cOf ν, z.2) = Vj ν s (j - 1) z := by
  unfold Vj
  rw [xj_shift]

theorem psij_shift (ν s : ℝ) (j : ℤ) (z : ℝ × ℝ) :
    psij ν s j (z.1 + cOf ν, z.2) = psij ν s (j - 1) z := by
  unfold psij
  rw [xj_shift]

theorem add_c_eq (ν : ℝ) (z : ℝ × ℝ) : z + (cOf ν, 0) = (z.1 + cOf ν, z.2) := by
  ext <;> simp

theorem fderiv_Vj_shift (ν s : ℝ) (j : ℤ) (z : ℝ × ℝ) :
    fderiv ℝ (Vj ν s j) (z.1 + cOf ν, z.2) = fderiv ℝ (Vj ν s (j - 1)) z := by
  have e1 : fderiv ℝ (fun w : ℝ × ℝ => Vj ν s j (w + (cOf ν, 0))) z
      = fderiv ℝ (Vj ν s j) (z + (cOf ν, 0)) := fderiv_comp_add_right _
  have e2 : (fun w : ℝ × ℝ => Vj ν s j (w + (cOf ν, 0))) = Vj ν s (j - 1) := by
    funext w
    rw [add_c_eq, Vj_shift]
  rw [e2, add_c_eq] at e1
  exact e1.symm

theorem fderiv_psij_shift (ν s : ℝ) (j : ℤ) (z : ℝ × ℝ) :
    fderiv ℝ (psij ν s j) (z.1 + cOf ν, z.2) = fderiv ℝ (psij ν s (j - 1)) z := by
  have e1 : fderiv ℝ (fun w : ℝ × ℝ => psij ν s j (w + (cOf ν, 0))) z
      = fderiv ℝ (psij ν s j) (z + (cOf ν, 0)) := fderiv_comp_add_right _
  have e2 : (fun w : ℝ × ℝ => psij ν s j (w + (cOf ν, 0))) = psij ν s (j - 1) := by
    funext w
    rw [add_c_eq, psij_shift]
  rw [e2, add_c_eq] at e1
  exact e1.symm

theorem hpA_shift (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    hpA ν χ A s (x.1 + cOf ν, x.2) = hpA ν χ A s x := by
  unfold hpA
  have key : ∀ j : ℤ,
      (merApply (Ay ν χ A s) (Vj ν s j (x.1 + cOf ν, x.2))
        - fderiv ℝ (Vj ν s j) (x.1 + cOf ν, x.2)
          (merApply (Ay ν χ A s) (xj ν j (x.1 + cOf ν, x.2))))
      = (merApply (Ay ν χ A s) (Vj ν s (j - 1) x)
        - fderiv ℝ (Vj ν s (j - 1)) x (merApply (Ay ν χ A s) (xj ν (j - 1) x))) := by
    intro j
    rw [Vj_shift, fderiv_Vj_shift, xj_shift]
  simp only [key]
  exact Equiv.tsum_eq (Equiv.subRight (1 : ℤ))
    (fun k : ℤ => merApply (Ay ν χ A s) (Vj ν s k x)
      - fderiv ℝ (Vj ν s k) x (merApply (Ay ν χ A s) (xj ν k x)))

theorem psipA_shift (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    psipA ν χ A s (x.1 + cOf ν, x.2) = psipA ν χ A s x := by
  unfold psipA
  have key : ∀ j : ℤ,
      (merTrace (Ay ν χ A s) * psij ν s j (x.1 + cOf ν, x.2)
        - fderiv ℝ (psij ν s j) (x.1 + cOf ν, x.2)
          (merApply (Ay ν χ A s) (xj ν j (x.1 + cOf ν, x.2))))
      = (merTrace (Ay ν χ A s) * psij ν s (j - 1) x
        - fderiv ℝ (psij ν s (j - 1)) x (merApply (Ay ν χ A s) (xj ν (j - 1) x))) := by
    intro j
    rw [psij_shift, fderiv_psij_shift, xj_shift]
  simp only [key]
  exact Equiv.tsum_eq (Equiv.subRight (1 : ℤ))
    (fun k : ℤ => merTrace (Ay ν χ A s) * psij ν s k x
      - fderiv ℝ (psij ν s k) x (merApply (Ay ν χ A s) (xj ν k x)))

theorem Kop_shift (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    Kop (fun s' y => psipA ν χ A s' y) s (x.1 + cOf ν, x.2)
      = Kop (fun s' y => psipA ν χ A s' y) s x := by
  unfold Kop
  have e1 : fderiv ℝ (fun w : ℝ × ℝ => psipA ν χ A s (w + (cOf ν, 0))) x
      = fderiv ℝ (fun y => psipA ν χ A s y) (x + (cOf ν, 0)) := fderiv_comp_add_right _
  have e2 : (fun w : ℝ × ℝ => psipA ν χ A s (w + (cOf ν, 0)))
      = fun y => psipA ν χ A s y := by
    funext w
    rw [add_c_eq]
    exact psipA_shift ν χ A s w
  rw [e2] at e1
  simp only [psipA_shift]
  rw [← add_c_eq ν x, e1]


theorem hbM_shift (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) :
    hbM ν ε χf A (s, (x.1 + cOf ν, x.2)) = hbM ν ε χf A (s, x) := by
  simp only [hbM, hpM, thetaM, Pi.add_apply, Pi.smul_apply, hpA_shift, psipA_shift,
    Kop_shift]

theorem hAcoef_eq_hbM (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) {s : ℝ} (hs : 0 < s) (x : ℝ × ℝ) :
    hAcoef ν ε χf A (s, x) = hbM ν ε χf A (s, x) := by
  have hsq : √s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  unfold hAcoef hhatA
  simp only
  rw [inv_smul_smul₀ hsq]
  ext i
  fin_cases i <;> simp [merOf, emb, hbM, hpM, thetaM, toMer]


theorem hLiftIsNv (as : ℝ) (χf : ℝ → ℝ) : HLiftIsNv as χf := by
  intro _ ν ε hν hε A _ τ y hy
  have hR : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  have hage : 0 < (chart ε⁻¹ τ y).1 := age_pos hR hy
  have key : ∀ p : Chart, 0 < p.1 →
      perExt (cOf ν) (hAcoef ν ε χf A) p = hbM ν ε χf A p := by
    rintro ⟨s, ξ, η⟩ hp
    have hper : Function.Periodic (fun ξ' => hbM ν ε χf A (s, (ξ', η))) (cOf ν) :=
      fun ξ' => hbM_shift ν ε χf A s (ξ', η)
    have hcell : cellRep (cOf ν) ξ = ξ - ⌊(ξ + cOf ν / 2) / cOf ν⌋ * cOf ν := by
      simp only [cellRep]
      ring
    show hAcoef ν ε χf A (s, (cellRep (cOf ν) ξ, η)) = hbM ν ε χf A (s, (ξ, η))
    rw [hAcoef_eq_hbM ν ε χf A hp, hcell]
    exact hper.sub_int_mul_eq _
  show Nv ε⁻¹ (perExt (cOf ν) (hAcoef ν ε χf A)) τ y = Nv ε⁻¹ (hbM ν ε χf A) τ y
  unfold Nv
  rw [key _ hage]

end UnforcedLeray.Short.PartIIIb.Concrete
