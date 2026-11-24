import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_5
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# `KerIBP`: integration by parts against a cylinder test (SP 2081-2084)

For `G` smooth and `d`-periodic in `q`, and a cylinder test `φ`,
`∫_{C_d} (∂_qG ∂_ηφ - ∂_ηG ∂_qφ) = 0`. The `q`-derivative is moved off `G` by periodic
integration by parts (`Cyl.integral_cell_partialQ_mul`), the `η`-derivative by integration by
parts with compact `η`-support (`Cyl.integral_cell_partialEta_mul`), and the two resulting
second derivatives of `φ` agree by symmetry of the second derivative.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace UnforcedLeray

theorem kerIBP_cell (c : ℝ) : B0579.cell c = Cyl.cell c := by
  unfold B0579.cell Cyl.cell
  rw [neg_div]

theorem kerIBP_pd_comm {f : B0579.Plane → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin 2)
    (x : B0579.Plane) :
    B0579.pd i (B0579.pd j f) x = B0579.pd j (B0579.pd i f) x := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  have h1 : ∀ (u : B0579.Plane), DifferentiableAt ℝ (fderiv ℝ f) x := fun _ =>
    ((hf2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have hder : ∀ k l : Fin 2, B0579.pd k (B0579.pd l f) x =
      fderiv ℝ (fderiv ℝ f) x (B0579.dir k) (B0579.dir l) := by
    intro k l
    unfold B0579.pd
    have hd := (h1 x).hasFDerivAt.clm_apply (hasFDerivAt_const (B0579.dir l) x)
    have := hd.fderiv
    simp only [ContinuousLinearMap.comp_zero, zero_add] at this
    rw [show (fun y => fderiv ℝ f y (B0579.dir l)) = _ from rfl, this]
    rfl
  rw [hder, hder]
  have hsym := (hf2.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  exact hsym _ _

theorem kerIBP_partialQ {ψ : B0579.Plane → ℝ} (hψ : Differentiable ℝ ψ) (z : B0579.Plane) :
    Cyl.partialQ ψ z = B0579.pd 0 ψ z := by
  rw [Cyl.partialQ_eq_fderiv hψ]
  rfl

theorem kerIBP_partialEta {ψ : B0579.Plane → ℝ} (hψ : Differentiable ℝ ψ) (z : B0579.Plane) :
    Cyl.partialEta ψ z = B0579.pd 1 ψ z := by
  rw [Cyl.partialEta_eq_fderiv hψ]
  rfl

theorem kerIBP_pd_continuous {G : B0579.Plane → ℝ} (hG : ContDiff ℝ ∞ G) (j : Fin 2) :
    Continuous (B0579.pd j G) := by
  have h : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by simp)
  unfold B0579.pd
  exact h.clm_apply continuous_const

theorem kerIBP_int_mul_test {c : ℝ} {g ψ : B0579.Plane → ℝ} (hg : Continuous g)
    (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun z => g z * ψ z) (Cyl.cell c) := by
  rw [← kerIBP_cell]
  obtain ⟨R, hR⟩ := hψ.vanish
  refine B0579.integrableOn_cell_of_continuous (hg.mul hψ.continuous)
    (B0579.isCompact_box c R) ?_
  intro x hx hxK
  simp [hR x hx hxK]

end UnforcedLeray

open UnforcedLeray

theorem kerIBP : UnforcedLeray.Short.IIIa.KerIBP := by
  intro d hd G hG hper φ hφ
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hGc : Continuous G := hG.continuous
  have hGp : Cyl.IsPeriodic d G := hper
  have hφ1 : B0579.IsCylTest d (B0579.pd 1 φ) := hφ.pd 1
  have hφ0 : B0579.IsCylTest d (B0579.pd 0 φ) := hφ.pd 0
  have hφ1d : Differentiable ℝ (B0579.pd 1 φ) := hφ1.differentiable
  have hφ0d : Differentiable ℝ (B0579.pd 0 φ) := hφ0.differentiable
  rw [kerIBP_cell d]
  have hint1 : IntegrableOn (fun x => B0579.pd 0 G x * B0579.pd 1 φ x) (Cyl.cell d) :=
    kerIBP_int_mul_test (kerIBP_pd_continuous hG 0) hφ1
  have hint2 : IntegrableOn (fun x => B0579.pd 1 G x * B0579.pd 0 φ x) (Cyl.cell d) :=
    kerIBP_int_mul_test (kerIBP_pd_continuous hG 1) hφ0
  rw [integral_sub hint1 hint2]
  -- q-integration by parts for the first term
  have qh1 : IntegrableOn (fun z => Cyl.partialQ G z * B0579.pd 1 φ z) (Cyl.cell d) := by
    simp only [kerIBP_partialQ hGd]
    exact hint1
  have qh2 : IntegrableOn (fun z => G z * Cyl.partialQ (B0579.pd 1 φ) z) (Cyl.cell d) := by
    simp only [kerIBP_partialQ hφ1d]
    exact kerIBP_int_mul_test hGc (hφ1.pd 0)
  have ea := Cyl.integral_cell_partialQ_mul hd hGd hφ1d hGp hφ1.periodic qh1 qh2
  -- eta-integration by parts for the second term
  have eh0 : IntegrableOn (fun z => G z * B0579.pd 0 φ z) (Cyl.cell d) :=
    kerIBP_int_mul_test hGc hφ0
  have eh1 : IntegrableOn (fun z => Cyl.partialEta G z * B0579.pd 0 φ z) (Cyl.cell d) := by
    simp only [kerIBP_partialEta hGd]
    exact hint2
  have eh2 : IntegrableOn (fun z => G z * Cyl.partialEta (B0579.pd 0 φ) z) (Cyl.cell d) := by
    simp only [kerIBP_partialEta hφ0d]
    exact kerIBP_int_mul_test hGc (hφ0.pd 1)
  have eb := Cyl.integral_cell_partialEta_mul hGd hφ0d eh0 eh1 eh2
  simp only [kerIBP_partialQ hGd, kerIBP_partialQ hφ1d, kerIBP_partialEta hGd,
    kerIBP_partialEta hφ0d] at ea eb
  have hcomm : ∀ z : B0579.Plane,
      B0579.pd 0 (B0579.pd 1 φ) z = B0579.pd 1 (B0579.pd 0 φ) z :=
    fun z => kerIBP_pd_comm hφ.smooth 0 1 z
  simp only [hcomm] at ea
  rw [ea, eb]
  ring
