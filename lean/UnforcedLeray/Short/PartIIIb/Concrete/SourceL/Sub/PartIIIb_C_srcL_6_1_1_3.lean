import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3.Helpers

/-!
# Local domination of the Newton leaves (task `PartIII-b:C/srcL/6/1/1/3`)

Source of record: `the November 2 reference manuscript` lines 4776-4791, 4917-4937.
Leaf 3 `NewtonFamDom`: for `x` in the region `U = {5ν/6 < x₀²+x₁²}` there is a neighbourhood `s`
and an integrable bound `g` on `(0,1]` for the `n`-th derivative of `newtonFam i t` on `s`.
The bound is `t^{2μ+2} · B` with `B = (∫ Σ_{jk}|Σ_M(a)_{jk}| da) · C`, where `C` bounds the
kernel derivatives on the compact set `kerSet δ R` of arguments avoiding `0`
(`NewtonFam.locDom_unif`); the parametric-integral bound is `norm_iteratedFDeriv_integral_le`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem newtonFamDom : NewtonFamDom := by
  intro c ν μ χo M hc hν hμ hχ hM i n x hx
  obtain ⟨s, hs, hsU, C, hC⟩ := NewtonFam.locDom_unif c ν χo M hν hχ i n x hx
  have hU := isOpen_newtonRegion ν
  have hint : Integrable (fun a : ℝ × ℝ => ∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖)
      (volume : Measure (ℝ × ℝ)) :=
    NewtonFam.sigma_norm_sum_integrable c ν χo M hc hν hχ hM
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = (∫ a : ℝ × ℝ,
      ∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖ ∂(volume : Measure (ℝ × ℝ))) * C :=
    ⟨_, rfl⟩
  refine ⟨s, hs, fun t => t ^ (2 * μ + 2) * B, ?_, ?_⟩
  · have hcont : Continuous (fun t : ℝ => t ^ (2 * μ + 2) * B) :=
      (continuous_id.rpow_const fun _ => Or.inr (by linarith)).mul continuous_const
    exact hcont.integrableOn_Ioc
  · intro t ht y hy
    show ‖iteratedFDeriv ℝ n (newtonFam c ν μ χo M i t) y‖ ≤ t ^ (2 * μ + 2) * B
    have hyU : y ∈ {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := hsU hy
    have hsmooth := NewtonFam.famF_integral_contDiffOn c ν χo M hc hν hχ hM t ht i
    have hGat : ContDiffAt ℝ (n : WithTop ℕ∞)
        (fun y : Vec3 => ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y ∂(volume : Measure (ℝ × ℝ))) y :=
      (hsmooth.contDiffAt ((isOpen_newtonRegion ν).mem_nhds hyU)).of_le (by exact_mod_cast le_top)
    have e : newtonFam c ν μ χo M i t = (t ^ (2 * μ + 2)) •
        (fun y : Vec3 => ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y ∂(volume : Measure (ℝ × ℝ))) := by
      funext z
      rfl
    have hbound : ‖iteratedFDeriv ℝ n
        (fun y : Vec3 => ∫ a : ℝ × ℝ, NewtonFam.famF c ν χo M t i a y ∂(volume : Measure (ℝ × ℝ))) y‖
          ≤ B := by
      have h1 := UnforcedLeray.L09.norm_iteratedFDeriv_integral_le (μ := (volume : Measure (ℝ × ℝ))) hU
        (Filter.Eventually.of_forall fun a => NewtonFam.famF_contDiffOn c ν χo M hν hχ t ht i a)
        (fun n x hx => NewtonFam.famF_aesm c ν χo M hc hν hχ hM t ht i n x hx)
        (NewtonFam.famF_locDom c ν χo M hν hχ hc hM t ht i) n hyU
      have hB' : ∫ a : ℝ × ℝ, (∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) * C
          ∂(volume : Measure (ℝ × ℝ)) = B := by
        rw [hBdef, integral_mul_const]
      have h2 : ∫ a : ℝ × ℝ, ‖iteratedFDeriv ℝ n (NewtonFam.famF c ν χo M t i a) y‖
            ∂(volume : Measure (ℝ × ℝ))
          ≤ ∫ a : ℝ × ℝ, (∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) * C
            ∂(volume : Measure (ℝ × ℝ)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => norm_nonneg _)
          (hint.mul_const C) (Filter.Eventually.of_forall fun a => hC t ht a y hy)
      exact h1.trans (h2.trans hB'.le)
    rw [e, iteratedFDeriv_const_smul_apply hGat, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg ht.1.le _)

end UnforcedLeray.Short.PartIIIb.Concrete
