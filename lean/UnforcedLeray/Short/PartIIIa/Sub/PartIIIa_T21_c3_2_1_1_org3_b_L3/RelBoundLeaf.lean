import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L3.RelBoundLeaf.Core

/-!
# Leaf F: the planar relative bound (SP 2926-2935, 2976-2980)

Source: `the November 2 reference manuscript` (SP) 2926-2935, 2976-2980.

`PlanarRelBoundLeaf κ`: `‖e^{-γB}e^{B𝓛}𝒬 + e^{-B}𝒫‖ ≤ C₀e^{-hB} + Cproj e^{-B}` on `L²_m`.

Proof. Split `x = x₀ + x'` into the angular sector `0`, `x₀ = P₀x`, and the rest. The sector `0`
is stationary, `e^{B𝓛}x₀ = x₀`, and `𝒫x₀ = 0` (the pairings read the sectors `±2`), so the
relative evolution is `e^{-γB}x₀`; `e^{-γB} ≤ e^{-hB} ≤ C₀e^{-hB}` because `h ≤ γ` and `C₀ ≥ 1`
(`SeedCtx` at `t = 0`). The rest `x'` has zero mass, so it is the value of an element of
`𝒳_{0,m}` (`PartI.xjM0Bridge`); there `𝒫x' = seedProjFun h x'` a.e., `SeedCtx` bounds the
`𝒬` part by `C₀e^{-hB}‖x'‖` and `SeedProjBdd` the `𝒫` part by `Cproj e^{-B}‖x'‖`. The two
images are orthogonal (the second has no sector-`0` part: `e^{B𝓛}` preserves sectors and `𝒫`
maps into the sectors `±2`), and `x₀ ⊥ x'`, so Pythagoras gives the bound for `x`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.IIIa.PlanarDysonL3

open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit
open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3
open UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.PlanarB
open EigenLeafAux RelBoundAux

/-- **Leaf F** (SP 2926-2935, 2976-2980). -/
theorem planarRelBoundLeaf_proof (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.PlanarDysonL3.PlanarRelBoundLeaf κ := by
  intro hκ P _hP m hm _hm8 C₀ h Cproj B hC₀ hh hhγ hCp hB hctx hproj
  have hC₀1 : 1 ≤ C₀ := one_le_of_seedCtx κ hκ P hm hctx
  obtain ⟨lam₁, h₁, hh₁, ℓ₁, hs₁, he0₁, he1₁, -, hdec⟩ := hctx
  obtain ⟨lam₂, h₂, hh₂, ℓ₂, hs₂, he0₂, he1₂, hbdd⟩ := hproj
  set K : ℝ := C₀ * Real.exp (-h * B) + Cproj * Real.exp (-B) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hK0 (fun x => ?_)
  -- the splitting `x = x₀ + x'`
  set v₀ : Planar.ProfL2 m := Planar.secProf m 0 x with hv₀
  set x₀ : Planar.L2w m := Planar.secEmb m 0 v₀ with hx₀
  set x' : Planar.L2w m := x - x₀ with hx'
  have hxx : x = x₀ + x' := by rw [hx']; abel
  have hsx' : Planar.secProf m 0 x' = 0 := by
    rw [hx', map_sub, hx₀, Planar.secProf_secEmb_self, hv₀, sub_self]
  -- sector `0`
  have hP0 : planarProj κ hm x₀ = 0 :=
    planarProj_secEmb_eq_zero κ hκ hm hs₁ he0₁ v₀ (by decide) (by decide)
  have hE0 : Planar.eulerGroupW hm B x₀ = x₀ := by
    have hL : Planar.Lsec hm 0 v₀ = (0 : ℂ) • v₀ := by
      rw [Planar.Lsec_zero, ContinuousLinearMap.zero_apply, zero_smul]
    rw [hx₀, eulerGroupW_secEmb_eigen hm hL B, zero_mul, Complex.exp_zero, one_smul]
  have hR0 : relSol κ P hm B x₀ = ((Real.exp (-P.eigenvalue.re * B) : ℝ) : ℂ) • x₀ := by
    rw [relSol_apply, hP0, sub_zero, hE0, smul_zero, add_zero]
  have hexp : Real.exp (-P.eigenvalue.re * B) ≤ K := by
    have h1 : Real.exp (-P.eigenvalue.re * B) ≤ Real.exp (-h * B) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h2 : Real.exp (-h * B) ≤ C₀ * Real.exp (-h * B) :=
      le_mul_of_one_le_left (Real.exp_pos _).le hC₀1
    have h3 : 0 ≤ Cproj * Real.exp (-B) := mul_nonneg hCp (Real.exp_pos _).le
    linarith
  have hb0 : ‖relSol κ P hm B x₀‖ ≤ K * ‖x₀‖ := by
    rw [hR0, norm_ofReal_exp_smul]
    exact mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  -- the zero-mass rest
  have hx'X : x' ∈ Planar.X0 hm := by
    show Planar.massCLM hm x' = 0
    rw [hx', map_sub, Planar.massCLM_eq_secEmb_zero hm x, sub_self]
  obtain ⟨F₀, hF₀v, hF₀n⟩ := (PartI.xjM0Bridge m hm).2 ⟨x', hx'X⟩
  have hF₀n' : ‖F₀‖ = ‖x'‖ := hF₀n
  obtain ⟨u, g, hu, hg, hb⟩ := hdec hm B hB.le F₀
  have hsp₁ := planarProj_ae_seedProjFun κ hκ hm hs₁ he0₁ he1₁ x' hF₀v.symm
  have hu' : u = x' - planarProj κ hm x' := by
    apply Lp.ext
    refine (Planar.wMeasure_ac m).ae_le ?_
    filter_upwards [hu, hF₀v, hsp₁,
      (Planar.volume_ac m).ae_le (Lp.coeFn_sub x' (planarProj κ hm x'))] with y a b c d
    rw [a, b, ← c, d, Pi.sub_apply]
  have hgv : ((g : B0008.HjM 0 m).value : Planar.L2w m) =
      Planar.eulerGroupW hm B (x' - planarProj κ hm x') := by
    rw [← hu']
    exact Lp.ext ((B0008.wMeasure_ac m).ae_le hg)
  have hgn : ‖g‖ = ‖Planar.eulerGroupW hm B (x' - planarProj κ hm x')‖ := by
    rw [← hgv]
    exact PartI.xjM0_norm_eq_value _
  rw [hgn, hF₀n'] at hb
  obtain ⟨u₂, hu₂, hu₂b⟩ := hbdd F₀
  have hsp₂ := planarProj_ae_seedProjFun κ hκ hm hs₂ he0₂ he1₂ x' hF₀v.symm
  have hu₂' : u₂ = planarProj κ hm x' := by
    apply Lp.ext
    refine (Planar.wMeasure_ac m).ae_le ?_
    filter_upwards [hu₂, hsp₂] with y a b
    rw [a, b]
  rw [hu₂', hF₀n'] at hu₂b
  have hb' : ‖relSol κ P hm B x'‖ ≤ K * ‖x'‖ := by
    rw [relSol_apply]
    calc _ ≤ ‖((Real.exp (-P.eigenvalue.re * B) : ℝ) : ℂ) •
            Planar.eulerGroupW hm B (x' - planarProj κ hm x')‖ +
          ‖((Real.exp (-B) : ℝ) : ℂ) • planarProj κ hm x'‖ := norm_add_le _ _
      _ = Real.exp (-P.eigenvalue.re * B) *
            ‖Planar.eulerGroupW hm B (x' - planarProj κ hm x')‖ +
          Real.exp (-B) * ‖planarProj κ hm x'‖ := by
        rw [norm_ofReal_exp_smul, norm_ofReal_exp_smul]
      _ ≤ C₀ * Real.exp (-h * B) * ‖x'‖ + Real.exp (-B) * (Cproj * ‖x'‖) :=
        add_le_add hb (mul_le_mul_of_nonneg_left hu₂b (Real.exp_pos _).le)
      _ = K * ‖x'‖ := by rw [hK]; ring
  -- orthogonality and Pythagoras
  have hsR : Planar.secProf m 0 (relSol κ P hm B x') = 0 := by
    rw [relSol_apply, map_add, map_smul, map_smul, Planar.secProf_eulerGroupW,
      Planar.expSec_zero_sector, ContinuousLinearMap.one_apply, map_sub, hsx',
      secProf_zero_planarProj κ hm (hh := hh₁) he0₁ he1₁, sub_self, smul_zero, smul_zero,
      add_zero]
  have hR0' : relSol κ P hm B x₀ =
      Planar.secEmb m 0 (((Real.exp (-P.eigenvalue.re * B) : ℝ) : ℂ) • v₀) := by
    rw [hR0, hx₀, LinearIsometry.map_smul]
  have horthR : ⟪relSol κ P hm B x₀, relSol κ P hm B x'⟫_ℂ = 0 := by
    rw [hR0']
    exact inner_secEmb_zero_of _ hsR
  have horthx : ⟪x₀, x'⟫_ℂ = 0 := inner_secEmb_zero_of _ hsx'
  have hPy1 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthR
  have hPy2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthx
  rw [← map_add, ← hxx] at hPy1
  rw [← hxx] at hPy2
  have hKx : 0 ≤ K * ‖x‖ := mul_nonneg hK0 (norm_nonneg _)
  refine (mul_self_le_mul_self_iff (norm_nonneg _) hKx).2 ?_
  have e1 : ‖relSol κ P hm B x₀‖ * ‖relSol κ P hm B x₀‖ ≤ (K * ‖x₀‖) * (K * ‖x₀‖) :=
    mul_self_le_mul_self (norm_nonneg _) hb0
  have e2 : ‖relSol κ P hm B x'‖ * ‖relSol κ P hm B x'‖ ≤ (K * ‖x'‖) * (K * ‖x'‖) :=
    mul_self_le_mul_self (norm_nonneg _) hb'
  calc ‖relSol κ P hm B x‖ * ‖relSol κ P hm B x‖
      = ‖relSol κ P hm B x₀‖ * ‖relSol κ P hm B x₀‖ +
          ‖relSol κ P hm B x'‖ * ‖relSol κ P hm B x'‖ := hPy1
    _ ≤ (K * ‖x₀‖) * (K * ‖x₀‖) + (K * ‖x'‖) * (K * ‖x'‖) := add_le_add e1 e2
    _ = K * K * (‖x₀‖ * ‖x₀‖ + ‖x'‖ * ‖x'‖) := by ring
    _ = (K * ‖x‖) * (K * ‖x‖) := by rw [← hPy2]; ring

end UnforcedLeray.Short.IIIa.PlanarDysonL3
