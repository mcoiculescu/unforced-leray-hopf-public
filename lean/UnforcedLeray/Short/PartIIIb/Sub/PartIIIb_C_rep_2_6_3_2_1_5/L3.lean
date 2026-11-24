import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S1a

/-!
# `LkerSumEq` (`PartIII-b:C/rep/2/6/3/2/1/5/3`)

Source `the November 2 reference manuscript`
lines 3603-3626, 3800-3807, 4171-4200.

`∑∑ Gker · T(t₀-h) = -(l/2) sepPhi (l,z)` (`gkerSum_eq_sepPhi`, `l = e^{-h/2}`) holds for all `y`,
and `L` is linear in the kernel with `T` independent of `y`.  The `y`-derivatives of the finite
sums are taken termwise (`HasFDerivAt.sum`, `HasFDerivAt.const_mul`), each `Gker` being `C²` in `y`
for `h > 0` (`L4_term_cd`, `heatLerayKSmooth`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem L3_fderivApp_diff (f : Space → ℂ) (hf : ContDiff ℝ 2 f) (e : Space) :
    Differentiable ℝ (fun x => fderiv ℝ f x e) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  exact (h1.clm_apply contDiff_const).differentiable (by norm_num)

theorem L3_gker_cd (ν : ℝ) (μ : ℂ) (h : ℝ) (hν : 0 < ν) (hh : 0 < h) (z : Space) (i j k : Fin 3) :
    ContDiff ℝ 2 (fun x => Gker ν μ h x z i j k) := by
  have hexp : Real.exp (-h) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have ht : 0 < ν * (1 - Real.exp (-h)) := mul_pos hν (by linarith)
  have hK : ContDiff ℝ 3 (fun x => IIIa.heatLerayK (ν * (1 - Real.exp (-h))) i j x) :=
    heatLerayKSmooth _ ht i j
  unfold Gker
  exact L4_term_cd _ hK _ _ _

theorem L3_nested_fderiv (w : Fin 3 → Fin 3 → ℂ) (H : Fin 3 → Fin 3 → Space → ℂ)
    (hH : ∀ j k, Differentiable ℝ (H j k)) (x : Space) :
    fderiv ℝ (fun x' => ∑ j : Fin 3, ∑ k : Fin 3, w j k * H j k x') x =
      ∑ j : Fin 3, ∑ k : Fin 3, w j k • fderiv ℝ (H j k) x := by
  have h : HasFDerivAt (fun x' => ∑ j : Fin 3, ∑ k : Fin 3, w j k * H j k x')
      (∑ j : Fin 3, ∑ k : Fin 3, w j k • fderiv ℝ (H j k) x) x := by
    have hk : ∀ j : Fin 3, HasFDerivAt (fun x' => ∑ k : Fin 3, w j k * H j k x')
        (∑ k : Fin 3, w j k • fderiv ℝ (H j k) x) x := fun j =>
      HasFDerivAt.fun_sum (fun k _ => ((hH j k x).hasFDerivAt).const_mul (w j k))
    exact HasFDerivAt.fun_sum (fun j _ => hk j)
  exact h.fderiv

theorem L3_fderiv_const_mul (c : ℂ) (f : Space → ℂ) (hf : Differentiable ℝ f) (y e : Space) :
    fderiv ℝ (fun x => c * f x) y e = c * fderiv ℝ f y e := by
  rw [((hf y).hasFDerivAt.const_mul c).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem lkerSumEq : LkerSumEq := by
  intro ν μ hν T t₀ h hh y z i
  have hl : Real.exp (-h / 2) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
  have hSc : ContDiff ℝ 2 (sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z)) :=
    sepPhi_contDiff heatLerayKSmooth ν (μ : ℂ) T t₀ i _ z hν hl
  have hSd : Differentiable ℝ (sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z)) :=
    hSc.differentiable (by norm_num)
  have hGd : ∀ j k, Differentiable ℝ (fun x => Gker ν (μ : ℂ) h x z i j k) := fun j k =>
    (L3_gker_cd ν (μ : ℂ) h hν hh z i j k).differentiable (by norm_num)
  -- pointwise identity of the sums
  have hF : ∀ x, ∑ j : Fin 3, ∑ k : Fin 3, ((T (t₀ - h) z j k : ℝ) : ℂ) * Gker ν (μ : ℂ) h x z i j k
      = -((Real.exp (-h / 2) / 2 : ℝ) : ℂ) * sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z) x := by
    intro x
    rw [← gkerSum_eq_sepPhi ν (μ : ℂ) T t₀ i x z h]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hFfun : (fun x => ∑ j : Fin 3, ∑ k : Fin 3, ((T (t₀ - h) z j k : ℝ) : ℂ) * Gker ν (μ : ℂ) h x z i j k)
      = fun x => -((Real.exp (-h / 2) / 2 : ℝ) : ℂ) * sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z) x :=
    funext hF
  have hFd : ∀ x, fderiv ℝ (fun x' => ∑ j : Fin 3, ∑ k : Fin 3,
      ((T (t₀ - h) z j k : ℝ) : ℂ) * Gker ν (μ : ℂ) h x' z i j k) x
      = (-((Real.exp (-h / 2) / 2 : ℝ) : ℂ)) • fderiv ℝ (sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z)) x := by
    intro x
    rw [hFfun]
    exact ((hSd x).hasFDerivAt.const_mul _).fderiv
  -- first derivative in the direction e
  have hpt : ∀ (x e : Space), ∑ j : Fin 3, ∑ k : Fin 3, ((T (t₀ - h) z j k : ℝ) : ℂ) *
      fderiv ℝ (fun x'' => Gker ν (μ : ℂ) h x'' z i j k) x e
      = -((Real.exp (-h / 2) / 2 : ℝ) : ℂ) * fderiv ℝ (sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z)) x e := by
    intro x e
    have hn := L3_nested_fderiv (fun j k => ((T (t₀ - h) z j k : ℝ) : ℂ))
      (fun j k x' => Gker ν (μ : ℂ) h x' z i j k) (fun j k => hGd j k) x
    have h2 := congrArg (fun L : Space →L[ℝ] ℂ => L e) (hn.symm.trans (hFd x))
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h2
    exact h2
  have E1 : ∑ j : Fin 3, ∑ k : Fin 3, ((T (t₀ - h) z j k : ℝ) : ℂ) *
      fderiv ℝ (fun y' => Gker ν (μ : ℂ) h y' z i j k) y y
      = -((Real.exp (-h / 2) / 2 : ℝ) : ℂ) * fderiv ℝ (sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z)) y y :=
    hpt y y
  have E2 : ∀ m : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ((T (t₀ - h) z j k : ℝ) : ℂ) *
      fderiv ℝ (fun y' => fderiv ℝ (fun y'' => Gker ν (μ : ℂ) h y'' z i j k) y'
        (UnforcedLeray.coordinateVector m)) y (UnforcedLeray.coordinateVector m)
      = -((Real.exp (-h / 2) / 2 : ℝ) : ℂ) * fderiv ℝ (fun y' =>
          fderiv ℝ (sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z)) y'
            (UnforcedLeray.coordinateVector m)) y (UnforcedLeray.coordinateVector m) := by
    intro m
    have hH : ∀ j k, Differentiable ℝ (fun x' => fderiv ℝ
        (fun y'' => Gker ν (μ : ℂ) h y'' z i j k) x' (UnforcedLeray.coordinateVector m)) :=
      fun j k => L3_fderivApp_diff _ (L3_gker_cd ν (μ : ℂ) h hν hh z i j k) _
    have hn2 := L3_nested_fderiv (fun j k => ((T (t₀ - h) z j k : ℝ) : ℂ))
      (fun j k x' => fderiv ℝ (fun y'' => Gker ν (μ : ℂ) h y'' z i j k) x'
        (UnforcedLeray.coordinateVector m)) hH y
    have hfun2 : (fun x' => ∑ j : Fin 3, ∑ k : Fin 3, ((T (t₀ - h) z j k : ℝ) : ℂ) *
        fderiv ℝ (fun y'' => Gker ν (μ : ℂ) h y'' z i j k) x' (UnforcedLeray.coordinateVector m))
        = fun x' => -((Real.exp (-h / 2) / 2 : ℝ) : ℂ) * fderiv ℝ
          (sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z)) x' (UnforcedLeray.coordinateVector m) :=
      funext fun x' => hpt x' _
    have hn3 : fderiv ℝ (fun x' => ∑ j : Fin 3, ∑ k : Fin 3, ((T (t₀ - h) z j k : ℝ) : ℂ) *
        fderiv ℝ (fun y'' => Gker ν (μ : ℂ) h y'' z i j k) x' (UnforcedLeray.coordinateVector m)) y
        = fderiv ℝ (fun x' => -((Real.exp (-h / 2) / 2 : ℝ) : ℂ) * fderiv ℝ
          (sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z)) x' (UnforcedLeray.coordinateVector m)) y := by
      rw [hfun2]
    have h5 := L3_fderiv_const_mul (-((Real.exp (-h / 2) / 2 : ℝ) : ℂ))
      (fun x' => fderiv ℝ (sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z)) x'
        (UnforcedLeray.coordinateVector m))
      (L3_fderivApp_diff _ hSc _) y (UnforcedLeray.coordinateVector m)
    have key : (∑ j : Fin 3, ∑ k : Fin 3, ((T (t₀ - h) z j k : ℝ) : ℂ) •
        fderiv ℝ (fun x' => fderiv ℝ (fun y'' => Gker ν (μ : ℂ) h y'' z i j k) x'
          (UnforcedLeray.coordinateVector m)) y) (UnforcedLeray.coordinateVector m)
        = -((Real.exp (-h / 2) / 2 : ℝ) : ℂ) * fderiv ℝ (fun y' =>
          fderiv ℝ (sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z)) y'
            (UnforcedLeray.coordinateVector m)) y (UnforcedLeray.coordinateVector m) := by
      rw [← hn2, hn3, h5]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at key
    exact key
  unfold Lker
  have E2_0 := E2 0
  have E2_1 := E2 1
  have E2_2 := E2 2
  simp only [Fin.sum_univ_three] at E1 E2_0 E2_1 E2_2 ⊢
  linear_combination (1 / 2 : ℂ) * E1 + (ν : ℂ) * (E2_0 + E2_1 + E2_2)

end UnforcedLeray.Short.PartIIIb.Concrete
