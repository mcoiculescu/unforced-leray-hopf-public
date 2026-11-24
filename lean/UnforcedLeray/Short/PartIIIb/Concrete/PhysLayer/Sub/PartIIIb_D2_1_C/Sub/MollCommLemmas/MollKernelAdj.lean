import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt

/-!
# `MollKernelAdj`: the transpose of `L₀` on the mollified field

Source `the November 2 reference manuscript` (adjoint graph at `r = 2`, lines
1351-1362, and the mollified commutator, lines 1556-1583); the definitions are those of
`MollCommDefs`. For a `P`-periodic `Φ ∈ Y_2` (locally integrable by `locInt_of_isInYr`) and the
smooth compactly supported bump `κ = ρ.normed volume`, `mollP ρ Φ = κ ⋆ Φ` is differentiated
under the integral sign (Mathlib `HasCompactSupport.hasFDerivAt_convolution_left`), so every
derivative of `mollP ρ Φ` is the convolution of `Φ` with the corresponding derivative of `κ`.
Collecting terms gives exactly the kernel `adjKer ν μ ρ x`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `x ↦ ∫ c t • Φ (x - t)` for a real kernel `c`. -/
def kConv (c : ℝ × Space → ℝ) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => ∫ t, c t • Φ (x - t)

/-- A real kernel that is continuous with compact support. -/
def GoodK (c : ℝ × Space → ℝ) : Prop := Continuous c ∧ HasCompactSupport c

theorem gk_mul (a : ℝ) {c : ℝ × Space → ℝ} (hc : GoodK c) : GoodK (fun t => a * c t) :=
  ⟨continuous_const.mul hc.1, hc.2.mul_left (f := fun _ : ℝ × Space => a)⟩

theorem gk_add {c d : ℝ × Space → ℝ} (hc : GoodK c) (hd : GoodK d) :
    GoodK (fun t => c t + d t) :=
  ⟨hc.1.add hd.1, hc.2.add hd.2⟩

theorem gk_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ × Space → ℝ)
    (hc : ∀ i ∈ s, GoodK (c i)) : GoodK (fun t => ∑ i ∈ s, c i t) := by
  refine ⟨continuous_finsetSum s (fun i hi => (hc i hi).1), ?_⟩
  have hfun : (fun t => ∑ i ∈ s, c i t) = ∑ i ∈ s, c i := by
    funext t
    simp [Finset.sum_apply]
  rw [hfun]
  exact Finset.sum_induction c (fun f => HasCompactSupport f) (fun a b ha hb => ha.add hb)
    HasCompactSupport.zero (fun i hi => (hc i hi).2)

theorem gk_fderiv {c : ℝ × Space → ℝ} (hc : ContDiff ℝ 1 c) (hcs : HasCompactSupport c)
    (v : ℝ × Space) : GoodK (fun t => fderiv ℝ c t v) :=
  ⟨(hc.continuous_fderiv one_ne_zero).clm_apply continuous_const, hcs.fderiv_apply ℝ v⟩

theorem kConv_integrable {Φ : ℝ × Space → CVec3} (hloc : LocallyIntegrable Φ volume)
    {c : ℝ × Space → ℝ} (hc : GoodK c) (x : ℝ × Space) :
    Integrable (fun t => c t • Φ (x - t)) volume :=
  hc.2.convolutionExists_left ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3)) hc.1 hloc x

theorem kConv_fderiv {Φ : ℝ × Space → CVec3} (hloc : LocallyIntegrable Φ volume)
    {c : ℝ × Space → ℝ} (hc : ContDiff ℝ 1 c) (hcs : HasCompactSupport c) (x v : ℝ × Space) :
    fderiv ℝ (kConv c Φ) x v = kConv (fun t => fderiv ℝ c t v) Φ x := by
  have hEq : kConv c Φ = c ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3), volume] Φ := by
    funext y
    simp [kConv, convolution_def]
  have hD := hcs.hasFDerivAt_convolution_left ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3)) hc hloc x
  have hint : Integrable (fun t =>
      ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3)).precompL (ℝ × Space) (fderiv ℝ c t) (Φ (x - t)))
      volume :=
    (hcs.fderiv ℝ).convolutionExists_left (((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3)).precompL
      (ℝ × Space)) (hc.continuous_fderiv one_ne_zero) hloc x
  rw [hEq, hD.fderiv]
  simp only [convolution_def]
  rw [ContinuousLinearMap.integral_apply hint v]
  simp only [kConv]
  congr 1

theorem kConv_add {Φ : ℝ × Space → CVec3} (hloc : LocallyIntegrable Φ volume)
    {c d : ℝ × Space → ℝ} (hc : GoodK c) (hd : GoodK d) (x : ℝ × Space) :
    kConv (fun t => c t + d t) Φ x = kConv c Φ x + kConv d Φ x := by
  simp only [kConv, add_smul]
  exact integral_add (kConv_integrable hloc hc x) (kConv_integrable hloc hd x)

theorem kConv_smul_left (Φ : ℝ × Space → CVec3) (a : ℝ) (c : ℝ × Space → ℝ) (x : ℝ × Space) :
    kConv (fun t => a * c t) Φ x = a • kConv c Φ x := by
  simp only [kConv, mul_smul]
  exact integral_smul a _

theorem kConv_sum {Φ : ℝ × Space → CVec3} (hloc : LocallyIntegrable Φ volume)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ × Space → ℝ) (hc : ∀ i ∈ s, GoodK (c i))
    (x : ℝ × Space) :
    ∑ i ∈ s, kConv (c i) Φ x = kConv (fun t => ∑ i ∈ s, c i t) Φ x := by
  simp only [kConv, Finset.sum_smul]
  rw [integral_finset_sum]
  intro i hi
  exact kConv_integrable hloc (hc i hi) x

theorem prod_zero_decomp (v : Space) :
    ((0 : ℝ), v) = ∑ j : Fin 3, v j • ((0 : ℝ), coordinateVector j) := by
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · rw [Prod.snd_sum]
    ext i
    simp [coordinateVector, Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem mollKernelAdj : MollKernelAdj := by
  intro P ν μ hP Φ hΦ ρ x
  have hloc : LocallyIntegrable Φ volume := locInt_of_isInYr hP hΦ
  set κ : ℝ × Space → ℝ := ρ.normed volume with hκdef
  have hκ2 : ContDiff ℝ 2 κ := ρ.contDiff_normed
  have hκ1 : ContDiff ℝ 1 κ := ρ.contDiff_normed
  have hκc : HasCompactSupport κ := ρ.hasCompactSupport_normed
  have hF1 : ContDiff ℝ 1 (fderiv ℝ κ) := hκ2.fderiv_right (by norm_num)
  have hkv1 : ∀ v : ℝ × Space, ContDiff ℝ 1 (fun t => fderiv ℝ κ t v) :=
    fun v => hF1.clm_apply contDiff_const
  have hκG : GoodK κ := ⟨hκ1.continuous, hκc⟩
  have hK1 : GoodK (kerDτ κ) := gk_fderiv hκ1 hκc (1, 0)
  have hK2 : GoodK (kerDv κ x.2) := gk_fderiv hκ1 hκc (0, x.2)
  have hK3 : GoodK (kerLap κ) := by
    refine gk_sum Finset.univ
      (fun j => fun t => fderiv ℝ (fun t' => fderiv ℝ κ t' (0, coordinateVector j)) t
        (0, coordinateVector j)) ?_
    intro j _
    exact gk_fderiv (hkv1 _) (hκc.fderiv_apply ℝ _) _
  -- first derivatives of the mollification
  have hdF : ∀ w y, fderiv ℝ (mollP ρ Φ) y w = kConv (fun t => fderiv ℝ κ t w) Φ y :=
    fun w y => kConv_fderiv hloc hκ1 hκc y w
  have hdτ : dτ (mollP ρ Φ) x = kConv (kerDτ κ) Φ x := hdF (1, 0) x
  have hdy : ∀ j y, dy j (mollP ρ Φ) y
      = kConv (fun t => fderiv ℝ κ t (0, coordinateVector j)) Φ y :=
    fun j y => hdF _ y
  have hradial : radialT (mollP ρ Φ) x = kConv (kerDv κ x.2) Φ x := by
    simp only [radialT, hdy]
    simp only [← kConv_smul_left]
    rw [kConv_sum hloc Finset.univ (fun j t => x.2 j * fderiv ℝ κ t (0, coordinateVector j))
      (fun j _ => gk_mul _ (gk_fderiv hκ1 hκc _))]
    congr 1
    funext t
    rw [kerDv, prod_zero_decomp x.2, map_sum]
    simp only [map_smul, smul_eq_mul]
  -- second derivatives: the Laplacian
  have hdydy : ∀ j, dy j (dy j (mollP ρ Φ)) x
      = kConv (fun t => fderiv ℝ (fun t' => fderiv ℝ κ t' (0, coordinateVector j)) t
          (0, coordinateVector j)) Φ x := by
    intro j
    have hfun : dy j (mollP ρ Φ)
        = kConv (fun t => fderiv ℝ κ t (0, coordinateVector j)) Φ := funext fun y => hdy j y
    show fderiv ℝ (dy j (mollP ρ Φ)) x (0, coordinateVector j) = _
    rw [hfun]
    exact kConv_fderiv hloc (hkv1 _) (hκc.fderiv_apply ℝ _) x _
  have hlap : lapT (mollP ρ Φ) x = kConv (kerLap κ) Φ x := by
    show ∑ j : Fin 3, dy j (dy j (mollP ρ Φ)) x = _
    simp only [hdydy]
    rw [kConv_sum hloc Finset.univ
      (fun j => fun t => fderiv ℝ (fun t' => fderiv ℝ κ t' (0, coordinateVector j)) t
        (0, coordinateVector j))
      (fun j _ => gk_fderiv (hkv1 _) (hκc.fderiv_apply ℝ _) _)]
    rfl
  -- the left-hand side
  have hLHS : L0T ν (mollP ρ Φ) x + (μ : ℂ) • mollP ρ Φ x
      = -kConv (kerDτ κ) Φ x + (1 / 2 : ℝ) • kConv (kerDv κ x.2) Φ x
        + (3 / 2 : ℝ) • kConv κ Φ x - ν • kConv (kerLap κ) Φ x
        - (1 / 2 : ℝ) • kConv κ Φ x + (μ : ℂ) • kConv κ Φ x := by
    simp only [L0T, driftT, nuLapT, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply]
    rw [hdτ, hradial, hlap]
    rfl
  -- the right-hand side: the adjoint kernel is a linear combination of the four kernels
  have hG1 : GoodK (fun z => (μ + 1) * κ z + (-1) * kerDτ κ z) :=
    gk_add (gk_mul _ hκG) (gk_mul _ hK1)
  have hG2 : GoodK (fun z => (1 / 2) * kerDv κ x.2 z + (-ν) * kerLap κ z) :=
    gk_add (gk_mul _ hK2) (gk_mul _ hK3)
  have hRHS : ∫ z, adjKer ν μ ρ x z • Φ (x - z)
      = (μ + 1 : ℝ) • kConv κ Φ x + (-1 : ℝ) • kConv (kerDτ κ) Φ x
        + ((1 / 2 : ℝ) • kConv (kerDv κ x.2) Φ x + (-ν) • kConv (kerLap κ) Φ x) := by
    have h1 : (fun z => adjKer ν μ ρ x z) = fun z =>
        ((μ + 1) * κ z + (-1) * kerDτ κ z) + ((1 / 2) * kerDv κ x.2 z + (-ν) * kerLap κ z) := by
      funext z
      simp only [adjKer]
      ring
    have h2 : ∫ z, adjKer ν μ ρ x z • Φ (x - z) = kConv (fun z => adjKer ν μ ρ x z) Φ x := rfl
    rw [h2, h1, kConv_add hloc hG1 hG2 x, kConv_add hloc (gk_mul _ hκG) (gk_mul _ hK1) x,
      kConv_add hloc (gk_mul _ hK2) (gk_mul _ hK3) x]
    simp only [kConv_smul_left]
  rw [hLHS, hRHS]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  module

end UnforcedLeray.Short.PartIIIb.Concrete
