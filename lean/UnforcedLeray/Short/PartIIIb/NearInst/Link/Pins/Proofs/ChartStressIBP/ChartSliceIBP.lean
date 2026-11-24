import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartStressIBP.BandSliceSmooth
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartStressIBP.SpaceIBPPairing

/-!
# `ChartSliceIBP` (task `PartIII-b:C/near/pins/4/2/3`)

Source `the November 2 reference manuscript` 1660-1665 (`⟨div T, Φ⟩ = -⟨T, ∇Φ⟩`).

For fixed `τ`, the slice of `Φ·F` integrates to `-∫ Σ_{ij} T_ij ∂_jΦ_i`:
* off the axis `{hRad = 0}` (a Lebesgue null set) `F_i = Σ_j ∂_j T_ij` by hypothesis;
* each `T_ij(τ,·)` is `C¹` with compact support (`bandSliceSmooth`), and the joint derivative in
  `(τ,y)` exists off the axis, so the slice derivative agrees with `dy`;
* `spaceIBPPairing` gives the integration by parts for each `(i,j)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory Set Filter Topology
open UnforcedLeray.PhaseSpace UnforcedLeray.Short.PartIIIb.Concrete

/-- The component `v ↦ v i` of `ℂ³` as a real-linear map to `ℂ`. -/
def chartIBP_compL (i : Fin 3) : CVec3 →L[ℝ] ℂ :=
  (ContinuousLinearMap.restrictScalars ℝ (EuclideanSpace.proj (𝕜 := ℂ) i : CVec3 →L[ℂ] ℂ))

theorem chartIBP_compL_apply (i : Fin 3) (v : CVec3) : chartIBP_compL i v = v i := rfl

/-- The axis-complement submodule `{y | y 0 = 0}` (a proper submodule, hence Lebesgue null). -/
def chartIBP_axis : Submodule ℝ Space :=
  LinearMap.ker (ContinuousLinearMap.toLinearMap (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)))

theorem chartIBP_axis_ne_top : chartIBP_axis ≠ ⊤ := by
  intro h
  have hmem : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space) ∈ chartIBP_axis := by
    rw [h]; exact Submodule.mem_top
  simp [chartIBP_axis] at hmem

theorem chartIBP_axis_null : ∀ᵐ y : Space ∂(volume : Measure Space), 0 < hRad y := by
  rw [ae_iff]
  have hsub : {y : Space | ¬ 0 < hRad y} ⊆ (chartIBP_axis : Set Space) := by
    intro y hy
    have hy' : hRad y ≤ 0 := not_lt.mp hy
    have h0 : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) = 0 := le_antisymm hy' (Real.sqrt_nonneg _)
    have hsq : y 0 ^ 2 + y 1 ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp h0
    have hsq0 : y 0 ^ 2 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have hy0 : y 0 = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq0
    rw [SetLike.mem_coe]
    simp [chartIBP_axis, hy0]
  exact measure_mono_null hsub (Measure.addHaar_submodule (volume : Measure Space) chartIBP_axis
    chartIBP_axis_ne_top)

/-- Joint `C¹` regularity of the raw chart point off the axis. -/
theorem chartIBP_ptOf_joint {R : ℝ} (hR : 0 < R) {τ : ℝ} {y : Space} (hy : 0 < hRad y) :
    ContDiffAt ℝ 1 (fun p : ℝ × Space => ptOf R p.1 p.2) (τ, y) := by
  have hRC : ContDiffAt ℝ 1 (fun p : ℝ × Space => hRad p.2) (τ, y) :=
    ContDiffAt.comp (g := fun z : Space => hRad z) (f := fun p : ℝ × Space => p.2) (τ, y)
      (hRad_contDiffAt_pos hy) contDiffAt_snd
  have hs : ContDiffAt ℝ 1 (fun p : ℝ × Space => R ^ 2 / hRad p.2 ^ 2) (τ, y) :=
    contDiffAt_const.div (hRC.pow 2) (pow_ne_zero 2 hy.ne')
  have hQ : ContDiffAt ℝ 1
      (fun p : ℝ × Space => R * Real.log (hRad p.2 / R) + R * p.1 / 2) (τ, y) :=
    (contDiffAt_const.mul ((hRC.div_const R).log (div_ne_zero hy.ne' hR.ne'))).add
      ((contDiffAt_const.mul contDiffAt_fst).div_const 2)
  have hy2 : ContDiff ℝ 1 (fun z : Space => z 2) := (contDiff_piLp (p := 2)).mp contDiff_id 2
  have hη : ContDiffAt ℝ 1 (fun p : ℝ × Space => R * p.2 2 / hRad p.2) (τ, y) :=
    (contDiffAt_const.mul (hy2.contDiffAt.comp (τ, y) contDiffAt_snd)).div hRC hy.ne'
  exact hs.prodMk (hQ.prodMk hη)

theorem chartIBP_sandwich {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C N : E → Matrix (Fin 3) (Fin 3) ℝ} {s : E → ℝ} {x : E} (i j : Fin 3)
    (hC : ∀ a b : Fin 3, ContDiffAt ℝ 1 (fun z => C z a b) x)
    (hN : ∀ a b : Fin 3, ContDiffAt ℝ 1 (fun z => N z a b) x)
    (hs : ContDiffAt ℝ 1 s x) :
    ContDiffAt ℝ 1 (fun z => (C z * ((s z) • N z) * (C z).transpose) i j) x := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  refine ContDiffAt.sum fun k _ => ?_
  refine ContDiffAt.mul ?_ (hC j k)
  refine ContDiffAt.sum fun l _ => ?_
  exact (hC i l).mul (hs.mul (hN l k))

/-- Joint `C¹` regularity of the lifted stress components at `(τ,y)`, off the axis. -/
theorem chartIBP_strPhys_joint {R c : ℝ} (hR : 0 < R) (M : Chart → Ten3)
    (hM : UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)))
    {τ : ℝ} {y : Space} (hy : 0 < hRad y) (i j : Fin 3) :
    ContDiffAt ℝ 1 (fun p : ℝ × Space => strPhys R c M p i j) (τ, y) := by
  have hfun : (fun p : ℝ × Space => strPhys R c M p i j) =
      fun p : ℝ × Space => (cylFrame p.2 * ((R ^ 2 / hRad p.2 ^ 2) •
        nsSym (M (ptOf R p.1 p.2))) * (cylFrame p.2).transpose) i j := by
    funext ⟨τ', y'⟩
    show strPhys R c M (τ', y') i j = _
    rw [strPhys_eq_sandwich R c τ' M hM y']
  rw [hfun]
  have hC : ∀ a b : Fin 3,
      ContDiffAt ℝ 1 (fun p : ℝ × Space => cylFrame p.2 a b) (τ, y) :=
    fun a b => (cylFrame_entry_contDiffAt hy a b).comp (τ, y) contDiffAt_snd
  have hN : ∀ a b : Fin 3,
      ContDiffAt ℝ 1 (fun p : ℝ × Space => nsSym (M (ptOf R p.1 p.2)) a b) (τ, y) :=
    fun a b => (nsSym_entry_contDiff M hM a b).comp_contDiffAt (τ, y)
      (chartIBP_ptOf_joint hR hy)
  have hs : ContDiffAt ℝ 1 (fun p : ℝ × Space => R ^ 2 / hRad p.2 ^ 2) (τ, y) :=
    contDiffAt_const.div (((ContDiffAt.comp (g := fun z : Space => hRad z)
      (f := fun p : ℝ × Space => p.2) (τ, y) (hRad_contDiffAt_pos hy) contDiffAt_snd)).pow 2)
      (pow_ne_zero 2 hy.ne')
  exact chartIBP_sandwich (C := fun p : ℝ × Space => cylFrame p.2)
    (N := fun p : ℝ × Space => nsSym (M (ptOf R p.1 p.2)))
    (s := fun p : ℝ × Space => R ^ 2 / hRad p.2 ^ 2) i j hC hN hs

/-- Slice derivative in the spatial direction equals the phase-space `dy`. -/
theorem chartIBP_fderiv_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ × Space → F} {τ : ℝ} {y : Space}
    (hG : DifferentiableAt ℝ G (τ, y)) (j : Fin 3) :
    fderiv ℝ (fun z : Space => G (τ, z)) y (coordinateVector j) =
      UnforcedLeray.PhaseSpace.dy j G (τ, y) := by
  have h := hG.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) τ y)
  have e : (fun z : Space => G (τ, z)) = G ∘ (fun z : Space => (τ, z)) := rfl
  rw [e, h.fderiv]
  simp [UnforcedLeray.PhaseSpace.dy]

theorem chartSliceIBP : ChartSliceIBP := by
  intro c ε hc hε M hM F hF Φ hΦ τ
  have hR : 0 < ε⁻¹ := inv_pos.mpr hε
  have hB : ∀ i j : Fin 3,
      ContDiff ℝ 1 (fun y : Space => strPhys ε⁻¹ c M (τ, y) i j) ∧
      HasCompactSupport (fun y : Space => strPhys ε⁻¹ c M (τ, y) i j) ∧
      (∀ y, strPhys ε⁻¹ c M (τ, y) i j ≠ 0 → 0 < hRad y) :=
    fun i j => bandSliceSmooth c ε hc hε M hM τ i j
  have hΦd : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hΦC : ContDiff ℝ 1 (fun y : Space => Φ (τ, y)) :=
    (hΦ.smooth.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  -- component derivatives of Φ
  have hgC : ∀ i : Fin 3, ContDiff ℝ 1 (fun y : Space => Φ (τ, y) i) :=
    fun i => (chartIBP_compL i).contDiff.comp hΦC
  have hgd : ∀ (i j : Fin 3) (y : Space),
      fderiv ℝ (fun z : Space => Φ (τ, z) i) y (coordinateVector j) =
        UnforcedLeray.PhaseSpace.dy j Φ (τ, y) i := by
    intro i j y
    have hpair : DifferentiableAt ℝ (fun z : Space => ((τ, z) : ℝ × Space)) y :=
      (differentiableAt_const τ).prodMk differentiableAt_id
    have hsl : DifferentiableAt ℝ (fun z : Space => Φ (τ, z)) y :=
      (hΦd (τ, y)).comp y hpair
    have h1 : HasFDerivAt (fun z : Space => Φ (τ, z) i)
        ((chartIBP_compL i).comp (fderiv ℝ (fun z : Space => Φ (τ, z)) y)) y :=
      (chartIBP_compL i).hasFDerivAt.comp y hsl.hasFDerivAt
    rw [h1.fderiv, ContinuousLinearMap.comp_apply,
      chartIBP_fderiv_slice (hΦd (τ, y)) j]
    rfl
  -- continuity of the phase derivative components
  have hdyC : ∀ (j i : Fin 3), Continuous (fun y : Space => UnforcedLeray.PhaseSpace.dy j Φ (τ, y) i) := by
    intro j i
    have hc1 : Continuous (fun y : Space => UnforcedLeray.PhaseSpace.dy j Φ (τ, y)) :=
      (hΦ.dy j).smooth.continuous.comp (continuous_const.prodMk continuous_id)
    exact (chartIBP_compL i).continuous.comp hc1
  -- joint differentiability off the axis, and the slice derivative identity
  have hdiff : ∀ i j : Fin 3, ∀ y : Space, 0 < hRad y →
      UnforcedLeray.PhaseSpace.dy j (fun x : ℝ × Space => ((strPhys ε⁻¹ c M x i j : ℝ) : ℂ))
          (τ, y) =
        ((fderiv ℝ (fun z : Space => strPhys ε⁻¹ c M (τ, z) i j) y (coordinateVector j) : ℝ) : ℂ) := by
    intro i j y hy
    have hG : DifferentiableAt ℝ (fun x : ℝ × Space => ((strPhys ε⁻¹ c M x i j : ℝ) : ℂ)) (τ, y) :=
      Complex.ofRealCLM.differentiableAt.comp (τ, y)
        ((chartIBP_strPhys_joint hR M hM hy i j).differentiableAt (by norm_num))
    rw [← chartIBP_fderiv_slice hG j]
    exact ofRealComp_fderiv_spaceIBP (hB i j).1 y _
  -- the integration by parts for each component pair
  have hIBP : ∀ i j : Fin 3,
      ∫ y : Space, Φ (τ, y) i *
          ((fderiv ℝ (fun z : Space => strPhys ε⁻¹ c M (τ, z) i j) y (coordinateVector j) : ℝ) : ℂ) =
        -∫ y : Space, ((strPhys ε⁻¹ c M (τ, y) i j : ℝ) : ℂ) *
          UnforcedLeray.PhaseSpace.dy j Φ (τ, y) i := by
    intro i j
    have key := spaceIBPPairing (fun y => strPhys ε⁻¹ c M (τ, y) i j)
      (fun y => Φ (τ, y) i) (hB i j).1 (hB i j).2.1 (hgC i) j
    simp only [hgd] at key
    have e2 : ∫ y : Space, UnforcedLeray.PhaseSpace.dy j Φ (τ, y) i *
        ((strPhys ε⁻¹ c M (τ, y) i j : ℝ) : ℂ) =
        ∫ y : Space, ((strPhys ε⁻¹ c M (τ, y) i j : ℝ) : ℂ) *
          UnforcedLeray.PhaseSpace.dy j Φ (τ, y) i := by
      congr 1
      funext y
      ring
    rw [key, e2]
  -- integrability
  have hAint : ∀ i j : Fin 3, MeasureTheory.Integrable
      (fun y : Space => Φ (τ, y) i *
        ((fderiv ℝ (fun z : Space => strPhys ε⁻¹ c M (τ, z) i j) y (coordinateVector j) : ℝ) : ℂ)) := by
    intro i j
    have hcd : Continuous (fun y : Space =>
        ((fderiv ℝ (fun z : Space => strPhys ε⁻¹ c M (τ, z) i j) y (coordinateVector j) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        (((hB i j).1.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    have hfc : HasCompactSupport (fun z : Space => strPhys ε⁻¹ c M (τ, z) i j) := (hB i j).2.1
    have hDc : HasCompactSupport (fun y : Space =>
        ((fderiv ℝ (fun z : Space => strPhys ε⁻¹ c M (τ, z) i j) y (coordinateVector j) : ℝ) : ℂ)) :=
      (hfc.fderiv (𝕜 := ℝ)).comp_left
        (g := fun L : Space →L[ℝ] ℝ => ((L (coordinateVector j) : ℝ) : ℂ)) (by simp)
    exact Continuous.integrable_of_hasCompactSupport ((hgC i).continuous.mul hcd) hDc.mul_left
  have hBint : ∀ i j : Fin 3, MeasureTheory.Integrable
      (fun y : Space => ((strPhys ε⁻¹ c M (τ, y) i j : ℝ) : ℂ) *
        UnforcedLeray.PhaseSpace.dy j Φ (τ, y) i) := by
    intro i j
    have hcs : Continuous (fun y : Space => ((strPhys ε⁻¹ c M (τ, y) i j : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hB i j).1.continuous
    have hGc : HasCompactSupport (fun y : Space => ((strPhys ε⁻¹ c M (τ, y) i j : ℝ) : ℂ)) :=
      HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (hB i j).2.1 (by simp)
    exact Continuous.integrable_of_hasCompactSupport (hcs.mul (hdyC j i)) hGc.mul_right
  have hsumA : ∫ y : Space, ∑ i : Fin 3, ∑ j : Fin 3, Φ (τ, y) i *
      ((fderiv ℝ (fun z : Space => strPhys ε⁻¹ c M (τ, z) i j) y (coordinateVector j) : ℝ) : ℂ)
      = ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Space, Φ (τ, y) i *
      ((fderiv ℝ (fun z : Space => strPhys ε⁻¹ c M (τ, z) i j) y (coordinateVector j) : ℝ) : ℂ) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hAint i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hAint i j)]
  have hsumB : ∫ y : Space, ∑ i : Fin 3, ∑ j : Fin 3,
      ((strPhys ε⁻¹ c M (τ, y) i j : ℝ) : ℂ) * UnforcedLeray.PhaseSpace.dy j Φ (τ, y) i
      = ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Space,
      ((strPhys ε⁻¹ c M (τ, y) i j : ℝ) : ℂ) * UnforcedLeray.PhaseSpace.dy j Φ (τ, y) i := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hBint i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hBint i j)]
  -- the a.e. identity off the axis
  have hae : ∀ᵐ y : Space ∂(volume : Measure Space),
      dotL (Φ (τ, y)) (F (τ, y)) = ∑ i : Fin 3, ∑ j : Fin 3, Φ (τ, y) i *
        ((fderiv ℝ (fun z : Space => strPhys ε⁻¹ c M (τ, z) i j) y (coordinateVector j) : ℝ) : ℂ) := by
    filter_upwards [chartIBP_axis_null] with y hy
    rw [dotL_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hF τ y hy i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdiff i j y hy]
  calc ∫ y : Space, dotL (Φ (τ, y)) (F (τ, y))
      = ∫ y : Space, ∑ i : Fin 3, ∑ j : Fin 3, Φ (τ, y) i *
        ((fderiv ℝ (fun z : Space => strPhys ε⁻¹ c M (τ, z) i j) y (coordinateVector j) : ℝ) : ℂ) :=
        integral_congr_ae hae
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Space, Φ (τ, y) i *
        ((fderiv ℝ (fun z : Space => strPhys ε⁻¹ c M (τ, z) i j) y (coordinateVector j) : ℝ) : ℂ) :=
        hsumA
    _ = ∑ i : Fin 3, ∑ j : Fin 3, -∫ y : Space, ((strPhys ε⁻¹ c M (τ, y) i j : ℝ) : ℂ) *
        UnforcedLeray.PhaseSpace.dy j Φ (τ, y) i :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hIBP i j
    _ = -∫ y : Space, ∑ i : Fin 3, ∑ j : Fin 3,
        ((strPhys ε⁻¹ c M (τ, y) i j : ℝ) : ℂ) * UnforcedLeray.PhaseSpace.dy j Φ (τ, y) i := by
        rw [hsumB]
        simp [Finset.sum_neg_distrib]

end UnforcedLeray.Short.PartIIIb.NearInst
