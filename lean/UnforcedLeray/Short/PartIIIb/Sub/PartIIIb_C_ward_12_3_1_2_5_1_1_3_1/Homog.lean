import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg

/-!
# Proof of `HomogJets` (organizer task `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/1/1/1`)

Source `the November 2 reference manuscript`,
lines 1206-1216 (ring chart of the far field). Pure calculus, following the sketch in the spec:

1. scaling: for `λ > 0`, `D^m f (λ y) ∘ (λ • id) = λ^d • D^m f y` (`m ≥ 1`), on `axisᶜ`;
2. axial translation: `D^m f (y + t e₃) = D^m f y` on `axisᶜ`;
3. norm scaling: `‖M‖ ≤ r^(d-m) ‖N‖` when `M ∘ (r • id) = r^d • N`;
4. a compact set `K = {u : u₂ = 0, ϱ u = 1}` inside `axisᶜ`, on which `‖D^m f‖` is bounded.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The scaling map `z ↦ λ • z` as a continuous linear map. -/
def hjG (lam : ℝ) : UnforcedLeray.Space →L[ℝ] UnforcedLeray.Space :=
  lam • ContinuousLinearMap.id ℝ UnforcedLeray.Space

theorem hjG_apply (lam : ℝ) (x : UnforcedLeray.Space) : hjG lam x = lam • x := by
  simp [hjG]

theorem hjLe (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast le_top

theorem hjSmulOff {lam : ℝ} (hlam : 0 < lam) {x : UnforcedLeray.Space}
    (hx : x ∉ Axi.axis) : lam • x ∉ Axi.axis := by
  intro h
  apply hx
  have h' : lam * x 0 = 0 ∧ lam * x 1 = 0 := h
  show x 0 = 0 ∧ x 1 = 0
  exact ⟨(mul_eq_zero.mp h'.1).resolve_left hlam.ne', (mul_eq_zero.mp h'.2).resolve_left hlam.ne'⟩

/-- Scaling of the iterated derivative on the open set `axisᶜ`. -/
theorem hjScale {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : UnforcedLeray.Space → F) (d : ℝ) (g : ℝ → F)
    (hf : ContDiffOn ℝ ∞ f Axi.axisᶜ)
    (lam : ℝ) (hlam : 0 < lam)
    (hsc : ∀ z : UnforcedLeray.Space, z ∉ Axi.axis → f (lam • z) = lam ^ d • f z + g lam)
    (m : ℕ) (hm : 1 ≤ m) (y : UnforcedLeray.Space) (hy : y ∉ Axi.axis) :
    (iteratedFDeriv ℝ m f (lam • y)).compContinuousLinearMap (fun _ => hjG lam) =
      lam ^ d • iteratedFDeriv ℝ m f y := by
  have hU : IsOpen (Axi.axisᶜ : Set UnforcedLeray.Space) := Axi.isOpen_compl_axis
  have hpre : IsOpen (hjG lam ⁻¹' (Axi.axisᶜ : Set UnforcedLeray.Space)) :=
    hU.preimage (hjG lam).continuous
  have hyP : y ∈ hjG lam ⁻¹' (Axi.axisᶜ : Set UnforcedLeray.Space) := by
    show hjG lam y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space)
    rw [hjG_apply]
    exact hjSmulOff hlam hy
  have hxU : hjG lam y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space) := by
    rw [hjG_apply]
    exact hjSmulOff hlam hy
  have hcomp := (hjG lam).iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn
    hpre.uniqueDiffOn hxU (hjLe m)
  rw [iteratedFDerivWithin_of_isOpen m hpre hyP, iteratedFDerivWithin_of_isOpen m hU hxU]
    at hcomp
  rw [hjG_apply] at hcomp
  have hev : (f ∘ hjG lam) =ᶠ[nhds y] (fun z => lam ^ d • f z + g lam) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    show f (hjG lam z) = lam ^ d • f z + g lam
    rw [hjG_apply]
    exact hsc z hz
  have hD := (hev.iteratedFDeriv ℝ m).eq_of_nhds
  have hm0 : m ≠ 0 := by omega
  have hA : ContDiffAt ℝ m f y := (hf.contDiffAt (hU.mem_nhds hy)).of_le (hjLe m)
  have hadd : iteratedFDeriv ℝ m (fun z => lam ^ d • f z + g lam) y =
      lam ^ d • iteratedFDeriv ℝ m f y := by
    have hsm : ContDiffAt ℝ m (fun z => lam ^ d • f z) y := hA.const_smul _
    have hfun : (fun z => lam ^ d • f z + g lam) =
        (fun z => lam ^ d • f z) + (fun _ : UnforcedLeray.Space => g lam) := rfl
    rw [hfun, iteratedFDeriv_add_apply hsm contDiffAt_const]
    have hc : iteratedFDeriv ℝ m (fun _ : UnforcedLeray.Space => g lam) y = 0 := by
      rw [iteratedFDeriv_const_of_ne hm0]
      rfl
    rw [hc, add_zero, iteratedFDeriv_const_smul_apply' hA]
  rw [← hcomp, hD, hadd]

/-- Axial invariance of the iterated derivative on `axisᶜ`. -/
theorem hjTrans {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : UnforcedLeray.Space → F)
    (hf : ContDiffOn ℝ ∞ f Axi.axisᶜ)
    (hinv : ∀ y : UnforcedLeray.Space, y ∉ Axi.axis → ∀ t : ℝ, f (y + t • Axi.e3) = f y)
    (m : ℕ) (y : UnforcedLeray.Space) (hy : y ∉ Axi.axis) (t : ℝ) :
    iteratedFDeriv ℝ m f (y + t • Axi.e3) = iteratedFDeriv ℝ m f y := by
  have hU : IsOpen (Axi.axisᶜ : Set UnforcedLeray.Space) := Axi.isOpen_compl_axis
  have hev : (fun z => f (z + t • Axi.e3)) =ᶠ[nhds y] f := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact hinv z hz t
  have h1 := (hev.iteratedFDeriv ℝ m).eq_of_nhds
  rw [← iteratedFDeriv_comp_add_right m (t • Axi.e3) y]
  exact h1

/-- Norm of a multilinear map under scaling of its arguments. -/
theorem hjNormScale {m : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M N : ContinuousMultilinearMap ℝ (fun _ : Fin m => UnforcedLeray.Space) F)
    (d r : ℝ) (hr : 0 < r)
    (h : M.compContinuousLinearMap (fun _ => hjG r) = r ^ d • N) :
    ‖M‖ ≤ r ^ (d - (m : ℝ)) * ‖N‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro w
  have hw : (fun i => r • (r⁻¹ • w i)) = w := funext fun i => by
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have key : M w = r ^ d • N (fun i => r⁻¹ • w i) := by
    have h1 := congrArg
      (fun P : ContinuousMultilinearMap ℝ (fun _ : Fin m => UnforcedLeray.Space) F =>
        P (fun i => r⁻¹ • w i)) h
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hjG_apply,
      ContinuousMultilinearMap.smul_apply] at h1
    rw [hw] at h1
    exact h1
  have hprod : ∏ i, ‖r⁻¹ • w i‖ = (r⁻¹) ^ m * ∏ i, ‖w i‖ := by
    simp [norm_smul, Finset.prod_mul_distrib, Finset.prod_const, norm_inv, abs_of_pos hr]
  have hN := N.le_opNorm (fun i => r⁻¹ • w i)
  rw [key, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
  calc r ^ d * ‖N (fun i => r⁻¹ • w i)‖
      ≤ r ^ d * (‖N‖ * ∏ i, ‖r⁻¹ • w i‖) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = r ^ (d - (m : ℝ)) * ‖N‖ * ∏ i, ‖w i‖ := by
        rw [hprod, Real.rpow_sub hr, Real.rpow_natCast]
        ring

/-- The unit circle of the plane `u₂ = 0` is compact and misses the axis. -/
theorem hjCompact :
    IsCompact (({u : UnforcedLeray.Space | u 2 = 0}) ∩ {u : UnforcedLeray.Space | Axi.ϱ u = 1}) := by
  have c2 : Continuous fun u : UnforcedLeray.Space => u 2 := by fun_prop
  have c0 : Continuous fun u : UnforcedLeray.Space => u 0 := by fun_prop
  have c1 : Continuous fun u : UnforcedLeray.Space => u 1 := by fun_prop
  have cϱ : Continuous fun u : UnforcedLeray.Space => Axi.ϱ u :=
    ((c0.pow 2).add (c1.pow 2)).sqrt
  have hcl : IsClosed (({u : UnforcedLeray.Space | u 2 = 0}) ∩
      {u : UnforcedLeray.Space | Axi.ϱ u = 1}) :=
    (isClosed_eq c2 continuous_const).inter (isClosed_eq cϱ continuous_const)
  apply IsCompact.of_isClosed_subset (isCompact_sphere (0 : UnforcedLeray.Space) 1) hcl
  intro u hu
  obtain ⟨hu2, hϱu⟩ := hu
  have hu2' : u 2 = 0 := hu2
  have hϱu' : Axi.ϱ u = 1 := hϱu
  have hsq : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have h := hϱu'
    unfold Axi.ϱ at h
    exact (Real.sqrt_eq_one).mp h
  rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs, hu2']
  rw [show u 0 ^ 2 + u 1 ^ 2 + 0 ^ 2 = 1 by linarith [hsq]]
  simp

theorem hjKU : (({u : UnforcedLeray.Space | u 2 = 0}) ∩
    {u : UnforcedLeray.Space | Axi.ϱ u = 1}) ⊆ Axi.axisᶜ := by
  intro u hu
  obtain ⟨_, hϱu⟩ := hu
  have hϱu' : Axi.ϱ u = 1 := hϱu
  intro hax
  have h0 : u 0 = 0 := hax.1
  have h1 : u 1 = 0 := hax.2
  have h2 : Axi.ϱ u = 0 := by
    unfold Axi.ϱ
    rw [h0, h1]
    simp
  rw [h2] at hϱu'
  norm_num at hϱu'

theorem homogJets : HomogJets := by
  unfold HomogJets
  intro F _ _ f d g hf hinv hsc m hm
  have hU : IsOpen (Axi.axisᶜ : Set UnforcedLeray.Space) := Axi.isOpen_compl_axis
  have hKc := hjCompact
  have hKU := hjKU
  have hcont : ContinuousOn (fun u => ‖iteratedFDeriv ℝ m f u‖)
      (({u : UnforcedLeray.Space | u 2 = 0}) ∩ {u : UnforcedLeray.Space | Axi.ϱ u = 1}) := by
    have h1 : ContinuousOn (iteratedFDeriv ℝ m f) Axi.axisᶜ :=
      (hf.continuousOn_iteratedFDerivWithin (hjLe m) hU.uniqueDiffOn).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen m hU hx).symm)
    exact h1.norm.mono hKU
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro y hy
  have hr : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hhor : Axi.hor y ∉ Axi.axis := by
    intro h
    apply hy
    show y 0 = 0 ∧ y 1 = 0
    have h0 : Axi.hor y 0 = 0 := h.1
    have h1 : Axi.hor y 1 = 0 := h.2
    rw [Axi.hor_apply_zero] at h0
    rw [Axi.hor_apply_one] at h1
    exact ⟨h0, h1⟩
  have hϱh : Axi.ϱ (Axi.hor y) = Axi.ϱ y := by
    simp only [Axi.ϱ, Axi.hor_apply_zero, Axi.hor_apply_one]
  obtain ⟨u, hu_def⟩ : ∃ u : UnforcedLeray.Space, u = (Axi.ϱ y)⁻¹ • Axi.hor y := ⟨_, rfl⟩
  have hhor_eq : Axi.hor y = Axi.ϱ y • u := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hu : u ∈ (({u : UnforcedLeray.Space | u 2 = 0}) ∩
      {u : UnforcedLeray.Space | Axi.ϱ u = 1}) := by
    refine ⟨?_, ?_⟩
    · show u 2 = 0
      rw [hu_def]
      simp [Axi.hor_apply_two]
    · show Axi.ϱ u = 1
      rw [hu_def, Axi.ϱ_smul, hϱh, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  have hBu : ‖iteratedFDeriv ℝ m f u‖ ≤ B := by
    have := hB u hu
    simpa using this
  have hS := hjScale f d g hf (Axi.ϱ y) hr (hsc (Axi.ϱ y) hr) m hm u (hKU hu)
  rw [← hhor_eq] at hS
  have hNorm := hjNormScale (iteratedFDeriv ℝ m f (Axi.hor y)) (iteratedFDeriv ℝ m f u) d
    (Axi.ϱ y) hr hS
  have hyy : Axi.hor y + (y 2) • Axi.e3 = y := by
    rw [Axi.hor_eq, sub_add_cancel]
  have e1 : iteratedFDeriv ℝ m f y = iteratedFDeriv ℝ m f (Axi.hor y) := by
    have := hjTrans f hf hinv m (Axi.hor y) hhor (y 2)
    rw [hyy] at this
    exact this
  calc ‖iteratedFDeriv ℝ m f y‖ = ‖iteratedFDeriv ℝ m f (Axi.hor y)‖ := by rw [e1]
    _ ≤ Axi.ϱ y ^ (d - (m : ℝ)) * ‖iteratedFDeriv ℝ m f u‖ := hNorm
    _ ≤ Axi.ϱ y ^ (d - (m : ℝ)) * B :=
        mul_le_mul_of_nonneg_left hBu (by positivity)
    _ ≤ Axi.ϱ y ^ (d - (m : ℝ)) * max B 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    _ = max B 0 * Axi.ϱ y ^ (d - (m : ℝ)) := mul_comm _ _

end UnforcedLeray.Short.PartIIIb.Concrete
