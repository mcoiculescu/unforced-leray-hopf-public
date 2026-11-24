import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs

/-!
# Pointwise calculus for the additivity of the Ward fields (source 4171-4174, 4271-4280)

Helpers for `Ward/YHAdd.lean` and `Ward/EAdd.lean`.  If `C = A + B` pointwise on an open set `s`
and `A, B` are `C³` there, then at a point `y ∈ s` the first and second partial derivatives, the
Laplacian, the chart-free residual pieces and `fderiv` add.  Nothing here uses the Ward fields
specifically; the time derivative is handled by `physDmu_sum_pt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.WardCalc

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

variable {s : Set Space}

/-- Locality of `physPd` at a point. -/
theorem physPd_congr_pt {f₁ f₂ : Space → Space} {y : Space} (h : f₁ =ᶠ[𝓝 y] f₂) (j : Fin 3) :
    physPd f₁ j y = physPd f₂ j y := by
  unfold physPd
  rw [h.fderiv_eq]

theorem fderiv_sum_of_eventuallyEq {A B C : Space → Space} {y : Space}
    (hA : DifferentiableAt ℝ A y) (hB : DifferentiableAt ℝ B y)
    (hC : C =ᶠ[𝓝 y] fun y' => A y' + B y') :
    fderiv ℝ C y = fderiv ℝ A y + fderiv ℝ B y :=
  hC.fderiv_eq.trans (fderiv_add hA hB)

theorem physPd_sum_of_eventuallyEq {A B C : Space → Space} {y : Space}
    (hA : DifferentiableAt ℝ A y) (hB : DifferentiableAt ℝ B y)
    (hC : C =ᶠ[𝓝 y] fun y' => A y' + B y') (j : Fin 3) :
    physPd C j y = physPd A j y + physPd B j y := by
  unfold physPd
  rw [fderiv_sum_of_eventuallyEq hA hB hC]
  rfl

theorem diffAt_of_contDiffOn {A : Space → Space} (hs : IsOpen s) (hA : ContDiffOn ℝ 3 A s)
    {y : Space} (hy : y ∈ s) : DifferentiableAt ℝ A y :=
  (hA.contDiffAt (hs.mem_nhds hy)).differentiableAt (by norm_num)

theorem ev_of_pt {A B C : Space → Space} (hs : IsOpen s) {y : Space} (hy : y ∈ s)
    (hC : ∀ y' ∈ s, C y' = A y' + B y') : C =ᶠ[𝓝 y] fun y' => A y' + B y' :=
  Filter.eventually_of_mem (hs.mem_nhds hy) hC

/-- `∂_j A` of a `C³` field on an open set is `C²`. -/
theorem contDiffOn_physPd {A : Space → Space} (hs : IsOpen s) (hA : ContDiffOn ℝ 3 A s)
    (j : Fin 3) : ContDiffOn ℝ 2 (fun y => physPd A j y) s := by
  unfold physPd
  exact (hA.fderiv_of_isOpen hs (m := 2) (by norm_num)).clm_apply contDiffOn_const

/-- `∂_j∂_l A` of a `C³` field on an open set is `C¹`. -/
theorem contDiffOn_physPd2 {A : Space → Space} (hs : IsOpen s) (hA : ContDiffOn ℝ 3 A s)
    (j l : Fin 3) : ContDiffOn ℝ 1 (fun y => physPd2 A j l y) s := by
  unfold physPd2
  exact ((contDiffOn_physPd hs hA l).fderiv_of_isOpen hs (m := 1) (by norm_num)).clm_apply
    contDiffOn_const

theorem differentiableAt_physPd {A : Space → Space} (hs : IsOpen s) (hA : ContDiffOn ℝ 3 A s)
    {y : Space} (hy : y ∈ s) (j : Fin 3) : DifferentiableAt ℝ (fun y' => physPd A j y') y :=
  ((contDiffOn_physPd hs hA j).differentiableOn (by norm_num)).differentiableAt (hs.mem_nhds hy)

theorem differentiableAt_physPd2 {A : Space → Space} (hs : IsOpen s) (hA : ContDiffOn ℝ 3 A s)
    {y : Space} (hy : y ∈ s) (j l : Fin 3) :
    DifferentiableAt ℝ (fun y' => physPd2 A j l y') y :=
  ((contDiffOn_physPd2 hs hA j l).differentiableOn (by norm_num)).differentiableAt
    (hs.mem_nhds hy)

/-! ## Pointwise sums on an open set -/

theorem fderiv_sum_pt {A B C : Space → Space} (hs : IsOpen s) (hA : ContDiffOn ℝ 3 A s)
    (hB : ContDiffOn ℝ 3 B s) (hC : ∀ y' ∈ s, C y' = A y' + B y') {y : Space} (hy : y ∈ s) :
    fderiv ℝ C y = fderiv ℝ A y + fderiv ℝ B y :=
  fderiv_sum_of_eventuallyEq (diffAt_of_contDiffOn hs hA hy) (diffAt_of_contDiffOn hs hB hy)
    (ev_of_pt hs hy hC)

theorem physPd_sum_pt {A B C : Space → Space} (hs : IsOpen s) (hA : ContDiffOn ℝ 3 A s)
    (hB : ContDiffOn ℝ 3 B s) (hC : ∀ y' ∈ s, C y' = A y' + B y') {y : Space} (hy : y ∈ s)
    (j : Fin 3) : physPd C j y = physPd A j y + physPd B j y :=
  physPd_sum_of_eventuallyEq (diffAt_of_contDiffOn hs hA hy) (diffAt_of_contDiffOn hs hB hy)
    (ev_of_pt hs hy hC) j

theorem physPd2_sum_pt {A B C : Space → Space} (hs : IsOpen s) (hA : ContDiffOn ℝ 3 A s)
    (hB : ContDiffOn ℝ 3 B s) (hC : ∀ y' ∈ s, C y' = A y' + B y') {y : Space} (hy : y ∈ s)
    (j l : Fin 3) : physPd2 C j l y = physPd2 A j l y + physPd2 B j l y := by
  unfold physPd2
  have hEq : (fun y' => physPd C l y') =ᶠ[𝓝 y]
      fun y' => physPd A l y' + physPd B l y' := by
    filter_upwards [hs.mem_nhds hy] with y' hy'
    exact physPd_sum_pt hs hA hB hC hy' l
  rw [physPd_congr_pt hEq j]
  exact physPd_sum_of_eventuallyEq (differentiableAt_physPd hs hA hy l)
    (differentiableAt_physPd hs hB hy l) EventuallyEq.rfl j

theorem physLap_sum_pt {A B C : Space → Space} (hs : IsOpen s) (hA : ContDiffOn ℝ 3 A s)
    (hB : ContDiffOn ℝ 3 B s) (hC : ∀ y' ∈ s, C y' = A y' + B y') {y : Space} (hy : y ∈ s) :
    physLap C y = physLap A y + physLap B y := by
  unfold physLap
  simp only [physPd2_sum_pt hs hA hB hC hy, Finset.sum_add_distrib]

/-- The displacement is a sum off the axis and `Y`-type fields add at `y` (time derivative
included).  `X1, X2, X3` are displacement families; `hX3` is the pointwise sum at every time. -/
theorem physDmu_sum_pt {X1 X2 X3 : ℝ → Space → Space} {ν μ' τ : ℝ} (hs : IsOpen s)
    (hA : ContDiffOn ℝ 3 (X1 τ) s) (hB : ContDiffOn ℝ 3 (X2 τ) s)
    (hX3 : ∀ t, ∀ y' ∈ s, X3 t y' = X1 t y' + X2 t y') {y : Space} (hy : y ∈ s)
    (ht1 : DifferentiableAt ℝ (fun t => X1 t y) τ)
    (ht2 : DifferentiableAt ℝ (fun t => X2 t y) τ) :
    physDmu ν μ' X3 τ y = physDmu ν μ' X1 τ y + physDmu ν μ' X2 τ y := by
  have ht : (fun t => X3 t y) = fun t => X1 t y + X2 t y := funext fun t => hX3 t y hy
  have hd : deriv (fun t => X3 t y) τ = deriv (fun t => X1 t y) τ + deriv (fun t => X2 t y) τ := by
    rw [ht]
    exact deriv_add ht1 ht2
  unfold physDmu
  rw [hd, fderiv_sum_pt hs hA hB (hX3 τ) hy,
    physLap_sum_pt hs hA hB (hX3 τ) hy, hX3 τ y hy]
  simp only [add_apply, smul_add]
  abel

/-- `physDmu` of a `C³` displacement is differentiable in space at `y ∈ s`, given that the
time-derivative term is differentiable on `s`. -/
theorem physDmu_differentiableAt {X : ℝ → Space → Space} {ν μ' τ : ℝ} (hs : IsOpen s)
    (hX : ContDiffOn ℝ 3 (X τ) s)
    (hder : DifferentiableOn ℝ (fun y' => deriv (fun t => X t y') τ) s)
    {y : Space} (hy : y ∈ s) :
    DifferentiableAt ℝ (fun y' => physDmu ν μ' X τ y') y := by
  have ha : DifferentiableAt ℝ (fun y' => deriv (fun t => X t y') τ) y :=
    hder.differentiableAt (hs.mem_nhds hy)
  have hF : ContDiffOn ℝ 2 (fun y' => fderiv ℝ (X τ) y') s :=
    hX.fderiv_of_isOpen hs (m := 2) (by norm_num)
  have h2 : ContDiffOn ℝ 2 (fun y' => fderiv ℝ (X τ) y' (id y')) s :=
    hF.clm_apply contDiffOn_id
  have hb : DifferentiableAt ℝ (fun y' => fderiv ℝ (X τ) y' y') y :=
    (h2.differentiableOn (by norm_num)).differentiableAt (hs.mem_nhds hy)
  have hc : DifferentiableAt ℝ (fun y' => physLap (X τ) y') y := by
    unfold physLap
    exact DifferentiableAt.fun_sum fun j _ => differentiableAt_physPd2 hs hX hy j j
  have hd : DifferentiableAt ℝ (fun y' => X τ y') y := diffAt_of_contDiffOn hs hX hy
  unfold physDmu
  exact ((ha.sub (hb.const_smul (1 / 2 : ℝ))).sub (hc.const_smul ν)).add
    (hd.const_smul (μ' - 1 / 2))

/-! ## The residual pieces -/

theorem physCdiff_sum_pt {A B C : Space → Space} (U : Space → Space) (hs : IsOpen s)
    (hA : ContDiffOn ℝ 3 A s) (hB : ContDiffOn ℝ 3 B s) (hC : ∀ y' ∈ s, C y' = A y' + B y')
    {y : Space} (hy : y ∈ s) :
    physCdiff U C y = physCdiff U A y + physCdiff U B y := by
  unfold physCdiff
  simp only [physPd_sum_pt hs hA hB hC hy, physPd2_sum_pt hs hA hB hC hy, PiLp.add_apply,
    smul_add, add_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

theorem physUUD2_sum_pt {A B C : Space → Space} (U : Space → Space) (hs : IsOpen s)
    (hA : ContDiffOn ℝ 3 A s) (hB : ContDiffOn ℝ 3 B s) (hC : ∀ y' ∈ s, C y' = A y' + B y')
    {y : Space} (hy : y ∈ s) :
    physUUD2 U C y = physUUD2 U A y + physUUD2 U B y := by
  unfold physUUD2
  simp only [physPd2_sum_pt hs hA hB hC hy, smul_add, Finset.sum_add_distrib]

theorem physDXp_sum_pt {A B C : Space → Space} (q : Space → ℝ) (hs : IsOpen s)
    (hA : ContDiffOn ℝ 3 A s) (hB : ContDiffOn ℝ 3 B s) (hC : ∀ y' ∈ s, C y' = A y' + B y')
    {y : Space} (hy : y ∈ s) :
    physDXp C q y = physDXp A q y + physDXp B q y := by
  unfold physDXp
  ext i
  simp only [physPd_sum_pt hs hA hB hC hy, PiLp.add_apply, add_mul,
    Finset.sum_add_distrib]
  abel

end UnforcedLeray.Short.PartIIIb.Concrete.WardCalc
