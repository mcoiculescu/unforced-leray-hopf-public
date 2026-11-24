import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_org2_1_org

/-!
# Organizer task `PartIII-b:C/rep/8/2/pres/4/org2/1/3`: `coefChgSumLe`

Source `the November 2 reference manuscript` 5287-5289 (coefficient change
`|U - U_raw| + |D(U - U_raw)| + |D²(U - U_raw)|`), 2389-2390. Pure calculus: if `U = W + Σ aᵢEᵢ`
and `W`, `Eᵢ` are `C²` on an open set `s` containing `y`, then the density `coefChgDens U W y`
is at most `Σᵢ |aᵢ| Σ_{j ≤ 2} ‖Dʲ Eᵢ(y)‖`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Norm of a finite signed combination, termwise. -/
private theorem cs_norm_sum_le {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : Fin 2 → ℝ) (v : Fin 2 → F) : ‖∑ i, c i • v i‖ ≤ ∑ i, |c i| * ‖v i‖ := by
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [norm_smul, Real.norm_eq_abs]

theorem coefChgSumLe : CoefChgSumLe := by
  intro U W E a s y hs hy hW hE hU
  -- differentiability on the open set `s`
  have hW1 : ContDiffOn ℝ 1 (fun x => fderiv ℝ W x) s := hW.fderiv_of_isOpen hs (by norm_num)
  have hE1 : ∀ i, ContDiffOn ℝ 1 (fun x => fderiv ℝ (E i) x) s :=
    fun i => (hE i).fderiv_of_isOpen hs (by norm_num)
  have hWd : ∀ x ∈ s, DifferentiableAt ℝ W x :=
    fun x hx => (hW.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)
  have hEd : ∀ i, ∀ x ∈ s, DifferentiableAt ℝ (E i) x :=
    fun i x hx => ((hE i).contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)
  have hWd1 : ∀ x ∈ s, DifferentiableAt ℝ (fun x => fderiv ℝ W x) x :=
    fun x hx => (hW1.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)
  have hEd1 : ∀ i, ∀ x ∈ s, DifferentiableAt ℝ (fun x => fderiv ℝ (E i) x) x :=
    fun i x hx => ((hE1 i).contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)
  -- first derivative of `U` on `s`
  have hHU : ∀ x ∈ s, HasFDerivAt U (fderiv ℝ W x + ∑ i, a i • fderiv ℝ (E i) x) x := by
    intro x hx
    have hUf : U = fun z => W z + ∑ i, a i • E i z := funext hU
    rw [hUf]
    exact (hWd x hx).hasFDerivAt.add
      (HasFDerivAt.fun_sum fun i _ => (hEd i x hx).hasFDerivAt.const_smul (a i))
  have hfd : ∀ x ∈ s, fderiv ℝ U x = fderiv ℝ W x + ∑ i, a i • fderiv ℝ (E i) x :=
    fun x hx => (hHU x hx).fderiv
  have hev : (fun x => fderiv ℝ U x) =ᶠ[nhds y]
      (fun x => fderiv ℝ W x + ∑ i, a i • fderiv ℝ (E i) x) :=
    Filter.eventually_of_mem (hs.mem_nhds hy) (fun x hx => hfd x hx)
  -- the derivative of the derivative at `y`
  have hD : HasFDerivAt (fun x => fderiv ℝ W x + ∑ i, a i • fderiv ℝ (E i) x)
      (fderiv ℝ (fun x => fderiv ℝ W x) y +
        ∑ i, a i • fderiv ℝ (fun x => fderiv ℝ (E i) x) y) y :=
    (hWd1 y hy).hasFDerivAt.add
      (HasFDerivAt.fun_sum fun i _ => (hEd1 i y hy).hasFDerivAt.const_smul (a i))
  have hdiffU : DifferentiableAt ℝ (fun x => fderiv ℝ U x) y :=
    hD.differentiableAt.congr_of_eventuallyEq hev
  have hsecU : secondJet U y = fderiv ℝ (fun x => fderiv ℝ U x) y :=
    secondJet_eq_fderiv hdiffU
  have hsecW : secondJet W y = fderiv ℝ (fun x => fderiv ℝ W x) y :=
    secondJet_eq_fderiv (hWd1 y hy)
  have hfdU2 : fderiv ℝ (fun x => fderiv ℝ U x) y =
      fderiv ℝ (fun x => fderiv ℝ W x + ∑ i, a i • fderiv ℝ (E i) x) y := hev.fderiv_eq
  -- the three differences
  have hUW : U y - W y = ∑ i, a i • E i y := by
    rw [hU y, add_sub_cancel_left]
  have hfdUW : fderiv ℝ U y - fderiv ℝ W y = ∑ i, a i • fderiv ℝ (E i) y := by
    rw [hfd y hy, add_sub_cancel_left]
  have h2 : secondJet U y - secondJet W y =
      ∑ i, a i • fderiv ℝ (fun x => fderiv ℝ (E i) x) y := by
    rw [hsecU, hfdU2, hD.fderiv, hsecW]
    abel
  -- norm identities for the three terms of the density
  have hn0 : ∀ i, ‖iteratedFDeriv ℝ 0 (E i) y‖ = ‖E i y‖ := fun i => norm_iteratedFDeriv_zero
  have hn1 : ∀ i, ‖iteratedFDeriv ℝ 1 (E i) y‖ = ‖fderiv ℝ (E i) y‖ :=
    fun i => norm_iteratedFDeriv_one (E i)
  have hn2 : ∀ i, ‖iteratedFDeriv ℝ 2 (E i) y‖ = ‖fderiv ℝ (fun x => fderiv ℝ (E i) x) y‖ := by
    intro i
    rw [← norm_iteratedFDeriv_one]
    exact norm_iteratedFDeriv_fderiv.symm
  have T0 : ‖U y - W y‖ ≤ ∑ i, |a i| * ‖E i y‖ := by
    rw [hUW]; exact cs_norm_sum_le a (fun i => E i y)
  have T1 : ‖fderiv ℝ U y - fderiv ℝ W y‖ ≤ ∑ i, |a i| * ‖fderiv ℝ (E i) y‖ := by
    rw [hfdUW]; exact cs_norm_sum_le a (fun i => fderiv ℝ (E i) y)
  have T2 : ‖secondJet U y - secondJet W y‖ ≤
      ∑ i, |a i| * ‖fderiv ℝ (fun x => fderiv ℝ (E i) x) y‖ := by
    rw [h2]; exact cs_norm_sum_le a (fun i => fderiv ℝ (fun x => fderiv ℝ (E i) x) y)
  have hexp : ∀ i, ∑ j ∈ Finset.range 3, ‖iteratedFDeriv ℝ j (E i) y‖ =
      ‖E i y‖ + ‖fderiv ℝ (E i) y‖ + ‖fderiv ℝ (fun x => fderiv ℝ (E i) x) y‖ := by
    intro i
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hn0, hn1, hn2]
  unfold coefChgDens
  calc ‖U y - W y‖ + ‖fderiv ℝ U y - fderiv ℝ W y‖ + ‖secondJet U y - secondJet W y‖
      ≤ (∑ i, |a i| * ‖E i y‖) + (∑ i, |a i| * ‖fderiv ℝ (E i) y‖) +
          ∑ i, |a i| * ‖fderiv ℝ (fun x => fderiv ℝ (E i) x) y‖ :=
        add_le_add (add_le_add T0 T1) T2
    _ = ∑ i, |a i| * ∑ j ∈ Finset.range 3, ‖iteratedFDeriv ℝ j (E i) y‖ := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hexp i]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
