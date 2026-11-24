import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4_1

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/1/1` (`DualRemVanish`): `Rem_L = 0` off `tsupport χ`.

Source: `the November 2 reference manuscript` lines 1923-1927.
If `ψ = 0` on an open set `U`, then all `cpdC`-derivatives vanish on `U`, hence so do
`perpC ψ` and `flatTransposeC (perpC ψ)` (iterated `cpdC`) on `U`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem dualVan_cpdC {U : Set Coord} (hU : IsOpen U) {ψ : Coord → ℂ}
    (h : ∀ y ∈ U, ψ y = 0) (j : Fin 3) : ∀ y ∈ U, cpdC j ψ y = 0 := by
  intro y hy
  have hev : ψ =ᶠ[𝓝 y] (fun _ : Coord => (0 : ℂ)) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact h z hz
  have hd : fderiv ℝ ψ y = fderiv ℝ (fun _ : Coord => (0 : ℂ)) y := hev.fderiv_eq
  unfold cpdC
  rw [hd, fderiv_const_apply]
  simp

theorem dualVan_perpC {U : Set Coord} (hU : IsOpen U) {ψ : Coord → ℂ}
    (h : ∀ y ∈ U, ψ y = 0) : ∀ y ∈ U, ∀ i : Fin 2, perpC ψ y i = 0 := by
  intro y hy i
  have h1 := dualVan_cpdC hU h 1 y hy
  have h2 := dualVan_cpdC hU h 2 y hy
  fin_cases i <;> simp [perpC, h1, h2]

theorem dualVan_flatT {U : Set Coord} (hU : IsOpen U) (ν : ℝ) (μ : ℂ) {ψ : Coord → ℂ}
    (h : ∀ y ∈ U, ψ y = 0) : ∀ x ∈ U, ∀ i : Fin 2, flatTransposeC ν μ (perpC ψ) x i = 0 := by
  intro x hx i
  have hΨ : ∀ y ∈ U, perpC ψ y i = 0 := fun y hy => dualVan_perpC hU h y hy i
  have hi : ∀ y ∈ U, (fun z => perpC ψ z i) y = 0 := fun y hy => hΨ y hy
  have c0 := dualVan_cpdC hU (ψ := fun z => perpC ψ z i) hi 0 x hx
  have c1 := dualVan_cpdC hU (ψ := fun y => cpdC 1 (fun z => perpC ψ z i) y)
    (fun y hy => dualVan_cpdC hU hi 1 y hy) 1 x hx
  have c2 := dualVan_cpdC hU (ψ := fun y => cpdC 2 (fun z => perpC ψ z i) y)
    (fun y hy => dualVan_cpdC hU hi 2 y hy) 2 x hx
  unfold flatTransposeC
  rw [hΨ x hx, c0, c1, c2]
  simp

theorem dualRemVanish : UnforcedLeray.Short.IIb.DualRemVanish := by
  intro ν μ χ φ H s L x hx i
  have hU : IsOpen {y : Coord | y.1 ∉ tsupport χ} :=
    (isClosed_tsupport χ).isOpen_compl.preimage continuous_fst
  have hxU : x ∈ {y : Coord | y.1 ∉ tsupport χ} := hx
  have hχ : ∀ y ∈ {y : Coord | y.1 ∉ tsupport χ}, χ y.1 = 0 :=
    fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hPsiInf : ∀ y ∈ {y : Coord | y.1 ∉ tsupport χ}, dualPsiInf μ χ H s y = 0 := by
    intro y hy
    unfold dualPsiInf
    rw [hχ y hy]
    simp
  have hPsi : ∀ y ∈ {y : Coord | y.1 ∉ tsupport χ}, dualPsi μ χ φ H s L y = 0 := by
    intro y hy
    unfold dualPsi
    rw [hPsiInf y hy]
    simp
  simp only [dualRem]
  rw [dualVan_flatT hU ν μ hPsi x hxU i, dualVan_flatT hU ν μ hPsiInf x hxU i]
  simp

end UnforcedLeray.Short.IIb
