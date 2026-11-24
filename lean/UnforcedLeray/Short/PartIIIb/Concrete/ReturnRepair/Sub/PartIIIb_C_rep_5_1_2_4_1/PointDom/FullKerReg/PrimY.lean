import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.RingMap

/-!
# The primitive as a function of the receiver `y`: `Φ(y) = primInt A w (ϱ y, 0, y₃)`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem ringMap_apply0 (y : Space) : ringMap y 0 = ϱ y := by simp [ringMap]
theorem ringMap_apply2 (y : Space) : ringMap y 2 = y 2 := by simp [ringMap]

theorem primY_main {r₁ : ℝ} (hr₁ : 0 < r₁) (Y : ℝ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {A : Space → ℝ}, ContDiff ℝ 2 A → ∀ (w : Space) {K ρ₀ δ : ℝ}, 0 ≤ K → 0 ≤ ρ₀ →
      0 < δ → ρ₀ + δ = r₁ → w 0 ≤ ρ₀ →
      (∀ x : Space, x ≠ 0 → |A x| ≤ K * (‖x‖ ^ 4)⁻¹) →
      (∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ 1 A x‖ ≤ K * (‖x‖ ^ 5)⁻¹) →
      (∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ 2 A x‖ ≤ K * (‖x‖ ^ 6)⁻¹) →
      ∀ y : Space, r₁ < ϱ y → ‖y‖ < Y →
        ContDiffAt ℝ 2 (fun y' => primInt A w (ringMap y')) y ∧
        ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (fun y' => primInt A w (ringMap y')) y‖ ≤
          (n.factorial : ℝ) * (primCp ρ₀ δ * K *
            (1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - w 2) ^ 2)))) * D ^ n := by
  obtain ⟨B, hB0, hB⟩ := region_bound (contDiffOn_ringMap) hr₁ Y
  refine ⟨max 1 B, le_max_left _ _, fun {A} hA w {K ρ₀ δ} hK hρ₀ hδ hrd hw b0 b1 b2 y hy hyY => ?_⟩
  obtain ⟨hcd, hbd⟩ := primInt_main hA w hK hρ₀ hδ hw b0 b1 b2
  set s : Set Space := {y | r₁ < ϱ y} with hs
  have hso : IsOpen s := isOpen_lt continuous_const continuous_ϱ
  have hUo : IsOpen {q : Space | ρ₀ + δ < q 0} :=
    isOpen_lt continuous_const ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous)
  have hst : MapsTo ringMap s {q : Space | ρ₀ + δ < q 0} := fun y' hy' => by
    show ρ₀ + δ < ringMap y' 0
    rw [ringMap_apply0, hrd]; exact hy'
  have hring : ContDiffOn ℝ 2 ringMap s :=
    contDiffOn_ringMap.mono (fun y' hy' => lt_trans hr₁ hy')
  have hcomp : ContDiffOn ℝ 2 (fun y' => primInt A w (ringMap y')) s :=
    hcd.comp hring hst
  refine ⟨hcomp.contDiffAt (hso.mem_nhds hy), fun n hn => ?_⟩
  have hq : ρ₀ + δ < ringMap y 0 := hst hy
  obtain ⟨h0, h1, h2⟩ := hbd (ringMap y) hq
  rw [ringMap_apply0, ringMap_apply2] at h0 h1 h2
  have := comp_bound_open (g := primInt A w) (f := ringMap) hUo hso hcd hring hst hy
    (C := primCp ρ₀ δ * K * (1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - w 2) ^ 2)))) (D := max 1 B)
    (fun i hi => by
      interval_cases i
      · exact h0
      · exact h1
      · exact h2)
    (fun i h1i hi => by
      have hBi := hB y hy.le hyY.le i hi
      calc ‖iteratedFDeriv ℝ i ringMap y‖ ≤ B := hBi
        _ ≤ max 1 B := le_max_right _ _
        _ ≤ (max 1 B) ^ i := le_self_pow₀ (le_max_left _ _) (by omega)) n hn
  exact this

end UnforcedLeray.Short.PartIIIb.Concrete

end
