import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_5
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.WindowTest
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.DriftOffAxis.Rep

/-!
# Helper for `PartII-b:G4/3/5/1` (`ProfileWindowZero`): the vector phase test of a window test

Source of record: `the November 2 reference manuscript`, lines 1902-1906, 2370-2384.

For a window test `χ` and `j = r, z`, `Φ_j = φ · realC(e_j)` with `φ = winPer χ ∘ chart` is a phase test
(`φ` vanishes near the axis, where `e_r` is singular), and off the axis
`dotL(Φ_j, N_v g) = φ √s g_j(chart)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

namespace WindowZeroHelp

open ChartWinHelp ChartWinHelp2

/-- The `j`-th meridional unit vector. -/
def ej (j : Fin 2) (y : Space) : Space := if j = 0 then Axi.eR y else Axi.e3

/-- The chart pullback of the periodized window. -/
def Gw (c ε : ℝ) (χ : Coord → ℝ) (x : ℝ × Space) : ℝ := winPer c χ (Axi.chart ε⁻¹ x.1 x.2)

theorem ϱ_axis {y : Space} (hax : y ∈ Axi.axis) : Axi.ϱ y = 0 := by
  obtain ⟨h0, h1⟩ := hax
  unfold Axi.ϱ
  rw [h0, h1]
  simp

/-- `winPer ∘ chart` vanishes in a neighbourhood of the axis (including the axis). -/
theorem Gw_zero_near_axis {c ε : ℝ} (hε : 0 < ε) {χ : Coord → ℝ} (hχ : IsWinTest c χ) :
    ∃ δ > 0, ∀ (τ : ℝ) (y : Space), Axi.ϱ y < δ → Gw c ε χ (τ, y) = 0 := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  obtain ⟨a, ha, b, hb, M, hab⟩ := supp_bounds hχ
  have hab' : ∀ y : Coord, χ y ≠ 0 → a ≤ y.1 ∧ y.1 ≤ b :=
    fun y hy => ⟨(hab y hy).1, (hab y hy).2.1⟩
  refine ⟨ε⁻¹ / (b + 1), div_pos hR (by linarith), fun τ y hx => ?_⟩
  apply winPer_zero_of_s hab'
  show Axi.age ε⁻¹ y < a ∨ b < Axi.age ε⁻¹ y
  by_cases h0 : Axi.ϱ y = 0
  · left
    have h3 : Axi.age ε⁻¹ y = 0 := by
      unfold Axi.age
      rw [h0]
      simp
    rw [h3]
    exact ha
  · right
    have hnn : 0 ≤ Axi.ϱ y := Real.sqrt_nonneg _
    have hp : 0 < Axi.ϱ y := lt_of_le_of_ne hnn (Ne.symm h0)
    have h2 : Axi.ϱ y * (b + 1) < ε⁻¹ := (lt_div_iff₀ (by linarith : (0 : ℝ) < b + 1)).1 hx
    unfold Axi.age
    rw [lt_div_iff₀ (pow_pos hp 2)]
    have h3 : 0 < ε⁻¹ + Axi.ϱ y * (b + 1) := by
      have := mul_pos hp (show (0 : ℝ) < b + 1 by linarith)
      linarith
    have h4 := mul_pos (sub_pos.2 h2) h3
    nlinarith [h4, mul_nonneg (sq_nonneg (Axi.ϱ y))
      (show (0 : ℝ) ≤ b ^ 2 + b + 1 by nlinarith [sq_nonneg b])]

theorem ej_contDiffAt (j : Fin 2) {y : Space} (hy : y ∉ Axi.axis) : ContDiffAt ℝ ∞ (ej j) y := by
  unfold ej
  split_ifs
  · exact Axi.contDiffOn_eR.contDiffAt (Axi.isClosed_axis.isOpen_compl.mem_nhds hy)
  · exact contDiffAt_const

end WindowZeroHelp

open WindowZeroHelp ChartWinHelp ChartWinHelp2 in
/-- **`WZ-A`**: the vector phase test of a window test. -/
theorem windowPhaseVec (c ε : ℝ) (χ : Coord → ℝ) (hc : 0 < c) (hε : 0 < ε)
    (hχ : IsWinTest c χ) (j : Fin 2) :
    ∃ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ ∧
      ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
        Φ (τ, y) = ((winPer c χ (Axi.chart ε⁻¹ τ y) : ℝ) : ℂ) • B0412.realC (ej j y) := by
  obtain ⟨φ, hφ, hφe⟩ := chartWindowTest_proof c ε χ hc hε hχ
  obtain ⟨δ, hδ, hz⟩ := Gw_zero_near_axis hε hχ
  have hRpos : 0 < ε⁻¹ := inv_pos.2 hε
  have hG := G_contDiff hc hRpos hχ
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by
    rw [div_inv_eq_mul]
    ring
  refine ⟨fun x => ((Gw c ε χ x : ℝ) : ℂ) • B0412.realC (ej j x.2), ⟨?_, ?_, ?_⟩, fun τ y _ => rfl⟩
  · rw [contDiff_iff_contDiffAt]
    intro x0
    by_cases hnear : Axi.ϱ x0.2 < δ
    · have hev : ∀ᶠ x in 𝓝 x0, Axi.ϱ x.2 < δ :=
        (Axi.continuous_ϱ.comp continuous_snd).continuousAt.eventually_lt continuousAt_const hnear
      have hzero : (fun x : ℝ × Space => ((Gw c ε χ x : ℝ) : ℂ) • B0412.realC (ej j x.2)) =ᶠ[𝓝 x0]
          fun _ => (0 : CVec3) := by
        filter_upwards [hev] with x hx
        simp [hz x.1 x.2 hx]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
    · have hy0 : x0.2 ∉ Axi.axis := fun hax => hnear (by rw [ϱ_axis hax]; exact hδ)
      have h1 : ContDiffAt ℝ ∞ (fun x : ℝ × Space => ((Gw c ε χ x : ℝ) : ℂ)) x0 :=
        (Complex.ofRealCLM.contDiff.comp hG).contDiffAt
      have h2 : ContDiffAt ℝ ∞ (fun x : ℝ × Space => DriftOff.realCL (ej j x.2)) x0 :=
        DriftOff.realCL.contDiff.contDiffAt.comp x0 ((ej_contDiffAt j hy0).comp x0 contDiffAt_snd)
      exact h1.smul h2
  · intro τ y
    have hper : winPer c χ (Axi.chart ε⁻¹ (τ + 2 * ε * c) y) =
        winPer c χ (Axi.chart ε⁻¹ τ y) := by
      rw [Axi.chart_add_period hRpos.ne' hP τ y]
      exact winPer_add_c hc χ (Axi.chart ε⁻¹ τ y)
    show ((winPer c χ (Axi.chart ε⁻¹ (τ + 2 * ε * c) y) : ℝ) : ℂ) • B0412.realC (ej j y) =
      ((winPer c χ (Axi.chart ε⁻¹ τ y) : ℝ) : ℂ) • B0412.realC (ej j y)
    rw [hper]
  · obtain ⟨R, hR⟩ := hφ.bounded_support
    refine ⟨R, fun τ y hy => ?_⟩
    by_cases hax : y ∈ Axi.axis
    · have := hz τ y (by rw [ϱ_axis hax]; exact hδ)
      simp [this]
    · have h0 := hR τ y hy
      rw [hφe τ y hax] at h0
      have : Gw c ε χ (τ, y) = 0 := by exact_mod_cast h0
      simp [this]

end UnforcedLeray.Short.IIb
