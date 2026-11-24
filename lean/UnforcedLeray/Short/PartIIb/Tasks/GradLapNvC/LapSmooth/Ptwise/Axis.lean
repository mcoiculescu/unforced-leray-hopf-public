import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5_5

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- On the axis the ring lift vanishes: `age = R²/0 = 0`, so `√age = 0`. -/
theorem Nv_axis_zero (R : ℝ) (g : Coord → UnforcedLeray.Axi.Merid) (τ : ℝ) {y : Space}
    (hy : y ∈ UnforcedLeray.Axi.axis) : UnforcedLeray.Axi.Nv R g τ y = 0 := by
  have hy' : y 0 = 0 ∧ y 1 = 0 := hy
  have hϱ : UnforcedLeray.Axi.ϱ y = 0 := by
    simp [UnforcedLeray.Axi.ϱ, hy'.1, hy'.2]
  have hage : UnforcedLeray.Axi.age R y = 0 := by
    simp [UnforcedLeray.Axi.age, hϱ]
  simp [UnforcedLeray.Axi.Nv, hage]

/-- A ring lift vanishes when its profile vanishes at the chart point. -/
theorem Nv_eq_zero_of_chart (R : ℝ) (g : Coord → UnforcedLeray.Axi.Merid) (τ : ℝ) (y : Space)
    (h : g (UnforcedLeray.Axi.chart R τ y) = 0) : UnforcedLeray.Axi.Nv R g τ y = 0 := by
  simp [UnforcedLeray.Axi.Nv, h]

/-- Off the axis, with `y₀² + y₁² < R²/(|s₁|+1)`, the chart's age is either below `s₀`
(this includes the junk value `0` on the axis) or above `s₁`. -/
theorem age_lt_or_gt (R : ℝ) (hR : 0 < R) (s₀ s₁ : ℝ) (hs₀ : 0 < s₀) (y : Space)
    (hy : y 0 ^ 2 + y 1 ^ 2 < R ^ 2 / (|s₁| + 1)) :
    UnforcedLeray.Axi.age R y < s₀ ∨ s₁ < UnforcedLeray.Axi.age R y := by
  by_cases hq : y 0 ^ 2 + y 1 ^ 2 = 0
  · left
    have h0 : y 0 = 0 := (pow_eq_zero_iff two_ne_zero).1 (by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)])
    have h1 : y 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 (by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)])
    have hϱ : UnforcedLeray.Axi.ϱ y = 0 := by simp [UnforcedLeray.Axi.ϱ, h0, h1]
    simp [UnforcedLeray.Axi.age, hϱ, hs₀]
  · right
    have hqpos : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hq)
    have hϱ2 : UnforcedLeray.Axi.ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
      unfold UnforcedLeray.Axi.ϱ
      exact Real.sq_sqrt (by positivity)
    have hM : (0 : ℝ) < |s₁| + 1 := by positivity
    have hy' := (lt_div_iff₀ hM).1 hy
    unfold UnforcedLeray.Axi.age
    rw [hϱ2, lt_div_iff₀ hqpos]
    nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self s₁)) hqpos.le, abs_nonneg s₁]

/-- The ring lift of any complex profile vanishes on the open set `ϱ² < R²/(|s₁|+1)` when the
profile vanishes outside the nice box. -/
theorem NvC_near_zero (R : ℝ) (hR : 0 < R) (s₀ s₁ L : ℝ) (hs₀ : 0 < s₀) (b : CProf)
    (hb : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → b x = 0)
    (t : ℝ) (y : Space) (hy : y 0 ^ 2 + y 1 ^ 2 < R ^ 2 / (|s₁| + 1)) :
    NvC R b (t, y) = 0 := by
  have hc : b (UnforcedLeray.Axi.chart R t y) = 0 := by
    apply hb
    rcases age_lt_or_gt R hR s₀ s₁ hs₀ y hy with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hre : UnforcedLeray.Axi.Nv R (fun z => reM (b z)) t y = 0 :=
    Nv_eq_zero_of_chart _ _ _ _ (by rw [hc]; ext i; simp [reM])
  have him : UnforcedLeray.Axi.Nv R (fun z => imM (b z)) t y = 0 :=
    Nv_eq_zero_of_chart _ _ _ _ (by rw [hc]; ext i; simp [imM])
  simp [NvC, hre, him, UnforcedLeray.B0412.realC]

/-- Zero of `lapT` at a point having a neighbourhood where the function vanishes. -/
theorem lapT_eq_zero_on_open {Φ : ℝ × Space → CVec3} {U : Set (ℝ × Space)} (hU : IsOpen U)
    (hΦ : ∀ q ∈ U, Φ q = 0) {p : ℝ × Space} (hp : p ∈ U) :
    UnforcedLeray.PhaseSpace.lapT Φ p = 0 := by
  have hfd : ∀ q ∈ U, fderiv ℝ Φ q = 0 := by
    intro q hq
    have hev : Φ =ᶠ[𝓝 q] (0 : ℝ × Space → CVec3) :=
      Filter.eventually_of_mem (hU.mem_nhds hq) (fun x hx => hΦ x hx)
    rw [hev.fderiv_eq]
    simp
  have hdy : ∀ j : Fin 3, ∀ q ∈ U, UnforcedLeray.PhaseSpace.dy j Φ q = 0 := by
    intro j q hq
    show fderiv ℝ Φ q _ = 0
    rw [hfd q hq]
    simp
  simp only [UnforcedLeray.PhaseSpace.lapT]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hev : UnforcedLeray.PhaseSpace.dy j Φ =ᶠ[𝓝 p] (0 : ℝ × Space → CVec3) :=
    Filter.eventually_of_mem (hU.mem_nhds hp) (fun x hx => hdy j x hx)
  show fderiv ℝ (UnforcedLeray.PhaseSpace.dy j Φ) p _ = 0
  rw [hev.fderiv_eq]
  simp

theorem lapAxis : UnforcedLeray.Short.IIb.LapAxis := by
  intro c ε ν b hc hε hb t y hy
  obtain ⟨-, -, s₀, s₁, L, hs₀, hbz⟩ := hb
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  let U : Set (ℝ × Space) := {p | p.2 0 ^ 2 + p.2 1 ^ 2 < (ε⁻¹) ^ 2 / (|s₁| + 1)}
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hyU : (t, y) ∈ U := by
    have hy' : y 0 = 0 ∧ y 1 = 0 := hy
    show y 0 ^ 2 + y 1 ^ 2 < (ε⁻¹) ^ 2 / (|s₁| + 1)
    have hpos := div_pos (pow_pos hR 2) (show (0 : ℝ) < |s₁| + 1 by positivity)
    rw [hy'.1, hy'.2]
    linarith
  have hvan : ∀ q ∈ U, NvC ε⁻¹ b q = 0 := fun q hq =>
    NvC_near_zero ε⁻¹ hR s₀ s₁ L hs₀ b hbz q.1 q.2 hq
  have hL : nuLapT ν (NvC ε⁻¹ b) (t, y) = 0 := by
    unfold UnforcedLeray.PhaseSpace.nuLapT
    rw [Pi.smul_apply, lapT_eq_zero_on_open hU hvan hyU, smul_zero]
  have hR' : NvC ε⁻¹ (lapProf ν ε b (classQ ε (classQ ε b)) (classEta (classEta b))) (t, y) = 0 := by
    simp [NvC, Nv_axis_zero _ _ _ hy, UnforcedLeray.B0412.realC]
  rw [hL, hR']

end UnforcedLeray.Short.IIb
