import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer

/-!
# `wardYoungPointwise`: Young support of the Ward fields `Y`, `h` (source 4306-4311)

For `1 < ν s` at the chart point `p = (s, (q, η))`, the similarity point `y₀ = NearInst.chartY R p` has
`ϱ y₀ = R/√s > 0` and `age R y₀ = s`.  Near `y₀` the cutoff `χ_y(ν·age)` and its derivative
vanish (`χ_y = 0` on `[1, ∞)`), so the Ward stream cutoff `𝒞_y Z` is zero near `y₀`.  Hence
`X` vanishes near `y₀` at every time, which kills `Y = D_{μ+1}X` and `h = [U, X]` at `y₀`, and so
their chart coefficients `coefOf R · p`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wyp_streamCut_near {ν R : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (Z : ℝ → Space → Space) (τ : ℝ) {y₀ : Space} (hϱ : 0 < ϱ y₀) (hage : 1 < ν * age R y₀) :
    wardStreamCut ν R χy Z τ =ᶠ[𝓝 y₀] fun _ => (0 : Space) := by
  have hc1 : ContinuousAt (fun y => ν * age R y) y₀ := by
    unfold age
    exact continuousAt_const.mul
      (continuousAt_const.div (continuous_ϱ.continuousAt.pow 2) (pow_pos hϱ 2).ne')
  have hc2 : ContinuousAt ϱ y₀ := continuous_ϱ.continuousAt
  have hev1 : ∀ᶠ y in 𝓝 y₀, 1 < ν * age R y := continuousAt_const.eventually_lt hc1 hage
  have hev2 : ∀ᶠ y in 𝓝 y₀, 0 < ϱ y := continuousAt_const.eventually_lt hc2 hϱ
  filter_upwards [hev1, hev2] with y hy1 hy2
  have hχ0 : χy (ν * age R y) = 0 := hχy.zero _ hy1.le
  have hdχ : deriv χy (ν * age R y) = 0 := by
    have hev : χy =ᶠ[𝓝 (ν * age R y)] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hy1)
        (fun t ht => hχy.zero t (le_of_lt (Set.mem_Ioi.mp ht)))
    rw [hev.deriv_eq, deriv_const]
  unfold wardStreamCut
  rw [hχ0, hdχ]
  simp

theorem wyp_at (ν μ R c : ℝ) {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy) (g : Chart → Ten3)
    {y₀ : Space} (hϱ : 0 < ϱ y₀) (hage : 1 < ν * age R y₀) (τ : ℝ) :
    wardX ν μ R c χy g τ =ᶠ[𝓝 y₀] fun _ => (0 : Space) :=
  wyp_streamCut_near hχy _ τ hϱ hage

theorem wyp_physPd_zero {F : Space → Space} {y₀ : Space}
    (h : F =ᶠ[𝓝 y₀] fun _ => (0 : Space)) (j : Fin 3) :
    physPd F j =ᶠ[𝓝 y₀] fun _ => (0 : Space) := by
  have hF : fderiv ℝ F =ᶠ[𝓝 y₀] fderiv ℝ (fun _ => (0 : Space)) := h.fderiv
  filter_upwards [hF] with y hy
  simp [physPd, hy]

theorem wyp_physPd2_zero {F : Space → Space} {y₀ : Space}
    (h : F =ᶠ[𝓝 y₀] fun _ => (0 : Space)) (j l : Fin 3) : physPd2 F j l y₀ = 0 := by
  have hG : (fun y' => physPd F l y') =ᶠ[𝓝 y₀] fun _ => (0 : Space) := wyp_physPd_zero h l
  show fderiv ℝ (fun y' => physPd F l y') y₀ (coordinateVector j) = 0
  rw [hG.fderiv_eq]
  simp

theorem wyp_physLap_zero {F : Space → Space} {y₀ : Space}
    (h : F =ᶠ[𝓝 y₀] fun _ => (0 : Space)) : physLap F y₀ = 0 := by
  unfold physLap
  exact Finset.sum_eq_zero fun j _ => wyp_physPd2_zero h j j

theorem wyp_physDmu_zero (ν μ : ℝ) {F : ℝ → Space → Space} {y₀ : Space}
    (h : ∀ t, F t =ᶠ[𝓝 y₀] fun _ => (0 : Space)) (τ : ℝ) : physDmu ν μ F τ y₀ = 0 := by
  have h1 : deriv (fun t => F t y₀) τ = 0 := by
    have hfun : (fun t => F t y₀) = fun _ => (0 : Space) :=
      funext fun t => (h t).self_of_nhds
    rw [hfun, deriv_const]
  have h2 : fderiv ℝ (F τ) y₀ = 0 := by
    rw [(h τ).fderiv_eq, fderiv_const_apply]
  have h3 : physLap (F τ) y₀ = 0 := wyp_physLap_zero (h τ)
  unfold physDmu
  rw [h1, h2, h3, (h τ).self_of_nhds]
  simp

theorem wyp_coef_zero (R : ℝ) (F : ℝ → Space → Space) (p : Chart)
    (h : ∀ τ, F τ (NearInst.chartY R p) = 0) : coefOf R F p = 0 := by
  unfold coefOf
  rw [h (NearInst.chartTau R p)]
  ext i
  fin_cases i <;> simp

theorem wardYoungPointwise {ν μ R c : ℝ} {χy : ℝ → ℝ} (U : ℝ → SpatialField) (hν : 0 < ν)
    (hR : 0 < R) (hχy : IsYoungCutoff χy) : WardYoungPointwise ν μ R c χy U := by
  unfold WardYoungPointwise
  intro g p hp
  have hs : 0 < p.1 := by
    by_contra h
    have h' : p.1 ≤ 0 := not_lt.mp h
    nlinarith
  have hsq : 0 < Real.sqrt p.1 := Real.sqrt_pos.mpr hs
  have hR0 : R ≠ 0 := hR.ne'
  have hy0 : (NearInst.chartY R p) 0 = R / Real.sqrt p.1 := by simp [NearInst.chartY]
  have hy1 : (NearInst.chartY R p) 1 = 0 := by simp [NearInst.chartY]
  have hϱ0 : ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 := by
    unfold ϱ
    rw [hy0, hy1]
    rw [show (R / Real.sqrt p.1) ^ 2 + (0 : ℝ) ^ 2 = (R / Real.sqrt p.1) ^ 2 by ring]
    exact Real.sqrt_sq (div_pos hR hsq).le
  have hage0 : age R (NearInst.chartY R p) = p.1 := by
    unfold age
    rw [hϱ0, div_pow, Real.sq_sqrt hs.le]
    field_simp
  have hϱpos : 0 < ϱ (NearInst.chartY R p) := by
    rw [hϱ0]
    exact div_pos hR hsq
  have hνage : 1 < ν * age R (NearInst.chartY R p) := by
    rw [hage0]
    exact hp
  have hX : ∀ τ, wardX ν μ R c χy g τ =ᶠ[𝓝 (NearInst.chartY R p)] fun _ => (0 : Space) :=
    fun τ => wyp_at ν μ R c hχy g hϱpos hνage τ
  have hY : ∀ τ, physDmu ν (μ + 1) (wardX ν μ R c χy g) τ (NearInst.chartY R p) = 0 :=
    fun τ => wyp_physDmu_zero ν (μ + 1) hX τ
  have hH : ∀ τ, wardH ν μ R c χy U g τ (NearInst.chartY R p) = 0 := by
    intro τ
    unfold wardH
    have h1 : fderiv ℝ (wardX ν μ R c χy g τ) (NearInst.chartY R p) = 0 := by
      rw [(hX τ).fderiv_eq, fderiv_const_apply]
    have h2 : wardX ν μ R c χy g τ (NearInst.chartY R p) = 0 := (hX τ).self_of_nhds
    rw [h1, h2]
    simp
  exact ⟨wyp_coef_zero R (wardY ν μ R c χy g) p hY, wyp_coef_zero R (wardH ν μ R c χy U g) p hH⟩

end UnforcedLeray.Short.PartIIIb.Concrete
