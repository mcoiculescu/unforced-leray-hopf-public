import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.PhaseIBP
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Point.Kern
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Point.Omega
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Point.Lim
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Point.RealPart
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Point.Hor

/-!
# `OscPoint` (task `PartIII-b:C/rep/8/1/1/1/2/1/3`)

Source `shorter-proof-2026-11-02.tex` lines 5400-5427, 3768-3790.  Helpers in `Point/`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

open UnforcedLeray.Short.IIIa

lemma fd_eq (i j k : Fin 3) (w : Space) {s : ℝ} (hs : 0 < s) (l : ℝ) (z y0 : Space) :
    fderiv ℝ (fun y' => fderiv ℝ (fun x => heatLerayK s i j x) (y' - l • z)
      (UnforcedLeray.coordinateVector k)) y0 w = Hk i j k w (s, y0 - l • z) := by
  rw [Hk_eq i j k w hs]
  have hG := h2_smooth i j k hs
  have h := ((hG.differentiable (by simp)) (y0 - l • z)).hasFDerivAt.comp y0
    ((hasFDerivAt_id y0).sub_const (l • z))
  have h' : HasFDerivAt (fun y' => fderiv ℝ (fun x => heatLerayK s i j x) (y' - l • z)
      (UnforcedLeray.coordinateVector k)) _ y0 := h
  rw [h'.fderiv]
  simp

theorem oscPoint : UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg.OscPoint := by
  intro K hK hRe
  obtain ⟨C, hCpos, hpk⟩ := kerPack
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = 3 + 2 * |R| := ⟨_, rfl⟩
  have hΛ1 : 1 ≤ Λ := by rw [hΛdef]; linarith [abs_nonneg R]
  refine ⟨(2 * Λ + 8) * C, 9, by positivity, ?_⟩
  intro ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ f hfm hper hmean z xo q₀ hz hxo i j k w hw
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := ⟨_, rfl⟩
  rw [← hrdef] at hxo ⊢
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hrpos : 0 < r := by linarith
  have hd : 0 < r - ρo := by linarith
  obtain ⟨y0, hy0⟩ : ∃ y0 : Space, y0 = ε⁻¹ • xo := ⟨_, rfl⟩
  rw [← hy0]
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = (r - ρo) / ε := ⟨_, rfl⟩
  have hg : 0 < g := by rw [hgdef]; exact div_pos hd hε
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = ρo / ε + |z 2| := ⟨_, rfl⟩
  have hzh : hor z ≤ ρo / ε := by
    rw [le_div_iff₀ hε, mul_comm]
    exact hz
  have hZ : ‖z‖ ≤ Z := by rw [hZdef]; linarith [norm_le_hor z]
  have hZ0 : 0 ≤ Z := (norm_nonneg z).trans hZ
  have hgap : ∀ l ∈ Ioo (0 : ℝ) 1, g ≤ ‖y0 - l • z‖ := by
    intro l hl
    have h1 := hor_sub y0 z l hl.1.le
    have h2 : hor y0 = ε⁻¹ * r := by
      rw [hy0, hor_smul _ (inv_nonneg.2 hε.le), hrdef]; rfl
    have h3 : l * hor z ≤ ρo / ε := by
      calc l * hor z ≤ 1 * (ρo / ε) :=
            mul_le_mul hl.2.le hzh (by unfold hor; positivity) (by norm_num)
        _ = _ := one_mul _
    have h4 : g = ε⁻¹ * r - ρo / ε := by rw [hgdef]; field_simp
    have := hor_le_norm (y0 - l • z)
    linarith
  -- the coefficient
  obtain ⟨a, hadef⟩ : ∃ a : ℂ, a = 2 * μ + 2 := ⟨_, rfl⟩
  have hare : a.re = 2 * μ.re + 2 := by rw [hadef]; simp
  have hμre := hRe μ hμ
  have hnorm : ‖1 + a‖ ≤ Λ := by
    rw [hadef, hΛdef]
    calc ‖1 + (2 * μ + 2)‖ = ‖(3 : ℂ) + 2 * μ‖ := by congr 1; ring
      _ ≤ ‖(3 : ℂ)‖ + ‖2 * μ‖ := norm_add_le _ _
      _ ≤ 3 + 2 * |R| := by
        rw [norm_mul]
        have h3 : ‖(3 : ℂ)‖ = 3 := by simp
        have h2 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h3, h2]
        have := hR μ hμ
        have := le_abs_self R
        linarith
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Λ * (C * g ^ (-5 : ℝ)) + 2 * C * g ^ (-7 : ℝ) +
      C * Z * g ^ (-6 : ℝ) := ⟨_, rfl⟩
  have g5 : 0 < g ^ (-5 : ℝ) := Real.rpow_pos_of_pos hg _
  have g6 : 0 ≤ g ^ (-6 : ℝ) := Real.rpow_nonneg hg.le _
  have g7 : 0 < g ^ (-7 : ℝ) := Real.rpow_pos_of_pos hg _
  have hE : 0 < E := by rw [hEdef]; positivity
  have hb := fun l (hl : l ∈ Ioo (0 : ℝ) 1) =>
    om_bounds C hCpos.le hpk hν hν1 a z y0 i j k w hw hg hZ hgap hl
  have hkey := osc_abstract phaseIBP (om a ν z y0 i j k w) (a.re + 1) E (by rw [hare]; linarith) hE
    (om_cd hν a z y0 i j k w)
    (fun l hl => by
      have := (hb l hl).1
      have e : a.re + 1 - 1 = a.re := by ring
      rw [e]
      refine this.trans ?_
      have hlr : 0 ≤ l ^ a.re := Real.rpow_nonneg hl.1.le _
      rw [mul_comm E]
      refine mul_le_mul_of_nonneg_left ?_ hlr
      rw [hEdef]
      have : 0 ≤ C * g ^ (-5 : ℝ) := by positivity
      nlinarith [mul_nonneg this (by linarith : 0 ≤ Λ - 1), mul_pos hCpos g7, mul_nonneg (mul_nonneg hCpos.le hZ0) g6])
    (fun l hl => by
      have := (hb l hl).2
      have e : a.re + 1 - 1 = a.re := by ring
      rw [e]
      refine this.trans ?_
      have hlr : 0 ≤ l ^ a.re := Real.rpow_nonneg hl.1.le _
      rw [mul_comm E]
      refine mul_le_mul_of_nonneg_left ?_ hlr
      rw [hEdef]
      have : 0 ≤ C * g ^ (-5 : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hnorm this])
    ε c hε hc f hfm hper hmean q₀
  -- identify the integrand
  have hint_eq : (∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
      ((fderiv ℝ (fun y' => fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x)
        (y' - l • z) (UnforcedLeray.coordinateVector k)) y0 w : ℝ) : ℂ) *
      ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ)) =
      ∫ l in Ioo (0 : ℝ) 1, om a ν z y0 i j k w l * ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun l hl => ?_)
    have hs : 0 < ν * (1 - l ^ 2) := pth_pos' hν z y0 hl
    rw [fd_eq i j k w hs l z y0]
    unfold om pth
    rw [hadef]
  rw [hint_eq]
  refine hkey.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  rw [hEdef, hgdef, hZdef]
  exact real_part C Λ ε ρo ρi ν c r (z 2) hCpos hΛ1 hν hc hε hε1 hρo hρ hxo (hgdef ▸ hg)

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
end
