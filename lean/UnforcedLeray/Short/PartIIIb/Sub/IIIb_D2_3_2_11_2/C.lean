import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2

/-!
# `WardXrSmoothOfParts` (`PartIII-b:IIIb-D2/3/2/11/2/6`, source 4180-4186)

Joint `C^∞` of `wardXr` from the smoothness hypotheses on `X₀` and its outward primitive. The
regularized field is `0` on the open set `{ϱ < R√ν}` and equals the streaming cut `wardStreamCut`
on the open set `{R√(5ν/6) < ϱ}` (`wardXr_of_not_mem`); the two open sets cover `Space`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The young-region formula for `wardXr` is jointly smooth on the open set `{R√(5ν/6) < ϱ}`. -/
theorem wardXr_contDiffOn_young (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3)
    (hν : 0 < ν) (hR : 0 < R) (hχy : IsYoungCutoff χy)
    (h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => wardX0 ν μ R c g x.1 x.2)
      {x | x.2 ∈ youngOpen ν R})
    (h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ × ℝ => outPrim (wardX0 ν μ R c g) x.1 x.2.1 x.2.2)
      {x | R * Real.sqrt (5 * ν / 6) < x.2.1}) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => wardXr ν μ R c χy g x.1 x.2)
      {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} := by
  have hW : IsOpen {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    isOpen_lt continuous_const (continuous_ϱ.comp continuous_snd)
  have hp0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hWax : ∀ x : ℝ × Space, R * Real.sqrt (5 * ν / 6) < ϱ x.2 → x.2 ∉ axis := by
    intro x hx h
    have h0 : ϱ x.2 = 0 := (mem_axis_iff x.2).1 h
    rw [h0] at hx
    linarith
  have hfor : ∀ x ∈ {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2},
      wardXr ν μ R c χy g x.1 x.2 = wardStreamCut ν R χy (wardX0 ν μ R c g) x.1 x.2 := by
    intro x hx
    rw [wardXr_of_not_mem ν μ R c χy g x.1 (hWax x hx)]
    rfl
  refine ContDiffOn.congr ?_ hfor
  have hϱ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => ϱ x.2)
      {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    contDiffOn_ϱ.comp contDiffOn_snd (fun x hx => hWax x hx)
  have hne : ∀ x ∈ {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2}, ϱ x.2 ≠ 0 :=
    fun x hx => ϱ_ne_zero (hWax x hx)
  have hage : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => age R x.2)
      {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    ContDiffOn.div contDiffOn_const (hϱ.pow 2) (fun x hx => pow_ne_zero 2 (hne x hx))
  have hνage : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => ν * age R x.2)
      {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    contDiffOn_const.mul hage
  have hdχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv χy) :=
    (show ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) χy from hχy.smooth).deriv'
  have hχA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => χy (ν * age R x.2))
      {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    hχy.smooth.comp_contDiffOn hνage
  have hdA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => deriv χy (ν * age R x.2))
      {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    hdχ.comp_contDiffOn hνage
  have hK : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => -2 * ν * R ^ 2 / ϱ x.2 ^ 3)
      {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    ContDiffOn.div contDiffOn_const (hϱ.pow 3) (fun x hx => pow_ne_zero 3 (hne x hx))
  have hz : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => x.2 2)
      {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd).contDiffOn
  have hmap : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => ((x.1, ϱ x.2, x.2 2) : ℝ × ℝ × ℝ))
      {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    contDiffOn_fst.prodMk (hϱ.prodMk hz)
  have hop : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => outPrim (wardX0 ν μ R c g) x.1 (ϱ x.2) (x.2 2))
      {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    h4.comp hmap (fun x hx => hx)
  have hZ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => wardX0 ν μ R c g x.1 x.2)
      {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    h2.mono (fun x hx => hx)
  have hterm1 := hχA.smul hZ
  have hterm2 := (((hdA.mul hK).div hϱ hne).mul hop).smul
    (contDiffOn_const (c := (coordinateVector 2 : Space)))
  exact hterm1.add hterm2

/-- **`WardXrSmoothOfParts`** (source 4180-4186): `wardXr` is jointly `C^∞`. -/
theorem wardXrSmoothOfParts_proved : WardXrSmoothOfParts := by
  intro ν μ R c χy g hν hR hχy h2 h4
  have hW := wardXr_contDiffOn_young ν μ R c χy g hν hR hχy h2 h4
  have hWo : IsOpen {x : ℝ × Space | R * Real.sqrt (5 * ν / 6) < ϱ x.2} :=
    isOpen_lt continuous_const (continuous_ϱ.comp continuous_snd)
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : R * Real.sqrt (5 * ν / 6) < ϱ p.2
  · exact hW.contDiffAt (hWo.mem_nhds hp)
  · have hlt : ϱ p.2 < R * Real.sqrt ν := by
      have h1 : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
        Real.sqrt_lt_sqrt (by linarith) (by linarith)
      have h2' : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := mul_lt_mul_of_pos_left h1 hR
      have h3 : ϱ p.2 ≤ R * Real.sqrt (5 * ν / 6) := not_lt.1 hp
      linarith
    have hO : IsOpen {x : ℝ × Space | ϱ x.2 < R * Real.sqrt ν} :=
      isOpen_lt (continuous_ϱ.comp continuous_snd) continuous_const
    have hev : (fun x : ℝ × Space => wardXr ν μ R c χy g x.1 x.2) =ᶠ[𝓝 p]
        (fun _ : ℝ × Space => (0 : Space)) := by
      filter_upwards [hO.mem_nhds (show p ∈ {x : ℝ × Space | ϱ x.2 < R * Real.sqrt ν} from hlt)]
        with x hx
      have hx' : ϱ x.2 < R * Real.sqrt ν := hx
      have h0 : 0 ≤ ϱ x.2 := ϱ_nonneg x.2
      have hs2 : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt hν.le
      have hm := mul_le_mul hx'.le hx'.le h0 (mul_nonneg hR.le (Real.sqrt_nonneg ν))
      have he : (R * Real.sqrt ν) * (R * Real.sqrt ν) = ν * R ^ 2 := by
        rw [show (R * Real.sqrt ν) * (R * Real.sqrt ν) = R ^ 2 * Real.sqrt ν ^ 2 by ring, hs2]
        ring
      have hsq : ϱ x.2 ^ 2 ≤ ν * R ^ 2 := by nlinarith [hm, he]
      exact wardXr_eq_zero_of_sq_le (ν := ν) (μ := μ) (R := R) (c := c) hχy g x.1 hsq
    exact contDiffAt_const.congr_of_eventuallyEq hev

end UnforcedLeray.Short.PartIIIb.Concrete
