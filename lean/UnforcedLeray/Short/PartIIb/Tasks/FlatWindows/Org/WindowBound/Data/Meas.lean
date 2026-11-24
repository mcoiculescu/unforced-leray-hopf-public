import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_7_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelMeasurable.Periodic

/-!
# `PartII-b:T13/1/7/1/1`: measurability of the window data (`WbdDMeas`)

Source: `the November 2 reference manuscript` lines 1928-1933.

The cutoff vanishes off `[a/2, 4a]`, and so does its derivative. On `{s > 0}` the `H_r`
representatives of `b` and `G` (`exists_periodic_rep`) agree with them volume-a.e., so both window
profiles agree a.e. with functions built from the strongly measurable representatives.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

open UnforcedLeray.Short.IIb

/-- Off `[a/2, 4a]` the cutoff and its derivative vanish. -/
theorem wbdm_zero_off {M a : ℝ} (ha : 0 < a) (hcut : WinCutBd M) {s : ℝ}
    (hs : s ∉ Icc (a / 2) (4 * a)) : winCut a s = 0 ∧ deriv (winCut a) s = 0 := by
  have hns : s ∉ tsupport (winCut a) := fun h => hs ((hcut a ha).2.2.1 h)
  exact ⟨image_eq_zero_of_notMem_tsupport hns, deriv_of_notMem_tsupport hns⟩

/-- Component of a measurable `CMerid`-valued function is measurable. -/
theorem wbdm_coord_meas {f : Coord → CMerid} (hf : Measurable f) (i : Fin 2) :
    Measurable (fun x => f x i) :=
  (EuclideanSpace.proj i).continuous.measurable.comp hf

theorem wbddMeas : UnforcedLeray.Short.IIb.WbdDMeas := by
  unfold UnforcedLeray.Short.IIb.WbdDMeas
  intro M hM0 hcut c r hc h1 h3 μ G b hG hb a ha i
  obtain ⟨G', hG's, hGa⟩ := exists_periodic_rep (a := r / 2 - 5 / 2) hc hG.periodic
    (hG.meas : AEStronglyMeasurable G (UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)))
  obtain ⟨b', hb's, hba⟩ := exists_periodic_rep (a := r / 2 - 5 / 2) hc hb.periodic
    (hb.meas : AEStronglyMeasurable b (UnforcedLeray.Axi.ageμ c (r / 2 - 5 / 2)))
  have hcont : Continuous (winCut a) := ((hcut a ha).1).continuous
  have hw : Measurable (fun x : Coord => winCut a x.1) :=
    hcont.measurable.comp measurable_fst
  have hd : Measurable (fun x : Coord => deriv (winCut a) x.1) :=
    ((hcut a ha).1.continuous_deriv (by simp)).measurable.comp measurable_fst
  have hwq : Measurable (fun x : Coord => winCut a x.1 / x.1) :=
    hw.div measurable_fst
  have hb'i : ∀ j : Fin 2, Measurable (fun x => b' x j) := fun j =>
    wbdm_coord_meas hb's.measurable j
  have hG'i : ∀ j : Fin 2, Measurable (fun x => G' x j) := fun j =>
    wbdm_coord_meas hG's.measurable j
  constructor
  · -- windowProfile a b x i
    have hm : Measurable (fun x : Coord => (winCut a x.1 : ℂ) * b' x i) :=
      (Complex.measurable_ofReal.comp hw).mul (hb'i i)
    have hae : (fun x => windowProfile a b x i) =ᵐ[volume]
        (fun x : Coord => (winCut a x.1 : ℂ) * b' x i) := by
      filter_upwards [hba] with x hx
      by_cases hpos : 0 < x.1
      · have hbx := hx hpos
        simp only [windowProfile, PiLp.smul_apply, smul_eq_mul, hbx]
      · have hs : x.1 ∉ Icc (a / 2) (4 * a) := fun h => hpos (lt_of_lt_of_le
          (by linarith) h.1)
        simp only [windowProfile, PiLp.smul_apply, smul_eq_mul,
          (wbdm_zero_off ha hcut hs).1, Complex.ofReal_zero, zero_mul]
    exact hm.aestronglyMeasurable.congr hae.symm
  · -- windowSource a μ G b x i
    have hm : Measurable (fun x : Coord =>
        ((winCut a x.1 / x.1 : ℝ) : ℂ) * (G' x i - μ * b' x i) +
          ((deriv (winCut a) x.1 : ℝ) : ℂ) * b' x i) :=
      ((Complex.measurable_ofReal.comp hwq).mul
        ((hG'i i).sub ((hb'i i).const_mul μ))).add
        ((Complex.measurable_ofReal.comp hd).mul (hb'i i))
    have hae : (fun x => windowSource a μ G b x i) =ᵐ[volume]
        (fun x : Coord => ((winCut a x.1 / x.1 : ℝ) : ℂ) * (G' x i - μ * b' x i) +
          ((deriv (winCut a) x.1 : ℝ) : ℂ) * b' x i) := by
      filter_upwards [hGa, hba] with x hxG hxb
      by_cases hpos : 0 < x.1
      · have hGx := hxG hpos
        have hbx := hxb hpos
        simp only [windowSource, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
          hGx, hbx]
      · have hs : x.1 ∉ Icc (a / 2) (4 * a) := fun h => hpos (lt_of_lt_of_le
          (by linarith) h.1)
        obtain ⟨h0, h0'⟩ := wbdm_zero_off ha hcut hs
        simp only [windowSource, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
          h0, h0', zero_div, Complex.ofReal_zero, zero_mul, zero_add]
    exact hm.aestronglyMeasurable.congr hae.symm

#print axioms wbddMeas
