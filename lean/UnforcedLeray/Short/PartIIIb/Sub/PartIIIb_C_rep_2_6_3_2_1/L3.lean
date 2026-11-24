import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.D
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S1a

/-!
# `extIntMeasurable` (`PartIII-b:C/rep/2/6/3/2/1/3`)

Source `the November 2 reference manuscript` lines 3611-3626.
On `{h > 0}` the kernel `Kd` is the everywhere-measurable `gh`-combination `gk` (`gkerD` is the
`if`-guarded directional derivative used in `gkerG_measurable`).  The shifted integrand is
`S.indicator W ∘ (s,z) ↦ (t-s,z)` with `S = Ioi 0 ×ˢ univ`.  For `kdDh` the integrand is a
pointwise limit of the difference quotients `(u_n)⁻¹ (Kd(h+u_n) - Kd(h))` with `u_n = 1/(n+1)`,
each measurable, converging by `gkerHasDerivH` (`h > 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The everywhere-measurable version of the `h`-kernel (`gkerD` carries the `if 0 < ν(1-e^{-h})`
guard, which is harmless on `{h > 0}`). -/
def gh (ν : ℝ) (m : ℂ) (i j k : Fin 3) (y : Space) (p : ℝ × Space) : ℂ :=
  Complex.exp (-(m + 3 / 2) * (p.1 : ℂ)) * ((gkerD ν i j k y p : ℝ) : ℂ)

theorem gh_measurable (ν : ℝ) (m : ℂ) (i j k : Fin 3) (y : Space) :
    Measurable (gh ν m i j k y) := by
  have hJ : HeatLerayJointMeas :=
    heatLerayJointMeas_of (heatLerayScale_of heatGTailScale) heatLerayKSmooth
  have hQ : Measurable (fun p : ℝ × Space =>
      (ν * (1 - Real.exp (-p.1)), y - Real.exp (-p.1 / 2) • p.2)) := by
    fun_prop
  have hS1 := (hJ i j 1 (by norm_num)).comp_measurable hQ
  have hc : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Space) ℝ =>
      A (fun _ => UnforcedLeray.coordinateVector k)) := continuous_eval_const _
  have hD : Measurable (gkerD ν i j k y) := (hc.comp_stronglyMeasurable hS1).measurable
  unfold gh
  refine (Complex.continuous_exp.measurable.comp ?_).mul (Complex.measurable_ofReal.comp hD)
  exact (by fun_prop : Continuous fun p : ℝ × Space => -(m + 3 / 2) * (p.1 : ℂ)).measurable

theorem gh_eq (ν : ℝ) (hν : 0 < ν) (m : ℂ) (i j k : Fin 3) (y : Space) (p : ℝ × Space)
    (hp : 0 < p.1) : gh ν m i j k y p = Gker ν m p.1 y p.2 i j k := by
  have hlt : Real.exp (-p.1) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < ν * (1 - Real.exp (-p.1)) := mul_pos hν (by linarith)
  simp only [gh, gkerD, Gker, if_pos hpos, iteratedFDeriv_one_apply]

/-- `Kd` on `{h > 0}` written with the measurable `gh`. -/
def gk (ν μ : ℝ) (i j k : Fin 3) (y : Space) (p : ℝ × Space) : ℂ :=
  gh ν (μ : ℂ) i j k y p - gh ν ((μ : ℂ) + 1) i j k y p

theorem gk_measurable (ν μ : ℝ) (i j k : Fin 3) (y : Space) : Measurable (gk ν μ i j k y) :=
  (gh_measurable ν (μ : ℂ) i j k y).sub (gh_measurable ν ((μ : ℂ) + 1) i j k y)

theorem gk_eq (ν : ℝ) (hν : 0 < ν) (μ : ℝ) (i j k : Fin 3) (y : Space) (p : ℝ × Space)
    (hp : 0 < p.1) : gk ν μ i j k y p = Kd ν μ p.1 y p.2 i j k := by
  unfold gk Kd
  rw [gh_eq ν hν (μ : ℂ) i j k y p hp, gh_eq ν hν ((μ : ℂ) + 1) i j k y p hp]

/-- The positive-`h` half-space as a subset of `ℝ × Space`. -/
abbrev Spos : Set (ℝ × Space) := Ioi (0 : ℝ) ×ˢ (univ : Set Space)

theorem Spos_measurable : MeasurableSet Spos := measurableSet_Ioi.prod MeasurableSet.univ

/-- Pointwise form of the shifted integrand as an indicator on `Spos`. -/
theorem extInt_eq_ind (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (t : ℝ) (y : Space) (i : Fin 3)
    (p : ℝ × Space) :
    extInt T Φ t y i p = Spos.indicator (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
      Φ q.1 y q.2 i j k * ((T (t - q.1) q.2 j k : ℝ) : ℂ)) (t - p.1, p.2) := by
  rcases p with ⟨s, z⟩
  by_cases hs : s < t
  · have h1 : s ∈ Iio t := hs
    have h2 : (t - s, z) ∈ Spos := ⟨sub_pos.mpr hs, mem_univ _⟩
    rw [Set.indicator_of_mem h2]
    simp only [extInt, Set.indicator_of_mem h1, sub_sub_cancel]
  · have h1 : s ∉ Iio t := fun h => hs h
    have h3 : (t - s, z) ∉ Spos := fun h => by
      have := h.1
      simp only [mem_Ioi] at this
      linarith
    rw [Set.indicator_of_notMem h3]
    simp only [extInt, Set.indicator_of_notMem h1]

theorem sumT_measurable (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : IIIa.IsSepSource P rOut T)
    (t : ℝ) (G : Fin 3 → Fin 3 → ℝ × Space → ℂ) (hG : ∀ j k, Measurable (G j k)) :
    Measurable (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
      G j k q * ((T (t - q.1) q.2 j k : ℝ) : ℂ)) := by
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  refine Measurable.mul (hG j k) ?_
  exact Complex.measurable_ofReal.comp
    ((hT.measurable j k).comp (by fun_prop : Measurable fun q : ℝ × Space => (t - q.1, q.2)))


/-- The `n`-th difference quotient step `u_n = 1/(n+1)`. -/
def uN (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem uN_pos (n : ℕ) : 0 < uN n := by unfold uN; positivity

theorem uN_tendsto : Tendsto uN atTop (𝓝[≠] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n => (uN_pos n).ne'⟩

/-- The `n`-th difference quotient of the shifted kernel integrand. -/
def dnq (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (ν μ t : ℝ) (y : Space) (i : Fin 3)
    (n : ℕ) (q : ℝ × Space) : ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3, ((uN n)⁻¹ • (gk ν μ i j k y (q.1 + uN n, q.2) - gk ν μ i j k y q)) *
    ((T (t - q.1) q.2 j k : ℝ) : ℂ)

theorem dnq_measurable (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : IIIa.IsSepSource P rOut T) (ν μ t : ℝ) (y : Space) (i : Fin 3) (n : ℕ) :
    Measurable (dnq T ν μ t y i n) := by
  unfold dnq
  refine sumT_measurable P rOut T hT t _ fun j k => ?_
  have hm : Measurable (fun q : ℝ × Space => gk ν μ i j k y (q.1 + uN n, q.2) - gk ν μ i j k y q) :=
    ((gk_measurable ν μ i j k y).comp
      (by fun_prop : Measurable fun q : ℝ × Space => (q.1 + uN n, q.2))).sub
        (gk_measurable ν μ i j k y)
  exact hm.const_smul ((uN n)⁻¹)

theorem gk_slope (ν : ℝ) (hν : 0 < ν) (μ : ℝ) (i j k : Fin 3) (y : Space) (q : ℝ × Space)
    (hq : 0 < q.1) :
    Tendsto (fun n : ℕ => (uN n)⁻¹ • (gk ν μ i j k y (q.1 + uN n, q.2) - gk ν μ i j k y q))
      atTop (𝓝 (kdDh ν μ q.1 y q.2 i j k)) := by
  have h1 := gkerHasDerivH ν (μ : ℂ) hν q.1 hq y q.2 i j k
  have h2 := gkerHasDerivH ν ((μ : ℂ) + 1) hν q.1 hq y q.2 i j k
  have hd : HasDerivAt (fun h' => Kd ν μ h' y q.2 i j k) (kdDh ν μ q.1 y q.2 i j k) q.1 :=
    (h1.sub h2).differentiableAt.hasDerivAt
  have hs := (hasDerivAt_iff_tendsto_slope_zero.mp hd).comp uN_tendsto
  refine Tendsto.congr (fun n => ?_) hs
  have hp : 0 < q.1 + uN n := by linarith [uN_pos n]
  show (uN n)⁻¹ • (Kd ν μ (q.1 + uN n) y q.2 i j k - Kd ν μ q.1 y q.2 i j k) =
    (uN n)⁻¹ • (gk ν μ i j k y (q.1 + uN n, q.2) - gk ν μ i j k y q)
  rw [gk_eq ν hν μ i j k y (q.1 + uN n, q.2) hp, gk_eq ν hν μ i j k y q hq]


/-- **(C) Measurability of the shifted integrands** (source 3611-3626). -/
theorem extIntMeasurable : ExtIntMeasurable := by
  intro ν μ rOut P T hD y i
  obtain ⟨hν, hμ, hr, hP, hT, hM⟩ := hD
  have hψm : ∀ t : ℝ, Measurable (fun p : ℝ × Space => (t - p.1, p.2)) := fun t => by fun_prop
  constructor
  · intro t
    have hW : Measurable (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
        gk ν μ i j k y q * ((T (t - q.1) q.2 j k : ℝ) : ℂ)) :=
      sumT_measurable P rOut T hT t _ fun j k => gk_measurable ν μ i j k y
    have hind : Spos.indicator (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
        Kd ν μ q.1 y q.2 i j k * ((T (t - q.1) q.2 j k : ℝ) : ℂ)) =
        Spos.indicator (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
          gk ν μ i j k y q * ((T (t - q.1) q.2 j k : ℝ) : ℂ)) := by
      funext q
      by_cases hq : q ∈ Spos
      · have hq1 : 0 < q.1 := hq.1
        have key : ∀ a b c : Fin 3, gk ν μ a b c y q = Kd ν μ q.1 y q.2 a b c :=
          fun a b c => gk_eq ν hν μ a b c y q hq1
        simp only [Set.indicator_of_mem hq, key]
      · simp only [Set.indicator_of_notMem hq]
    have hfun : extInt T (Kd ν μ) t y i =
        fun p : ℝ × Space => Spos.indicator (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
          gk ν μ i j k y q * ((T (t - q.1) q.2 j k : ℝ) : ℂ)) (t - p.1, p.2) := by
      funext p
      rw [extInt_eq_ind, hind]
    rw [hfun]
    exact ((hW.indicator Spos_measurable).comp (hψm t)).aestronglyMeasurable
  · intro t
    have hpt : ∀ p : ℝ × Space, extInt T (kdDh ν μ) t y i p =
        Spos.indicator (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
          kdDh ν μ q.1 y q.2 i j k * ((T (t - q.1) q.2 j k : ℝ) : ℂ)) (t - p.1, p.2) :=
      fun p => extInt_eq_ind T (kdDh ν μ) t y i p
    have hlim : ∀ q : ℝ × Space, Tendsto (fun n : ℕ => Spos.indicator (dnq T ν μ t y i n) q)
        atTop (𝓝 (Spos.indicator (fun q : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
          kdDh ν μ q.1 y q.2 i j k * ((T (t - q.1) q.2 j k : ℝ) : ℂ)) q)) := by
      intro q
      by_cases hq : q ∈ Spos
      · have hq1 : 0 < q.1 := hq.1
        simp only [Set.indicator_of_mem hq, dnq]
        apply tendsto_finset_sum
        intro j _
        apply tendsto_finset_sum
        intro k _
        exact (gk_slope ν hν μ i j k y q hq1).mul_const _
      · simp only [Set.indicator_of_notMem hq]
        exact tendsto_const_nhds
    have hQm : ∀ n : ℕ, Measurable (fun p : ℝ × Space =>
        Spos.indicator (dnq T ν μ t y i n) (t - p.1, p.2)) := fun n =>
      ((dnq_measurable P rOut T hT ν μ t y i n).indicator Spos_measurable).comp (hψm t)
    have hSM : StronglyMeasurable (fun p : ℝ × Space => extInt T (kdDh ν μ) t y i p) :=
      stronglyMeasurable_of_tendsto (u := atTop)
        (f := fun n (p : ℝ × Space) => Spos.indicator (dnq T ν μ t y i n) (t - p.1, p.2))
        (g := fun p : ℝ × Space => extInt T (kdDh ν μ) t y i p)
        (fun n => (hQm n).stronglyMeasurable)
        (tendsto_pi_nhds.2 fun (p : ℝ × Space) => by
          show Tendsto (fun n : ℕ => Spos.indicator (dnq T ν μ t y i n) (t - p.1, p.2)) atTop
            (𝓝 (extInt T (kdDh ν μ) t y i p))
          rw [hpt p]
          exact hlim (t - p.1, p.2))
    exact hSM.aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
