import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XDiff.Zfield
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T9

/-!
# The phase derivative of the outward primitive is differentiable in `y`
(source 4176-4214, 4181-4192)

Source of record: `the November 2 reference manuscript` (73 pages).

For a separated source `T` with finite `Y₂` moment, `Z = X₀ = sepX0`, `Z' = ∂_τ Z`, the primitive
`Ψ_{Z'}(r, z) = -∫_r^∞ ρ Z'_z(ρ, 0, z) dρ` (the `τ`-derivative of `Ψ_Z`, `tcr_outPrim_tau`) has
partial derivatives `∂_rΨ_{Z'} = r Z'_z` (fundamental theorem of calculus) and
`∂_zΨ_{Z'} = -r Z'_r`: the latter from `∂_zΨ_Z(τ,·) = -r Z_r(τ,·)` (`outPrimDerivZ`), integrated over
a `z`-interval and differentiated in the phase under the integral (the phase derivative `Z'` is
bounded uniformly in the phase on compact pieces of the half plane, by the free equation and
`tcd_X0_bound`).  Both partials are continuous, hence `Ψ_{Z'}` is differentiable in `(r, z)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem xd_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)

/-! ## 1. A phase-uniform bound for `∂_τX₀` on compact pieces of the half plane -/

theorem xd_Zd_bound {ν μ rOut P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hr : 0 ≤ rOut) (hP : 0 < P)
    (hT : IIIa.IsSepSource P rOut T) (hM : SepMoment P T) (r K : ℝ) (hr' : rOut < r) :
    ∃ B : ℝ, ∀ (t s : ℝ), |s| ≤ K →
      ‖deriv (fun u => sepX0 ν μ T u (!₂[r, 0, s] : Space)) t‖ ≤ B := by
  obtain ⟨C, hC0, hb⟩ := tcd_X0_bound hν hμ hr hP hT hM
  have hr0 : 0 ≤ r := hr.trans hr'.le
  have hD : 0 < r - rOut := by linarith
  set D : ℝ := r - rOut with hDdef
  refine ⟨‖reL‖ * (C * D ^ (-(5 / 2 : ℝ))) + 1 / 2 * (C * D ^ (-(5 / 2 : ℝ) - 1) * (r + K)) +
    ν * (3 * (C * D ^ (-(5 / 2 : ℝ) - 2))) + |μ + 1 - 1 / 2| * (C * D ^ (-(5 / 2 : ℝ))), ?_⟩
  intro t s hs
  set p : Space := (!₂[r, 0, s] : Space) with hp
  have hϱ : ϱ p = r := tcd_varrho hr0
  have hy : rOut < ϱ p := by rw [hϱ]; exact hr'
  obtain ⟨hj, hW⟩ := hb t p hy
  rw [hϱ] at hj hW
  have hcd : ContDiffAt ℝ 2 (sepX0 ν μ T t) p := tcd_X0_cd hν hμ hr hP hT hM t hy
  have a0 : ‖sepX0 ν μ T t p‖ ≤ C * D ^ (-(5 / 2 : ℝ)) := by
    have := hj 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at this
    simpa using this
  have a1 : ‖fderiv ℝ (sepX0 ν μ T t) p‖ ≤ C * D ^ (-(5 / 2 : ℝ) - 1) := by
    have := hj 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at this
    simpa using this
  have a2 : ‖iteratedFDeriv ℝ 2 (sepX0 ν μ T t) p‖ ≤ C * D ^ (-(5 / 2 : ℝ) - 2) := by
    have := hj 2 (by norm_num)
    simpa using this
  have hpn : ‖p‖ ≤ r + K := (tcd_norm_pt r s hr0).trans (by linarith)
  have hWb : ‖sepWre ν μ T t p‖ ≤ ‖reL‖ * (C * D ^ (-(5 / 2 : ℝ))) := by
    have : sepWre ν μ T t p = reL (IIIa.sepW ν (μ : ℂ) T p t) := rfl
    rw [this]
    exact (reL.le_opNorm _).trans (mul_le_mul_of_nonneg_left hW (norm_nonneg _))
  have hGb : ‖fderiv ℝ (sepX0 ν μ T t) p p‖ ≤ C * D ^ (-(5 / 2 : ℝ) - 1) * (r + K) :=
    ((fderiv ℝ (sepX0 ν μ T t) p).le_opNorm p).trans
      (mul_le_mul a1 hpn (norm_nonneg _) (by positivity))
  have hLb : ‖physLap (sepX0 ν μ T t) p‖ ≤ 3 * (C * D ^ (-(5 / 2 : ℝ) - 2)) :=
    (tcd_physLap_norm hcd).trans (by linarith)
  rw [tcd_freeEq hν hμ hr hP hT hM t hy]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hWb ?_)) ?_)) ?_)
  · rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact mul_le_mul_of_nonneg_left hGb (by norm_num)
  · rw [norm_smul, Real.norm_of_nonneg hν.le]
    exact mul_le_mul_of_nonneg_left hLb hν.le
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left a0 (abs_nonneg _)

/-! ## 2. The fundamental theorem of calculus for the tail primitive -/

theorem xd_primR_deriv {F : ℝ → ℝ} {c : ℝ} (hc : ContinuousOn F (Ioi c))
    (hi : ∀ a, c < a → IntegrableOn F (Ioi a)) {r : ℝ} (hr : c < r) :
    HasDerivAt (fun r' => -∫ ρ in Ioi r', F ρ) (F r) r := by
  obtain ⟨a, hca, har⟩ : ∃ a : ℝ, c < a ∧ a < r := ⟨(c + r) / 2, by linarith, by linarith⟩
  have hrm : r ∈ Ioi c := hr
  have hFi := hi a hca
  have hout : ∀ r' : ℝ, a < r' →
      -∫ ρ in Ioi r', F ρ = -(∫ ρ in Ioi a, F ρ) + ∫ ρ in a..r', F ρ := by
    intro r' hr'
    have hsplit : ∫ ρ in Ioi a, F ρ = (∫ ρ in Ioc a r', F ρ) + ∫ ρ in Ioi r', F ρ := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hr'.le]
      refine setIntegral_union ?_ measurableSet_Ioi ?_ ?_
      · exact Set.disjoint_left.2 fun x hx hx' => absurd hx' (not_lt.2 hx.2)
      · exact hFi.mono_set fun x hx => hx.1
      · exact hFi.mono_set fun x hx => lt_trans hr' hx
    rw [intervalIntegral.integral_of_le hr'.le, hsplit]
    ring
  have hint : IntervalIntegrable F volume a r := by
    refine ContinuousOn.intervalIntegrable (hc.mono ?_)
    rw [Set.uIcc_of_le (le_of_lt har)]
    intro x hx
    exact lt_of_lt_of_le hca hx.1
  have hmeas : StronglyMeasurableAtFilter F (nhds r) volume :=
    hc.stronglyMeasurableAtFilter isOpen_Ioi r hrm
  have hcont := hc.continuousAt (isOpen_Ioi.mem_nhds hrm)
  have hI : HasDerivAt (fun u => ∫ ρ in a..u, F ρ) (F r) r :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  have hderiv := hI.const_add (-(∫ ρ in Ioi a, F ρ))
  refine hderiv.congr_of_eventuallyEq ?_
  exact Filter.eventually_of_mem (Ioi_mem_nhds har) (fun r' hr' => hout r' hr')

/-! ## 3. The context -/

section Ctx

variable {ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}

/-- The two partial derivatives of the primitive of `X₀` at every phase. -/
theorem xd_hdr (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hR : 0 < R) (hP : 0 < P)
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (haxi : AxiNoSwirlOn (youngOpen ν R) (sepX0 ν μ T)) (τ : ℝ) :
    ∀ r z, R * Real.sqrt (5 * ν / 6) < r →
      HasDerivAt (fun r' => outPrim (sepX0 ν μ T) τ r' z)
        (r * sepX0 ν μ T τ !₂[r, 0, z] 2) r ∧
      HasDerivAt (fun z' => outPrim (sepX0 ν μ T) τ r z')
        (-(r * sepX0 ν μ T τ !₂[r, 0, z] 0)) z := by
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hcdOn : ContDiffOn ℝ 2 (sepX0 ν μ T τ) (youngOpen ν R) :=
    (xd_X0_top hν hμ hr0 hP hT hM τ).of_le (xd_le_top 2)
  have hdec := tcr_streamDecay hν hμ hR hP hT hM τ
  have hdiv : ∀ y' ∈ youngOpen ν R, ∑ j : Fin 3, physPd (sepX0 ν μ T τ) j y' j = 0 :=
    fun y' hy' => tcr_divFree hν hμ hr0 hP hT hM τ hy'
  intro r z hr
  exact ⟨outPrimDerivR ν R (sepX0 ν μ T) τ hcdOn hdec r z hr,
    outPrimDerivZ ν R (sepX0 ν μ T) τ hcdOn hdiv haxi hdec r z hr⟩

/-- Continuity of `∂_τX₀` on the young region. -/
theorem xd_Zd_contOn (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hR : 0 < R) (hP : 0 < P)
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T) (τ : ℝ) :
    ContinuousOn (fun y => deriv (fun t => sepX0 ν μ T t y) τ) (youngOpen ν R) := by
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  exact (xd_Zd_diffOn hν hμ hr0 hP hT hM τ).continuousOn

/-- **`∂_zΨ_{∂_τX₀} = -r (∂_τX₀)_r`.** -/
theorem xd_primZ (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hR : 0 < R) (hP : 0 < P)
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (haxi : AxiNoSwirlOn (youngOpen ν R) (sepX0 ν μ T)) (τ r z : ℝ)
    (hr : R * Real.sqrt (5 * ν / 6) < r) :
    HasDerivAt (fun z' => outPrim (fun t y' => deriv (fun s => sepX0 ν μ T s y') t) τ r z')
      (-(r * deriv (fun s => sepX0 ν μ T s (!₂[r, 0, z] : Space)) τ 0)) z := by
  set rO : ℝ := R * Real.sqrt (5 * ν / 6) with hrO
  have hr0 : 0 ≤ rO := by positivity
  have hr0' : 0 ≤ r := hr0.trans hr.le
  have hpt : Continuous (fun s : ℝ => (!₂[r, 0, s] : Space)) := by fun_prop
  have hmaps : ∀ s : ℝ, (!₂[r, 0, s] : Space) ∈ youngOpen ν R := by
    intro s
    show rO < ϱ (!₂[r, 0, s] : Space)
    rw [tcd_varrho hr0']; exact hr
  have hcdOn : ∀ t, ContinuousOn (sepX0 ν μ T t) (youngOpen ν R) := fun t =>
    (xd_X0_top hν hμ hr0 hP hT hM t).continuousOn
  have hAc : ∀ t, Continuous (fun s : ℝ => sepX0 ν μ T t (!₂[r, 0, s] : Space) 0) := fun t =>
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp
      ((hcdOn t).comp_continuous hpt hmaps)
  have hdz := fun t s => (xd_hdr hν hμ hR hP hT hM haxi t r s hr).2
  have hΨ : ∀ (t h : ℝ), outPrim (sepX0 ν μ T) t r (z + h) - outPrim (sepX0 ν μ T) t r z =
      ∫ s in z..z + h, (-(r * sepX0 ν μ T t (!₂[r, 0, s] : Space) 0)) := by
    intro t h
    symm
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hdz t s)
      (((hAc t).const_mul r).neg.intervalIntegrable _ _)
  have hΨt : ∀ s : ℝ, HasDerivAt (fun t => outPrim (sepX0 ν μ T) t r s)
      (outPrim (fun t y' => deriv (fun u => sepX0 ν μ T u y') t) τ r s) τ := by
    intro s
    have h := tcr_outPrim_tau hν hμ hr0 hP hT hM τ (y := (!₂[r, 0, s] : Space)) (hmaps s)
    have e1 : ϱ (!₂[r, 0, s] : Space) = r := tcd_varrho hr0'
    have e2 : (!₂[r, 0, s] : Space) 2 = s := by simp
    rw [e1, e2] at h
    exact h
  have hZdc : Continuous (fun s : ℝ =>
      deriv (fun u => sepX0 ν μ T u (!₂[r, 0, s] : Space)) τ 0) :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp
      ((xd_Zd_contOn hν hμ hR hP hT hM τ).comp_continuous hpt hmaps)
  have hEq : ∀ h : ℝ, outPrim (fun t y' => deriv (fun u => sepX0 ν μ T u y') t) τ r (z + h) -
      outPrim (fun t y' => deriv (fun u => sepX0 ν μ T u y') t) τ r z =
      ∫ s in z..z + h, (-(r * deriv (fun u => sepX0 ν μ T u (!₂[r, 0, s] : Space)) τ 0)) := by
    intro h
    obtain ⟨B, hB⟩ := xd_Zd_bound hν hμ hr0 hP hT hM r (|z| + |h|) hr
    have hsub : ∀ s ∈ Set.uIoc z (z + h), |s| ≤ |z| + |h| := by
      intro s hs
      have hs' : s ∈ Set.uIoc z (z + h) := hs
      rw [Set.uIoc, Set.mem_Ioc] at hs'
      have h1 : min z (z + h) < s := hs'.1
      have h2 : s ≤ max z (z + h) := hs'.2
      rw [abs_le]
      constructor
      · have : min z (z + h) ≥ -(|z| + |h|) := by
          rw [ge_iff_le, le_min_iff]
          constructor <;> linarith [neg_abs_le z, neg_abs_le h, le_abs_self h]
        linarith
      · have : max z (z + h) ≤ |z| + |h| := by
          rw [max_le_iff]
          constructor <;> linarith [le_abs_self z, le_abs_self h, neg_abs_le h]
        linarith
    have hder := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := z) (b := z + h)
      (F := fun t s => -(r * sepX0 ν μ T t (!₂[r, 0, s] : Space) 0))
      (F' := fun t s => -(r * deriv (fun u => sepX0 ν μ T u (!₂[r, 0, s] : Space)) t 0))
      (x₀ := τ) (s := Set.univ) (bound := fun _ => r * |B|) Filter.univ_mem
      (Filter.Eventually.of_forall fun t => ((hAc t).const_mul r).neg.aestronglyMeasurable)
      (((hAc τ).const_mul r).neg.intervalIntegrable _ _)
      (by
        have : Continuous (fun s : ℝ =>
            -(r * deriv (fun u => sepX0 ν μ T u (!₂[r, 0, s] : Space)) τ 0)) :=
          (hZdc.const_mul r).neg
        exact this.aestronglyMeasurable)
      (by
        refine Filter.Eventually.of_forall fun s hs t _ => ?_
        have hb := hB t s (hsub s hs)
        have hc : |deriv (fun u => sepX0 ν μ T u (!₂[r, 0, s] : Space)) t 0| ≤ |B| := by
          have := PiLp.norm_apply_le
            (deriv (fun u => sepX0 ν μ T u (!₂[r, 0, s] : Space)) t) 0
          rw [Real.norm_eq_abs] at this
          exact this.trans (hb.trans (le_abs_self B))
        rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_of_nonneg hr0']
        exact mul_le_mul_of_nonneg_left hc hr0')
      intervalIntegrable_const
      (by
        refine Filter.Eventually.of_forall fun s _ t _ => ?_
        have hy := hmaps s
        have hd := tcr_hasDerivAt_tau hν hμ hr0 hP hT hM t (y := (!₂[r, 0, s] : Space)) hy
        have hc : HasDerivAt (fun u => sepX0 ν μ T u (!₂[r, 0, s] : Space) 0)
            (deriv (fun u => sepX0 ν μ T u (!₂[r, 0, s] : Space)) t 0) t :=
          (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hd
        exact (hc.const_mul r).neg)
    have hfun : (fun t => outPrim (sepX0 ν μ T) t r (z + h) - outPrim (sepX0 ν μ T) t r z) =
        fun t => ∫ s in z..z + h, (-(r * sepX0 ν μ T t (!₂[r, 0, s] : Space) 0)) :=
      funext fun t => hΨ t h
    have h1 : HasDerivAt (fun t => outPrim (sepX0 ν μ T) t r (z + h) -
        outPrim (sepX0 ν μ T) t r z)
        (outPrim (fun t y' => deriv (fun u => sepX0 ν μ T u y') t) τ r (z + h) -
          outPrim (fun t y' => deriv (fun u => sepX0 ν μ T u y') t) τ r z) τ :=
      (hΨt (z + h)).sub (hΨt z)
    rw [hfun] at h1
    exact h1.unique hder.2
  have hG : HasDerivAt (fun u => ∫ s in z..u,
      (-(r * deriv (fun v => sepX0 ν μ T v (!₂[r, 0, s] : Space)) τ 0)))
      (-(r * deriv (fun v => sepX0 ν μ T v (!₂[r, 0, z] : Space)) τ 0)) z := by
    have hc : Continuous (fun s : ℝ =>
        -(r * deriv (fun v => sepX0 ν μ T v (!₂[r, 0, s] : Space)) τ 0)) :=
      (hZdc.const_mul r).neg
    exact (hc.integral_hasStrictDerivAt z z).hasDerivAt
  have hfin := hG.const_add (outPrim (fun t y' => deriv (fun u => sepX0 ν μ T u y') t) τ r z)
  refine hfin.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  have := hEq (u - z)
  rw [add_sub_cancel] at this
  simp only
  linarith

/-- **`∂_τΨ_{X₀}` is differentiable in `y` on the young region.** -/
theorem xd_Psid_diffOn (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hR : 0 < R) (hP : 0 < P)
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (haxi : AxiNoSwirlOn (youngOpen ν R) (sepX0 ν μ T)) (τ : ℝ) :
    DifferentiableOn ℝ (fun y : Space =>
      outPrim (fun t y' => deriv (fun s => sepX0 ν μ T s y') t) τ (ϱ y) (y 2)) (youngOpen ν R) := by
  set rO : ℝ := R * Real.sqrt (5 * ν / 6) with hrO
  have hr0 : 0 ≤ rO := by positivity
  set Zd : ℝ → Space → Space := fun t y' => deriv (fun s => sepX0 ν μ T s y') t with hZd
  have hS : IsOpen {p : ℝ × ℝ | rO < p.1} := isOpen_lt continuous_const continuous_fst
  have hmapS : ∀ p : ℝ × ℝ, p ∈ {p : ℝ × ℝ | rO < p.1} →
      (!₂[p.1, 0, p.2] : Space) ∈ youngOpen ν R := by
    intro p hp
    have hp' : rO < p.1 := hp
    show rO < ϱ (!₂[p.1, 0, p.2] : Space)
    rw [tcd_varrho (hr0.trans hp'.le)]; exact hp'
  have hpc : Continuous (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space)) := by fun_prop
  have hZc : ContinuousOn (Zd τ) (youngOpen ν R) := xd_Zd_contOn hν hμ hR hP hT hM τ
  have hZcp : ContinuousOn (fun p : ℝ × ℝ => Zd τ (!₂[p.1, 0, p.2] : Space))
      {p : ℝ × ℝ | rO < p.1} := hZc.comp hpc.continuousOn hmapS
  have hPc : ContinuousOn (fun p : ℝ × ℝ => p.1 * Zd τ (!₂[p.1, 0, p.2] : Space) 2)
      {p : ℝ × ℝ | rO < p.1} :=
    continuousOn_fst.mul ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp_continuousOn
      hZcp)
  have hQc : ContinuousOn (fun p : ℝ × ℝ => -(p.1 * Zd τ (!₂[p.1, 0, p.2] : Space) 0))
      {p : ℝ × ℝ | rO < p.1} :=
    (continuousOn_fst.mul ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp_continuousOn
      hZcp)).neg
  have h1 : ∀ p ∈ {p : ℝ × ℝ | rO < p.1},
      HasDerivAt (fun r => outPrim Zd τ r p.2) (p.1 * Zd τ (!₂[p.1, 0, p.2] : Space) 2) p.1 := by
    intro p hp
    have hp' : rO < p.1 := hp
    have hc := tcr_cont_tau hν hμ hr0 hP hT hM τ p.2
    have hi : ∀ a, rO < a →
        IntegrableOn (fun ρ : ℝ => ρ * deriv (fun s => sepX0 ν μ T s (!₂[ρ, 0, p.2] : Space)) τ 2)
          (Ioi a) := by
      intro a ha
      obtain ⟨Cb, hCb, hb⟩ := tcd_half hν hμ hr0 hP hT hM ha
      have hint : Integrable (fun ρ : ℝ => Cb * (1 + |p.2|) * (ρ - rO) ^ (-(3 / 2 : ℝ)))
          (volume.restrict (Ioi a)) := (tcd_int_shift rO a (by linarith)).const_mul _
      refine Integrable.mono' hint ?_ ?_
      · exact (hc.mono (Ioi_subset_Ioi ha.le)).aestronglyMeasurable measurableSet_Ioi
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun ρ hρ => ?_)
        have := (hb τ ρ p.2 (le_of_lt hρ)).2.2.2.2.2
        rw [Real.norm_eq_abs]
        exact this
    have := xd_primR_deriv (F := fun ρ : ℝ =>
      ρ * deriv (fun s => sepX0 ν μ T s (!₂[ρ, 0, p.2] : Space)) τ 2) hc hi hp'
    exact this
  have h2 : ∀ p ∈ {p : ℝ × ℝ | rO < p.1},
      HasDerivAt (fun z => outPrim Zd τ p.1 z)
        (-(p.1 * Zd τ (!₂[p.1, 0, p.2] : Space) 0)) p.2 := by
    intro p hp
    exact xd_primZ hν hμ hR hP hT hM haxi τ p.1 p.2 hp
  have hD : ∀ p ∈ {p : ℝ × ℝ | rO < p.1}, DifferentiableAt ℝ (fun q : ℝ × ℝ => outPrim Zd τ q.1 q.2) p :=
    fun p hp => (t9_hasFDerivAt_of_partials _ hS (fun q : ℝ × ℝ => outPrim Zd τ q.1 q.2)
      (fun q : ℝ × ℝ => q.1 * Zd τ (!₂[q.1, 0, q.2] : Space) 2)
      (fun q : ℝ × ℝ => -(q.1 * Zd τ (!₂[q.1, 0, q.2] : Space) 0)) hPc hQc h1 h2 p hp
      ).differentiableAt
  have hϱ : DifferentiableOn ℝ (fun y : Space => ϱ y) (youngOpen ν R) :=
    ((contDiffOn_ϱ (k := 1)).mono (fun y hy => t9_not_axis hν hR hy)).differentiableOn (by simp)
  have hz2 : DifferentiableOn ℝ (fun y : Space => y 2) (youngOpen ν R) :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).differentiable.differentiableOn
  intro y hy
  have hyS : (ϱ y, y 2) ∈ {p : ℝ × ℝ | rO < p.1} := hy
  have hgy : DifferentiableWithinAt ℝ (fun y : Space => ((ϱ y, y 2) : ℝ × ℝ)) (youngOpen ν R) y :=
    (hϱ y hy).prodMk (hz2 y hy)
  have key : DifferentiableWithinAt ℝ ((fun q : ℝ × ℝ => outPrim Zd τ q.1 q.2) ∘
      (fun y : Space => ((ϱ y, y 2) : ℝ × ℝ))) (youngOpen ν R) y :=
    DifferentiableAt.comp_differentiableWithinAt y (hD _ hyS) hgy
  exact key

end Ctx

end UnforcedLeray.Short.PartIIIb.Concrete
