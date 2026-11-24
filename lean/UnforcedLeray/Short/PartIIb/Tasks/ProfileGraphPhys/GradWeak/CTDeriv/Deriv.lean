import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.CTDeriv.Smooth

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- Support bound in the `q`-variable on the support of a coordinate test. -/
theorem tsupport_q_bound {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ p ∈ tsupport φ, |p.2.1| ≤ Q := by
  have hK : IsCompact (tsupport φ) := hφ.compact.isCompact
  obtain ⟨Q0, hQ0⟩ := hK.isBounded.subset_closedBall (0 : Coord)
  refine ⟨max Q0 0, le_max_right _ _, fun p hp => ?_⟩
  have hn : ‖p‖ ≤ Q0 := by simpa using hQ0 hp
  have h := ((norm_fst_le p.2).trans ((norm_snd_le p).trans hn))
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-- A `cpd` (or radial combination) of `φ` vanishes off `tsupport φ`. -/
theorem fderiv_ne_zero_mem {φ : Coord → ℝ} {p : Coord} (h : fderiv ℝ φ p ≠ 0) :
    p ∈ tsupport φ :=
  support_fderiv_subset (𝕜 := ℝ) (f := φ) (show p ∈ Function.support (fderiv ℝ φ) from h)

theorem termR_local_finite_gen {c R a : ℝ} (hc : 0 < c) (hR : 0 < R) {ψ : Coord → ℝ} {Q : ℝ}
    (hq : ∀ p, ψ p ≠ 0 → |p.2.1| ≤ Q) {x0 : ℝ × Space} (hx0 : x0.2 ∉ Axi.axis) :
    ∃ N : Finset ℤ, ∀ᶠ x in 𝓝 x0, ∀ n ∉ N, termR c R a ψ n x = 0 := by
  have hcont := continuousAt_phase hR.ne' hx0
  set ξ0 := Axi.phase R x0.1 x0.2 with hξ0
  have hev : ∀ᶠ x in 𝓝 x0, |Axi.phase R x.1 x.2 - ξ0| < 1 := by
    have := hcont.preimage_mem_nhds (Metric.ball_mem_nhds ξ0 one_pos)
    filter_upwards [this] with x hx
    rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hx
    exact hx
  set K : ℝ := Q + |ξ0| + 1 with hK
  set M : ℤ := ⌈K / c⌉ with hM
  refine ⟨Finset.Icc (-M) M, ?_⟩
  filter_upwards [hev] with x hx
  intro n hn
  by_contra hne
  apply hn
  have hψne : ψ (Axi.age R x.2, (Axi.phase R x.1 x.2 + n * c, Axi.trans R x.2)) ≠ 0 := by
    intro h
    apply hne
    unfold termR
    rw [h, mul_zero]
  have hq' := hq _ hψne
  change |Axi.phase R x.1 x.2 + n * c| ≤ Q at hq'
  have hA := abs_le.1 hq'
  have hB := abs_lt.1 hx
  have hξ1 := le_abs_self ξ0
  have hξ2 := neg_abs_le ξ0
  have h1 : |(n : ℝ) * c| ≤ K := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |(n : ℝ)| ≤ K / c := by
    rw [le_div_iff₀ hc]
    have e : |(n : ℝ)| * c = |(n : ℝ) * c| := by rw [abs_mul, abs_of_pos hc]
    linarith
  have h3 : |(n : ℝ)| ≤ (M : ℝ) := h2.trans (Int.le_ceil _)
  have h4 : |n| ≤ M := by exact_mod_cast h3
  rw [Finset.mem_Icc]
  exact abs_le.1 h4

/-- The finite cell set realizing the periodization near a non-axis point. -/
theorem ctLift_eq_sum_of_fin {c ε a : ℝ} {ψ : Coord → ℝ} {S : Finset ℤ} {x0 : ℝ × Space}
    (h : ∀ᶠ x in 𝓝 x0, ∀ n ∉ S, termR c ε⁻¹ a ψ n x = 0) :
    ctLift c ε a ψ =ᶠ[𝓝 x0] fun x => ∑ n ∈ S, termR c ε⁻¹ a ψ n x := by
  filter_upwards [h] with x hx
  rw [ctLift_eq_tsum]
  exact tsum_eq_sum (fun n hn => hx n hn)

theorem fderiv_snd_apply {f : ℝ × Space → ℝ} {τ : ℝ} {y : Space}
    (hf : DifferentiableAt ℝ f (τ, y)) (w : Space) :
    fderiv ℝ f (τ, y) (0, w) = fderiv ℝ (fun y' => f (τ, y')) y w := by
  have h1 : HasFDerivAt (fun y' : Space => ((τ, y') : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have h2 := hf.hasFDerivAt.comp y h1
  rw [show (fun y' => f (τ, y')) = f ∘ (fun y' => (τ, y')) from rfl, h2.fderiv]
  simp

/-- The shift of the `q`-variable by the cell `n c`. -/
def shiftC (c : ℝ) (n : ℤ) (p : Coord) : Coord := (p.1, (p.2.1 + n * c, p.2.2))

theorem shiftC_hasFDerivAt (c : ℝ) (n : ℤ) (p : Coord) :
    HasFDerivAt (shiftC c n) (ContinuousLinearMap.id ℝ Coord) p := by
  have hfun : shiftC c n = fun q : Coord => id q + ((0 : ℝ), ((n : ℝ) * c, (0 : ℝ))) := by
    funext q
    rcases q with ⟨q1, q2, q3⟩
    simp [shiftC]
  rw [hfun]
  exact (hasFDerivAt_id p).add_const _

/-- The one-term profile `s ↦ s^a φ(shift)`, so that `termR` is `Fn` composed with the chart. -/
def Fn (a c : ℝ) (φ : Coord → ℝ) (n : ℤ) (p : Coord) : ℝ := p.1 ^ a * φ (shiftC c n p)

theorem Fn_differentiableAt {a c : ℝ} {φ : Coord → ℝ} (hφ : IsCoordTest φ) (n : ℤ) {p : Coord}
    (hp : 0 < p.1) : DifferentiableAt ℝ (Fn a c φ n) p := by
  have hpow : HasFDerivAt (fun q : Coord => q.1 ^ a) ((a * p.1 ^ (a - 1)) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (Real.hasDerivAt_rpow_const (p := a) (x := p.1) (Or.inl hp.ne')).comp_hasFDerivAt p hasFDerivAt_fst
  have hφd : DifferentiableAt ℝ (fun q => φ (shiftC c n q)) p :=
    ((hφ.smooth.differentiable (by simp)) _).comp p (shiftC_hasFDerivAt c n p).differentiableAt
  exact (hpow.differentiableAt).mul hφd

theorem fderiv_Fn {a c : ℝ} {φ : Coord → ℝ} (hφ : IsCoordTest φ) (n : ℤ) {p : Coord}
    (hp : 0 < p.1) (v : Coord) :
    fderiv ℝ (Fn a c φ n) p v =
      a * p.1 ^ (a - 1) * v.1 * φ (shiftC c n p) + p.1 ^ a * fderiv ℝ φ (shiftC c n p) v := by
  have hpow : HasFDerivAt (fun q : Coord => q.1 ^ a) ((a * p.1 ^ (a - 1)) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (Real.hasDerivAt_rpow_const (p := a) (x := p.1) (Or.inl hp.ne')).comp_hasFDerivAt p hasFDerivAt_fst
  have hφd : HasFDerivAt (fun q => φ (shiftC c n q))
      ((fderiv ℝ φ (shiftC c n p)).comp (ContinuousLinearMap.id ℝ Coord)) p :=
    ((hφ.smooth.differentiable (by simp)) _).hasFDerivAt.comp p (shiftC_hasFDerivAt c n p)
  have hF := hpow.mul hφd
  rw [show fderiv ℝ (Fn a c φ n) p = fderiv ℝ ((fun q : Coord => q.1 ^ a) * fun q => φ (shiftC c n q)) p
    from rfl, hF.fderiv]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem eR_decomp (y : Space) :
    Axi.eR y = (y 0 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • EuclideanSpace.single 0 1 +
      (y 1 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp [Axi.eR, Axi.ϱ, div_eq_inv_mul]


theorem mem_tsupport_of_ne {φ : Coord → ℝ} {p : Coord} (h : φ p ≠ 0 ∨ fderiv ℝ φ p ≠ 0) :
    p ∈ tsupport φ := by
  rcases h with h | h
  · exact subset_tsupport φ h
  · exact fderiv_ne_zero_mem h

theorem zero_of_nmem_tsupport {φ : Coord → ℝ} {p : Coord} (h : p ∉ tsupport φ) :
    φ p = 0 ∧ fderiv ℝ φ p = 0 :=
  ⟨by
    by_contra hne
    exact h (subset_tsupport φ hne), by
    by_contra hne
    exact h (fderiv_ne_zero_mem hne)⟩

theorem finite_of_tsupport {c R a : ℝ} (hc : 0 < c) (hR : 0 < R) {φ : Coord → ℝ}
    (hφ : IsCoordTest φ) {ψ : Coord → ℝ} (hψ : ∀ p, ψ p ≠ 0 → p ∈ tsupport φ)
    {x0 : ℝ × Space} (hx0 : x0.2 ∉ Axi.axis) :
    ∃ N : Finset ℤ, ∀ᶠ x in 𝓝 x0, ∀ n ∉ N, termR c R a ψ n x = 0 := by
  obtain ⟨Q, -, hQ⟩ := tsupport_q_bound hφ
  exact termR_local_finite_gen hc hR (fun p hp => hQ p (hψ p hp)) hx0

theorem fderiv_ctLift_eq_sum {c ε a : ℝ} (hR : 0 < ε⁻¹) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    {S : Finset ℤ} {x0 : ℝ × Space} (hx0 : x0.2 ∉ Axi.axis)
    (hS : ∀ᶠ x in 𝓝 x0, ∀ n ∉ S, termR c ε⁻¹ a φ n x = 0) (v : ℝ × Space) :
    fderiv ℝ (ctLift c ε a φ) x0 v = ∑ n ∈ S, fderiv ℝ (termR c ε⁻¹ a φ n) x0 v := by
  rw [(ctLift_eq_sum_of_fin hS).fderiv_eq]
  rw [fderiv_fun_sum (fun n _ => (termR_contDiffAt hR hφ n hx0).differentiableAt (by simp))]
  simp [ContinuousLinearMap.sum_apply]

theorem termR_fderiv_z {c R a : ℝ} (hR : 0 < R) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    (n : ℤ) (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    fderiv ℝ (termR c R a φ n) (τ, y) (0, EuclideanSpace.single 2 1) =
      termR c R (a + 1 / 2) (fun m => cpd 2 φ m) n (τ, y) := by
  have hd : DifferentiableAt ℝ (termR c R a φ n) (τ, y) :=
    (termR_contDiffAt hR hφ n hy).differentiableAt (by simp)
  rw [fderiv_snd_apply hd]
  have hfun : (fun y' : Space => termR c R a φ n (τ, y')) =
      fun y' => Fn a c φ n (Axi.chart R τ y') := rfl
  have hpos : 0 < Axi.age R y := Axi.age_pos hR.ne' hy
  have hp : 0 < (Axi.chart R τ y).1 := hpos
  have he3 : (EuclideanSpace.single 2 1 : Space) = Axi.e3 := by
    ext i
    simp [Axi.e3, coordinateVector, EuclideanSpace.single_apply]
  rw [hfun, he3, Axi.axial_chain hR hy (Fn_differentiableAt hφ n hp)]
  unfold Axi.dEta
  rw [fderiv_Fn hφ n hp]
  have hc2 : cpd 2 φ (shiftC c n (Axi.chart R τ y)) =
      fderiv ℝ φ (shiftC c n (Axi.chart R τ y)) (0, (0, 1)) := rfl
  simp only [zero_mul, zero_add, smul_eq_mul]
  rw [← hc2]
  unfold termR
  rw [Real.rpow_add hpos, Real.sqrt_eq_rpow]
  simp only [Axi.chart, shiftC, Prod.fst, Prod.snd]
  ring

theorem termR_fderiv_eR_comb {c R a : ℝ} (φ : Coord → ℝ) (n : ℤ) (τ : ℝ) {y : Space} :
    (y 0 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) * fderiv ℝ (termR c R a φ n) (τ, y) (0, EuclideanSpace.single 0 1) +
      (y 1 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) * fderiv ℝ (termR c R a φ n) (τ, y) (0, EuclideanSpace.single 1 1) =
      fderiv ℝ (termR c R a φ n) (τ, y) (0, Axi.eR y) := by
  have hv : ((0 : ℝ), Axi.eR y) = (y 0 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • ((0 : ℝ), (EuclideanSpace.single 0 1 : Space)) +
      (y 1 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) • ((0 : ℝ), (EuclideanSpace.single 1 1 : Space)) := by
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add, Prod.snd]
      exact eR_decomp y
  rw [hv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem termR_fderiv_radial {c R a e : ℝ} (hR : 0 < R) (he : e = R⁻¹) {φ : Coord → ℝ}
    (hφ : IsCoordTest φ) (n : ℤ) (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    fderiv ℝ (termR c R a φ n) (τ, y) (0, Axi.eR y) =
      termR c R (a + 1 / 2) (fun m => cpd 1 φ m - e * (2 * m.1 * cpd 0 φ m + m.2.2 * cpd 2 φ m)
        - 2 * a * e * φ m) n (τ, y) := by
  have hd : DifferentiableAt ℝ (termR c R a φ n) (τ, y) :=
    (termR_contDiffAt hR hφ n hy).differentiableAt (by simp)
  rw [fderiv_snd_apply hd]
  have hfun : (fun y' : Space => termR c R a φ n (τ, y')) =
      fun y' => Fn a c φ n (Axi.chart R τ y') := rfl
  have hpos : 0 < Axi.age R y := Axi.age_pos hR.ne' hy
  have hp : 0 < (Axi.chart R τ y).1 := hpos
  rw [hfun, Axi.radial_chain hR hy (Fn_differentiableAt hφ n hp)]
  unfold Axi.dQ Axi.dS Axi.dEta
  simp only [fderiv_Fn hφ n hp]
  have e0 : ∀ m : Coord, fderiv ℝ φ m (1, (0, 0)) = cpd 0 φ m := fun m => rfl
  have e1 : ∀ m : Coord, fderiv ℝ φ m (0, (1, 0)) = cpd 1 φ m := fun m => rfl
  have e2 : ∀ m : Coord, fderiv ℝ φ m (0, (0, 1)) = cpd 2 φ m := fun m => rfl
  simp only [e0, e1, e2]
  unfold termR
  dsimp only [Axi.chart, shiftC]
  rw [he, Real.rpow_add hpos, Real.sqrt_eq_rpow, Real.rpow_sub_one hpos.ne']
  simp only [smul_eq_mul]
  field_simp
  ring

theorem ct_deriv_z {c ε a : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    (τ : ℝ) (y : Space) (hy : y ∉ Axi.axis) :
    fderiv ℝ (ctLift c ε a φ) (τ, y) (0, EuclideanSpace.single 2 1) =
      ctLift c ε (a + 1 / 2) (fun m => cpd 2 φ m) (τ, y) := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hx0 : (τ, y).2 ∉ Axi.axis := hy
  obtain ⟨N1, h1⟩ := finite_of_tsupport hc hR hφ (ψ := φ) (fun p hp => subset_tsupport φ hp) hx0
  obtain ⟨N2, h2⟩ := finite_of_tsupport hc hR hφ (ψ := fun m => cpd 2 φ m)
    (fun p hp => mem_tsupport_of_ne (Or.inr (fun h => hp (by simp [cpd, h])))) hx0
  have hS : ∀ᶠ x in 𝓝 (τ, y), ∀ n ∉ N1 ∪ N2, termR c ε⁻¹ a φ n x = 0 := by
    filter_upwards [h1] with x hx1 n hn
    exact hx1 n (fun h => hn (Finset.mem_union_left _ h))
  have hS2 : ∀ᶠ x in 𝓝 (τ, y), ∀ n ∉ N1 ∪ N2, termR c ε⁻¹ (a + 1 / 2) (fun m => cpd 2 φ m) n x = 0 := by
    filter_upwards [h2] with x hx2 n hn
    exact hx2 n (fun h => hn (Finset.mem_union_right _ h))
  have hRHS : ctLift c ε (a + 1 / 2) (fun m => cpd 2 φ m) (τ, y) =
      ∑ n ∈ N1 ∪ N2, termR c ε⁻¹ (a + 1 / 2) (fun m => cpd 2 φ m) n (τ, y) :=
    (ctLift_eq_sum_of_fin hS2).self_of_nhds
  rw [fderiv_ctLift_eq_sum hR hφ hx0 hS, hRHS]
  apply Finset.sum_congr rfl
  intro n _
  exact termR_fderiv_z hR hφ n τ hy

theorem ct_deriv_radial {c ε a : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ}
    (hφ : IsCoordTest φ) (τ : ℝ) (y : Space) (hy : y ∉ Axi.axis) :
    (y 0 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) *
        fderiv ℝ (ctLift c ε a φ) (τ, y) (0, EuclideanSpace.single 0 1) +
      (y 1 / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) *
        fderiv ℝ (ctLift c ε a φ) (τ, y) (0, EuclideanSpace.single 1 1) =
      ctLift c ε (a + 1 / 2)
        (fun m => cpd 1 φ m - ε * (2 * m.1 * cpd 0 φ m + m.2.2 * cpd 2 φ m) - 2 * a * ε * φ m)
        (τ, y) := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hx0 : (τ, y).2 ∉ Axi.axis := hy
  obtain ⟨N1, h1⟩ := finite_of_tsupport hc hR hφ (ψ := φ) (fun p hp => subset_tsupport φ hp) hx0
  obtain ⟨N3, h3⟩ := finite_of_tsupport hc hR hφ
    (ψ := fun m => cpd 1 φ m - ε * (2 * m.1 * cpd 0 φ m + m.2.2 * cpd 2 φ m) - 2 * a * ε * φ m)
    (fun p hp => by
      by_contra hn
      obtain ⟨h0, hd⟩ := zero_of_nmem_tsupport hn
      apply hp
      simp [cpd, h0, hd])
    hx0
  have hS : ∀ᶠ x in 𝓝 (τ, y), ∀ n ∉ N1 ∪ N3, termR c ε⁻¹ a φ n x = 0 := by
    filter_upwards [h1] with x hx1 n hn
    exact hx1 n (fun h => hn (Finset.mem_union_left _ h))
  have hS3 : ∀ᶠ x in 𝓝 (τ, y), ∀ n ∉ N1 ∪ N3,
      termR c ε⁻¹ (a + 1 / 2)
        (fun m => cpd 1 φ m - ε * (2 * m.1 * cpd 0 φ m + m.2.2 * cpd 2 φ m) - 2 * a * ε * φ m) n x = 0 := by
    filter_upwards [h3] with x hx3 n hn
    exact hx3 n (fun h => hn (Finset.mem_union_right _ h))
  have hRHS : ctLift c ε (a + 1 / 2)
      (fun m => cpd 1 φ m - ε * (2 * m.1 * cpd 0 φ m + m.2.2 * cpd 2 φ m) - 2 * a * ε * φ m) (τ, y) =
      ∑ n ∈ N1 ∪ N3, termR c ε⁻¹ (a + 1 / 2)
        (fun m => cpd 1 φ m - ε * (2 * m.1 * cpd 0 φ m + m.2.2 * cpd 2 φ m) - 2 * a * ε * φ m) n (τ, y) :=
    (ctLift_eq_sum_of_fin hS3).self_of_nhds
  rw [fderiv_ctLift_eq_sum hR hφ hx0 hS, fderiv_ctLift_eq_sum hR hφ hx0 hS, hRHS, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [termR_fderiv_eR_comb φ n τ]
  have he : ε = (ε⁻¹)⁻¹ := (inv_inv ε).symm
  exact termR_fderiv_radial hR he hφ n τ hy

theorem ct_deriv_part {c ε a : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ}
    (hφ : IsCoordTest φ) :
    IsPhaseTest (2 * ε * c) (ctLift c ε a φ) ∧
    (∀ x : ℝ × Space, x.2 ∉ Axi.axis →
      fderiv ℝ (ctLift c ε a φ) x (0, EuclideanSpace.single 2 1) =
        ctLift c ε (a + 1 / 2) (fun m => cpd 2 φ m) x) ∧
    (∀ x : ℝ × Space, x.2 ∉ Axi.axis →
      (x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2)) *
          fderiv ℝ (ctLift c ε a φ) x (0, EuclideanSpace.single 0 1) +
        (x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2)) *
          fderiv ℝ (ctLift c ε a φ) x (0, EuclideanSpace.single 1 1) =
        ctLift c ε (a + 1 / 2)
          (fun m => cpd 1 φ m - ε * (2 * m.1 * cpd 0 φ m + m.2.2 * cpd 2 φ m) - 2 * a * ε * φ m) x) := by
  refine ⟨ctLift_isPhaseTest hc hε hφ, ?_, ?_⟩
  · rintro ⟨τ, y⟩ hy
    exact ct_deriv_z hc hε hφ τ y hy
  · rintro ⟨τ, y⟩ hy
    exact ct_deriv_radial hc hε hφ τ y hy

end UnforcedLeray.Short.IIb
