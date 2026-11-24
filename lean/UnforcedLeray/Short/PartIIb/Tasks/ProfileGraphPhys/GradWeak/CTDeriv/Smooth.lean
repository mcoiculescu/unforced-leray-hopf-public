import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.CTDeriv.Periodic

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- Compact support of a coordinate test: bounds on the support, away from `s = 0`. -/
theorem coord_support_bounds {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    ∃ a0 Q : ℝ, 0 < a0 ∧ 0 ≤ Q ∧
      ∀ p : Coord, φ p ≠ 0 → a0 ≤ p.1 ∧ p.1 ≤ Q ∧ |p.2.1| ≤ Q ∧ |p.2.2| ≤ Q := by
  have hK : IsCompact (tsupport φ) := hφ.compact.isCompact
  obtain ⟨Q0, hQ0⟩ := hK.isBounded.subset_closedBall (0 : Coord)
  have hnorm : ∀ p ∈ tsupport φ, ‖p‖ ≤ Q0 := fun p hp => by simpa using hQ0 hp
  obtain ⟨a0, ha0, hlow⟩ : ∃ a0 : ℝ, 0 < a0 ∧ ∀ p ∈ tsupport φ, a0 ≤ p.1 := by
    rcases (tsupport φ).eq_empty_or_nonempty with hE | ⟨p1, hp1⟩
    · exact ⟨1, one_pos, fun p hp => by simp [hE] at hp⟩
    · obtain ⟨p0, hp0, hmin⟩ := hK.exists_isMinOn ⟨p1, hp1⟩ continuous_fst.continuousOn
      exact ⟨p0.1, (hφ.supp hp0).1, fun p hp => hmin hp⟩
  refine ⟨a0, max Q0 0, ha0, le_max_right _ _, fun p hp => ?_⟩
  have hp' : p ∈ tsupport φ := subset_tsupport φ hp
  have hn := hnorm p hp'
  have hA : |p.1| ≤ max Q0 0 := by
    have h := (norm_fst_le p).trans hn
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hB : |p.2.1| ≤ max Q0 0 := by
    have h := (norm_fst_le p.2).trans ((norm_snd_le p).trans hn)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hC : |p.2.2| ≤ max Q0 0 := by
    have h := (norm_snd_le p.2).trans ((norm_snd_le p).trans hn)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  exact ⟨hlow p hp', (le_abs_self _).trans hA, hB, hC⟩

/-- Outside the `s`-support the test vanishes. -/
theorem phi_eq_zero_of_out {φ : Coord → ℝ} {a0 Q : ℝ}
    (hsupp : ∀ p : Coord, φ p ≠ 0 → a0 ≤ p.1 ∧ p.1 ≤ Q ∧ |p.2.1| ≤ Q ∧ |p.2.2| ≤ Q)
    {s q η : ℝ} (h : s < a0 ∨ Q < s) : φ (s, (q, η)) = 0 := by
  by_contra hne
  obtain ⟨h1, h2, -, -⟩ := hsupp _ hne
  change a0 ≤ s at h1
  change s ≤ Q at h2
  rcases h with h | h <;> linarith

/-- Near the axis the age is either zero or large. -/
theorem age_out {R a0 Q : ℝ} (hR : 0 < R) (ha0 : 0 < a0) (hQ : 0 ≤ Q) {y : Space}
    (hy : Axi.ϱ y < R / (Q + 1)) : Axi.age R y < a0 ∨ Q < Axi.age R y := by
  rcases (Axi.ϱ_nonneg y).eq_or_lt with h0 | hpos
  · left
    unfold Axi.age
    rw [← h0]
    simpa using ha0
  · right
    unfold Axi.age
    have h1 : Axi.ϱ y * (Q + 1) < R := by
      rwa [lt_div_iff₀ (by linarith)] at hy
    have h2 : (Axi.ϱ y * (Q + 1)) ^ 2 < R ^ 2 := by
      have := mul_nonneg hpos.le (by linarith : (0:ℝ) ≤ Q + 1)
      nlinarith
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (Axi.ϱ y)) (by nlinarith : (0:ℝ) ≤ Q ^ 2 + Q + 1)]

theorem continuousAt_age {R : ℝ} {y : Space} (hy : y ∉ Axi.axis) :
    ContinuousAt (fun z : Space => Axi.age R z) y := by
  unfold Axi.age
  exact continuousAt_const.div ((Axi.continuous_ϱ.continuousAt).pow 2)
    (pow_ne_zero 2 (Axi.ϱ_ne_zero hy))

theorem continuousAt_phase {R : ℝ} (hR : R ≠ 0) {x0 : ℝ × Space} (hx0 : x0.2 ∉ Axi.axis) :
    ContinuousAt (fun x : ℝ × Space => Axi.phase R x.1 x.2) x0 := by
  have hage : ContinuousAt (fun x : ℝ × Space => Axi.age R x.2) x0 :=
    (continuousAt_age hx0).comp continuousAt_snd
  have hne : Axi.age R x0.2 ≠ 0 := (Axi.age_pos hR hx0).ne'
  have hlog := hage.log hne
  unfold Axi.phase
  exact ((continuous_const.mul continuous_fst).div_const 2).continuousAt.sub
    (continuousAt_const.mul hlog)

/-- One chart term of the periodization, before summing over the cell index `n`. -/
def termR (c R a : ℝ) (φ : Coord → ℝ) (n : ℤ) (x : ℝ × Space) : ℝ :=
  (Axi.age R x.2) ^ a * φ (Axi.age R x.2, (Axi.phase R x.1 x.2 + n * c, Axi.trans R x.2))

theorem ctLift_eq_tsum (c ε a : ℝ) (φ : Coord → ℝ) (x : ℝ × Space) :
    ctLift c ε a φ x = ∑' n : ℤ, termR c ε⁻¹ a φ n x := rfl

/-- Local finiteness of the cell sum away from the axis. -/
theorem termR_local_finite {c R a : ℝ} (hc : 0 < c) (hR : 0 < R) {φ : Coord → ℝ}
    (hφ : IsCoordTest φ) {x0 : ℝ × Space} (hx0 : x0.2 ∉ Axi.axis) :
    ∃ N : Finset ℤ, ∀ᶠ x in 𝓝 x0, ∀ n ∉ N, termR c R a φ n x = 0 := by
  obtain ⟨a0, Q, ha0, hQ0, hsupp⟩ := coord_support_bounds hφ
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
  have hφne : φ (Axi.age R x.2, (Axi.phase R x.1 x.2 + n * c, Axi.trans R x.2)) ≠ 0 := by
    intro h
    apply hne
    unfold termR
    rw [h, mul_zero]
  have hq := (hsupp _ hφne).2.2.1
  change |Axi.phase R x.1 x.2 + n * c| ≤ Q at hq
  have hA := abs_le.1 hq
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

theorem termR_contDiffAt {c R a : ℝ} (hR : 0 < R) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    (n : ℤ) {x0 : ℝ × Space} (hx0 : x0.2 ∉ Axi.axis) :
    ContDiffAt ℝ ∞ (fun x => termR c R a φ n x) x0 := by
  have hϱ : ContDiffAt ℝ ∞ (fun y : Space => Axi.ϱ y) x0.2 :=
    Axi.contDiffOn_ϱ.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hx0)
  have hage : ContDiffAt ℝ ∞ (fun y : Space => Axi.age R y) x0.2 := by
    unfold Axi.age
    exact contDiffAt_const.div (hϱ.pow 2) (pow_ne_zero 2 (Axi.ϱ_ne_zero hx0))
  have hage' : ContDiffAt ℝ ∞ (fun x : ℝ × Space => Axi.age R x.2) x0 :=
    hage.comp x0 contDiffAt_snd
  have hne : Axi.age R x0.2 ≠ 0 := (Axi.age_pos hR.ne' hx0).ne'
  have hpow : ContDiffAt ℝ ∞ (fun x : ℝ × Space => (Axi.age R x.2) ^ a) x0 :=
    hage'.rpow_const_of_ne hne
  have hlog : ContDiffAt ℝ ∞ (fun x : ℝ × Space => Real.log (Axi.age R x.2)) x0 :=
    hage'.log hne
  have hph : ContDiffAt ℝ ∞ (fun x : ℝ × Space => Axi.phase R x.1 x.2 + n * c) x0 := by
    unfold Axi.phase
    exact (((contDiffAt_const (c := R)).mul contDiffAt_fst).div_const 2 |>.sub
      ((contDiffAt_const (c := R / 2)).mul hlog)).add contDiffAt_const
  have hy2 : ContDiffAt ℝ ∞ (fun x : ℝ × Space => x.2 2) x0 :=
    ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.contDiffAt).comp x0 contDiffAt_snd
  have htr : ContDiffAt ℝ ∞ (fun x : ℝ × Space => Axi.trans R x.2) x0 := by
    unfold Axi.trans
    exact ((contDiffAt_const (c := R)).mul hy2).div (hϱ.comp x0 contDiffAt_snd)
      (Axi.ϱ_ne_zero hx0)
  have hφc : ContDiffAt ℝ ∞
      (fun x : ℝ × Space => φ (Axi.age R x.2, (Axi.phase R x.1 x.2 + n * c, Axi.trans R x.2))) x0 :=
    (hφ.smooth.contDiffAt).comp x0 (hage'.prodMk (hph.prodMk htr))
  unfold termR
  exact hpow.mul hφc

theorem ctLift_contDiff {c ε a : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ}
    (hφ : IsCoordTest φ) :
    ContDiff ℝ ∞ (fun x : ℝ × Space => ctLift c ε a φ x) := by
  rw [contDiff_iff_contDiffAt]
  intro x0
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  by_cases hx0 : x0.2 ∈ Axi.axis
  · obtain ⟨a0, Q, ha0, hQ0, hsupp⟩ := coord_support_bounds hφ
    have hδ : 0 < ε⁻¹ / (Q + 1) := by positivity
    have hev : ∀ᶠ y in 𝓝 x0.2, Axi.ϱ y < ε⁻¹ / (Q + 1) :=
      (Axi.continuous_ϱ.continuousAt).eventually_lt continuousAt_const
        (by rw [(Axi.mem_axis_iff _).1 hx0]; exact hδ)
    have hev' : ∀ᶠ x in 𝓝 x0, Axi.ϱ x.2 < ε⁻¹ / (Q + 1) :=
      (continuous_snd.tendsto x0).eventually hev
    have hz : ∀ᶠ x in 𝓝 x0, ctLift c ε a φ x = 0 := by
      filter_upwards [hev'] with x hx
      have hterm : ∀ n : ℤ, termR c ε⁻¹ a φ n x = 0 := by
        intro n
        unfold termR
        rw [phi_eq_zero_of_out hsupp (age_out hR ha0 hQ0 hx), mul_zero]
      rw [ctLift_eq_tsum]
      simp only [hterm, tsum_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · obtain ⟨N, hN⟩ := termR_local_finite hc hR hφ hx0
    have hsum : ContDiffAt ℝ ∞ (fun x => ∑ n ∈ N, termR c ε⁻¹ a φ n x) x0 :=
      ContDiffAt.sum (fun n _ => termR_contDiffAt hR hφ n hx0)
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [hN] with x hx
    rw [ctLift_eq_tsum]
    exact tsum_eq_sum (fun n hn => hx n hn)

theorem ctLift_bounded {c ε a : ℝ} (hε : 0 < ε) {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    ∃ Rb : ℝ, ∀ (τ : ℝ) (y : Space), Rb < ‖y‖ → ctLift c ε a φ (τ, y) = 0 := by
  obtain ⟨a0, Q, ha0, hQ0, hsupp⟩ := coord_support_bounds hφ
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  refine ⟨(ε⁻¹ ^ 2 + Q ^ 2) / a0 + 1, fun τ y hy => ?_⟩
  have hterm : ∀ n : ℤ, termR c ε⁻¹ a φ n (τ, y) = 0 := by
    intro n
    unfold termR
    by_cases hz : φ (Axi.age ε⁻¹ y, (Axi.phase ε⁻¹ τ y + n * c, Axi.trans ε⁻¹ y)) = 0
    · rw [hz, mul_zero]
    exfalso
    obtain ⟨h1, h2, -, h4⟩ := hsupp _ hz
    change a0 ≤ Axi.age ε⁻¹ y at h1
    change |Axi.trans ε⁻¹ y| ≤ Q at h4
    have hage0 : 0 < Axi.age ε⁻¹ y := lt_of_lt_of_le ha0 h1
    have hϱ2 : 0 < Axi.ϱ y ^ 2 := by
      by_contra h
      have h0 : Axi.ϱ y ^ 2 = 0 := le_antisymm (not_lt.1 h) (sq_nonneg _)
      unfold Axi.age at hage0
      rw [h0, div_zero] at hage0
      exact lt_irrefl _ hage0
    have hA : a0 * Axi.ϱ y ^ 2 ≤ ε⁻¹ ^ 2 := by
      unfold Axi.age at h1
      rw [le_div_iff₀ hϱ2] at h1
      linarith
    have hT : (ε⁻¹ * y 2) ^ 2 ≤ Q ^ 2 * Axi.ϱ y ^ 2 := by
      unfold Axi.trans at h4
      have := pow_le_pow_left₀ (abs_nonneg _) h4 2
      rw [sq_abs, div_pow, div_le_iff₀ hϱ2] at this
      exact this
    have hy2 : a0 * y 2 ^ 2 ≤ Q ^ 2 := by
      have hR2 : 0 < ε⁻¹ ^ 2 := by positivity
      have e1 : ε⁻¹ ^ 2 * (a0 * y 2 ^ 2) ≤ ε⁻¹ ^ 2 * Q ^ 2 := by
        calc ε⁻¹ ^ 2 * (a0 * y 2 ^ 2) = a0 * (ε⁻¹ * y 2) ^ 2 := by ring
          _ ≤ a0 * (Q ^ 2 * Axi.ϱ y ^ 2) := mul_le_mul_of_nonneg_left hT ha0.le
          _ = Q ^ 2 * (a0 * Axi.ϱ y ^ 2) := by ring
          _ ≤ Q ^ 2 * ε⁻¹ ^ 2 := mul_le_mul_of_nonneg_left hA (sq_nonneg Q)
          _ = ε⁻¹ ^ 2 * Q ^ 2 := by ring
      exact le_of_mul_le_mul_left e1 hR2
    have hnorm : a0 * ‖y‖ ^ 2 ≤ ε⁻¹ ^ 2 + Q ^ 2 := by
      rw [Axi.norm_sq_eq_ϱ_sq_add]
      calc a0 * (Axi.ϱ y ^ 2 + y 2 ^ 2) = a0 * Axi.ϱ y ^ 2 + a0 * y 2 ^ 2 := by ring
        _ ≤ ε⁻¹ ^ 2 + Q ^ 2 := by linarith
    have hK0 : 0 ≤ (ε⁻¹ ^ 2 + Q ^ 2) / a0 := div_nonneg (by positivity) ha0.le
    have hsq : ‖y‖ ^ 2 ≤ (ε⁻¹ ^ 2 + Q ^ 2) / a0 := by
      rw [le_div_iff₀ ha0]
      nlinarith
    nlinarith [norm_nonneg y]
  show ∑' n : ℤ, termR c ε⁻¹ a φ n (τ, y) = 0
  simp only [hterm, tsum_zero]

theorem ctLift_isPhaseTest {c ε a : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ}
    (hφ : IsCoordTest φ) : IsPhaseTest (2 * ε * c) (ctLift c ε a φ) :=
  { smooth := ctLift_contDiff hc hε hφ
    periodic := fun τ y => ctLift_periodic c ε a hε φ (τ, y)
    bounded_support := by
      obtain ⟨Rb, hRb⟩ := ctLift_bounded (c := c) (a := a) hε hφ
      exact ⟨Rb, fun τ y hy => hRb τ y hy⟩ }

end UnforcedLeray.Short.IIb
