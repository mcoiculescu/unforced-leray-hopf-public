import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.Defs

/-!
# `SliceDetermined` from a countable `C¹`-dense family

Source `the November 2 reference manuscript` lines 1351-1362 (weak `y`-gradient of the
stream potential `bsPot`) and 1334-1337 (`Y_r`).

Given `D` with `TDFam D`, locally integrable `u, E`, and the relation
`∫ ∂ⱼχ u + ∫ χ E = 0` for `χ ∈ D`, we show the same relation for every `C_c^∞` test `φ`.
Choose `n` with `φ = 0` outside `B_n`, approximate `φ` by `χ ∈ D` (support in `B_n`,
`ε`-close in `C¹`). The difference of the two relations is an integral over `B_n` of an
integrand bounded by `ε (|u| + |E|)`, so `|∫ ∂ⱼφ u + ∫ φ E| ≤ ε M` with `M` independent of `ε`.
Letting `ε → 0` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- A continuous compactly supported scalar times a locally integrable scalar function is
integrable on `ℝ³`. -/
theorem sd_integrable_mul (c u : Space → ℂ) (hc : Continuous c) (hcc : HasCompactSupport c)
    (hu : ∀ R : ℝ, IntegrableOn u (closedBall 0 R) volume) :
    Integrable (fun y : Space => c y * u y) volume := by
  obtain ⟨R, hR⟩ := hcc.isCompact.isBounded.subset_closedBall (0 : Space)
  have h1 : IntegrableOn (fun y : Space => c y * u y) (closedBall 0 R) volume :=
    (hu R).continuousOn_mul hc.continuousOn (isCompact_closedBall 0 R)
  refine h1.integrable_of_forall_notMem_eq_zero ?_
  intro y hy
  have hy' : y ∉ tsupport c := fun h => hy (hR h)
  have hc0 : c y = 0 := (notMem_tsupport_iff_eventuallyEq.mp hy').eq_of_nhds
  simp [hc0]

/-- The partial derivative `∂ⱼ φ` of a `C_c^∞` function is continuous with compact support. -/
theorem sd_fderiv_smooth (φ : Space → ℂ) (hφ : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ)
    (j : Fin 3) :
    Continuous (fun y : Space => fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) ∧
      HasCompactSupport (fun y : Space => fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) := by
  refine ⟨(hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const, ?_⟩
  exact (hφ.2.fderiv ℝ).comp_left
    (g := fun L : Space →L[ℝ] ℂ => L (EuclideanSpace.single j (1 : ℝ))) (by simp)

/-- A function vanishing on the open set `{‖y‖ > n}` has zero derivative there. -/
theorem sd_fderiv_zero (f : Space → ℂ) (n : ℕ) (hf : ∀ y : Space, (n : ℝ) < ‖y‖ → f y = 0)
    (y : Space) (hy : (n : ℝ) < ‖y‖) :
    fderiv ℝ f y = 0 := by
  have hev : f =ᶠ[𝓝 y] (0 : Space → ℂ) :=
    eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hy)
      (fun z hz => hf z hz)
  rw [hev.fderiv_eq]
  simp

theorem sliceDetermined : SliceDetermined := by
  unfold SliceDetermined
  intro D hD u E j hu hE hχ φ hφ
  have hφ' : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ := hφ
  obtain ⟨R, hR⟩ := hφ'.2.isCompact.isBounded.subset_closedBall (0 : Space)
  obtain ⟨n, hRn⟩ : ∃ n : ℕ, R ≤ n := ⟨⌈R⌉₊, Nat.le_ceil R⟩
  have hφ0 : ∀ y : Space, (n : ℝ) < ‖y‖ → φ y = 0 := by
    intro y hy
    have hy' : y ∉ tsupport φ := by
      intro h
      have h2 := hR h
      rw [mem_closedBall_zero_iff] at h2
      linarith
    exact (notMem_tsupport_iff_eventuallyEq.mp hy').eq_of_nhds
  -- the key estimate: for every ε > 0, the defect is at most ε times a fixed constant
  have key : ∀ ε : ℝ, 0 < ε →
      ‖(∫ y : Space, fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y) +
          ∫ y : Space, φ y * E y‖ ≤
        ε * ∫ y in closedBall (0 : Space) (n : ℝ), (‖u y‖ + ‖E y‖) := by
    intro ε hε
    obtain ⟨χ, hχD, hχ0, hχsup, hχder⟩ := hD.2.2 n φ hφ'.1 hφ0 ε hε
    have hχS : ContDiff ℝ ∞ χ ∧ HasCompactSupport χ := hD.2.1 χ hχD
    have hGχ := hχ χ hχD
    have hdφ := sd_fderiv_smooth φ hφ' j
    have hdχ := sd_fderiv_smooth χ hχS j
    have hiA : Integrable
        (fun y : Space => fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y) volume :=
      sd_integrable_mul _ u hdφ.1 hdφ.2 hu
    have hiB : Integrable (fun y : Space => φ y * E y) volume :=
      sd_integrable_mul φ E hφ'.1.continuous hφ'.2 hE
    have hiC : Integrable
        (fun y : Space => fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ)) * u y) volume :=
      sd_integrable_mul _ u hdχ.1 hdχ.2 hu
    have hiD : Integrable (fun y : Space => χ y * E y) volume :=
      sd_integrable_mul χ E hχS.1.continuous hχS.2 hE
    -- the defect integrand
    have hid : (∫ y : Space, fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y) +
          ∫ y : Space, φ y * E y =
        ∫ y : Space, ((fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y -
              fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ)) * u y) +
            (φ y * E y - χ y * E y)) := by
      have hAC : Integrable (fun y : Space =>
          fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y -
            fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ)) * u y) volume := hiA.sub hiC
      have hBD : Integrable (fun y : Space => φ y * E y - χ y * E y) volume := hiB.sub hiD
      rw [integral_add hAC hBD, integral_sub hiA hiC, integral_sub hiB hiD]
      linear_combination hGχ
    -- pointwise bound by ε (|u| + |E|)
    have hpt : ∀ y : Space,
        ‖(fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y -
              fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ)) * u y) +
            (φ y * E y - χ y * E y)‖ ≤ ε * (‖u y‖ + ‖E y‖) := by
      intro y
      have ha : ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) -
          fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ))‖ ≤ ε := hχder j y
      have hc : ‖φ y - χ y‖ ≤ ε := hχsup y
      have heq : (fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y -
              fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ)) * u y) +
            (φ y * E y - χ y * E y) =
          (fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) -
              fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ))) * u y + (φ y - χ y) * E y := by
        ring
      rw [heq]
      calc ‖(fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) -
                fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ))) * u y + (φ y - χ y) * E y‖
          ≤ ‖(fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) -
                fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ))) * u y‖ +
              ‖(φ y - χ y) * E y‖ := norm_add_le _ _
        _ = ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) -
                fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ))‖ * ‖u y‖ +
              ‖φ y - χ y‖ * ‖E y‖ := by rw [norm_mul, norm_mul]
        _ ≤ ε * ‖u y‖ + ε * ‖E y‖ :=
              add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
                (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
        _ = ε * (‖u y‖ + ‖E y‖) := by ring
    -- the defect integrand vanishes outside B_n
    have hzero : ∀ y : Space, y ∉ closedBall (0 : Space) (n : ℝ) →
        (fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y -
              fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ)) * u y) +
            (φ y * E y - χ y * E y) = 0 := by
      intro y hy
      have hy' : (n : ℝ) < ‖y‖ := by
        rw [mem_closedBall_zero_iff] at hy
        exact not_le.mp hy
      rw [sd_fderiv_zero φ n hφ0 y hy', sd_fderiv_zero χ n hχ0 y hy', hφ0 y hy', hχ0 y hy']
      simp
    have hrestr : (∫ y : Space,
          ((fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y -
              fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ)) * u y) +
            (φ y * E y - χ y * E y))) =
        ∫ y in closedBall (0 : Space) (n : ℝ),
          ((fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y -
              fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ)) * u y) +
            (φ y * E y - χ y * E y)) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    have hbound : ‖∫ y in closedBall (0 : Space) (n : ℝ),
          ((fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y -
              fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ)) * u y) +
            (φ y * E y - χ y * E y))‖ ≤
        ∫ y in closedBall (0 : Space) (n : ℝ), ε * (‖u y‖ + ‖E y‖) := by
      apply norm_integral_le_of_norm_le
      · exact Integrable.const_mul
          (Integrable.add (Integrable.norm (hu (n : ℝ))) (Integrable.norm (hE (n : ℝ)))) ε
      · exact ae_of_all _ hpt
    have hconst : ∫ y in closedBall (0 : Space) (n : ℝ), ε * (‖u y‖ + ‖E y‖) =
        ε * ∫ y in closedBall (0 : Space) (n : ℝ), (‖u y‖ + ‖E y‖) :=
      integral_const_mul ε _
    rw [hid, hrestr]
    rw [hconst] at hbound
    exact hbound
  -- let ε → 0
  have hM0 : 0 ≤ ∫ y in closedBall (0 : Space) (n : ℝ), (‖u y‖ + ‖E y‖) :=
    integral_nonneg (fun y => add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hnorm : ‖(∫ y : Space, fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y) +
      ∫ y : Space, φ y * E y‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hpos : (0 : ℝ) < (∫ y in closedBall (0 : Space) (n : ℝ), (‖u y‖ + ‖E y‖)) + 1 := by
      linarith
    have h1 := key (δ / ((∫ y in closedBall (0 : Space) (n : ℝ), (‖u y‖ + ‖E y‖)) + 1))
      (div_pos hδ hpos)
    have h2 : δ / ((∫ y in closedBall (0 : Space) (n : ℝ), (‖u y‖ + ‖E y‖)) + 1) *
        (∫ y in closedBall (0 : Space) (n : ℝ), (‖u y‖ + ‖E y‖)) ≤ δ := by
      calc δ / ((∫ y in closedBall (0 : Space) (n : ℝ), (‖u y‖ + ‖E y‖)) + 1) *
            (∫ y in closedBall (0 : Space) (n : ℝ), (‖u y‖ + ‖E y‖))
          ≤ δ / ((∫ y in closedBall (0 : Space) (n : ℝ), (‖u y‖ + ‖E y‖)) + 1) *
              ((∫ y in closedBall (0 : Space) (n : ℝ), (‖u y‖ + ‖E y‖)) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hδ.le hpos.le)
        _ = δ := by field_simp
    linarith
  exact norm_eq_zero.mp hnorm

end UnforcedLeray.Short.PartIIIb.Concrete
