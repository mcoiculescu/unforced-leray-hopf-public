import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.EtaCutProps
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.LapPMul

/-!


Source: `the November 2 reference manuscript`, lines 2074-2105.
With `θ = etaCut R`: `θ φ - φ = (θ - 1) φ`, and the planar derivatives of `θ φ - φ` are
`(θ - 1)` times the derivatives of `φ`, plus `φ` times the derivatives of `θ` (`∂_q θ = 0`,
`|∂_η θ|, |Δθ| ≤ C_θ`). The weight `(1 + η²)^N ≤ (1 + η²)^(N+1) / (1 + R²)` on `|η| ≥ R`, and
the difference vanishes on `|η| < R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

/-- A jointly `C^∞` function of the plane is `C^2`. -/
theorem contDiff_two_of_top {f : B0579.Plane → ℝ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) : ContDiff ℝ 2 f :=
  h.of_le (by norm_num)

/-- Planar error of a product with a `θ` whose `∂_q` vanishes at `x`. -/
theorem planarErr_prod (θ g : B0579.Plane → ℝ) (x : B0579.Plane)
    (hθ : ContDiff ℝ 2 θ) (hg : ContDiff ℝ 2 g) (h0 : B0579.pd 0 θ x = 0) :
    planarErr (fun y => θ y * g y) g x =
      |(θ x - 1) * g x| + |(θ x - 1) * B0579.pd 0 g x| +
        |(θ x - 1) * B0579.pd 1 g x + g x * B0579.pd 1 θ x| +
        |(θ x - 1) * lapP g x + g x * lapP θ x + 2 * B0579.pd 1 θ x * B0579.pd 1 g x| := by
  have hθd : DifferentiableAt ℝ θ x := (hθ.differentiable (by norm_num)) x
  have hgd : DifferentiableAt ℝ g x := (hg.differentiable (by norm_num)) x
  have e0 : θ x * g x - g x = (θ x - 1) * g x := by ring
  have e1 : B0579.pd 0 (fun y => θ y * g y) x - B0579.pd 0 g x =
      (θ x - 1) * B0579.pd 0 g x := by
    rw [lapPMul_pd_mul 0 θ g x hθd hgd, h0]
    ring
  have e2 : B0579.pd 1 (fun y => θ y * g y) x - B0579.pd 1 g x =
      (θ x - 1) * B0579.pd 1 g x + g x * B0579.pd 1 θ x := by
    rw [lapPMul_pd_mul 1 θ g x hθd hgd]
    ring
  have e3 : lapP (fun y => θ y * g y) x - lapP g x =
      (θ x - 1) * lapP g x + g x * lapP θ x + 2 * B0579.pd 1 θ x * B0579.pd 1 g x := by
    rw [lapPMul θ g x hθ hg, h0]
    ring
  simp only [planarErr]
  rw [e0, e1, e2, e3]

/-- Elementary bound for the four planar error terms. -/
theorem abs_planar_bound (t p l G P0 P1 L C : ℝ) (hC : 0 ≤ C) (ht : |t| ≤ 1)
    (hp : |p| ≤ C) (hl : |l| ≤ C) :
    |t * G| + |t * P0| + |t * P1 + G * p| + |t * L + G * l + 2 * p * P1| ≤
      (1 + 2 * C) * (|G| + |P0| + |P1| + |L|) := by
  have h1 : |t * G| ≤ |G| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) ht
  have h2 : |t * P0| ≤ |P0| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) ht
  have hGp : |G * p| ≤ C * |G| := by
    calc |G * p| = |G| * |p| := abs_mul _ _
      _ ≤ |G| * C := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ = C * |G| := mul_comm _ _
  have hGl : |G * l| ≤ C * |G| := by
    calc |G * l| = |G| * |l| := abs_mul _ _
      _ ≤ |G| * C := mul_le_mul_of_nonneg_left hl (abs_nonneg _)
      _ = C * |G| := mul_comm _ _
  have h3 : |t * P1 + G * p| ≤ |P1| + C * |G| := by
    have a1 : |t * P1 + G * p| ≤ |t * P1| + |G * p| := abs_add_le _ _
    have a2 : |t * P1| ≤ |P1| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) ht
    linarith
  have hL : |t * L| ≤ |L| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) ht
  have hP : |2 * p * P1| ≤ 2 * C * |P1| := by
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul_of_nonneg_right hp (abs_nonneg P1)
    linarith
  have h4 : |t * L + G * l + 2 * p * P1| ≤ |L| + C * |G| + 2 * C * |P1| := by
    have b1 := abs_add_le (t * L + G * l) (2 * p * P1)
    have b2 := abs_add_le (t * L) (G * l)
    linarith
  have hC0 := mul_nonneg hC (abs_nonneg P0)
  have hC1 := mul_nonneg hC (abs_nonneg L)
  nlinarith

theorem cutTail : UnforcedLeray.Short.IIb.TdSums.CutTail := by
  intro c t₀ t₁ φ hφ N
  obtain ⟨C₁, hC₁⟩ := hφ.decay (N + 1)
  obtain ⟨C₂, hC₂⟩ := hφ.decay_r (N + 1)
  have hEC := etaCutProps
  unfold EtaCutProps at hEC
  obtain ⟨Cθ, hCθ0, hCθ⟩ := hEC
  have hcoef0 : (0 : ℝ) ≤ 1 + 2 * Cθ := by linarith
  have hK0 : 0 ≤ (1 + 2 * Cθ) * |C₁| + |C₂| :=
    add_nonneg (mul_nonneg hcoef0 (abs_nonneg _)) (abs_nonneg _)
  refine ⟨(1 + 2 * Cθ) * |C₁| + |C₂|, fun R hR => ?_⟩
  have hRpos : 0 < R := by linarith
  have hden : 0 < 1 + R ^ 2 := by positivity
  have hθsm : ContDiff ℝ 2 (etaCut R) := contDiff_two_of_top (hCθ R hR).1
  have hslice : ∀ r ∈ Icc t₀ t₁, ContDiff ℝ 2 (φ r) := by
    intro r hr
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((fun z : ℝ × B0579.Plane => φ z.1 z.2) ∘ (fun x : B0579.Plane => (r, x))) univ :=
      ContDiffOn.comp hφ.smooth (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun x _ => Set.mk_mem_prod hr (mem_univ x))
    exact contDiff_two_of_top (contDiffOn_univ.mp h1)
  refine ⟨fun r hr x => ?_, fun r hr x => ?_⟩
  · have hφr := hslice r hr
    have hS := hC₁ r hr x
    have hw0 : 0 ≤ (1 + x.2 ^ 2) ^ N := Real.rpow_nonneg (by positivity) N
    have hpow : (1 + x.2 ^ 2) ^ (N + 1) = (1 + x.2 ^ 2) ^ N * (1 + x.2 ^ 2) :=
      Real.rpow_add_one (by positivity) N
    rw [hpow] at hS
    show planarErr (fun y => etaCut R y * φ r y) (φ r) x * (1 + x.2 ^ 2) ^ N ≤
      ((1 + 2 * Cθ) * |C₁| + |C₂|) / (1 + R ^ 2)
    rw [le_div_iff₀ hden]
    by_cases hxR : |x.2| < R
    · have hzero : planarErr (fun y => etaCut R y * φ r y) (φ r) x = 0 := by
        obtain ⟨θ0, θ1, θ2, θ3, θ4, θ5, θ6, θ7, θ8⟩ := (hCθ R hR).2 x
        have hθ1 : etaCut R x = 1 := θ2 hxR.le
        obtain ⟨hp1, hl1⟩ := θ8 hxR
        rw [planarErr_prod (etaCut R) (φ r) x hθsm hφr θ5, hθ1, hp1, hl1]
        simp
      simp only [hzero, zero_mul]
      exact hK0
    · push_neg at hxR
      have hR2 : 1 + R ^ 2 ≤ 1 + x.2 ^ 2 := by
        have h := pow_le_pow_left₀ hRpos.le hxR 2
        rw [sq_abs] at h
        linarith
      obtain ⟨θ0, θ1, θ2, θ3, θ4, θ5, θ6, θ7, θ8⟩ := (hCθ R hR).2 x
      have ht : |etaCut R x - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hPE : planarErr (fun y => etaCut R y * φ r y) (φ r) x ≤
          (1 + 2 * Cθ) * (|φ r x| + |B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x| +
            |lapP (φ r) x|) := by
        rw [planarErr_prod (etaCut R) (φ r) x hθsm hφr θ5]
        exact abs_planar_bound _ _ _ _ _ _ _ _ hCθ0 ht θ6 θ7
      have hS0 : 0 ≤ |φ r x| + |B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x| +
          |lapP (φ r) x| := by positivity
      set S := |φ r x| + |B0579.pd 0 (φ r) x| + |B0579.pd 1 (φ r) x| + |lapP (φ r) x| with hSdef
      calc planarErr (fun y => etaCut R y * φ r y) (φ r) x * (1 + x.2 ^ 2) ^ N * (1 + R ^ 2)
          ≤ (1 + 2 * Cθ) * S * (1 + x.2 ^ 2) ^ N * (1 + R ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hPE hw0
        _ ≤ (1 + 2 * Cθ) * S * (1 + x.2 ^ 2) ^ N * (1 + x.2 ^ 2) := by
            apply mul_le_mul_of_nonneg_left hR2
            exact mul_nonneg (mul_nonneg hcoef0 hS0) hw0
        _ = (1 + 2 * Cθ) * (S * ((1 + x.2 ^ 2) ^ N * (1 + x.2 ^ 2))) := by ring
        _ ≤ (1 + 2 * Cθ) * C₁ := mul_le_mul_of_nonneg_left hS hcoef0
        _ ≤ (1 + 2 * Cθ) * |C₁| := mul_le_mul_of_nonneg_left (le_abs_self _) hcoef0
        _ ≤ (1 + 2 * Cθ) * |C₁| + |C₂| := le_add_of_nonneg_right (abs_nonneg _)
  · have hD := hC₂ r hr x
    have hw0 : 0 ≤ (1 + x.2 ^ 2) ^ N := Real.rpow_nonneg (by positivity) N
    have hpow : (1 + x.2 ^ 2) ^ (N + 1) = (1 + x.2 ^ 2) ^ N * (1 + x.2 ^ 2) :=
      Real.rpow_add_one (by positivity) N
    rw [hpow] at hD
    show |etaCut R x * deriv (fun s => φ s x) r - deriv (fun s => φ s x) r| *
        (1 + x.2 ^ 2) ^ N ≤ ((1 + 2 * Cθ) * |C₁| + |C₂|) / (1 + R ^ 2)
    rw [le_div_iff₀ hden]
    by_cases hxR : |x.2| < R
    · have hθ1 : etaCut R x = 1 := ((hCθ R hR).2 x).2.2.1 hxR.le
      rw [hθ1]
      simp only [one_mul, sub_self, abs_zero, zero_mul]
      linarith [hK0]
    · push_neg at hxR
      have hR2 : 1 + R ^ 2 ≤ 1 + x.2 ^ 2 := by
        have h := pow_le_pow_left₀ hRpos.le hxR 2
        rw [sq_abs] at h
        linarith
      obtain ⟨θ0, θ1, -⟩ := (hCθ R hR).2 x
      have ht : |etaCut R x - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hd : |etaCut R x * deriv (fun s => φ s x) r - deriv (fun s => φ s x) r| ≤
          |deriv (fun s => φ s x) r| := by
        have e : etaCut R x * deriv (fun s => φ s x) r - deriv (fun s => φ s x) r =
            (etaCut R x - 1) * deriv (fun s => φ s x) r := by ring
        rw [e, abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) ht
      calc |etaCut R x * deriv (fun s => φ s x) r - deriv (fun s => φ s x) r| *
            (1 + x.2 ^ 2) ^ N * (1 + R ^ 2)
          ≤ |deriv (fun s => φ s x) r| * (1 + x.2 ^ 2) ^ N * (1 + R ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hw0) (by positivity)
        _ ≤ |deriv (fun s => φ s x) r| * (1 + x.2 ^ 2) ^ N * (1 + x.2 ^ 2) :=
            mul_le_mul_of_nonneg_left hR2 (mul_nonneg (abs_nonneg _) hw0)
        _ = |deriv (fun s => φ s x) r| * ((1 + x.2 ^ 2) ^ N * (1 + x.2 ^ 2)) := by ring
        _ ≤ C₂ := hD
        _ ≤ (1 + 2 * Cθ) * |C₁| + |C₂| := by
            linarith [le_abs_self C₂, mul_nonneg hcoef0 (abs_nonneg C₁)]

end TdSums

end UnforcedLeray.Short.IIb
