import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ae_zero_of_periodic_tests (P : ℝ) [Fact (0 < P)] (h : ℝ → ℂ)
    (hint : IntegrableOn h (Set.Ioc 0 P))
    (h0 : ∀ θ : ℝ → ℂ, ContDiff ℝ ∞ θ → (∀ τ, θ (τ + P) = θ τ) →
      ∫ τ in Set.Ioc 0 P, θ τ * h τ = 0) :
    ∀ᵐ τ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) P)), h τ = 0 := by
  have hP : 0 < P := Fact.out
  have key : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo 0 P → ∫ x, g x • h x = 0 := by
    intro g hg hgc hsupp
    have hgR : ∀ x, g x ≠ 0 → x ∈ Ioo 0 P := fun x hx => hsupp (subset_tsupport g hx)
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
    have hshift : ∀ n : ℤ, ContDiff ℝ ∞ (fun τ : ℝ => g (τ + (n:ℝ) * P)) :=
      fun n => hg.comp (contDiff_id.add contDiff_const)
    have hterm : ∀ n : ℤ, ContDiff ℝ ∞ (fun τ : ℝ => ((g (τ + (n:ℝ) * P) : ℝ) : ℂ)) :=
      fun n => Complex.ofRealCLM.contDiff.comp (hshift n)
    -- local finiteness of the periodic sum
    have hloc : ∀ τ0 : ℝ, ∃ M : ℕ, ∀ τ ∈ Metric.ball τ0 1, ∀ n : ℤ,
        n ∉ Finset.Icc (-(M:ℤ)) (M:ℤ) → g (τ + (n:ℝ) * P) = 0 := by
      intro τ0
      obtain ⟨M, hM⟩ := exists_nat_gt ((R + |τ0| + 1) / P)
      refine ⟨M, fun τ hτ n hn => ?_⟩
      by_contra hne
      have hmem : τ + (n:ℝ) * P ∈ Metric.closedBall (0:ℝ) R := hR (subset_tsupport _ hne)
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
      rw [Metric.mem_ball, Real.dist_eq] at hτ
      have hτ1 := abs_lt.1 hτ
      have hm1 := abs_le.1 hmem
      have hC : R + |τ0| + 1 < (M:ℝ) * P := (div_lt_iff₀ hP).1 hM
      have hn1 : (n:ℝ) * P < R + |τ0| + 1 := by
        linarith [hm1.2, hτ1.1, neg_le_abs τ0]
      have hn2 : -(R + |τ0| + 1) < (n:ℝ) * P := by
        linarith [hm1.1, hτ1.2, le_abs_self τ0]
      have hlt : (n:ℝ) < (M:ℝ) := by
        by_contra hc
        push_neg at hc
        have := mul_le_mul_of_nonneg_right hc hP.le
        linarith
      have hgt : -(M:ℝ) < (n:ℝ) := by
        by_contra hc
        push_neg at hc
        have := mul_le_mul_of_nonneg_right hc hP.le
        linarith
      have h1 : -(M:ℤ) < n := by exact_mod_cast hgt
      have h2 : n < (M:ℤ) := by exact_mod_cast hlt
      exact hn (Finset.mem_Icc.2 ⟨h1.le, h2.le⟩)
    -- on a ball, the tsum is a finite sum
    have hcomp : ∀ τ0 : ℝ, ∃ s : Finset ℤ, ∀ τ ∈ Metric.ball τ0 1,
        (∑' n : ℤ, ((g (τ + (n:ℝ) * P) : ℝ) : ℂ)) = ∑ n ∈ s, ((g (τ + (n:ℝ) * P) : ℝ) : ℂ) := by
      intro τ0
      obtain ⟨M, hM⟩ := hloc τ0
      refine ⟨Finset.Icc (-(M:ℤ)) (M:ℤ), fun τ hτ => ?_⟩
      exact tsum_eq_sum (fun n hn => by simp [hM τ hτ n hn])
    have hcont : ∀ τ0 : ℝ, ContDiffAt ℝ ∞
        (fun τ : ℝ => ∑' n : ℤ, ((g (τ + (n:ℝ) * P) : ℝ) : ℂ)) τ0 := by
      intro τ0
      obtain ⟨s, hs⟩ := hcomp τ0
      have hsm : ContDiff ℝ ∞ (fun τ : ℝ => ∑ n ∈ s, ((g (τ + (n:ℝ) * P) : ℝ) : ℂ)) :=
        ContDiff.sum (fun n _ => hterm n)
      exact hsm.contDiffAt.congr_of_eventuallyEq
        (Filter.eventually_of_mem (Metric.ball_mem_nhds τ0 one_pos) hs)
    have hsmooth : ContDiff ℝ ∞
        (fun τ : ℝ => ∑' n : ℤ, ((g (τ + (n:ℝ) * P) : ℝ) : ℂ)) :=
      contDiff_iff_contDiffAt.2 hcont
    -- periodicity
    have hper : ∀ τ : ℝ, (∑' n : ℤ, ((g (τ + P + (n:ℝ) * P) : ℝ) : ℂ))
        = ∑' n : ℤ, ((g (τ + (n:ℝ) * P) : ℝ) : ℂ) := by
      intro τ
      calc (∑' n : ℤ, ((g (τ + P + (n:ℝ) * P) : ℝ) : ℂ))
          = ∑' n : ℤ, ((g (τ + (((Equiv.addRight (1:ℤ)) n : ℤ):ℝ) * P) : ℝ) : ℂ) := by
            congr 1
            funext n
            have hn : τ + P + (n:ℝ) * P = τ + (((Equiv.addRight (1:ℤ)) n : ℤ):ℝ) * P := by
              simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
              ring
            rw [hn]
        _ = ∑' n : ℤ, ((g (τ + (n:ℝ) * P) : ℝ) : ℂ) :=
            (Equiv.addRight (1:ℤ)).tsum_eq (fun n : ℤ => ((g (τ + (n:ℝ) * P) : ℝ) : ℂ))
    -- on (0, P] the periodic sum is g
    have hon : ∀ τ ∈ Ioc 0 P,
        (∑' n : ℤ, ((g (τ + (n:ℝ) * P) : ℝ) : ℂ)) = ((g τ : ℝ) : ℂ) := by
      intro τ hτ
      obtain ⟨hτ1, hτ2⟩ := hτ
      rw [tsum_eq_single 0]
      · simp
      · intro n hn
        by_contra hne
        have hg0 : g (τ + (n:ℝ) * P) ≠ 0 := by
          intro h0'
          apply hne
          simp [h0']
        obtain ⟨h1, h2⟩ := hgR _ hg0
        have hn1 : (n:ℝ) < 1 := by
          by_contra hc
          push_neg at hc
          have := mul_le_mul_of_nonneg_right hc hP.le
          linarith
        have hn2 : (-1:ℝ) < (n:ℝ) := by
          by_contra hc
          push_neg at hc
          have := mul_le_mul_of_nonneg_right hc hP.le
          linarith
        have h3 : n < 1 := by exact_mod_cast hn1
        have h4 : -1 < n := by exact_mod_cast hn2
        exact hn (by omega)
    have hint' : ∫ τ in Ioc 0 P, (∑' n : ℤ, ((g (τ + (n:ℝ) * P) : ℝ) : ℂ)) * h τ
        = ∫ τ in Ioc 0 P, ((g τ : ℝ) : ℂ) * h τ :=
      setIntegral_congr_fun measurableSet_Ioc (fun τ hτ => by simp only [hon τ hτ])
    have hzero : ∫ τ in Ioc 0 P, ((g τ : ℝ) : ℂ) * h τ = 0 := by
      rw [← hint']
      exact h0 (fun τ => ∑' n : ℤ, ((g (τ + (n:ℝ) * P) : ℝ) : ℂ)) hsmooth hper
    have hext : ∫ x, g x • h x = ∫ x in Ioc 0 P, g x • h x := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
      intro x hx
      by_cases hg0 : g x = 0
      · simp [hg0]
      · exact absurd (Ioo_subset_Ioc_self (hgR x hg0)) hx
    rw [hext]
    simp only [Complex.real_smul]
    exact hzero
  have hloc_int : LocallyIntegrableOn h (Ioo 0 P) volume :=
    (hint.mono_set Ioo_subset_Ioc_self).locallyIntegrableOn
  have hmain : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo 0 P → h x = 0 :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc_int
      (fun g hg hgc hts => key g hg hgc hts)
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hmain, Measure.ae_ne (volume : Measure ℝ) P] with x h1 h2 hx
  exact h1 ⟨hx.1, lt_of_le_of_ne hx.2 h2⟩

end UnforcedLeray.Short.PartIIIb.Concrete
