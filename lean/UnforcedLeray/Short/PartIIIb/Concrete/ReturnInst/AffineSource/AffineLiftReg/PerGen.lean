import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.PerGen.Glue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# `PartIII-b:C/asrc/ra/5/1`: generic lattice-sum smoothness (source 4978)

`contDiffOn_tsum_shift`: `p ↦ Σ_j G(p₁, p₂₁ - j c, p₂₂)` is `C^n` on `U × ℝ` when `G` is `C^n` on
`U × ℝ` with the Gaussian derivative bounds `hbd` (uniform on compact `s`- and `η`-sets). Each
point has an open box `V` on which the derivatives of the lattice terms are bounded by
`K_k exp(-b j²)` (`b = a c²/2`), a bump `ψ` equal to `1` near the point and supported in `V`
makes each term globally `C^n` (`perGen_glue`), and `contDiff_tsum` applies.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem contDiffOn_tsum_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n : ℕ) (c : ℝ) (hc : 0 < c) (U : Set ℝ) (hU : IsOpen U) (G : ℝ × (ℝ × ℝ) → E)
    (hG : ContDiffOn ℝ (n : WithTop ℕ∞) G (U ×ˢ Set.univ))
    (hbd : ∀ K : Set ℝ, K ⊆ U → IsCompact K → ∀ L : Set ℝ, IsCompact L → ∃ C a : ℝ, 0 < a ∧ ∀ m : ℕ, m ≤ n → ∀ s ∈ K, ∀ q : ℝ, ∀ η ∈ L, ‖iteratedFDeriv ℝ m G (s, (q, η))‖ ≤ C * Real.exp (-a * q ^ 2)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => ∑' j : ℤ, G (p.1, (p.2.1 - j * c, p.2.2))) (U ×ˢ Set.univ) := by
  have hloc : ∀ p0 ∈ U ×ˢ (Set.univ : Set (ℝ × ℝ)), ContDiffAt ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => ∑' j : ℤ, G (p.1, (p.2.1 - j * c, p.2.2))) p0 := by
    rintro ⟨s0, q0, η0⟩ ⟨hs0, -⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU s0 hs0
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / 2 := ⟨_, rfl⟩
    have hδpos : 0 < δ := by rw [hδ]; linarith
    obtain ⟨K, hK⟩ : ∃ K : Set ℝ, K = Icc (s0 - δ) (s0 + δ) := ⟨_, rfl⟩
    have hKU : K ⊆ U := by
      intro t ht
      rw [hK] at ht
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have hKc : IsCompact K := by rw [hK]; exact isCompact_Icc
    have hsK : s0 ∈ K := by rw [hK]; exact ⟨by linarith, by linarith⟩
    obtain ⟨L, hL⟩ : ∃ L : Set ℝ, L = Icc (η0 - 1) (η0 + 1) := ⟨_, rfl⟩
    have hLc : IsCompact L := by rw [hL]; exact isCompact_Icc
    have hηL : η0 ∈ L := by rw [hL]; exact ⟨by linarith, by linarith⟩
    obtain ⟨C, a, ha, hCb⟩ := hbd K hKU hKc L hLc
    have hC0 : 0 ≤ C := by
      have h := hCb 0 (Nat.zero_le _) s0 hsK 0 η0 hηL
      have h0 := le_trans (norm_nonneg _) h
      simpa using h0
    obtain ⟨V, hV⟩ : ∃ V : Set (ℝ × (ℝ × ℝ)),
        V = Ioo (s0 - δ) (s0 + δ) ×ˢ (Ioo (q0 - 1) (q0 + 1) ×ˢ Ioo (η0 - 1) (η0 + 1)) := ⟨_, rfl⟩
    have hVo : IsOpen V := by
      rw [hV]; exact isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)
    have hVmem : ∀ p ∈ V, p.1 ∈ K ∧ p.2.1 ∈ Ioo (q0 - 1) (q0 + 1) ∧ p.2.2 ∈ L := by
      rintro ⟨s, q, η⟩ hp
      rw [hV] at hp
      obtain ⟨h1, h2, h3⟩ := hp
      refine ⟨?_, h2, ?_⟩
      · rw [hK]; exact ⟨h1.1.le, h1.2.le⟩
      · rw [hL]; exact ⟨h3.1.le, h3.2.le⟩
    have hp0V : (s0, (q0, η0)) ∈ V := by
      rw [hV]
      simp only [Set.mem_prod, Set.mem_Ioo]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
    obtain ⟨ε', hε', hballV⟩ := Metric.isOpen_iff.mp hVo (s0, (q0, η0)) hp0V
    let ψb : ContDiffBump ((s0, (q0, η0)) : ℝ × (ℝ × ℝ)) :=
      { rIn := ε' / 4, rOut := ε' / 2, rIn_pos := by linarith, rIn_lt_rOut := by linarith }
    have hψinf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ⇑ψb := ψb.contDiff
    have hψn : ContDiff ℝ (n : WithTop ℕ∞) ⇑ψb := hψinf.of_le (by exact_mod_cast le_top)
    have hψsupp : tsupport ⇑ψb ⊆ V := by
      rw [ψb.tsupport_eq]
      exact (Metric.closedBall_subset_ball (show ψb.rOut < ε' by show ε' / 2 < ε'; linarith)).trans hballV
    have hψone : ∀ p ∈ Metric.ball (s0, (q0, η0)) (ε' / 4), ψb p = 1 := by
      intro p hp
      apply ψb.one_of_mem_closedBall
      exact Metric.ball_subset_closedBall hp
    have hψ_one_nhds : ∀ᶠ p in 𝓝 ((s0, (q0, η0)) : ℝ × (ℝ × ℝ)), ψb p = 1 :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds _ (by linarith)) (fun p hp => hψone p hp)
    have hbdψ : ∀ i : ℕ, ∃ Bi : ℝ, ∀ x, ‖iteratedFDeriv ℝ i ⇑ψb x‖ ≤ Bi := fun i =>
      (hψinf.continuous_iteratedFDeriv (m := i) (WithTop.coe_le_coe.mpr le_top)).bounded_above_of_compact_support
        (ψb.hasCompactSupport.iteratedFDeriv i)
    choose B hB using hbdψ
    have hB0 : ∀ i, 0 ≤ B i := fun i => le_trans (norm_nonneg _) (hB i 0)
    obtain ⟨Km, hKm⟩ : ∃ Km : ℕ → ℝ, ∀ k, Km k =
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i) * C * Real.exp (a * (|q0| + 1) ^ 2) :=
      ⟨_, fun k => rfl⟩
    have hKnn : ∀ k, 0 ≤ Km k := by
      intro k
      rw [hKm]
      exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hB0 i)) hC0)
        (Real.exp_pos _).le
    -- lattice term `j` is a translate of `G` and obeys the Gaussian bound on `V`
    have hGder : ∀ (j : ℤ) (k : ℕ), k ≤ n → ∀ p ∈ V,
        ‖iteratedFDeriv ℝ k (fun z : ℝ × (ℝ × ℝ) => G (z.1, (z.2.1 - j * c, z.2.2))) p‖
          ≤ C * Real.exp (-a * (p.2.1 - j * c) ^ 2) := by
      intro j k hk p hp
      obtain ⟨hpK, -, hpL⟩ := hVmem p hp
      have e : (fun z : ℝ × (ℝ × ℝ) => G (z.1, (z.2.1 - j * c, z.2.2)))
          = fun z => G (z + ((0 : ℝ), ((-(j : ℝ) * c), (0 : ℝ)))) := by
        funext z
        congr 1
        simp [Prod.ext_iff, sub_eq_add_neg]
      have e2 : p + ((0 : ℝ), ((-(j : ℝ) * c), (0 : ℝ))) = (p.1, (p.2.1 - j * c, p.2.2)) := by
        simp [Prod.ext_iff, sub_eq_add_neg]
      rw [e, iteratedFDeriv_comp_add_right, e2]
      exact hCb k hk p.1 hpK (p.2.1 - j * c) p.2.2 hpL
    have hgjs : ∀ j : ℤ, ContDiffOn ℝ (n : WithTop ℕ∞)
        (fun z : ℝ × (ℝ × ℝ) => G (z.1, (z.2.1 - j * c, z.2.2))) V := by
      intro j
      have hφ : ContDiff ℝ (n : WithTop ℕ∞)
          (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1 - j * c, z.2.2))) := by fun_prop
      have hmaps : MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1 - j * c, z.2.2)))
          V (U ×ˢ Set.univ) := by
        intro z hz
        obtain ⟨hzK, -, -⟩ := hVmem z hz
        exact ⟨hKU hzK, trivial⟩
      exact hG.comp hφ.contDiffOn hmaps
    have hexp_bound : ∀ (q : ℝ) (j : ℤ), q ^ 2 ≤ (|q0| + 1) ^ 2 →
        Real.exp (-a * (q - j * c) ^ 2) ≤
          Real.exp (a * (|q0| + 1) ^ 2) * Real.exp (-(a * c ^ 2 / 2 * (j : ℝ) ^ 2)) := by
      intro q j hq
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg ha.le (sq_nonneg (q - j * c / 2)), mul_le_mul_of_nonneg_left hq ha.le]
    -- Leibniz bound on the open box `V`
    have hterm : ∀ (j : ℤ) (m : ℕ), m ≤ n → ∀ x ∈ V,
        ‖iteratedFDeriv ℝ m (fun z : ℝ × (ℝ × ℝ) => ψb z • G (z.1, (z.2.1 - j * c, z.2.2))) x‖
          ≤ Km m * Real.exp (-(a * c ^ 2 / 2 * (j : ℝ) ^ 2)) := by
      intro j m hm x hx
      have hψc : ContDiffOn ℝ (n : WithTop ℕ∞) ⇑ψb V := hψn.contDiffOn
      have hgj' := hgjs j
      rw [← iteratedFDerivWithin_of_isOpen m hVo hx]
      refine (norm_iteratedFDerivWithin_smul_le hψc hgj' hVo.uniqueDiffOn hx
        (by exact_mod_cast hm)).trans ?_
      have hz : ∀ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i ⇑ψb V x‖ *
            ‖iteratedFDerivWithin ℝ (m - i) (fun z : ℝ × (ℝ × ℝ) => G (z.1, (z.2.1 - j * c, z.2.2))) V x‖
          ≤ (m.choose i : ℝ) * B i * (C * Real.exp (a * (|q0| + 1) ^ 2) * Real.exp (-(a * c ^ 2 / 2 * (j : ℝ) ^ 2))) := by
        intro i hi
        have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [iteratedFDerivWithin_of_isOpen i hVo hx, iteratedFDerivWithin_of_isOpen (m - i) hVo hx]
        obtain ⟨-, hqI, -⟩ := hVmem x hx
        obtain ⟨hq1, hq2⟩ := hqI
        have hq : x.2.1 ^ 2 ≤ (|q0| + 1) ^ 2 :=
          sq_le_sq' (by linarith [neg_abs_le q0]) (by linarith [le_abs_self q0])
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hB i x) (Nat.cast_nonneg _)) ?_
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
        refine (hGder j (m - i) (le_trans (Nat.sub_le m i) hm) x hx).trans ?_
        calc C * Real.exp (-a * (x.2.1 - j * c) ^ 2)
            ≤ C * (Real.exp (a * (|q0| + 1) ^ 2) * Real.exp (-(a * c ^ 2 / 2 * (j : ℝ) ^ 2))) :=
              mul_le_mul_of_nonneg_left (hexp_bound x.2.1 j hq) hC0
          _ = C * Real.exp (a * (|q0| + 1) ^ 2) * Real.exp (-(a * c ^ 2 / 2 * (j : ℝ) ^ 2)) := by ring
      refine (Finset.sum_le_sum hz).trans ?_
      rw [← Finset.sum_mul, hKm]
      ring_nf
      exact le_rfl
    have hfs : ∀ j : ℤ, ContDiff ℝ (n : WithTop ℕ∞)
        (fun z : ℝ × (ℝ × ℝ) => ψb z • G (z.1, (z.2.1 - j * c, z.2.2))) :=
      fun j => perGen_glue ⇑ψb (fun z => G (z.1, (z.2.1 - j * c, z.2.2))) V hVo hψn hψsupp (hgjs j)
    have hbound : ∀ (j : ℤ) (k : ℕ), k ≤ n → ∀ x : ℝ × (ℝ × ℝ),
        ‖iteratedFDeriv ℝ k (fun z : ℝ × (ℝ × ℝ) => ψb z • G (z.1, (z.2.1 - j * c, z.2.2))) x‖
          ≤ Km k * Real.exp (-(a * c ^ 2 / 2 * (j : ℝ) ^ 2)) := by
      intro j k hk x
      by_cases hx : x ∈ V
      · exact hterm j k hk x hx
      · have hev : ⇑ψb =ᶠ[𝓝 x] (0 : ℝ × (ℝ × ℝ) → ℝ) :=
          notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hψsupp h))
        have h2 : (fun z : ℝ × (ℝ × ℝ) => ψb z • G (z.1, (z.2.1 - j * c, z.2.2)))
            =ᶠ[𝓝 x] (fun _ => (0 : E)) := by
          filter_upwards [hev] with z hz
          simp [hz]
        have h0 : iteratedFDeriv ℝ k (fun _ : ℝ × (ℝ × ℝ) => (0 : E)) x = 0 := by
          rcases Nat.eq_zero_or_pos k with rfl | hpos
          · simp
          · rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (Nat.pos_iff_ne_zero.mp hpos)]
            simp
        rw [(h2.iteratedFDeriv ℝ k).eq_of_nhds, h0, norm_zero]
        exact mul_nonneg (hKnn k) (Real.exp_pos _).le
    have hS : ContDiff ℝ (n : WithTop ℕ∞)
        (fun z : ℝ × (ℝ × ℝ) => ∑' j : ℤ, ψb z • G (z.1, (z.2.1 - j * c, z.2.2))) := by
      refine contDiff_tsum (f := fun (j : ℤ) (z : ℝ × (ℝ × ℝ)) => ψb z • G (z.1, (z.2.1 - j * c, z.2.2)))
        (v := fun k j => Km k * Real.exp (-(a * c ^ 2 / 2 * (j : ℝ) ^ 2))) hfs ?_ ?_
      · intro k _
        exact (perGen_gauss_summable (a * c ^ 2 / 2)
          (div_pos (mul_pos ha (pow_pos hc 2)) two_pos)).mul_left (Km k)
      · intro k j x hk
        exact hbound j k (by exact_mod_cast hk) x
    have hEq : (fun p : ℝ × (ℝ × ℝ) => ∑' j : ℤ, G (p.1, (p.2.1 - j * c, p.2.2)))
        =ᶠ[𝓝 (s0, (q0, η0))]
          (fun z : ℝ × (ℝ × ℝ) => ∑' j : ℤ, ψb z • G (z.1, (z.2.1 - j * c, z.2.2))) := by
      filter_upwards [hψ_one_nhds] with p hp
      simp only [hp, one_smul]
    exact hS.contDiffAt.congr_of_eventuallyEq hEq
  intro p hp
  exact (hloc p hp).contDiffWithinAt

end UnforcedLeray.Short.PartIIIb.Concrete
