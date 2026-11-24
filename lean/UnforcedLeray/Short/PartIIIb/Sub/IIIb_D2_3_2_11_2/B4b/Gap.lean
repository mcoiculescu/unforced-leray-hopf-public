import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2.GapTop

/-!
# Decaying all-order gap bound (helper of `B4b`, source 3604-3621, 4177-4179)

The version of `sepGapPointwiseTop` with the decay in `ϱ y`: for `ρ' ≥ max 1 (2 rOut)` and
`ϱ y ≥ ρ'`, `‖D^n_{(τ,y)} Φ(l,z;τ,y)‖ ≤ C l^{2Re μ+2} 1_{|z| ≤ Z} ρ'^{-4}` (gap `d = ρ'/2`,
`|y - l z| ≥ d`, `d^{-4-m} ≤ 2^{4+m} ρ'^{-4}`).  `C` does not depend on `ρ'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem gapDpow_le (ρ' : ℝ) (h1 : 1 ≤ ρ') (m : ℕ) :
    (ρ' / 2) ^ (-4 - (m : ℝ)) ≤ 2 ^ (4 + m) * (ρ' ^ 4)⁻¹ := by
  have hρ : 0 < ρ' := by linarith
  have e : (-4 - (m : ℝ)) = -(((4 + m : ℕ)) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_neg (by positivity), Real.rpow_natCast, div_pow, inv_div, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ h1 (by omega))

set_option maxHeartbeats 2000000 in
theorem sepGapDecayTop (hK : IIIa.SepKernelBounds) (ν : ℝ) (μ : ℂ) (rOut P : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hν : 0 < ν) (hP : 0 < P)
    (hS : IIIa.IsSepSource P rOut T)
    (hT : ∀ j k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => T x.1 x.2 j k))
    (Z : ℝ) (hZ : ∀ τ z, Z < ‖z‖ → T τ z = 0) (i : Fin 3) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ' : ℝ, 1 ≤ ρ' → 2 * rOut ≤ ρ' → ∀ x : ℝ × Space, ρ' ≤ ϱ x.2 →
      ∀ l ∈ Ioo (0 : ℝ) 1, ∀ z : Space, ‖iteratedFDeriv ℝ n (sepPhiJ ν μ T i (l, z)) x‖ ≤
        C * (l ^ (2 * μ.re + 2) * (if ‖z‖ ≤ Z then 1 else 0)) * (ρ' ^ 4)⁻¹ := by
  choose Cy hCy0 hCy using gapYBound hK
  choose M hM0 hM using fun (a : ℕ) (j k : Fin 3) =>
    gapTauBound P hP T hS.periodic hT Z j k a
  obtain ⟨Cfin, hCfin⟩ : ∃ C : ℝ, C = ∑ p : Fin 3 × Fin 3, ∑ m ∈ Finset.range (n + 1),
      (n.choose m : ℝ) * (Cy m * 2 ^ (4 + m)) * M (n - m) p.1 p.2 := ⟨_, rfl⟩
  have hCfin0 : 0 ≤ Cfin := by
    rw [hCfin]
    refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun m _ => ?_
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hCy0 m) (by positivity)))
      (hM0 _ _ _)
  refine ⟨2 * Cfin, by positivity, fun ρ' hρ1 hρr x hx l hl z => ?_⟩
  have hn : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hρ0 : 0 < ρ' := by linarith
  have hinv : 0 ≤ (ρ' ^ 4)⁻¹ := by positivity
  by_cases hz : ‖z‖ ≤ Z ∧ ϱ z ≤ rOut
  · obtain ⟨hzZ, hzr⟩ := hz
    obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = ρ' / 2 := ⟨_, rfl⟩
    have hd : 0 < d := by rw [hd_def]; positivity
    have hyr : rOut + d ≤ ϱ x.2 := by rw [hd_def]; linarith
    have hgap : d ≤ ‖x.2 - l • z‖ := gapNorm_ge l hl.1.le hl.2.le z x.2 d rOut hzr hyr
    have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith [hl.1, hl.2])
    obtain ⟨c0, hc0def⟩ : ∃ c0 : ℂ, c0 = -2 * (l : ℂ) ^ (2 * μ + 2) := ⟨_, rfl⟩
    obtain ⟨F, hF⟩ : ∃ F : Fin 3 × Fin 3 → ℝ × Space → ℂ, ∀ p x', F p x' =
        c0 * ((fderiv ℝ (fun v => IIIa.heatLerayK (ν * (1 - l ^ 2)) i p.1 v) (x'.2 - l • z)
          (coordinateVector p.2) : ℝ) : ℂ) :=
      ⟨_, fun _ _ => rfl⟩
    obtain ⟨G, hG⟩ : ∃ G : Fin 3 × Fin 3 → ℝ × Space → ℂ, ∀ p x',
        G p x' = ((T (x'.1 + 2 * Real.log l) z p.1 p.2 : ℝ) : ℂ) :=
      ⟨_, fun _ _ => rfl⟩
    have hdec : ∀ x', sepPhiJ ν μ T i (l, z) x' = ∑ p : Fin 3 × Fin 3, F p x' * G p x' := by
      intro x'
      rw [Fintype.sum_prod_type]
      simp only [sepPhiJ, sepPhi, hF, hG, hc0def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have hfunEq : sepPhiJ ν μ T i (l, z) = fun x' => ∑ p : Fin 3 × Fin 3, F p x' * G p x' :=
      funext hdec
    have hFs : ∀ p, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F p) := by
      intro p
      have hFeq : F p = fun x' => c0 * ((fderiv ℝ (fun v => IIIa.heatLerayK (ν * (1 - l ^ 2)) i p.1 v)
          (x'.2 - l • z) (coordinateVector p.2) : ℝ) : ℂ) := funext (hF p)
      rw [hFeq]
      exact gapFSmooth _ ht i p.1 p.2 (l • z) c0
    have hGs : ∀ p, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G p) := by
      intro p
      have hGeq : G p = fun x' => ((T (x'.1 + 2 * Real.log l) z p.1 p.2 : ℝ) : ℂ) := funext (hG p)
      rw [hGeq]
      exact gapGSmooth T hT p.1 p.2 _ z
    have hper : ∀ p : Fin 3 × Fin 3, ‖iteratedFDeriv ℝ n (fun y => F p y * G p y) x‖ ≤
        ‖c0‖ * (∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * (Cy m * 2 ^ (4 + m)) *
          M (n - m) p.1 p.2) * (ρ' ^ 4)⁻¹ := by
      intro p
      refine (norm_iteratedFDeriv_mul_le (hFs p) (hGs p) x hn).trans ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun m _ => ?_
      have hKs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun v => IIIa.heatLerayK (ν * (1 - l ^ 2)) i p.1 v) :=
        heatLerayKSmoothTop _ ht i p.1
      have hGK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : Space =>
          fderiv ℝ (fun u => IIIa.heatLerayK (ν * (1 - l ^ 2)) i p.1 u) v (coordinateVector p.2)) :=
        ((contDiff_infty_iff_fderiv.1 hKs).2).clm_apply contDiff_const
      have h1 : ‖iteratedFDeriv ℝ m (F p) x‖ ≤ ‖c0‖ * (Cy m * d ^ (-4 - (m : ℝ))) :=
        gapFBound _ hGK c0 (F p) (l • z) (fun x' => hF p x') d (Cy m) m
          (fun y hy => hCy m _ ht i p.1 p.2 (l • z) y d hd hy) x hgap
      have h2 : ‖iteratedFDeriv ℝ (n - m) (G p) x‖ ≤ M (n - m) p.1 p.2 := by
        have hGeq : G p = fun x' => ((T (x'.1 + 2 * Real.log l) z p.1 p.2 : ℝ) : ℂ) :=
          funext (hG p)
        rw [hGeq]
        exact hM (n - m) p.1 p.2 (2 * Real.log l) z hzZ x
      have hC0 : (0 : ℝ) ≤ (n.choose m : ℝ) := Nat.cast_nonneg _
      have hdp : d ^ (-4 - (m : ℝ)) ≤ 2 ^ (4 + m) * (ρ' ^ 4)⁻¹ := by
        rw [hd_def]; exact gapDpow_le ρ' hρ1 m
      have h1' : ‖iteratedFDeriv ℝ m (F p) x‖ ≤ ‖c0‖ * (Cy m * (2 ^ (4 + m) * (ρ' ^ 4)⁻¹)) :=
        h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdp (hCy0 m))
          (norm_nonneg _))
      calc (n.choose m : ℝ) * ‖iteratedFDeriv ℝ m (F p) x‖ * ‖iteratedFDeriv ℝ (n - m) (G p) x‖
          ≤ (n.choose m : ℝ) * (‖c0‖ * (Cy m * (2 ^ (4 + m) * (ρ' ^ 4)⁻¹))) * M (n - m) p.1 p.2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1' hC0) h2 (norm_nonneg _)
              (mul_nonneg hC0 (mul_nonneg (norm_nonneg _)
                (mul_nonneg (hCy0 m) (mul_nonneg (by positivity) hinv))))
        _ = ‖c0‖ * ((n.choose m : ℝ) * (Cy m * 2 ^ (4 + m)) * M (n - m) p.1 p.2) * (ρ' ^ 4)⁻¹ := by
            ring
    have hsum : ‖iteratedFDeriv ℝ n (fun x' => ∑ p : Fin 3 × Fin 3, F p x' * G p x') x‖ ≤
        ∑ p : Fin 3 × Fin 3, ‖iteratedFDeriv ℝ n (fun y => F p y * G p y) x‖ :=
      normIter_finsum Finset.univ (fun p y => F p y * G p y)
        (fun p _ => (hFs p).mul (hGs p)) n x
    have hc0n : ‖c0‖ = 2 * l ^ (2 * μ.re + 2) := by
      have hre : (2 * μ + 2).re = 2 * μ.re + 2 := by simp
      have h2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
      rw [hc0def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, h2, hre]
    rw [hfunEq, if_pos hzZ, mul_one]
    refine le_trans hsum ?_
    calc ∑ p : Fin 3 × Fin 3, ‖iteratedFDeriv ℝ n (fun y => F p y * G p y) x‖
        ≤ ∑ p : Fin 3 × Fin 3, ‖c0‖ * (∑ m ∈ Finset.range (n + 1),
            (n.choose m : ℝ) * (Cy m * 2 ^ (4 + m)) * M (n - m) p.1 p.2) * (ρ' ^ 4)⁻¹ :=
          Finset.sum_le_sum fun p _ => hper p
      _ = ‖c0‖ * Cfin * (ρ' ^ 4)⁻¹ := by
          rw [hCfin, Finset.mul_sum, Finset.sum_mul]
      _ = 2 * Cfin * l ^ (2 * μ.re + 2) * (ρ' ^ 4)⁻¹ := by rw [hc0n]; ring
  · have hT0 : ∀ τ, T τ z = 0 := by
      intro τ
      by_cases h1 : Z < ‖z‖
      · exact hZ τ z h1
      · have h2 : rOut < ϱ z := by
          by_contra h3
          exact hz ⟨not_lt.mp h1, not_lt.mp h3⟩
        exact hS.support τ z h2
    have hzero : ∀ x' : ℝ × Space, sepPhiJ ν μ T i (l, z) x' = 0 := by
      intro x'
      simp [sepPhiJ, sepPhi, hT0]
    have hfz : sepPhiJ ν μ T i (l, z) = fun _ => 0 := funext hzero
    rw [hfz]
    have hR : 0 ≤ 2 * Cfin * (l ^ (2 * μ.re + 2) * (if ‖z‖ ≤ Z then 1 else 0)) *
        (ρ' ^ 4)⁻¹ := by
      apply mul_nonneg _ hinv
      apply mul_nonneg (by positivity)
      apply mul_nonneg (Real.rpow_nonneg hl.1.le _)
      split_ifs <;> norm_num
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      simpa using hR
    · rw [iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]
      exact hR

end UnforcedLeray.Short.PartIIIb.Concrete
