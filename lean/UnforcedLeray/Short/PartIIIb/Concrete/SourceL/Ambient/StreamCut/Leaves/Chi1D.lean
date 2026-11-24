import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_3

/-!
# Proof of `SCChi1D` (source 4161-4166, 4178-4186)

For `φ(r) = χ(ν/r²)` put `u = ν/r²`, `v_j(u) = u^j χ^{(j)}(u)`.  The span `S_d` of `v_0,…,v_d`
is stable under the chain rule: for `g ∈ S_d` the function `r ↦ r^e g(ν/r²)` has derivative
`r^(e-1) h(ν/r²)` with `h ∈ S_{d+1}` (`h` independent of `ν`).  Iterating gives
`k`-th derivatives `r^(e-k) h_k(ν/r²)` with `h_k ∈ S_{d+k}`, and `S_d` functions are bounded on
`(0,∞)` since `v_j = 0` for `u > 1` and `χ^{(j)}` is bounded on `[0,1]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `u ↦ u^j χ^{(j)}(u)`. -/
def scChiVec (χ : ℝ → ℝ) (j : ℕ) : ℝ → ℝ := fun u => u ^ j * iteratedDeriv j χ u

/-- Span of `v_0, …, v_d`. -/
def scChiSpan (χ : ℝ → ℝ) (d : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ ((fun j => scChiVec χ j) '' Set.Iic d)

theorem scKeyPow (j : ℕ) (u : ℝ) : (j : ℝ) * u ^ (j - 1) * u = (j : ℝ) * u ^ j := by
  cases j with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel]
    rw [pow_succ]
    push_cast
    ring

theorem scChiVec_hasDerivAt {χ : ℝ → ℝ} (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (j : ℕ)
    (u : ℝ) :
    HasDerivAt (scChiVec χ j)
      ((j : ℝ) * u ^ (j - 1) * iteratedDeriv j χ u + u ^ j * iteratedDeriv (j + 1) χ u) u := by
  have hdiff : Differentiable ℝ (iteratedDeriv j χ) :=
    hs.differentiable_iteratedDeriv j (by exact_mod_cast (ENat.natCast_lt_top j))
  have hD : HasDerivAt (iteratedDeriv j χ) (iteratedDeriv (j + 1) χ u) u := by
    have := (hdiff u).hasDerivAt
    rwa [← iteratedDeriv_succ] at this
  exact (hasDerivAt_pow j u).mul hD

theorem scNuDeriv (ν r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun r : ℝ => ν / r ^ 2) (-2 * (ν / r ^ 2) / r) r := by
  have h := (hasDerivAt_const r ν).div (hasDerivAt_pow 2 r) (pow_ne_zero 2 hr)
  refine h.congr_deriv ?_
  norm_num <;> field_simp <;> ring

theorem scChiSpan_step {χ : ℝ → ℝ} (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (e : ℝ)
    (d : ℕ) {g : ℝ → ℝ} (hg : g ∈ scChiSpan χ d) :
    ∃ h ∈ scChiSpan χ (d + 1), ∀ ν r : ℝ, 0 < r →
      HasDerivAt (fun r => r ^ e * g (ν / r ^ 2)) (r ^ (e - 1) * h (ν / r ^ 2)) r := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    dsimp only
    have hjd : j ≤ d := Set.mem_Iic.mp hj
    have hmem0 : scChiVec χ j ∈ scChiSpan χ (d + 1) :=
      Submodule.subset_span ⟨j, Set.mem_Iic.mpr (by omega), rfl⟩
    have hmem1 : scChiVec χ (j + 1) ∈ scChiSpan χ (d + 1) :=
      Submodule.subset_span ⟨j + 1, Set.mem_Iic.mpr (by omega), rfl⟩
    refine ⟨(e • scChiVec χ j) - ((2 * (j : ℝ)) • scChiVec χ j) - ((2 : ℝ) • scChiVec χ (j + 1)),
      ?_, ?_⟩
    · exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hmem0)
        (Submodule.smul_mem _ _ hmem0)) (Submodule.smul_mem _ _ hmem1)
    · intro ν r hr
      have hu := scNuDeriv ν r hr.ne'
      have hv := (scChiVec_hasDerivAt hs j (ν / r ^ 2)).comp r hu
      have hp := Real.hasDerivAt_rpow_const (p := e) (x := r) (Or.inl hr.ne')
      have hprod := hp.mul hv
      have K := scKeyPow j (ν / r ^ 2)
      refine HasDerivAt.congr_deriv hprod ?_
      rw [Real.rpow_sub_one hr.ne' e]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      unfold scChiVec
      linear_combination (-(2 * r ^ e / r * iteratedDeriv j χ (ν / r ^ 2))) * K
  | zero =>
    refine ⟨0, Submodule.zero_mem _, fun ν r hr => ?_⟩
    simp only [Pi.zero_apply, mul_zero]
    exact hasDerivAt_const r (0 : ℝ)
  | add x y hx hy ih1 ih2 =>
    obtain ⟨h1, m1, E1⟩ := ih1
    obtain ⟨h2, m2, E2⟩ := ih2
    refine ⟨h1 + h2, Submodule.add_mem _ m1 m2, fun ν r hr => ?_⟩
    have hf : (fun r : ℝ => r ^ e * (x + y) (ν / r ^ 2))
        = fun r => r ^ e * x (ν / r ^ 2) + r ^ e * y (ν / r ^ 2) := by
      funext s
      simp [mul_add]
    rw [hf]
    have := (E1 ν r hr).add (E2 ν r hr)
    refine HasDerivAt.congr_deriv this ?_
    simp only [Pi.add_apply]
    ring
  | smul a x hx ih =>
    obtain ⟨h1, m1, E1⟩ := ih
    refine ⟨a • h1, Submodule.smul_mem _ _ m1, fun ν r hr => ?_⟩
    have hf : (fun r : ℝ => r ^ e * (a • x) (ν / r ^ 2))
        = fun r => a * (r ^ e * x (ν / r ^ 2)) := by
      funext s
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hf]
    have := (E1 ν r hr).const_mul a
    refine HasDerivAt.congr_deriv this ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem scChiVec_bounded {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) (j : ℕ) :
    ∃ M : ℝ, ∀ u : ℝ, 0 < u → |scChiVec χ j u| ≤ M := by
  have hcont : Continuous (iteratedDeriv j χ) :=
    hχ.smooth.continuous_iteratedDeriv j (by exact_mod_cast (ENat.natCast_lt_top j).le)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨M, fun u hu => ?_⟩
  unfold scChiVec
  by_cases h1 : u ≤ 1
  · have hpow : u ^ j ≤ 1 := pow_le_one₀ hu.le h1
    have hD := hM u ⟨hu.le, h1⟩
    rw [Real.norm_eq_abs] at hD
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu.le j)]
    exact (mul_le_of_le_one_left (abs_nonneg _) hpow).trans hD
  · have hgt : 1 < u := not_le.mp h1
    have hzero : iteratedDeriv j χ u = 0 := by
      have hev : χ =ᶠ[nhds u] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with t ht
        exact hχ.zero t (le_of_lt ht)
      rw [Filter.EventuallyEq.iteratedDeriv_eq j hev, iteratedDeriv_const]
      simp
    rw [hzero, mul_zero, abs_zero]
    exact (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)

theorem scChiSpan_bound {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) (d : ℕ) {g : ℝ → ℝ}
    (hg : g ∈ scChiSpan χ d) : ∃ M : ℝ, ∀ u : ℝ, 0 < u → |g u| ≤ M := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, _, rfl⟩ := hx
    exact scChiVec_bounded hχ j
  | zero => exact ⟨0, fun u _ => by simp⟩
  | add x y hx hy ih1 ih2 =>
    obtain ⟨M1, h1⟩ := ih1
    obtain ⟨M2, h2⟩ := ih2
    refine ⟨M1 + M2, fun u hu => ?_⟩
    simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (h1 u hu) (h2 u hu))
  | smul a x hx ih =>
    obtain ⟨M, h⟩ := ih
    refine ⟨|a| * M, fun u hu => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (h u hu) (abs_nonneg a)

theorem scChiSpan_iter {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) (k : ℕ) (e : ℝ) (d : ℕ)
    {g : ℝ → ℝ} (hg : g ∈ scChiSpan χ d) :
    ∃ h ∈ scChiSpan χ (d + k), ∀ ν r : ℝ, 0 < r →
      iteratedDeriv k (fun r => r ^ e * g (ν / r ^ 2)) r = r ^ (e - k) * h (ν / r ^ 2) := by
  induction k with
  | zero =>
    exact ⟨g, by simpa using hg, fun ν r hr => by simp⟩
  | succ k ih =>
    obtain ⟨h, hm, E⟩ := ih
    obtain ⟨h', hm', S⟩ := scChiSpan_step hχ.smooth (e - k) (d + k) hm
    refine ⟨h', hm', fun ν r hr => ?_⟩
    have hev : iteratedDeriv k (fun r => r ^ e * g (ν / r ^ 2))
        =ᶠ[nhds r] (fun s => s ^ (e - k) * h (ν / s ^ 2)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
      exact E ν s hs
    rw [iteratedDeriv_succ, hev.deriv_eq, (S ν r hr).deriv]
    congr 1
    push_cast
    ring_nf

theorem scChi1D (χy : ℝ → ℝ) : SCChi1D χy := by
  by_cases hχ : IsStreamCutoff χy
  swap
  · exact ⟨0, fun ν _ h => absurd h hχ⟩
  have hv0 : scChiVec χy 0 ∈ scChiSpan χy 0 :=
    Submodule.subset_span ⟨0, Set.mem_Iic.mpr le_rfl, rfl⟩
  obtain ⟨h1, hm1, S1⟩ := scChiSpan_step hχ.smooth 0 0 hv0
  have hloc : ∀ ν s : ℝ, 0 < s → chiYr ν 1 χy =ᶠ[nhds s]
      (fun r => r ^ (0 : ℝ) * scChiVec χy 0 (ν / r ^ 2)) := by
    intro ν s hs
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    have ht' : 0 < t := ht
    have ht0 : t ≠ 0 := ht'.ne'
    simp [chiYr, ht0, scChiVec]
  have hψloc : ∀ ν s : ℝ, 0 < s → (fun t => deriv (chiYr ν 1 χy) t / t)
      =ᶠ[nhds s] (fun t => t ^ ((0 : ℝ) - 1 - 1) * h1 (ν / t ^ 2)) := by
    intro ν s hs
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    have ht' : 0 < t := ht
    show deriv (chiYr ν 1 χy) t / t = t ^ ((0 : ℝ) - 1 - 1) * h1 (ν / t ^ 2)
    rw [(hloc ν t ht').deriv_eq, (S1 ν t ht').deriv, Real.rpow_sub_one ht'.ne' ((0 : ℝ) - 1)]
    ring
  have hE : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ ν r : ℝ, 0 < ν → 0 < r →
      |iteratedDeriv k (chiYr ν 1 χy) r| ≤ M * r ^ (-(k : ℝ)) ∧
      |iteratedDeriv k (fun r => deriv (chiYr ν 1 χy) r / r) r| ≤ M * r ^ (-(2 : ℝ) - k) := by
    intro k
    obtain ⟨h0k, hm0k, E0k⟩ := scChiSpan_iter hχ k 0 0 hv0
    obtain ⟨h1k, hm1k, E1k⟩ := scChiSpan_iter hχ k ((0 : ℝ) - 1 - 1) (0 + 1) hm1
    obtain ⟨M0, hM0⟩ := scChiSpan_bound hχ _ hm0k
    obtain ⟨M1, hM1⟩ := scChiSpan_bound hχ _ hm1k
    refine ⟨|M0| + |M1|, add_nonneg (abs_nonneg _) (abs_nonneg _), fun ν r hν hr => ?_⟩
    have hu : 0 < ν / r ^ 2 := div_pos hν (by positivity)
    constructor
    · rw [(hloc ν r hr).iteratedDeriv_eq k, E0k ν r hr, zero_sub, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hr.le _)]
      have hb : |h0k (ν / r ^ 2)| ≤ |M0| + |M1| :=
        (hM0 _ hu).trans ((le_abs_self M0).trans (le_add_of_nonneg_right (abs_nonneg M1)))
      exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hr.le _) |>.trans_eq (mul_comm _ _)
    · have hex : (0 : ℝ) - 1 - 1 - k = -(2 : ℝ) - k := by ring
      rw [Filter.EventuallyEq.iteratedDeriv_eq k (hψloc ν r hr), E1k ν r hr, hex, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hr.le _)]
      have hb : |h1k (ν / r ^ 2)| ≤ |M0| + |M1| :=
        (hM1 _ hu).trans ((le_abs_self M1).trans (le_add_of_nonneg_left (abs_nonneg M0)))
      exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hr.le _) |>.trans_eq (mul_comm _ _)
  choose M hMnn hMb using hE
  refine ⟨Finset.sum (Finset.range 8) M, fun ν hν _ k hk r hr => ?_⟩
  have hle : M k ≤ Finset.sum (Finset.range 8) M :=
    Finset.single_le_sum (fun i _ => hMnn i) (Finset.mem_range.mpr (by omega))
  obtain ⟨b1, b2⟩ := hMb k ν r hν hr
  exact ⟨b1.trans (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hr.le _)),
    b2.trans (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hr.le _))⟩

end UnforcedLeray.Short.PartIIIb.Concrete
