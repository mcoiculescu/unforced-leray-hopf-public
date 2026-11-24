import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1_1.SeedJet

/-!
# All-order jet decay of the seed dual kernels (helper for `PartIII-a:T21/c5/1/1/2/1-2`)

Source `the November 2 reference manuscript`
lines 593-610 (`eq:short-seed-functional`) and 2891-2897 ("the planar dual kernels and their
fixed derivatives have the `O(|y|^{-2-j})` decay").

For a Part I seed kernel `κ` the dual kernels are `λ₀(z) = F(conj w)`, `w = z₁ + i z₂`, with
`F(u) = u² β(|u|²)` and `β(s) = K b(s)/(e^{-s/4} - a₀)` (`SeedJet.lean`).  Here we prove the
decay of every derivative:

* `regB_jet_decay`: `|b^{(k)}(s)| (1+s)^{k+2}` is bounded on `s ≥ 0`, by induction from the
  differentiated regular equation `s b^{(k+2)} = (κ b)^{(k)}/4 - (k+3) b^{(k+1)}` and the rapid
  decay of `(κ b)^{(k)}`;
* `betaFun_jet_decay`: the same for `β`, using `m = (E - a₀)⁻¹ = -a₀⁻¹ + a₀⁻¹ E m`;
* `angularTwo_jet_decay`: `‖D^n F(u)‖ (1+|u|)^{n+2}` is bounded, by rescaling
  `F(u) = R^{-2} F_R(u/R)`, `F_R(v) = v² R⁴ β(R²|v|²)`, `R = |u|`;
* `lamP_jet_decay`: the bounds for `κ.lamP j`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa.LamJetInf

open UnforcedLeray.ComplexODEC UnforcedLeray.Short.IIIa.SeedJet2Aux

/-- `(1+s)^n e^{-s/4}` is bounded on `s ≥ 0`. -/
theorem pow_mul_exp_le (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
    (1 + s) ^ n * Real.exp ((-1 / 4) * s) ≤ C := by
  refine ⟨4 ^ n * n.factorial * Real.exp (1 / 4), by positivity, fun s hs => ?_⟩
  have h := Real.pow_div_factorial_le_exp (x := (1 + s) / 4) (by positivity) n
  rw [div_le_iff₀ (by positivity)] at h
  have e1 : Real.exp ((1 + s) / 4) = Real.exp (1 / 4) * Real.exp (s / 4) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (s / 4) * Real.exp ((-1 / 4) * s) = 1 := by
    rw [← Real.exp_add]
    have : s / 4 + (-1 / 4) * s = 0 := by ring
    rw [this, Real.exp_zero]
  have e3 : (1 + s) ^ n = 4 ^ n * ((1 + s) / 4) ^ n := by
    rw [div_pow]; field_simp
  calc (1 + s) ^ n * Real.exp ((-1 / 4) * s)
      = 4 ^ n * ((1 + s) / 4) ^ n * Real.exp ((-1 / 4) * s) := by rw [e3]
    _ ≤ 4 ^ n * (Real.exp ((1 + s) / 4) * n.factorial) * Real.exp ((-1 / 4) * s) := by gcongr
    _ = 4 ^ n * n.factorial * Real.exp (1 / 4) *
          (Real.exp (s / 4) * Real.exp ((-1 / 4) * s)) := by rw [e1]; ring
    _ = 4 ^ n * n.factorial * Real.exp (1 / 4) := by rw [e2, mul_one]

/-- Rapid decay of `(κ b)^{(k)}` on `s ≥ 0`. -/
theorem kappa_regB_rapid {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) (k M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      ‖iteratedDeriv k (fun σ => kappa c σ * regB c σ) s‖ * (1 + s) ^ M ≤ C := by
  have hc := hF.im_ne_zero
  have hb := (derivBound_kappa hc).mul (contDiff_kappa hc) (contDiff_regB hc)
    (fun _ _ => (Real.exp_pos _).le) (fun _ _ => zero_le_one) (derivBound_regB hF)
  obtain ⟨C, N, hC0, hCb⟩ := hb k k le_rfl
  obtain ⟨C', hC'0, hC'⟩ := pow_mul_exp_le (N + M)
  refine ⟨C * C', by positivity, fun s hs => ?_⟩
  have h1 := hCb s hs
  simp only [mul_one] at h1
  rw [abs_of_nonneg hs] at h1
  calc ‖iteratedDeriv k (fun σ => kappa c σ * regB c σ) s‖ * (1 + s) ^ M
      ≤ C * (1 + s) ^ N * Real.exp ((-1 / 4) * s) * (1 + s) ^ M := by gcongr
    _ = C * ((1 + s) ^ (N + M) * Real.exp ((-1 / 4) * s)) := by ring
    _ ≤ C * C' := by gcongr; exact hC' s hs

/-- **All-order decay of the regular solution**: `|b^{(k)}(s)| (1+s)^{k+2} ≤ C` on `s ≥ 0`. -/
theorem regB_jet_decay {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      ‖iteratedDeriv k (regB c) s‖ * (1 + s) ^ (k + 2) ≤ C := by
  have hc := hF.im_ne_zero
  have hbc := contDiff_regB hc
  have step : ∀ k : ℕ, (∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      ‖iteratedDeriv (k + 1) (regB c) s‖ * (1 + s) ^ (k + 3) ≤ C) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
        ‖iteratedDeriv (k + 2) (regB c) s‖ * (1 + s) ^ (k + 4) ≤ C := by
    intro k ⟨C₁, hC₁0, hC₁⟩
    obtain ⟨C₂, hC₂0, hC₂⟩ := kappa_regB_rapid hF k (k + 3)
    have hcont : Continuous (iteratedDeriv (k + 2) (regB c)) :=
      hbc.continuous_iteratedDeriv (k + 2) (le_top_nat (k + 2))
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hcont.continuousOn (s := Icc (0 : ℝ) 1))
    refine ⟨max (|K| * 2 ^ (k + 4)) (2 * (C₂ / 4 + ((k : ℝ) + 3) * C₁)),
      le_trans (by positivity) (le_max_left _ _), fun s hs => ?_⟩
    rcases le_total s 1 with h1 | h1
    · refine le_trans ?_ (le_max_left _ _)
      have hb := (hK s ⟨hs, h1⟩).trans (le_abs_self K)
      have hp : (1 + s) ^ (k + 4) ≤ 2 ^ (k + 4) :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
      exact mul_le_mul hb hp (by positivity) (abs_nonneg _)
    · refine le_trans ?_ (le_max_right _ _)
      have hode := regB_iteratedDeriv_add_two hc k s
      have hs0 : 0 < s := by linarith
      have hk3 : ‖((k : ℂ) + 3)‖ = (k : ℝ) + 3 := by
        rw [show ((k : ℂ) + 3) = (((k : ℝ) + 3 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hnorm : s * ‖iteratedDeriv (k + 2) (regB c) s‖ ≤
          ‖iteratedDeriv k (fun σ => kappa c σ * regB c σ) s‖ / 4 +
            ((k : ℝ) + 3) * ‖iteratedDeriv (k + 1) (regB c) s‖ := by
        have := congrArg norm hode
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0] at this
        rw [this]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_div, norm_mul, hk3]
        norm_num
      have hA := hC₂ s hs
      have hB := hC₁ s hs
      have h2s : 1 + s ≤ 2 * s := by linarith
      calc ‖iteratedDeriv (k + 2) (regB c) s‖ * (1 + s) ^ (k + 4)
          = ‖iteratedDeriv (k + 2) (regB c) s‖ * (1 + s) * (1 + s) ^ (k + 3) := by ring
        _ ≤ ‖iteratedDeriv (k + 2) (regB c) s‖ * (2 * s) * (1 + s) ^ (k + 3) := by gcongr
        _ = 2 * ((s * ‖iteratedDeriv (k + 2) (regB c) s‖) * (1 + s) ^ (k + 3)) := by ring
        _ ≤ 2 * ((‖iteratedDeriv k (fun σ => kappa c σ * regB c σ) s‖ / 4 +
              ((k : ℝ) + 3) * ‖iteratedDeriv (k + 1) (regB c) s‖) * (1 + s) ^ (k + 3)) := by
          gcongr
        _ = 2 * ((‖iteratedDeriv k (fun σ => kappa c σ * regB c σ) s‖ * (1 + s) ^ (k + 3)) / 4 +
              ((k : ℝ) + 3) * (‖iteratedDeriv (k + 1) (regB c) s‖ * (1 + s) ^ (k + 3))) := by
          ring
        _ ≤ 2 * (C₂ / 4 + ((k : ℝ) + 3) * C₁) := by gcongr
  have base1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      ‖iteratedDeriv (0 + 1) (regB c) s‖ * (1 + s) ^ (0 + 3) ≤ C := by
    obtain ⟨C, hC0, hC⟩ := exists_decay_deriv_regB hF
    exact ⟨C, hC0, fun s hs => by rw [zero_add, iteratedDeriv_one]; exact hC s hs⟩
  have hall : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      ‖iteratedDeriv (k + 1) (regB c) s‖ * (1 + s) ^ (k + 3) ≤ C := by
    intro k
    induction k with
    | zero => exact base1
    | succ k ih => exact step k ih
  rcases k with _ | k
  · obtain ⟨C, hC0, hC⟩ := exists_decay_regB hF
    exact ⟨C, hC0, fun s hs => by rw [iteratedDeriv_zero]; exact hC s hs⟩
  · exact hall k

/-- **All-order decay of the radial profile `β = K b m`**: `|β^{(n)}(s)|(1+s)^{n+2} ≤ C`. -/
theorem betaFun_jet_decay {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) {a₀ : ℂ}
    (ha : a₀.im ≠ 0) (K : ℂ) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      ‖iteratedDeriv n (betaFun c a₀ K) s‖ * (1 + s) ^ (n + 2) ≤ C := by
  have hc := hF.im_ne_zero
  have ha0 : a₀ ≠ 0 := fun h => ha (by simp [h])
  have hb := contDiff_regB hc
  have hm := contDiff_resI ha
  have hsplit : betaFun c a₀ K = fun s => (-(K * a₀⁻¹)) * regB c s +
      (K * a₀⁻¹) * ((regB c s * gaussE s) * resI a₀ s) := by
    funext s
    have hden : denM a₀ s = (gaussE s - a₀)⁻¹ := by
      unfold denM gaussE4 gaussE
      congr 3
      ring
    have hres : resI a₀ s = (gaussE s - a₀)⁻¹ := rfl
    have hE : gaussE s - a₀ ≠ 0 := ofReal_sub_ne_zero ha _
    unfold betaFun
    rw [hden, hres]
    field_simp
    ring
  have hbE : DerivBound (fun s => 1 * Real.exp ((-1 / 4) * s)) (Ici 0)
      (fun s => regB c s * gaussE s) :=
    DerivBound.mul hb contDiff_gaussE (fun _ _ => zero_le_one) (fun _ _ => (Real.exp_pos _).le)
      (derivBound_regB hF) (fun k => (derivBound_gaussE k).mono_set (subset_univ _))
  have hbEm : DerivBound (fun s => 1 * Real.exp ((-1 / 4) * s) * 1) (Ici 0)
      (fun s => (regB c s * gaussE s) * resI a₀ s) :=
    DerivBound.mul (hb.mul contDiff_gaussE) hm
      (fun _ _ => mul_nonneg zero_le_one (Real.exp_pos _).le) (fun _ _ => zero_le_one) hbE
      (fun k => derivBound_resI ha k)
  obtain ⟨C₁, hC₁0, hC₁⟩ := regB_jet_decay hF n
  obtain ⟨C₂, N, hC₂0, hC₂⟩ := hbEm n n le_rfl
  obtain ⟨C₃, hC₃0, hC₃⟩ := pow_mul_exp_le (N + (n + 2))
  refine ⟨‖K * a₀⁻¹‖ * C₁ + ‖K * a₀⁻¹‖ * (C₂ * C₃), by positivity, fun s hs => ?_⟩
  have hgc : ContDiff ℝ ∞ (fun s => (regB c s * gaussE s) * resI a₀ s) :=
    (hb.mul contDiff_gaussE).mul hm
  have hderiv : iteratedDeriv n (betaFun c a₀ K) s =
      (-(K * a₀⁻¹)) * iteratedDeriv n (regB c) s +
        (K * a₀⁻¹) * iteratedDeriv n (fun s => (regB c s * gaussE s) * resI a₀ s) s := by
    rw [hsplit, iteratedDeriv_fun_add (contDiffAt_const.mul (contDiffAt_of_infty hb n s))
      (contDiffAt_const.mul (contDiffAt_of_infty hgc n s)),
      iteratedDeriv_const_mul _ (contDiffAt_of_infty hb n s),
      iteratedDeriv_const_mul _ (contDiffAt_of_infty hgc n s)]
  have h1 := hC₁ s hs
  have h2 := hC₂ s hs
  simp only [mul_one, one_mul] at h2
  rw [abs_of_nonneg hs] at h2
  have h3 := hC₃ s hs
  rw [hderiv]
  calc ‖(-(K * a₀⁻¹)) * iteratedDeriv n (regB c) s +
        (K * a₀⁻¹) * iteratedDeriv n (fun s => (regB c s * gaussE s) * resI a₀ s) s‖ *
          (1 + s) ^ (n + 2)
      ≤ (‖K * a₀⁻¹‖ * ‖iteratedDeriv n (regB c) s‖ +
          ‖K * a₀⁻¹‖ * ‖iteratedDeriv n (fun s => (regB c s * gaussE s) * resI a₀ s) s‖) *
          (1 + s) ^ (n + 2) := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_neg]
    _ = ‖K * a₀⁻¹‖ * (‖iteratedDeriv n (regB c) s‖ * (1 + s) ^ (n + 2)) +
          ‖K * a₀⁻¹‖ * (‖iteratedDeriv n (fun s => (regB c s * gaussE s) * resI a₀ s) s‖ *
            (1 + s) ^ (n + 2)) := by ring
    _ ≤ ‖K * a₀⁻¹‖ * C₁ + ‖K * a₀⁻¹‖ * (C₂ * (1 + s) ^ N * Real.exp ((-1 / 4) * s) *
            (1 + s) ^ (n + 2)) := by gcongr
    _ = ‖K * a₀⁻¹‖ * C₁ + ‖K * a₀⁻¹‖ * (C₂ * ((1 + s) ^ (N + (n + 2)) *
            Real.exp ((-1 / 4) * s))) := by ring
    _ ≤ ‖K * a₀⁻¹‖ * C₁ + ‖K * a₀⁻¹‖ * (C₂ * C₃) := by gcongr

/-- **Planar all-order decay of `F(u) = u² β(|u|²)`** by rescaling `F(u) = R^{-2} F_R(u/R)`. -/
theorem angularTwo_jet_decay {β : ℝ → ℂ} (hβ : ContDiff ℝ ∞ β)
    (hdec : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      ‖iteratedDeriv m β s‖ * (1 + s) ^ (m + 2) ≤ C)
    (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ,
      ‖iteratedFDeriv ℝ n (fun w : ℂ => w ^ 2 * β (‖w‖ ^ 2)) u‖ * (1 + ‖u‖) ^ (n + 2) ≤ C := by
  set F : ℂ → ℂ := fun w => w ^ 2 * β (‖w‖ ^ 2) with hFdef
  have hF : ContDiff ℝ ∞ F := Planar.contDiff_angularTwo hβ
  obtain ⟨A, N, hA⟩ := Planar.norm_iteratedFDeriv_angularTwo_le n
  choose Cm hCm0 hCm using hdec
  have hcont : Continuous (iteratedFDeriv ℝ n F) :=
    hF.continuous_iteratedFDeriv (le_top_nat n)
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hcont.continuousOn
  set B : ℝ := |A| * 2 ^ N * ∑ m ∈ Finset.range (n + 1), Cm m with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ∑ m ∈ Finset.range (n + 1), Cm m := Finset.sum_nonneg fun m _ => hCm0 m
    positivity
  refine ⟨max (|K₀| * 2 ^ (n + 2)) (2 ^ (n + 2) * B),
    le_trans (by positivity) (le_max_left _ _), fun u => ?_⟩
  rcases le_or_gt ‖u‖ 1 with hu | hu
  · refine le_trans ?_ (le_max_left _ _)
    have h1 := (hK₀ u (mem_closedBall_zero_iff.2 hu)).trans (le_abs_self _)
    have h2 : (1 + ‖u‖) ^ (n + 2) ≤ 2 ^ (n + 2) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    exact mul_le_mul h1 h2 (by positivity) (abs_nonneg _)
  · refine le_trans ?_ (le_max_right _ _)
    set R : ℝ := ‖u‖ with hR
    have hR1 : 1 < R := hu
    have hR0 : 0 < R := by linarith
    set βR : ℝ → ℂ := fun s => ((R ^ 4 : ℝ) : ℂ) * β (R ^ 2 * s) with hβR
    have hβRc : ContDiff ℝ ∞ βR :=
      contDiff_const.mul (hβ.comp (contDiff_const.mul contDiff_id))
    set FR : ℂ → ℂ := fun w => w ^ 2 * βR (‖w‖ ^ 2) with hFR
    have hFRc : ContDiff ℝ ∞ FR := Planar.contDiff_angularTwo hβRc
    set L : ℂ →L[ℝ] ℂ := (R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ with hL
    have hLw : ∀ w : ℂ, L w = (R⁻¹ : ℝ) • w := fun w => rfl
    have hid : F = ((R ^ 2)⁻¹ : ℝ) • (FR ∘ L) := by
      funext w
      simp only [Pi.smul_apply, Function.comp_apply, hFR, hβR, hFdef, hLw]
      have hn : ‖(R⁻¹ : ℝ) • w‖ = R⁻¹ * ‖w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR0)]
      rw [hn]
      have hsq : R ^ 2 * (R⁻¹ * ‖w‖) ^ 2 = ‖w‖ ^ 2 := by field_simp
      rw [hsq, Complex.real_smul, Complex.real_smul]
      have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
      push_cast
      field_simp
    have hLn : ‖L‖ ≤ R⁻¹ := by
      rw [hL]
      refine (norm_smul_le (R⁻¹ : ℝ) (ContinuousLinearMap.id ℝ ℂ)).trans ?_
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR0)]
      exact mul_le_of_le_one_right (inv_pos.2 hR0).le ContinuousLinearMap.norm_id_le
    have hLu1 : ‖L u‖ = 1 := by
      rw [hLw, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR0), ← hR]
      field_simp
    have hnorm : ‖iteratedFDeriv ℝ n F u‖ ≤
        (R ^ 2)⁻¹ * (‖iteratedFDeriv ℝ n FR (L u)‖ * R⁻¹ ^ n) := by
      rw [hid, iteratedFDeriv_const_smul_apply
        ((hFRc.comp L.contDiff).contDiffAt.of_le (le_top_nat n)), norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      gcongr
      rw [ContinuousLinearMap.iteratedFDeriv_comp_right L hFRc u (le_top_nat n)]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      gcongr
    have hβRm : ∀ m : ℕ, ‖iteratedDeriv m βR (‖L u‖ ^ 2)‖ ≤ Cm m := by
      intro m
      rw [hLu1, one_pow]
      have e1 : iteratedDeriv m βR 1 =
          ((R ^ 4 : ℝ) : ℂ) * iteratedDeriv m (fun s => β (R ^ 2 * s)) 1 :=
        iteratedDeriv_const_mul _
          ((hβ.comp (contDiff_const.mul contDiff_id)).contDiffAt.of_le (le_top_nat m))
      rw [e1, iteratedDeriv_comp_const_smul (hβ.of_le (le_top_nat m)) (R ^ 2), norm_mul,
        norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity), abs_of_pos (by positivity), mul_one]
      have hb := hCm m (R ^ 2) (by positivity)
      have hp : R ^ 4 * (R ^ 2) ^ m ≤ (1 + R ^ 2) ^ (m + 2) := by
        calc R ^ 4 * (R ^ 2) ^ m = (R ^ 2) ^ (m + 2) := by ring
          _ ≤ (1 + R ^ 2) ^ (m + 2) := pow_le_pow_left₀ (by positivity) (by linarith) _
      calc R ^ 4 * ((R ^ 2) ^ m * ‖iteratedDeriv m β (R ^ 2)‖)
          = (R ^ 4 * (R ^ 2) ^ m) * ‖iteratedDeriv m β (R ^ 2)‖ := by ring
        _ ≤ (1 + R ^ 2) ^ (m + 2) * ‖iteratedDeriv m β (R ^ 2)‖ := by gcongr
        _ = ‖iteratedDeriv m β (R ^ 2)‖ * (1 + R ^ 2) ^ (m + 2) := by ring
        _ ≤ Cm m := hb
    have hFRb : ‖iteratedFDeriv ℝ n FR (L u)‖ ≤ B := by
      refine (hA βR (hβRc.of_le (le_top_nat n)) (L u)).trans ?_
      rw [hLu1]
      have hsum : ∑ m ∈ Finset.range (n + 1), ‖iteratedDeriv m βR (‖L u‖ ^ 2)‖ ≤
          ∑ m ∈ Finset.range (n + 1), Cm m := Finset.sum_le_sum fun m _ => hβRm m
      rw [hLu1] at hsum
      have hs0 : 0 ≤ ∑ m ∈ Finset.range (n + 1), ‖iteratedDeriv m βR (1 ^ 2)‖ :=
        Finset.sum_nonneg fun m _ => norm_nonneg _
      calc A * (1 + 1) ^ N * ∑ m ∈ Finset.range (n + 1), ‖iteratedDeriv m βR (1 ^ 2)‖
          ≤ |A| * (1 + 1) ^ N * ∑ m ∈ Finset.range (n + 1), ‖iteratedDeriv m βR (1 ^ 2)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self A)
              (by positivity)) hs0
        _ ≤ |A| * 2 ^ N * ∑ m ∈ Finset.range (n + 1), Cm m := by
            rw [show (1 : ℝ) + 1 = 2 by norm_num]
            exact mul_le_mul_of_nonneg_left hsum (by positivity)
    have h2R : 1 + ‖u‖ ≤ 2 * R := by rw [← hR]; linarith
    calc ‖iteratedFDeriv ℝ n F u‖ * (1 + ‖u‖) ^ (n + 2)
        ≤ (R ^ 2)⁻¹ * (B * R⁻¹ ^ n) * (2 * R) ^ (n + 2) := by
          gcongr
          exact hnorm.trans (by gcongr)
      _ = 2 ^ (n + 2) * B := by
          have hRn : R ^ n * R⁻¹ ^ n = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ hR0.ne', one_pow]
          have hR2 : (R ^ 2)⁻¹ * R ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
          calc (R ^ 2)⁻¹ * (B * R⁻¹ ^ n) * (2 * R) ^ (n + 2)
              = 2 ^ (n + 2) * B * ((R ^ 2)⁻¹ * R ^ 2) * (R ^ n * R⁻¹ ^ n) := by ring
            _ = 2 ^ (n + 2) * B := by rw [hR2, hRn, mul_one, mul_one]

/-- **All-order jet decay of the seed dual kernels**: `κ.lamP j` is `C^∞` and
`‖D^n λ_j(z)‖ (1 + ‖z‖)^{n+2} ≤ C_n` (SP 2891-2897). -/
theorem lamP_jet_decay {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    (∀ j, ContDiff ℝ ∞ (κ.lamP j)) ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) (z : ℝ × ℝ),
      ‖iteratedFDeriv ℝ n (κ.lamP j) z‖ * (1 + ‖z‖) ^ (n + 2) ≤ C := by
  obtain ⟨lam, h, hh, ℓ, hIS, -, -, -, hlamP⟩ := CutFTCGradPerSum.lamP_eq_seedDualExplicit hκ
  obtain ⟨c, F, β₀, μ, hF, hG⟩ := seed_greenN_eq_mode hIS
  have hre := hIS.re_pos
  have ha₀ : (Complex.I * lam / 2).im ≠ 0 := by
    have : (Complex.I * lam / 2).im = lam.re / 2 := by simp [Complex.div_ofNat_im]
    rw [this]
    positivity
  set K : ℂ := (PartI.seedJ h)⁻¹ / (2 * Real.pi : ℂ) * μ * β₀ with hK
  set β : ℝ → ℂ := betaFun c (Complex.I * lam / 2) K with hβ
  have hβc : ContDiff ℝ ∞ β := (betaFun_bounds hF ha₀ K).1
  have hdec : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      ‖iteratedDeriv m β s‖ * (1 + s) ^ (m + 2) ≤ C := fun m => betaFun_jet_decay hF ha₀ K m
  set F₀ : ℂ → ℂ := fun w => w ^ 2 * β (‖w‖ ^ 2) with hF₀
  have hF0c : ContDiff ℝ ∞ F₀ := Planar.contDiff_angularTwo hβc
  have h0eq : ∀ z, κ.lamP 0 z = F₀ (conj (planeToC z)) := fun z => by
    rw [hlamP 0]
    exact seedDualExplicit_zero_eq hre hG z
  have hfe : κ.lamP 0 = F₀ ∘ conjPlaneCLM :=
    funext fun z => by rw [h0eq z, Function.comp_apply, conjPlaneCLM_apply]
  have hcd0 : ContDiff ℝ ∞ (κ.lamP 0) := by
    rw [hfe]
    exact hF0c.comp conjPlaneCLM.contDiff
  have h1eq : κ.lamP 1 = fun z => conj (κ.lamP 0 z) := by
    rw [hlamP 1, hlamP 0, seedDualExplicit_one_eq_conj]
  have hcd1 : ContDiff ℝ ∞ (κ.lamP 1) := by
    rw [h1eq]
    exact Complex.conjCLE.contDiff.comp hcd0
  refine ⟨fun j => by fin_cases j; exacts [hcd0, hcd1], fun n => ?_⟩
  obtain ⟨C, hC0, hC⟩ := angularTwo_jet_decay hβc hdec n
  have key : ∀ z, ‖iteratedFDeriv ℝ n (κ.lamP 0) z‖ * (1 + ‖z‖) ^ (n + 2) ≤ 2 ^ n * C := by
    intro z
    have hcomp : ‖iteratedFDeriv ℝ n (κ.lamP 0) z‖ ≤
        ‖iteratedFDeriv ℝ n F₀ (conjPlaneCLM z)‖ * 2 ^ n := by
      rw [hfe, ContinuousLinearMap.iteratedFDeriv_comp_right conjPlaneCLM hF0c z (le_top_nat n)]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      gcongr
      exact norm_conjPlaneCLM_le
    have hw : ‖z‖ ≤ ‖conjPlaneCLM z‖ := by
      rw [conjPlaneCLM_apply, Complex.norm_conj, Prod.norm_def]
      exact max_le (by rw [Real.norm_eq_abs]; exact abs_fst_le_norm_planeToC z)
        (by rw [Real.norm_eq_abs]; exact abs_snd_le_norm_planeToC z)
    calc ‖iteratedFDeriv ℝ n (κ.lamP 0) z‖ * (1 + ‖z‖) ^ (n + 2)
        ≤ ‖iteratedFDeriv ℝ n F₀ (conjPlaneCLM z)‖ * 2 ^ n * (1 + ‖conjPlaneCLM z‖) ^ (n + 2) := by
          gcongr
      _ = 2 ^ n * (‖iteratedFDeriv ℝ n F₀ (conjPlaneCLM z)‖ *
            (1 + ‖conjPlaneCLM z‖) ^ (n + 2)) := by ring
      _ ≤ 2 ^ n * C := by gcongr; exact hC _
  refine ⟨2 ^ n * C, by positivity, fun j z => ?_⟩
  fin_cases j
  · exact key z
  · show ‖iteratedFDeriv ℝ n (κ.lamP 1) z‖ * _ ≤ _
    rw [h1eq]
    exact (mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_conj_le hcd0 z n)
      (by positivity)).trans (key z)

end UnforcedLeray.Short.IIIa.LamJetInf
