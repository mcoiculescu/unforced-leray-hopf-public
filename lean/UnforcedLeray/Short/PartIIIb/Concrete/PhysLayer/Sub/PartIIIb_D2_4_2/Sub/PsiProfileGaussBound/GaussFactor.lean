import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PsiProfileGaussBound.GaussFactor.ExpBound

/-!
# Leaf G of `PsiProfileGaussBound` (task `PartIII-b:IIIb-D2/4/2/1/3/1`)

Source of record: `the November 2 reference manuscript` lines 4963-4991.
`psiGauss ν = exp ∘ q`, `q(s,y) = -|y|²/(4a(s))`, `a = 1+νs`.  `q` lies in the polynomial-growth
class `PB` (`ChartBounds.lean`), so `exp_comp_bound` (`ExpBound.lean`) gives
`‖D^k G‖ ≤ e^{q} · C (1+‖y‖)^{2N}`, and `a ≤ K = 1+2νs₀` on `[s₀/2, 2s₀]` gives
`e^{q} ≤ e^{-|y|²/(4K)}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiGaussFactor_proof : PsiGaussFactor := by
  intro ν hν s0 hs0
  have hpos : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))), 0 < ageA ν p.1 := by
    intro p hp
    have h : (0 : ℝ) < p.1 := hp.1
    unfold ageA
    positivity
  have ha : ContDiffOn ℝ 2 (fun p : Chart => ageA ν p.1) (Ioi (0 : ℝ) ×ˢ univ) := by
    unfold ageA
    exact (contDiff_const.add (contDiff_const.mul contDiff_fst)).contDiffOn
  have hden : ContDiffOn ℝ 2 (fun p : Chart => 4 * ageA ν p.1) (Ioi (0 : ℝ) ×ˢ univ) :=
    contDiffOn_const.mul ha
  have hden0 : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))), 4 * ageA ν p.1 ≠ 0 :=
    fun p hp => by have := hpos p hp; positivity
  have hq1 : ContDiffOn ℝ 2 (fun p : Chart => -(sq2 p.2)) (Ioi (0 : ℝ) ×ˢ univ) := by
    unfold sq2
    fun_prop
  have hq : ContDiffOn ℝ 2 (fun p : Chart => -(sq2 p.2) / (4 * ageA ν p.1))
      (Ioi (0 : ℝ) ×ˢ univ) := hq1.div hden hden0
  refine ⟨hq.exp, ?_⟩
  -- the exponent lies in the polynomial-growth class
  have hb : ContDiffOn ℝ 2 (fun s : ℝ => (4 * ageA ν s)⁻¹) (Ioi 0) := by
    have h4 : ContDiffOn ℝ 2 (fun s : ℝ => 4 * ageA ν s) (Ioi 0) := by
      unfold ageA
      exact (contDiff_const.mul (contDiff_const.add (contDiff_const.mul contDiff_id))).contDiffOn
    refine h4.inv (fun s hs => ?_)
    have h : (0 : ℝ) < s := hs
    unfold ageA
    positivity
  have hPB : PB s0 (fun p : Chart => -(sq2 p.2) / (4 * ageA ν p.1)) := by
    have h1 := (PB.y1.mul hs0 PB.y1).add hs0 (PB.y2.mul hs0 PB.y2)
    have h2 := ((PB.const (s0 := s0) (-1)).mul hs0 h1).mul hs0 (PB.sfun hs0 hb)
    exact h2.congr (fun p => by simp only [sq2, div_eq_mul_inv]; ring)
  obtain ⟨_, N, C, hC⟩ := hPB
  refine ⟨2 * N, (1 + 2 * |C|) ^ 2, fun p hp k hk => ?_⟩
  have hpU := strip_mem hs0 hp
  have e : ‖iteratedFDeriv ℝ k (psiGauss ν) p‖ ≤
      Real.exp (-(sq2 p.2) / (4 * ageA ν p.1)) *
        (1 + ‖iteratedFDeriv ℝ 1 (fun p : Chart => -(sq2 p.2) / (4 * ageA ν p.1)) p‖ +
          ‖iteratedFDeriv ℝ 2 (fun p : Chart => -(sq2 p.2) / (4 * ageA ν p.1)) p‖) ^ 2 :=
    exp_comp_bound strip_open hq hpU k hk
  have hr : (1 : ℝ) ≤ (1 + ‖p.2‖) ^ N := one_le_pow₀ (by linarith [norm_nonneg p.2])
  have hR : (0 : ℝ) ≤ (1 + ‖p.2‖) ^ N := by linarith
  have c1 := hC p hp 1 (by norm_num)
  have c2 := hC p hp 2 (by norm_num)
  have hCa : C * (1 + ‖p.2‖) ^ N ≤ |C| * (1 + ‖p.2‖) ^ N :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hR
  have hsum : 1 + ‖iteratedFDeriv ℝ 1 (fun p : Chart => -(sq2 p.2) / (4 * ageA ν p.1)) p‖ +
      ‖iteratedFDeriv ℝ 2 (fun p : Chart => -(sq2 p.2) / (4 * ageA ν p.1)) p‖ ≤
      (1 + 2 * |C|) * (1 + ‖p.2‖) ^ N := by nlinarith [abs_nonneg C]
  have hsq : (1 + ‖iteratedFDeriv ℝ 1 (fun p : Chart => -(sq2 p.2) / (4 * ageA ν p.1)) p‖ +
      ‖iteratedFDeriv ℝ 2 (fun p : Chart => -(sq2 p.2) / (4 * ageA ν p.1)) p‖) ^ 2 ≤
      (1 + 2 * |C|) ^ 2 * (1 + ‖p.2‖) ^ (2 * N) := by
    have h0 : (0 : ℝ) ≤ 1 + ‖iteratedFDeriv ℝ 1 (fun p : Chart => -(sq2 p.2) / (4 * ageA ν p.1)) p‖ +
      ‖iteratedFDeriv ℝ 2 (fun p : Chart => -(sq2 p.2) / (4 * ageA ν p.1)) p‖ := by positivity
    calc _ ≤ ((1 + 2 * |C|) * (1 + ‖p.2‖) ^ N) ^ 2 := pow_le_pow_left₀ h0 hsum 2
      _ = _ := by rw [mul_pow, ← pow_mul, mul_comm N 2]
  -- `a ≤ K` on the range gives the Gaussian comparison
  have hs : 0 < p.1 := lt_of_lt_of_le (by positivity) hp.1
  have haK : ageA ν p.1 ≤ 1 + 2 * ν * s0 := by
    unfold ageA
    nlinarith [hp.2]
  have ha0 : 0 < ageA ν p.1 := hpos p hpU
  have hK0 : 0 < 1 + 2 * ν * s0 := by positivity
  have hexp : Real.exp (-(sq2 p.2) / (4 * ageA ν p.1)) ≤
      Real.exp (-(sq2 p.2) / (4 * (1 + 2 * ν * s0))) := by
    apply Real.exp_le_exp.2
    have hs2 : 0 ≤ sq2 p.2 := by unfold sq2; positivity
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hs2 (by positivity) (by linarith)
  have hE0 : 0 ≤ Real.exp (-(sq2 p.2) / (4 * ageA ν p.1)) := (Real.exp_pos _).le
  calc _ ≤ _ := e
    _ ≤ Real.exp (-(sq2 p.2) / (4 * ageA ν p.1)) *
          ((1 + 2 * |C|) ^ 2 * (1 + ‖p.2‖) ^ (2 * N)) := mul_le_mul_of_nonneg_left hsq hE0
    _ ≤ Real.exp (-(sq2 p.2) / (4 * (1 + 2 * ν * s0))) *
          ((1 + 2 * |C|) ^ 2 * (1 + ‖p.2‖) ^ (2 * N)) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
