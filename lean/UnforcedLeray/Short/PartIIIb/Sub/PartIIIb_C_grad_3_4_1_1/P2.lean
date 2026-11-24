import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.P2.Ext
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.L1

/-!
# `PartIII-b:C/grad/3/4/1/2/2` (leaf B, `ψ^p`): termwise differentiation of the lattice sum

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.

Route: `psiExprs`/`gradPsiTermEnvExt` (`P2/Ext.lean`) give the termwise envelopes of the seven
operators on `νs ≤ 23/20`, hence on a neighbourhood of every `s` with `νs < 23/20`
(`psiLoc`).  The first-order sum (`id, ∂_q, ∂_η, 𝒦`) is `tsumOps_of` for the terms
(`psiR1`, valid on the open range); the second-order sum (`∂_q𝒦, ∂_η𝒦, 𝒦²`) is `tsumOps_of` for
the family `𝒦 term_j` with `U = 𝒦 ψ^p_A`, using `psiR1` on a neighbourhood of `s`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma nfbP2 (F : ℝ × ℝ → ℝ) (y : ℝ × ℝ) :
    ‖fderiv ℝ F y‖ ≤ |fderiv ℝ F y (ei 0)| + |fderiv ℝ F y (ei 1)| := by
  set L := fderiv ℝ F y with hLdef
  apply ContinuousLinearMap.opNorm_le_bound L (by positivity)
  intro v
  have hv : L v = v.1 * L (ei 0) + v.2 * L (ei 1) := by
    have h2 : L v = L (v.1 • ei 0 + v.2 • ei 1) := by
      congr 1
      ext <;> simp [ei]
    rw [h2, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have h1 : |v.1| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]; exact norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]; exact norm_snd_le v
  rw [hv, Real.norm_eq_abs]
  calc |v.1 * L (ei 0) + v.2 * L (ei 1)|
      ≤ |v.1 * L (ei 0)| + |v.2 * L (ei 1)| := abs_add_le _ _
    _ = |v.1| * |L (ei 0)| + |v.2| * |L (ei 1)| := by rw [abs_mul, abs_mul]
    _ ≤ ‖v‖ * |L (ei 0)| + ‖v‖ * |L (ei 1)| :=
        add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
    _ = (|L (ei 0)| + |L (ei 1)|) * ‖v‖ := by ring

/-- x-local majorant data from termwise `∂_q, ∂_η` envelopes at the fixed age `s`. -/
theorem xdata_of {f : ℤ → ℝ → ℝ × ℝ → ℝ} {ν : ℝ} (hν : 0 < ν) {s : ℝ} {x : ℝ × ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hd : ∀ j y, DifferentiableAt ℝ (f j s) y)
    (hq : ∀ j y, |dQ (f j) s y| ≤ B * gradW ν y j)
    (he : ∀ j y, |dEta (f j) s y| ≤ B * gradW ν y j)
    (hsum : Summable (fun j => f j s x)) : TsumXData f s x := by
  obtain ⟨M, g1, hM, hg1, hball⟩ := gradW_ball_majorant ν hν x
  refine ⟨1, one_pos, fun j => 2 * B * M * g1 j, hg1.mul_left (2 * B * M), hsum, ?_⟩
  intro j y hy
  have hyd : dist y x ≤ 1 := (mem_ball.mp hy).le
  refine ⟨hd j y, ?_⟩
  calc ‖fderiv ℝ (f j s) y‖
      ≤ |fderiv ℝ (f j s) y (ei 0)| + |fderiv ℝ (f j s) y (ei 1)| := nfbP2 _ y
    _ ≤ B * gradW ν y j + B * gradW ν y j := add_le_add (hq j y) (he j y)
    _ ≤ B * (M * g1 j) + B * (M * g1 j) :=
        add_le_add (mul_le_mul_of_nonneg_left (hball y hyd j) hB)
          (mul_le_mul_of_nonneg_left (hball y hyd j) hB)
    _ = 2 * B * M * g1 j := by ring

/-- s-local majorant data from termwise `𝒦, ∂_η` envelopes near `s`
(`2 t ∂_t f = 𝒦 f - η ∂_η f`). -/
theorem sdata_of {f : ℤ → ℝ → ℝ × ℝ → ℝ} {ν : ℝ} {s : ℝ} (hs : 0 < s) {x : ℝ × ℝ} {r B : ℝ}
    (hr : 0 < r) (hrs : r ≤ s / 2)
    (hd : ∀ j, ∀ t ∈ ball s r, DifferentiableAt ℝ (fun t' => f j t' x) t)
    (hK : ∀ j, ∀ t ∈ ball s r, |Kop (f j) t x| ≤ B * gradW ν x j)
    (he : ∀ j, ∀ t ∈ ball s r, |dEta (f j) t x| ≤ B * gradW ν x j)
    (hW : Summable (gradW ν x)) : TsumSData f s x := by
  refine ⟨r, hr, fun j => B * (1 + |x.2|) * gradW ν x j / s,
    (hW.mul_left (B * (1 + |x.2|))).div_const s, ?_⟩
  intro j t ht
  refine ⟨hd j t ht, ?_⟩
  have ht' := mem_ball.mp ht
  rw [Real.dist_eq, abs_sub_lt_iff] at ht'
  have hts : s / 2 ≤ t := by linarith [ht'.2]
  have htpos : 0 < t := by linarith
  have key : Kop (f j) t x = x.2 * fderiv ℝ (f j t) x (ei 1)
      + 2 * t * deriv (fun s' => f j s' x) t := rfl
  have h2 : 2 * t * deriv (fun s' => f j s' x) t
      = Kop (f j) t x - x.2 * dEta (f j) t x := by
    rw [key]; unfold dEta; ring
  have hb : |2 * t * deriv (fun s' => f j s' x) t| ≤ B * (1 + |x.2|) * gradW ν x j := by
    rw [h2]
    have h3 := hK j t ht
    have h4 := he j t ht
    calc |Kop (f j) t x - x.2 * dEta (f j) t x|
        ≤ |Kop (f j) t x| + |x.2 * dEta (f j) t x| := abs_sub _ _
      _ = |Kop (f j) t x| + |x.2| * |dEta (f j) t x| := by rw [abs_mul]
      _ ≤ B * gradW ν x j + |x.2| * (B * gradW ν x j) :=
          add_le_add h3 (mul_le_mul_of_nonneg_left h4 (abs_nonneg _))
      _ = B * (1 + |x.2|) * gradW ν x j := by ring
  rw [Real.norm_eq_abs]
  rw [le_div_iff₀ hs]
  have : |2 * t * deriv (fun s' => f j s' x) t| =
      2 * t * |deriv (fun s' => f j s' x) t| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * t)]
  rw [this] at hb
  nlinarith [abs_nonneg (deriv (fun s' => f j s' x) t)]

theorem frob_contP2 : Continuous frob := by unfold frob; fun_prop

theorem gradF_cont {H : ℝ → Mat3} {t : ℝ} (hH : ContDiffAt ℝ 2 H t) :
    ContinuousAt (fun s => frob (H s) + frob (sDeriv H s) + frob (sDeriv (sDeriv H) s)) t := by
  have h0 : ContinuousAt H t := hH.continuousAt
  have hC1 : ContDiffAt ℝ 1 (deriv H) t := hH.derivWithin (by norm_num)
  have hS1 : ContDiffAt ℝ 1 (sDeriv H) t := by
    have : sDeriv H = fun s => s • deriv H s := rfl
    rw [this]; exact contDiffAt_id.smul hC1
  have hD1 : ContDiffAt ℝ 0 (deriv (sDeriv H)) t := hS1.derivWithin (by norm_num)
  have hS1c : ContinuousAt (sDeriv H) t := hS1.continuousAt
  have hS2c : ContinuousAt (sDeriv (sDeriv H)) t := by
    have : sDeriv (sDeriv H) = fun s => s • deriv (sDeriv H) s := rfl
    rw [this]; exact continuousAt_id.smul hD1.continuousAt
  exact ((frob_contP2.continuousAt.comp h0).add (frob_contP2.continuousAt.comp hS1c)).add
    (frob_contP2.continuousAt.comp hS2c)

lemma gSum_diff (e : Fin 3 → Fin 2 → Fin 2 → GExpr)
    (hL : ∀ r : Fin 3, 1 < r.val → ∀ a b, e r a b = []) (ν : ℝ) (j : ℤ) (Ay : ℝ → Mat3)
    (σ : ℝ) (y : ℝ × ℝ) (hν : 0 < ν) (hσ : 0 < σ) (hA : ContDiffAt ℝ 2 Ay σ) :
    DifferentiableAt ℝ (GSum e ν j Ay σ) y ∧
      DifferentiableAt ℝ (fun t => GSum e ν j Ay t y) σ := by
  have h1 : GSum e ν j Ay σ = fun z => ∑ p : Fin 3 × Fin 2 × Fin 2, gkT e ν j Ay p σ z :=
    funext fun z => gSum_eq_gkT e ν j Ay σ z
  have h2 : (fun t => GSum e ν j Ay t y)
      = fun t => ∑ p : Fin 3 × Fin 2 × Fin 2, gkT e ν j Ay p t y :=
    funext fun t => gSum_eq_gkT e ν j Ay t y
  rw [h1, h2]
  exact ⟨DifferentiableAt.fun_sum (fun p _ => (gkT_ok e ν j Ay σ y hν hσ hA hL p).1),
    DifferentiableAt.fun_sum (fun p _ => (gkT_ok e ν j Ay σ y hν hσ hA hL p).2)⟩

lemma gcombo_diff {e : Fin 3 → Fin 2 → Fin 2 → GExpr}
    (hL : ∀ r : Fin 3, 1 < r.val → ∀ a b, e r a b = []) {ν : ℝ} {j : ℤ} {Ay : ℝ → Mat3}
    {σ : ℝ} {F : ℝ → ℝ × ℝ → ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hA : ContDiffAt ℝ 2 Ay σ)
    (hF : GCombo e ν j Ay σ F) (y : ℝ × ℝ) :
    DifferentiableAt ℝ (F σ) y ∧ DifferentiableAt ℝ (fun t => F t y) σ := by
  obtain ⟨h1, h2⟩ := gSum_diff e hL ν j Ay σ y hν hσ hA
  have hFs : F σ = GSum e ν j Ay σ := funext fun z => gCombo_self hF z
  refine ⟨by rw [hFs]; exact h1, h2.congr_of_eventuallyEq (hF.mono fun t ht => ht y)⟩

/-- Local envelope near an age `t` with `νt < 23/20`. -/
theorem psiLoc {ν : ℝ} {χf : ℝ → ℝ} {A : ℝ → Mat3} (hν : 0 < ν) (hν1 : ν ≤ 1) {t : ℝ}
    (ht : 0 < t) (hνt : ν * t < 23 / 20) (hA : ContDiffAt ℝ 2 (Ay ν χf A) t) :
    ∃ r B : ℝ, 0 < r ∧ r ≤ t / 2 ∧ 0 ≤ B ∧ ∀ t' ∈ ball t r, 0 < t' ∧ ν * t' < 23 / 20 ∧
      ContDiffAt ℝ 2 (Ay ν χf A) t' ∧ ∀ (x : ℝ × ℝ) (m : Fin 7) (j : ℤ),
        |gradPsiOps m (gradPsiTm ν χf A j) t' x| ≤ B * gradW ν x j := by
  obtain ⟨C, hC0, hC⟩ := gradPsiTermEnvExt
  have hcF : ContinuousAt (gradF ν χf A) t := gradF_cont hA
  have hev : ∀ᶠ t' in 𝓝 t, gradF ν χf A t' < gradF ν χf A t + 1 :=
    hcF.eventually_lt continuousAt_const (lt_add_one _)
  have hC2 : ∀ᶠ t' in 𝓝 t, ContDiffAt ℝ 2 (Ay ν χf A) t' := hA.eventually (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and hC2)
  have hgap : 0 < (23 / 20 - ν * t) / (2 * ν) := by
    apply div_pos (by linarith) (by positivity)
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = min ε (min (t / 2) ((23 / 20 - ν * t) / (2 * ν))) :=
    ⟨_, rfl⟩
  have hr : 0 < r := by
    rw [hr_def]; exact lt_min hε (lt_min (by linarith) hgap)
  have hrε : r ≤ ε := by rw [hr_def]; exact min_le_left _ _
  have hrt : r ≤ t / 2 := by rw [hr_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hrg : r ≤ (23 / 20 - ν * t) / (2 * ν) := by
    rw [hr_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hF0 := gradF_nonneg ν χf A t
  refine ⟨r, C * (gradF ν χf A t + 1), hr, hrt, mul_nonneg hC0 (by linarith), ?_⟩
  intro t' ht'
  have hd' := mem_ball.mp ht'
  have hdε : dist t' t < ε := lt_of_lt_of_le hd' hrε
  obtain ⟨hF1, hAt'⟩ := hball hdε
  rw [Real.dist_eq, abs_sub_lt_iff] at hd'
  have htpos : 0 < t' := by linarith [hd'.2]
  have hνr : ν * r ≤ (23 / 20 - ν * t) / 2 := by
    have := mul_le_mul_of_nonneg_left hrg hν.le
    have e : ν * ((23 / 20 - ν * t) / (2 * ν)) = (23 / 20 - ν * t) / 2 := by
      field_simp
    linarith
  have hνt' : ν * t' < 23 / 20 := by
    have : ν * (t' - t) ≤ ν * r := mul_le_mul_of_nonneg_left (by linarith [hd'.1]) hν.le
    nlinarith
  refine ⟨htpos, hνt', hAt', ?_⟩
  intro x m j
  refine (hC ν t' χf A hν hν1 htpos hνt'.le hAt' x m j).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF1.le hC0) (gradW_nonneg _ _ _)

/-- First-order termwise sums, on the open range `νt < 23/20`. -/
theorem psiR1 {ν : ℝ} {χf : ℝ → ℝ} {A : ℝ → Mat3} (hν : 0 < ν) (hν1 : ν ≤ 1) {t : ℝ}
    (ht : 0 < t) (hνt : ν * t < 23 / 20) (hA : ContDiffAt ℝ 2 (Ay ν χf A) t) (y : ℝ × ℝ) :
    HasSum (fun j => gradPsiTm ν χf A j t y) (psipA ν χf A t y) ∧
    HasSum (fun j => dQ (gradPsiTm ν χf A j) t y) (dQ (psipA ν χf A) t y) ∧
    HasSum (fun j => dEta (gradPsiTm ν χf A j) t y) (dEta (psipA ν χf A) t y) ∧
    HasSum (fun j => Kop (gradPsiTm ν χf A j) t y) (Kop (psipA ν χf A) t y) := by
  obtain ⟨r, B, hr, hrt, hB, hloc⟩ := psiLoc (χf := χf) (A := A) hν hν1 ht hνt hA
  obtain ⟨e0, e0q, e0e, e1, e1q, e1e, e2, hl0, hl1, hS⟩ := psiExprs
  have hL0 : ∀ r : Fin 3, 1 < r.val → ∀ a b, e0 r a b = [] :=
    fun r hr a b => hl0 r (lt_trans Nat.zero_lt_one hr) a b
  have hW := gradW_summable gradLatticeSummable ν hν y
  have env : ∀ t' ∈ ball t r, ∀ (x : ℝ × ℝ) (m : Fin 7) (j : ℤ),
      |gradPsiOps m (gradPsiTm ν χf A j) t' x| ≤ B * gradW ν x j :=
    fun t' ht' => (hloc t' ht').2.2.2
  have env0 := env t (mem_ball_self hr)
  refine tsumOps_of (f := gradPsiTm ν χf A) (U := psipA ν χf A) (s := t) (x := y)
    (Filter.Eventually.of_forall fun y' => psipA_eq ν χf A t y')
    (Filter.Eventually.of_forall fun t' => psipA_eq ν χf A t' y) ?_ ?_
  · refine xdata_of hν hB ?_ ?_ ?_ ?_
    · intro j y'
      exact (gcombo_diff hL0 hν ht hA (hS ν χf A j t hν ht hA).1 y').1
    · intro j y'; exact env0 y' 1 j
    · intro j y'; exact env0 y' 2 j
    · refine Summable.of_norm_bounded (hW.mul_left B) (fun j => ?_)
      rw [Real.norm_eq_abs]; exact env0 y 0 j
  · refine sdata_of (ν := ν) (B := B) ht hr hrt ?_ ?_ ?_ hW
    · intro j t' ht'
      obtain ⟨hp, -, hAt', -⟩ := hloc t' ht'
      exact (gcombo_diff hL0 hν hp hAt' (hS ν χf A j t' hν hp hAt').1 y).2
    · intro j t' ht'; exact env t' ht' y 3 j
    · intro j t' ht'; exact env t' ht' y 2 j

theorem gradPsiTsum : GradPsiTsum := by
  intro ν s χf A hd x m
  obtain ⟨hν, hν1, hs, hsb, hC2⟩ := hd
  have hνs : ν * s ≤ 11 / 10 := by
    rw [le_div_iff₀ hν] at hsb; linarith
  have hνs' : ν * s < 23 / 20 := by linarith
  obtain ⟨r, B, hr, hrs, hB, hloc⟩ := psiLoc (χf := χf) (A := A) hν hν1 hs hνs' hC2
  obtain ⟨e0, e0q, e0e, e1, e1q, e1e, e2, hl0, hl1, hS⟩ := psiExprs
  have hL1 : ∀ r : Fin 3, 1 < r.val → ∀ a b, e1 r a b = [] := hl1
  have hW := gradW_summable gradLatticeSummable ν hν x
  have env : ∀ t' ∈ ball s r, ∀ (x : ℝ × ℝ) (m : Fin 7) (j : ℤ),
      |gradPsiOps m (gradPsiTm ν χf A j) t' x| ≤ B * gradW ν x j :=
    fun t' ht' => (hloc t' ht').2.2.2
  have env0 := env s (mem_ball_self hr)
  have R1 := psiR1 (χf := χf) (A := A) hν hν1 hs hνs' hC2
  have key := tsumOps_of
    (f := fun j => fun s' y => Kop (gradPsiTm ν χf A j) s' y)
    (U := fun s' y => Kop (psipA ν χf A) s' y) (s := s) (x := x)
    (Filter.Eventually.of_forall fun y' => (R1 y').2.2.2.tsum_eq.symm)
    (by
      filter_upwards [ball_mem_nhds s hr] with t' ht'
      obtain ⟨hp, hlt, hAt', -⟩ := hloc t' ht'
      exact (psiR1 (χf := χf) (A := A) hν hν1 hp hlt hAt' x).2.2.2.tsum_eq.symm)
    (xdata_of hν hB
      (fun j y' => (gcombo_diff hL1 hν hs hC2 (hS ν χf A j s hν hs hC2).2.2.2.1 y').1)
      (fun j y' => env0 y' 4 j) (fun j y' => env0 y' 5 j)
      (Summable.of_norm_bounded (hW.mul_left B) (fun j => by
        rw [Real.norm_eq_abs]; exact env0 x 3 j)))
    (sdata_of (ν := ν) (B := B) hs hr hrs
      (fun j t' ht' => by
        obtain ⟨hp, -, hAt', -⟩ := hloc t' ht'
        exact (gcombo_diff hL1 hν hp hAt' (hS ν χf A j t' hν hp hAt').2.2.2.1 x).2)
      (fun j t' ht' => env t' ht' x 6 j) (fun j t' ht' => env t' ht' x 5 j) hW)
  fin_cases m
  · exact (R1 x).1
  · exact (R1 x).2.1
  · exact (R1 x).2.2.1
  · exact (R1 x).2.2.2
  · exact key.2.1
  · exact key.2.2.1
  · exact key.2.2.2

end UnforcedLeray.Short.PartIIIb.Concrete
