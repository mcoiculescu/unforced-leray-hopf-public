import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.PsiSubst
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.ParamInt7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.PsiFSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.PsiFMeas
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.PsiFDom

/-!
# Proof of `SCPsiBound` (source 4178-4186, 4917-4937)

`Ψ_Z(y) = -(y₀²+y₁²) ∫_{(1,∞)} t Z_z(t y₀, t y₁, y₂) dt` (`scPsiSubst`).  The `m`-th derivative
is bounded by Leibniz: the polynomial factor has `‖D^i q‖ r^i ≤ 4 r²` (zero for `i ≥ 3`), and the
integral has `‖D^j I‖ ≤ B (r^{4+j})⁻¹` by differentiation under the integral (norm form, proved
here by induction on the order) and the pointwise `t^{-3}` jet bound.
Source: `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PsiBoundAux

/-- Norm form of differentiation under the integral over `(1,∞)`: the `m`-th derivative of the
integral is bounded by the integral of the `m`-th derivatives (induction on `m`; the first
derivative is exchanged with the integral by dominated differentiation). -/
theorem normExch (m : ℕ) : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set Vec3) (F : ℝ → Vec3 → E) (N : ℕ), IsOpen U → m ≤ N →
    (∀ t : ℝ, 1 < t → ContDiffOn ℝ (N : WithTop ℕ∞) (F t) U) →
    (∀ k : ℕ, k ≤ N → ∀ x ∈ U,
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ k (F t) x) (volume.restrict (Ioi (1 : ℝ)))) →
    (∀ x₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ bd : ℝ → ℝ, IntegrableOn bd (Ioi (1 : ℝ)) ∧
      ∀ k : ℕ, k ≤ N → ∀ t : ℝ, 1 < t → ∀ x ∈ U ∩ ball x₀ ε,
        ‖iteratedFDeriv ℝ k (F t) x‖ ≤ bd t) →
    ∀ x ∈ U, ‖iteratedFDeriv ℝ m (fun y => ∫ t in Ioi (1 : ℝ), F t y) x‖
      ≤ ∫ t in Ioi (1 : ℝ), ‖iteratedFDeriv ℝ m (F t) x‖ := by
  induction m with
  | zero =>
    intro E _ _ U F N _ _ _ _ _ x _
    simp only [norm_iteratedFDeriv_zero]
    exact norm_integral_le_integral_norm _
  | succ m ih =>
    intro E _ _ U F N hU hmN hF hM hD x hx
    have hN1 : (N : WithTop ℕ∞) ≠ 0 := by
      exact_mod_cast (show N ≠ 0 by omega)
    have hdiff : ∀ y ∈ U, HasFDerivAt (fun y => ∫ t in Ioi (1 : ℝ), F t y)
        (∫ t in Ioi (1 : ℝ), fderiv ℝ (F t) y) y := by
      intro x₁ hx₁
      obtain ⟨ε, hε, bd, hbd, hb⟩ := hD x₁ hx₁
      have hs : U ∩ ball x₁ ε ∈ 𝓝 x₁ := (hU.inter isOpen_ball).mem_nhds ⟨hx₁, mem_ball_self hε⟩
      have hbdae : ∀ y ∈ U ∩ ball x₁ ε, ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))), ‖F t y‖ ≤ bd t :=
        fun y hy => ParamInt7Aux.ae_Ioi_one_of fun t ht => by
          simpa using hb 0 (Nat.zero_le _) t ht y hy
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le
        (μ := volume.restrict (Ioi (1 : ℝ))) (F := fun y t => F t y)
        (F' := fun y t => fderiv ℝ (F t) y) (x₀ := x₁) (bound := bd) (s := U ∩ ball x₁ ε)
        hs ?_ ?_ ?_ ?_ hbd ?_
      · filter_upwards [hs] with y hy
        exact ParamInt7Aux.aesm_zero F y (hM 0 (Nat.zero_le _) y hy.1)
      · exact hbd.mono' (ParamInt7Aux.aesm_zero F x₁ (hM 0 (Nat.zero_le _) x₁ hx₁))
          (hbdae x₁ ⟨hx₁, mem_ball_self hε⟩)
      · exact ParamInt7Aux.aesm_zero (fun t y => fderiv ℝ (F t) y) x₁
          (ParamInt7Aux.aesm_jet_fderiv 0 F x₁ (hM 1 (by omega) x₁ hx₁))
      · exact ParamInt7Aux.ae_Ioi_one_of fun t ht y hy => by
          simpa using hb 1 (by omega) t ht y hy
      · exact ParamInt7Aux.ae_Ioi_one_of fun t ht y hy =>
          (((hF t ht).differentiableOn hN1).differentiableAt
            (hU.mem_nhds hy.1)).hasFDerivAt
    have hcongr : ∀ y ∈ U, fderiv ℝ (fun z => ∫ t in Ioi (1 : ℝ), F t z) y =
        ∫ t in Ioi (1 : ℝ), fderiv ℝ (F t) y := fun y hy => (hdiff y hy).fderiv
    have hEv : (fun y => fderiv ℝ (fun z => ∫ t in Ioi (1 : ℝ), F t z) y) =ᶠ[𝓝 x]
        (fun y => ∫ t in Ioi (1 : ℝ), fderiv ℝ (F t) y) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) hcongr
    have hF' : ∀ t : ℝ, 1 < t → ContDiffOn ℝ (m : WithTop ℕ∞) (fun y => fderiv ℝ (F t) y) U :=
      fun t ht => (hF t ht).fderiv_of_isOpen hU (by exact_mod_cast hmN)
    have hM' : ∀ k : ℕ, k ≤ m → ∀ x ∈ U,
        AEStronglyMeasurable (fun t => iteratedFDeriv ℝ k (fun y => fderiv ℝ (F t) y) x)
          (volume.restrict (Ioi (1 : ℝ))) :=
      fun k hk x' hx' => ParamInt7Aux.aesm_jet_fderiv k F x' (hM (k + 1) (by omega) x' hx')
    have hD' : ∀ x₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ bd : ℝ → ℝ, IntegrableOn bd (Ioi (1 : ℝ)) ∧
        ∀ k : ℕ, k ≤ m → ∀ t : ℝ, 1 < t → ∀ x ∈ U ∩ ball x₀ ε,
          ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ (F t) y) x‖ ≤ bd t := by
      intro x₀ hx₀
      obtain ⟨ε, hε, bd, hbd, hb⟩ := hD x₀ hx₀
      refine ⟨ε, hε, bd, hbd, fun k hk t ht x' hx' => ?_⟩
      have e := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F t) (x := x') (n := k)
      exact e.trans_le (hb (k + 1) (by omega) t ht x' hx')
    have hG : ‖iteratedFDeriv ℝ m (fun y => ∫ t in Ioi (1 : ℝ), fderiv ℝ (F t) y) x‖
        ≤ ∫ t in Ioi (1 : ℝ), ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ (F t) y) x‖ :=
      ih (E := Vec3 →L[ℝ] E) U (fun t y => fderiv ℝ (F t) y) m hU le_rfl hF' hM' hD' x hx
    have key1 : ‖iteratedFDeriv ℝ (m + 1) (fun z => ∫ t in Ioi (1 : ℝ), F t z) x‖
        = ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ (fun z => ∫ t in Ioi (1 : ℝ), F t z) y) x‖ :=
      (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun z => ∫ t in Ioi (1 : ℝ), F t z)
        (x := x) (n := m)).symm
    have key2 : iteratedFDeriv ℝ m (fun y => fderiv ℝ (fun z => ∫ t in Ioi (1 : ℝ), F t z) y) x
        = iteratedFDeriv ℝ m (fun y => ∫ t in Ioi (1 : ℝ), fderiv ℝ (F t) y) x :=
      (hEv.iteratedFDeriv (𝕜 := ℝ) m).self_of_nhds
    calc ‖iteratedFDeriv ℝ (m + 1) (fun z => ∫ t in Ioi (1 : ℝ), F t z) x‖
        = ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ (fun z => ∫ t in Ioi (1 : ℝ), F t z) y) x‖ := key1
      _ = ‖iteratedFDeriv ℝ m (fun y => ∫ t in Ioi (1 : ℝ), fderiv ℝ (F t) y) x‖ := by rw [key2]
      _ ≤ ∫ t in Ioi (1 : ℝ), ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ (F t) y) x‖ := hG
      _ = ∫ t in Ioi (1 : ℝ), ‖iteratedFDeriv ℝ (m + 1) (F t) x‖ := by
        congr 1
        funext t
        exact norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F t) (x := x) (n := m)

/-- Pointwise `t^{-3}` jet bound for `psiF` at a point `x ∈ psiU ν` (the leaf `scPsiF_dom` with
`x₀ = x` and the sharp power of `cylR x`). -/
theorem psiF_jet_bound (ν B : ℝ) (Z : Vec3 → Vec3) (hν : 0 < ν) (hB : 0 ≤ B)
    (hZ : SCZHyp ν B Z) (t : ℝ) (ht : 1 < t) (x : Vec3) (hx : x ∈ psiU ν) (k : ℕ) (hk : k ≤ 7) :
    ‖iteratedFDeriv ℝ k (psiF Z t) x‖ ≤ B * (cylR x ^ (4 + k))⁻¹ * t ^ (-3 : ℝ) := by
  obtain ⟨hZ1, hZ2⟩ := hZ
  have hx' : ν * (11 / 12) < eucSq x ∧ 0 < cylR x := hx
  have hr : 0 < cylR x := hx'.2
  have hS : IsOpen {w : Vec3 | ν * (11 / 12) < eucSq w} :=
    isOpen_lt continuous_const (by unfold eucSq; fun_prop)
  have ht1 : (1 : ℝ) ≤ t := ht.le
  have ht0 : (0 : ℝ) < t := by linarith
  have hLx0 : psiFdomL t x 0 = t * x 0 := by rw [psiFdomL_apply]; rfl
  have hLx1 : psiFdomL t x 1 = t * x 1 := by rw [psiFdomL_apply]; rfl
  have hLx2 : psiFdomL t x 2 = x 2 := by rw [psiFdomL_apply]; rfl
  have hsq : eucSq x ≤ eucSq (psiFdomL t x) := by
    rw [psiFdom_eucSq, psiFdom_eucSq, hLx0, hLx1, hLx2]
    nlinarith [mul_nonneg (by nlinarith : (0:ℝ) ≤ t ^ 2 - 1)
      (add_nonneg (sq_nonneg (x 0)) (sq_nonneg (x 1)))]
  have hLmem : ν * (11 / 12) < eucSq (psiFdomL t x) := lt_of_lt_of_le hx'.1 hsq
  have hcx : cylR x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    unfold cylR
    exact Real.sq_sqrt (by positivity)
  have hsq2 : (t * cylR x) ^ 2 ≤ eucSq (psiFdomL t x) := by
    rw [psiFdom_eucSq, hLx0, hLx1, hLx2, mul_pow, hcx]
    nlinarith [sq_nonneg (x 2), sq_nonneg t, sq_nonneg (x 0), sq_nonneg (x 1)]
  have hsqrt : t * cylR x ≤ Real.sqrt (eucSq (psiFdomL t x)) :=
    (Real.le_sqrt (mul_pos ht0 hr).le
      (by rw [psiFdom_eucSq]; positivity)).mpr hsq2
  have hZb := hZ2 k hk (psiFdomL t x) hLmem
  have hpow : (Real.sqrt (eucSq (psiFdomL t x))) ^ (-(4:ℝ) - (k:ℝ))
      ≤ (t * cylR x) ^ (-(4:ℝ) - (k:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos ht0 hr) hsqrt
      (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hZbound : ‖iteratedFDeriv ℝ k Z (psiFdomL t x)‖
      ≤ B * (t * cylR x) ^ (-(4:ℝ) - (k:ℝ)) :=
    hZb.trans (mul_le_mul_of_nonneg_left hpow hB)
  have hZat : ContDiffAt ℝ 7 Z (psiFdomL t x) :=
    hZ1.contDiffAt (hS.mem_nhds hLmem)
  have hQ : ‖iteratedFDeriv ℝ k ((t • (ContinuousLinearMap.proj (2 : Fin 3) :
        Vec3 →L[ℝ] ℝ)) ∘ Z) (psiFdomL t x)‖
      ≤ ‖t • (ContinuousLinearMap.proj (2 : Fin 3) : Vec3 →L[ℝ] ℝ)‖
        * ‖iteratedFDeriv ℝ k Z (psiFdomL t x)‖ :=
    ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ hZat (by exact_mod_cast hk)
  have hQn : ‖t • (ContinuousLinearMap.proj (2 : Fin 3) : Vec3 →L[ℝ] ℝ)‖ ≤ t := by
    rw [norm_smul, Real.norm_of_nonneg ht0.le]
    have := mul_le_mul_of_nonneg_left psiFdom_proj_norm_le ht0.le
    linarith
  have hW : ContDiffOn ℝ 7 ((t • (ContinuousLinearMap.proj (2 : Fin 3) :
        Vec3 →L[ℝ] ℝ)) ∘ Z) {w : Vec3 | ν * (11 / 12) < eucSq w} :=
    (ContinuousLinearMap.contDiff (t • (ContinuousLinearMap.proj (2 : Fin 3) :
        Vec3 →L[ℝ] ℝ))).comp_contDiffOn hZ1
  have hcomp := psiFdom_iteratedFDeriv_comp (i := k) hS hW (psiFdomL t) hLmem
    (by exact_mod_cast hk)
  have hfun : psiF Z t = ((t • (ContinuousLinearMap.proj (2 : Fin 3) :
        Vec3 →L[ℝ] ℝ)) ∘ Z) ∘ psiFdomL t := by
    funext y
    simp [psiF, psiFdomL_apply]
  have hconv : cylR x ^ (-(4:ℝ) - (k:ℝ)) = (cylR x ^ (4 + k))⁻¹ := by
    rw [show (-(4:ℝ) - (k:ℝ)) = -((4 + k : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hr.le, Real.rpow_natCast]
  show ‖iteratedFDeriv ℝ k (psiF Z t) x‖ ≤ B * (cylR x ^ (4 + k))⁻¹ * t ^ (-3 : ℝ)
  rw [hfun]
  calc ‖iteratedFDeriv ℝ k (((t • (ContinuousLinearMap.proj (2 : Fin 3) :
          Vec3 →L[ℝ] ℝ)) ∘ Z) ∘ psiFdomL t) x‖
      ≤ ‖iteratedFDeriv ℝ k ((t • (ContinuousLinearMap.proj (2 : Fin 3) :
          Vec3 →L[ℝ] ℝ)) ∘ Z) (psiFdomL t x)‖ * ‖psiFdomL t‖ ^ k := hcomp
    _ ≤ (‖t • (ContinuousLinearMap.proj (2 : Fin 3) : Vec3 →L[ℝ] ℝ)‖
          * ‖iteratedFDeriv ℝ k Z (psiFdomL t x)‖) * ‖psiFdomL t‖ ^ k :=
        mul_le_mul_of_nonneg_right hQ (by positivity)
    _ ≤ (t * (B * (t * cylR x) ^ (-(4:ℝ) - (k:ℝ)))) * t ^ k :=
        mul_le_mul
          (mul_le_mul hQn hZbound (norm_nonneg _) ht0.le)
          (pow_le_pow_left₀ (norm_nonneg _) (psiFdomL_norm_le ht1) k)
          (by positivity)
          (mul_nonneg ht0.le (mul_nonneg hB (Real.rpow_nonneg (mul_pos ht0 hr).le _)))
    _ = B * cylR x ^ (-(4:ℝ) - (k:ℝ)) * t ^ (-3:ℝ) := psiFdom_key ht0 hr k
    _ = B * (cylR x ^ (4 + k))⁻¹ * t ^ (-3 : ℝ) := by rw [hconv]

/-- The integral `I(y) = ∫_{(1,∞)} psiF Z t y dt` has `‖D^j I y‖ ≤ B (r^{4+j})⁻¹`, `j ≤ 7`. -/
theorem psiI_bound (ν B : ℝ) (Z : Vec3 → Vec3) (hν : 0 < ν) (hB : 0 ≤ B)
    (hZ : SCZHyp ν B Z) (y : Vec3) (hy : y ∈ psiU ν) (j : ℕ) (hj : j ≤ 7) :
    ‖iteratedFDeriv ℝ j (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
      ≤ B * (cylR y ^ (4 + j))⁻¹ := by
  have hFs : ∀ t : ℝ, 1 < t → ContDiffOn ℝ ((7 : ℕ) : WithTop ℕ∞) (psiF Z t) (psiU ν) :=
    fun t ht => by exact_mod_cast scPsiF_smooth ν B Z hν hB hZ t ht
  have hE := normExch j (E := ℝ) (psiU ν) (psiF Z) 7 (psiU_isOpen ν) hj hFs
    (fun k hk x hx => scPsiF_meas ν B Z hν hB hZ k hk x hx)
    (fun x₀ hx₀ => scPsiF_dom ν B Z hν hB hZ x₀ hx₀) y hy
  have hr : 0 < cylR y := (show ν * (11 / 12) < eucSq y ∧ 0 < cylR y from hy).2
  have hp : 0 < cylR y ^ (4 + j) := pow_pos hr _
  have hint : IntegrableOn (fun t : ℝ => B * (cylR y ^ (4 + j))⁻¹ * t ^ (-3 : ℝ))
      (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -3) (c := 1) (by norm_num) one_pos).const_mul _
  have hmono : ∫ t in Ioi (1 : ℝ), ‖iteratedFDeriv ℝ j (psiF Z t) y‖
      ≤ ∫ t in Ioi (1 : ℝ), B * (cylR y ^ (4 + j))⁻¹ * t ^ (-3 : ℝ) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _) hint ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht =>
        psiF_jet_bound ν B Z hν hB hZ t ht y hy j hj)
  have hval : ∫ t in Ioi (1 : ℝ), B * (cylR y ^ (4 + j))⁻¹ * t ^ (-3 : ℝ)
      = B * (cylR y ^ (4 + j))⁻¹ * (1 / 2) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  have hc : 0 ≤ B * (cylR y ^ (4 + j))⁻¹ := mul_nonneg hB (inv_nonneg.mpr hp.le)
  calc ‖iteratedFDeriv ℝ j (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
      ≤ ∫ t in Ioi (1 : ℝ), ‖iteratedFDeriv ℝ j (psiF Z t) y‖ := hE
    _ ≤ _ := hmono
    _ = B * (cylR y ^ (4 + j))⁻¹ * (1 / 2) := hval
    _ ≤ B * (cylR y ^ (4 + j))⁻¹ := by linarith

theorem neg_add_norm_le (f g : Vec3 → ℝ) (i : ℕ) (y : Vec3) (hf : ContDiffAt ℝ i f y)
    (hg : ContDiffAt ℝ i g y) :
    ‖iteratedFDeriv ℝ i (fun z => -(f z + g z)) y‖
      ≤ ‖iteratedFDeriv ℝ i f y‖ + ‖iteratedFDeriv ℝ i g y‖ := by
  have e1 : iteratedFDeriv ℝ i (fun z => -(f z + g z)) y
      = -(iteratedFDeriv ℝ i (fun z => f z + g z) y) := iteratedFDeriv_neg_apply
  have e2 : iteratedFDeriv ℝ i (fun z => f z + g z) y
      = iteratedFDeriv ℝ i f y + iteratedFDeriv ℝ i g y := iteratedFDeriv_add_apply hf hg
  rw [e1, norm_neg, e2]
  exact norm_add_le _ _

theorem clm_iter_ge2 (L : Vec3 →L[ℝ] ℝ) (y : Vec3) (j : ℕ) (hj : 2 ≤ j) :
    ‖iteratedFDeriv ℝ j (⇑L) y‖ = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := ⇑L) (x := y) (n := n + 1)
  have hf : fderiv ℝ (⇑L) = fun _ => L := by
    funext z
    exact L.fderiv
  rw [hf, iteratedFDeriv_succ_const] at h
  simp only [Pi.zero_apply, norm_zero] at h
  exact h.symm

theorem clm_norm_one_eq (L : Vec3 →L[ℝ] ℝ) (y : Vec3) :
    ‖iteratedFDeriv ℝ 1 (⇑L) y‖ = ‖L‖ := by
  rw [norm_iteratedFDeriv_one, L.fderiv]

theorem proj_norm_le_one (c : Fin 3) :
    ‖(ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => ?_)
  rw [one_mul]
  exact norm_le_pi_norm (f := y) c

theorem prod_leibniz (c : Fin 3) (y : Vec3) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z : Vec3 => (ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ) z *
        (ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ) z) y‖
      ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j (⇑(ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ)) y‖ *
          ‖iteratedFDeriv ℝ (i - j) (⇑(ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ)) y‖ :=
  norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := ⊤) (ContinuousLinearMap.contDiff _)
    (ContinuousLinearMap.contDiff _) y (n := i) le_top

theorem prod_norm_bounds (c : Fin 3) (y : Vec3) :
    ‖iteratedFDeriv ℝ 0 (fun z : Vec3 => (ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ) z *
        (ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ) z) y‖ ≤ y c ^ 2 ∧
    ‖iteratedFDeriv ℝ 1 (fun z : Vec3 => (ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ) z *
        (ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ) z) y‖ ≤ 2 * |y c| ∧
    ‖iteratedFDeriv ℝ 2 (fun z : Vec3 => (ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ) z *
        (ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ) z) y‖ ≤ 2 ∧
    ∀ i : ℕ, 3 ≤ i → ‖iteratedFDeriv ℝ i (fun z : Vec3 => (ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ) z *
        (ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ) z) y‖ = 0 := by
  have h0 : ‖iteratedFDeriv ℝ 0 (⇑(ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ)) y‖ = |y c| := by
    rw [norm_iteratedFDeriv_zero]
    simp
  have h1 : ‖iteratedFDeriv ℝ 1 (⇑(ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ)) y‖ ≤ 1 := by
    rw [clm_norm_one_eq]
    exact proj_norm_le_one c
  have hz : ∀ j : ℕ, 2 ≤ j →
      ‖iteratedFDeriv ℝ j (⇑(ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ)) y‖ = 0 :=
    fun j hj => clm_iter_ge2 _ y j hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := prod_leibniz c y 0
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_self, Nat.cast_one,
      Nat.sub_self, Nat.sub_zero, one_mul, zero_add, h0] at this
    have := abs_mul_abs_self (y c)
    nlinarith [this, abs_nonneg (y c), sq_abs (y c)]
  · have := prod_leibniz c y 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
      Nat.choose_self, Nat.cast_one, Nat.sub_self, Nat.sub_zero, zero_add, one_mul] at this
    have hh : |y c| * ‖iteratedFDeriv ℝ 1 (⇑(ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ)) y‖
        ≤ |y c| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    nlinarith [this, hh, h0]
  · have key : (∑ j ∈ Finset.range (2 + 1), ((Nat.choose 2 j : ℕ) : ℝ) *
        ‖iteratedFDeriv ℝ j (⇑(ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ)) y‖ *
        ‖iteratedFDeriv ℝ (2 - j) (⇑(ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ)) y‖)
        = 2 * ‖iteratedFDeriv ℝ 1 (⇑(ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ)) y‖ *
          ‖iteratedFDeriv ℝ 1 (⇑(ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ)) y‖ := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        show (2:ℕ) - 0 = 2 from rfl, show (2:ℕ) - 1 = 1 from rfl, show (2:ℕ) - 2 = 0 from rfl,
        hz 2 le_rfl, h0, show Nat.choose 2 0 = 1 from rfl, show Nat.choose 2 1 = 2 from rfl,
        show Nat.choose 2 2 = 1 from rfl, Nat.cast_one, Nat.cast_ofNat]
      ring
    have hL := prod_leibniz c y 2
    rw [key] at hL
    have hn1 := norm_nonneg (iteratedFDeriv ℝ 1 (⇑(ContinuousLinearMap.proj c : Vec3 →L[ℝ] ℝ)) y)
    have hm := mul_le_mul h1 h1 hn1 zero_le_one
    nlinarith [hL, hm]
  · intro i hi
    apply le_antisymm _ (norm_nonneg _)
    refine (prod_leibniz c y i).trans (le_of_eq (Finset.sum_eq_zero fun j hj => ?_))
    by_cases hj2 : 2 ≤ j
    · rw [hz j hj2]; simp
    · have hij : 2 ≤ i - j := by
        have := Finset.mem_range.mp hj
        omega
      rw [hz (i - j) hij]; simp

theorem qPoly_iter (y : Vec3) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ * cylR y ^ i
      ≤ 4 * cylR y ^ 2 := by
  have hfun : (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2))
      = fun z => -((fun w : Vec3 => (ContinuousLinearMap.proj (0 : Fin 3) : Vec3 →L[ℝ] ℝ) w *
          (ContinuousLinearMap.proj (0 : Fin 3) : Vec3 →L[ℝ] ℝ) w) z
        + (fun w : Vec3 => (ContinuousLinearMap.proj (1 : Fin 3) : Vec3 →L[ℝ] ℝ) w *
          (ContinuousLinearMap.proj (1 : Fin 3) : Vec3 →L[ℝ] ℝ) w) z) := by
    funext z
    simp [sq]
  have hA : ∀ n : ℕ, ‖iteratedFDeriv ℝ n (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖
      ≤ ‖iteratedFDeriv ℝ n (fun w : Vec3 => (ContinuousLinearMap.proj (0 : Fin 3) : Vec3 →L[ℝ] ℝ) w *
          (ContinuousLinearMap.proj (0 : Fin 3) : Vec3 →L[ℝ] ℝ) w) y‖
        + ‖iteratedFDeriv ℝ n (fun w : Vec3 => (ContinuousLinearMap.proj (1 : Fin 3) : Vec3 →L[ℝ] ℝ) w *
          (ContinuousLinearMap.proj (1 : Fin 3) : Vec3 →L[ℝ] ℝ) w) y‖ := by
    intro n
    rw [hfun]
    refine neg_add_norm_le _ _ n y ?_ ?_
    · exact ((ContinuousLinearMap.contDiff _).mul (ContinuousLinearMap.contDiff _)).contDiffAt
    · exact ((ContinuousLinearMap.contDiff _).mul (ContinuousLinearMap.contDiff _)).contDiffAt
  have hb0 := prod_norm_bounds 0 y
  have hb1 := prod_norm_bounds 1 y
  have hc0 : |y 0| ≤ cylR y := by
    unfold cylR
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 1)])
  have hc1 : |y 1| ≤ cylR y := by
    unfold cylR
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 0)])
  have hsq : cylR y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    unfold cylR
    exact Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ cylR y := by unfold cylR; positivity
  by_cases hi : 3 ≤ i
  · have hz0 := hb0.2.2.2 i hi
    have hz1 := hb1.2.2.2 i hi
    have hz : ‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ = 0 :=
      le_antisymm (by linarith [hA i]) (norm_nonneg _)
    rw [hz]
    nlinarith [sq_nonneg (cylR y)]
  · interval_cases i
    · have h0' : ‖iteratedFDeriv ℝ 0 (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖
          = y 0 ^ 2 + y 1 ^ 2 := by
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
      rw [pow_zero, mul_one, h0']
      nlinarith [sq_nonneg (cylR y)]
    · have h2 : ‖iteratedFDeriv ℝ 1 (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ ≤ 4 * cylR y := by
        linarith [hA 1, hb0.2.1, hb1.2.1, hc0, hc1]
      have h3 := mul_le_mul_of_nonneg_right h2 hr0
      rw [pow_one]
      nlinarith [h3, sq_nonneg (cylR y)]
    · have h2 : ‖iteratedFDeriv ℝ 2 (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ ≤ 4 := by
        linarith [hA 2, hb0.2.2.1, hb1.2.2.1]
      have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (cylR y))
      nlinarith [h3, sq_nonneg (cylR y)]

end PsiBoundAux

open PsiBoundAux

theorem term_ab (r B a b : ℝ) (i j m : ℕ) (hr : 0 < r) (hB : 0 ≤ B) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) (hij : i + j = m) (ha : a * r ^ i ≤ 4 * r ^ 2)
    (hb : b ≤ B * (r ^ (4 + j))⁻¹) :
    a * b ≤ 4 * B * (r ^ (2 + m))⁻¹ := by
  have hp : 0 < r ^ (4 + j) := pow_pos hr _
  have hne1 : r ^ (4 + j) ≠ 0 := hp.ne'
  have hne2 : r ^ (2 + m) ≠ 0 := (pow_pos hr _).ne'
  have hbB : b * r ^ (4 + j) ≤ B := by
    calc b * r ^ (4 + j) ≤ B * (r ^ (4 + j))⁻¹ * r ^ (4 + j) :=
          mul_le_mul_of_nonneg_right hb hp.le
      _ = B := by field_simp
  have hprod : (a * r ^ i) * (b * r ^ (4 + j)) ≤ (4 * r ^ 2) * B :=
    mul_le_mul ha hbB (mul_nonneg hb0 hp.le) (by positivity)
  have hm : r ^ (2 + m) * r ^ 2 = r ^ i * r ^ (4 + j) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hr2 : 0 < r ^ 2 := by positivity
  have key : a * b * r ^ (2 + m) ≤ 4 * B := by
    have h1 : (a * b * r ^ (2 + m)) * r ^ 2 ≤ (4 * B) * r ^ 2 := by
      calc (a * b * r ^ (2 + m)) * r ^ 2 = (a * b) * (r ^ (2 + m) * r ^ 2) := by ring
        _ = (a * b) * (r ^ i * r ^ (4 + j)) := by rw [hm]
        _ = (a * r ^ i) * (b * r ^ (4 + j)) := by ring
        _ ≤ (4 * r ^ 2) * B := hprod
        _ = (4 * B) * r ^ 2 := by ring
    exact le_of_mul_le_mul_right h1 hr2
  calc a * b = (a * b * r ^ (2 + m)) * (r ^ (2 + m))⁻¹ := by field_simp
    _ ≤ (4 * B) * (r ^ (2 + m))⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.mpr (pow_nonneg hr.le _))
    _ = 4 * B * (r ^ (2 + m))⁻¹ := rfl

theorem cylR_sq_eq' (y : Vec3) : cylR y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  unfold cylR
  exact Real.sq_sqrt (by positivity)

theorem scPsiBound : SCPsiBound := by
  refine ⟨512, ?_⟩
  intro ν B Z hν hB hZ m hm y hy
  have hcyl_sq := cylR_sq_eq' y
  have hr2 : 0 < cylR y ^ 2 := lt_of_lt_of_le hν hy
  have hr0 : 0 ≤ cylR y := by unfold cylR; positivity
  have hr : 0 < cylR y :=
    lt_of_le_of_ne hr0 (fun h => by rw [← h] at hr2; norm_num at hr2)
  have hyU : y ∈ psiU ν := by
    show ν * (11 / 12) < eucSq y ∧ 0 < cylR y
    refine ⟨?_, hr⟩
    rw [psiFdom_eucSq]
    nlinarith [sq_nonneg (y 2), sq_nonneg (y 0), sq_nonneg (y 1)]
  have hEq : streamPsi Z =ᶠ[𝓝 y]
      (fun z => -(z 0 ^ 2 + z 1 ^ 2) * ∫ t in Ioi (1 : ℝ), psiF Z t z) :=
    Filter.eventually_of_mem ((psiU_isOpen ν).mem_nhds hyU) (fun z hz =>
      scPsiSubst Z z (show ν * (11 / 12) < eucSq z ∧ 0 < cylR z from hz).2)
  rw [(hEq.iteratedFDeriv (𝕜 := ℝ) m).self_of_nhds]
  have hIc : ContDiffOn ℝ 7 (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) (psiU ν) :=
    scParamInt7 (psiU ν) (psiF Z) (psiU_isOpen ν)
      (fun t ht => scPsiF_smooth ν B Z hν hB hZ t ht)
      (fun k hk x hx => scPsiF_meas ν B Z hν hB hZ k hk x hx)
      (fun x₀ hx₀ => scPsiF_dom ν B Z hν hB hZ x₀ hx₀)
  have hqc : ContDiffOn ℝ 7 (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) (psiU ν) :=
    (by fun_prop : ContDiff ℝ 7 (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2))).contDiffOn
  have hmle : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm
  have hL := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) hqc hIc
    (psiU_isOpen ν).uniqueDiffOn hyU hmle
  have hsum : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      ‖iteratedFDerivWithin ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) (psiU ν) y‖ *
      ‖iteratedFDerivWithin ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) (psiU ν) y‖)
      = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ *
      ‖iteratedFDeriv ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖ :=
    Finset.sum_congr rfl (fun i _ => by
      rw [(iteratedFDerivWithin_of_isOpen i (psiU_isOpen ν)) hyU,
        (iteratedFDerivWithin_of_isOpen (m - i) (psiU_isOpen ν)) hyU])
  have hL2 : ‖iteratedFDeriv ℝ m (fun z => -(z 0 ^ 2 + z 1 ^ 2) *
      ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
      ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖ := by
    rw [← (iteratedFDerivWithin_of_isOpen m (psiU_isOpen ν)) hyU]
    exact hL.trans (le_of_eq hsum)
  have hbound : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ *
        ‖iteratedFDeriv ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
      ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (4 * B * (cylR y ^ (2 + m))⁻¹) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ m := by
      have := Finset.mem_range.mp hi
      omega
    have t := term_ab (cylR y) B _ _ i (m - i) m hr hB (norm_nonneg _) (norm_nonneg _)
      (by omega) (qPoly_iter y i) (psiI_bound ν B Z hν hB hZ y hyU (m - i) (by omega))
    have hc : (0 : ℝ) ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
    calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
        = (m.choose i : ℝ) * (‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖) := by ring
      _ ≤ (m.choose i : ℝ) * (4 * B * (cylR y ^ (2 + m))⁻¹) := mul_le_mul_of_nonneg_left t hc
  have hpow : (2 : ℝ) ^ m ≤ 128 := by
    have : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ 7 := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this
    linarith
  have hsc : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = 2 ^ m := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    rfl
  have hconv : cylR y ^ (-(2 : ℝ) - (m : ℝ)) = (cylR y ^ (2 + m))⁻¹ := by
    rw [show (-(2 : ℝ) - (m : ℝ)) = -((2 + m : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hr.le, Real.rpow_natCast]
  have hK : 0 ≤ 4 * B * (cylR y ^ (2 + m))⁻¹ := by
    have := inv_nonneg.mpr (pow_nonneg hr.le (2 + m))
    positivity
  calc ‖iteratedFDeriv ℝ m (fun z => -(z 0 ^ 2 + z 1 ^ 2) *
          ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
      ≤ _ := hL2
    _ ≤ _ := hbound
    _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * (4 * B * (cylR y ^ (2 + m))⁻¹) := by
        rw [Finset.sum_mul]
    _ = 2 ^ m * (4 * B * (cylR y ^ (2 + m))⁻¹) := by rw [hsc]
    _ ≤ 128 * (4 * B * (cylR y ^ (2 + m))⁻¹) := mul_le_mul_of_nonneg_right hpow hK
    _ = 512 * B * cylR y ^ (-(2 : ℝ) - (m : ℝ)) := by rw [hconv]; ring



end UnforcedLeray.Short.PartIIIb.Concrete
