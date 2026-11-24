import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGradOrg
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.PsiBound

/-!
# `SCPsiBoundOff`: the outward stream primitive off the ray (source 4180-4182, 5400-5413)

Same proof as `scPsiBound` (`StreamCut/PsiBound.lean`), but the integrand bound keeps the full
height: `‖D^k psiF Z t x‖ ≤ B r^{-k} t (t²r²+z²)^{-2}`, and
`∫_{(1,∞)} t (t²r²+z²)^{-2} dt = 1/(2r²(r²+z²))`.
Source: `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PsiOffAux

theorem sharp_alg (t r s B : ℝ) (k : ℕ) (ht : 0 < t) (hr : 0 < r) (hs : t * r ≤ s) (hB : 0 ≤ B) :
    t * (B * s ^ (-(4:ℝ) - (k:ℝ))) * t ^ k ≤ B * (r ^ k)⁻¹ * (t / (s ^ 2) ^ 2) := by
  have hs0 : 0 < s := lt_of_lt_of_le (mul_pos ht hr) hs
  have hconv : s ^ (-(4:ℝ) - (k:ℝ)) = (s ^ (4 + k))⁻¹ := by
    rw [show (-(4:ℝ) - (k:ℝ)) = -((4 + k : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hs0.le, Real.rpow_natCast]
  rw [hconv]
  have hk : t ^ k * r ^ k ≤ s ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (mul_pos ht hr).le hs k
  have hrk : 0 < r ^ k := pow_pos hr _
  have hsk : 0 < s ^ k := pow_pos hs0 _
  have h1 : t ^ k / s ^ k ≤ (r ^ k)⁻¹ := by
    rw [div_le_iff₀ hsk]
    calc t ^ k = t ^ k * r ^ k * (r ^ k)⁻¹ := by field_simp
      _ ≤ s ^ k * (r ^ k)⁻¹ := mul_le_mul_of_nonneg_right hk (inv_nonneg.mpr hrk.le)
      _ = (r ^ k)⁻¹ * s ^ k := by ring
  have e1 : t * (B * (s ^ (4 + k))⁻¹) * t ^ k = (B * t / s ^ 4) * (t ^ k / s ^ k) := by
    rw [pow_add]; field_simp
  have e2 : B * (r ^ k)⁻¹ * (t / (s ^ 2) ^ 2) = (B * t / s ^ 4) * (r ^ k)⁻¹ := by
    rw [← pow_mul]; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem psiF_jet_bound_off (ν B : ℝ) (Z : Vec3 → Vec3) (hν : 0 < ν) (hB : 0 ≤ B)
    (hZ : SCZHyp ν B Z) (t : ℝ) (ht : 1 < t) (x : Vec3) (hx : x ∈ psiU ν) (k : ℕ) (hk : k ≤ 7) :
    ‖iteratedFDeriv ℝ k (psiF Z t) x‖
      ≤ B * (cylR x ^ k)⁻¹ * (t / (t ^ 2 * cylR x ^ 2 + x 2 ^ 2) ^ 2) := by
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
  have hSeq : eucSq (psiFdomL t x) = t ^ 2 * cylR x ^ 2 + x 2 ^ 2 := by
    rw [psiFdom_eucSq, hLx0, hLx1, hLx2, hcx]; ring
  have hsq2 : (t * cylR x) ^ 2 ≤ eucSq (psiFdomL t x) := by
    rw [hSeq, mul_pow]; nlinarith [sq_nonneg (x 2)]
  have hsqrt : t * cylR x ≤ Real.sqrt (eucSq (psiFdomL t x)) :=
    (Real.le_sqrt (mul_pos ht0 hr).le
      (by rw [psiFdom_eucSq]; positivity)).mpr hsq2
  have hZbound := hZ2 k hk (psiFdomL t x) hLmem
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
  have hsal := sharp_alg t (cylR x) (Real.sqrt (eucSq (psiFdomL t x))) B k ht0 hr hsqrt hB
  have hsr : (Real.sqrt (eucSq (psiFdomL t x))) ^ 2 = t ^ 2 * cylR x ^ 2 + x 2 ^ 2 := by
    rw [Real.sq_sqrt (by rw [psiFdom_eucSq]; positivity), hSeq]
  rw [hsr] at hsal
  show ‖iteratedFDeriv ℝ k (psiF Z t) x‖ ≤ _
  rw [hfun]
  calc ‖iteratedFDeriv ℝ k (((t • (ContinuousLinearMap.proj (2 : Fin 3) :
          Vec3 →L[ℝ] ℝ)) ∘ Z) ∘ psiFdomL t) x‖
      ≤ ‖iteratedFDeriv ℝ k ((t • (ContinuousLinearMap.proj (2 : Fin 3) :
          Vec3 →L[ℝ] ℝ)) ∘ Z) (psiFdomL t x)‖ * ‖psiFdomL t‖ ^ k := hcomp
    _ ≤ (‖t • (ContinuousLinearMap.proj (2 : Fin 3) : Vec3 →L[ℝ] ℝ)‖
          * ‖iteratedFDeriv ℝ k Z (psiFdomL t x)‖) * ‖psiFdomL t‖ ^ k :=
        mul_le_mul_of_nonneg_right hQ (by positivity)
    _ ≤ (t * (B * (Real.sqrt (eucSq (psiFdomL t x))) ^ (-(4:ℝ) - (k:ℝ)))) * t ^ k :=
        mul_le_mul
          (mul_le_mul hQn hZbound (norm_nonneg _) ht0.le)
          (pow_le_pow_left₀ (norm_nonneg _) (psiFdomL_norm_le ht1) k)
          (by positivity)
          (mul_nonneg ht0.le (mul_nonneg hB
            (Real.rpow_nonneg (Real.sqrt_nonneg _) _)))
    _ ≤ _ := hsal

theorem integral_off (r z : ℝ) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t / (t ^ 2 * r ^ 2 + z ^ 2) ^ 2) (Ioi (1 : ℝ)) ∧
    ∫ t in Ioi (1 : ℝ), t / (t ^ 2 * r ^ 2 + z ^ 2) ^ 2 = 1 / (2 * r ^ 2 * (r ^ 2 + z ^ 2)) := by
  have hpos : ∀ t : ℝ, 1 ≤ t → 0 < t ^ 2 * r ^ 2 + z ^ 2 := fun t ht => by
    have : 0 < t ^ 2 * r ^ 2 := by positivity
    nlinarith [sq_nonneg z]
  have hr2 : 0 < r ^ 2 := by positivity
  set f : ℝ → ℝ := fun t => -(1 / (2 * r ^ 2)) * (t ^ 2 * r ^ 2 + z ^ 2)⁻¹ with hf
  have hderiv : ∀ t ∈ Ici (1 : ℝ), HasDerivAt f (t / (t ^ 2 * r ^ 2 + z ^ 2) ^ 2) t := by
    intro t ht
    have hp := hpos t ht
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 * r ^ 2 + z ^ 2) (2 * t * r ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).mul_const (r ^ 2)).add_const (z ^ 2)
      exact this.congr_deriv (by norm_num)
    have h2 := (h1.inv hp.ne').const_mul (-(1 / (2 * r ^ 2)))
    refine h2.congr_deriv ?_
    field_simp
  have hcont : ContinuousWithinAt f (Ici 1) 1 :=
    (hderiv 1 (by simp)).continuousAt.continuousWithinAt
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ 2 * r ^ 2) atTop atTop :=
      (tendsto_pow_atTop (two_ne_zero)).atTop_mul_const hr2
    have h2 : Tendsto (fun t : ℝ => t ^ 2 * r ^ 2 + z ^ 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ h1
    have h3 := (tendsto_inv_atTop_zero.comp h2).const_mul (-(1 / (2 * r ^ 2)))
    simpa [hf] using h3
  have hnn : ∀ t ∈ Ioi (1 : ℝ), 0 ≤ t / (t ^ 2 * r ^ 2 + z ^ 2) ^ 2 := fun t ht => by
    have := hpos t (le_of_lt ht)
    have : (0:ℝ) < t := by linarith [mem_Ioi.mp ht]
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont
    (fun t ht => hderiv t (Ioi_subset_Ici_self ht)) hnn hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun t ht => hderiv t (Ioi_subset_Ici_self ht)) hint hlim]
  simp only [hf]
  have := hpos 1 le_rfl
  field_simp
  ring

theorem psiI_bound_off (ν B : ℝ) (Z : Vec3 → Vec3) (hν : 0 < ν) (hB : 0 ≤ B)
    (hZ : SCZHyp ν B Z) (y : Vec3) (hy : y ∈ psiU ν) (j : ℕ) (hj : j ≤ 7) :
    ‖iteratedFDeriv ℝ j (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
      ≤ B * (cylR y ^ (2 + j))⁻¹ * (eucSq y)⁻¹ := by
  have hFs : ∀ t : ℝ, 1 < t → ContDiffOn ℝ ((7 : ℕ) : WithTop ℕ∞) (psiF Z t) (psiU ν) :=
    fun t ht => by exact_mod_cast scPsiF_smooth ν B Z hν hB hZ t ht
  have hE := PsiBoundAux.normExch j (E := ℝ) (psiU ν) (psiF Z) 7 (psiU_isOpen ν) hj hFs
    (fun k hk x hx => scPsiF_meas ν B Z hν hB hZ k hk x hx)
    (fun x₀ hx₀ => scPsiF_dom ν B Z hν hB hZ x₀ hx₀) y hy
  have hr : 0 < cylR y := (show ν * (11 / 12) < eucSq y ∧ 0 < cylR y from hy).2
  have hcy := cylR_sq_eq' y
  have hE2 : eucSq y = cylR y ^ 2 + y 2 ^ 2 := by
    rw [psiFdom_eucSq, hcy]
  obtain ⟨hint0, hval0⟩ := integral_off (cylR y) (y 2) hr
  have hint : IntegrableOn
      (fun t : ℝ => B * (cylR y ^ j)⁻¹ * (t / (t ^ 2 * cylR y ^ 2 + y 2 ^ 2) ^ 2))
      (Ioi (1 : ℝ)) := hint0.const_mul _
  have hmono : ∫ t in Ioi (1 : ℝ), ‖iteratedFDeriv ℝ j (psiF Z t) y‖
      ≤ ∫ t in Ioi (1 : ℝ),
        B * (cylR y ^ j)⁻¹ * (t / (t ^ 2 * cylR y ^ 2 + y 2 ^ 2) ^ 2) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _) hint ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht =>
        psiF_jet_bound_off ν B Z hν hB hZ t ht y hy j hj)
  have hval : ∫ t in Ioi (1 : ℝ),
        B * (cylR y ^ j)⁻¹ * (t / (t ^ 2 * cylR y ^ 2 + y 2 ^ 2) ^ 2)
      = B * (cylR y ^ j)⁻¹ * (1 / (2 * cylR y ^ 2 * (eucSq y))) := by
    rw [integral_const_mul, hval0, hE2]
  have hp : 0 < cylR y ^ j := pow_pos hr _
  have hEpos : 0 < eucSq y := by rw [hE2]; positivity
  have hfin : B * (cylR y ^ j)⁻¹ * (1 / (2 * cylR y ^ 2 * eucSq y))
      ≤ B * (cylR y ^ (2 + j))⁻¹ * (eucSq y)⁻¹ := by
    have : B * (cylR y ^ j)⁻¹ * (1 / (2 * cylR y ^ 2 * eucSq y))
        = (B * (cylR y ^ (2 + j))⁻¹ * (eucSq y)⁻¹) * (1 / 2) := by
      rw [pow_add]; field_simp
    rw [this]
    have : 0 ≤ B * (cylR y ^ (2 + j))⁻¹ * (eucSq y)⁻¹ := by positivity
    linarith
  calc ‖iteratedFDeriv ℝ j (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
      ≤ ∫ t in Ioi (1 : ℝ), ‖iteratedFDeriv ℝ j (psiF Z t) y‖ := hE
    _ ≤ _ := hmono
    _ = _ := hval
    _ ≤ _ := hfin

theorem term_off (r B E a b : ℝ) (i j m : ℕ) (hr : 0 < r) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hij : i + j = m) (ha : a * r ^ i ≤ 4 * r ^ 2)
    (hb : b ≤ B * (r ^ (2 + j))⁻¹ * E) :
    a * b ≤ 4 * B * E * (r ^ m)⁻¹ := by
  have hp : 0 < r ^ (2 + j) := pow_pos hr _
  have hpm : 0 < r ^ m := pow_pos hr _
  have hbB : b * r ^ (2 + j) ≤ B * E := by
    calc b * r ^ (2 + j) ≤ B * (r ^ (2 + j))⁻¹ * E * r ^ (2 + j) :=
          mul_le_mul_of_nonneg_right hb hp.le
      _ = B * E := by field_simp
  have hprod : (a * r ^ i) * (b * r ^ (2 + j)) ≤ (4 * r ^ 2) * (B * E) :=
    mul_le_mul ha hbB (mul_nonneg hb0 hp.le) (by positivity)
  have hm : r ^ m * r ^ 2 = r ^ i * r ^ (2 + j) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hr2 : 0 < r ^ 2 := by positivity
  have key : a * b * r ^ m ≤ 4 * (B * E) := by
    have h1 : (a * b * r ^ m) * r ^ 2 ≤ (4 * (B * E)) * r ^ 2 := by
      calc (a * b * r ^ m) * r ^ 2 = (a * b) * (r ^ m * r ^ 2) := by ring
        _ = (a * b) * (r ^ i * r ^ (2 + j)) := by rw [hm]
        _ = (a * r ^ i) * (b * r ^ (2 + j)) := by ring
        _ ≤ (4 * r ^ 2) * (B * E) := hprod
        _ = (4 * (B * E)) * r ^ 2 := by ring
    exact le_of_mul_le_mul_right h1 hr2
  calc a * b = (a * b * r ^ m) * (r ^ m)⁻¹ := by field_simp
    _ ≤ (4 * (B * E)) * (r ^ m)⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hpm.le)
    _ = 4 * B * E * (r ^ m)⁻¹ := by ring

end PsiOffAux

open PsiOffAux PsiBoundAux in
/-- **`SCPsiBoundOff`** (source 4180-4182, 5400-5413). -/
theorem scPsiBoundOff : SCPsiBoundOff := by
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
  have hEpos : 0 < eucSq y := by
    rw [psiFdom_eucSq]; nlinarith [sq_nonneg (y 2), sq_nonneg (y 0), sq_nonneg (y 1)]
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
  have hm7 : m ≤ 7 := by omega
  have hmle : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm7
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
        (4 * B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ m := by
      have := Finset.mem_range.mp hi
      omega
    have t := term_off (cylR y) B (eucSq y)⁻¹ _ _ i (m - i) m hr hB (inv_nonneg.mpr hEpos.le)
      (norm_nonneg _) (norm_nonneg _)
      (by omega) (qPoly_iter y i) (psiI_bound_off ν B Z hν hB hZ y hyU (m - i) (by omega))
    have hc : (0 : ℝ) ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
    calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
        = (m.choose i : ℝ) * (‖iteratedFDeriv ℝ i (fun z : Vec3 => -(z 0 ^ 2 + z 1 ^ 2)) y‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun z => ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖) := by ring
      _ ≤ (m.choose i : ℝ) * (4 * B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹) :=
          mul_le_mul_of_nonneg_left t hc
  have hpow : (2 : ℝ) ^ m ≤ 8 := by
    have : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) hm
    norm_num at this
    linarith
  have hsc : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) = 2 ^ m := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    rfl
  have hconv : cylR y ^ (-(m : ℝ)) = (cylR y ^ m)⁻¹ := by
    rw [Real.rpow_neg hr.le, Real.rpow_natCast]
  have hK : 0 ≤ 4 * B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹ := by
    have := inv_nonneg.mpr (pow_nonneg hr.le m)
    have := inv_nonneg.mpr hEpos.le
    positivity
  calc ‖iteratedFDeriv ℝ m (fun z => -(z 0 ^ 2 + z 1 ^ 2) *
          ∫ t in Ioi (1 : ℝ), psiF Z t z) y‖
      ≤ _ := hL2
    _ ≤ _ := hbound
    _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * (4 * B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹) := by
        rw [Finset.sum_mul]
    _ = 2 ^ m * (4 * B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹) := by rw [hsc]
    _ ≤ 8 * (4 * B * (eucSq y)⁻¹ * (cylR y ^ m)⁻¹) := mul_le_mul_of_nonneg_right hpow hK
    _ ≤ 512 * B * cylR y ^ (-(m : ℝ)) * (eucSq y)⁻¹ := by rw [hconv]; nlinarith [hK]

end UnforcedLeray.Short.PartIIIb.Concrete
