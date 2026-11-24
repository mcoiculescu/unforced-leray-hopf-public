import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonAxis
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.SDLine
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.SDEuler
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.SDMat

/-!
# Short-time (`0 < s < 4 / (5ν)`) Taylor remainder bound (`PartIII-b:IIIb-D3/2/G5/2`)

Reduces the `0 < s < 4 / (5ν)` branch of `NewtonTaylor` to `SigmaIntForm χo` and
`NewtonVRemBound χo` via the axis line restriction (`SDLine`), the cutoff extension `chiYr ν 1 χy`,
the Euler operator (`SDEuler`), and matrix entrywise bookkeeping (`SDMat`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

/-- Jet bound for the zero-width Newton Taylor remainder `newtonVRem := newtonV - newtonV0`
on `{w | ν * (11 / 12) < eucSq w}` with the cut first moment `oldN1w`. -/
def NewtonVRemBound (χo : ℝ → ℝ) : Prop :=
  ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
    ∀ (c ν μ : ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo → 0 ≤ μ →
      ∀ M : Chart → Mat3, OldThinFinite c ν M →
        ContDiffOn ℝ 7 (newtonVRem c ν μ χo M) {w | ν * (11 / 12) < eucSq w} ∧
        ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
          ‖iteratedFDeriv ℝ m (newtonVRem c ν μ χo M) w‖ ≤
            C m * oldN1w c ν χo M * (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m)

/-- `oldN1w c ν χo M` is nonnegative for `0 < ν`, `IsOutwardCutoff χo`. -/
theorem oldN1w_nonneg {c ν : ℝ} (hν : 0 < ν) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (M : Chart → Mat3) : 0 ≤ oldN1w c ν χo M := by
  unfold oldN1w
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  have hu0 : 0 < u := ha.trans hu
  have hχ0 : 0 ≤ χo (ν * u) := (hχo.range (ν * u)).1
  have hcell : 0 ≤ ∫ p, frob (M (u, p)) ∂(Cyl.avgμ c) :=
    integral_nonneg fun p => frob_nonneg' _
  positivity

/-- Local congruence for `sDerivIter` at a point `s`. -/
theorem sDerivIter_congr_nhds : ∀ (j : ℕ) {A B : ℝ → Mat3} {s : ℝ},
    A =ᶠ[𝓝 s] B → sDerivIter j A =ᶠ[𝓝 s] sDerivIter j B
  | 0, _, _, _, h => h
  | j + 1, A, B, s, h => by
    have ih := sDerivIter_congr_nhds j h
    filter_upwards [ih.eventuallyEq_nhds] with t ht
    show t • deriv (sDerivIter j A) t = t • deriv (sDerivIter j B) t
    rw [ht.deriv_eq]

/-- Line restriction on `{w | ν * (11 / 12) < eucSq w}`: if `Z` is `C^7` on that open set with
`‖D^m Z(w)‖ ≤ B * |w|^{-5-m}`, then `h(r) := fderiv ℝ Z ![r, 0, 0] (Pi.single j 1) i` is `C^6` on
`Ioi (Real.sqrt (ν * (11 / 12)))` with `|h^{(k)}(r)| ≤ B * r^{-5-(k+1)}` for `k ≤ 6`. -/
theorem line_rem_bound {ν B : ℝ} (hν : 0 < ν) (_hB : 0 ≤ B) {Z : Vec3 → Vec3}
    (hZ : ContDiffOn ℝ 7 Z {w | ν * (11 / 12) < eucSq w})
    (hb : ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
      ‖iteratedFDeriv ℝ m Z w‖ ≤ B * (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m))
    (i j : Fin 3) :
    ContDiffOn ℝ 6 (fun r : ℝ => fderiv ℝ Z ![r, 0, 0] (Pi.single j 1) i)
      (Ioi (Real.sqrt (ν * (11 / 12)))) ∧
    ∀ k : ℕ, k ≤ 6 → ∀ r : ℝ, Real.sqrt (ν * (11 / 12)) < r →
      |iteratedDeriv k (fun r : ℝ => fderiv ℝ Z ![r, 0, 0] (Pi.single j 1) i) r| ≤
        B * r ^ (-(5 : ℝ) - (k + 1 : ℕ)) := by
  set U : Set Vec3 := {w | ν * (11 / 12) < eucSq w} with hUdef
  have hUo : IsOpen U := NewtonVGeom.isOpen_regU ν
  have hF' : ContDiffOn ℝ 6 (fderiv ℝ Z) U := hZ.fderiv_of_isOpen hUo (by norm_num)
  obtain ⟨L, hLapp⟩ : ∃ L : ℝ →L[ℝ] Vec3, ∀ t, L t = t • (Pi.single 0 (1 : ℝ) : Vec3) :=
    ⟨ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (Pi.single 0 (1 : ℝ)),
      fun t => by simp⟩
  have he0 : ‖(Pi.single 0 (1 : ℝ) : Vec3)‖ = 1 := by rw [Pi.norm_single, norm_one]
  have hej : ‖(Pi.single j (1 : ℝ) : Vec3)‖ = 1 := by rw [Pi.norm_single, norm_one]
  have hLline : ∀ t : ℝ, L t = ![t, 0, 0] := by
    intro t; rw [hLapp]; ext k; fin_cases k <;> simp
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound L zero_le_one fun t => ?_
    rw [hLapp, norm_smul, he0, one_mul, mul_comm]; simp
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Vec3 →L[ℝ] Vec3) →L[ℝ] ℝ,
      ∀ A : Vec3 →L[ℝ] Vec3, Φ A = A (Pi.single j (1 : ℝ)) i :=
    ⟨(ContinuousLinearMap.proj i).comp (ContinuousLinearMap.apply ℝ Vec3 (Pi.single j (1 : ℝ))),
      fun A => rfl⟩
  have hΦn : ‖Φ‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound Φ zero_le_one fun A => ?_
    rw [hΦ, one_mul]
    calc ‖A (Pi.single j (1 : ℝ)) i‖ ≤ ‖A (Pi.single j (1 : ℝ))‖ := norm_le_pi_norm _ i
      _ ≤ ‖A‖ * ‖(Pi.single j (1 : ℝ) : Vec3)‖ := A.le_opNorm _
      _ = ‖A‖ := by rw [hej, mul_one]
  have hG : ContDiffOn ℝ 6 (fun y => Φ (fderiv ℝ Z y)) U := Φ.contDiff.comp_contDiffOn hF'
  have heuc_L : ∀ t : ℝ, eucSq (L t) = t ^ 2 := by
    intro t
    rw [hLline t]
    unfold eucSq
    rw [Fin.sum_univ_three]
    simp
  have hLmaps : MapsTo L (Ioi (Real.sqrt (ν * (11 / 12)))) U := by
    intro t ht
    show ν * (11 / 12) < eucSq (L t)
    rw [heuc_L t]
    have ht_lt : Real.sqrt (ν * (11 / 12)) < t := ht
    have h0 : 0 ≤ Real.sqrt (ν * (11 / 12)) := Real.sqrt_nonneg _
    have hsq : (Real.sqrt (ν * (11 / 12))) ^ 2 < t ^ 2 :=
      pow_lt_pow_left₀ ht_lt h0 (by decide)
    rwa [Real.sq_sqrt (by positivity)] at hsq
  have hhc : ContDiffOn ℝ 6 ((fun y => Φ (fderiv ℝ Z y)) ∘ L) (Ioi (Real.sqrt (ν * (11 / 12)))) :=
    hG.comp L.contDiff.contDiffOn hLmaps
  have hfun : (fun r : ℝ => fderiv ℝ Z ![r, 0, 0] (Pi.single j (1 : ℝ)) i) =
      (fun y => Φ (fderiv ℝ Z y)) ∘ L := by
    funext r
    show fderiv ℝ Z ![r, 0, 0] (Pi.single j (1 : ℝ)) i = Φ (fderiv ℝ Z (L r))
    rw [hΦ, hLline r]
  refine ⟨by rw [hfun]; exact hhc, fun k hk r hr => ?_⟩
  rw [hfun]
  have hLr : L r ∈ U := hLmaps hr
  have hrU : r ∈ L ⁻¹' U := hLr
  have hwithin := L.iteratedFDerivWithin_comp_right hG hUo.uniqueDiffOn
    (IsOpen.preimage L.continuous hUo).uniqueDiffOn hLr (i := k) (by exact_mod_cast hk)
  have e1 : iteratedFDerivWithin ℝ k ((fun y => Φ (fderiv ℝ Z y)) ∘ L) (L ⁻¹' U) r =
      iteratedFDeriv ℝ k ((fun y => Φ (fderiv ℝ Z y)) ∘ L) r :=
    iteratedFDerivWithin_of_isOpen k (IsOpen.preimage L.continuous hUo) hrU
  have e2 : iteratedFDerivWithin ℝ k (fun y => Φ (fderiv ℝ Z y)) U (L r) =
      iteratedFDeriv ℝ k (fun y => Φ (fderiv ℝ Z y)) (L r) :=
    iteratedFDerivWithin_of_isOpen k hUo hLr
  have hfd : iteratedFDeriv ℝ k ((fun y => Φ (fderiv ℝ Z y)) ∘ L) r =
      (iteratedFDeriv ℝ k (fun y => Φ (fderiv ℝ Z y)) (L r)).compContinuousLinearMap
        (fun _ => L) := by
    rw [← e1, hwithin, e2]
  have hn1 : ‖iteratedFDeriv ℝ k ((fun y => Φ (fderiv ℝ Z y)) ∘ L) r‖ ≤
      ‖iteratedFDeriv ℝ k (fun y => Φ (fderiv ℝ Z y)) (L r)‖ := by
    rw [hfd]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hprod : ∏ _i : Fin k, ‖L‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hLn)
    exact mul_le_of_le_one_right (norm_nonneg _) hprod
  have hcontAt : ContDiffAt ℝ 6 (fderiv ℝ Z) (L r) :=
    (hZ.contDiffAt (hUo.mem_nhds hLr)).fderiv_right (m := 6) (by norm_num)
  have hn2 : ‖iteratedFDeriv ℝ k (fun y => Φ (fderiv ℝ Z y)) (L r)‖ ≤
      ‖iteratedFDeriv ℝ k (fderiv ℝ Z) (L r)‖ := by
    have := ContinuousLinearMap.norm_iteratedFDeriv_comp_left Φ hcontAt
      (n := k) (by exact_mod_cast hk)
    exact this.trans (mul_le_of_le_one_left (norm_nonneg _) hΦn)
  have hn3 : ‖iteratedFDeriv ℝ k (fderiv ℝ Z) (L r)‖ =
      ‖iteratedFDeriv ℝ (k + 1) Z (L r)‖ := norm_iteratedFDeriv_fderiv
  have hrpos : 0 < r := lt_of_lt_of_le (Real.sqrt_pos.2 (by positivity)) hr.le
  have h4 := hb (k + 1) (by omega) (L r) hLr
  have hsq_L : Real.sqrt (eucSq (L r)) = r := by
    rw [heuc_L r, Real.sqrt_sq hrpos.le]
  rw [hsq_L] at h4
  have h5 : |iteratedDeriv k ((fun y => Φ (fderiv ℝ Z y)) ∘ L) r| ≤
      ‖iteratedFDeriv ℝ k ((fun y => Φ (fderiv ℝ Z y)) ∘ L) r‖ := by
    rw [iteratedDeriv_eq_iteratedFDeriv, ← Real.norm_eq_abs]
    have := (iteratedFDeriv ℝ k ((fun y => Φ (fderiv ℝ Z y)) ∘ L) r).le_opNorm
      (fun _ : Fin k => (1 : ℝ))
    simpa using this
  exact (((h5.trans hn1).trans hn2).trans hn3.le).trans h4

/-- `chiYr ν 1 χy` is `ContDiffOn ℝ 6` on `Ioi 0`. -/
theorem contDiffOn_chiYr_Ioi (ν : ℝ) {χy : ℝ → ℝ} (hχy : IsStreamCutoff χy) :
    ContDiffOn ℝ 6 (chiYr ν 1 χy) (Ioi 0) := by
  have hsm : ContDiff ℝ 6 χy := hχy.smooth.of_le (by norm_num)
  have hg : ContDiffOn ℝ 6 (fun r : ℝ => ν / (1 * r) ^ 2) (Ioi 0) := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have h1 : ContDiffAt ℝ 6 (fun x : ℝ => (1 * x) ^ 2) r := by fun_prop
    exact (contDiffAt_const.div h1
      (pow_ne_zero 2 (mul_ne_zero one_ne_zero hr0))).contDiffWithinAt
  refine (hsm.comp_contDiffOn hg).congr fun r hr => ?_
  unfold chiYr
  rw [if_neg (ne_of_gt hr)]
  rfl

/-- Cutoff extension to `Ioi 0`: if `h_raw` is `ContDiffOn ℝ 6` on `Ioi (Real.sqrt (ν * (11 / 12)))`,
then `r ↦ chiYr ν 1 χy r * h_raw r` is `ContDiffOn ℝ 6` on `Ioi 0`. -/
theorem contDiffOn_chiYr_mul_Ioi {ν : ℝ} (hν : 0 < ν) {χy : ℝ → ℝ} (hχy : IsStreamCutoff χy)
    {h_raw : ℝ → ℝ} (hh : ContDiffOn ℝ 6 h_raw (Ioi (Real.sqrt (ν * (11 / 12))))) :
    ContDiffOn ℝ 6 (fun r => chiYr ν 1 χy r * h_raw r) (Ioi 0) := by
  intro r hr
  by_cases hgt : Real.sqrt (ν * (11 / 12)) < r
  · have hc1 : ContDiffAt ℝ 6 (chiYr ν 1 χy) r :=
      (contDiffOn_chiYr_Ioi ν hχy).contDiffAt (isOpen_Ioi.mem_nhds hr)
    have hc2 : ContDiffAt ℝ 6 h_raw r :=
      hh.contDiffAt (isOpen_Ioi.mem_nhds hgt)
    exact (hc1.mul hc2).contDiffWithinAt
  · have hlt : r < Real.sqrt ν := by
      have h1 : Real.sqrt (ν * (11 / 12)) < Real.sqrt ν :=
        Real.sqrt_lt_sqrt (by positivity) (by linarith)
      exact lt_of_le_of_lt (not_lt.1 hgt) h1
    have hopen : IsOpen (Ioo (0 : ℝ) (Real.sqrt ν)) := isOpen_Ioo
    have hmem : r ∈ Ioo (0 : ℝ) (Real.sqrt ν) := ⟨hr, hlt⟩
    have hev : (fun t => chiYr ν 1 χy t * h_raw t) =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hmem] with t ht
      have ht2 : t ^ 2 < ν := by
        have hsq : t ^ 2 < (Real.sqrt ν) ^ 2 :=
          pow_lt_pow_left₀ ht.2 ht.1.le (by decide)
        rwa [Real.sq_sqrt hν.le] at hsq
      rw [xj_chiYr_zero hχy ht2, zero_mul]
    exact (contDiffAt_const.congr_of_eventuallyEq hev).contDiffWithinAt

/-- Euler bound at `s` when `h` is `C^6` on `Ioi 0` and satisfies `|h^{(k)}(r)| ≤ B * r^{-6-k}`
at the single point `r = 1 / √s` (`k ≤ 6`). -/
theorem euler_pointwise_s3 {h : ℝ → ℝ} {B s : ℝ} (hB : 0 ≤ B)
    (hh : ContDiffOn ℝ 6 h (Ioi 0)) (hs : 0 < s)
    (hbd : ∀ k : ℕ, k ≤ 6 →
      |iteratedDeriv k h ((1 : ℝ)⁻¹ / Real.sqrt s)| ≤
        B * ((1 : ℝ)⁻¹ / Real.sqrt s) ^ (-(5 : ℝ) - (k + 1 : ℕ)))
    (j : ℕ) (hj6 : j ≤ 6) :
    |sDerivIterS j (fun t : ℝ => if 0 < t then h ((1 : ℝ)⁻¹ / Real.sqrt t) else 0) s| ≤
      35280 * B * s ^ (3 : ℝ) := by
  obtain ⟨c, -, hcb, hcr⟩ := eulerT_coeff h hh j hj6
  set r := (1 : ℝ)⁻¹ / Real.sqrt s with hrdef
  have hr : 0 < r := by
    have := Real.sqrt_pos.2 hs
    positivity
  have hpk : ∀ k : ℕ, r ^ k * r ^ (-(5 : ℝ) - (k + 1 : ℕ)) = r ^ (-(6 : ℝ)) := by
    intro k
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    congr 1
    push_cast
    ring
  have hFb : |eulerT^[j] h r| ≤
      ((j : ℝ) + 1) * ((j + 1).factorial : ℝ) * B * r ^ (-(6 : ℝ)) := by
    rw [hcr r hr]
    calc |∑ k ∈ Finset.range (j + 1), c k * r ^ k * iteratedDeriv k h r|
        ≤ ∑ k ∈ Finset.range (j + 1), |c k * r ^ k * iteratedDeriv k h r| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (j + 1), ((j + 1).factorial : ℝ) * B * r ^ (-(6 : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have h1 : |c k| ≤ ((j + 1).factorial : ℝ) := hcb k hk'
          have h2 : |iteratedDeriv k h r| ≤ B * r ^ (-(5 : ℝ) - (k + 1 : ℕ)) :=
            hbd k (by omega)
          calc |c k * r ^ k * iteratedDeriv k h r|
              = |c k| * r ^ k * |iteratedDeriv k h r| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr.le k)]
            _ ≤ ((j + 1).factorial : ℝ) * r ^ k * (B * r ^ (-(5 : ℝ) - (k + 1 : ℕ))) :=
                mul_le_mul (mul_le_mul_of_nonneg_right h1 (pow_nonneg hr.le k)) h2
                  (abs_nonneg _) (by positivity)
            _ = ((j + 1).factorial : ℝ) * B * r ^ (-(6 : ℝ)) := by
                rw [← hpk k]
                ring
      _ = ((j : ℝ) + 1) * ((j + 1).factorial : ℝ) * B * r ^ (-(6 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hr6 : r ^ (-(6 : ℝ)) = s ^ (3 : ℝ) := by
    rw [hrdef, inv_one, one_div, Real.inv_rpow (Real.sqrt_nonneg s), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hs.le, ← Real.rpow_neg hs.le]
    congr 1
    norm_num
  have hpow1 : |(-1 / 2 : ℝ) ^ j| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (by norm_num [abs_div])
  have hcomb : ((j : ℝ) + 1) * ((j + 1).factorial : ℝ) ≤ 35280 := by
    interval_cases j <;> norm_num [Nat.factorial]
  have hS0 : 0 ≤ s ^ (3 : ℝ) := Real.rpow_nonneg hs.le _
  rw [eulerT_sdS_comp h hh j hj6 s hs, abs_mul]
  calc |(-1 / 2 : ℝ) ^ j| * |eulerT^[j] h r|
      ≤ 1 * |eulerT^[j] h r| := mul_le_mul_of_nonneg_right hpow1 (abs_nonneg _)
    _ = |eulerT^[j] h r| := one_mul _
    _ ≤ ((j : ℝ) + 1) * ((j + 1).factorial : ℝ) * B * r ^ (-(6 : ℝ)) := hFb
    _ = ((j : ℝ) + 1) * ((j + 1).factorial : ℝ) * B * s ^ (3 : ℝ) := by rw [hr6]
    _ ≤ 35280 * B * s ^ (3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcomb hB) hS0

/-- Bound `s ^ (-(5 / 2)) * s ^ 3 * Real.exp (-as * s) ≤ 1 + as⁻¹` for `as > 0` and `s > 0`. -/
theorem rpow_neg_five_halves_mul_s3_exp_le {as s : ℝ} (has : 0 < as) (hs : 0 < s) :
    s ^ (-(5 / 2 : ℝ)) * s ^ (3 : ℝ) * Real.exp (-as * s) ≤ 1 + as⁻¹ := by
  have hpow : s ^ (-(5 / 2 : ℝ)) * s ^ (3 : ℝ) = Real.sqrt s := by
    rw [← Real.rpow_add hs, Real.sqrt_eq_rpow]
    congr 1
    norm_num
  rw [hpow]
  by_cases hs1 : s ≤ 1
  · have h1 : Real.sqrt s ≤ 1 := by simpa using Real.sqrt_le_sqrt hs1
    have h2 : Real.exp (-as * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    calc Real.sqrt s * Real.exp (-as * s) ≤ 1 * 1 :=
          mul_le_mul h1 h2 (Real.exp_nonneg _) zero_le_one
      _ ≤ 1 + as⁻¹ := by linarith [inv_pos.2 has]
  · have hs1' : 1 < s := lt_of_not_ge hs1
    have hsqrt_le : Real.sqrt s ≤ s := by
      have h1 : 1 ≤ Real.sqrt s := by simpa using Real.sqrt_le_sqrt hs1'.le
      calc Real.sqrt s = 1 * Real.sqrt s := (one_mul _).symm
        _ ≤ Real.sqrt s * Real.sqrt s := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg s)
        _ = s := Real.mul_self_sqrt hs.le
    have hexp : s * Real.exp (-as * s) ≤ as⁻¹ := by
      have hle : as * s ≤ Real.exp (as * s) :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (as * s))
      have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_nonneg (-as * s))
      rw [← Real.exp_add] at hmul
      have h0 : as * s + -as * s = 0 := by ring
      rw [h0, Real.exp_zero, mul_assoc] at hmul
      have hinv := (le_inv_mul_iff₀ has).2 hmul
      linarith
    calc Real.sqrt s * Real.exp (-as * s) ≤ s * Real.exp (-as * s) :=
          mul_le_mul_of_nonneg_right hsqrt_le (Real.exp_nonneg _)
      _ ≤ as⁻¹ := hexp
      _ ≤ 1 + as⁻¹ := by linarith

/-- Short-time (`0 < s < 4 / (5 * ν)`) bound for `NewtonTaylor`, derived from `SigmaIntForm χo`
and `NewtonVRemBound χo`. -/
theorem newtonShort (as : ℝ) (χo χy : ℝ → ℝ) (has : 0 < as)
    (hS : SigmaIntForm χo) (hRem : NewtonVRemBound χo) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c ν ε μ : ℝ), LHyp c ν ε μ χo χy →
        ∀ M : Chart → Mat3, OldThinFinite c ν M →
          ∀ s : ℝ, 0 < s → s < 4 / (5 * ν) →
            affTerm as 6 (Lpt c ν ε μ χo χy M - ellMuGen c ν ε μ χo M • aMuFun μ) s ≤
              C * ε ^ 3 * oldN1w c ν χo M := by
  obtain ⟨CRem, hCRem0, hCRem⟩ := hRem
  set Cmax : ℝ := ∑ m ∈ Finset.range 8, CRem m with hCmax_def
  have hCmax0 : 0 ≤ Cmax := Finset.sum_nonneg fun m _ => hCRem0 m
  have hCRem_le : ∀ m : ℕ, m ≤ 7 → CRem m ≤ Cmax := fun m hm =>
    Finset.single_le_sum (fun k _ => hCRem0 k) (Finset.mem_range.2 (by omega))
  refine ⟨7 * 9 * 35280 * (2 * Cmax) * (1 + as⁻¹), by positivity, ?_⟩
  intro c ν ε μ h M hM s hs0 hs1
  -- Step 1: factor out `ε ^ 3`
  have hscale : (Lpt c ν ε μ χo χy M - ellMuGen c ν ε μ χo M • aMuFun μ) =
      (ε ^ 3) • (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ) := by
    funext t
    have hL := Scale.lptScale c ν ε μ χo χy M h.eps_pos t
    have hell : ellMuGen c ν ε μ χo M = ε ^ 3 * ellMuGen c ν 1 μ χo M := by
      unfold ellMuGen
      ring
    simp only [Pi.sub_apply, Pi.smul_apply, hL, hell, smul_sub, mul_smul]
  have haff_scale : affTerm as 6 (Lpt c ν ε μ χo χy M - ellMuGen c ν ε μ χo M • aMuFun μ) s =
      ε ^ 3 * affTerm as 6 (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ) s := by
    unfold affTerm affSum
    rw [hscale]
    have hsum : ∑ i ∈ Finset.range (6 + 1),
        frob (sDerivIter i ((ε ^ 3) • (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ)) s) =
        ε ^ 3 * ∑ i ∈ Finset.range (6 + 1),
          frob (sDerivIter i (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ) s) := by
      have hε3 : 0 ≤ ε ^ 3 := pow_nonneg h.eps_pos.le 3
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsmul : ((ε ^ 3) • (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ)) =
          fun t => (ε ^ 3) • (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ) t := rfl
      rw [hsmul, rj6_sDerivIter_smul, rj6_frob_smul, abs_of_nonneg hε3]
    rw [hsum]
    ring
  rw [haff_scale]
  -- Step 2: bound `Z := newtonVRem c ν μ χo M - newtonVRem c ν (μ + 1) χo M` on `U`
  set Z : Vec3 → Vec3 := newtonVRem c ν μ χo M - newtonVRem c ν (μ + 1) χo M with hZdef
  set B : ℝ := 2 * Cmax * oldN1w c ν χo M with hBdef
  have hN1_0 : 0 ≤ oldN1w c ν χo M := oldN1w_nonneg h.nu_pos h.chiO M
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨hcd0, hb0⟩ := hCRem c ν μ h.c_pos h.nu_pos h.chiO h.mu_pos.le M hM
  obtain ⟨hcd1, hb1⟩ := hCRem c ν (μ + 1) h.c_pos h.nu_pos h.chiO (by linarith [h.mu_pos]) M hM
  have hZcd : ContDiffOn ℝ 7 Z {w | ν * (11 / 12) < eucSq w} := hcd0.sub hcd1
  have hZb : ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
      ‖iteratedFDeriv ℝ m Z w‖ ≤ B * (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m) := by
    intro m hm w hw
    have hUo := NewtonVGeom.isOpen_regU ν
    have hc0 : ContDiffAt ℝ 7 (newtonVRem c ν μ χo M) w := hcd0.contDiffAt (hUo.mem_nhds hw)
    have hc1 : ContDiffAt ℝ 7 (newtonVRem c ν (μ + 1) χo M) w := hcd1.contDiffAt (hUo.mem_nhds hw)
    have hmle : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm
    have hsub : iteratedFDeriv ℝ m Z w =
        iteratedFDeriv ℝ m (newtonVRem c ν μ χo M) w -
          iteratedFDeriv ℝ m (newtonVRem c ν (μ + 1) χo M) w := by
      rw [hZdef]
      exact iteratedFDeriv_sub_apply (hc0.of_le hmle) (hc1.of_le hmle)
    have hp0 : 0 ≤ (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hm0 := (hb0 m hm w hw).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCRem_le m hm) hN1_0) hp0)
    have hm1 := (hb1 m hm w hw).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCRem_le m hm) hN1_0) hp0)
    rw [hsub]
    calc ‖iteratedFDeriv ℝ m (newtonVRem c ν μ χo M) w -
            iteratedFDeriv ℝ m (newtonVRem c ν (μ + 1) χo M) w‖
        ≤ ‖iteratedFDeriv ℝ m (newtonVRem c ν μ χo M) w‖ +
            ‖iteratedFDeriv ℝ m (newtonVRem c ν (μ + 1) χo M) w‖ := norm_sub_le _ _
      _ ≤ Cmax * oldN1w c ν χo M * (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m) +
            Cmax * oldN1w c ν χo M * (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m) := add_le_add hm0 hm1
      _ = B * (Real.sqrt (eucSq w)) ^ (-(5 : ℝ) - m) := by rw [hBdef]; ring
  -- Step 3: Cutoff line functions `h_cut i j` and matrix `A_cut`
  let h_raw : Fin 3 → Fin 3 → ℝ → ℝ :=
    fun i j r => fderiv ℝ Z ![r, 0, 0] (Pi.single j 1) i
  let h_cut : Fin 3 → Fin 3 → ℝ → ℝ :=
    fun i j r => chiYr ν 1 χy r * h_raw i j r
  let A_cut : ℝ → Mat3 :=
    fun t => if 0 < t then (fun i j => h_cut i j ((1 : ℝ)⁻¹ / Real.sqrt t)) else 0
  have hh_cut : ∀ i j : Fin 3, ContDiffOn ℝ 6 (h_cut i j) (Ioi 0) :=
    fun i j => contDiffOn_chiYr_mul_Ioi h.nu_pos h.chiY
      (line_rem_bound h.nu_pos hB0 hZcd hZb i j).1
  have hA_cut_cd : ∀ i j : Fin 3, ContDiffOn ℝ 6 (fun t => A_cut t i j) (Ioi 0) := by
    intro i j
    have hg : ContDiffOn ℝ 6 (fun t : ℝ => (1 : ℝ)⁻¹ / Real.sqrt t) (Ioi 0) := by
      intro x hx
      exact (contDiffAt_const.div (Real.contDiffAt_sqrt (ne_of_gt hx))
        (Real.sqrt_ne_zero'.2 hx)).contDiffWithinAt
    have hmap : MapsTo (fun t : ℝ => (1 : ℝ)⁻¹ / Real.sqrt t) (Ioi 0) (Ioi 0) := by
      intro x hx
      show 0 < (1 : ℝ)⁻¹ / Real.sqrt x
      have := Real.sqrt_pos.2 hx
      positivity
    refine ((hh_cut i j).comp hg hmap).congr fun x hx => ?_
    have hx' : 0 < x := hx
    simp [A_cut, hx']
  -- Step 4: `Lpt - ellMuGen • aMuFun =ᶠ[𝓝 s] A_cut`
  have hA_ev : (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ) =ᶠ[𝓝 s] A_cut := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hs0, hs1⟩] with t ht
    ext i j
    have h1 := lpt_sub_aMu_eq_fderiv_newtonVRem hS h hM ht.1 ht.2 i j
    have hgt : 5 * ν / 4 < ((1 : ℝ)⁻¹ / Real.sqrt t) ^ 2 := by
      rw [inv_one, div_pow, one_pow, Real.sq_sqrt ht.1.le, lt_div_iff₀ ht.1]
      have hν5 : 0 < 5 * ν := by linarith [h.nu_pos]
      have := (lt_div_iff₀ hν5).1 ht.2
      linarith
    have hchi1 : chiYr ν 1 χy ((1 : ℝ)⁻¹ / Real.sqrt t) = 1 :=
      chiYr_one_of_sq_ge h.nu_pos h.chiY hgt.le
    simp only [A_cut, if_pos ht.1, h_cut, hchi1, one_mul, h_raw, hZdef]
    exact h1
  -- Step 5: Bound each `sDerivIter j` at `s`
  have hj_bound : ∀ j ∈ Finset.range 7,
      frob (sDerivIter j (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ) s) ≤
        9 * 35280 * B * s ^ (3 : ℝ) := by
    intro j hj
    have hj6 : j ≤ 6 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [(sDerivIter_congr_nhds j hA_ev).eq_of_nhds]
    refine (sdMat A_cut hA_cut_cd s hs0 j hj6).trans ?_
    have hentry : ∀ i i' : Fin 3,
        |sDerivIterS j (fun t => A_cut t i i') s| ≤ 35280 * B * s ^ (3 : ℝ) := by
      intro i i'
      have hkey : (fun t => A_cut t i i') =
          (fun t => if 0 < t then h_cut i i' ((1 : ℝ)⁻¹ / Real.sqrt t) else 0) := by
        funext t; by_cases ht : 0 < t <;> simp [A_cut, ht]
      rw [hkey]
      refine euler_pointwise_s3 hB0 (hh_cut i i') hs0 (fun k hk => ?_) j hj6
      set r := (1 : ℝ)⁻¹ / Real.sqrt s with hrdef
      have hr2 : 5 * ν / 4 < r ^ 2 := by
        rw [hrdef, inv_one, div_pow, one_pow, Real.sq_sqrt hs0.le, lt_div_iff₀ hs0]
        have hν5 : 0 < 5 * ν := by linarith [h.nu_pos]
        have := (lt_div_iff₀ hν5).1 hs1
        linarith
      have hopen_r : IsOpen {u : ℝ | 5 * ν / 4 < u ^ 2} :=
        isOpen_lt continuous_const (by fun_prop)
      have hev_r : h_cut i i' =ᶠ[𝓝 r] h_raw i i' := by
        filter_upwards [hopen_r.mem_nhds hr2] with u hu
        simp [h_cut, chiYr_one_of_sq_ge h.nu_pos h.chiY (le_of_lt hu)]
      rw [hev_r.iteratedDeriv_eq k]
      have hr_gt : Real.sqrt (ν * (11 / 12)) < r := by
        have hν0 : 0 ≤ ν * (11 / 12) := by linarith [h.nu_pos]
        have hsq : (Real.sqrt (ν * (11 / 12))) ^ 2 < r ^ 2 := by
          rw [Real.sq_sqrt hν0]
          linarith [h.nu_pos]
        have hr_pos : 0 < r := by
          have := Real.sqrt_pos.2 hs0
          positivity
        exact lt_of_pow_lt_pow_left₀ 2 hr_pos.le hsq
      exact (line_rem_bound h.nu_pos hB0 hZcd hZb i i').2 k hk r hr_gt
    calc ∑ i : Fin 3, ∑ i' : Fin 3, |sDerivIterS j (fun t => A_cut t i i') s|
        ≤ ∑ _i : Fin 3, ∑ _i' : Fin 3, 35280 * B * s ^ (3 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => hentry i i'
      _ = 9 * 35280 * B * s ^ (3 : ℝ) := by simp; ring
  -- Step 6: Assemble `affTerm` bound
  have hsum_le : ∑ j ∈ Finset.range 7,
      frob (sDerivIter j (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ) s) ≤
        7 * (9 * 35280 * B) * s ^ (3 : ℝ) := by
    calc ∑ j ∈ Finset.range 7,
          frob (sDerivIter j (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ) s)
        ≤ ∑ _j ∈ Finset.range 7, 9 * 35280 * B * s ^ (3 : ℝ) :=
          Finset.sum_le_sum hj_bound
      _ = 7 * (9 * 35280 * B) * s ^ (3 : ℝ) := by simp; ring
  have haff_1 : affTerm as 6 (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ) s ≤
      7 * 9 * 35280 * (2 * Cmax) * (1 + as⁻¹) * oldN1w c ν χo M := by
    unfold affTerm affSum
    have hfac0 : 0 ≤ Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) :=
      mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hs0.le _)
    calc Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) *
          ∑ j ∈ Finset.range (6 + 1),
            frob (sDerivIter j (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ) s)
        ≤ Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) * (7 * (9 * 35280 * B) * s ^ (3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum_le hfac0
      _ = (7 * 9 * 35280 * B) * (s ^ (-(5 / 2 : ℝ)) * s ^ (3 : ℝ) * Real.exp (-as * s)) := by
          ring
      _ ≤ (7 * 9 * 35280 * B) * (1 + as⁻¹) :=
          mul_le_mul_of_nonneg_left (rpow_neg_five_halves_mul_s3_exp_le has hs0) (by positivity)
      _ = 7 * 9 * 35280 * (2 * Cmax) * (1 + as⁻¹) * oldN1w c ν χo M := by
          rw [hBdef]; ring
  have hε3_0 : 0 ≤ ε ^ 3 := pow_nonneg h.eps_pos.le 3
  calc ε ^ 3 * affTerm as 6 (Lpt c ν 1 μ χo χy M - ellMuGen c ν 1 μ χo M • aMuFun μ) s
      ≤ ε ^ 3 * (7 * 9 * 35280 * (2 * Cmax) * (1 + as⁻¹) * oldN1w c ν χo M) :=
        mul_le_mul_of_nonneg_left haff_1 hε3_0
    _ = 7 * 9 * 35280 * (2 * Cmax) * (1 + as⁻¹) * ε ^ 3 * oldN1w c ν χo M := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
