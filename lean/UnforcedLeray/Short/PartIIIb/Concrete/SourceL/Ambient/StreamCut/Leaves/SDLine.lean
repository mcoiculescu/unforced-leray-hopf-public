import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_5

/-!
# Part III-b, task `PartIII-b:C/srcL/9/5/5/1`: line restriction `SDLine` (source 4917-4937)

Along the axis line `L t = t • e₀` (so `![t,0,0] = L t`, `cylR (L r) = r` for `r > 0`), the entry
`h(r) = fderiv X (L r) e_j i = Φ (fderiv X (L r))` with the continuous linear functional
`Φ A = A e_j i` (`‖Φ‖ ≤ 1`). On the open set `U = {cylR > 0}` the composition formula
`ContinuousLinearMap.iteratedFDerivWithin_comp_right` gives
`‖D^k h(r)‖ ≤ ‖D^k (fderiv X)(L r)‖ ≤ ‖D^{k+1} X(L r)‖ ≤ K r^{-5-k}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sdLine_cylR_pos (t : ℝ) (ht : 0 < t) : cylR ![t, 0, 0] = t := by
  unfold cylR
  simp [Real.sqrt_sq ht.le]

theorem sdLine : SDLine := by
  unfold SDLine
  intro X K hK hX hb i j
  -- the open set where `X` is smooth with the derivative bounds
  set U : Set Vec3 := {y | 0 < cylR y} with hUdef
  have hcont : Continuous cylR := by
    unfold cylR
    fun_prop
  have hUo : IsOpen U := isOpen_lt continuous_const hcont
  have hXU : ContDiffOn ℝ 7 X U := fun y hy => (hX y hy).contDiffWithinAt
  have hF' : ContDiffOn ℝ 6 (fderiv ℝ X) U := hXU.fderiv_of_isOpen hUo (by norm_num)
  -- the axis line and the functional `A ↦ A e_j i`
  obtain ⟨L, hLapp⟩ : ∃ L : ℝ →L[ℝ] Vec3, ∀ t, L t = t • (Pi.single 0 (1 : ℝ) : Vec3) :=
    ⟨ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (Pi.single 0 (1 : ℝ)),
      fun t => by simp⟩
  have he0 : ‖(Pi.single 0 (1 : ℝ) : Vec3)‖ = 1 := by
    rw [Pi.norm_single, norm_one]
  have hej : ‖(Pi.single j (1 : ℝ) : Vec3)‖ = 1 := by
    rw [Pi.norm_single, norm_one]
  have hLline : ∀ t : ℝ, L t = ![t, 0, 0] := by
    intro t
    rw [hLapp]
    ext k
    fin_cases k <;> simp
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound L zero_le_one fun t => ?_
    rw [hLapp, norm_smul, he0, one_mul, mul_comm]
    simp
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
  -- the composed function
  have hG : ContDiffOn ℝ 6 (fun y => Φ (fderiv ℝ X y)) U :=
    Φ.contDiff.comp_contDiffOn hF'
  have hLmaps : MapsTo L (Ioi 0) U := by
    intro t ht
    show 0 < cylR (L t)
    rw [hLline t, sdLine_cylR_pos t ht]
    exact ht
  have hhc : ContDiffOn ℝ 6 ((fun y => Φ (fderiv ℝ X y)) ∘ L) (Ioi 0) :=
    hG.comp L.contDiff.contDiffOn hLmaps
  have hfun : (fun r : ℝ => fderiv ℝ X ![r, 0, 0] (Pi.single j (1 : ℝ)) i) =
      (fun y => Φ (fderiv ℝ X y)) ∘ L := by
    funext r
    show fderiv ℝ X ![r, 0, 0] (Pi.single j (1 : ℝ)) i = Φ (fderiv ℝ X (L r))
    rw [hΦ, hLline r]
  refine ⟨by rw [hfun]; exact hhc, fun k hk r hr => ?_⟩
  rw [hfun]
  have hLr : L r ∈ U := by
    show 0 < cylR (L r)
    rw [hLline r, sdLine_cylR_pos r hr]
    exact hr
  have hrU : r ∈ L ⁻¹' U := hLr
  -- composition formula on the open preimage
  have hwithin := L.iteratedFDerivWithin_comp_right hG hUo.uniqueDiffOn
    (IsOpen.preimage L.continuous hUo).uniqueDiffOn hLr (i := k) (by exact_mod_cast hk)
  have e1 : iteratedFDerivWithin ℝ k ((fun y => Φ (fderiv ℝ X y)) ∘ L) (L ⁻¹' U) r =
      iteratedFDeriv ℝ k ((fun y => Φ (fderiv ℝ X y)) ∘ L) r :=
    iteratedFDerivWithin_of_isOpen k (IsOpen.preimage L.continuous hUo) hrU
  have e2 : iteratedFDerivWithin ℝ k (fun y => Φ (fderiv ℝ X y)) U (L r) =
      iteratedFDeriv ℝ k (fun y => Φ (fderiv ℝ X y)) (L r) :=
    iteratedFDerivWithin_of_isOpen k hUo hLr
  have hfd : iteratedFDeriv ℝ k ((fun y => Φ (fderiv ℝ X y)) ∘ L) r =
      (iteratedFDeriv ℝ k (fun y => Φ (fderiv ℝ X y)) (L r)).compContinuousLinearMap
        (fun _ => L) := by
    rw [← e1, hwithin, e2]
  -- norm estimates
  have hn1 : ‖iteratedFDeriv ℝ k ((fun y => Φ (fderiv ℝ X y)) ∘ L) r‖ ≤
      ‖iteratedFDeriv ℝ k (fun y => Φ (fderiv ℝ X y)) (L r)‖ := by
    rw [hfd]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hprod : ∏ _i : Fin k, ‖L‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hLn)
    exact mul_le_of_le_one_right (norm_nonneg _) hprod
  have hcontAt : ContDiffAt ℝ 6 (fderiv ℝ X) (L r) :=
    (hX (L r) hLr).fderiv_right (m := 6) (by norm_num)
  have hn2 : ‖iteratedFDeriv ℝ k (fun y => Φ (fderiv ℝ X y)) (L r)‖ ≤
      ‖iteratedFDeriv ℝ k (fderiv ℝ X) (L r)‖ := by
    have := ContinuousLinearMap.norm_iteratedFDeriv_comp_left Φ hcontAt
      (n := k) (by exact_mod_cast hk)
    refine this.trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) hΦn
  have hn3 : ‖iteratedFDeriv ℝ k (fderiv ℝ X) (L r)‖ =
      ‖iteratedFDeriv ℝ (k + 1) X (L r)‖ := norm_iteratedFDeriv_fderiv
  have h4 := hb (k + 1) (by omega) (L r) (show 0 < cylR (L r) from hLr)
  have hc : cylR (L r) = r := by
    rw [hLline r]
    exact sdLine_cylR_pos r hr
  rw [hc] at h4
  have hexp : (-(4 : ℝ) - ((k + 1 : ℕ) : ℝ)) = -(5 : ℝ) - k := by
    push_cast
    ring
  rw [hexp] at h4
  -- from the iterated derivative to the operator norm
  have h5 : |iteratedDeriv k ((fun y => Φ (fderiv ℝ X y)) ∘ L) r| ≤
      ‖iteratedFDeriv ℝ k ((fun y => Φ (fderiv ℝ X y)) ∘ L) r‖ := by
    rw [iteratedDeriv_eq_iteratedFDeriv, ← Real.norm_eq_abs]
    have := (iteratedFDeriv ℝ k ((fun y => Φ (fderiv ℝ X y)) ∘ L) r).le_opNorm
      (fun _ : Fin k => (1 : ℝ))
    simpa using this
  calc |iteratedDeriv k ((fun y => Φ (fderiv ℝ X y)) ∘ L) r|
      ≤ ‖iteratedFDeriv ℝ k ((fun y => Φ (fderiv ℝ X y)) ∘ L) r‖ := h5
    _ ≤ ‖iteratedFDeriv ℝ k (fun y => Φ (fderiv ℝ X y)) (L r)‖ := hn1
    _ ≤ ‖iteratedFDeriv ℝ k (fderiv ℝ X) (L r)‖ := hn2
    _ = ‖iteratedFDeriv ℝ (k + 1) X (L r)‖ := hn3
    _ ≤ K * r ^ (-(5 : ℝ) - k) := h4

end UnforcedLeray.Short.PartIIIb.Concrete
