import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2.HeatKTop
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# `SepGapPointwiseTop` (`PartIII-b:IIIb-D2/3/2/11/2/2/2/4`, source 3604-3621)

Pointwise all-order `sep:kernel` bound at the gap.  Leibniz rule for the product
`(τ,y) ↦ F(y) · G(τ)` with `F` the `y`-derivative of the kernel (`SepKernelBounds`, translated
by `l z`, bounded below by `d` on the gap) and `G` the `τ`-derivative of `T` (periodic in `τ`,
compactly supported in `z`, bounded by compactness on one period).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ### Geometry of `ϱ` -/

theorem gapRho_le_norm (a : Space) : ϱ a ≤ ‖a‖ := by
  unfold ϱ
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  apply Real.sqrt_le_sqrt
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (a 2)]

theorem gapRho_sub_le (a b : Space) : ϱ a ≤ ϱ (a - b) + ϱ b := by
  unfold ϱ
  have h0 : (a - b) 0 = a 0 - b 0 := by simp
  have h1 : (a - b) 1 = a 1 - b 1 := by simp
  rw [h0, h1]
  have hr2 : Real.sqrt ((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2) ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hs2 : Real.sqrt (b 0 ^ 2 + b 1 ^ 2) ^ 2 = b 0 ^ 2 + b 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hr0 := Real.sqrt_nonneg ((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2)
  have hs0 := Real.sqrt_nonneg (b 0 ^ 2 + b 1 ^ 2)
  set r := Real.sqrt ((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2) with hr_def
  set s := Real.sqrt (b 0 ^ 2 + b 1 ^ 2) with hs_def
  have hcs2 : ((a 0 - b 0) * b 0 + (a 1 - b 1) * b 1) ^ 2 ≤ (r * s) ^ 2 := by
    rw [mul_pow, hr2, hs2]
    nlinarith [sq_nonneg ((a 0 - b 0) * b 1 - (a 1 - b 1) * b 0)]
  have hcs : (a 0 - b 0) * b 0 + (a 1 - b 1) * b 1 ≤ r * s := by
    nlinarith [mul_nonneg hr0 hs0]
  rw [show r + s = Real.sqrt ((r + s) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  nlinarith [hr2, hs2, hcs]

theorem gapRho_smul_le (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (z : Space) : ϱ (l • z) ≤ ϱ z := by
  unfold ϱ
  have h0 : (l • z) 0 = l * z 0 := by simp
  have h1 : (l • z) 1 = l * z 1 := by simp
  rw [h0, h1]
  apply Real.sqrt_le_sqrt
  have hl2 : l ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hl2) (add_nonneg (sq_nonneg (z 0)) (sq_nonneg (z 1)))]

theorem gapNorm_ge (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (z y : Space) (d rOut : ℝ)
    (hz : ϱ z ≤ rOut) (hy : rOut + d ≤ ϱ y) : d ≤ ‖y - l • z‖ := by
  have h1 := gapRho_sub_le y (l • z)
  have h2 := gapRho_smul_le l hl0 hl1 z
  have h3 := gapRho_le_norm (y - l • z)
  linarith

/-! ### Derivative bounds -/

/-- The `y`-derivative of the kernel, translated by `w`, at distance `≥ d` from the origin. -/
theorem gapYBound (hK : IIIa.SepKernelBounds) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), 0 < t → ∀ (i j k : Fin 3) (w y : Space) (d : ℝ), 0 < d →
      d ≤ ‖y - w‖ →
      ‖iteratedFDeriv ℝ n (fun u => fderiv ℝ (fun v => IIIa.heatLerayK t i j v) (u - w)
        (coordinateVector k)) y‖ ≤ C * d ^ (-4 - (n : ℝ)) := by
  obtain ⟨C0, hC0⟩ := hK n
  refine ⟨max C0 0, le_max_right _ _, fun t ht i j k w y d hd hdy => ?_⟩
  have hv0 : y - w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdy
    linarith
  have hKs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => IIIa.heatLerayK t i j v) :=
    heatLerayKSmoothTop t ht i j
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (fun v => IIIa.heatLerayK t i j v)) :=
    (contDiff_infty_iff_fderiv.1 hKs).2
  have hcl := norm_iteratedFDeriv_clm_apply_const (c := coordinateVector k) (x := y - w)
    (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) (n := n) hfd.contDiffAt (by exact_mod_cast le_top)
  have hcoord : ‖coordinateVector k‖ = 1 := by
    unfold coordinateVector
    rw [EuclideanSpace.norm_single, norm_one]
  rw [hcoord, one_mul, norm_iteratedFDeriv_fderiv] at hcl
  have e1 : iteratedFDeriv ℝ n (fun u => fderiv ℝ (fun v => IIIa.heatLerayK t i j v) (u - w)
        (coordinateVector k)) y = iteratedFDeriv ℝ n
        (fun v => fderiv ℝ (fun v => IIIa.heatLerayK t i j v) v (coordinateVector k)) (y - w) :=
    iteratedFDeriv_comp_sub (f := fun v => fderiv ℝ (fun v => IIIa.heatLerayK t i j v) v
      (coordinateVector k)) n w y
  rw [e1]
  have hK1 := (hC0 (y - w) hv0 i j).1 t ht
  have hnorm_pos : 0 < ‖y - w‖ := lt_of_lt_of_le hd hdy
  have hexp : (-4 - (n : ℝ)) ≤ 0 := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  have hA : ‖y - w‖ ^ (-4 - (n : ℝ)) ≤ d ^ (-4 - (n : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hd hdy hexp
  have hA0 : 0 ≤ ‖y - w‖ ^ (-4 - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  calc ‖iteratedFDeriv ℝ n (fun v => fderiv ℝ (fun v => IIIa.heatLerayK t i j v) v
        (coordinateVector k)) (y - w)‖
      ≤ ‖iteratedFDeriv ℝ (n + 1) (fun v => IIIa.heatLerayK t i j v) (y - w)‖ := hcl
    _ ≤ C0 * ‖y - w‖ ^ (-4 - (n : ℝ)) := hK1
    _ ≤ max C0 0 * ‖y - w‖ ^ (-4 - (n : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) hA0
    _ ≤ max C0 0 * d ^ (-4 - (n : ℝ)) := mul_le_mul_of_nonneg_left hA (le_max_right _ _)

theorem gapFSmooth (t : ℝ) (ht : 0 < t) (i j k : Fin 3) (w : Space) (c0 : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space =>
      c0 * ((fderiv ℝ (fun v => IIIa.heatLerayK t i j v) (x.2 - w) (coordinateVector k) : ℝ) : ℂ)) := by
  have hKs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => IIIa.heatLerayK t i j v) :=
    heatLerayKSmoothTop t ht i j
  have hK' := (contDiff_infty_iff_fderiv.1 hKs).2
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space =>
      fderiv ℝ (fun v => IIIa.heatLerayK t i j v) (x.2 - w) (coordinateVector k)) :=
    (hK'.comp (contDiff_snd.sub contDiff_const)).clm_apply contDiff_const
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hφ)

theorem gapGSmooth (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ j k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => T x.1 x.2 j k))
    (j k : Fin 3) (c : ℝ) (z : Space) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => ((T (x.1 + c) z j k : ℝ) : ℂ)) := by
  have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => (x.1 + c, z)) :=
    (contDiff_fst.add contDiff_const).prodMk contDiff_const
  exact Complex.ofRealCLM.contDiff.comp ((hT j k).comp h4)

/-! ### Composition and sums -/

theorem gapProjBound {E E' F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] E') (hL : ‖L‖ ≤ 1) (f : E' → F)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (x : E) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun x => f (L x)) x‖ ≤ ‖iteratedFDeriv ℝ m f (L x)‖ := by
  have hm : ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hcr := ContinuousLinearMap.iteratedFDeriv_comp_right L hf x (i := m) hm
  show ‖iteratedFDeriv ℝ m (f ∘ L) x‖ ≤ _
  rw [hcr]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h3 : (∏ i : Fin m, ‖(fun _ : Fin m => L) i‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)
  exact (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans (mul_one _).le

theorem gapFBound (G : Space → ℝ) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (c0 : ℂ)
    (F' : ℝ × Space → ℂ) (w : Space) (hF' : ∀ x' : ℝ × Space, F' x' = c0 * ((G (x'.2 - w) : ℝ) : ℂ))
    (d C : ℝ) (m : ℕ)
    (hC : ∀ y : Space, d ≤ ‖y - w‖ →
      ‖iteratedFDeriv ℝ m (fun u => G (u - w)) y‖ ≤ C * d ^ (-4 - (m : ℝ)))
    (x : ℝ × Space) (hx : d ≤ ‖x.2 - w‖) :
    ‖iteratedFDeriv ℝ m F' x‖ ≤ ‖c0‖ * (C * d ^ (-4 - (m : ℝ))) := by
  have hm : ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hGw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Space => G (u - w)) :=
    hG.comp (contDiff_id.sub contDiff_const)
  have hφs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x' : ℝ × Space => G (x'.2 - w)) :=
    hGw.comp contDiff_snd
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x' : ℝ × Space => ((G (x'.2 - w) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφs
  have hFeq : F' = c0 • (fun x' : ℝ × Space => ((G (x'.2 - w) : ℝ) : ℂ)) := by
    funext x'
    rw [hF']
    simp [smul_eq_mul]
  have hψm : ContDiffAt ℝ (m : WithTop ℕ∞) (fun x' : ℝ × Space => ((G (x'.2 - w) : ℝ) : ℂ)) x :=
    hψ.contDiffAt.of_le hm
  rw [hFeq, iteratedFDeriv_const_smul_apply hψm, norm_smul]
  have h1 : ‖iteratedFDeriv ℝ m (fun x' : ℝ × Space => ((G (x'.2 - w) : ℝ) : ℂ)) x‖ ≤
      ‖iteratedFDeriv ℝ m (fun x' : ℝ × Space => G (x'.2 - w)) x‖ := by
    have := ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.ofRealCLM
      (hφs.contDiffAt (x := x)) hm
    rw [Complex.ofRealCLM_norm, one_mul] at this
    exact this
  have h2 : ‖iteratedFDeriv ℝ m (fun x' : ℝ × Space => G (x'.2 - w)) x‖ ≤
      ‖iteratedFDeriv ℝ m (fun u => G (u - w)) x.2‖ :=
    gapProjBound (ContinuousLinearMap.snd ℝ ℝ Space) (ContinuousLinearMap.norm_snd_le ℝ ℝ Space)
      (fun u => G (u - w)) hGw x m
  have h3 := hC x.2 hx
  exact mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) (norm_nonneg _)

theorem normIter_finsum {ι : Type} (s : Finset ι) (h : ι → ℝ × Space → ℂ)
    (hh : ∀ p ∈ s, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h p)) (n : ℕ) (x : ℝ × Space) :
    ‖iteratedFDeriv ℝ n (fun y => ∑ p ∈ s, h p y) x‖ ≤ ∑ p ∈ s, ‖iteratedFDeriv ℝ n (h p) x‖ := by
  have hle : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  rw [iteratedFDeriv_sum (𝕜 := ℝ) (i := n) (fun p hp => (hh p hp).of_le hle), Finset.sum_apply]
  exact norm_sum_le _ _

/-! ### The τ-derivative bound on one period -/

theorem gapTauBound (P : ℝ) (hP : 0 < P) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hper : ∀ τ z, T (τ + P) z = T τ z)
    (hT : ∀ j k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => T x.1 x.2 j k))
    (Z : ℝ) (j k : Fin 3) (a : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (c : ℝ) (z : Space), ‖z‖ ≤ Z → ∀ x : ℝ × Space,
      ‖iteratedFDeriv ℝ a (fun x : ℝ × Space => ((T (x.1 + c) z j k : ℝ) : ℂ)) x‖ ≤ M := by
  have hm : ((a : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  set S : ℝ × Space → ℝ := fun w => T w.1 w.2 j k with hSdef
  have hSs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S := hT j k
  have hperS : ∀ w : ℝ × Space, S (w + (P, 0)) = S w := by
    intro w
    simp only [hSdef, Prod.fst_add, Prod.snd_add, add_zero]
    rw [hper]
  have hcomp : ∀ w : ℝ × Space, iteratedFDeriv ℝ a S (w + (P, 0)) = iteratedFDeriv ℝ a S w := by
    intro w
    have h : iteratedFDeriv ℝ a (fun z => S (z + (P, 0))) w = iteratedFDeriv ℝ a S (w + (P, 0)) :=
      iteratedFDeriv_comp_add_right a (P, 0) w
    have h2 : (fun z => S (z + (P, 0))) = S := funext hperS
    rw [h2] at h
    exact h.symm
  have hpe : ∀ z : Space, Function.Periodic (fun s : ℝ => ‖iteratedFDeriv ℝ a S (s, z)‖) P := by
    intro z s
    have e : ((s + P, z) : ℝ × Space) = (s, z) + (P, 0) := by ext <;> simp
    simp only [e, hcomp]
  have hcont : Continuous (fun w : ℝ × Space => ‖iteratedFDeriv ℝ a S w‖) :=
    (hSs.continuous_iteratedFDeriv hm).norm
  obtain ⟨M0, hM0⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) Z)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max M0 0, le_max_right _ _, fun c z hz x => ?_⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ × Space →L[ℝ] ℝ × Space,
      L = (ContinuousLinearMap.inl ℝ ℝ Space).comp (ContinuousLinearMap.fst ℝ ℝ Space) := ⟨_, rfl⟩
  have hL : ‖L‖ ≤ 1 := by
    rw [hLdef]
    calc ‖(ContinuousLinearMap.inl ℝ ℝ Space).comp (ContinuousLinearMap.fst ℝ ℝ Space)‖
        ≤ ‖ContinuousLinearMap.inl ℝ ℝ Space‖ * ‖ContinuousLinearMap.fst ℝ ℝ Space‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul (ContinuousLinearMap.norm_inl_le_one ℝ ℝ Space)
          (ContinuousLinearMap.norm_fst_le ℝ ℝ Space) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hLx : ∀ x' : ℝ × Space, L x' + (c, z) = (x'.1 + c, z) := by
    intro x'
    rw [hLdef]
    ext <;> simp
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ × Space => S (w + (c, z))) :=
    hSs.comp (contDiff_id.add contDiff_const)
  have hfunL : (fun x' : ℝ × Space => S (x'.1 + c, z)) = (fun w => S (w + (c, z))) ∘ L := by
    funext x'
    simp only [Function.comp_apply]
    rw [hLx]
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x' : ℝ × Space => S (x'.1 + c, z)) :=
    hSs.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_const)
  have hbound1 : ‖iteratedFDeriv ℝ a (fun x' : ℝ × Space => S (x'.1 + c, z)) x‖ ≤
      ‖iteratedFDeriv ℝ a S (x.1 + c, z)‖ := by
    rw [hfunL]
    have hcr := ContinuousLinearMap.iteratedFDeriv_comp_right L hh x (i := a) hm
    rw [hcr]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hprod : (∏ _i : Fin a, ‖(fun _ : Fin a => L) _i‖) ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)
    have hiter : iteratedFDeriv ℝ a (fun w : ℝ × Space => S (w + (c, z))) (L x) =
        iteratedFDeriv ℝ a S (L x + (c, z)) :=
      iteratedFDeriv_comp_add_right a (c, z) (L x)
    rw [hiter, hLx]
    exact (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans (mul_one _).le
  have hbound2 : ‖iteratedFDeriv ℝ a S (x.1 + c, z)‖ ≤ M0 := by
    obtain ⟨s0, hs0, heq⟩ := (hpe z).exists_mem_Ico₀ hP (x.1 + c)
    have hmem : (s0, z) ∈ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) Z :=
      ⟨Ico_subset_Icc_self hs0, by simpa using hz⟩
    have hb := hM0 (s0, z) hmem
    rw [norm_norm] at hb
    calc ‖iteratedFDeriv ℝ a S (x.1 + c, z)‖ = ‖iteratedFDeriv ℝ a S (s0, z)‖ := heq
      _ ≤ M0 := hb
  have hfun : (fun x' : ℝ × Space => ((T (x'.1 + c) z j k : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun x' : ℝ × Space => S (x'.1 + c, z)) := by
    funext x'
    simp [hSdef]
  calc ‖iteratedFDeriv ℝ a (fun x' : ℝ × Space => ((T (x'.1 + c) z j k : ℝ) : ℂ)) x‖
      = ‖iteratedFDeriv ℝ a (Complex.ofRealCLM ∘ (fun x' : ℝ × Space => S (x'.1 + c, z))) x‖ := by
        rw [hfun]
    _ ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ a (fun x' : ℝ × Space => S (x'.1 + c, z)) x‖ :=
        ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ (hgs.contDiffAt (x := x)) hm
    _ ≤ 1 * ‖iteratedFDeriv ℝ a (fun x' : ℝ × Space => S (x'.1 + c, z)) x‖ := by
        rw [Complex.ofRealCLM_norm]
    _ ≤ ‖iteratedFDeriv ℝ a S (x.1 + c, z)‖ := by
        rw [one_mul]; exact hbound1
    _ ≤ M0 := hbound2
    _ ≤ max M0 0 := le_max_left _ _

/-! ### Main theorem -/

set_option maxHeartbeats 2000000 in
theorem sepGapPointwiseTop : SepGapPointwiseTop := by
  intro hK ν μ rOut P T hν hμ hr hP hS hT Z hZ i x0 hx0
  have hd0 : 0 < (ϱ x0.2 - rOut) / 2 := by linarith
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = (ϱ x0.2 - rOut) / 2 := ⟨_, rfl⟩
  have hd : 0 < d := by rw [hd_def]; exact hd0
  choose Cy hCy0 hCy using gapYBound hK
  choose M hM0 hM using fun (a : ℕ) (j k : Fin 3) =>
    gapTauBound P hP T hS.periodic hT Z j k a
  refine ⟨d, hd, fun n => ?_⟩
  obtain ⟨Cfin, hCfin⟩ : ∃ C : ℝ, C = ∑ p : Fin 3 × Fin 3, ∑ m ∈ Finset.range (n + 1),
      (n.choose m : ℝ) * (Cy m * d ^ (-4 - (m : ℝ))) * M (n - m) p.1 p.2 := ⟨_, rfl⟩
  refine ⟨|2 * Cfin|, abs_nonneg _, fun x hx l hl z => ?_⟩
  have hn : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  by_cases hz : ‖z‖ ≤ Z ∧ ϱ z ≤ rOut
  · obtain ⟨hzZ, hzr⟩ := hz
    have hxball : dist x x0 < d := Metric.mem_ball.mp hx
    rw [dist_eq_norm] at hxball
    have hsnd : ‖x.2 - x0.2‖ ≤ ‖x - x0‖ := by
      rw [← Prod.snd_sub]
      exact norm_snd_le _
    have hxd : ‖x.2 - x0.2‖ < d := lt_of_le_of_lt hsnd hxball
    have hyr : rOut + d ≤ ϱ x.2 := by
      have h1 := gapRho_sub_le x0.2 x.2
      have h2 := gapRho_le_norm (x0.2 - x.2)
      rw [norm_sub_rev] at h2
      linarith
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
        ‖c0‖ * (∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * (Cy m * d ^ (-4 - (m : ℝ))) *
          M (n - m) p.1 p.2) := by
      intro p
      refine (norm_iteratedFDeriv_mul_le (hFs p) (hGs p) x hn).trans ?_
      rw [Finset.mul_sum]
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
      have hX : 0 ≤ Cy m * d ^ (-4 - (m : ℝ)) := mul_nonneg (hCy0 m) (Real.rpow_nonneg hd.le _)
      calc (n.choose m : ℝ) * ‖iteratedFDeriv ℝ m (F p) x‖ * ‖iteratedFDeriv ℝ (n - m) (G p) x‖
          ≤ (n.choose m : ℝ) * (‖c0‖ * (Cy m * d ^ (-4 - (m : ℝ)))) * M (n - m) p.1 p.2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 hC0) h2 (norm_nonneg _)
              (mul_nonneg hC0 (mul_nonneg (norm_nonneg _) hX))
        _ = ‖c0‖ * ((n.choose m : ℝ) * (Cy m * d ^ (-4 - (m : ℝ))) * M (n - m) p.1 p.2) := by ring
    have hsum : ‖iteratedFDeriv ℝ n (fun x' => ∑ p : Fin 3 × Fin 3, F p x' * G p x') x‖ ≤
        ∑ p : Fin 3 × Fin 3, ‖iteratedFDeriv ℝ n (fun y => F p y * G p y) x‖ :=
      normIter_finsum Finset.univ (fun p y => F p y * G p y)
        (fun p _ => (hFs p).mul (hGs p)) n x
    have hc0n : ‖c0‖ = 2 * l ^ (2 * μ.re + 2) := by
      have hre : (2 * μ + 2).re = 2 * μ.re + 2 := by simp
      have h2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
      rw [hc0def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, h2, hre]
    have hq : 0 ≤ l ^ (2 * μ.re + 2) := Real.rpow_nonneg hl.1.le _
    rw [hfunEq, if_pos hzZ, mul_one]
    refine le_trans hsum ?_
    calc ∑ p : Fin 3 × Fin 3, ‖iteratedFDeriv ℝ n (fun y => F p y * G p y) x‖
        ≤ ∑ p : Fin 3 × Fin 3, ‖c0‖ * (∑ m ∈ Finset.range (n + 1),
            (n.choose m : ℝ) * (Cy m * d ^ (-4 - (m : ℝ))) * M (n - m) p.1 p.2) :=
          Finset.sum_le_sum fun p _ => hper p
      _ = ‖c0‖ * Cfin := by rw [hCfin, Finset.mul_sum]
      _ = (2 * Cfin) * l ^ (2 * μ.re + 2) := by rw [hc0n]; ring
      _ ≤ |2 * Cfin| * l ^ (2 * μ.re + 2) := mul_le_mul_of_nonneg_right (le_abs_self _) hq
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
    have hR : 0 ≤ |2 * Cfin| * (l ^ (2 * μ.re + 2) * (if ‖z‖ ≤ Z then 1 else 0)) := by
      apply mul_nonneg (abs_nonneg _)
      apply mul_nonneg (Real.rpow_nonneg hl.1.le _)
      split_ifs <;> norm_num
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      simpa using hR
    · rw [iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]
      exact hR

end UnforcedLeray.Short.PartIIIb.Concrete
