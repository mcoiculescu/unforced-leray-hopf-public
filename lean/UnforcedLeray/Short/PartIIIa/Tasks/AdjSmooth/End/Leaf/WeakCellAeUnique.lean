import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_3_3

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The open strip `(-c/2, c/2) × ℝ`, the interior of the cell. -/
def wuStrip (c : ℝ) : Set (ℝ × ℝ) := Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)

theorem wuStrip_subset_cell (c : ℝ) : wuStrip c ⊆ B0579.cell c :=
  Set.prod_mono Ioo_subset_Ico_self (subset_refl _)

/-- Periodization in `x₁` of a smooth function vanishing when `|y₁| > A` (with `A < c/2`) or
`|y₂| > R`: the finite-in-each-region sum `Σ_n θ(x₁ + n c, x₂)` is a cylinder test which equals `θ`
on the cell. -/
theorem wkPeriodize {c : ℝ} (hc : 0 < c) {θ : ℝ × ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {A R : ℝ}
    (hA : A < c / 2) (hv : ∀ y : ℝ × ℝ, (A < |y.1| ∨ R < |y.2|) → θ y = 0) :
    ∃ Θ : ℝ × ℝ → ℝ, B0579.IsCylTest c Θ ∧ ∀ x ∈ B0579.cell c, Θ x = θ x := by
  have hloc : ∀ x0 : ℝ × ℝ, ContDiffAt ℝ ∞
      (fun x : ℝ × ℝ => ∑ᶠ n : ℤ, θ (x.1 + (n : ℝ) * c, x.2)) x0 := by
    intro x0
    set M : ℝ := |x0.1| + 1 with hM
    set N : ℕ := ⌈(A + M) / c⌉₊ with hN
    have hnb : {x : ℝ × ℝ | |x.1| < M} ∈ 𝓝 x0 :=
      IsOpen.mem_nhds (isOpen_lt continuous_fst.abs continuous_const)
        (show |x0.1| < M by rw [hM]; linarith)
    have heq : (fun x : ℝ × ℝ => ∑ᶠ n : ℤ, θ (x.1 + (n : ℝ) * c, x.2)) =ᶠ[𝓝 x0]
        (fun x : ℝ × ℝ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), θ (x.1 + (n : ℝ) * c, x.2)) := by
      filter_upwards [hnb] with x hx
      have hx' : |x.1| < M := hx
      apply finsum_eq_sum_of_support_subset
      intro n hn
      have hne : θ (x.1 + (n : ℝ) * c, x.2) ≠ 0 := hn
      have hA' : |x.1 + (n : ℝ) * c| ≤ A := by
        by_contra hcon
        exact hne (hv (x.1 + (n : ℝ) * c, x.2) (Or.inl (not_le.1 hcon)))
      obtain ⟨p1, p2⟩ := abs_le.1 hA'
      obtain ⟨q1, q2⟩ := abs_lt.1 hx'
      have h1 : |(n : ℝ) * c| ≤ A + M := abs_le.2 ⟨by linarith, by linarith⟩
      rw [abs_mul, abs_of_pos hc] at h1
      have h2 : |(n : ℝ)| ≤ (N : ℝ) := by
        have h3 : |(n : ℝ)| ≤ (A + M) / c := by
          rw [le_div_iff₀ hc]; linarith
        exact h3.trans (Nat.le_ceil _)
      obtain ⟨l1, l2⟩ := abs_le.1 h2
      have hl : -(N : ℤ) ≤ n := by exact_mod_cast l1
      have hr : n ≤ (N : ℤ) := by exact_mod_cast l2
      exact Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨hl, hr⟩)
    have hsum : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        θ (x.1 + (n : ℝ) * c, x.2)) := by
      apply ContDiff.sum
      intro n _
      exact hθ.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
    exact hsum.contDiffAt.congr_of_eventuallyEq heq
  refine ⟨fun x => ∑ᶠ n : ℤ, θ (x.1 + (n : ℝ) * c, x.2),
    ⟨contDiff_iff_contDiffAt.2 hloc, ?_, ?_⟩, ?_⟩
  · intro x
    show ∑ᶠ n : ℤ, θ ((x.1 + c) + (n : ℝ) * c, x.2) = ∑ᶠ n : ℤ, θ (x.1 + (n : ℝ) * c, x.2)
    have e1 : ∀ n : ℤ, θ ((x.1 + c) + (n : ℝ) * c, x.2) =
        (fun m : ℤ => θ (x.1 + (m : ℝ) * c, x.2)) (Equiv.addRight (1 : ℤ) n) := by
      intro n
      show θ ((x.1 + c) + (n : ℝ) * c, x.2) = θ (x.1 + ((n + 1 : ℤ) : ℝ) * c, x.2)
      congr 1
      exact Prod.ext (by push_cast; ring) rfl
    rw [finsum_congr e1]
    exact finsum_comp_equiv (f := fun m : ℤ => θ (x.1 + (m : ℝ) * c, x.2)) (Equiv.addRight (1 : ℤ))
  · refine ⟨R, fun x hx => ?_⟩
    have h0 : ∀ n : ℤ, θ (x.1 + (n : ℝ) * c, x.2) = 0 := fun n => hv _ (Or.inr hx)
    show ∑ᶠ n : ℤ, θ (x.1 + (n : ℝ) * c, x.2) = 0
    simp only [h0, finsum_zero]
  · intro x hx
    have hxa : |x.1| ≤ c / 2 := abs_le.2 ⟨by linarith [hx.1.1], le_of_lt hx.1.2⟩
    have hzero : ∀ n : ℤ, n ≠ 0 → θ (x.1 + (n : ℝ) * c, x.2) = 0 := by
      intro n hn
      apply hv
      left
      show A < |x.1 + (n : ℝ) * c|
      by_contra hcon
      push_neg at hcon
      obtain ⟨p1, p2⟩ := abs_le.1 hcon
      have hxa' := abs_le.1 hxa
      rcases lt_or_gt_of_ne hn with hn' | hn'
      · have hn2 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
        have h3 : (n : ℝ) * c ≤ (-1) * c := mul_le_mul_of_nonneg_right hn2 hc.le
        linarith [hxa'.1, hxa'.2]
      · have hn2 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have h3 : 1 * c ≤ (n : ℝ) * c := mul_le_mul_of_nonneg_right hn2 hc.le
        linarith [hxa'.1, hxa'.2]
    show ∑ᶠ n : ℤ, θ (x.1 + (n : ℝ) * c, x.2) = θ x
    refine (finsum_eq_single (fun n : ℤ => θ (x.1 + (n : ℝ) * c, x.2)) 0
      (fun n hn => hzero n hn)).trans ?_
    simp

/-- A compact set inside the open strip lies in `|y₁| ≤ A < c/2`, `|y₂| ≤ R`. -/
theorem wkBounds {c : ℝ} (hc : 0 < c) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ wuStrip c) :
    ∃ A R : ℝ, A < c / 2 ∧ ∀ y ∈ K, |y.1| ≤ A ∧ |y.2| ≤ R := by
  rcases K.eq_empty_or_nonempty with hempty | hne
  · exact ⟨0, 0, by linarith, fun y hy => by simp [hempty] at hy⟩
  · obtain ⟨p, hp, hpmax⟩ := hK.exists_isMaxOn hne (continuous_fst.abs.continuousOn)
    obtain ⟨q, hq, hqmax⟩ := hK.exists_isMaxOn hne (continuous_snd.abs.continuousOn)
    refine ⟨|p.1|, |q.2|, ?_, fun y hy => ⟨isMaxOn_iff.1 hpmax y hy, isMaxOn_iff.1 hqmax y hy⟩⟩
    exact abs_lt.2 (hKU hp).1

/-- A smooth bump, equal to `1` at a point of the open strip, supported in a box inside the
strip. -/
theorem wkBump {c : ℝ} {x : ℝ × ℝ} (hx : x ∈ wuStrip c) :
    ∃ θ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ θ ∧ ∃ A R : ℝ, A < c / 2 ∧
      (∀ y : ℝ × ℝ, (A < |y.1| ∨ R < |y.2|) → θ y = 0) ∧ θ x = 1 := by
  have h1 : |x.1| < c / 2 := abs_lt.2 hx.1
  set A0 : ℝ := (|x.1| + c / 2) / 2 with hA0
  set R0 : ℝ := |x.2| + 1 with hR0
  have hA0c : A0 < c / 2 := by rw [hA0]; linarith
  have hxA : |x.1| < A0 := by rw [hA0]; linarith
  have hxR : |x.2| < R0 := by rw [hR0]; linarith
  have hs : Ioo (-A0) A0 ×ˢ Ioo (-R0) R0 ∈ 𝓝 x := by
    apply (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
    exact ⟨abs_lt.1 hxA, abs_lt.1 hxR⟩
  obtain ⟨θ, hsub, -, hsm, -, hx1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hs
  refine ⟨θ, hsm, A0, R0, hA0c, fun y hy => ?_, hx1⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hyt
  have hys := hsub hyt
  rcases hy with h | h
  · have := abs_lt.2 hys.1
    linarith
  · have := abs_lt.2 hys.2
    linarith

theorem weakCellAeUnique : UnforcedLeray.Short.IIIa.WeakCellAeUnique := by
  intro c j φ g₁ g₂ h1 h2
  obtain ⟨hint1, heq1⟩ := h1
  obtain ⟨hint2, heq2⟩ := h2
  rcases le_or_gt c 0 with hc | hc
  · have hempty : B0579.cell c = ∅ := by
      unfold B0579.cell
      rw [Set.Ico_eq_empty_of_le (by linarith : c / 2 ≤ -(c / 2)), Set.empty_prod]
    rw [hempty, Measure.restrict_empty]
    simp only [EventuallyEq, ae_zero, eventually_bot]
  · have hdiff : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
        ∫ x in B0579.cell c, (g₁ x - g₂ x) * ((ψ x : ℝ) : ℂ) = 0 := by
      intro ψ hψ
      have e1 := heq1 ψ hψ
      have e2 := heq2 ψ hψ
      have i1 := (hint1 ψ hψ).2
      have i2 := (hint2 ψ hψ).2
      simp only [sub_mul]
      rw [integral_sub i1 i2]
      linear_combination e1 - e2
    have hloc : LocallyIntegrableOn (fun x => g₁ x - g₂ x) (wuStrip c) := by
      intro x hx
      obtain ⟨θ, hθ, A, R, hA, hv, hθx⟩ := wkBump hx
      obtain ⟨Θ, hΘ, hΘeq⟩ := wkPeriodize hc hθ hA hv
      have hxc : x ∈ B0579.cell c := wuStrip_subset_cell c hx
      have hhalf : (1 / 2 : ℝ) < Θ x := by
        rw [hΘeq x hxc, hθx]; norm_num
      have hev : {y : ℝ × ℝ | (1 / 2 : ℝ) < Θ y} ∈ 𝓝 x :=
        (hΘ.continuous.tendsto x).eventually (lt_mem_nhds hhalf)
      unfold IntegrableAtFilter
      refine ⟨wuStrip c ∩ {y : ℝ × ℝ | (1 / 2 : ℝ) < Θ y}, inter_mem_nhdsWithin _ hev, ?_⟩
      have hTcell : wuStrip c ∩ {y : ℝ × ℝ | (1 / 2 : ℝ) < Θ y} ⊆ B0579.cell c :=
        fun y hy => wuStrip_subset_cell c hy.1
      have hTm : MeasurableSet (wuStrip c ∩ {y : ℝ × ℝ | (1 / 2 : ℝ) < Θ y}) :=
        (isOpen_Ioo.prod isOpen_univ).measurableSet.inter
          (isOpen_lt continuous_const hΘ.continuous).measurableSet
      have hG : IntegrableOn (fun y => g₁ y * ((Θ y : ℝ) : ℂ) - g₂ y * ((Θ y : ℝ) : ℂ))
          (B0579.cell c) :=
        (hint1 Θ hΘ).2.sub (hint2 Θ hΘ).2
      have hk : Continuous (fun y : ℝ × ℝ => (1 / max (Θ y) (1 / 2) : ℝ)) :=
        continuous_const.div (hΘ.continuous.max continuous_const)
          (fun y => ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_right _ _)))
      have hkb : ∀ᵐ y ∂(volume.restrict (B0579.cell c)),
          ‖((1 / max (Θ y) (1 / 2) : ℝ) : ℂ)‖ ≤ 2 :=
        Filter.Eventually.of_forall fun y => by
          have hpos : (0 : ℝ) < max (Θ y) (1 / 2) :=
            lt_of_lt_of_le (by norm_num) (le_max_right _ _)
          rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt (div_pos one_pos hpos)),
            div_le_iff₀ hpos]
          linarith [le_max_right (Θ y) (1 / 2)]
      have hK : IntegrableOn (fun y => ((1 / max (Θ y) (1 / 2) : ℝ) : ℂ) *
          (g₁ y * ((Θ y : ℝ) : ℂ) - g₂ y * ((Θ y : ℝ) : ℂ))) (B0579.cell c) :=
        Integrable.bdd_mul hG (Complex.continuous_ofReal.comp hk).aestronglyMeasurable hkb
      refine (hK.mono_set hTcell).congr_fun ?_ hTm
      intro y hy
      have hΘy : (1 / 2 : ℝ) < Θ y := hy.2
      have hmax : max (Θ y) (1 / 2) = Θ y := max_eq_left hΘy.le
      have hne : ((Θ y : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.2 (ne_of_gt (lt_trans (by norm_num) hΘy))
      show ((1 / max (Θ y) (1 / 2) : ℝ) : ℂ) *
        (g₁ y * ((Θ y : ℝ) : ℂ) - g₂ y * ((Θ y : ℝ) : ℂ)) = g₁ y - g₂ y
      rw [hmax]
      push_cast
      field_simp
    have htest : ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
        tsupport g ⊆ wuStrip c →
        ∫ x, g x • (g₁ x - g₂ x) ∂(volume : Measure (ℝ × ℝ)) = 0 := by
      intro g hg hcpt hsub
      obtain ⟨A, R, hA, hbd⟩ := wkBounds hc hcpt.isCompact hsub
      have hv : ∀ y : ℝ × ℝ, (A < |y.1| ∨ R < |y.2|) → g y = 0 := by
        intro y hy
        by_contra hne
        obtain ⟨b1, b2⟩ := hbd y (subset_tsupport g (Function.mem_support.2 hne))
        rcases hy with h | h <;> linarith
      obtain ⟨Θ, hΘ, hΘeq⟩ := wkPeriodize hc hg hA hv
      have hout : ∀ x ∉ B0579.cell c, g x • (g₁ x - g₂ x) = 0 := by
        intro x hx
        have hxn : x ∉ tsupport g := fun h => hx (wuStrip_subset_cell c (hsub h))
        rw [image_eq_zero_of_notMem_tsupport hxn, zero_smul]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B0579.cell c) hout]
      have e1 : ∫ x in B0579.cell c, g x • (g₁ x - g₂ x) =
          ∫ x in B0579.cell c, (g₁ x - g₂ x) * ((Θ x : ℝ) : ℂ) :=
        setIntegral_congr_fun (B0579.measurableSet_cell c) (fun x hx => by
          simp only [hΘeq x hx, Complex.real_smul]
          ring)
      rw [e1]
      exact hdiff Θ hΘ
    have hopen : IsOpen (wuStrip c) := isOpen_Ioo.prod isOpen_univ
    have hfund : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), x ∈ wuStrip c → g₁ x - g₂ x = 0 :=
      hopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc htest
    have hline : volume {x : ℝ × ℝ | x.1 = -(c / 2)} = 0 := by
      have e : {x : ℝ × ℝ | x.1 = -(c / 2)} = ({-(c / 2)} : Set ℝ) ×ˢ (univ : Set ℝ) := by
        ext x
        simp
      rw [e, Measure.volume_eq_prod, Measure.prod_prod]
      simp
    have hnull : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), x.1 ≠ -(c / 2) := by
      rw [ae_iff]
      simpa using hline
    show ∀ᵐ x ∂(volume.restrict (B0579.cell c)), g₁ x = g₂ x
    rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
    filter_upwards [hfund, hnull] with x hx1 hx2 hxc
    have hxU : x ∈ wuStrip c :=
      ⟨⟨lt_of_le_of_ne hxc.1.1 (Ne.symm hx2), hxc.1.2⟩, mem_univ _⟩
    exact sub_eq_zero.1 (hx1 hxU)

end UnforcedLeray.Short.IIIa
