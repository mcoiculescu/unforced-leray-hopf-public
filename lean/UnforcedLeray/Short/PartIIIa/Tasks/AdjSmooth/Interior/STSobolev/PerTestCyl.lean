import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/7/4`: the periodization `perTest` is a cylinder test

Source: `the November 2 reference manuscript` lines 3060-3061.
`perTest c θ x = ∑ᶠ k, θ (x₁ + k c, x₂)` is locally a finite sum (`θ` has compact support), hence
smooth; it is `c`-periodic in `x₁`, vanishes for `|x₂|` large, and commutes with the coordinate
derivatives.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem perTestCyl : UnforcedLeray.Short.IIIa.PerTestCyl := by
  intro c θ hc hθ hθc
  have hK : IsCompact (tsupport θ) := hθc.isCompact
  have hd : Differentiable ℝ θ := hθ.differentiable (by simp)
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (continuous_fst.continuousOn)
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn (continuous_snd.continuousOn)
  -- the sum over `ℤ` is a finite sum on a strip `|x₁ - x₀₁| < 1`
  have hpt : ∀ (g : ℝ × ℝ → ℝ) (x : ℝ × ℝ),
      perTest c g x = ∑ᶠ k : ℤ, g (x + ((k : ℝ) * c, 0)) := by
    intro g x
    unfold perTest
    apply finsum_congr
    intro k
    congr 1
    ext <;> simp
  have loc : ∀ x0 : ℝ × ℝ, ∃ N : ℤ, ∀ g : ℝ × ℝ → ℝ, (∀ y, g y ≠ 0 → y ∈ tsupport θ) →
      ∀ x : ℝ × ℝ, |x.1 - x0.1| < 1 →
        perTest c g x = ∑ k ∈ Finset.Icc (-N) N, g (x + ((k : ℝ) * c, 0)) := by
    intro x0
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = A + |x0.1| + 1 := ⟨_, rfl⟩
    obtain ⟨N, hNdef⟩ : ∃ N : ℤ, N = ⌈S / c⌉ := ⟨_, rfl⟩
    have hNc : S ≤ (N : ℝ) * c := by
      rw [hNdef]
      exact (div_le_iff₀ hc).1 (Int.le_ceil _)
    refine ⟨N, fun g hg x hx => ?_⟩
    have hsub : Function.support (fun k : ℤ => g (x + ((k : ℝ) * c, 0))) ⊆
        ↑(Finset.Icc (-N) N) := by
      intro k hk
      have hmem : x + ((k : ℝ) * c, 0) ∈ tsupport θ := hg _ (Function.mem_support.1 hk)
      have hb : |x.1 + (k : ℝ) * c| ≤ A := by
        have := hA _ hmem
        simpa [Real.norm_eq_abs] using this
      have h1 := abs_le.1 hb
      have h2 := abs_lt.1 hx
      have h3 := le_abs_self x0.1
      have h4 := neg_abs_le x0.1
      have hkc1 : (k : ℝ) * c ≤ (N : ℝ) * c := by linarith [h1.1, h1.2, h2.1, h2.2]
      have hkc2 : -(k : ℝ) * c ≤ (N : ℝ) * c := by linarith [h1.1, h1.2, h2.1, h2.2]
      have hk1 : (k : ℝ) ≤ (N : ℝ) := le_of_mul_le_mul_right hkc1 hc
      have hk2 : -(k : ℝ) ≤ (N : ℝ) := le_of_mul_le_mul_right hkc2 hc
      have hk1' : k ≤ N := by exact_mod_cast hk1
      have hk2' : -k ≤ N := by exact_mod_cast hk2
      exact Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨by omega, hk1'⟩)
    rw [hpt g x]
    exact finsum_eq_sum_of_support_subset _ hsub
  have hθsupp : ∀ y, θ y ≠ 0 → y ∈ tsupport θ := fun y hy => subset_tsupport _ (Function.mem_support.2 hy)
  have hU : ∀ x0 : ℝ × ℝ, ∀ᶠ y in 𝓝 x0, |y.1 - x0.1| < 1 := fun x0 =>
    ((continuous_fst.sub continuous_const).abs.continuousAt).eventually_lt
      (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ => (1 : ℝ)) x0) (by simp)
  -- smoothness
  have hSmooth : ContDiff ℝ ∞ (perTest c θ) := by
    refine contDiff_iff_contDiffAt.2 fun x0 => ?_
    obtain ⟨N, hN⟩ := loc x0
    have hloc : ContDiff ℝ ∞
        (fun y : ℝ × ℝ => ∑ k ∈ Finset.Icc (-N) N, θ (y + ((k : ℝ) * c, 0))) := by
      refine ContDiff.sum fun k _ => ?_
      exact hθ.comp (contDiff_id.add contDiff_const)
    have hev : perTest c θ =ᶠ[𝓝 x0]
        (fun y : ℝ × ℝ => ∑ k ∈ Finset.Icc (-N) N, θ (y + ((k : ℝ) * c, 0))) :=
      (hU x0).mono fun y hy => hN θ hθsupp y hy
    exact hloc.contDiffAt.congr_of_eventuallyEq hev
  -- periodicity
  have hper : ∀ x : ℝ × ℝ, perTest c θ (x.1 + c, x.2) = perTest c θ x := by
    intro x
    rw [hpt, hpt]
    have key := finsum_comp_equiv (Equiv.addRight (1 : ℤ))
      (f := fun k : ℤ => θ (x + ((k : ℝ) * c, 0)))
    refine Eq.trans (finsum_congr fun k => ?_) key
    show θ ((x.1 + c, x.2) + ((k : ℝ) * c, 0)) = θ (x + (((Equiv.addRight (1 : ℤ)) k : ℝ) * c, 0))
    congr 1
    ext <;> simp <;> ring
  -- band
  have hband : ∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → perTest c θ x = 0 := by
    refine ⟨B2, fun x hx => ?_⟩
    rw [hpt]
    have hz : ∀ k : ℤ, θ (x + ((k : ℝ) * c, 0)) = 0 := by
      intro k
      by_contra hne
      have hmem : x + ((k : ℝ) * c, 0) ∈ tsupport θ := hθsupp _ hne
      have h1 := hB2 _ hmem
      simp only [Prod.snd_add, add_zero, Real.norm_eq_abs] at h1
      linarith
    simp only [hz, finsum_zero]
  -- derivatives
  have hD : ∀ i : Fin 2, B0579.pd i (perTest c θ) = perTest c (B0579.pd i θ) := by
    intro i
    funext x0
    obtain ⟨N, hN⟩ := loc x0
    have hpdsupp : ∀ y, B0579.pd i θ y ≠ 0 → y ∈ tsupport θ := by
      intro y hy
      have hne : fderiv ℝ θ y ≠ 0 := fun h0 => hy (by simp [B0579.pd, h0])
      exact (support_fderiv_subset (𝕜 := ℝ)) (Function.mem_support.2 hne)
    have hTd : ∀ k : ℤ, HasFDerivAt (fun y : ℝ × ℝ => θ (y + ((k : ℝ) * c, 0)))
        (fderiv ℝ θ (x0 + ((k : ℝ) * c, 0))) x0 :=
      fun k => (hasFDerivAt_comp_add_right ((k : ℝ) * c, 0)).2 (hd _).hasFDerivAt
    have hSd : HasFDerivAt
        (fun y : ℝ × ℝ => ∑ k ∈ Finset.Icc (-N) N, θ (y + ((k : ℝ) * c, 0)))
        (∑ k ∈ Finset.Icc (-N) N, fderiv ℝ θ (x0 + ((k : ℝ) * c, 0))) x0 := by
      have := HasFDerivAt.sum (u := Finset.Icc (-N) N)
        (A := fun k y => θ (y + ((k : ℝ) * c, 0)))
        (A' := fun k => fderiv ℝ θ (x0 + ((k : ℝ) * c, 0)))
        (x := x0) (fun k _ => hTd k)
      have e : (fun y : ℝ × ℝ => ∑ k ∈ Finset.Icc (-N) N, θ (y + ((k : ℝ) * c, 0))) =
          ∑ k ∈ Finset.Icc (-N) N, (fun y : ℝ × ℝ => θ (y + ((k : ℝ) * c, 0))) := by
        funext y
        simp [Finset.sum_apply]
      rw [e]
      exact this
    have hEv : perTest c θ =ᶠ[𝓝 x0]
        (fun y : ℝ × ℝ => ∑ k ∈ Finset.Icc (-N) N, θ (y + ((k : ℝ) * c, 0))) :=
      (hU x0).mono fun y hy => hN θ hθsupp y hy
    have lhs : B0579.pd i (perTest c θ) x0 =
        ∑ k ∈ Finset.Icc (-N) N, B0579.pd i θ (x0 + ((k : ℝ) * c, 0)) := by
      rw [B0579.pd, hEv.fderiv_eq, hSd.fderiv]
      simp [B0579.pd]
    have rhs : perTest c (B0579.pd i θ) x0 =
        ∑ k ∈ Finset.Icc (-N) N, B0579.pd i θ (x0 + ((k : ℝ) * c, 0)) :=
      hN (B0579.pd i θ) hpdsupp x0 (by simp)
    rw [lhs, rhs]
  exact ⟨⟨hSmooth, fun x => hper x, hband⟩, fun i => hD i⟩

end UnforcedLeray.Short.IIIa
