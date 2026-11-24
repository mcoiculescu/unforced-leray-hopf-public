import UnforcedLeray.Short.PartIIb.Sub.G1

/-!
# Part II-b, task `PartII-b:G1/3`: a bound through the axis

Target: `UnforcedLeray.Short.IIb.boundThroughAxis : BoundThroughAxis` (`Sub/G1.lean`). This is the
continuity step of `PartII-b:G1`: a `C¹` field satisfying the bound at every off-axis point of age
`> S` satisfies it on the axis.

Proof. For `y₀ ∈ axis`, the points `g t = y₀ + t • e₀` with `t > 0` are off the axis, satisfy
`ϱ(g t) = t` and `age R (g t) = R² / t²`. As `t → 0⁺` they tend to `y₀`, and the age tends to
`∞`, so the off-axis bound holds at `g t` for all small `t > 0`. Continuity of `F` and of
`fderiv ℝ F` passes the bound to the limit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:G1/3`: a bound through the axis** (continuity, `BoundThroughAxis` of `Sub/G1.lean`). -/
theorem boundThroughAxis : BoundThroughAxis := by
  intro R S M F hR hF hbound y₀ hy₀
  have hFc : Continuous F := hF.continuous
  have hFd : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  have hax0 : y₀ 0 = 0 ∧ y₀ 1 = 0 := hy₀
  -- the approach path `g t = y₀ + t e₀`
  obtain ⟨g, hg⟩ : ∃ g : ℝ → Space, ∀ t : ℝ,
      g t = y₀ + t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) :=
    ⟨fun t => y₀ + t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ), fun t => rfl⟩
  have hgfun : g = fun t => y₀ + t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := funext hg
  have hgc : Continuous g := by
    rw [hgfun]
    fun_prop
  have hg0 : g 0 = y₀ := by
    rw [hg 0]
    simp
  have hg0c : ∀ t : ℝ, g t 0 = t := by
    intro t
    rw [hg t]
    simp [hax0.1]
  have hg1c : ∀ t : ℝ, g t 1 = 0 := by
    intro t
    rw [hg t]
    simp [hax0.2]
  have hϱt : ∀ t : ℝ, 0 < t → Axi.ϱ (g t) = t := by
    intro t ht
    unfold Axi.ϱ
    rw [hg0c t, hg1c t]
    simp [Real.sqrt_sq ht.le]
  -- the quantity `‖F y‖ + ‖fderiv ℝ F y‖` is continuous along the path
  have hG : Continuous (fun t => ‖F (g t)‖ + ‖fderiv ℝ F (g t)‖) :=
    ((hFc.comp hgc).norm).add ((hFd.comp hgc).norm)
  have hlim : Tendsto (fun t => ‖F (g t)‖ + ‖fderiv ℝ F (g t)‖) (𝓝[>] (0 : ℝ))
      (𝓝 (‖F y₀‖ + ‖fderiv ℝ F y₀‖)) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    have h0 := hG.tendsto (0 : ℝ)
    simp only [hg0] at h0
    exact h0
  -- the bound holds along the path for small `t > 0`
  have hpos2 : (0 : ℝ) < |S| + 2 := by positivity
  have hδ : (0 : ℝ) < min 1 (R ^ 2 / (|S| + 2)) :=
    lt_min one_pos (div_pos (pow_pos hR 2) hpos2)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖F (g t)‖ + ‖fderiv ℝ F (g t)‖ ≤ M := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    obtain ⟨ht0, htδ⟩ := ht
    have ht1 : t < 1 := lt_of_lt_of_le htδ (min_le_left _ _)
    have htR : t < R ^ 2 / (|S| + 2) := lt_of_lt_of_le htδ (min_le_right _ _)
    rw [lt_div_iff₀ hpos2] at htR
    have hR2 : 0 < R ^ 2 := pow_pos hR 2
    have h2 : t * (t * (|S| + 2)) < t * R ^ 2 := mul_lt_mul_of_pos_left htR ht0
    have h3 : t * R ^ 2 < 1 * R ^ 2 := mul_lt_mul_of_pos_right ht1 hR2
    have h4 : S * t ^ 2 ≤ |S| * t ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self S) (sq_nonneg t)
    have hSt : S < R ^ 2 / t ^ 2 := by
      rw [lt_div_iff₀ (pow_pos ht0 2)]
      nlinarith [sq_nonneg t]
    have hgax : g t ∉ Axi.axis := by
      intro h
      rw [Axi.mem_axis_iff, hϱt t ht0] at h
      exact ht0.ne' h
    have hage : Axi.age R (g t) = R ^ 2 / t ^ 2 := by
      unfold Axi.age
      rw [hϱt t ht0]
    exact hbound (g t) hgax (by rw [hage]; exact hSt)
  exact le_of_tendsto hlim hev

end UnforcedLeray.Short.IIb
