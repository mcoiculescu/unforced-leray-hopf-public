import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1_2_2

/-!
# Part II-b, leaf `PartII-b:T08/1/2/2/2` (`NvCDriftOnAxis`)

Source: `the November 2 reference manuscript` 1912-1915.
On the axis the ring lift vanishes identically (`age = R²/ϱ² = 0` there, so `√age = 0`), and for a
nice profile `N_v b` vanishes on a neighbourhood of the axis (`s > s₁` forces `b = 0`, and on the
neighbourhood the chart age exceeds `s₁`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

theorem nvCDriftOnAxis_proof : UnforcedLeray.Short.IIb.NvCDriftOnAxis := by
  -- the ring lift vanishes identically on the axis
  have hNvAxis : ∀ (R : ℝ) (F : UnforcedLeray.Short.IIb.CProf) (q : ℝ × UnforcedLeray.Space),
      q.2 ∈ UnforcedLeray.Axi.axis → UnforcedLeray.Short.IIb.NvC R F q = 0 := by
    intro R F q hq
    have hage : UnforcedLeray.Axi.age R q.2 = 0 := by
      rw [UnforcedLeray.Axi.age, (UnforcedLeray.Axi.mem_axis_iff _).1 hq]
      simp
    simp [UnforcedLeray.Short.IIb.NvC, UnforcedLeray.Axi.Nv, hage, UnforcedLeray.B0412.realC]
  intro c ε b hc hε hb p hp
  obtain ⟨_, _, s₀, s₁, L, hs0, hz⟩ := hb
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hK : 0 < |s₁| + 1 := by positivity
  have hδ : 0 < (ε⁻¹) ^ 2 / (|s₁| + 1) := by positivity
  -- the open neighbourhood of the axis on which `N_v b` vanishes
  have hU : IsOpen {q : ℝ × UnforcedLeray.Space | q.2 0 ^ 2 + q.2 1 ^ 2 < (ε⁻¹) ^ 2 / (|s₁| + 1)} :=
    isOpen_lt (by fun_prop) continuous_const
  have hpU : p ∈ {q : ℝ × UnforcedLeray.Space | q.2 0 ^ 2 + q.2 1 ^ 2 < (ε⁻¹) ^ 2 / (|s₁| + 1)} := by
    have h0 : p.2 0 = 0 := hp.1
    have h1 : p.2 1 = 0 := hp.2
    show p.2 0 ^ 2 + p.2 1 ^ 2 < (ε⁻¹) ^ 2 / (|s₁| + 1)
    rw [h0, h1]
    simpa using hδ
  have hev : UnforcedLeray.Short.IIb.NvC ε⁻¹ b =ᶠ[𝓝 p] fun _ => 0 := by
    refine Filter.eventually_of_mem (hU.mem_nhds hpU) fun q hq => ?_
    show UnforcedLeray.Short.IIb.NvC ε⁻¹ b q = 0
    have hq' : q.2 0 ^ 2 + q.2 1 ^ 2 < (ε⁻¹) ^ 2 / (|s₁| + 1) := hq
    by_cases hax : q.2 ∈ UnforcedLeray.Axi.axis
    · exact hNvAxis _ b q hax
    · have hne : q.2 0 ^ 2 + q.2 1 ^ 2 ≠ 0 := by
        intro h0
        apply hax
        constructor <;> nlinarith [sq_nonneg (q.2 0), sq_nonneg (q.2 1)]
      have hpos : 0 < q.2 0 ^ 2 + q.2 1 ^ 2 :=
        lt_of_le_of_ne (by positivity) (Ne.symm hne)
      have hage : s₁ < UnforcedLeray.Axi.age ε⁻¹ q.2 := by
        rw [UnforcedLeray.Axi.age, UnforcedLeray.Axi.ϱ_sq, lt_div_iff₀ hpos]
        rw [lt_div_iff₀ hK] at hq'
        nlinarith [le_abs_self s₁, sq_nonneg (q.2 0 ^ 2 + q.2 1 ^ 2)]
      have hb0 : b (UnforcedLeray.Axi.chart ε⁻¹ q.1 q.2) = 0 :=
        hz _ (Or.inr (Or.inl hage))
      have hz0 : (WithLp.toLp 2 fun _ : Fin 2 => (0 : ℝ)) = (0 : UnforcedLeray.Axi.Merid) := by
        ext i; simp
      simp [UnforcedLeray.Short.IIb.NvC, UnforcedLeray.Axi.Nv, hb0, UnforcedLeray.Short.IIb.reM,
        UnforcedLeray.Short.IIb.imM, UnforcedLeray.B0412.realC, hz0]
  have hd0 : fderiv ℝ (UnforcedLeray.Short.IIb.NvC ε⁻¹ b) p = 0 := by
    rw [hev.fderiv_eq]
    simp
  simp [UnforcedLeray.PhaseSpace.dτ, UnforcedLeray.PhaseSpace.radialT,
    UnforcedLeray.PhaseSpace.dy, hd0, hNvAxis _ _ p hp]

#print axioms nvCDriftOnAxis_proof
