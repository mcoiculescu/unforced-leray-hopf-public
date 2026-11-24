import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.ProfileUnique.WindowZero.PhaseVec
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.ProfileUnique.WindowZero.Integral

/-!
# Part II-b, task `PartII-b:G4/3/5/1` (`ProfileWindowZero`)

Source of record: `the November 2 reference manuscript`, lines 1902-1906, 2370-2384.
Target `profileWindowZero : UnforcedLeray.Short.IIb.ProfileWindowZero`.

Proof. For a window test `χ` and `j = r, z`, `Φ_j = φ · realC(e_j)` is a phase test (`windowPhaseVec`);
off the axis `dotL(Φ_j, N_v b) = φ · sLift(√s b_j)` (`nvC_rep`), so the phase pairing is
`(πR²/c) wInt χ (√s b_j)` (`windowChartIntegralVec`).  Equal pairings for `b, b'` give equal window
integrals; `wInt` is additive on locally integrable `√s b_j`, `√s b'_j` (`profileLocInt`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete WindowZeroHelp

namespace WindowZeroHelp2

/-- The dot product of `G e_j` with the ring lift picks the `j`-th component. -/
theorem dot_ej (G : ℂ) (j : Fin 2) (F : CProf) (R τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    dotL (G • B0412.realC (ej j y)) (NvC R F (τ, y)) =
      G * (((Real.sqrt (Axi.age R y) : ℝ) : ℂ) * F (Axi.chart R τ y) j) := by
  rw [DriftOff.nvC_rep]
  have hsq := Axi.eR_sq_sum hy
  have hϱ := Axi.ϱ_ne_zero hy
  fin_cases j
  · simp [ej, dotL_apply, Fin.sum_univ_three, DriftOff.realCL_apply, B0412.realC_apply,
      Axi.eR_apply_zero, Axi.eR_apply_one, Axi.eR_apply_two]
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) hsq
    push_cast at h2
    left
    linear_combination (((Real.sqrt (Axi.age R y) : ℝ) : ℂ) * F (Axi.chart R τ y) 0) * h2
  · simp [ej, dotL_apply, Fin.sum_univ_three, DriftOff.realCL_apply, B0412.realC_apply,
      Axi.eR_apply_zero, Axi.eR_apply_one, Axi.eR_apply_two]

/-- Integrability of the window integrand for a locally integrable `g`. -/
theorem wInt_integrable {c : ℝ} {χ : Coord → ℝ} (hχ : IsWinTest c χ) {g : Coord → ℂ}
    (hg : LocallyIntegrableOn g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) volume) :
    Integrable (fun x : Coord => ((χ x : ℂ) * ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) * g x) volume := by
  set K := tsupport χ with hK
  have hKc : IsCompact K := hχ.1.compact
  have hKsub : K ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := fun x hx => ⟨(hχ.1.supp hx).1, trivial⟩
  have h1 : IntegrableOn g K volume := hg.integrableOn_compact_subset hKsub hKc
  have hcont : ContinuousOn (fun x : Coord => (χ x : ℂ) * ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) K := by
    have hχc : Continuous fun x : Coord => (χ x : ℂ) :=
      Complex.continuous_ofReal.comp hχ.1.smooth.continuous
    have hw : ContinuousOn (fun x : Coord => ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) K := by
      refine (Complex.continuous_ofReal.comp_continuousOn ?_)
      exact ContinuousOn.rpow_const continuous_fst.continuousOn
        (fun x hx => Or.inl (ne_of_gt (hχ.1.supp hx).1))
    exact hχc.continuousOn.mul hw
  have h2 := h1.continuousOn_mul hcont hKc
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h2
  intro x hx
  by_contra hxK
  apply hx
  have : χ x = 0 := by
    by_contra h
    exact hxK (subset_tsupport χ (Function.mem_support.2 h))
  simp [this]

theorem wInt_sub {c : ℝ} {χ : Coord → ℝ} (hχ : IsWinTest c χ) {f g : Coord → ℂ}
    (hf : LocallyIntegrableOn f (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) volume)
    (hg : LocallyIntegrableOn g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) volume) :
    wInt χ (fun x => f x - g x) = wInt χ f - wInt χ g := by
  unfold wInt
  simp only [mul_sub]
  exact integral_sub (wInt_integrable hχ hf) (wInt_integrable hχ hg)

/-- The phase pairing of the window test `Φ_j` with the ring lift of `b ∈ H_p`. -/
theorem pairF_window (c ε : ℝ) (χ : Coord → ℝ) (hc : 0 < c) (hε : 0 < ε) (hχ : IsWinTest c χ)
    (j : Fin 2) (Φ : ℝ × Space → CVec3)
    (hΦe : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      Φ (τ, y) = ((winPer c χ (Axi.chart ε⁻¹ τ y) : ℝ) : ℂ) • B0412.realC (ej j y))
    (b : CProf) (hb : InHr c bgp b) :
    pairF (2 * ε * c) Φ (NvC ε⁻¹ b) =
      ((Real.pi * (ε⁻¹) ^ 2 / c : ℝ) : ℂ) *
        wInt χ (fun z : Coord => ((Real.sqrt z.1 : ℝ) : ℂ) * b z j) := by
  rw [← windowChartIntegralVec c ε χ (fun x => ((winPer c χ (Axi.chart ε⁻¹ x.1 x.2) : ℝ) : ℂ)) b j
    hc hε hχ hb (fun _ _ _ => rfl)]
  unfold pairF phaseInt
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun τ _ => ?_)
  have hax : ∀ᵐ y : Space, y ∉ Axi.axis := measure_eq_zero_iff_ae_notMem.1 Axi.volume_axis
  refine integral_congr_ae ?_
  filter_upwards [hax] with y hy
  show dotL (Φ (τ, y)) (NvC ε⁻¹ b (τ, y)) = _
  rw [hΦe τ y hy, dot_ej _ j b ε⁻¹ τ hy]
  rfl

end WindowZeroHelp2

open WindowZeroHelp2 in
theorem profileWindowZero : UnforcedLeray.Short.IIb.ProfileWindowZero := by
  intro c ε b b' hc hε hb hb' hpair χ hχ j
  obtain ⟨Φ, hΦ, hΦe⟩ := windowPhaseVec c ε χ hc hε hχ j
  have h := hpair Φ hΦ
  rw [pairF_window c ε χ hc hε hχ j Φ hΦe b hb, pairF_window c ε χ hc hε hχ j Φ hΦe b' hb'] at h
  have hne : ((Real.pi * (ε⁻¹) ^ 2 / c : ℝ) : ℂ) ≠ 0 := by
    have : (Real.pi * (ε⁻¹) ^ 2 / c : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have h2 := mul_left_cancel₀ hne h
  have e : (fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) * (b x j - b' x j)) =
      fun x => ((Real.sqrt x.1 : ℝ) : ℂ) * b x j - ((Real.sqrt x.1 : ℝ) : ℂ) * b' x j := by
    funext x; ring
  rw [e, wInt_sub hχ (profileLocInt c b hc hb j) (profileLocInt c b' hc hb' j), h2, sub_self]

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.profileWindowZero
