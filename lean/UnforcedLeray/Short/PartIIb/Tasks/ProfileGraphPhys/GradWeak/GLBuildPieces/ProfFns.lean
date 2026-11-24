import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_3

/-!
# `PartII-b:T10/7/1/1/3` piece: `glProfFns_of_AB` (complex profile functions of `radComb g` and `g 2`)

Source of record: `the November 2 reference manuscript` 1912-1921 (chart 1639-1668).

Route: for a field `F : ℝ × Space → CVec3` that is a.e. `P`-periodic in `τ`, a.e. measurable, and whose
real and imaginary parts are `𝒪`-equivariant, apply `GLAvgRep` to `reS ∘ F` and `imS ∘ F`, then
`GLProfPeriodic` to make the profile functions everywhere `P`-periodic, and recombine with
`F = realC (reS F) + I • realC (imS F)`.  Apply this to `F = radComb g` and `F = g 2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb.GLProfFnsAux

theorem realC_add_aux (x y : UnforcedLeray.Space) :
    UnforcedLeray.B0412.realC (x + y) =
      UnforcedLeray.B0412.realC x + UnforcedLeray.B0412.realC y := by
  ext i
  simp [UnforcedLeray.B0412.realC_apply]

theorem realC_smul_real_aux (k : ℝ) (x : UnforcedLeray.Space) :
    UnforcedLeray.B0412.realC (k • x) = (k : ℂ) • UnforcedLeray.B0412.realC x := by
  ext i
  simp [UnforcedLeray.B0412.realC_apply]

theorem realC_reS_imS_aux (v : UnforcedLeray.PhaseSpace.CVec3) :
    UnforcedLeray.B0412.realC (UnforcedLeray.Short.IIb.reS v) +
      Complex.I • UnforcedLeray.B0412.realC (UnforcedLeray.Short.IIb.imS v) = v := by
  ext i
  have hri := Complex.re_add_im (v i)
  simp [UnforcedLeray.B0412.realC_apply, UnforcedLeray.Short.IIb.reS, UnforcedLeray.Short.IIb.imS]
  linear_combination hri

theorem continuous_reS_aux : Continuous UnforcedLeray.Short.IIb.reS := by
  unfold UnforcedLeray.Short.IIb.reS
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact Complex.continuous_re.comp (PiLp.continuous_apply 2 _ i)

theorem continuous_imS_aux : Continuous UnforcedLeray.Short.IIb.imS := by
  unfold UnforcedLeray.Short.IIb.imS
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact Complex.continuous_im.comp (PiLp.continuous_apply 2 _ i)

/-- One complex profile function from the real and imaginary parts of a periodic field. -/
theorem profFns_complex_of (h1 : UnforcedLeray.Short.IIb.GLAvgRep)
    (h2 : UnforcedLeray.Short.IIb.GLProfPeriodic) (P : ℝ) (hP : 0 < P)
    (F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (hF : AEStronglyMeasurable F volume)
    (hper : ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume, F (x.1 + P, x.2) = F x)
    (hE : UnforcedLeray.Short.IIb.GLEquivar (fun x => UnforcedLeray.Short.IIb.reS (F x)) ∧
      UnforcedLeray.Short.IIb.GLEquivar (fun x => UnforcedLeray.Short.IIb.imS (F x))) :
    ∃ Ar Az : ℝ × (ℝ × ℝ) → ℂ,
      Measurable Ar ∧ Measurable Az ∧
      (∀ p, Ar (p.1 + P, p.2) = Ar p) ∧ (∀ p, Az (p.1 + P, p.2) = Az p) ∧
      (∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume,
        F x = Ar (x.1, UnforcedLeray.Axi.mer x.2) •
            UnforcedLeray.B0412.realC (UnforcedLeray.Axi.eR x.2) +
          Az (x.1, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.B0412.realC UnforcedLeray.Axi.e3) := by
  have hRe : AEStronglyMeasurable (fun x => UnforcedLeray.Short.IIb.reS (F x)) volume :=
    continuous_reS_aux.comp_aestronglyMeasurable hF
  have hIm : AEStronglyMeasurable (fun x => UnforcedLeray.Short.IIb.imS (F x)) volume :=
    continuous_imS_aux.comp_aestronglyMeasurable hF
  have hperRe : ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume,
      (fun x => UnforcedLeray.Short.IIb.reS (F x)) (x.1 + P, x.2) =
        (fun x => UnforcedLeray.Short.IIb.reS (F x)) x := by
    filter_upwards [hper] with x hx
    simp only [hx]
  have hperIm : ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume,
      (fun x => UnforcedLeray.Short.IIb.imS (F x)) (x.1 + P, x.2) =
        (fun x => UnforcedLeray.Short.IIb.imS (F x)) x := by
    filter_upwards [hper] with x hx
    simp only [hx]
  obtain ⟨A, B, hA, hB, hrepRe⟩ := h1 (fun x => UnforcedLeray.Short.IIb.reS (F x)) hRe hE.1
  obtain ⟨C, D, hC, hD, hrepIm⟩ := h1 (fun x => UnforcedLeray.Short.IIb.imS (F x)) hIm hE.2
  obtain ⟨A', B', hA', hB', hpA', hpB', hrepRe'⟩ :=
    h2 P (fun x => UnforcedLeray.Short.IIb.reS (F x)) A B hP hA hB hrepRe hperRe
  obtain ⟨C', D', hC', hD', hpC', hpD', hrepIm'⟩ :=
    h2 P (fun x => UnforcedLeray.Short.IIb.imS (F x)) C D hP hC hD hrepIm hperIm
  refine ⟨fun p => ((A' p : ℝ) : ℂ) + Complex.I * ((C' p : ℝ) : ℂ),
    fun p => ((B' p : ℝ) : ℂ) + Complex.I * ((D' p : ℝ) : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · exact (Complex.measurable_ofReal.comp hA').add
      (measurable_const.mul (Complex.measurable_ofReal.comp hC'))
  · exact (Complex.measurable_ofReal.comp hB').add
      (measurable_const.mul (Complex.measurable_ofReal.comp hD'))
  · intro p
    simp only [hpA' p, hpC' p]
  · intro p
    simp only [hpB' p, hpD' p]
  · filter_upwards [hrepRe', hrepIm'] with x h1x h2x
    have e : F x = UnforcedLeray.B0412.realC (UnforcedLeray.Short.IIb.reS (F x)) +
        Complex.I • UnforcedLeray.B0412.realC (UnforcedLeray.Short.IIb.imS (F x)) :=
      (realC_reS_imS_aux (F x)).symm
    rw [e]
    rw [h1x, h2x]
    simp only [realC_add_aux, realC_smul_real_aux]
    module

/-- Measurability of the radial combination (a.e. strongly measurable). -/
theorem radComb_aesm_aux (g : Fin 3 → ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3)
    (P r : ℝ) (hgY : ∀ j, UnforcedLeray.Short.IIb.IsInYr P r (g j)) :
    AEStronglyMeasurable (UnforcedLeray.Short.IIb.radComb g) volume := by
  have hc0 : Measurable (fun x : ℝ × UnforcedLeray.Space =>
      (((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ)) : ℂ)) := by
    fun_prop
  have hc1 : Measurable (fun x : ℝ × UnforcedLeray.Space =>
      (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ)) : ℂ)) := by
    fun_prop
  show AEStronglyMeasurable (fun x : ℝ × UnforcedLeray.Space =>
      (((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ)) : ℂ) • g 0 x +
      (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ)) : ℂ) • g 1 x) volume
  exact ((hc0.aestronglyMeasurable).smul (hgY 0).meas).add
    ((hc1.aestronglyMeasurable).smul (hgY 1).meas)

end UnforcedLeray.Short.IIb.GLProfFnsAux

open UnforcedLeray.Short.IIb.GLProfFnsAux in
theorem glProfFns_of_AB (h1 : UnforcedLeray.Short.IIb.GLAvgRep)
    (h2 : UnforcedLeray.Short.IIb.GLProfPeriodic) :
    UnforcedLeray.Short.IIb.GLProfFns := by
  intro c ε r g hc hε hr1 hr3 hgY hE
  have hP : 0 < 2 * ε * c := by positivity
  have hradper : ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume,
      UnforcedLeray.Short.IIb.radComb g (x.1 + 2 * ε * c, x.2) =
        UnforcedLeray.Short.IIb.radComb g x := by
    filter_upwards [(hgY 0).periodic, (hgY 1).periodic] with x h0 h1'
    simp only [UnforcedLeray.Short.IIb.radComb, h0, h1']
  obtain ⟨Ar, Az, hmAr, hmAz, hpAr, hpAz, hrad⟩ :=
    profFns_complex_of h1 h2 (2 * ε * c) hP
      (UnforcedLeray.Short.IIb.radComb g)
      (radComb_aesm_aux g (2 * ε * c) r hgY) hradper
      ⟨(hE UnforcedLeray.Short.IIb.reS (Or.inl rfl)).1,
        (hE UnforcedLeray.Short.IIb.imS (Or.inr rfl)).1⟩
  obtain ⟨Br, Bz, hmBr, hmBz, hpBr, hpBz, hradB⟩ :=
    profFns_complex_of h1 h2 (2 * ε * c) hP (fun x => g 2 x)
      (hgY 2).meas (hgY 2).periodic
      ⟨(hE UnforcedLeray.Short.IIb.reS (Or.inl rfl)).2,
        (hE UnforcedLeray.Short.IIb.imS (Or.inr rfl)).2⟩
  exact ⟨Ar, Az, Br, Bz, hmAr, hmAz, hmBr, hmBz, hpAr, hpAz, hpBr, hpBz, hrad, hradB⟩
