import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4.Of

/-!
# `PartIII-a:T21/c1/a/4/1`: `SeedBiorthExt` from five analytic leaves

Source: `the November 2 reference manuscript`
lines 603-610.  Cutoff `f_R = f chi(./R)`, `R = n+1`; dominated convergence on both sides.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Lemma 1** (cutoff): a smooth compactly supported `chi : ℂ → ℝ` with `0 ≤ chi ≤ 1` and
`chi = 1` on the closed unit disc. -/
def ExtCutoff : Prop :=
  ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
    ∀ z : ℂ, ‖z‖ ≤ 1 → χ z = 1

/-- **Lemma 2** (sectors of Gaussian-bounded functions): the sector `n` of a continuous `g` with
`|g(y)| ≤ C exp(-|y|^2/8)` obeys the same bound in the radius and is strongly measurable. -/
def ExtSectorBound : Prop :=
  ∀ (g : ℂ → ℂ) (C : ℝ) (n : ℤ), Continuous g →
    (∀ y : ℝ × ℝ, ‖g (planeToC y)‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) →
    (∀ r : ℝ, 0 ≤ r → ‖Planar.NUE.Polar.angularSector g n r‖ ≤ C * Real.exp (-(r ^ 2) / 8)) ∧
      StronglyMeasurable (Planar.NUE.Polar.angularSector g n)

/-- **Lemma 3** (bounded weight `h/k`; `SeedFunctional`'s `g = h/k` is `O(r⁻²)` for `r ≥ 1`, and on
`(0,1]` one has `|k| ≥ 7/4 e^{-1/4}` and `|h r| = |seedPlanar h r|` bounded). -/
def ExtWeightBound : Prop :=
  PartI.SeedFunctional →
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h) ℓ → ContDiff ℝ ∞ (PartI.seedPlanar h) →
    (∃ C : ℝ, ∀ y : ℝ × ℝ,
        ‖PartI.seedPlanar h (planeToC y)‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) →
    ∃ C : ℝ, ∀ r : ℝ, 0 < r → strainK r ≠ 0 → ‖h r / (strainK r : ℂ)‖ ≤ C

/-- **Lemma 4** (dominated convergence for `seedEll`): with `h/k` bounded and profiles `F n`
Gaussian-bounded, measurable, converging pointwise on `(0,∞)`, `seedEll h (F n) → seedEll h Finf`. -/
def ExtRightDCT : Prop :=
  ∀ (h : ℝ → ℂ) (Cw : ℝ), AEStronglyMeasurable h (volume.restrict (Ioi (0 : ℝ))) →
    (∀ r : ℝ, 0 < r → strainK r ≠ 0 → ‖h r / (strainK r : ℂ)‖ ≤ Cw) →
    ∀ (F : ℕ → ℝ → ℂ) (Finf : ℝ → ℂ) (C : ℝ),
      (∀ n, AEStronglyMeasurable (F n) (volume.restrict (Ioi (0 : ℝ)))) →
      (∀ n (r : ℝ), 0 < r → ‖F n r‖ ≤ C * Real.exp (-(r ^ 2) / 8)) →
      (∀ r : ℝ, 0 < r → Tendsto (fun n => F n r) atTop (𝓝 (Finf r))) →
      Tendsto (fun n => PartI.seedEll h (F n)) atTop (𝓝 (PartI.seedEll h Finf))

/-- **Lemma 5** (dominated convergence on the plane): `lamP y * f` is integrable and
`∫ lamP (chi(./(n+1)) f) → ∫ lamP f`. -/
def ExtLeftDCT : Prop :=
  ∀ (lamP : ℝ × ℝ → ℂ), Continuous lamP →
    (∃ C : ℝ, ∀ y, ‖lamP y‖ ≤ C * (1 + |y.1| + |y.2|)⁻¹ ^ 2) →
    ∀ (f : ℂ → ℂ), Continuous f →
      (∃ C : ℝ, ∀ y : ℝ × ℝ, ‖f (planeToC y)‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) →
      ∀ χ : ℂ → ℝ, Continuous χ → (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) → (∀ z : ℂ, ‖z‖ ≤ 1 → χ z = 1) →
        Integrable (fun y => lamP y * f (planeToC y)) ∧
        Tendsto (fun n : ℕ => ∫ y, lamP y *
            (((χ (planeToC y / ((n : ℂ) + 1)) : ℝ) : ℂ) * f (planeToC y))) atTop
          (𝓝 (∫ y, lamP y * f (planeToC y)))

theorem seedBiorthExt_of (hc : ExtCutoff) (hs : ExtSectorBound) (hw : ExtWeightBound)
    (hr : ExtRightDCT) (hl : ExtLeftDCT) : SeedBiorthExt := by
  intro hSF lam h hh ℓ hIS hsm hG lamP hcont hd hcl f hf hfG
  obtain ⟨χ, hχs, hχc, hχb, hχ1⟩ := hc
  obtain ⟨Cw, hCw⟩ := hw hSF lam h hh ℓ hIS hsm hG
  have hfc : Continuous f := hf.continuous
  obtain ⟨Cf, hCf⟩ := hfG
  -- cutoff functions
  set fn : ℕ → ℂ → ℂ := fun n z => ((χ (z / ((n : ℂ) + 1)) : ℝ) : ℂ) * f z with hfn
  have hn0 : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := fun n => by
    have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero n
  have hfnS : ∀ n, ContDiff ℝ ∞ (fn n) := by
    intro n
    have h1 : ContDiff ℝ ∞ (fun z : ℂ => z / ((n : ℂ) + 1)) :=
      (contDiff_id.div_const _)
    exact (Complex.ofRealCLM.contDiff.comp (hχs.comp h1)).mul hf
  have hfnC : ∀ n, HasCompactSupport (fn n) := by
    intro n
    have h1 : HasCompactSupport (fun z : ℂ => χ (z / ((n : ℂ) + 1))) := by
      have := hχc.comp_smul (c := ((n : ℂ) + 1)⁻¹) (inv_ne_zero (hn0 n))
      simpa [div_eq_inv_mul] using this
    have h2 : HasCompactSupport (fun z : ℂ => ((χ (z / ((n : ℂ) + 1)) : ℝ) : ℂ)) :=
      h1.comp_left Complex.ofReal_zero
    exact h2.mul_right
  have hfnb : ∀ n (y : ℝ × ℝ), ‖fn n (planeToC y)‖ ≤ Cf * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    intro n y
    simp only [hfn, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (hχb _).1]
    calc _ ≤ 1 * ‖f (planeToC y)‖ := by
          apply mul_le_mul_of_nonneg_right (hχb _).2 (norm_nonneg _)
      _ ≤ _ := by simpa using hCf y
  have hfnCont : ∀ n, Continuous (fn n) := fun n => (hfnS n).continuous
  -- the identities for f_n
  have hid := fun n => hcl (fn n) (hfnS n) (hfnC n)
  -- left limits
  have L0 := (hl (lamP 0) (hcont 0) (hd.imp fun C hC y => hC 0 y) f hfc ⟨Cf, hCf⟩ χ hχs.continuous hχb hχ1)
  have L1 := (hl (lamP 1) (hcont 1) (hd.imp fun C hC y => hC 1 y) f hfc ⟨Cf, hCf⟩ χ hχs.continuous hχb hχ1)
  -- right limits
  have hhmeas : AEStronglyMeasurable h (volume.restrict (Ioi (0 : ℝ))) := by
    have hcont' : Continuous (fun r : ℝ => PartI.seedPlanar h (r : ℂ)) :=
      hsm.continuous.comp Complex.continuous_ofReal
    refine hcont'.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr' : 0 < r := hr
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr'.ne'
    simp [PartI.seedPlanar, Planar.NUE.Ang.ofProfile, Planar.NUE.Ang.angPhase,
      abs_of_pos hr', hrC]
  have hCfn : ∀ n (k : ℤ), (∀ r : ℝ, 0 ≤ r → ‖Planar.NUE.Polar.angularSector (fn n) k r‖ ≤
      Cf * Real.exp (-(r ^ 2) / 8)) ∧ StronglyMeasurable (Planar.NUE.Polar.angularSector (fn n) k) :=
    fun n k => hs (fn n) Cf k (hfnCont n) (hfnb n)
  have hCf0 : ∀ (k : ℤ), (∀ r : ℝ, 0 ≤ r → ‖Planar.NUE.Polar.angularSector f k r‖ ≤
      Cf * Real.exp (-(r ^ 2) / 8)) ∧ StronglyMeasurable (Planar.NUE.Polar.angularSector f k) :=
    fun k => hs f Cf k hfc hCf
  -- eventually fn n = f on circle of radius r
  have hev : ∀ (k : ℤ) (r : ℝ), 0 < r →
      ∀ᶠ n : ℕ in atTop, Planar.NUE.Polar.angularSector (fn n) k r =
        Planar.NUE.Polar.angularSector f k r := by
    intro k r hr
    filter_upwards [eventually_ge_atTop ⌈r⌉₊] with n hn
    unfold Planar.NUE.Polar.angularSector
    congr 2
    funext θ
    have hnorm : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hr.le]
    have hrn : r ≤ (n : ℝ) + 1 := by
      have := Nat.le_ceil r
      have h2 : (⌈r⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hχone : χ (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) / ((n : ℂ) + 1)) = 1 := by
      apply hχ1
      have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
      rw [this, norm_div, hnorm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [div_le_one (by positivity)]
      exact hrn
    simp only [hfn, hχone]
    simp
  have R0 : Tendsto (fun n => PartI.seedEll h (Planar.NUE.Polar.angularSector (fn n) 2)) atTop
      (𝓝 (PartI.seedEll h (Planar.NUE.Polar.angularSector f 2))) :=
    hr h Cw hhmeas hCw _ _ Cf
      (fun n => ((hCfn n 2).2).aestronglyMeasurable)
      (fun n r hr => (hCfn n 2).1 r hr.le)
      (fun r hr => tendsto_const_nhds.congr' ((hev 2 r hr).mono fun n hn => hn.symm))
  have R1 : Tendsto (fun n => PartI.seedEll h
      (fun r => conj (Planar.NUE.Polar.angularSector (fn n) (-2) r))) atTop
      (𝓝 (PartI.seedEll h (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r)))) :=
    hr h Cw hhmeas hCw _ _ Cf
      (fun n => (Complex.continuous_conj.comp_stronglyMeasurable (hCfn n (-2)).2).aestronglyMeasurable)
      (fun n r hr => by simpa using (hCfn n (-2)).1 r hr.le)
      (fun r hr => tendsto_const_nhds.congr' ((hev (-2) r hr).mono fun n hn => by simp [hn]))
  constructor
  · have : ∀ n : ℕ, ∫ y, lamP 0 y * (((χ (planeToC y / ((n : ℂ) + 1)) : ℝ) : ℂ) * f (planeToC y)) =
        PartI.seedEll h (Planar.NUE.Polar.angularSector (fn n) 2) := fun n => (hid n).1
    exact tendsto_nhds_unique L0.2 (R0.congr fun n => (this n).symm)
  · have : ∀ n : ℕ, ∫ y, lamP 1 y * (((χ (planeToC y / ((n : ℂ) + 1)) : ℝ) : ℂ) * f (planeToC y)) =
        conj (PartI.seedEll h (fun r => conj (Planar.NUE.Polar.angularSector (fn n) (-2) r))) :=
      fun n => (hid n).2
    have R1' := (Complex.continuous_conj.tendsto _).comp R1
    exact tendsto_nhds_unique L1.2 (R1'.congr fun n => (this n).symm)

end UnforcedLeray.Short.IIIa
