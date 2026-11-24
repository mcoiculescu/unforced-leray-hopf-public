import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# `FarMajorantL2` from the chart bookkeeping (source 3996-4005)

Assembly of `FarMajorantL2` from the generic steps of `Sub/PositiveKernel` and the chart facts of
`Sub/FarMajorantL2/Defs.lean`. See that file for the route and the constants.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

theorem farMajorantL2_of (hA : FarMajorantPointwise) (hK : FarKernL1) (hM : DilationMargin)
    (hL : DilMajL2) (hMeasD : DilMajMeasurable) (hAx : DilMajAxisym) (hG : GAxFacts)
    (hCM : ChartL2Majorant) (hCS : ChartL2Source) (hNs : NsSymNormLe) : FarMajorantL2 := by
  intro Kset hK' hKs dm dp hdm b δ hb hb1 hδ
  obtain ⟨CM, hCM0, hCMb⟩ := hM Kset hK' hKs
  obtain ⟨CT, hCT0, hCTb⟩ := hK
  have hcδ : 0 < 1 - Real.exp (-δ / 2) := by
    have : Real.exp (-δ / 2) < 1 := (Real.exp_lt_exp.2 (by linarith : -δ / 2 < 0)).trans_eq Real.exp_zero
    linarith
  refine ⟨CM * CT / (1 - Real.exp (-δ / 2)), 0, 1, one_pos, ?_⟩
  intro p d hreg hν μ hμ sm hsm hsS f hf _
  have hε : 0 < p.ε := p.ε_pos
  have hR : 0 < p.R := p.R_pos
  have hc : 0 < p.c := by
    rw [hreg.c_eq]; exact inv_pos.2 (pow_pos p.ν_pos 2)
  set R := p.R with hRdef
  set c := p.c with hcdef
  have hdd : 0 < (1 - Real.exp (-δ / 2)) * R / Real.sqrt sm :=
    div_pos (mul_pos hcδ hR) (Real.sqrt_pos.2 hsm)
  set dd := (1 - Real.exp (-δ / 2)) * R / Real.sqrt sm with hdd_def
  set A : ℝ≥0∞ := ENNReal.ofReal (CT / dd) with hAdef
  obtain ⟨hax, hper, hmeas⟩ := hG R c f hR hc hf.measurable
  set g := gAx R c f with hg
  set Mf : ℝ → UnforcedLeray.Space → ℝ≥0∞ := dilMaj μ dd g with hMf
  have hMmeas : Measurable (Function.uncurry Mf) := hMeasD μ dd g hmeas
  have hMper : ∀ τ y, Mf (τ + 2 * c / R) y = Mf τ y := by
    intro τ y
    simp only [hMf, dilMaj]
    refine lintegral_congr fun l => ?_
    congr 1
    refine lintegral_congr fun z => ?_
    have : τ + 2 * c / R + 2 * Real.log l = (τ + 2 * Real.log l) + 2 * c / R := by ring
    rw [this, hper]
  have hMax : AxisymProf Mf := fun τ y y' h1 h2 => hAx μ dd g hax τ y y' h1 h2
  have hPpos : 0 < 2 * c / R := div_pos (by linarith) hR
  have hmeasB : MeasurableSet (ageBelow sm) := measurableSet_lt measurable_fst measurable_const
  -- Step 1: pointwise majorant
  set E : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) with hE
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  have hfn : eLpNorm f 2 (ageμ c (-1 / 2)) = E ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2]
  rw [hfn]
  set LHS : ℝ≥0∞ := ∫⁻ x in ageBelow sm,
    (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * farMajE R c δ μ f x) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) with hLHS
  set X : ℝ≥0∞ := ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ y : UnforcedLeray.Space,
    Mf τ y ^ (2 : ℝ) with hX
  set G : ℝ≥0∞ := ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ z : UnforcedLeray.Space,
    g τ z ^ (2 : ℝ) with hGdef
  set k : ℝ := 1 / (2 * Real.pi * c * R) with hk
  have hk0 : 0 < k := by positivity
  -- Step 1: pointwise majorant, a.e. on the age region
  have step1 : LHS ≤ ∫⁻ x in ageBelow sm, (ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
      Mf (chartTau R x) (chartY R x)) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) := by
    refine lintegral_mono_ae ?_
    have hpos : ∀ᵐ x ∂(ageμ c (-3 / 2)), 0 < x.1 := by
      filter_upwards [ae_ageμ_mem hc (-3 / 2)] with x hx using hx.1
    refine (ae_restrict_iff' hmeasB).2 ?_
    filter_upwards [hpos] with x hx hxB
    have hxlt : x.1 < sm := hxB
    refine ENNReal.rpow_le_rpow (mul_le_mul' le_rfl ?_) (by norm_num)
    exact hA R c δ μ sm hR hδ hsm f x hx hxlt
  -- Step 2: the chart identity
  have step2 : ∫⁻ x in ageBelow sm, (ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
      Mf (chartTau R x) (chartY R x)) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) =
      ENNReal.ofReal k * ∫⁻ τ in Ico (0 : ℝ) (2 * c / R),
        ∫⁻ y in {y : UnforcedLeray.Space | R / Real.sqrt sm < hRad y}, Mf τ y ^ (2 : ℝ) :=
    hCM R c sm hR hc hsm Mf hMmeas hMper hMax
  have step3 : ∫⁻ τ in Ico (0 : ℝ) (2 * c / R),
        ∫⁻ y in {y : UnforcedLeray.Space | R / Real.sqrt sm < hRad y}, Mf τ y ^ (2 : ℝ) ≤ X :=
    lintegral_mono fun τ => setLIntegral_le_lintegral _ _
  have hLX : LHS ≤ ENNReal.ofReal k * X :=
    step1.trans (step2.le.trans (mul_le_mul' le_rfl step3))
  -- Step 4: Young + Minkowski
  have hmarg : ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) ≤ ENNReal.ofReal CM :=
    hCMb μ hμ
  have hkern : ∫⁻ x, farKern dd x ≤ A := hCTb dd hdd
  have hXG : X ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal CM * A * G ^ (1 / 2 : ℝ) := by
    refine (hL μ dd g hmeas (2 * c / R) hPpos hper A hkern).trans ?_
    gcongr
  -- Step 5: the source norm
  have hGE : G ≤ ENNReal.ofReal (2 * Real.pi * R * c) * E := by
    rw [hGdef, hg, hCS R c hR hc f hf.measurable]
    refine mul_le_mul' le_rfl (lintegral_mono fun x => ?_)
    have hx : ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (f x))) ≤ ‖f x‖ₑ := by
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hNs (f x))
    exact ENNReal.rpow_le_rpow hx (by norm_num)
  have hkk : ENNReal.ofReal k * ENNReal.ofReal (2 * Real.pi * R * c) = 1 := by
    rw [← ENNReal.ofReal_mul hk0.le, hk]
    have : 1 / (2 * Real.pi * c * R) * (2 * Real.pi * R * c) = 1 := by
      field_simp
    rw [this, ENNReal.ofReal_one]
  have hfin : LHS ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal CM * A * E ^ (1 / 2 : ℝ) := by
    calc LHS ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal k * X) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hLX (by norm_num)
      _ = ENNReal.ofReal k ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ ENNReal.ofReal k ^ (1 / 2 : ℝ) * (ENNReal.ofReal CM * A * G ^ (1 / 2 : ℝ)) := by
          gcongr
      _ ≤ ENNReal.ofReal k ^ (1 / 2 : ℝ) * (ENNReal.ofReal CM * A *
            (ENNReal.ofReal (2 * Real.pi * R * c) * E) ^ (1 / 2 : ℝ)) := by
          gcongr
      _ = ENNReal.ofReal CM * A * ((ENNReal.ofReal k * ENNReal.ofReal (2 * Real.pi * R * c)) ^
            (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          ring
      _ = ENNReal.ofReal CM * A * E ^ (1 / 2 : ℝ) := by
          rw [hkk, ENNReal.one_rpow, one_mul]
  have hcoef : ENNReal.ofReal CM * A = ENNReal.ofReal (CM * CT / (1 - Real.exp (-δ / 2)) *
      p.ν⁻¹ ^ (0 : ℕ) * (p.ε * Real.sqrt sm)) := by
    rw [hAdef, ← ENNReal.ofReal_mul hCM0, pow_zero, mul_one]
    congr 1
    have hRe : R = p.ε⁻¹ := rfl
    have hs : 0 < Real.sqrt sm := Real.sqrt_pos.2 hsm
    rw [hdd_def, hRe]
    field_simp
  rw [← hcoef]
  exact hfin

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
