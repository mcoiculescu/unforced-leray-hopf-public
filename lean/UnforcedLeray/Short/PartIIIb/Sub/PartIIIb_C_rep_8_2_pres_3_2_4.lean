import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_4.Merid
import UnforcedLeray.Short.PartIIb.Sub.R1_7
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# `rawResid_of` (`PartIII-b:C/rep/8/2/pres/3/2/4`)

Source of record: `the November 2 reference manuscript`,
lines 1205-1225 (Proposition `sct:lift`, `sct:residual-bound`: `‖F_R‖_{C_per W^{1,p}} ≤ P_p ε^{1-2/p}`;
`p = 11/4` gives `Pε^{3/11}`), 1263 (`F_R = s^{3/2} r`), 2031.

For large `n` the level train is an exact planar train at `c = ν^{-2}` and `R = ε⁻¹ ≥ 2`, so
`PartIIa.RingResidualBound` at `ρ = 2`, `p = 11/4` gives periodicity of `F_R` and the `L^{11/4}`
bound `C(1+ν^{-2}+ν^{-1})^d ε^{3/11} ≤ C 3^d ν^{-2d} ε^{3/11}` (`ν ≤ 1`).  Measurability: the
cylindrical residual only involves first and second partial derivatives of the `C²` lifted
profiles, hence is continuous on `{r > 0, t > 0}` (`Merid.lean`); `F_R` is continuous off the axis.
Axisymmetry: `F_R = a e_r + b e₃` with `a, b` functions of `(ϱ, y₃)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.Short.PartIIa (ringResidual physResidualField)
open UnforcedLeray.Short.IIb (meridDomain MeridSmooth)

/-- `F_R` is continuous off the axis (source 1203-1250, 1263). -/
theorem pf4_ringResidual_contOn (R ν : ℝ) (ψ pr : UnforcedLeray.B0184.ProfilePoint → ℝ) (hR : 2 ≤ R)
    (hψ : ContDiffOn ℝ 3 ψ UnforcedLeray.B0185.ageDomain)
    (hp : ContDiffOn ℝ 2 pr UnforcedLeray.B0185.ageDomain) :
    ContinuousOn (fun x : ℝ × Space => ringResidual R ν ψ pr x.1 x.2) offAxisSet := by
  obtain ⟨m1, m2, m3⟩ := UnforcedLeray.Short.IIb.liftMeridSmooth R ψ pr hR hψ hp
  have hA := pf4_contOn_radial (ν := ν) m1 m2 m3
  have hB := pf4_contOn_axial (ν := ν) m1 m2 m3
  set e : ℝ × Space → ℝ := fun x => Real.exp (x.1 / 2) with he
  have hec : Continuous e := by rw [he]; fun_prop
  set X : ℝ × Space → Space := fun x => e x • x.2 with hX
  have hXc : Continuous X := hec.smul continuous_snd
  have hϱX : ∀ x : ℝ × Space, ϱ (X x) = e x * ϱ x.2 := by
    intro x
    simp only [hX, ϱ_smul, he, abs_of_pos (Real.exp_pos _)]
  have hXmem : ∀ x ∈ offAxisSet, X x ∈ (axis : Set Space)ᶜ := by
    intro x hx h
    have h0 := (mem_axis_iff _).1 h
    rw [hϱX] at h0
    exact (mul_pos (Real.exp_pos _) (ϱ_pos (y := x.2) hx)).ne' h0
  set φ : ℝ × Space → ℝ × ℝ × ℝ := fun x => (ϱ (X x), (X x) 2, Real.exp x.1) with hφ
  have hX2 : Continuous fun x : ℝ × Space => (X x) 2 :=
    (by fun_prop : Continuous fun y : Space => y 2).comp hXc
  have hφc : Continuous φ :=
    (continuous_ϱ.comp hXc).prodMk (hX2.prodMk (Real.continuous_exp.comp continuous_fst))
  have hφm : MapsTo φ offAxisSet meridDomain := by
    intro x hx
    exact ⟨ϱ_pos (y := X x) (hXmem x hx), Real.exp_pos _⟩
  have hAc := hA.comp hφc.continuousOn hφm
  have hBc := hB.comp hφc.continuousOn hφm
  have hRc : ContinuousOn (fun x : ℝ × Space => eR (X x)) offAxisSet :=
    (contDiffOn_eR (k := 0)).continuousOn.comp hXc.continuousOn hXmem
  have hall := (hec.pow 3).continuousOn.smul ((hAc.smul hRc).add (hBc.smul (continuousOn_const (c := (e3 : Space)))))
  exact hall.congr fun x _ => rfl

/-- The norm of `F_R` is invariant under `merPt` (source 2031: `F_R = a e_r + b e₃`,
`a, b` functions of `(ϱ, y₃)`). -/
theorem pf4_norm_ringResidual (R ν : ℝ) (ψ pr : UnforcedLeray.B0184.ProfilePoint → ℝ) (τ : ℝ) (y : Space) :
    ‖ringResidual R ν ψ pr τ y‖ = ‖ringResidual R ν ψ pr τ (merPt y)‖ := by
  have hc : 0 < Real.exp (τ / 2) := Real.exp_pos _
  have hm : Real.exp (τ / 2) • merPt y = merPt (Real.exp (τ / 2) • y) := by
    ext i
    have hr : ϱ (Real.exp (τ / 2) • y) = Real.exp (τ / 2) * ϱ y := by
      rw [ϱ_smul, abs_of_pos hc]
    fin_cases i
    · simp [merPt, hr]
    · simp [merPt]
    · simp [merPt]
  unfold ringResidual physResidualField
  rw [hm]
  simp only [pf4_ϱ_merPt, pf4_merPt_two]
  rw [norm_smul, norm_smul]
  congr 1
  exact pf4_norm_merid_eq _ _ _

theorem pf4_cOf_eq (ν : ℝ) (hν : 0 < ν) : cOf ν = ν ^ (-(2 : ℝ)) := by
  rw [cOf, Real.rpow_neg hν.le, Real.rpow_two]

theorem pf4_poly_le {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (d : ℕ) :
    (1 + ν ^ (-(2 : ℝ)) + ν⁻¹) ^ d ≤ 3 ^ d * (ν⁻¹) ^ (2 * d) := by
  have hw : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.2 hν1
  have h2 : ν ^ (-(2 : ℝ)) = ν⁻¹ ^ 2 := by
    rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]
  rw [h2, pow_mul, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ d
  nlinarith

theorem rawResid_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hB : UnforcedLeray.Short.PartIIa.RingResidualBound) : D.RawResid := by
  obtain ⟨ν₀, hν₀, C, d, H⟩ := hB 2 (11 / 4) (by norm_num) (by norm_num)
  refine ⟨|C| * 3 ^ d, 2 * d, ?_⟩
  filter_upwards [D.pf2_eventually_regime hst (ν₀ := min ν₀ 1) (lt_min hν₀ one_pos)] with n hn
  obtain ⟨hν, hR⟩ := hn
  set L := D.level n with hL
  have hνpos : 0 < L.ν := L.ν_pos
  have hνlt : L.ν < ν₀ := lt_of_lt_of_le hν (min_le_left _ _)
  have hν1 : L.ν ≤ 1 := (lt_of_lt_of_le hν (min_le_right _ _)).le
  have hext := pf2_exactPlanarTrain D.Pl L
  obtain ⟨hper, hbdd⟩ := H L.ν ⟨hνpos, hνlt⟩ _ _ hext (L.params D.Pl).R hR
  have hRe : (L.params D.Pl).R = L.ε⁻¹ := rfl
  -- smoothness of the profiles
  have hψ : ContDiffOn ℝ 3 (UnforcedLeray.Short.IIb.trainStream (L.params D.Pl))
      UnforcedLeray.B0185.ageDomain :=
    (UnforcedLeray.Short.IIb.trainStreamSmoothBUC_of UnforcedLeray.Short.PartI.trainStreamSmooth
      L.ν (cOf L.ν) hνpos (cOf_pos hνpos) L.train L.train_buc).of_le (by simp)
  have hpr : ContDiffOn ℝ 2 (UnforcedLeray.Short.IIb.trainPressure (L.params D.Pl))
      UnforcedLeray.B0185.ageDomain :=
    (UnforcedLeray.Short.IIb.trainPressureSmooth L.ν (cOf L.ν) L.train).of_le (by simp)
  have hcont := pf4_ringResidual_contOn (L.params D.Pl).R L.ν _ _ hR hψ hpr
  have hc := pf4_cOf_eq L.ν hνpos
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact pf4_axisZero_measurable (f := fun τ y => ‖rawResidF D.Pl L τ y‖) hcont.norm
  · intro τ y
    have := hper (τ)
    have e : 2 * L.ε * cOf L.ν = 2 * L.ν ^ (-(2 : ℝ)) / (L.params D.Pl).R := by
      rw [hc, hRe]
      field_simp
    show ‖ringResidual _ _ _ _ (τ + 2 * L.ε * cOf L.ν) y‖ = ‖ringResidual _ _ _ _ τ y‖
    rw [e, hper τ]
  · intro τ y
    exact pf4_norm_ringResidual _ _ _ _ τ y
  · intro τ
    obtain ⟨G, hmem, hG, hsum, -⟩ := hbdd
    have hfin : eLpNorm (rawResidF D.Pl L τ) (ENNReal.ofReal (11 / 4)) volume ≠ ⊤ :=
      (hmem τ).eLpNorm_ne_top
    have hle : (eLpNorm (rawResidF D.Pl L τ) (ENNReal.ofReal (11 / 4)) volume).toReal ≤
        UnforcedLeray.Short.PartIIa.polyConst C d L.ν (L.ν ^ (-(2 : ℝ))) *
          ((L.params D.Pl).R⁻¹) ^ (1 - 2 / (11 / 4 : ℝ)) := by
      have h0 : (eLpNorm (rawResidF D.Pl L τ) (ENNReal.ofReal (11 / 4)) volume).toReal +
          ∑ i, (eLpNorm (G τ i) (ENNReal.ofReal (11 / 4)) volume).toReal ≤
          UnforcedLeray.Short.PartIIa.polyConst C d L.ν (L.ν ^ (-(2 : ℝ))) *
            ((L.params D.Pl).R⁻¹) ^ (1 - 2 / (11 / 4 : ℝ)) := hsum τ
      have h1 : 0 ≤ ∑ i, (eLpNorm (G τ i) (ENNReal.ofReal (11 / 4)) volume).toReal :=
        Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
      linarith
    rw [← pf_e114] at hfin hle
    have hε : (L.params D.Pl).R⁻¹ = L.ε := by rw [hRe, inv_inv]
    have hexp : (1 - 2 / (11 / 4 : ℝ)) = 3 / 11 := by norm_num
    rw [hε, hexp] at hle
    have hεnn : 0 ≤ L.ε ^ (3 / 11 : ℝ) := Real.rpow_nonneg L.ε_pos.le _
    have hpoly := pf4_poly_le hνpos hν1 d
    have hP0 : 0 ≤ (1 + L.ν ^ (-(2 : ℝ)) + L.ν⁻¹) ^ d := by positivity
    have hB' : UnforcedLeray.Short.PartIIa.polyConst C d L.ν (L.ν ^ (-(2 : ℝ))) *
        L.ε ^ (3 / 11 : ℝ) ≤ |C| * 3 ^ d * L.ν⁻¹ ^ (2 * d) * L.ε ^ (3 / 11 : ℝ) := by
      unfold UnforcedLeray.Short.PartIIa.polyConst
      refine mul_le_mul_of_nonneg_right ?_ hεnn
      calc C * (1 + L.ν ^ (-(2 : ℝ)) + L.ν⁻¹) ^ d
          ≤ |C| * (1 + L.ν ^ (-(2 : ℝ)) + L.ν⁻¹) ^ d :=
            mul_le_mul_of_nonneg_right (le_abs_self C) hP0
        _ ≤ |C| * (3 ^ d * L.ν⁻¹ ^ (2 * d)) := mul_le_mul_of_nonneg_left hpoly (abs_nonneg C)
        _ = |C| * 3 ^ d * L.ν⁻¹ ^ (2 * d) := by ring
    calc eLpNorm (rawResidF D.Pl L τ) (11 / 4) volume
        = ENNReal.ofReal (eLpNorm (rawResidF D.Pl L τ) (11 / 4) volume).toReal :=
          (ENNReal.ofReal_toReal hfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hle.trans hB')

end UnforcedLeray.Short.PartIIIb.Concrete
