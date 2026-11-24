import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Sop
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressTransportNorm
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarKernelL2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarKernelLinear

/-!
# The leaf `NearSNCont`: the near inverse `S_N = S_ε - S_far` is norm continuous in `μ`
(source 3888-3920, 5684-5685, 5701-5704, 5918-5920)

Source of record: `the November 2 reference manuscript` (73 pages).

On the Floquet window `μ_n([-1,1]) ⊆ [σ₀/2, (σ₀ + 1/4)/2] ⊂ (0, 1/4)` (for large `n`,
`inv_seq_large`), the pinned near operator `(nearOpsAt D.Pl D.K L μ).SN` satisfies `IsMaskedNear`:
`SN = Seps - Sf` where `Seps` is the real transport of the stress map of `T_ε(μ)` and `Sf` has the
far-mask kernel pin `IsFarMask`.
1. By uniqueness of stress maps (`StressMapUnique`) and uniqueness of stress transports
   (`isStressTransport_unique`), `Seps` coincides on the window with `realForm (S' μ)` for the
   norm-continuous complex stress-map family `S'` of `PartIII-b:C/cont/S` (`SopFam.lean`).
2. For `μ, μ' ≥ 0`, the masked dilation kernel `sepWfar` satisfies
   `|l^{2μ+2} - l^{2μ'+2}| ≤ 8 |μ - μ'| l^{2(-1/8)+2}` on `l ∈ (0, 1)`, so
   `‖farOut μ f - farOut μ' f‖ ≤ C |μ - μ'| farMajOut (-1/8) f` a.e. on box tensors `f`.
   By `farMajL2` at `μ₀ = -1/8 > -1/4` and density of box tensors in `Z` (`boxDenseZ`),
   `‖Sf μ - Sf μ'‖ ≤ K |μ - μ'|`, giving operator-norm continuity of `Sf` and hence of `SN`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst
open UnforcedLeray.Short.PartIIIb.NearInst.Masked
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. Uniqueness of stress transports -/

/-- **Stress transports are unique** (source 1641-1646, 2676-2683): an `IsStressTransport` real
form of `S'` is determined by `S'`, since `cellPt` carries `measureH c` to `c • ageμ c (-3/2)`
(`CellPtH`). -/
theorem isStressTransport_unique {c mZ ρb : ℝ} (hc : 0 < c) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb)
    {S₁ S₂ : Zsp c mZ ρb →L[ℝ] Hsp c}
    {S' : UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC}
    (h₁ : IsStressTransport S₁ S') (h₂ : IsStressTransport S₂ S') : S₁ = S₂ := by
  have hT : CellPtHT c := cpcHT_eq c hc
  have hH : CellPtH c := cpcH_eq c hc
  ext1 F
  have hae : (cplxT c hT (zsumL c mZ ρb hmZ hρ F) :
      UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
        =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c]
      fun p => tv4 (zsum F (cellPt c p)) := by
    filter_upwards [cplxT_ae c hT (zsumL c mZ ρb hmZ hρ F),
      stressTransport_zsum_ae hc hT hmZ hρ F] with p a b
    rw [a, b]
  have e : (fun p => merC ((S₁ F : Chart → Merid) (cellPt c p))) =ᵐ[UnforcedLeray.B0220.measureH c]
      fun p => merC ((S₂ F : Chart → Merid) (cellPt c p)) :=
    (h₁ F _ hae).symm.trans (h₂ F _ hae)
  have e' : (fun p => (S₁ F : Chart → Merid) (cellPt c p)) =ᵐ[UnforcedLeray.B0220.measureH c]
      fun p => (S₂ F : Chart → Merid) (cellPt c p) := by
    filter_upwards [e] with p hp
    simpa [merReL_merC] using congrArg merReL hp
  have hm : AEMeasurable (cellPt c) (UnforcedLeray.B0220.measureH c) :=
    (measurable_cellPt c).aemeasurable
  have hmap : Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) =
      ENNReal.ofReal c • ageμ c (-3 / 2) := hH
  have hs1 : AEStronglyMeasurable (S₁ F : Chart → Merid)
      (Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c)) := by
    rw [hmap]; exact (Lp.aestronglyMeasurable (S₁ F)).smul_measure _
  have hs2 : AEStronglyMeasurable (S₂ F : Chart → Merid)
      (Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c)) := by
    rw [hmap]; exact (Lp.aestronglyMeasurable (S₂ F)).smul_measure _
  have k1 := hs1.ae_eq_mk
  have k2 := hs2.ae_eq_mk
  have k12 : hs1.mk _ =ᵐ[Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c)] hs2.mk _ := by
    have hmeas : MeasurableSet {x | hs1.mk _ x = hs2.mk _ x} :=
      measurableSet_eq_fun hs1.stronglyMeasurable_mk.measurable hs2.stronglyMeasurable_mk.measurable
    rw [Filter.EventuallyEq, ae_map_iff hm hmeas]
    filter_upwards [e', ae_of_ae_map hm k1, ae_of_ae_map hm k2] with p a b c'
    rw [← b, ← c', a]
  have hfin : (S₁ F : Chart → Merid) =ᵐ[Measure.map (cellPt c)
      (UnforcedLeray.B0220.measureH c)] (S₂ F : Chart → Merid) := k1.trans (k12.trans k2.symm)
  rw [hmap] at hfin
  have hne : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hfin' : (S₁ F : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] (S₂ F : Chart → Merid) := by
    simpa [Filter.EventuallyEq, Measure.ae_ennreal_smul_measure_eq hne] using hfin
  exact Lp.ext hfin'

/-! ## 2. `μ`-Lipschitz domination of the far-mask kernel `farOut` -/

private theorem neg_log_mul_rpow_le {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    (-Real.log l) * l ^ (1 / 4 : ℝ) ≤ 4 := by
  have h1 : 1 + (-Real.log l) / 4 ≤ Real.exp ((-Real.log l) / 4) := by
    linarith [Real.add_one_le_exp ((-Real.log l) / 4)]
  have h2 : Real.exp ((-Real.log l) / 4) = l ^ (-1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos hl.1]
    congr 1
    ring
  have h3 : (-Real.log l) / 4 ≤ l ^ (-1 / 4 : ℝ) := by linarith
  have h4 : 0 ≤ l ^ (1 / 4 : ℝ) := Real.rpow_nonneg hl.1.le _
  have h5 : l ^ (-1 / 4 : ℝ) * l ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hl.1]
    norm_num
  nlinarith [mul_le_mul_of_nonneg_right h3 h4]

private theorem rpow_sub_rpow_le {l μ μ' : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1)
    (hμ : 0 ≤ μ) (hμ' : 0 ≤ μ') :
    |l ^ (2 * μ + 2) - l ^ (2 * μ' + 2)| ≤ 8 * |μ - μ'| * l ^ (2 * (-1 / 8 : ℝ) + 2) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => l ^ (2 * s + 2))
      (Real.log l * 2 * l ^ (2 * t + 2)) t := by
    intro t
    have hg : HasDerivAt (fun s : ℝ => 2 * s + 2) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).add_const (2 : ℝ)
    exact hg.const_rpow hl.1
  have hbound : ∀ t ∈ Ici (0 : ℝ),
      ‖deriv (fun s : ℝ => l ^ (2 * s + 2)) t‖ ≤ 8 * l ^ (2 * (-1 / 8 : ℝ) + 2) := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    rw [(hderiv t).deriv, Real.norm_eq_abs, abs_mul, abs_mul]
    have hlpos : 0 ≤ l ^ (2 * t + 2) := Real.rpow_nonneg hl.1.le _
    have hlog : |Real.log l| = -Real.log l := abs_of_neg (Real.log_neg hl.1 hl.2)
    rw [abs_of_nonneg hlpos, show |(2 : ℝ)| = 2 by norm_num, hlog]
    have hsplit : l ^ (2 * t + 2) = l ^ (2 * (-1 / 8 : ℝ) + 2) * l ^ (2 * t + 1 / 4) := by
      rw [← Real.rpow_add hl.1]
      congr 1
      ring
    have hexp : l ^ (2 * t + 1 / 4) ≤ l ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hl.1 hl.2.le (by linarith)
    have hlog0 : 0 ≤ -Real.log l := by linarith [Real.log_neg hl.1 hl.2]
    have ha0 : 0 ≤ l ^ (2 * (-1 / 8 : ℝ) + 2) := Real.rpow_nonneg hl.1.le _
    have hstep1 : (-Real.log l) * 2 * l ^ (2 * t + 2) ≤
        l ^ (2 * (-1 / 8 : ℝ) + 2) * (2 * ((-Real.log l) * l ^ (1 / 4 : ℝ))) := by
      rw [hsplit]
      nlinarith [mul_le_mul_of_nonneg_left hexp (mul_nonneg ha0 hlog0)]
    have hstep2 := neg_log_mul_rpow_le hl
    nlinarith
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (s := Ici (0 : ℝ))
    (fun t _ => (hderiv t).differentiableAt) hbound (convex_Ici 0) hμ' hμ
  simp only [Real.norm_eq_abs] at hmvt
  linarith

private theorem cpow_two_mul_add_two {l : ℝ} (hl : 0 < l) (μ : ℝ) :
    (l : ℂ) ^ (2 * (μ : ℂ) + 2) = ((l ^ (2 * μ + 2) : ℝ) : ℂ) := by
  have he : (2 * (μ : ℂ) + 2 : ℂ) = ((2 * μ + 2 : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.ofReal_cpow hl.le]

private theorem integral_sepPhi_sub_eq (ν μ μ' : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) (i : Fin 3) (l : ℝ) :
    (∫ z : Space, (sepPhi ν (μ : ℂ) T τ i (l, z) y - sepPhi ν (μ' : ℂ) T τ i (l, z) y)) =
      (-2 * ((l : ℂ) ^ (2 * (μ : ℂ) + 2) - (l : ℂ) ^ (2 * (μ' : ℂ) + 2))) *
        farMajWz ν T y τ i l := by
  unfold farMajWz
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  unfold sepPhi
  ring

private theorem sepWfar_sub_bound (C0 ν : ℝ) (hC0 : 0 ≤ C0) (hν : 0 < ν)
    (hk : ∀ x : Space, x ≠ 0 → ∀ t : ℝ, 0 < t → ∀ i j k : Fin 3,
      ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x (coordinateVector k)‖
        ≤ C0 * ‖x‖ ^ (-4 : ℝ))
    {R c δ : ℝ} (hR : 0 < R) (hc : 0 < c) (hδ : 0 < δ) {μ μ' : ℝ} (hμ : 0 ≤ μ) (hμ' : 0 ≤ μ')
    {f : Chart → Ten3} (hf : IsBoxTensor f) {x : Chart} (hx : 0 < x.1) (i : Fin 3) :
    ENNReal.ofReal ‖sepWfar ν (μ : ℂ) R δ x.1 (cartLift R c f) (chartY R x) (chartTau R x) i -
        sepWfar ν (μ' : ℂ) R δ x.1 (cartLift R c f) (chartY R x) (chartTau R x) i‖ ≤
      ENNReal.ofReal (144 * C0 * |μ - μ'|) * farMaj R c (-1 / 8) δ f x := by
  set T := maskedLift R c δ x.1 f
  set y := chartY R x
  set τ := chartTau R x
  have hgap : R * Real.exp (-δ / 2) / Real.sqrt x.1 < hRad y := by
    rw [hRad_chartY R hR x hx]
    have hq : 0 < Real.sqrt x.1 := Real.sqrt_pos.2 hx
    have he : Real.exp (-δ / 2) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
    exact div_lt_div_of_pos_right (by nlinarith) hq
  have i1 := maskedSepPhi_integrable maskedLiftSource maskedLiftMoment R c δ x.1 ν μ
    hR hc hδ hx hν (by linarith) f hf y hgap τ i
  have i2 := maskedSepPhi_integrable maskedLiftSource maskedLiftMoment R c δ x.1 ν μ'
    hR hc hδ hx hν (by linarith) f hf y hgap τ i
  have hsub : sepWfar ν (μ : ℂ) R δ x.1 (cartLift R c f) y τ i -
      sepWfar ν (μ' : ℂ) R δ x.1 (cartLift R c f) y τ i =
      ∫ l in Ioo (0 : ℝ) 1,
        (-2 * ((l : ℂ) ^ (2 * (μ : ℂ) + 2) - (l : ℂ) ^ (2 * (μ' : ℂ) + 2))) *
          farMajWz ν T y τ i l := by
    change UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) T y τ i -
      UnforcedLeray.Short.IIIa.sepW ν (μ' : ℂ) T y τ i = _
    rw [sepW_eq_integral ν (μ : ℂ) T τ i y i1, sepW_eq_integral ν (μ' : ℂ) T τ i y i2,
      ← integral_sub i1 i2]
    have i12 : Integrable (fun p => sepPhi ν (μ : ℂ) T τ i p y - sepPhi ν (μ' : ℂ) T τ i p y)
        sepRho := i1.sub i2
    unfold sepRho at i12 ⊢
    rw [integral_prod _ i12]
    refine setIntegral_congr_fun measurableSet_Ioo fun l _ => ?_
    exact integral_sepPhi_sub_eq ν μ μ' T τ y i l
  rw [hsub, farMaj_eq_masked R c (-1 / 8) δ f x, ofReal_norm]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
  have hl0 : 0 < l := hl.1
  rw [← ofReal_norm, norm_mul, norm_mul, show ‖(-2 : ℂ)‖ = 2 by norm_num]
  have hcp : ‖(l : ℂ) ^ (2 * (μ : ℂ) + 2) - (l : ℂ) ^ (2 * (μ' : ℂ) + 2)‖ =
      |l ^ (2 * μ + 2) - l ^ (2 * μ' + 2)| := by
    rw [cpow_two_mul_add_two hl0 μ, cpow_two_mul_add_two hl0 μ', ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hcp]
  have hlip := rpow_sub_rpow_le hl hμ hμ'
  have hle1 : 2 * |l ^ (2 * μ + 2) - l ^ (2 * μ' + 2)| * ‖farMajWz ν T y τ i l‖ ≤
      (16 * |μ - μ'|) * l ^ (2 * (-1 / 8 : ℝ) + 2) * ‖farMajWz ν T y τ i l‖ := by
    have : 2 * |l ^ (2 * μ + 2) - l ^ (2 * μ' + 2)| ≤
        (16 * |μ - μ'|) * l ^ (2 * (-1 / 8 : ℝ) + 2) := by linarith
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hz := farMaj_Wz_bound C0 ν hC0 hν hk T y τ i l hl
  calc ENNReal.ofReal (2 * |l ^ (2 * μ + 2) - l ^ (2 * μ' + 2)| * ‖farMajWz ν T y τ i l‖)
      ≤ ENNReal.ofReal ((16 * |μ - μ'|) * l ^ (2 * (-1 / 8 : ℝ) + 2) * ‖farMajWz ν T y τ i l‖) :=
        ENNReal.ofReal_le_ofReal hle1
    _ = ENNReal.ofReal (16 * |μ - μ'|) * ENNReal.ofReal (l ^ (2 * (-1 / 8 : ℝ) + 2)) *
          ENNReal.ofReal ‖farMajWz ν T y τ i l‖ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (16 * |μ - μ'|) * ENNReal.ofReal (l ^ (2 * (-1 / 8 : ℝ) + 2)) *
          (ENNReal.ofReal (9 * C0) *
            ∫⁻ z : Space, ENNReal.ofReal (‖y - l • z‖ ^ (-4 : ℝ) *
              UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z))) := by
        gcongr
    _ = ENNReal.ofReal (144 * C0 * |μ - μ'|) * (ENNReal.ofReal (l ^ (2 * (-1 / 8 : ℝ) + 2)) *
          ∫⁻ z : Space, ENNReal.ofReal (‖y - l • z‖ ^ (-4 : ℝ) *
            UnforcedLeray.Short.IIIa.tensorNorm (T (τ + 2 * Real.log l) z))) := by
        have e : ENNReal.ofReal (16 * |μ - μ'|) * ENNReal.ofReal (9 * C0) =
            ENNReal.ofReal (144 * C0 * |μ - μ'|) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
        rw [← e]
        ring

private theorem farOut_sub_majorant (C0 ν : ℝ) (hC0 : 0 ≤ C0) (hν : 0 < ν)
    (hk : ∀ x : Space, x ≠ 0 → ∀ t : ℝ, 0 < t → ∀ i j k : Fin 3,
      ‖fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x (coordinateVector k)‖
        ≤ C0 * ‖x‖ ^ (-4 : ℝ))
    {R c δ S : ℝ} (hR : 0 < R) (hc : 0 < c) (hδ : 0 < δ) {μ μ' : ℝ} (hμ : 0 ≤ μ) (hμ' : 0 ≤ μ')
    {f : Chart → Ten3} (hf : IsBoxTensor f) {x : Chart} (hx : 0 < x.1) :
    ENNReal.ofReal ‖farOut R c ν μ δ S f x - farOut R c ν μ' δ S f x‖ ≤
      ENNReal.ofReal (288 * C0 * |μ - μ'|) * farMajOut R c (-1 / 8) δ S f x := by
  unfold farOut farMajOut
  by_cases hxS : x.1 < S
  · simp only [hxS, ite_true]
    set W := sepWfar ν (μ : ℂ) R δ x.1 (cartLift R c f) (chartY R x) (chartTau R x)
    set W' := sepWfar ν (μ' : ℂ) R δ x.1 (cartLift R c f) (chartY R x) (chartTau R x)
    have hsub : (Real.sqrt x.1)⁻¹ • merRe (-W) - (Real.sqrt x.1)⁻¹ • merRe (-W') =
        (Real.sqrt x.1)⁻¹ • merRe (-(W - W')) := by
      rw [← smul_sub]
      congr 1
      have h := merRe_neg_add_smul W W' (-1 : ℝ)
      simpa [sub_eq_add_neg] using h.symm
    have hsqrt : 0 ≤ (Real.sqrt x.1)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    rw [hsub, norm_smul, Real.norm_of_nonneg hsqrt, ENNReal.ofReal_mul hsqrt]
    have hW0 := sepWfar_sub_bound C0 ν hC0 hν hk hR hc hδ hμ hμ' hf hx 0
    have hW2 := sepWfar_sub_bound C0 ν hC0 hν hk hR hc hδ hμ hμ' hf hx 2
    have hm : ENNReal.ofReal ‖merRe (-(W - W'))‖ ≤
        2 * (ENNReal.ofReal (144 * C0 * |μ - μ'|) * farMaj R c (-1 / 8) δ f x) := by
      calc ENNReal.ofReal ‖merRe (-(W - W'))‖
          ≤ ENNReal.ofReal (‖(-(W - W')) 0‖ + ‖(-(W - W')) 2‖) :=
            ENNReal.ofReal_le_ofReal (farMaj_merRe_norm_le _)
        _ ≤ ENNReal.ofReal ‖(-(W - W')) 0‖ + ENNReal.ofReal ‖(-(W - W')) 2‖ :=
            ENNReal.ofReal_add_le
        _ ≤ _ := by
            rw [Pi.neg_apply, Pi.neg_apply, norm_neg, norm_neg, Pi.sub_apply, Pi.sub_apply, two_mul]
            exact add_le_add hW0 hW2
    calc ENNReal.ofReal (Real.sqrt x.1)⁻¹ * ENNReal.ofReal ‖merRe (-(W - W'))‖
        ≤ ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
            (2 * (ENNReal.ofReal (144 * C0 * |μ - μ'|) * farMaj R c (-1 / 8) δ f x)) := by gcongr
      _ = ENNReal.ofReal (288 * C0 * |μ - μ'|) *
            (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * farMaj R c (-1 / 8) δ f x) := by
          have e : ENNReal.ofReal (288 * C0 * |μ - μ'|) =
              2 * ENNReal.ofReal (144 * C0 * |μ - μ'|) := by
            rw [show (288 * C0 * |μ - μ'|) = 2 * (144 * C0 * |μ - μ'|) by ring,
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
          rw [e]; ring
  · simp only [hxS, ite_false, sub_self, norm_zero, ENNReal.ofReal_zero]
    exact zero_le

/-- `L²` `μ`-Lipschitz bound of `farOut` on box tensors for `μ, μ' ≥ 0` (source 3604-3621,
3902-3912, 5701-5704). -/
theorem farOut_sub_l2 {R c ν δ S : ℝ} (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν) (hδ : 0 < δ)
    (hS : 0 < S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ μ' : ℝ}, 0 ≤ μ → 0 ≤ μ' → ∀ f : Chart → Ten3, IsBoxTensor f →
      eLpNorm (farOut R c ν μ δ S f - farOut R c ν μ' δ S f) 2 (ageμ c (-3 / 2)) ≤
        ENNReal.ofReal (C * |μ - μ'|) * eLpNorm f 2 (ageμ c (-1 / 2)) := by
  obtain ⟨C0, hC0, hk⟩ := farMaj_kernel_bound UnforcedLeray.Short.IIIa.sepKernelBounds
  obtain ⟨C2, hC2, hl⟩ := _root_.farMajL2 R c δ S (-1 / 8) hR hc hδ hS (by norm_num)
  refine ⟨288 * C0 * C2, by positivity, fun {μ μ'} hμ hμ' f hf => ?_⟩
  set C1 := 288 * C0 * |μ - μ'|
  have hC1 : 0 ≤ C1 := by positivity
  have hp : (0 : ℝ) < 2 := by norm_num
  have key : ∫⁻ x, ‖(farOut R c ν μ δ S f - farOut R c ν μ' δ S f) x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) ≤
      (ENNReal.ofReal C1 * ENNReal.ofReal C2) ^ (2 : ℝ) *
        ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) := by
    calc ∫⁻ x, ‖(farOut R c ν μ δ S f - farOut R c ν μ' δ S f) x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-3 / 2))
        ≤ ∫⁻ x, (ENNReal.ofReal C1) ^ (2 : ℝ) * (farMajOut R c (-1 / 8) δ S f x) ^ (2 : ℝ)
            ∂(ageμ c (-3 / 2)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [UnforcedLeray.Short.IIIa.ae_pos_ageμ c (-3 / 2)] with x hx
          rw [Pi.sub_apply, ← ofReal_norm, ← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
          exact ENNReal.rpow_le_rpow (farOut_sub_majorant C0 ν hC0 hν hk hR hc hδ hμ hμ' hf hx) hp.le
      _ = (ENNReal.ofReal C1) ^ (2 : ℝ) *
            ∫⁻ x, (farMajOut R c (-1 / 8) δ S f x) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      _ ≤ (ENNReal.ofReal C1) ^ (2 : ℝ) *
            (ENNReal.ofReal C2 ^ (2 : ℝ) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2))) := by
          gcongr; exact hl f hf
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, mul_assoc]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  calc (∫⁻ x, ‖(farOut R c ν μ δ S f - farOut R c ν μ' δ S f) x‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2))) ^ (1 / (2 : ℝ))
      ≤ ((ENNReal.ofReal C1 * ENNReal.ofReal C2) ^ (2 : ℝ) *
        ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2))) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow key (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num
        rw [← ENNReal.ofReal_mul hC1]
        congr 2
        ring

/-! ## 3. Operator-norm continuity of `S_far` and `S_N` -/

/-- An operator `X : Z → H` bounded by `B` on box tensors has `‖X‖ ≤ B * ‖zsumL‖`
(by `boxDenseZ`). -/
theorem opNorm_le_mul_zsumL_of_box {c mZ ρb : ℝ} (hc : 0 < c) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb)
    (X : Zsp c mZ ρb →L[ℝ] Hsp c) {B : ℝ} (hB : 0 ≤ B)
    (hX : ∀ (F : Zsp c mZ ρb) (f : Chart → Ten3), IsBoxTensor f →
      zsum F =ᵐ[ageμ c (-1 / 2)] f →
        eLpNorm (X F : Chart → Merid) 2 (ageμ c (-3 / 2)) ≤
          ENNReal.ofReal B * eLpNorm f 2 (ageμ c (-1 / 2))) :
    ‖X‖ ≤ B * ‖zsumL c mZ ρb hmZ hρ‖ := by
  have hbox : ∀ G : Zsp c mZ ρb, (∃ f : Chart → Ten3, IsBoxTensor f ∧
      zsum G =ᵐ[ageμ c (-1 / 2)] f) → ‖X G‖ ≤ (B * ‖zsumL c mZ ρb hmZ hρ‖) * ‖G‖ := by
    rintro G ⟨f, hf, hGf⟩
    have hfz : eLpNorm f 2 (ageμ c (-1 / 2)) =
        eLpNorm (zsumL c mZ ρb hmZ hρ G : Chart → Ten3) 2 (ageμ c (-1 / 2)) :=
      (eLpNorm_congr_ae ((zsumL_ae c mZ ρb hmZ hρ G).trans hGf)).symm
    have hA := hX G f hf hGf
    have hfin : eLpNorm f 2 (ageμ c (-1 / 2)) ≠ ⊤ := by
      rw [hfz]; exact Lp.eLpNorm_ne_top _
    have hmono : (eLpNorm (X G : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal ≤
        (ENNReal.ofReal B * eLpNorm f 2 (ageμ c (-1 / 2))).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hA
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] at hmono
    rw [Lp.norm_def (X G)]
    calc (eLpNorm (X G : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal
        ≤ B * (eLpNorm f 2 (ageμ c (-1 / 2))).toReal := hmono
      _ = B * ‖zsumL c mZ ρb hmZ hρ G‖ := by rw [Lp.norm_def (zsumL c mZ ρb hmZ hρ G), hfz]
      _ ≤ B * (‖zsumL c mZ ρb hmZ hρ‖ * ‖G‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hB
      _ = (B * ‖zsumL c mZ ρb hmZ hρ‖) * ‖G‖ := (mul_assoc _ _ _).symm
  refine ContinuousLinearMap.opNorm_le_bound X (mul_nonneg hB (norm_nonneg _)) fun F => ?_
  have hcl : F ∈ closure {G : Zsp c mZ ρb |
      ∃ f : Chart → Ten3, IsBoxTensor f ∧ zsum G =ᵐ[ageμ c (-1 / 2)] f} := by
    rw [Metric.mem_closure_iff]
    intro η hη
    obtain ⟨G, hG, hn⟩ := boxDenseZ c mZ ρb hc hmZ hρ F η hη
    exact ⟨G, hG, by rwa [dist_eq_norm]⟩
  have hclosed : IsClosed {G : Zsp c mZ ρb | ‖X G‖ ≤ (B * ‖zsumL c mZ ρb hmZ hρ‖) * ‖G‖} :=
    isClosed_le (continuous_norm.comp X.continuous) (continuous_const.mul continuous_norm)
  exact closure_minimal (fun G hG => hbox G hG) hclosed hcl

/-- A family `Sf` satisfying `IsFarMask R ν μ δ S (Sf μ)` on `W ⊆ [0, ∞)` is operator-norm
continuous on `W`. -/
theorem isFarMask_continuousOn {c mZ ρb R ν δ S : ℝ} (hc : 0 < c) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb)
    (hR : 0 < R) (hν : 0 < ν) (hδ : 0 < δ) (hS : 0 < S) {W : Set ℝ} (hW : W ⊆ Ici 0)
    {Sf : ℝ → (Zsp c mZ ρb →L[ℝ] Hsp c)}
    (hfar : ∀ μ ∈ W, IsFarMask R ν μ δ S (Sf μ)) :
    ContinuousOn Sf W := by
  obtain ⟨C, hC0, hC⟩ := farOut_sub_l2 hR hc hν hδ hS
  intro μ0 hμ0
  set Lc := C * ‖zsumL c mZ ρb hmZ hρ‖
  have hLc0 : 0 ≤ Lc := mul_nonneg hC0 (norm_nonneg _)
  have hbound : ∀ μ ∈ W, ‖Sf μ - Sf μ0‖ ≤ Lc * |μ - μ0| := by
    intro μ hμ
    have h1 := opNorm_le_mul_zsumL_of_box hc hmZ hρ (Sf μ - Sf μ0)
      (mul_nonneg hC0 (abs_nonneg (μ - μ0))) fun F f hf hFf => by
        have hae1 := (isFarMask_iff R ν μ δ S (Sf μ)).1 (hfar μ hμ) F f hf hFf
        have hae0 := (isFarMask_iff R ν μ0 δ S (Sf μ0)).1 (hfar μ0 hμ0) F f hf hFf
        have hsub := Lp.coeFn_sub (Sf μ F) (Sf μ0 F)
        have hae : (((Sf μ - Sf μ0) F : Hsp c) : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
            farOut R c ν μ δ S f - farOut R c ν μ0 δ S f := by
          filter_upwards [hsub, hae1, hae0] with p hp hp1 hp0
          change ((Sf μ F - Sf μ0 F : Hsp c) : Chart → Merid) p = _
          rw [hp, Pi.sub_apply, hp1, hp0, Pi.sub_apply]
        rw [eLpNorm_congr_ae hae]
        exact hC (hW hμ) (hW hμ0) f hf
    calc ‖Sf μ - Sf μ0‖
        ≤ (C * |μ - μ0|) * ‖zsumL c mZ ρb hmZ hρ‖ := h1
      _ = Lc * |μ - μ0| := by ring
  have hT : Tendsto (fun μ : ℝ => Lc * |μ - μ0|) (𝓝[W] μ0) (𝓝 0) := by
    have hcont : Continuous (fun μ : ℝ => Lc * |μ - μ0|) :=
      continuous_const.mul (continuous_id.sub continuous_const).abs
    have hz : Lc * |μ0 - μ0| = 0 := by simp
    rw [← hz]
    exact (hcont.tendsto μ0).mono_left nhdsWithin_le_nhds
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall hbound) hT)

/-- **`NearSNCont`** on the concrete sequence (source 3888-3920, 5684-5685, 5701-5704, 5918-5920). -/
theorem SeqData.nearSNCont (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.NearSNCont := by
  have hF : StressMapFamilyCont :=
    stressMapFamilyCont_of UnforcedLeray.Short.PartIIa.nearStressMapExists
      (stressMapUnique_of tensorTestDense tensorTestDivMem)
      (stressMapResolvent tensorTestDense tensorTestDivMem)
  have hR : StressMapReal :=
    stressMapReal_of Body.tepsReal' tensorTestDense tensorTestDivMem
  have hUn : StressMapUnique :=
    stressMapUnique_of tensorTestDense tensorTestDivMem
  filter_upwards [inv_seq_large D hst.dm_pos hst.omega_ne hst.sigma_pos hst.sigma_lt hst.actual,
    hst.pins] with n hn hp
  obtain ⟨-, hper, hε1', hμ⟩ := hn
  set L := D.level n
  have hε1 : L.ε ≤ 1 := hε1'
  have hmZ : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  have hρ : 0 < L.ρb D.Pl D.K := inv_rhoB_pos hst.C0_pos
  have hc := cOf_pos L.ν_pos
  have hwin0 : D.win n ⊆ Ici (0 : ℝ) := by
    rintro _ ⟨z, hz, rfl⟩
    have := (hμ z hz).1
    change 0 ≤ D.mu n z
    linarith [hst.sigma_pos]
  have hwin : ∀ μ ∈ D.win n, -(1 / 4 : ℝ) < μ := fun μ hμw => by
    have : 0 ≤ μ := hwin0 hμw
    linarith
  obtain ⟨S', hSc, hS'⟩ := hF (L.params D.Pl) hε1 hper
  set SepsFam : ℝ → (Zsp (cOf L.ν) D.K.mZ (L.ρb D.Pl D.K) →L[ℝ] Hsp (cOf L.ν)) :=
    fun μ => realForm (cOf L.ν) D.K.mZ (L.ρb D.Pl D.K) hmZ hρ (cpcHT_eq _ hc) (cpcInvH_eq _ hc)
      (S' μ)
  have hSepsCont : ContinuousOn SepsFam (D.win n) :=
    realForm_continuousOn hmZ hρ (cpcHT_eq _ hc) (cpcInvH_eq _ hc)
      (hSc.mono (fun μ hμw => hwin μ hμw : D.win n ⊆ Ioi _))
  set SfFam : ℝ → (Zsp (cOf L.ν) D.K.mZ (L.ρb D.Pl D.K) →L[ℝ] Hsp (cOf L.ν)) :=
    fun μ => SepsFam μ - (nearOpsAt D.Pl D.K L μ).SN
  have hSfPin : ∀ μ ∈ D.win n,
      IsFarMask (L.params D.Pl).R (L.params D.Pl).ν μ D.K.δ (L.Scut D.K) (SfFam μ) := by
    rintro _ ⟨z, hz, rfl⟩
    have hnear := (nearOpsAt_spec (hp z hz).near).1.near
    obtain ⟨Seps, Sf, Seps', hmap, htr, hfar, hSN⟩ := hnear
    have hlt := hwin _ (D.mu_mem_win hz)
    have hS'eq : Seps' = S' (D.mu n z) :=
      hUn (L.params D.Pl).c (L.params D.Pl).ε _ Seps' (S' (D.mu n z)) hc hmap (hS' _ hlt)
    rw [hS'eq] at htr
    have hreal := hR (L.params D.Pl).ν (L.params D.Pl).ε (L.params D.Pl).c
      (L.params D.Pl).period (L.params D.Pl).ν_pos (L.params D.Pl).ε_pos (L.params D.Pl).c_pos rfl
      (D.mu n z) hlt (S' (D.mu n z)) (hS' _ hlt)
    have htr2 := isStressTransport_realForm (mZ := D.K.mZ) (ρb := L.ρb D.Pl D.K)
      hmZ hρ (cpcHT_eq _ hc) (cpcInvH_eq _ hc) (cpcH_eq _ hc) (S' (D.mu n z)) hreal
    have hSepsEq : Seps = SepsFam (D.mu n z) := isStressTransport_unique hc hmZ hρ htr htr2
    have hSfEq : SfFam (D.mu n z) = Sf := by
      dsimp [SfFam]
      rw [← hSepsEq, hSN]
      abel
    rwa [hSfEq]
  have hScut : 0 < L.Scut D.K := Real.rpow_pos_of_pos L.ε_pos _
  have hSfCont : ContinuousOn SfFam (D.win n) :=
    isFarMask_continuousOn hc hmZ hρ (L.params D.Pl).R_pos (L.params D.Pl).ν_pos hst.δ_pos hScut
      hwin0 hSfPin
  have hSNCont : ContinuousOn (fun μ => SepsFam μ - SfFam μ) (D.win n) :=
    hSepsCont.sub hSfCont
  refine hSNCont.congr fun μ _ => ?_
  dsimp [SfFam]
  exact (sub_sub_cancel _ _).symm

end UnforcedLeray.Short.PartIIIb.Concrete
