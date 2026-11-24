import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5
import Mathlib.MeasureTheory.Integral.MeanInequalities
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollLoc

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

theorem mollYoung_cell_translate (c t : ℝ) (hc : 0 < c) (φ : ℝ → ℝ≥0∞) (hφm : Measurable φ)
    (hφ : ∀ x, φ (x + c) = φ x) :
    ∫⁻ q in Ico (-c / 2) (c / 2), φ (q - t) = ∫⁻ q in Ico (-c / 2) (c / 2), φ q := by
  have hmp : MeasurePreserving (fun q : ℝ => q - t) volume volume := measurePreserving_sub_right volume t
  have h1 : ∫⁻ q in Ico (-c / 2) (c / 2), φ (q - t)
      = ∫⁻ y in Ico (-c / 2 - t) (c / 2 - t), φ y := by
    have := hmp.setLIntegral_comp_preimage (s := Ico (-c / 2 - t) (c / 2 - t)) measurableSet_Ico hφm
    rw [← this]
    congr 2
    ext q
    simp only [mem_preimage, mem_Ico]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [h1]
  have hper : ∀ (g : AddSubgroup.zmultiples c) (x : ℝ), φ (g +ᵥ x) = φ x := by
    intro g x
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 g.2
    have : (g : ℝ) = n • c := hn.symm
    show φ ((g : ℝ) + x) = φ x
    have hp : Function.Periodic φ c := hφ
    rw [this, add_comm]
    simpa using (hp.zsmul n) x
  have e1 : ∫⁻ y in Ico (-c / 2 - t) (c / 2 - t), φ y = ∫⁻ y in Ioc (-c / 2 - t) (-c / 2 - t + c), φ y := by
    rw [show -c / 2 - t + c = c / 2 - t by ring]
    exact setLIntegral_congr Ico_ae_eq_Ioc
  have e2 : ∫⁻ y in Ico (-c / 2) (c / 2), φ y = ∫⁻ y in Ioc (-c / 2) (-c / 2 + c), φ y := by
    rw [show -c / 2 + c = c / 2 by ring]
    exact setLIntegral_congr Ico_ae_eq_Ioc
  rw [e1, e2]
  exact (isAddFundamentalDomain_Ioc hc (-c / 2 - t)).setLIntegral_eq
    (isAddFundamentalDomain_Ioc hc (-c / 2)) φ hper


theorem mollYoung_avg_translate (c : ℝ) (hc : 0 < c) (H : ℝ × ℝ → ℝ≥0∞) (hHm : Measurable H)
    (hH : ∀ q η, H (q + c, η) = H (q, η)) (a b : ℝ) :
    ∫⁻ w, H (w.1 - a, w.2 - b) ∂(UnforcedLeray.Cyl.avgμ c) = ∫⁻ w, H w ∂(UnforcedLeray.Cyl.avgμ c) := by
  rw [UnforcedLeray.Cyl.lintegral_avgμ, UnforcedLeray.Cyl.lintegral_avgμ]
  congr 1
  have hm1 : Measurable (fun w : ℝ × ℝ => H (w.1 - a, w.2 - b)) :=
    hHm.comp ((measurable_fst.sub_const a).prodMk (measurable_snd.sub_const b))
  rw [UnforcedLeray.Cyl.lintegral_cell_eq hm1.aemeasurable,
    UnforcedLeray.Cyl.lintegral_cell_eq hHm.aemeasurable]
  have hin : ∀ q, ∫⁻ η, H (q - a, η - b) = ∫⁻ η, H (q - a, η) := fun q =>
    lintegral_sub_right_eq_self (fun η => H (q - a, η)) b
  simp_rw [hin]
  have hφm : Measurable (fun q : ℝ => ∫⁻ η, H (q, η)) :=
    hHm.lintegral_prod_right'
  have hφ : ∀ q : ℝ, (fun q : ℝ => ∫⁻ η, H (q, η)) (q + c) = (fun q : ℝ => ∫⁻ η, H (q, η)) q := by
    intro q; simp only [hH]
  exact mollYoung_cell_translate c a hc _ hφm hφ

theorem mollYoung_transl_core (c : ℝ) (hc : 0 < c) (G : Coord → ℝ≥0∞) (hGm : Measurable G)
    (hG : ∀ s q η, G (s, q + c, η) = G (s, q, η)) (z : Coord) :
    ∫⁻ x, G (x - z) ∂(cylMeas c) = ∫⁻ x, G x ∂(cylMeas c) := by
  unfold cylMeas
  have hm1 : Measurable (fun x : Coord => G (x - z)) := hGm.comp (measurable_id.sub_const z)
  rw [lintegral_prod _ hm1.aemeasurable, lintegral_prod _ hGm.aemeasurable]
  have h1 : ∀ s : ℝ, ∫⁻ w, G (((s, w) : Coord) - z) ∂(UnforcedLeray.Cyl.avgμ c)
      = ∫⁻ w, G (s - z.1, w) ∂(UnforcedLeray.Cyl.avgμ c) := by
    intro s
    exact mollYoung_avg_translate c hc (fun w => G (s - z.1, w))
      (hGm.comp (measurable_const.prodMk measurable_id)) (fun q η => hG _ q η) z.2.1 z.2.2
  simp_rw [h1]
  exact lintegral_sub_right_eq_self (fun s => ∫⁻ w, G (s, w) ∂(UnforcedLeray.Cyl.avgμ c)) z.1

theorem mollYoung_holder {α : Type*} [MeasurableSpace α] (μ : Measure α) (r : ℝ) (hr : 1 < r)
    (w a : α → ℝ≥0∞) (hw : Measurable w) (ha : Measurable a) :
    (∫⁻ z, a z * w z ∂μ) ^ r ≤ (∫⁻ z, w z ∂μ) ^ (r - 1) * ∫⁻ z, a z ^ r * w z ∂μ := by
  have hq : r.HolderConjugate (Real.conjExponent r) := Real.HolderConjugate.conjExponent hr
  set q := Real.conjExponent r with hqdef
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < q := hq.symm.pos
  have hinv : 1 / r + 1 / q = 1 := by
    have := hq.inv_add_inv_eq_one
    simpa [one_div] using this
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hq
    (f := fun z => a z * w z ^ (1 / r)) (g := fun z => w z ^ (1 / q))
    ((ha.mul (hw.pow_const _)).aemeasurable) ((hw.pow_const _).aemeasurable)
  have e1 : ∀ z, (a z * w z ^ (1 / r)) * w z ^ (1 / q) = a z * w z := by
    intro z
    rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hinv,
      ENNReal.rpow_one]
  have e2 : ∀ z, (a z * w z ^ (1 / r)) ^ r = a z ^ r * w z := by
    intro z
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul]
    field_simp
    simp
  have e3 : ∀ z, (w z ^ (1 / q)) ^ q = w z := by
    intro z
    rw [← ENNReal.rpow_mul]
    field_simp
    simp
  simp only [Pi.mul_apply, e1, e2, e3] at hH
  have hr1 : (1 / r) * r = 1 := by field_simp
  calc (∫⁻ z, a z * w z ∂μ) ^ r
      ≤ ((∫⁻ z, a z ^ r * w z ∂μ) ^ (1 / r) * (∫⁻ z, w z ∂μ) ^ (1 / q)) ^ r :=
        ENNReal.rpow_le_rpow hH hr0.le
    _ = (∫⁻ z, a z ^ r * w z ∂μ) * (∫⁻ z, w z ∂μ) ^ (r - 1) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hr1,
          ENNReal.rpow_one]
        congr 2
        have : r - 1 = r / q := by
          have h2 : 1 / q = 1 - 1 / r := by linarith
          field_simp at h2 ⊢
          nlinarith
        rw [this]; ring
    _ = _ := mul_comm _ _

theorem mollYoung_core (c r : ℝ) (hc : 0 < c) (hr : 1 < r) (κ : Coord → ℝ) (f : Coord → ℂ)
    (hκ : IsKer κ) (hfm : Measurable f) (hper : ∀ s q η, f (s, q + c, η) = f (s, q, η)) :
    eLpNorm (convK κ f) (ENNReal.ofReal r) (cylMeas c) ≤
      ENNReal.ofReal (∫ x, |κ x|) * eLpNorm f (ENNReal.ofReal r) (cylMeas c) := by
  have hr0 : 0 < r := by linarith
  have hp0 : ENNReal.ofReal r ≠ 0 := by simpa using hr0
  have hptop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpt : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop,
    hpt]
  have hκc : Continuous κ := hκ.1.continuous
  have hint : Integrable (fun x => |κ x|) volume := (hκc.integrable_of_hasCompactSupport hκ.2).abs
  set w : Coord → ℝ≥0∞ := fun z => ENNReal.ofReal |κ z| with hwdef
  have hwm : Measurable w := ENNReal.measurable_ofReal.comp hκc.abs.measurable
  set m : ℝ≥0∞ := ∫⁻ z, w z with hmdef
  have hm : ENNReal.ofReal (∫ x, |κ x|) = m :=
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => abs_nonneg _)
  have hmtop : m ≠ ⊤ := by rw [← hm]; exact ENNReal.ofReal_ne_top
  set Nf : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ r ∂(cylMeas c) with hNf
  have hGm : Measurable (fun x : Coord => ‖f x‖ₑ ^ r) := hfm.enorm.pow_const r
  have hpoint : ∀ x : Coord, ‖convK κ f x‖ₑ ^ r ≤
      m ^ (r - 1) * ∫⁻ z, ‖f (x - z)‖ₑ ^ r * w z := by
    intro x
    have h1 : ‖convK κ f x‖ₑ ≤ ∫⁻ z, ‖f (x - z)‖ₑ * w z := by
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      have e : ∀ y, ‖f y * (κ (x - y) : ℂ)‖ₑ = ‖f y‖ₑ * ENNReal.ofReal |κ (x - y)| := by
        intro y
        rw [enorm_mul]
        congr 1
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
      simp_rw [e]
      have := lintegral_sub_left_eq_self (μ := (volume : Measure Coord))
        (fun y => ‖f y‖ₑ * ENNReal.ofReal |κ (x - y)|) x
      simp only [sub_sub_cancel] at this
      exact this.ge
    refine (ENNReal.rpow_le_rpow h1 hr0.le).trans ?_
    exact mollYoung_holder volume r hr w (fun z => ‖f (x - z)‖ₑ) hwm
      (hfm.comp (measurable_const.sub measurable_id)).enorm
  have hm' : ENNReal.ofReal (∫ x, |κ x|) = m := hm
  rw [hm']
  have hprodm : Measurable (fun p : Coord × Coord => ‖f (p.1 - p.2)‖ₑ ^ r * w p.2) :=
    ((hfm.comp (measurable_fst.sub measurable_snd)).enorm.pow_const r).mul (hwm.comp measurable_snd)
  have : SFinite (cylMeas c) := by
    unfold cylMeas UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    infer_instance
  have hswap : ∫⁻ x, ∫⁻ z, ‖f (x - z)‖ₑ ^ r * w z ∂(volume : Measure Coord) ∂(cylMeas c)
      = Nf * m := by
    rw [lintegral_lintegral_swap hprodm.aemeasurable]
    have : ∀ z : Coord, ∫⁻ x, ‖f (x - z)‖ₑ ^ r * w z ∂(cylMeas c) = Nf * w z := by
      intro z
      have hmz : Measurable (fun x : Coord => ‖f (x - z)‖ₑ ^ r) :=
        (hfm.comp (measurable_id.sub_const z)).enorm.pow_const r
      rw [lintegral_mul_const _ hmz]
      congr 1
      exact mollYoung_transl_core c hc (fun x => ‖f x‖ₑ ^ r) hGm
        (fun s q η => by simp only [hper]) z
    simp_rw [this]
    exact lintegral_const_mul Nf hwm
  have hmain : ∫⁻ x, ‖convK κ f x‖ₑ ^ r ∂(cylMeas c) ≤ m ^ r * Nf := by
    calc ∫⁻ x, ‖convK κ f x‖ₑ ^ r ∂(cylMeas c)
        ≤ ∫⁻ x, m ^ (r - 1) * (∫⁻ z, ‖f (x - z)‖ₑ ^ r * w z) ∂(cylMeas c) := lintegral_mono hpoint
      _ = m ^ (r - 1) * ∫⁻ x, ∫⁻ z, ‖f (x - z)‖ₑ ^ r * w z ∂(volume : Measure Coord) ∂(cylMeas c) :=
          lintegral_const_mul' (m ^ (r - 1)) _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hmtop)
      _ = m ^ (r - 1) * (Nf * m) := by rw [hswap]
      _ = m ^ r * Nf := by
          have : m ^ r = m ^ (r - 1) * m := by
            conv_lhs => rw [show r = (r - 1) + 1 by ring]
            rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
          rw [this]; ring
  calc (∫⁻ x, ‖convK κ f x‖ₑ ^ r ∂(cylMeas c)) ^ (1 / r)
      ≤ (m ^ r * Nf) ^ (1 / r) := ENNReal.rpow_le_rpow hmain (by positivity)
    _ = m * Nf ^ (1 / r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
        have : r * (1 / r) = 1 := by field_simp
        rw [this, ENNReal.rpow_one]

theorem mollYoung_cylMeas_ac (c : ℝ) : cylMeas c ≪ (volume : Measure Coord) := by
  have h1 : UnforcedLeray.Cyl.avgμ c ≪ (volume : Measure (ℝ × ℝ)) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    exact Measure.smul_absolutelyContinuous.trans Measure.restrict_le_self.absolutelyContinuous
  unfold cylMeas
  rw [Measure.volume_eq_prod]
  exact Measure.AbsolutelyContinuous.prod (Measure.AbsolutelyContinuous.rfl) h1

/-- The pointwise `c`-periodic reduction `(s, q, η) ↦ (s, c·fract(q/c), η)`. -/
def mollYoungRed (c : ℝ) (x : Coord) : Coord := (x.1, (c * Int.fract (x.2.1 / c), x.2.2))

theorem mollYoungRed_measurable (c : ℝ) : Measurable (mollYoungRed c) := by
  unfold mollYoungRed
  exact measurable_fst.prodMk
    (((measurable_const.mul (measurable_fract.comp (measurable_fst.comp measurable_snd |>.div_const c))))
      |>.prodMk (measurable_snd.comp measurable_snd))

theorem mollYoungRed_eq (c : ℝ) (hc : 0 < c) (x : Coord) :
    mollYoungRed c x = qShift (((-⌊x.2.1 / c⌋ : ℤ) : ℝ) * c) x := by
  unfold mollYoungRed qShift
  have : c * Int.fract (x.2.1 / c) = x.2.1 + ((-⌊x.2.1 / c⌋ : ℤ) : ℝ) * c := by
    rw [Int.fract]; push_cast; field_simp; ring
  rw [this]

theorem mollYoung_proof : UnforcedLeray.Short.IIb.MollYoung := by
  intro c r hc hr κ f hκ hper hfm
  have hr0 : 0 < r := by linarith
  set g : Coord → ℂ := hfm.mk f with hg
  have hgs : StronglyMeasurable g := hfm.stronglyMeasurable_mk
  have hfg : f =ᵐ[volume] g := hfm.ae_eq_mk
  have hgper : ∀ᵐ x : Coord, g (qShift c x) = g x := by
    have h1 : ∀ᵐ x : Coord, f (qShift c x) = g (qShift c x) :=
      (mollLoc_mp c).quasiMeasurePreserving.ae hfg
    filter_upwards [h1, hper, hfg] with x h1 h2 h3
    rw [← h1, h2, h3]
  have hall : ∀ᵐ x : Coord, ∀ k : ℤ, g (qShift ((k : ℝ) * c) x) = g x :=
    ae_all_iff.2 (fun k => mollLoc_ae_int hgper k)
  set gh : Coord → ℂ := fun x => g (mollYoungRed c x) with hgh
  have hghm : Measurable gh := hgs.measurable.comp (mollYoungRed_measurable c)
  have hghg : gh =ᵐ[volume] g := by
    filter_upwards [hall] with x hx
    show g (mollYoungRed c x) = g x
    rw [mollYoungRed_eq c hc x]
    exact hx _
  have hghf : gh =ᵐ[volume] f := hghg.trans hfg.symm
  have hper' : ∀ s q η, gh (s, q + c, η) = gh (s, q, η) := by
    intro s q η
    show g (mollYoungRed c (s, q + c, η)) = g (mollYoungRed c (s, q, η))
    unfold mollYoungRed
    simp only
    rw [show (q + c) / c = q / c + 1 by field_simp, Int.fract_add_one]
  have hac := mollYoung_cylMeas_ac c
  have hconv : convK κ f = convK κ gh := by
    funext x
    unfold convK
    refine integral_congr_ae ?_
    filter_upwards [hghf] with y hy
    rw [hy]
  have hnorm : eLpNorm f (ENNReal.ofReal r) (cylMeas c) = eLpNorm gh (ENNReal.ofReal r) (cylMeas c) :=
    eLpNorm_congr_ae (hac.ae_le hghf.symm)
  rw [hconv, hnorm]
  exact mollYoung_core c r hc hr κ gh hκ hghm hper'

end UnforcedLeray.Short.IIb
