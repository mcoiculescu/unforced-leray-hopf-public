import UnforcedLeray.Short.PartIIb.Sub.FlatInverseDesign
import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy
import UnforcedLeray.Short.PartIIb.Tasks.HardySingular

/-!
# Part II-b, task `PartII-b:F8`: Local `H¹ → H²` smoothing and `s B_v z` bound (`LocalSmoothing`, SP 2296–2312)

Source of record: `the November 2 reference manuscript`
(SP), lines 2296–2312 (Section `Local smoothing and the s B_v z bound`).

For the meridional correction equation `∂_s z + B_v z - ν Δ_{q,η} z = g` on `C_c`, higher-order
cylinder energy estimates `E_j' + ν E_{j+1} ≤ C ∑_{i ≤ j} E_i` (`j ≤ 2`, `E_j = ‖D^j z‖_{L²(C_c)}²`)
give `H¹ → H²` smoothing norm `C [ν(t - s)]^{-1/2}` for `t - s ≤ 1`.
1. On `(0, T]` (`T = p.H = Σ / ν`), Duhamel from `s = 0` and the singular Hardy inequality
   `hardySingular_proof : HardySingular` (`PartII-b:T04`) bound `z` in `L^p((0, T], s^{13/8} ds; H²)`.
2. On `(T, ∞)` (`T ≥ 2`), Duhamel on the unit interval `[s - 1, s]` gives
   `‖z(s)‖_{H²} ≤ C ν^{-1/2} M_z + C ν^{-1/2} ∫_0^1 r^{-1/2} ‖g(s - r)‖_{H¹} dr`.
   Since `(s - r)^{-9/8} ≥ s^{-9/8}` for `r ∈ (0, 1)` and `∫_0^1 r^{-1/2} dr = 2`, Minkowski's
   integral inequality (`minkowski_lintegral_rpow`, `PartII-b:T02`) in `L^p((T, ∞), s^{-9/8} ds)`
   gives
   `‖z‖_{L^p((T, ∞), s^{-9/8} ds; H²)} ≤ C ν^{-1/2} [T^{-1/22} M_z + ‖g‖_{L^p((T - 1, ∞), s^{-9/8} ds; H¹)}]`.
3. Combining the early `(0, T]` and late `(T, ∞)` `H²` bounds with `s ‖v(s)‖_∞ + s ‖Dv(s)‖_∞ ≤ 𝒫_ν`
   (`s ≥ 1`) bounds `s B_v z = flatK p.train z zq zη` in `H_p`.

## Proved here (zero `sorry`)

1. `measurable_sliceL2Norm`, `measurable_sliceH1Norm`, `measurable_sliceH2Norm`,
   `sliceH1Norm_le_sliceH2Norm`: measurability and monotonicity of the cylinder `H¹(C_c)` and
   `H²(C_c)` slice norms;
2. `sLpNorm_mono_ae`, `lintegral_Ioc_zero_rpow`, `sLpNorm_inv_sqrt_le`: a.e. monotonicity of
   `sLpNorm b T` on `(0, T]` and exact evaluation/bound
   `sLpNorm (13 / 8) T (fun s => s^{-1/2}) ≤ T^{5/11}` (`(-1/2)(11/4) + 13/8 = 1/4`);
3. `sLpNorm_duhamel_le`, `early_duhamel_sLpNorm_bound`: application of `hardySingular_proof`
   (`PartII-b:T04`) to the `(0, T]` Duhamel singular integral and combined `(0, T]` `H²` bound;
4. `tail_sMeas_one`, `tailLpNorm_const_le`: exact tail integral `∫_T^∞ s^{-9/8} ds = 8 T^{-1/8}` and
   the resulting `8^{4/11} T^{-1/22} M_z ≤ 8 T^{-1/22} M_z` bound in `L^p((T, ∞), s^{-9/8} ds)`
   (SP 2306–2308);
5. `lintegral_Ioi_sub_right`, `lintegral_Ioc_zero_one_inv_sqrt`, `unit_duhamel_fiber_le`,
   `tailLpNorm_unit_duhamel_le`, `late_duhamel_tailLpNorm_bound`: the complete Minkowski proof on
   `(T, ∞)` (`T ≥ 1`) of
   `‖∫_0^1 r^{-1/2} G(s - r) dr‖_{L^p((T, ∞), s^{-9/8} ds)} ≤ 2 ‖G‖_{L^p((T - 1, ∞), s^{-9/8} ds)}`
   and the full late-age `H²` smoothing bound of SP 2305–2308;
6. `localSmoothing_of`: conditional assembly of `LocalSmoothing` from `CylinderParabolicH2Duhamel`
   (`PartII-b:F8/1`), `FlatKInteractionFromH2` (`PartII-b:F8/2`), and
   `hGE : TailSourceAndGlobalEnergy`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Measurability and monotonicity of `sliceH1Norm` and `sliceH2Norm` -/

theorem sliceL2Norm_eq_lintegral (c : ℝ) (u : CProf) (s : ℝ) :
    eLpNorm (fun x => u (s, x)) 2 (volume.restrict (B0579.cell c)) =
      (∫⁻ x in B0579.cell c, ‖u (s, x)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have h0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have ht : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ht]
  simp

theorem measurable_sliceL2Norm (c : ℝ) {u : CProf} (hu : StronglyMeasurable u) :
    Measurable (fun s : ℝ => eLpNorm (fun x => u (s, x)) 2 (volume.restrict (B0579.cell c))) := by
  have h1 : Measurable (fun p : Coord => ‖u p‖ₑ ^ (2 : ℝ)) :=
    (hu.measurable.enorm).pow_const (2 : ℝ)
  have h2 : Measurable (fun s : ℝ => ∫⁻ x in B0579.cell c, ‖u (s, x)‖ₑ ^ (2 : ℝ)) :=
    h1.lintegral_prod_right'
  have h3 : (fun s : ℝ => eLpNorm (fun x => u (s, x)) 2 (volume.restrict (B0579.cell c))) =
      fun s : ℝ => (∫⁻ x in B0579.cell c, ‖u (s, x)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    funext (sliceL2Norm_eq_lintegral c u)
  rw [h3]
  exact h2.pow_const (1 / 2 : ℝ)

theorem measurable_sliceH1Norm (c : ℝ) {z zq zη : CProf}
    (hz : StronglyMeasurable z) (hzq : StronglyMeasurable zq) (hzη : StronglyMeasurable zη) :
    Measurable (sliceH1Norm c z zq zη) := by
  unfold sliceH1Norm
  exact ((measurable_sliceL2Norm c hz).add (measurable_sliceL2Norm c hzq)).add
    (measurable_sliceL2Norm c hzη)

theorem measurable_sliceH2Norm (c : ℝ) {z zq zη : CProf} {D2z : Fin 2 → Fin 2 → CProf}
    (hz : StronglyMeasurable z) (hzq : StronglyMeasurable zq) (hzη : StronglyMeasurable zη)
    (hD2 : ∀ i j, StronglyMeasurable (D2z i j)) :
    Measurable (sliceH2Norm c z zq zη D2z) := by
  unfold sliceH2Norm
  refine (measurable_sliceH1Norm c hz hzq hzη).add ?_
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact measurable_sliceL2Norm c (hD2 i j)

theorem sliceH1Norm_le_sliceH2Norm (c : ℝ) (z zq zη : CProf) (D2z : Fin 2 → Fin 2 → CProf)
    (s : ℝ) :
    sliceH1Norm c z zq zη s ≤ sliceH2Norm c z zq zη D2z s :=
  le_self_add

/-! ## 2. Early-age `(0, T]` Duhamel `L^p(s^{13/8} ds)` bounds via `hardySingular_proof` (SP 2300–2305) -/

theorem sLpNorm_mono_ae {b T : ℝ} {f g : ℝ → ℝ≥0∞}
    (h : ∀ᵐ s ∂volume, s ∈ Ioc 0 T → f s ≤ g s) :
    sLpNorm b T f ≤ sLpNorm b T g := by
  unfold sLpNorm
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have h_sMeas : ∀ᵐ s ∂sMeas b, s ∈ Ioc 0 T → f s ≤ g s := by
    unfold sMeas
    exact withDensity_absolutelyContinuous _ _ (ae_restrict_of_ae h)
  refine lintegral_mono_ae ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mpr h_sMeas] with s hs
  exact ENNReal.rpow_le_rpow hs (by norm_num [bgp])

/-- Exact evaluation of `∫⁻ s in Ioc 0 T, ENNReal.ofReal (s ^ a) = ENNReal.ofReal (T ^ (a + 1) / (a + 1))`
for `-1 < a` and `0 ≤ T`. -/
theorem lintegral_Ioc_zero_rpow {a T : ℝ} (ha : -1 < a) (hT : 0 ≤ T) :
    ∫⁻ s in Ioc 0 T, ENNReal.ofReal (s ^ a) = ENNReal.ofReal (T ^ (a + 1) / (a + 1)) := by
  have hint : IntervalIntegrable (fun x : ℝ => x ^ a) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' ha
  have hnn : ∀ᵐ s ∂volume.restrict (Ioc 0 T), 0 ≤ s ^ a :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => Real.rpow_nonneg hs.1.le a
  rw [← ofReal_integral_eq_lintegral_ofReal hint.1 hnn,
    ← intervalIntegral.integral_of_le hT,
    integral_rpow (Or.inl ha),
    Real.zero_rpow (by linarith : a + 1 ≠ 0),
    sub_zero]

/-- Exact evaluation and bound for `‖s^{-1/2}‖_{L^p((0, T], s^{13/8} ds)}` (`p = 11/4`):
since `(-1/2) · (11/4) + 13/8 = 1/4 > -1`, `∫_0^T s^{1/4} ds = (4/5) T^{5/4} ≤ T^{5/4}`, so
`sLpNorm (13 / 8) T (s ↦ s^{-1/2}) ≤ T^{5/11}`. -/
theorem sLpNorm_inv_sqrt_le {T : ℝ} (hT : 0 < T) :
    sLpNorm (13 / 8) T (fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ))) ≤
      ENNReal.ofReal (T ^ (5 / 11 : ℝ)) := by
  unfold sLpNorm
  have hbgp : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have h411 : (0 : ℝ) ≤ 4 / 11 := by norm_num
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) ^ bgp) := by fun_prop
  rw [hardySing_sMeas_Ioc (13 / 8) T _ hm]
  have hcongr : ∫⁻ s in Ioc 0 T,
      ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ)) =
      ∫⁻ s in Ioc 0 T, ENNReal.ofReal (s ^ (1 / 4 : ℝ)) := by
    refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 < s := hs.1
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hs0.le _) hbgp,
      ← Real.rpow_mul hs0.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _),
      ← Real.rpow_add hs0]
    congr 2
    norm_num [bgp]
  rw [hcongr, lintegral_Ioc_zero_rpow (by norm_num) hT.le]
  have h14 : (1 / 4 : ℝ) + 1 = 5 / 4 := by norm_num
  rw [h14]
  have hle : T ^ (5 / 4 : ℝ) / (5 / 4 : ℝ) ≤ T ^ (5 / 4 : ℝ) := by
    have hpos : 0 ≤ T ^ (5 / 4 : ℝ) := Real.rpow_nonneg hT.le _
    linarith
  calc ENNReal.ofReal (T ^ (5 / 4 : ℝ) / (5 / 4 : ℝ)) ^ (4 / 11 : ℝ)
      ≤ ENNReal.ofReal (T ^ (5 / 4 : ℝ)) ^ (4 / 11 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hle) h411
    _ = ENNReal.ofReal (T ^ (5 / 11 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hT.le _) h411,
          ← Real.rpow_mul hT.le]
        congr 2
        norm_num

/-- Application of `hardySingular_proof` (`PartII-b:T04`) in `sLpNorm (13 / 8) T` notation:
for `0 < T` and measurable `G : ℝ → ℝ≥0∞`,
`sLpNorm (13 / 8) T (fun s => ∫⁻ t in Ioc 0 s, (s - t)^{-1/2} G(t)) ≤ ((hsC0.toReal + 1) √T) · sLpNorm (13 / 8) T G`. -/
theorem sLpNorm_duhamel_le {T : ℝ} (hT : 0 < T) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    sLpNorm (13 / 8) T
      (fun s => ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t) ≤
    ENNReal.ofReal ((hsC0.toReal + 1) * Real.sqrt T) * sLpNorm (13 / 8) T G := by
  have : SFinite (sMeas (13 / 8)) := hardySing_sMeas_sFinite (13 / 8)
  have hfin : hsC0 < ⊤ := hsC0_lt_top
  have hp1 : (1 : ℝ) ≤ bgp := by norm_num [bgp]
  have hp0 : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have hinv : (4 / 11 : ℝ) = 1 / bgp := by norm_num [bgp]
  have hF_meas : Measurable (Function.uncurry (hsF G)) := by
    change Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal ((1 - p.2) ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal (p.1 ^ (1 / 2 : ℝ)) * G (p.1 * p.2))
    fun_prop
  have hL : ∫⁻ s in Ioc 0 T,
        (∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t) ^ bgp ∂sMeas (13 / 8) =
      ∫⁻ s in Ioc 0 T, (∫⁻ u in Ioc 0 1, hsF G s u) ^ bgp ∂sMeas (13 / 8) := by
    refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    rw [hardySing_inner s hs.1 G]
  have hmink := minkowski_lintegral_rpow
    (μ := (sMeas (13 / 8)).restrict (Ioc 0 T)) (ν := volume.restrict (Ioc 0 1))
    (f := hsF G) hp1 hF_meas
  have hfib : ∀ u ∈ Ioc (0 : ℝ) 1,
      (∫⁻ a, hsF G a u ^ bgp ∂((sMeas (13 / 8)).restrict (Ioc 0 T))) ^ (1 / bgp) ≤
        hsA T u * (∫⁻ s in Ioc 0 T, G s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) := by
    intro u hu
    have h1 := hardySing_fiber T hT G hG u hu.1 hu.2
    calc (∫⁻ a, hsF G a u ^ bgp ∂((sMeas (13 / 8)).restrict (Ioc 0 T))) ^ (1 / bgp)
        ≤ (hsA T u ^ bgp * ∫⁻ s in Ioc 0 T, G s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) :=
          ENNReal.rpow_le_rpow h1 (one_div_nonneg.mpr hp0)
      _ = hsA T u * (∫⁻ s in Ioc 0 T, G s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp0), hardySing_rpow_inv]
  have hR : ∫⁻ b, (∫⁻ a, hsF G a b ^ bgp ∂((sMeas (13 / 8)).restrict (Ioc 0 T)))
        ^ (1 / bgp) ∂(volume.restrict (Ioc 0 1))
      ≤ (ENNReal.ofReal (Real.sqrt T) * hsC0) *
          (∫⁻ s in Ioc 0 T, G s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) := by
    have hsAm : Measurable fun b : ℝ => hsA T b := by
      unfold hsA
      fun_prop
    calc ∫⁻ b, (∫⁻ a, hsF G a b ^ bgp ∂((sMeas (13 / 8)).restrict (Ioc 0 T)))
            ^ (1 / bgp) ∂(volume.restrict (Ioc 0 1))
        ≤ ∫⁻ b in Ioc 0 1, hsA T b * (∫⁻ s in Ioc 0 T, G s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) :=
          setLIntegral_mono' measurableSet_Ioc (fun u hu => hfib u hu)
      _ = (∫⁻ b in Ioc 0 1, hsA T b) * (∫⁻ s in Ioc 0 T, G s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) :=
          lintegral_mul_const _ hsAm
      _ = (ENNReal.ofReal (Real.sqrt T) * hsC0) *
          (∫⁻ s in Ioc 0 T, G s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) := by
          rw [hardySing_hsA_integral]
  have hC : ENNReal.ofReal (Real.sqrt T) * hsC0 ≤
      ENNReal.ofReal ((hsC0.toReal + 1) * Real.sqrt T) := by
    have hnn : (0 : ℝ) ≤ hsC0.toReal + 1 := by linarith [ENNReal.toReal_nonneg (a := hsC0)]
    have hle : hsC0 ≤ ENNReal.ofReal (hsC0.toReal + 1) := by
      calc hsC0 = ENNReal.ofReal hsC0.toReal := (ENNReal.ofReal_toReal hfin.ne).symm
        _ ≤ ENNReal.ofReal (hsC0.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
    calc ENNReal.ofReal (Real.sqrt T) * hsC0
        ≤ ENNReal.ofReal (Real.sqrt T) * ENNReal.ofReal (hsC0.toReal + 1) :=
          mul_le_mul_of_nonneg_left hle zero_le
      _ = ENNReal.ofReal ((hsC0.toReal + 1) * Real.sqrt T) := by
          rw [ENNReal.ofReal_mul hnn]
          ring
  unfold sLpNorm
  rw [hinv, hL]
  exact le_trans hmink (le_trans hR (mul_le_mul_of_nonneg_right hC zero_le))

/-- Full early-age `L^p((0, T], s^{13/8} ds)` Duhamel smoothing bound (SP 2300–2305):
if for a.e. `s ∈ (0, T]`,
`Z2(s) ≤ C₀ ν^{-1/2} (s^{-1/2} M_z + ∫_0^s (s - t)^{-1/2} G(t) dt)`,
then
`sLpNorm (13 / 8) T Z2 ≤ (C₀ ν^{-1/2}) · (T^{5/11} M_z + ((hsC0.toReal + 1) √T) · sLpNorm (13 / 8) T G)`. -/
theorem early_duhamel_sLpNorm_bound {T ν C₀ M_z : ℝ} (hT : 0 < T) (hMz : 0 ≤ M_z)
    {Z2 G : ℝ → ℝ≥0∞} (hG : Measurable G)
    (hpt : ∀ᵐ s ∂volume, s ∈ Ioc 0 T →
      Z2 s ≤ ENNReal.ofReal (C₀ * ν ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M_z) +
          ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t)) :
    sLpNorm (13 / 8) T Z2 ≤
      ENNReal.ofReal (C₀ * ν ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal (T ^ (5 / 11 : ℝ) * M_z) +
          ENNReal.ofReal ((hsC0.toReal + 1) * Real.sqrt T) * sLpNorm (13 / 8) T G) := by
  have hm_hom : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M_z)) := by fun_prop
  have hm_ind : Measurable
      (fun p : ℝ × ℝ => Set.indicator (Ioc 0 p.1)
        (fun t => ENNReal.ofReal ((p.1 - t) ^ (-1 / 2 : ℝ)) * G t) p.2) := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ioc 0 p.1} := by
      have : {p : ℝ × ℝ | p.2 ∈ Ioc 0 p.1} =
          {p : ℝ × ℝ | 0 < p.2} ∩ {p : ℝ × ℝ | p.2 ≤ p.1} := by
        ext p; simp [mem_Ioc]
      rw [this]
      exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)
    exact Measurable.indicator (by fun_prop) hset
  have hm_int : Measurable
      (fun s : ℝ => ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t) := by
    have heq : (fun s : ℝ => ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t) =
        fun s : ℝ => ∫⁻ t, Set.indicator (Ioc 0 s)
          (fun t => ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t) t := by
      funext s
      exact (lintegral_indicator measurableSet_Ioc _).symm
    rw [heq]
    exact hm_ind.lintegral_prod_right'
  have hmono := sLpNorm_mono_ae (b := 13 / 8) hpt
  rw [sLpNorm_const_mul (13 / 8) T _ ENNReal.ofReal_ne_top] at hmono
  have hadd := sLpNorm_add_le (13 / 8) T hm_hom hm_int
  have h1 : sLpNorm (13 / 8) T (fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M_z)) ≤
      ENNReal.ofReal (T ^ (5 / 11 : ℝ) * M_z) := by
    have hsplit : (fun s : ℝ => ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M_z)) =
        fun s : ℝ => ENNReal.ofReal M_z * ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) := by
      funext s
      rw [mul_comm, ENNReal.ofReal_mul hMz]
    rw [hsplit, sLpNorm_const_mul (13 / 8) T _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal M_z * sLpNorm (13 / 8) T (fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ)))
        ≤ ENNReal.ofReal M_z * ENNReal.ofReal (T ^ (5 / 11 : ℝ)) :=
          mul_le_mul_of_nonneg_left (sLpNorm_inv_sqrt_le hT) zero_le
      _ = ENNReal.ofReal (T ^ (5 / 11 : ℝ) * M_z) := by
          rw [← ENNReal.ofReal_mul hMz, mul_comm]
  have h2 := sLpNorm_duhamel_le hT hG
  exact hmono.trans (mul_le_mul_of_nonneg_left (hadd.trans (add_le_add h1 h2)) zero_le)

/-! ## 3. Late-age `(T, ∞)` unit-interval Duhamel `L^p(s^{-9/8} ds)` bounds (SP 2305–2308) -/

/-- Exact evaluation of `∫_T^∞ s^{-9/8} ds = 8 T^{-1/8}` against `sMeas (-9 / 8)` for `T > 0`. -/
theorem tail_sMeas_one {T : ℝ} (hT : 0 < T) :
    ∫⁻ _s in Ioi T, (1 : ℝ≥0∞) ∂sMeas (-9 / 8) = ENNReal.ofReal (8 * T ^ (-1 / 8 : ℝ)) := by
  rw [sMeas_Ioi (-9 / 8) T hT.le _ measurable_const]
  simp only [one_mul]
  have hr : (-9 / 8 : ℝ) < -1 := by norm_num
  have hint : IntegrableOn (fun s : ℝ => s ^ (-9 / 8 : ℝ)) (Ioi T) volume :=
    integrableOn_Ioi_rpow_of_lt hr hT
  have hnn : ∀ᵐ s ∂volume.restrict (Ioi T), 0 ≤ s ^ (-9 / 8 : ℝ) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun s hs =>
      Real.rpow_nonneg (lt_trans hT hs).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Ioi_rpow_of_lt hr hT]
  congr 1
  have hexp : (-9 / 8 : ℝ) + 1 = -1 / 8 := by norm_num
  rw [hexp]
  ring

/-- Constant tail bound on `(T, ∞)` (`T > 0`, `M_z ≥ 0`):
`tailLpNorm (-9 / 8) T (fun _ => M_z) ≤ 8 (T^{-1/22} M_z)` (SP 2306–2308). -/
theorem tailLpNorm_const_le {T M_z : ℝ} (hT : 0 < T) (hM : 0 ≤ M_z) :
    tailLpNorm (-9 / 8) T (fun _ => ENNReal.ofReal M_z) ≤
      ENNReal.ofReal (8 * (T ^ (-1 / 22 : ℝ) * M_z)) := by
  unfold tailLpNorm
  have h411 : (0 : ℝ) ≤ 4 / 11 := by norm_num
  have hmul : bgp * (4 / 11 : ℝ) = 1 := by norm_num [bgp]
  have hconst : ∫⁻ _s in Ioi T, (ENNReal.ofReal M_z) ^ bgp ∂sMeas (-9 / 8) =
      (ENNReal.ofReal M_z) ^ bgp * ∫⁻ _s in Ioi T, (1 : ℝ≥0∞) ∂sMeas (-9 / 8) := by
    simp [lintegral_const]
  rw [hconst, tail_sMeas_one hT, ENNReal.mul_rpow_of_nonneg _ _ h411, ← ENNReal.rpow_mul, hmul,
    ENNReal.rpow_one]
  have h8T : 0 ≤ 8 * T ^ (-1 / 8 : ℝ) := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg h8T h411, ← ENNReal.ofReal_mul hM]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT.le _), ← Real.rpow_mul hT.le,
    show (-1 / 8 : ℝ) * (4 / 11 : ℝ) = -1 / 22 by norm_num]
  have h8_le : (8 : ℝ) ^ (4 / 11 : ℝ) ≤ 8 := by
    calc (8 : ℝ) ^ (4 / 11 : ℝ) ≤ (8 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 8 := Real.rpow_one 8
  have hTM_nonneg : 0 ≤ T ^ (-1 / 22 : ℝ) * M_z := mul_nonneg (Real.rpow_nonneg hT.le _) hM
  calc M_z * ((8 : ℝ) ^ (4 / 11 : ℝ) * T ^ (-1 / 22 : ℝ))
      = (8 : ℝ) ^ (4 / 11 : ℝ) * (T ^ (-1 / 22 : ℝ) * M_z) := by ring
    _ ≤ 8 * (T ^ (-1 / 22 : ℝ) * M_z) := mul_le_mul_of_nonneg_right h8_le hTM_nonneg

/-- Translation change-of-variables `u = s - r` on `Ioi T`:
`∫⁻ s in Ioi T, H (s - r) = ∫⁻ u in Ioi (T - r), H u`. -/
theorem lintegral_Ioi_sub_right (T r : ℝ) (H : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioi T, H (s - r) = ∫⁻ u in Ioi (T - r), H u := by
  have himg : (fun s : ℝ => s - r) '' Ioi T = Ioi (T - r) := by
    ext u
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨s, hs, rfl⟩
      linarith
    · intro hu
      exact ⟨u + r, by linarith, by ring⟩
  have hderiv : ∀ x ∈ Ioi T, HasDerivWithinAt (fun s : ℝ => s - r) 1 (Ioi T) x := by
    intro x _
    exact ((hasDerivAt_id x).sub_const r).hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => s - r) (Ioi T) :=
    (sub_left_injective).injOn
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj]
  simp

/-- Exact evaluation `∫_0^1 r^{-1/2} dr = 2` (SP 2306). -/
theorem lintegral_Ioc_zero_one_inv_sqrt :
    ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) = ENNReal.ofReal 2 := by
  rw [lintegral_Ioc_zero_rpow (by norm_num) zero_le_one]
  congr 1
  norm_num

/-- Fibre bound for the unit-interval Duhamel integral on `(T, ∞)` (`1 ≤ T`, `r ∈ (0, 1]`):
since `s - r ≤ s` and `-9/8 ≤ 0`, `s^{-9/8} ≤ (s - r)^{-9/8}`, so translating `u = s - r` and
using `Ioi (T - r) ⊆ Ioi (T - 1)` gives
`(∫⁻ s in Ioi T, (r^{-1/2} G(s - r))^p ∂sMeas (-9/8))^{1/p} ≤ r^{-1/2} ‖G‖_{L^p((T - 1, ∞), s^{-9/8} ds)}`. -/
theorem unit_duhamel_fiber_le {T r : ℝ} (hT1 : 1 ≤ T) (hr0 : 0 < r) (hr1 : r ≤ 1)
    {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ s in Ioi T,
        (ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r)) ^ bgp ∂sMeas (-9 / 8)) ^ (1 / bgp) ≤
      ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * tailLpNorm (-9 / 8) (T - 1) G := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT1
  have hTm1 : 0 ≤ T - 1 := sub_nonneg.mpr hT1
  have hp0 : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have h1p : (1 / bgp : ℝ) = 4 / 11 := by norm_num [bgp]
  have hpow : ∀ s : ℝ,
      (ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r)) ^ bgp =
        ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) ^ bgp * G (s - r) ^ bgp :=
    fun s => ENNReal.mul_rpow_of_nonneg _ _ hp0
  simp_rw [hpow]
  have hmG : Measurable (fun s : ℝ => G (s - r) ^ bgp) := by fun_prop
  rw [lintegral_const_mul _ hmG,
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp0),
    hardySing_rpow_inv]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [h1p]
  unfold tailLpNorm
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [sMeas_Ioi (-9 / 8) T hT0 _ hmG,
    sMeas_Ioi (-9 / 8) (T - 1) hTm1 _ (by fun_prop)]
  have hpt : ∀ s ∈ Ioi T,
      G (s - r) ^ bgp * ENNReal.ofReal (s ^ (-9 / 8 : ℝ)) ≤
        G (s - r) ^ bgp * ENNReal.ofReal ((s - r) ^ (-9 / 8 : ℝ)) := by
    intro s hs
    have hsr_pos : 0 < s - r := by linarith [mem_Ioi.mp hs]
    have hsr_le : s - r ≤ s := by linarith
    have hrpow : s ^ (-9 / 8 : ℝ) ≤ (s - r) ^ (-9 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hsr_pos hsr_le (by norm_num)
    exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hrpow) zero_le
  calc ∫⁻ s in Ioi T, G (s - r) ^ bgp * ENNReal.ofReal (s ^ (-9 / 8 : ℝ))
      ≤ ∫⁻ s in Ioi T, G (s - r) ^ bgp * ENNReal.ofReal ((s - r) ^ (-9 / 8 : ℝ)) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ∫⁻ u in Ioi (T - r), G u ^ bgp * ENNReal.ofReal (u ^ (-9 / 8 : ℝ)) :=
        lintegral_Ioi_sub_right T r (fun u => G u ^ bgp * ENNReal.ofReal (u ^ (-9 / 8 : ℝ)))
    _ ≤ ∫⁻ u in Ioi (T - 1), G u ^ bgp * ENNReal.ofReal (u ^ (-9 / 8 : ℝ)) :=
        lintegral_mono_set (Ioi_subset_Ioi (by linarith))

/-- **Unit-interval Duhamel Minkowski bound on `(T, ∞)` (`1 ≤ T`, SP 2305–2308)**:
since `(s - r)^{-9/8} ≥ s^{-9/8}` for `r ∈ (0, 1)` and `∫_0^1 r^{-1/2} dr = 2`, Minkowski's
integral inequality (`minkowski_lintegral_rpow`) in `L^p((T, ∞), s^{-9/8} ds)` gives
`‖∫_0^1 r^{-1/2} G(s - r) dr‖_{L^p((T, ∞), s^{-9/8} ds)} ≤ 2 ‖G‖_{L^p((T - 1, ∞), s^{-9/8} ds)}`. -/
theorem tailLpNorm_unit_duhamel_le {T : ℝ} (hT1 : 1 ≤ T) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    tailLpNorm (-9 / 8) T
      (fun s => ∫⁻ r in Ioc 0 1, ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r)) ≤
    ENNReal.ofReal 2 * tailLpNorm (-9 / 8) (T - 1) G := by
  have : SFinite (sMeas (-9 / 8)) := hardySing_sMeas_sFinite (-9 / 8)
  have hp1 : (1 : ℝ) ≤ bgp := by norm_num [bgp]
  have hinv : (4 / 11 : ℝ) = 1 / bgp := by norm_num [bgp]
  let F : ℝ → ℝ → ℝ≥0∞ := fun s r => ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r)
  have hF_meas : Measurable (Function.uncurry F) := by
    change Measurable fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ (-1 / 2 : ℝ)) * G (p.1 - p.2)
    fun_prop
  have hmink := minkowski_lintegral_rpow
    (μ := (sMeas (-9 / 8)).restrict (Ioi T)) (ν := volume.restrict (Ioc 0 1))
    (f := F) hp1 hF_meas
  have hLHS : tailLpNorm (-9 / 8) T (fun s => ∫⁻ r in Ioc 0 1, F s r) =
      (∫⁻ s in Ioi T, (∫⁻ r in Ioc 0 1, F s r) ^ bgp ∂sMeas (-9 / 8)) ^ (1 / bgp) := by
    unfold tailLpNorm
    rw [hinv]
  rw [hLHS]
  refine hmink.trans ?_
  calc ∫⁻ r in Ioc 0 1,
        (∫⁻ s in Ioi T, F s r ^ bgp ∂sMeas (-9 / 8)) ^ (1 / bgp)
      ≤ ∫⁻ r in Ioc 0 1,
          ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * tailLpNorm (-9 / 8) (T - 1) G := by
        refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
        exact unit_duhamel_fiber_le hT1 hr.1 hr.2 hG
    _ = (∫⁻ r in Ioc 0 1, ENNReal.ofReal (r ^ (-1 / 2 : ℝ))) *
          tailLpNorm (-9 / 8) (T - 1) G :=
        lintegral_mul_const _ (by fun_prop)
    _ = ENNReal.ofReal 2 * tailLpNorm (-9 / 8) (T - 1) G := by
        rw [lintegral_Ioc_zero_one_inv_sqrt]

/-- Full late-age `L^p((T, ∞), s^{-9/8} ds)` Duhamel smoothing bound for `2 ≤ T` (SP 2305–2308):
if for a.e. `s > T`,
`Z2(s) ≤ C₀ ν^{-1/2} (M_z + ∫_0^1 r^{-1/2} G(s - r) dr)`,
then
`tailLpNorm (-9 / 8) T Z2 ≤ (8 C₀ ν^{-1/2}) · (T^{-1/22} M_z + tailLpNorm (-9 / 8) (max 1 (T - 1)) G)`. -/
theorem late_duhamel_tailLpNorm_bound {T ν C₀ M_z : ℝ} (hT2 : 2 ≤ T) (hν0 : 0 < ν)
    (hC0 : 0 ≤ C₀) (hMz : 0 ≤ M_z) {Z2 G : ℝ → ℝ≥0∞} (hG : Measurable G)
    (hpt : ∀ᵐ s ∂volume, T < s →
      Z2 s ≤ ENNReal.ofReal (C₀ * ν ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal M_z +
          ∫⁻ r in Ioc 0 1, ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r))) :
    tailLpNorm (-9 / 8) T Z2 ≤
      ENNReal.ofReal (8 * C₀ * ν ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal (T ^ (-1 / 22 : ℝ) * M_z) +
          tailLpNorm (-9 / 8) (max 1 (T - 1)) G) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hmax : max 1 (T - 1) = T - 1 := max_eq_right (by linarith)
  have hm_prod : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ (-1 / 2 : ℝ)) * G (p.1 - p.2)) := by
    fun_prop
  have hm_int : Measurable
      (fun s : ℝ => ∫⁻ r in Ioc 0 1, ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r)) :=
    hm_prod.lintegral_prod_right'
  have hmono := tailLpNorm_mono_ae (b := -9 / 8) hpt
  rw [tailLpNorm_const_mul (-9 / 8) T _ ENNReal.ofReal_ne_top] at hmono
  have hadd := tailLpNorm_add_le (-9 / 8) T (measurable_const (a := ENNReal.ofReal M_z)) hm_int
  have h1 := tailLpNorm_const_le hT0 hMz
  have h2 := tailLpNorm_unit_duhamel_le hT1 hG
  rw [← hmax] at h2
  have h28 : ENNReal.ofReal 2 * tailLpNorm (-9 / 8) (max 1 (T - 1)) G ≤
      ENNReal.ofReal 8 * tailLpNorm (-9 / 8) (max 1 (T - 1)) G :=
    mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by norm_num)) zero_le
  have h1_split : ENNReal.ofReal (8 * (T ^ (-1 / 22 : ℝ) * M_z)) =
      ENNReal.ofReal 8 * ENNReal.ofReal (T ^ (-1 / 22 : ℝ) * M_z) :=
    ENNReal.ofReal_mul (by norm_num)
  calc tailLpNorm (-9 / 8) T Z2
      ≤ ENNReal.ofReal (C₀ * ν ^ (-1 / 2 : ℝ)) *
          (tailLpNorm (-9 / 8) T (fun _ => ENNReal.ofReal M_z) +
            tailLpNorm (-9 / 8) T
              (fun s => ∫⁻ r in Ioc 0 1, ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r))) :=
        hmono.trans (mul_le_mul_of_nonneg_left hadd zero_le)
    _ ≤ ENNReal.ofReal (C₀ * ν ^ (-1 / 2 : ℝ)) *
          (ENNReal.ofReal 8 * ENNReal.ofReal (T ^ (-1 / 22 : ℝ) * M_z) +
            ENNReal.ofReal 8 * tailLpNorm (-9 / 8) (max 1 (T - 1)) G) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ (h2.trans h28)) zero_le
        exact h1.trans_eq h1_split
    _ = ENNReal.ofReal (8 * C₀ * ν ^ (-1 / 2 : ℝ)) *
          (ENNReal.ofReal (T ^ (-1 / 22 : ℝ) * M_z) +
            tailLpNorm (-9 / 8) (max 1 (T - 1)) G) := by
        rw [← mul_add, ← mul_assoc,
          ← ENNReal.ofReal_mul (mul_nonneg hC0 (Real.rpow_nonneg hν0.le _))]
        congr 2
        ring

/-! ## 4. Leaf statements (`PartII-b:F8/1`, `PartII-b:F8/2`) and conditional assembly -/

/-- **Leaf 1 (`PartII-b:F8/1`, `CylinderParabolicH2Duhamel`, SP 2296–2305)**:
for the meridional correction equation `∂_s z + B_v z - ν Δ_{q,η} z = g` on `C_c`
(`IsGlobalMeridionalCorrection`), differentiating homogeneously twice and using incompressibility,
orthogonality of `P_0`, and `short-bg:train-uniform` gives the cylinder energy hierarchy
`E_j' + ν E_{j+1} ≤ C ∑_{i ≤ j} E_i` (`j ≤ 2`, `E_j = ‖D^j z‖_{L²(C_c)}²`). Multiplication by
successive powers of `ν(t - s)` and summation gives `H¹ → H²` smoothing norm
`C_sm [ν(t - s)]^{-1/2}` for `t - s ≤ 1` (and polynomial in `ν⁻¹` on `(0, p.H]`), producing
strongly measurable `c`-periodic representatives `zOf, zqOf, zηOf` and weak second spatial
derivatives `D2zOf i j` obeying the `(0, p.H]` Duhamel inequality and the `(p.H, ∞)` unit-interval
`[s - 1, s]` Duhamel inequality. -/
def CylinderParabolicH2Duhamel : Prop :=
  ∀ (C_late : ℝ), 0 < C_late →
    ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
      Blueprint.Planar.IsGrowingEigenpair lam q →
    ∀ a' : ℝ, 0 < a' → a' < lam.re / (1 + Sig) ^ 2 →
    ∀ dm dp : ℝ, 0 < dm →
    ∀ (C_ge : ℝ) (k_ge : ℕ), 0 < C_ge →
      ∃ (C_sm : ℝ) (k_sm : ℕ) (ν_sm : ℝ), 0 < C_sm ∧ 0 < ν_sm ∧
        ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_sm → p.ageCut = Sig → p.mode = q →
        ∀ (αMap : HpR p.c →L[ℝ] E2)
          (b0Of b0qOf b0ηOf gOf gqOf gηOf zOf₀ zqOf₀ zηOf₀ : HpR p.c →ₗ[ℝ] CProf),
          (∀ F : HpR p.c,
            let M_exp := Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3)
            InFlatClass p.c bgp (b0Of F) ∧
            IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
            HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
            HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
            QPeriodic p.c (gOf F) ∧
            HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
            HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
            IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
            IsGlobalMeridionalCorrection p (gOf F) (zOf₀ F) (zqOf₀ F) (zηOf₀ F) (αMap F) ∧
            Measurable (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ∧
            Measurable (sliceH1Norm p.c (zOf₀ F) (zqOf₀ F) (zηOf₀ F)) ∧
            sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
              ENNReal.ofReal (C_ge * (p.ν ^ k_ge)⁻¹ * ‖F‖) ∧
            (∫⁻ s in Ioi (max 1 (p.H - 1)),
                sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s ^ bgp ∂sMeas (-9 / 8)) ^
                  (4 / 11 : ℝ) ≤
              ENNReal.ofReal (C_ge * (p.ν ^ k_ge)⁻¹ * ‖F‖) ∧
            ∀ s : ℝ, 0 < s →
              sliceH1Norm p.c (zOf₀ F) (zqOf₀ F) (zηOf₀ F) s + ENNReal.ofReal ‖αMap F‖ ≤
                ENNReal.ofReal (C_ge * (p.ν ^ k_ge)⁻¹ * M_exp * ‖F‖)) →
          ∃ (zOf zqOf zηOf : HpR p.c →ₗ[ℝ] CProf)
            (D2zOf : Fin 2 → Fin 2 → HpR p.c →ₗ[ℝ] CProf),
            ∀ F : HpR p.c,
              let M_exp := Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3)
              let M_z0 := C_ge * (p.ν ^ k_ge)⁻¹ * M_exp * ‖F‖
              let G := sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)
              let Z2 := sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F)
              IsGlobalMeridionalCorrection p (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F) ∧
              QPeriodic p.c (zOf F) ∧ QPeriodic p.c (zqOf F) ∧ QPeriodic p.c (zηOf F) ∧
              StronglyMeasurable (zOf F) ∧ StronglyMeasurable (zqOf F) ∧
              StronglyMeasurable (zηOf F) ∧ (∀ i j, StronglyMeasurable (D2zOf i j F)) ∧
              HasWeakVec vQ0 dZero (zqOf F) (D2zOf 0 0 F) ∧
              HasWeakVec vEta dZero (zqOf F) (D2zOf 0 1 F) ∧
              HasWeakVec vQ0 dZero (zηOf F) (D2zOf 1 0 F) ∧
              HasWeakVec vEta dZero (zηOf F) (D2zOf 1 1 F) ∧
              (∀ s : ℝ, 0 < s →
                sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αMap F‖ ≤
                  ENNReal.ofReal M_z0) ∧
              (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
                Z2 s ≤ ENNReal.ofReal ((C_sm * (p.ν ^ k_sm)⁻¹) * p.ν ^ (-1 / 2 : ℝ)) *
                  (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M_z0) +
                    ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t)) ∧
              (∀ᵐ s ∂volume, p.H < s →
                Z2 s ≤ ENNReal.ofReal (C_sm * p.ν ^ (-1 / 2 : ℝ)) *
                  (ENNReal.ofReal M_z0 +
                    ∫⁻ r in Ioc 0 1, ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r)))

/-- **Leaf 2 (`PartII-b:F8/2`, `FlatKInteractionFromH2`, SP 2311–2314)**:
combining the cylinder Sobolev embedding `H²(C_c) → W^{1, 11/4}(C_c)` with the train velocity bounds
`‖v(s)‖_∞ + ‖Dv(s)‖_∞ ≤ 𝒫_ν` on `(0, p.H]` and `s ‖v(s)‖_∞ + s ‖Dv(s)‖_∞ ≤ 𝒫_ν` on `(p.H, ∞)`
(`s ≥ 1`), any strongly measurable `c`-periodic profile `z` with weak first and second spatial
derivatives `zq, zη, D2z` whose `sliceH2Norm` is finite in `sLpNorm (13 / 8) p.H` and
`tailLpNorm (-9 / 8) p.H` has `flatK p.train z zq zη ∈ H_p` with
`hNorm p.c bgp (flatK p.train z zq zη) ≤ C_K ν^{-k_K} (sLpNorm (13 / 8) p.H Z2 + tailLpNorm (-9 / 8) p.H Z2)`. -/
def FlatKInteractionFromH2 : Prop :=
  ∀ (Sig : ℝ), 0 < Sig → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C_K : ℝ) (k_K : ℕ) (ν_K : ℝ), 0 < C_K ∧ 0 < ν_K ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_K → p.ageCut = Sig →
      ∀ (z zq zη : CProf) (D2z : Fin 2 → Fin 2 → CProf),
        QPeriodic p.c z → QPeriodic p.c zq → QPeriodic p.c zη →
        StronglyMeasurable z → StronglyMeasurable zq → StronglyMeasurable zη →
        (∀ i j, StronglyMeasurable (D2z i j)) →
        HasWeakVec vQ0 dZero z zq → HasWeakVec vEta dZero z zη →
        HasWeakVec vQ0 dZero zq (D2z 0 0) → HasWeakVec vEta dZero zq (D2z 0 1) →
        HasWeakVec vQ0 dZero zη (D2z 1 0) → HasWeakVec vEta dZero zη (D2z 1 1) →
        sLpNorm (13 / 8) p.H (sliceH2Norm p.c z zq zη D2z) < ⊤ →
        tailLpNorm (-9 / 8) p.H (sliceH2Norm p.c z zq zη D2z) < ⊤ →
        InHr p.c bgp (flatK p.train z zq zη) ∧
        hNorm p.c bgp (flatK p.train z zq zη) ≤
          ENNReal.ofReal (C_K * (p.ν ^ k_K)⁻¹) *
            (sLpNorm (13 / 8) p.H (sliceH2Norm p.c z zq zη D2z) +
              tailLpNorm (-9 / 8) p.H (sliceH2Norm p.c z zq zη D2z))

private theorem inv_pow_mono_le {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) {j k : ℕ}
    (hjk : j ≤ k) : (ν ^ j)⁻¹ ≤ (ν ^ k)⁻¹ :=
  inv_anti₀ (pow_pos hν0 k) (pow_le_pow_of_le_one hν0.le hν1 hjk)

/-- **Conditional assembly of `LocalSmoothing` (`PartII-b:F8`, SP 2296–2312)** from
`CylinderParabolicH2Duhamel` (`PartII-b:F8/1`), `FlatKInteractionFromH2` (`PartII-b:F8/2`), and
`hGE : TailSourceAndGlobalEnergy`, using the proved `early_duhamel_sLpNorm_bound` and
`late_duhamel_tailLpNorm_bound`. -/
theorem localSmoothing_of
    (hDuh : CylinderParabolicH2Duhamel)
    (hFlatK : FlatKInteractionFromH2)
    (hGE : UnforcedLeray.Short.IIb.TailSourceAndGlobalEnergy) :
    UnforcedLeray.Short.IIb.LocalSmoothing := by
  obtain ⟨C_late, hC_late, hGE_core⟩ := hGE.2
  refine ⟨C_late, hC_late, ?_⟩
  intro Sig lam q hSig hq a' ha'0 ha'1 dm dp hdm
  obtain ⟨C_ge, k_ge, ν_ge, hC_ge, hν_ge, hGE_p⟩ :=
    hGE_core Sig lam q hSig hq a' ha'0 ha'1 dm dp hdm
  obtain ⟨C_sm, k_sm, ν_sm, hC_sm, hν_sm, hDuh_p⟩ :=
    hDuh C_late hC_late Sig lam q hSig hq a' ha'0 ha'1 dm dp hdm C_ge k_ge hC_ge
  obtain ⟨C_K, k_K, ν_K, hC_K, hν_K, hFlatK_p⟩ :=
    hFlatK Sig hSig dm dp hdm
  have hsC0_nn : (0 : ℝ) ≤ hsC0.toReal := ENNReal.toReal_nonneg
  set C_early : ℝ := C_sm * (hsC0.toReal + 2) * Sig * C_ge
  set C_late_z : ℝ := 16 * C_sm * C_ge
  set C : ℝ := C_ge + 8 * C_sm + (C_K + 1) * (C_early + C_late_z)
  set k : ℕ := k_ge + k_sm + k_K + 2
  set ν₀ : ℝ := min (min ν_ge ν_sm) (min ν_K (min 1 (Sig / 2)))
  have hC_early_pos : 0 < C_early := by dsimp [C_early]; positivity
  have hC_late_z_pos : 0 < C_late_z := by dsimp [C_late_z]; positivity
  have hCK_prod : 0 ≤ (C_K + 1) * (C_early + C_late_z) := by positivity
  have hC_pos : 0 < C := by dsimp [C]; positivity
  have hν₀_pos : 0 < ν₀ :=
    lt_min (lt_min hν_ge hν_sm) (lt_min hν_K (lt_min one_pos (half_pos hSig)))
  refine ⟨C, k, ν₀, hC_pos, hν₀_pos, ?_⟩
  intro p d hreg hν hAge hMode
  have hν0 : 0 < p.ν := p.ν_pos
  have hν_ge' : p.ν ≤ ν_ge := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_sm' : p.ν ≤ ν_sm := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_K' : p.ν ≤ ν_K := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : p.ν ≤ 1 :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_Sig : p.ν ≤ Sig / 2 :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hH_eq : p.H = Sig / p.ν := by
    change p.ageCut / p.ν = Sig / p.ν
    rw [hAge]
  have hH2 : 2 ≤ p.H := by
    rw [hH_eq, le_div_iff₀ hν0]
    linarith
  have hH1 : 1 ≤ p.H := by linarith
  have hH0 : 0 < p.H := by linarith
  obtain ⟨αMap, b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, zOf₀, zqOf₀, zηOf₀, hGE_F⟩ :=
    hGE_p p d hreg hν_ge' hAge hMode
  obtain ⟨zOf, zqOf, zηOf, D2zOf, hDuh_F⟩ :=
    hDuh_p p d hreg hν_sm' hAge hMode αMap b0Of b0qOf b0ηOf gOf gqOf gηOf zOf₀ zqOf₀ zηOf₀ hGE_F
  refine ⟨αMap, b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, zOf, zqOf, zηOf, D2zOf, ?_⟩
  intro F
  obtain ⟨hb0_cl, hb0_resp, hb0q, hb0η, hg_per, hgq, hgη, hg_src, _hz0_mc,
    hm_g1, _hm_z01, hg_early, hg_tail, _hz0_sup⟩ := hGE_F F
  obtain ⟨hz_mc, hz_per, hzq_per, hzη_per, hsm_z, hsm_zq, hsm_zη, hsm_D2,
    hD2_00, hD2_01, hD2_10, hD2_11, hz_sup, hpt_early, hpt_late⟩ := hDuh_F F
  set M_exp : ℝ := Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3)
  set M_z0 : ℝ := C_ge * (p.ν ^ k_ge)⁻¹ * M_exp * ‖F‖
  set M_z : ℝ := C * (p.ν ^ k)⁻¹ * M_exp * ‖F‖
  set G : ℝ → ℝ≥0∞ := sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)
  set Z2 : ℝ → ℝ≥0∞ := sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F)
  have hM_exp1 : 1 ≤ M_exp := by
    dsimp [M_exp]
    exact Real.one_le_exp (by positivity)
  have hMz0_nn : 0 ≤ M_z0 := by dsimp [M_z0]; positivity
  have hMz_nn : 0 ≤ M_z := by dsimp [M_z]; positivity
  have h_rpow_inv : p.ν ^ (-1 / 2 : ℝ) ≤ p.ν⁻¹ := by
    rw [← Real.rpow_neg_one p.ν]
    exact Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (by norm_num)
  have h_ge_le_Mz0 : C_ge * (p.ν ^ k_ge)⁻¹ * ‖F‖ ≤ M_z0 := by
    dsimp [M_z0]
    have h1 : C_ge * (p.ν ^ k_ge)⁻¹ * 1 ≤ C_ge * (p.ν ^ k_ge)⁻¹ * M_exp :=
      mul_le_mul_of_nonneg_left hM_exp1 (by positivity)
    simpa [mul_one] using mul_le_mul_of_nonneg_right h1 (norm_nonneg F)
  have hm_z1 : Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) :=
    measurable_sliceH1Norm p.c hsm_z hsm_zq hsm_zη
  have hm_z2 : Measurable Z2 :=
    measurable_sliceH2Norm p.c hsm_z hsm_zq hsm_zη hsm_D2
  have hk_ge_le : (p.ν ^ k_ge)⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    inv_pow_mono_le hν0 hν1 (by dsimp [k]; omega)
  have hC_ge_le : C_ge ≤ C := by dsimp [C]; linarith
  have hMz0_le_Mz : M_z0 ≤ M_z := by
    dsimp [M_z0, M_z]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
      (norm_nonneg F)
    exact mul_le_mul hC_ge_le hk_ge_le (by positivity) hC_pos.le
  -- Early `(0, p.H]` bound on `Z2`
  have hearly_raw :=
    early_duhamel_sLpNorm_bound hH0 hMz0_nn hm_g1 hpt_early
  have hH_511 : p.H ^ (5 / 11 : ℝ) ≤ Sig * p.ν⁻¹ := by
    calc p.H ^ (5 / 11 : ℝ) ≤ p.H ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hH1 (by norm_num)
      _ = p.H := Real.rpow_one p.H
      _ = Sig * p.ν⁻¹ := by rw [hH_eq, div_eq_mul_inv]
  have hH_sqrt : Real.sqrt p.H ≤ Sig * p.ν⁻¹ := by
    rw [Real.sqrt_eq_rpow]
    calc p.H ^ (1 / 2 : ℝ) ≤ p.H ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hH1 (by norm_num)
      _ = p.H := Real.rpow_one p.H
      _ = Sig * p.ν⁻¹ := by rw [hH_eq, div_eq_mul_inv]
  have hearly_bound :
      sLpNorm (13 / 8) p.H Z2 ≤
        ENNReal.ofReal (C_early * (p.ν ^ (k_ge + k_sm + 2))⁻¹ * M_exp * ‖F‖) := by
    have hG_le : sLpNorm (13 / 8) p.H G ≤ ENNReal.ofReal M_z0 :=
      hg_early.trans (ENNReal.ofReal_le_ofReal h_ge_le_Mz0)
    have hinner :
        ENNReal.ofReal (p.H ^ (5 / 11 : ℝ) * M_z0) +
          ENNReal.ofReal ((hsC0.toReal + 1) * Real.sqrt p.H) * sLpNorm (13 / 8) p.H G ≤
        ENNReal.ofReal ((hsC0.toReal + 2) * Sig * p.ν⁻¹ * M_z0) := by
      calc ENNReal.ofReal (p.H ^ (5 / 11 : ℝ) * M_z0) +
            ENNReal.ofReal ((hsC0.toReal + 1) * Real.sqrt p.H) * sLpNorm (13 / 8) p.H G
          ≤ ENNReal.ofReal (p.H ^ (5 / 11 : ℝ) * M_z0) +
              ENNReal.ofReal ((hsC0.toReal + 1) * Real.sqrt p.H) * ENNReal.ofReal M_z0 := by
            gcongr
        _ = ENNReal.ofReal
              (p.H ^ (5 / 11 : ℝ) * M_z0 + (hsC0.toReal + 1) * Real.sqrt p.H * M_z0) := by
            rw [← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal ((hsC0.toReal + 2) * Sig * p.ν⁻¹ * M_z0) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 : p.H ^ (5 / 11 : ℝ) + (hsC0.toReal + 1) * Real.sqrt p.H ≤
                (hsC0.toReal + 2) * (Sig * p.ν⁻¹) := by
              nlinarith [mul_le_mul_of_nonneg_left hH_sqrt (by linarith : (0 : ℝ) ≤ hsC0.toReal + 1)]
            calc p.H ^ (5 / 11 : ℝ) * M_z0 + (hsC0.toReal + 1) * Real.sqrt p.H * M_z0
                = (p.H ^ (5 / 11 : ℝ) + (hsC0.toReal + 1) * Real.sqrt p.H) * M_z0 := by ring
              _ ≤ ((hsC0.toReal + 2) * (Sig * p.ν⁻¹)) * M_z0 :=
                  mul_le_mul_of_nonneg_right h1 hMz0_nn
              _ = (hsC0.toReal + 2) * Sig * p.ν⁻¹ * M_z0 := by ring
    have houter :
        (C_sm * (p.ν ^ k_sm)⁻¹ * p.ν ^ (-1 / 2 : ℝ)) *
          ((hsC0.toReal + 2) * Sig * p.ν⁻¹ * M_z0) ≤
        C_early * (p.ν ^ (k_ge + k_sm + 2))⁻¹ * M_exp * ‖F‖ := by
      have hpref : C_sm * (p.ν ^ k_sm)⁻¹ * p.ν ^ (-1 / 2 : ℝ) ≤
          C_sm * (p.ν ^ k_sm)⁻¹ * p.ν⁻¹ :=
        mul_le_mul_of_nonneg_left h_rpow_inv (by positivity)
      calc (C_sm * (p.ν ^ k_sm)⁻¹ * p.ν ^ (-1 / 2 : ℝ)) *
            ((hsC0.toReal + 2) * Sig * p.ν⁻¹ * M_z0)
          ≤ (C_sm * (p.ν ^ k_sm)⁻¹ * p.ν⁻¹) *
              ((hsC0.toReal + 2) * Sig * p.ν⁻¹ * M_z0) :=
            mul_le_mul_of_nonneg_right hpref (by positivity)
        _ = C_early * ((p.ν ^ k_ge)⁻¹ * (p.ν ^ k_sm)⁻¹ * p.ν⁻¹ * p.ν⁻¹) * M_exp * ‖F‖ := by
            dsimp [C_early, M_z0]
            ring
        _ = C_early * (p.ν ^ (k_ge + k_sm + 2))⁻¹ * M_exp * ‖F‖ := by
            congr 2
            rw [pow_add, pow_add, pow_two, mul_inv, mul_inv, mul_inv]
            ring
    calc sLpNorm (13 / 8) p.H Z2
        ≤ ENNReal.ofReal (C_sm * (p.ν ^ k_sm)⁻¹ * p.ν ^ (-1 / 2 : ℝ)) *
            ENNReal.ofReal ((hsC0.toReal + 2) * Sig * p.ν⁻¹ * M_z0) :=
          hearly_raw.trans (mul_le_mul_of_nonneg_left hinner zero_le)
      _ = ENNReal.ofReal
            ((C_sm * (p.ν ^ k_sm)⁻¹ * p.ν ^ (-1 / 2 : ℝ)) *
              ((hsC0.toReal + 2) * Sig * p.ν⁻¹ * M_z0)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (C_early * (p.ν ^ (k_ge + k_sm + 2))⁻¹ * M_exp * ‖F‖) :=
          ENNReal.ofReal_le_ofReal houter
  -- Late `(p.H, ∞)` bound on `Z2`
  have hlate_raw :=
    late_duhamel_tailLpNorm_bound hH2 hν0 hC_sm.le hMz0_nn hm_g1 hpt_late
  have hlate_goal :
      tailLpNorm (-9 / 8) p.H Z2 ≤
        ENNReal.ofReal (C * p.ν ^ (-1 / 2 : ℝ)) *
          (ENNReal.ofReal (p.H ^ (-1 / 22 : ℝ) * M_z) +
            tailLpNorm (-9 / 8) (max 1 (p.H - 1)) G) := by
    refine hlate_raw.trans ?_
    have h8C : 8 * C_sm * p.ν ^ (-1 / 2 : ℝ) ≤ C * p.ν ^ (-1 / 2 : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hν0.le _)
      dsimp [C]
      linarith
    have hHMz : p.H ^ (-1 / 22 : ℝ) * M_z0 ≤ p.H ^ (-1 / 22 : ℝ) * M_z :=
      mul_le_mul_of_nonneg_left hMz0_le_Mz (Real.rpow_nonneg hH0.le _)
    gcongr
  have hlate_bound :
      tailLpNorm (-9 / 8) p.H Z2 ≤
        ENNReal.ofReal (C_late_z * (p.ν ^ (k_ge + 1))⁻¹ * M_exp * ‖F‖) := by
    have hG_tail_le : tailLpNorm (-9 / 8) (max 1 (p.H - 1)) G ≤ ENNReal.ofReal M_z0 :=
      hg_tail.trans (ENNReal.ofReal_le_ofReal h_ge_le_Mz0)
    have hH_neg : p.H ^ (-1 / 22 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hH1 (by norm_num)
    have hHMz0 : p.H ^ (-1 / 22 : ℝ) * M_z0 ≤ M_z0 := by
      calc p.H ^ (-1 / 22 : ℝ) * M_z0 ≤ 1 * M_z0 :=
            mul_le_mul_of_nonneg_right hH_neg hMz0_nn
        _ = M_z0 := one_mul M_z0
    have hinner :
        ENNReal.ofReal (p.H ^ (-1 / 22 : ℝ) * M_z0) +
          tailLpNorm (-9 / 8) (max 1 (p.H - 1)) G ≤
        ENNReal.ofReal (2 * M_z0) := by
      calc ENNReal.ofReal (p.H ^ (-1 / 22 : ℝ) * M_z0) +
            tailLpNorm (-9 / 8) (max 1 (p.H - 1)) G
          ≤ ENNReal.ofReal M_z0 + ENNReal.ofReal M_z0 :=
            add_le_add (ENNReal.ofReal_le_ofReal hHMz0) hG_tail_le
        _ = ENNReal.ofReal (2 * M_z0) := by
            rw [← ENNReal.ofReal_add hMz0_nn hMz0_nn, two_mul]
    have houter :
        (8 * C_sm * p.ν ^ (-1 / 2 : ℝ)) * (2 * M_z0) ≤
          C_late_z * (p.ν ^ (k_ge + 1))⁻¹ * M_exp * ‖F‖ := by
      have hpref : 8 * C_sm * p.ν ^ (-1 / 2 : ℝ) ≤ 8 * C_sm * p.ν⁻¹ :=
        mul_le_mul_of_nonneg_left h_rpow_inv (by positivity)
      calc (8 * C_sm * p.ν ^ (-1 / 2 : ℝ)) * (2 * M_z0)
          ≤ (8 * C_sm * p.ν⁻¹) * (2 * M_z0) :=
            mul_le_mul_of_nonneg_right hpref (by positivity)
        _ = C_late_z * ((p.ν ^ k_ge)⁻¹ * p.ν⁻¹) * M_exp * ‖F‖ := by
            dsimp [C_late_z, M_z0]
            ring
        _ = C_late_z * (p.ν ^ (k_ge + 1))⁻¹ * M_exp * ‖F‖ := by
            congr 2
            rw [pow_succ, mul_inv]
    calc tailLpNorm (-9 / 8) p.H Z2
        ≤ ENNReal.ofReal (8 * C_sm * p.ν ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (2 * M_z0) :=
          hlate_raw.trans (mul_le_mul_of_nonneg_left hinner zero_le)
      _ = ENNReal.ofReal ((8 * C_sm * p.ν ^ (-1 / 2 : ℝ)) * (2 * M_z0)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (C_late_z * (p.ν ^ (k_ge + 1))⁻¹ * M_exp * ‖F‖) :=
          ENNReal.ofReal_le_ofReal houter
  -- Escalate `early_bound` and `flatK` bound to `M_z`
  have hearly_lt_top : sLpNorm (13 / 8) p.H Z2 < ⊤ :=
    lt_of_le_of_lt hearly_bound ENNReal.ofReal_lt_top
  have hlate_lt_top : tailLpNorm (-9 / 8) p.H Z2 < ⊤ :=
    lt_of_le_of_lt hlate_bound ENNReal.ofReal_lt_top
  obtain ⟨hflatK_inHr, hflatK_bd⟩ :=
    hFlatK_p p d hreg hν_K' hAge (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F)
      hz_per hzq_per hzη_per hsm_z hsm_zq hsm_zη hsm_D2
      hz_mc.weak_q hz_mc.weak_eta hD2_00 hD2_01 hD2_10 hD2_11
      hearly_lt_top hlate_lt_top
  have hk_early_le : (p.ν ^ (k_ge + k_sm + 2))⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    inv_pow_mono_le hν0 hν1 (by dsimp [k]; omega)
  have hearly_goal : sLpNorm (13 / 8) p.H Z2 ≤ ENNReal.ofReal M_z := by
    refine hearly_bound.trans (ENNReal.ofReal_le_ofReal ?_)
    dsimp [M_z]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
      (norm_nonneg F)
    have hCe : C_early ≤ C := by
      dsimp [C]
      nlinarith [mul_nonneg hC_K.le (add_nonneg hC_early_pos.le hC_late_z_pos.le)]
    exact mul_le_mul hCe hk_early_le (by positivity) hC_pos.le
  have hflatK_goal : hNorm p.c bgp (flatK p.train (zOf F) (zqOf F) (zηOf F)) ≤
      ENNReal.ofReal M_z := by
    have hk1 : (p.ν ^ (k_ge + k_sm + 2))⁻¹ ≤ (p.ν ^ (k_ge + k_sm + 2))⁻¹ := le_rfl
    have hk2 : (p.ν ^ (k_ge + 1))⁻¹ ≤ (p.ν ^ (k_ge + k_sm + 2))⁻¹ :=
      inv_pow_mono_le hν0 hν1 (by omega)
    have hsum_Z2 :
        sLpNorm (13 / 8) p.H Z2 + tailLpNorm (-9 / 8) p.H Z2 ≤
          ENNReal.ofReal ((C_early + C_late_z) * (p.ν ^ (k_ge + k_sm + 2))⁻¹ * M_exp * ‖F‖) := by
      have h2' : tailLpNorm (-9 / 8) p.H Z2 ≤
          ENNReal.ofReal (C_late_z * (p.ν ^ (k_ge + k_sm + 2))⁻¹ * M_exp * ‖F‖) := by
        refine hlate_bound.trans (ENNReal.ofReal_le_ofReal ?_)
        gcongr
      calc sLpNorm (13 / 8) p.H Z2 + tailLpNorm (-9 / 8) p.H Z2
          ≤ ENNReal.ofReal (C_early * (p.ν ^ (k_ge + k_sm + 2))⁻¹ * M_exp * ‖F‖) +
              ENNReal.ofReal (C_late_z * (p.ν ^ (k_ge + k_sm + 2))⁻¹ * M_exp * ‖F‖) :=
            add_le_add hearly_bound h2'
        _ = ENNReal.ofReal ((C_early + C_late_z) * (p.ν ^ (k_ge + k_sm + 2))⁻¹ * M_exp * ‖F‖) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
    calc hNorm p.c bgp (flatK p.train (zOf F) (zqOf F) (zηOf F))
        ≤ ENNReal.ofReal (C_K * (p.ν ^ k_K)⁻¹) *
            ENNReal.ofReal ((C_early + C_late_z) * (p.ν ^ (k_ge + k_sm + 2))⁻¹ * M_exp * ‖F‖) :=
          hflatK_bd.trans (mul_le_mul_of_nonneg_left hsum_Z2 zero_le)
      _ = ENNReal.ofReal
            ((C_K * (C_early + C_late_z)) * (p.ν ^ k)⁻¹ * M_exp * ‖F‖) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hpow_k : (p.ν ^ k)⁻¹ = (p.ν ^ (k_ge + k_sm + 2))⁻¹ * (p.ν ^ k_K)⁻¹ := by
            dsimp [k]
            rw [show k_ge + k_sm + k_K + 2 = (k_ge + k_sm + 2) + k_K by omega,
              pow_add, mul_inv]
          rw [hpow_k]
          ring
      _ ≤ ENNReal.ofReal M_z := by
          refine ENNReal.ofReal_le_ofReal ?_
          dsimp [M_z]
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (norm_nonneg F)
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          dsimp [C]
          linarith
  refine ⟨hb0_cl, hb0_resp, hb0q, hb0η, hg_per, hgq, hgη, hg_src, hz_mc,
    hD2_00, hD2_01, hD2_10, hD2_11, hm_z1, hm_z2, ?_, hearly_goal, hlate_goal,
    hflatK_inHr, hflatK_goal⟩
  intro s hs
  exact (hz_sup s hs).trans (ENNReal.ofReal_le_ofReal hMz0_le_Mz)

end UnforcedLeray.Short.IIb

end
