import UnforcedLeray.Short.PartIIb.Sub.FlatInverseDesign
import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.FlatGraphD2Slice
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Part II-b, task `PartII-b:F7`: tail source estimate and global energy continuation (`SP 2269–2295`)

Source of record: `the November 2 reference manuscript`
(SP), lines 2269–2295, displays `short-bg:tail-source` at line 2281 and `short-bg:global-energy`
at line 2294:

  "Write `B_j(s) = (νs)^{j/2} ‖D^j b_0(s)‖_p`. Hölder gives
  `‖g(s)‖_{H¹} ≤ 𝒫_ν [ν⁻¹ s^{-85/44} B_2(s) + s^{-63/44}(ν^{-1/2} B_1(s) + B_0(s))]`.
  Each `B_j` has `L^p(s^{-9/8} ds)` norm at most `C ‖F‖_{H_p}`.
  For a factor `s^{-k} B_j`, weighted Hölder on `(T, ∞)` gives `T^{23/22 - k}`; hence the exponents
  in its `L¹` bound are `-39/44` and `-17/44`, respectively. The same expression belongs to
  `L^p(s^{-9/8} ds; H¹)`. Differentiated velocity energy and `(short-bg:train-late)` therefore give
  `M_z := sup_{s ≥ 0} ‖z(s)‖_{H¹} ≤ 𝒫_ν exp((a'Σ + C/(1+Σ))/ν + C ν³) ‖F‖_{H_p}`."

## Proved here (zero `sorry`)

1. `sMeas_Ioi`, `tailLpNorm`, `tailLpNorm_add_le`, `tailLpNorm_const_mul`, `tailLpNorm_mono_ae`:
   weighted `L^p((T, ∞), s^b ds)` Bochner seminorm and its Minkowski subadditivity, scaling, and
   a.e. monotonicity on `(T, ∞)`;
2. `tailLpNorm_sliceLpNorm_le_hNorm`, `tailLpNorm_sliceB0_le`, `tailLpNorm_sliceB1_le`,
   `tailLpNorm_sliceB2_le`: Tonelli bounds showing that `B_0(s)`, `B_1(s)`, `B_2(s)` have
   `L^p((T, ∞), s^{-9/8} ds)` norms bounded by `‖b_0'‖_{H_p}`, `√ν (‖√s b0q‖_{H_p} + ‖√s b0η‖_{H_p})`,
   and `ν ∑_{i,j} ‖s D²_{ij} b_0‖_{H_p}` (and hence by `C ‖F‖_{H_p}`);
3. `tail_holder_Ioi`, `tail_holder_85_44`, `tail_holder_63_44`, `tailLpNorm_rpow_mul_le`:
   the exact weighted Hölder inequality on `(T, ∞)` (`T > 0`) for `s^{-k} B(s)` (`k > 23/22`) giving
   the factor `T^{23/22 - k}` (exponents `-39/44` at `k = 85/44` and `-17/44` at `k = 63/44`), and
   the `L^p((T, ∞), s^{-9/8} ds)` domination on `T ≥ 1`;
4. `tailSource_integrals_of_slice_bound` and `tailSource_of_slice`: full proof that the pointwise
   slice bound `short-bg:tail-source` (`s ≥ 1`) and the global `H_p` bounds of `B_0, B_1, B_2` imply
   the `L¹((T, ∞); H¹)` and `L^p((T, ∞), s^{-9/8} ds; H¹)` bounds in `TailSource`;
5. `tailSourceAndGlobalEnergy_of_leaves`: conditional assembly of `TailSourceAndGlobalEnergy` from
   `TailSourceSliceBound` (`PartII-b:F7/1`) and `GlobalEnergyContinuation` (`PartII-b:F7/2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-! ## 1. The tail `L^p((T, ∞), s^b ds)` seminorm `tailLpNorm` -/

/-- The `L^p((T, ∞), s^b ds)` norm (`p = bgp = 11/4`, `1/p = 4/11`) of a nonnegative slice function
`N : ℝ → ℝ≥0∞`. -/
def tailLpNorm (b T : ℝ) (N : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ s in Ioi T, N s ^ bgp ∂sMeas b) ^ (4 / 11 : ℝ)

/-- Integrals against `sMeas b` over `(T, ∞)` (`T ≥ 0`) are integrals against `s ^ b`. -/
theorem sMeas_Ioi (b T : ℝ) (hT : 0 ≤ T) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ s in Ioi T, F s ∂sMeas b = ∫⁻ s in Ioi T, F s * ENNReal.ofReal (s ^ b) := by
  have hφ : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ b)) := by fun_prop
  have hset : Ioi T ∩ Ioi (0 : ℝ) = Ioi T :=
    Set.inter_eq_left.mpr (fun _ hx => lt_of_le_of_lt hT hx)
  unfold sMeas
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hset,
    lintegral_withDensity_eq_lintegral_mul _ hφ hF]
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply]
  exact mul_comm _ _

theorem tailLpNorm_add_le (b T : ℝ) {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    tailLpNorm b T (fun s => f s + g s) ≤ tailLpNorm b T f + tailLpNorm b T g := by
  unfold tailLpNorm
  have hinv : (4 / 11 : ℝ) = 1 / bgp := by norm_num [bgp]
  rw [hinv]
  exact ENNReal.lintegral_Lp_add_le hf.aemeasurable hg.aemeasurable bgp_gt_one.le

theorem tailLpNorm_const_mul (b T : ℝ) (K : ℝ≥0∞) (hK : K ≠ ⊤) (f : ℝ → ℝ≥0∞) :
    tailLpNorm b T (fun s => K * f s) = K * tailLpNorm b T f := by
  unfold tailLpNorm
  have hbgp : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have h411 : (0 : ℝ) ≤ 4 / 11 := by norm_num
  have hmul : bgp * (4 / 11 : ℝ) = 1 := by norm_num [bgp]
  have hpow : ∀ s, (K * f s) ^ bgp = K ^ bgp * f s ^ bgp :=
    fun s => ENNReal.mul_rpow_of_nonneg _ _ hbgp
  simp_rw [hpow]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg hbgp hK).ne,
    ENNReal.mul_rpow_of_nonneg _ _ h411, ← ENNReal.rpow_mul, hmul, ENNReal.rpow_one]

theorem tailLpNorm_mono_ae {b T : ℝ} {f g : ℝ → ℝ≥0∞}
    (h : ∀ᵐ s ∂volume, T < s → f s ≤ g s) :
    tailLpNorm b T f ≤ tailLpNorm b T g := by
  unfold tailLpNorm
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have h_sMeas : ∀ᵐ s ∂sMeas b, T < s → f s ≤ g s := by
    unfold sMeas
    exact withDensity_absolutelyContinuous _ _ (ae_restrict_of_ae h)
  refine lintegral_mono_ae ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mpr h_sMeas] with s hs
  exact ENNReal.rpow_le_rpow hs (by norm_num [bgp])

/-! ## 2. Tonelli `H_p` bounds for `sliceB0`, `sliceB1`, `sliceB2` on `(T, ∞)` -/

theorem tailLpNorm_sliceLpNorm_le_hNorm (c T : ℝ) {u : CProf} (hu : StronglyMeasurable u) :
    tailLpNorm (-9 / 8) T (sliceLpNorm c u) ≤ hNorm c bgp u := by
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := sfinite_avgμ c
  unfold tailLpNorm hNorm
  have hp0 : ENNReal.ofReal bgp ≠ 0 := by norm_num [bgp]
  have hpt : ENNReal.ofReal bgp ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hto : (ENNReal.ofReal bgp).toReal = bgp :=
    ENNReal.toReal_ofReal (by norm_num [bgp])
  have hinv : 1 / bgp = (4 / 11 : ℝ) := by norm_num [bgp]
  rw [hto, hinv]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hpow : ∀ s : ℝ,
      sliceLpNorm c u s ^ bgp = ∫⁻ z, ‖u (s, z)‖ₑ ^ bgp ∂UnforcedLeray.Cyl.avgμ c := by
    intro s
    rw [sliceLpNorm_eq_lintegral, ← ENNReal.rpow_mul]
    have hmul : (4 / 11 : ℝ) * bgp = 1 := by norm_num [bgp]
    rw [hmul, ENNReal.rpow_one]
  simp_rw [hpow]
  refine (setLIntegral_le_lintegral _ _).trans ?_
  have hm : Measurable (fun x : Coord => ‖u x‖ₑ ^ bgp) :=
    (hu.measurable.enorm).pow_const bgp
  rw [hMeas_bgp_eq_prod c, lintegral_prod _ hm.aemeasurable]

theorem measurable_sliceB0 (c : ℝ) {b0' : CProf} (hsm0 : StronglyMeasurable b0') :
    Measurable (sliceB0 c b0') :=
  measurable_sliceLpNorm c hsm0

theorem measurable_sliceB1 (ν c : ℝ) {b0q b0η : CProf}
    (hsmq : StronglyMeasurable b0q) (hsmη : StronglyMeasurable b0η) :
    Measurable (sliceB1 ν c b0q b0η) := by
  unfold sliceB1
  have hmq := measurable_sliceLpNorm c hsmq
  have hmη := measurable_sliceLpNorm c hsmη
  fun_prop

theorem measurable_sliceB2 (ν c : ℝ) {D2 : Fin 2 → Fin 2 → CProf}
    (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j)) :
    Measurable (sliceB2 ν c D2) := by
  unfold sliceB2
  have hm : ∀ i j, Measurable (sliceLpNorm c (D2 i j)) :=
    fun i j => measurable_sliceLpNorm c (hsmD2 i j)
  refine Measurable.mul (by fun_prop) ?_
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => hm i j

theorem tailLpNorm_sliceB0_le (c T : ℝ) {b0' : CProf} (hsm0 : StronglyMeasurable b0') :
    tailLpNorm (-9 / 8) T (sliceB0 c b0') ≤ hNorm c bgp b0' :=
  tailLpNorm_sliceLpNorm_le_hNorm c T hsm0

theorem tailLpNorm_sliceB1_le {ν c T : ℝ} (hν : 0 ≤ ν) {b0q b0η : CProf}
    (hsmq : StronglyMeasurable b0q) (hsmη : StronglyMeasurable b0η) :
    tailLpNorm (-9 / 8) T (sliceB1 ν c b0q b0η) ≤
      ENNReal.ofReal (Real.sqrt ν) * (hNorm c bgp (sqrtS b0q) + hNorm c bgp (sqrtS b0η)) := by
  have hsm_sq : StronglyMeasurable (sqrtS b0q) :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp continuous_fst)).stronglyMeasurable.smul hsmq
  have hsm_sη : StronglyMeasurable (sqrtS b0η) :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp continuous_fst)).stronglyMeasurable.smul hsmη
  have hpt : ∀ᵐ s ∂volume, T < s →
      sliceB1 ν c b0q b0η s ≤
        ENNReal.ofReal (Real.sqrt ν) *
          (sliceLpNorm c (sqrtS b0q) s + sliceLpNorm c (sqrtS b0η) s) := by
    refine Eventually.of_forall fun s _ => ?_
    unfold sliceB1
    rw [Real.sqrt_mul hν, ENNReal.ofReal_mul (Real.sqrt_nonneg ν), mul_assoc, mul_add,
      ← sliceLpNorm_sqrtS c b0q s, ← sliceLpNorm_sqrtS c b0η s]
  calc tailLpNorm (-9 / 8) T (sliceB1 ν c b0q b0η)
      ≤ tailLpNorm (-9 / 8) T (fun s =>
          ENNReal.ofReal (Real.sqrt ν) *
            (sliceLpNorm c (sqrtS b0q) s + sliceLpNorm c (sqrtS b0η) s)) :=
        tailLpNorm_mono_ae hpt
    _ = ENNReal.ofReal (Real.sqrt ν) *
          tailLpNorm (-9 / 8) T (fun s =>
            sliceLpNorm c (sqrtS b0q) s + sliceLpNorm c (sqrtS b0η) s) :=
        tailLpNorm_const_mul (-9 / 8) T _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal (Real.sqrt ν) *
          (tailLpNorm (-9 / 8) T (sliceLpNorm c (sqrtS b0q)) +
            tailLpNorm (-9 / 8) T (sliceLpNorm c (sqrtS b0η))) := by
        gcongr
        exact tailLpNorm_add_le (-9 / 8) T (measurable_sliceLpNorm c hsm_sq)
          (measurable_sliceLpNorm c hsm_sη)
    _ ≤ ENNReal.ofReal (Real.sqrt ν) * (hNorm c bgp (sqrtS b0q) + hNorm c bgp (sqrtS b0η)) := by
        gcongr
        · exact tailLpNorm_sliceLpNorm_le_hNorm c T hsm_sq
        · exact tailLpNorm_sliceLpNorm_le_hNorm c T hsm_sη

theorem tailLpNorm_sliceB2_le {ν c T : ℝ} (hν : 0 ≤ ν) (hT : 0 ≤ T)
    {D2 : Fin 2 → Fin 2 → CProf} (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j)) :
    tailLpNorm (-9 / 8) T (sliceB2 ν c D2) ≤
      ENNReal.ofReal ν * ∑ i : Fin 2, ∑ j : Fin 2, hNorm c bgp (mulS (D2 i j)) := by
  have hsm_m : ∀ i j, StronglyMeasurable (mulS (D2 i j)) := fun i j =>
    (Complex.continuous_ofReal.comp continuous_fst).stronglyMeasurable.smul (hsmD2 i j)
  have hm_m : ∀ i j, Measurable (sliceLpNorm c (mulS (D2 i j))) :=
    fun i j => measurable_sliceLpNorm c (hsm_m i j)
  have hpt : ∀ᵐ s ∂volume, T < s →
      sliceB2 ν c D2 s ≤
        ENNReal.ofReal ν * ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (mulS (D2 i j)) s := by
    refine Eventually.of_forall fun s hs => ?_
    have hs0 : 0 ≤ s := le_trans hT hs.le
    unfold sliceB2
    rw [ENNReal.ofReal_mul hν, mul_assoc, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) zero_le
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (sliceLpNorm_mulS c (D2 i j) hs0).symm
  calc tailLpNorm (-9 / 8) T (sliceB2 ν c D2)
      ≤ tailLpNorm (-9 / 8) T (fun s =>
          ENNReal.ofReal ν * ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (mulS (D2 i j)) s) :=
        tailLpNorm_mono_ae hpt
    _ = ENNReal.ofReal ν *
          tailLpNorm (-9 / 8) T (fun s =>
            ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (mulS (D2 i j)) s) :=
        tailLpNorm_const_mul (-9 / 8) T _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal ν * ∑ i : Fin 2, ∑ j : Fin 2,
          tailLpNorm (-9 / 8) T (sliceLpNorm c (mulS (D2 i j))) := by
        gcongr
        simp_rw [Fin.sum_univ_two]
        calc tailLpNorm (-9 / 8) T (fun s =>
              (sliceLpNorm c (mulS (D2 0 0)) s + sliceLpNorm c (mulS (D2 0 1)) s) +
                (sliceLpNorm c (mulS (D2 1 0)) s + sliceLpNorm c (mulS (D2 1 1)) s))
            ≤ tailLpNorm (-9 / 8) T (fun s =>
                sliceLpNorm c (mulS (D2 0 0)) s + sliceLpNorm c (mulS (D2 0 1)) s) +
              tailLpNorm (-9 / 8) T (fun s =>
                sliceLpNorm c (mulS (D2 1 0)) s + sliceLpNorm c (mulS (D2 1 1)) s) :=
              tailLpNorm_add_le (-9 / 8) T ((hm_m 0 0).add (hm_m 0 1)) ((hm_m 1 0).add (hm_m 1 1))
          _ ≤ (tailLpNorm (-9 / 8) T (sliceLpNorm c (mulS (D2 0 0))) +
                tailLpNorm (-9 / 8) T (sliceLpNorm c (mulS (D2 0 1)))) +
              (tailLpNorm (-9 / 8) T (sliceLpNorm c (mulS (D2 1 0))) +
                tailLpNorm (-9 / 8) T (sliceLpNorm c (mulS (D2 1 1)))) :=
              add_le_add (tailLpNorm_add_le (-9 / 8) T (hm_m 0 0) (hm_m 0 1))
                (tailLpNorm_add_le (-9 / 8) T (hm_m 1 0) (hm_m 1 1))
    _ ≤ ENNReal.ofReal ν * ∑ i : Fin 2, ∑ j : Fin 2, hNorm c bgp (mulS (D2 i j)) := by
        gcongr with i _ j _
        exact tailLpNorm_sliceLpNorm_le_hNorm c T (hsm_m i j)

/-! ## 3. Weighted Hölder on `(T, ∞)` (`SP 2283–2287`) -/

/-- Pointwise identity `(x · s^{-9/22})^{11/4} = x^{11/4} · s^{-9/8}` for `s > 0`. -/
theorem tail_bgp_factor (s : ℝ) (hs : 0 < s) (x : ℝ≥0∞) :
    (x * ENNReal.ofReal (s ^ (-9 / 22 : ℝ))) ^ bgp =
      x ^ bgp * ENNReal.ofReal (s ^ (-9 / 8 : ℝ)) := by
  have hbgp : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have hmul : (-9 / 22 : ℝ) * bgp = -9 / 8 := by norm_num [bgp]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hbgp,
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hs.le (-9 / 22 : ℝ)) hbgp,
    ← Real.rpow_mul hs.le, hmul]

/-- **Weighted Hölder on `(T, ∞)`** (SP 2284–2286: "For a factor `s^{-k} B_j`, weighted Hölder on
`(T, ∞)` gives `T^{23/22 - k}`"): for `k > 23/22` and `T > 0`,
`∫_T^∞ s^{-k} B(s) ds ≤ ((22k - 23)/14)^{-7/11} T^{23/22 - k} ‖B‖_{L^p((T, ∞), s^{-9/8} ds)}`. -/
theorem tail_holder_Ioi {k T : ℝ} (hk : 23 / 22 < k) (hT : 0 < T)
    {B : ℝ → ℝ≥0∞} (hB : Measurable B) :
    ∫⁻ s in Ioi T, ENNReal.ofReal (s ^ (-k)) * B s ≤
      ENNReal.ofReal (((22 * k - 23) / 14)⁻¹ ^ (7 / 11 : ℝ) * T ^ (23 / 22 - k)) *
        tailLpNorm (-9 / 8) T B := by
  have hpq : Real.HolderConjugate bgp (11 / 7 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num [bgp], by norm_num [bgp]⟩
  have hm1 : Measurable (fun s : ℝ => B s * ENNReal.ofReal (s ^ (-9 / 22 : ℝ))) := by fun_prop
  have hm2 : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ (9 / 22 - k))) := by fun_prop
  have hsplit : ∫⁻ s in Ioi T, ENNReal.ofReal (s ^ (-k)) * B s =
      ∫⁻ s in Ioi T,
        (B s * ENNReal.ofReal (s ^ (-9 / 22 : ℝ))) * ENNReal.ofReal (s ^ (9 / 22 - k)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : 0 < s := lt_trans hT hs
    have hexp : -9 / 22 + (9 / 22 - k) = -k := by ring
    rw [mul_comm (ENNReal.ofReal (s ^ (-k))) (B s), mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _), ← Real.rpow_add hs0, hexp]
  have hholder :
      ∫⁻ s in Ioi T,
        (B s * ENNReal.ofReal (s ^ (-9 / 22 : ℝ))) * ENNReal.ofReal (s ^ (9 / 22 - k)) ≤
      (∫⁻ s in Ioi T, (B s * ENNReal.ofReal (s ^ (-9 / 22 : ℝ))) ^ bgp) ^ (1 / bgp) *
        (∫⁻ s in Ioi T, ENNReal.ofReal (s ^ (9 / 22 - k)) ^ (11 / 7 : ℝ)) ^ (1 / (11 / 7 : ℝ)) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioi T)) hpq hm1.aemeasurable hm2.aemeasurable
  have hA : ∫⁻ s in Ioi T, (B s * ENNReal.ofReal (s ^ (-9 / 22 : ℝ))) ^ bgp =
      ∫⁻ s in Ioi T, B s ^ bgp ∂sMeas (-9 / 8) := by
    rw [sMeas_Ioi (-9 / 8) T hT.le (fun s => B s ^ bgp) (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    exact tail_bgp_factor s (lt_trans hT hs) (B s)
  set a : ℝ := (9 / 22 - k) * (11 / 7)
  have ha_lt : a < -1 := by
    dsimp [a]
    linarith
  have ha1_eq : -(a + 1) = (22 * k - 23) / 14 := by
    dsimp [a]
    ring
  have hpow : ∀ s ∈ Ioi T,
      ENNReal.ofReal (s ^ (9 / 22 - k)) ^ (11 / 7 : ℝ) = ENNReal.ofReal (s ^ a) := by
    intro s hs
    have hs0 : 0 < s := lt_trans hT hs
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hs0.le _) (by norm_num),
      ← Real.rpow_mul hs0.le]
  have hint : IntegrableOn (fun s : ℝ => s ^ a) (Ioi T) volume :=
    integrableOn_Ioi_rpow_of_lt ha_lt hT
  have hnn : ∀ᵐ s ∂volume.restrict (Ioi T), 0 ≤ s ^ a :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => Real.rpow_nonneg (lt_trans hT hs).le a)
  have hB_int : ∫⁻ s in Ioi T, ENNReal.ofReal (s ^ (9 / 22 - k)) ^ (11 / 7 : ℝ) =
      ENNReal.ofReal (((22 * k - 23) / 14)⁻¹ * T ^ (a + 1)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioi hpow,
      ← ofReal_integral_eq_lintegral_ofReal hint hnn,
      integral_Ioi_rpow_of_lt ha_lt hT]
    congr 1
    rw [div_eq_inv_mul, mul_neg, ← neg_mul, ← inv_neg, ha1_eq]
  have hpos_coef : 0 ≤ ((22 * k - 23) / 14)⁻¹ := by
    rw [← ha1_eq]
    exact inv_nonneg.mpr (by linarith)
  have hC : ENNReal.ofReal (((22 * k - 23) / 14)⁻¹ * T ^ (a + 1)) ^ (1 / (11 / 7 : ℝ)) =
      ENNReal.ofReal (((22 * k - 23) / 14)⁻¹ ^ (7 / 11 : ℝ) * T ^ (23 / 22 - k)) := by
    have h711 : (1 / (11 / 7 : ℝ)) = 7 / 11 := by norm_num
    have hexp : (a + 1) * (7 / 11 : ℝ) = 23 / 22 - k := by
      dsimp [a]
      ring
    rw [h711,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hpos_coef (Real.rpow_nonneg hT.le _))
        (by norm_num),
      Real.mul_rpow hpos_coef (Real.rpow_nonneg hT.le _),
      ← Real.rpow_mul hT.le, hexp]
  have h1bgp : (1 / bgp : ℝ) = 4 / 11 := by norm_num [bgp]
  rw [hsplit]
  refine hholder.trans (le_of_eq ?_)
  rw [hA, hB_int, hC, h1bgp, mul_comm]
  rfl

/-- Specialization of `tail_holder_Ioi` to `k = 85 / 44` (`23/22 - 85/44 = -39/44 < 0`) on `T ≥ 1`. -/
theorem tail_holder_85_44 {T : ℝ} (hT1 : 1 ≤ T) {B : ℝ → ℝ≥0∞} (hB : Measurable B) :
    ∫⁻ s in Ioi T, ENNReal.ofReal (s ^ (-85 / 44 : ℝ)) * B s ≤
      ENNReal.ofReal 2 * tailLpNorm (-9 / 8) T B := by
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  have hk : (23 / 22 : ℝ) < 85 / 44 := by norm_num
  have hneg : (-85 / 44 : ℝ) = -(85 / 44 : ℝ) := by norm_num
  simp_rw [hneg]
  refine (tail_holder_Ioi hk hT0 hB).trans
    (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
  have hT_pow : T ^ (23 / 22 - (85 / 44 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num)
  have hcoef_le : ((22 * (85 / 44 : ℝ) - 23) / 14)⁻¹ ^ (7 / 11 : ℝ) ≤ 2 := by
    have hbase : ((22 * (85 / 44 : ℝ) - 23) / 14)⁻¹ ≤ 2 := by norm_num
    have hbase0 : 0 ≤ ((22 * (85 / 44 : ℝ) - 23) / 14)⁻¹ := by norm_num
    calc ((22 * (85 / 44 : ℝ) - 23) / 14)⁻¹ ^ (7 / 11 : ℝ)
        ≤ (2 : ℝ) ^ (7 / 11 : ℝ) := Real.rpow_le_rpow hbase0 hbase (by norm_num)
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  calc ((22 * (85 / 44 : ℝ) - 23) / 14)⁻¹ ^ (7 / 11 : ℝ) * T ^ (23 / 22 - (85 / 44 : ℝ))
      ≤ 2 * 1 := mul_le_mul hcoef_le hT_pow (Real.rpow_nonneg hT0.le _) (by norm_num)
    _ = 2 := mul_one 2

/-- Specialization of `tail_holder_Ioi` to `k = 63 / 44` (`23/22 - 63/44 = -17/44 < 0`) on `T ≥ 1`. -/
theorem tail_holder_63_44 {T : ℝ} (hT1 : 1 ≤ T) {B : ℝ → ℝ≥0∞} (hB : Measurable B) :
    ∫⁻ s in Ioi T, ENNReal.ofReal (s ^ (-63 / 44 : ℝ)) * B s ≤
      ENNReal.ofReal 2 * tailLpNorm (-9 / 8) T B := by
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  have hk : (23 / 22 : ℝ) < 63 / 44 := by norm_num
  have hneg : (-63 / 44 : ℝ) = -(63 / 44 : ℝ) := by norm_num
  simp_rw [hneg]
  refine (tail_holder_Ioi hk hT0 hB).trans
    (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
  have hT_pow : T ^ (23 / 22 - (63 / 44 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num)
  have hcoef_le : ((22 * (63 / 44 : ℝ) - 23) / 14)⁻¹ ^ (7 / 11 : ℝ) ≤ 2 := by
    have hbase : ((22 * (63 / 44 : ℝ) - 23) / 14)⁻¹ ≤ 2 := by norm_num
    have hbase0 : 0 ≤ ((22 * (63 / 44 : ℝ) - 23) / 14)⁻¹ := by norm_num
    calc ((22 * (63 / 44 : ℝ) - 23) / 14)⁻¹ ^ (7 / 11 : ℝ)
        ≤ (2 : ℝ) ^ (7 / 11 : ℝ) := Real.rpow_le_rpow hbase0 hbase (by norm_num)
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  calc ((22 * (63 / 44 : ℝ) - 23) / 14)⁻¹ ^ (7 / 11 : ℝ) * T ^ (23 / 22 - (63 / 44 : ℝ))
      ≤ 2 * 1 := mul_le_mul hcoef_le hT_pow (Real.rpow_nonneg hT0.le _) (by norm_num)
    _ = 2 := mul_one 2

/-- On `Ioi T` (`1 ≤ T`) with `k ≤ 0`, `s ^ k ≤ 1`, so `tailLpNorm (-9/8) T (s^k · B) ≤ tailLpNorm (-9/8) T B`. -/
theorem tailLpNorm_rpow_mul_le {k T : ℝ} (hk : k ≤ 0) (hT1 : 1 ≤ T) (B : ℝ → ℝ≥0∞) :
    tailLpNorm (-9 / 8) T (fun s => ENNReal.ofReal (s ^ k) * B s) ≤ tailLpNorm (-9 / 8) T B := by
  refine tailLpNorm_mono_ae (Eventually.of_forall fun s hs => ?_)
  have hs1 : 1 ≤ s := le_trans hT1 hs.le
  have hpow : s ^ k ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 hk
  calc ENNReal.ofReal (s ^ k) * B s
      ≤ ENNReal.ofReal 1 * B s :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hpow) zero_le
    _ = B s := by rw [ENNReal.ofReal_one, one_mul]

/-! ## 4. Full proof of the `L¹((T, ∞); H¹)` and `L^p((T, ∞), s^{-9/8} ds; H¹)` bounds from the slice bound -/

/-- The right-hand side envelope of `short-bg:tail-source` (SP 2281) at age `s`:
`ν⁻¹ s^{-85/44} B_2(s) + s^{-63/44} (ν^{-1/2} B_1(s) + B_0(s))`. -/
def tailSliceRHS (ν c : ℝ) (b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (ν⁻¹ * s ^ (-85 / 44 : ℝ)) * sliceB2 ν c D2 s +
    ENNReal.ofReal (s ^ (-63 / 44 : ℝ)) *
      (ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * sliceB1 ν c b0q b0η s + sliceB0 c b0' s)

theorem measurable_tailSliceRHS (ν c : ℝ) {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j)) :
    Measurable (tailSliceRHS ν c b0' b0q b0η D2) := by
  unfold tailSliceRHS
  have hm0 := measurable_sliceB0 c hsm0
  have hm1 := measurable_sliceB1 ν c hsmq hsmη
  have hm2 := measurable_sliceB2 ν c hsmD2
  fun_prop

/-- **Core integral bound for `TailSource` (SP 2281–2288)**: if `sliceH1Norm p.c g gq gη s` is
bounded a.e. on `s ≥ 1` by `M * tailSliceRHS ν c b0' b0q b0η D2 s` and `b0', b0q, b0η, D2` obey
the global `H_p` free-graph bounds with constant `C_G`, then for every `T ≥ 1` (`0 < ν ≤ 1`),
`(∫⁻ s in Ioi T, sliceH1Norm c g gq gη s) + tailLpNorm (-9/8) T (sliceH1Norm c g gq gη)`
is bounded by `21 * M * C_G * ν⁻¹ * hNorm c bgp F`. -/
theorem tailSource_integrals_of_slice_bound {ν c M C_G : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hM0 : 0 ≤ M) (hCG0 : 0 ≤ C_G)
    {F b0' b0q b0η g gq gη : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j))
    (hb0_bd : hNorm c bgp b0' ≤ ENNReal.ofReal C_G * hNorm c bgp F)
    (hbq_bd : ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS b0q) ≤
      ENNReal.ofReal C_G * hNorm c bgp F)
    (hbη_bd : ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS b0η) ≤
      ENNReal.ofReal C_G * hNorm c bgp F)
    (hD2_bd : ∀ i j, ENNReal.ofReal ν * hNorm c bgp (mulS (D2 i j)) ≤
      ENNReal.ofReal C_G * hNorm c bgp F)
    (hslice : ∀ᵐ s ∂volume, 1 ≤ s →
      sliceH1Norm c g gq gη s ≤ ENNReal.ofReal M * tailSliceRHS ν c b0' b0q b0η D2 s)
    (T : ℝ) (hT1 : 1 ≤ T) :
    (∫⁻ s in Ioi T, sliceH1Norm c g gq gη s) +
        tailLpNorm (-9 / 8) T (sliceH1Norm c g gq gη) ≤
      ENNReal.ofReal (21 * M * C_G * ν⁻¹) * hNorm c bgp F := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT1
  have hmB0 := measurable_sliceB0 c hsm0
  have hmB1 := measurable_sliceB1 ν c hsmq hsmη
  have hmB2 := measurable_sliceB2 ν c hsmD2
  have h1_le_inv : (1 : ℝ) ≤ ν⁻¹ := (one_le_inv₀ hν0).mpr hν1
  have h_rpow_le_inv : ν ^ (-1 / 2 : ℝ) ≤ ν⁻¹ := by
    rw [← Real.rpow_neg_one ν]
    exact Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (by norm_num)
  -- 1. `tailLpNorm` bounds on `sliceB0`, `sliceB1`, `sliceB2`.
  have hB0_lp : tailLpNorm (-9 / 8) T (sliceB0 c b0') ≤
      ENNReal.ofReal (C_G * ν⁻¹) * hNorm c bgp F := by
    calc tailLpNorm (-9 / 8) T (sliceB0 c b0')
        ≤ ENNReal.ofReal C_G * hNorm c bgp F :=
          (tailLpNorm_sliceB0_le c T hsm0).trans hb0_bd
      _ ≤ ENNReal.ofReal (C_G * ν⁻¹) * hNorm c bgp F := by
          gcongr
          exact le_mul_of_one_le_right hCG0 h1_le_inv
  have hB1_lp : ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * tailLpNorm (-9 / 8) T (sliceB1 ν c b0q b0η) ≤
      ENNReal.ofReal (2 * C_G * ν⁻¹) * hNorm c bgp F := by
    have hB1_raw : tailLpNorm (-9 / 8) T (sliceB1 ν c b0q b0η) ≤
        ENNReal.ofReal (2 * C_G) * hNorm c bgp F := by
      calc tailLpNorm (-9 / 8) T (sliceB1 ν c b0q b0η)
          ≤ ENNReal.ofReal (Real.sqrt ν) *
              (hNorm c bgp (sqrtS b0q) + hNorm c bgp (sqrtS b0η)) :=
            tailLpNorm_sliceB1_le hν0.le hsmq hsmη
        _ = ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS b0q) +
              ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS b0η) := mul_add _ _ _
        _ ≤ ENNReal.ofReal C_G * hNorm c bgp F + ENNReal.ofReal C_G * hNorm c bgp F :=
            add_le_add hbq_bd hbη_bd
        _ = ENNReal.ofReal (2 * C_G) * hNorm c bgp F := by
            rw [← add_mul, ← ENNReal.ofReal_add hCG0 hCG0, two_mul]
    calc ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * tailLpNorm (-9 / 8) T (sliceB1 ν c b0q b0η)
        ≤ ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal (2 * C_G) * hNorm c bgp F) := by
          gcongr
      _ = ENNReal.ofReal (2 * C_G * ν⁻¹) * hNorm c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hν0.le)]
          congr 2; ring
  have hB2_lp : ENNReal.ofReal ν⁻¹ * tailLpNorm (-9 / 8) T (sliceB2 ν c D2) ≤
      ENNReal.ofReal (4 * C_G * ν⁻¹) * hNorm c bgp F := by
    have hB2_raw : tailLpNorm (-9 / 8) T (sliceB2 ν c D2) ≤
        ENNReal.ofReal (4 * C_G) * hNorm c bgp F := by
      calc tailLpNorm (-9 / 8) T (sliceB2 ν c D2)
          ≤ ENNReal.ofReal ν * ∑ i : Fin 2, ∑ j : Fin 2, hNorm c bgp (mulS (D2 i j)) :=
            tailLpNorm_sliceB2_le hν0.le hT0 hsmD2
        _ = ∑ i : Fin 2, ∑ j : Fin 2, ENNReal.ofReal ν * hNorm c bgp (mulS (D2 i j)) := by
            simp_rw [Finset.mul_sum]
        _ ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, (ENNReal.ofReal C_G * hNorm c bgp F) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hD2_bd i j
        _ = ENNReal.ofReal (4 * C_G) * hNorm c bgp F := by
            rw [Fin.sum_univ_two, Fin.sum_univ_two, ← add_mul, ← add_mul]
            congr 1
            rw [← ENNReal.ofReal_add hCG0 hCG0,
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
    calc ENNReal.ofReal ν⁻¹ * tailLpNorm (-9 / 8) T (sliceB2 ν c D2)
        ≤ ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal (4 * C_G) * hNorm c bgp F) :=
          mul_le_mul_of_nonneg_left hB2_raw zero_le
      _ = ENNReal.ofReal (4 * C_G * ν⁻¹) * hNorm c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hν0.le)]
          congr 2; ring
  -- 2. Pointwise split of `tailSliceRHS` into `term2 + term10`.
  set term2 : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal (s ^ (-85 / 44 : ℝ)) * sliceB2 ν c D2 s)
  set B10 : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * sliceB1 ν c b0q b0η s + sliceB0 c b0' s
  set term10 : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-63 / 44 : ℝ)) * B10 s
  have hmB10 : Measurable B10 := (hmB1.const_mul _).add hmB0
  have hm_term2 : Measurable term2 := by dsimp [term2]; fun_prop
  have hm_term10 : Measurable term10 := by dsimp [term10]; fun_prop
  have hRHS_eq : ∀ s : ℝ, tailSliceRHS ν c b0' b0q b0η D2 s = term2 s + term10 s := by
    intro s
    unfold tailSliceRHS
    dsimp [term2, term10, B10]
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hν0.le), mul_assoc]
  have hB10_lp : tailLpNorm (-9 / 8) T B10 ≤
      ENNReal.ofReal (3 * C_G * ν⁻¹) * hNorm c bgp F := by
    calc tailLpNorm (-9 / 8) T B10
        ≤ tailLpNorm (-9 / 8) T
            (fun s => ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * sliceB1 ν c b0q b0η s) +
          tailLpNorm (-9 / 8) T (sliceB0 c b0') :=
          tailLpNorm_add_le (-9 / 8) T (hmB1.const_mul _) hmB0
      _ = ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * tailLpNorm (-9 / 8) T (sliceB1 ν c b0q b0η) +
          tailLpNorm (-9 / 8) T (sliceB0 c b0') := by
          rw [tailLpNorm_const_mul (-9 / 8) T _ ENNReal.ofReal_ne_top _]
      _ ≤ ENNReal.ofReal (2 * C_G * ν⁻¹) * hNorm c bgp F +
          ENNReal.ofReal (C_G * ν⁻¹) * hNorm c bgp F := add_le_add hB1_lp hB0_lp
      _ = ENNReal.ofReal (3 * C_G * ν⁻¹) * hNorm c bgp F := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2; ring
  -- 3. `L¹(T, ∞)` bound on `tailSliceRHS`.
  have hL1_RHS : ∫⁻ s in Ioi T, tailSliceRHS ν c b0' b0q b0η D2 s ≤
      ENNReal.ofReal (14 * C_G * ν⁻¹) * hNorm c bgp F := by
    simp_rw [hRHS_eq]
    rw [lintegral_add_left hm_term2]
    have hL1_2 : ∫⁻ s in Ioi T, term2 s ≤
        ENNReal.ofReal (8 * C_G * ν⁻¹) * hNorm c bgp F := by
      dsimp [term2]
      rw [lintegral_const_mul _ (by fun_prop)]
      calc ENNReal.ofReal ν⁻¹ *
            ∫⁻ s in Ioi T, ENNReal.ofReal (s ^ (-85 / 44 : ℝ)) * sliceB2 ν c D2 s
          ≤ ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal 2 * tailLpNorm (-9 / 8) T (sliceB2 ν c D2)) :=
            mul_le_mul_of_nonneg_left (tail_holder_85_44 hT1 hmB2) zero_le
        _ = ENNReal.ofReal 2 * (ENNReal.ofReal ν⁻¹ * tailLpNorm (-9 / 8) T (sliceB2 ν c D2)) := by
            ring
        _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (4 * C_G * ν⁻¹) * hNorm c bgp F) :=
            mul_le_mul_of_nonneg_left hB2_lp zero_le
        _ = ENNReal.ofReal (8 * C_G * ν⁻¹) * hNorm c bgp F := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
            congr 2; ring
    have hL1_10 : ∫⁻ s in Ioi T, term10 s ≤
        ENNReal.ofReal (6 * C_G * ν⁻¹) * hNorm c bgp F := by
      calc ∫⁻ s in Ioi T, term10 s
          ≤ ENNReal.ofReal 2 * tailLpNorm (-9 / 8) T B10 := tail_holder_63_44 hT1 hmB10
        _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (3 * C_G * ν⁻¹) * hNorm c bgp F) :=
            mul_le_mul_of_nonneg_left hB10_lp zero_le
        _ = ENNReal.ofReal (6 * C_G * ν⁻¹) * hNorm c bgp F := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
            congr 2; ring
    calc (∫⁻ s in Ioi T, term2 s) + ∫⁻ s in Ioi T, term10 s
        ≤ ENNReal.ofReal (8 * C_G * ν⁻¹) * hNorm c bgp F +
            ENNReal.ofReal (6 * C_G * ν⁻¹) * hNorm c bgp F := add_le_add hL1_2 hL1_10
      _ = ENNReal.ofReal (14 * C_G * ν⁻¹) * hNorm c bgp F := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2; ring
  -- 4. `tailLpNorm` bound on `tailSliceRHS`.
  have hLp_RHS : tailLpNorm (-9 / 8) T (tailSliceRHS ν c b0' b0q b0η D2) ≤
      ENNReal.ofReal (7 * C_G * ν⁻¹) * hNorm c bgp F := by
    have h_eq : tailSliceRHS ν c b0' b0q b0η D2 = fun s => term2 s + term10 s :=
      funext hRHS_eq
    rw [h_eq]
    have hLp_2 : tailLpNorm (-9 / 8) T term2 ≤
        ENNReal.ofReal (4 * C_G * ν⁻¹) * hNorm c bgp F := by
      dsimp [term2]
      rw [tailLpNorm_const_mul (-9 / 8) T _ ENNReal.ofReal_ne_top _]
      exact (mul_le_mul_of_nonneg_left
        (tailLpNorm_rpow_mul_le (by norm_num) hT1 (sliceB2 ν c D2)) zero_le).trans hB2_lp
    have hLp_10 : tailLpNorm (-9 / 8) T term10 ≤
        ENNReal.ofReal (3 * C_G * ν⁻¹) * hNorm c bgp F :=
      (tailLpNorm_rpow_mul_le (by norm_num) hT1 B10).trans hB10_lp
    calc tailLpNorm (-9 / 8) T (fun s => term2 s + term10 s)
        ≤ tailLpNorm (-9 / 8) T term2 + tailLpNorm (-9 / 8) T term10 :=
          tailLpNorm_add_le (-9 / 8) T hm_term2 hm_term10
      _ ≤ ENNReal.ofReal (4 * C_G * ν⁻¹) * hNorm c bgp F +
            ENNReal.ofReal (3 * C_G * ν⁻¹) * hNorm c bgp F := add_le_add hLp_2 hLp_10
      _ = ENNReal.ofReal (7 * C_G * ν⁻¹) * hNorm c bgp F := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2; ring
  -- 5. Combine `L¹` and `tailLpNorm` bounds for `sliceH1Norm c g gq gη`.
  have h_ae_T : ∀ᵐ s ∂volume, T < s →
      sliceH1Norm c g gq gη s ≤ ENNReal.ofReal M * tailSliceRHS ν c b0' b0q b0η D2 s := by
    filter_upwards [hslice] with s hs hsT
    exact hs (le_trans hT1 hsT.le)
  have hL1_g : ∫⁻ s in Ioi T, sliceH1Norm c g gq gη s ≤
      ENNReal.ofReal M * ∫⁻ s in Ioi T, tailSliceRHS ν c b0' b0q b0η D2 s := by
    rw [← lintegral_const_mul _ (measurable_tailSliceRHS ν c hsm0 hsmq hsmη hsmD2)]
    exact lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr h_ae_T)
  have hLp_g : tailLpNorm (-9 / 8) T (sliceH1Norm c g gq gη) ≤
      ENNReal.ofReal M * tailLpNorm (-9 / 8) T (tailSliceRHS ν c b0' b0q b0η D2) := by
    calc tailLpNorm (-9 / 8) T (sliceH1Norm c g gq gη)
        ≤ tailLpNorm (-9 / 8) T
            (fun s => ENNReal.ofReal M * tailSliceRHS ν c b0' b0q b0η D2 s) :=
          tailLpNorm_mono_ae h_ae_T
      _ = ENNReal.ofReal M * tailLpNorm (-9 / 8) T (tailSliceRHS ν c b0' b0q b0η D2) :=
          tailLpNorm_const_mul (-9 / 8) T _ ENNReal.ofReal_ne_top _
  calc (∫⁻ s in Ioi T, sliceH1Norm c g gq gη s) +
        tailLpNorm (-9 / 8) T (sliceH1Norm c g gq gη)
      ≤ ENNReal.ofReal M * (ENNReal.ofReal (14 * C_G * ν⁻¹) * hNorm c bgp F) +
          ENNReal.ofReal M * (ENNReal.ofReal (7 * C_G * ν⁻¹) * hNorm c bgp F) :=
        add_le_add (hL1_g.trans (mul_le_mul_of_nonneg_left hL1_RHS zero_le))
          (hLp_g.trans (mul_le_mul_of_nonneg_left hLp_RHS zero_le))
    _ = ENNReal.ofReal (21 * M * C_G * ν⁻¹) * hNorm c bgp F := by
        rw [← mul_assoc, ← mul_assoc, ← add_mul,
          ← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_mul hM0,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2; ring

/-! ## 5. Leaf propositions (`PartII-b:F7/1`, `PartII-b:F7/2`) and conditional assemblies -/

/-- **Leaf 1 (`PartII-b:F7/1`, `TailSourceSliceBound`, SP 2269–2282)**:
for `s ≥ 1`, spatial Hölder with `r = 22/3` (`1/2 = 3/22 + 4/11`) and the Part I late train decay
bounds `‖D^j v(s)‖_{22/3} ≤ 𝒫_ν s^{-(41+22j)/44}`, `‖v(s)‖_∞ ≤ 𝒫_ν s⁻¹`, `‖Dv(s)‖_∞ ≤ 𝒫_ν s^{-3/2}`
yield the slice inequality `short-bg:tail-source` (`SP 2281`) together with the global `H_p`
free-graph bounds on the given representatives `b0', b0q, b0η, D2`. -/
def TailSourceSliceBound : Prop :=
  ∀ dm dp : ℝ, 0 < dm →
    ∃ (C_sl C_G : ℝ) (k_sl : ℕ) (ν₀ : ℝ), 0 < C_sl ∧ 0 < C_G ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ (F b0 b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf),
        InHr p.c bgp F → InFlatClass p.c bgp b0 → IsFlatResponse p.ν 0 F b0 →
        (∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) →
        InHr p.c bgp b0' → InHr p.c bgp (sqrtS b0q) → InHr p.c bgp (sqrtS b0η) →
        (∀ i j, InHr p.c bgp (mulS (D2 i j))) →
        StronglyMeasurable b0' → StronglyMeasurable b0q → StronglyMeasurable b0η →
        (∀ i j, StronglyMeasurable (D2 i j)) →
        HasWeakVec vQ0 dZero b0 b0q → HasWeakVec vEta dZero b0 b0η →
        HasWeakVec vQ0 dZero b0q (D2 0 0) → HasWeakVec vEta dZero b0q (D2 0 1) →
        HasWeakVec vQ0 dZero b0η (D2 1 0) → HasWeakVec vEta dZero b0η (D2 1 1) →
        hNorm p.c bgp b0' ≤ ENNReal.ofReal C_G * hNorm p.c bgp F ∧
        ENNReal.ofReal (Real.sqrt p.ν) * hNorm p.c bgp (sqrtS b0q) ≤
          ENNReal.ofReal C_G * hNorm p.c bgp F ∧
        ENNReal.ofReal (Real.sqrt p.ν) * hNorm p.c bgp (sqrtS b0η) ≤
          ENNReal.ofReal C_G * hNorm p.c bgp F ∧
        (∀ i j, ENNReal.ofReal p.ν * hNorm p.c bgp (mulS (D2 i j)) ≤
          ENNReal.ofReal C_G * hNorm p.c bgp F) ∧
        ∃ g gq gη : CProf,
          QPeriodic p.c g ∧ HasWeakVec vQ0 dZero g gq ∧ HasWeakVec vEta dZero g gη ∧
          IsBodySource p.train b0 b0q b0η g ∧
          Measurable (sliceH1Norm p.c g gq gη) ∧
          (∀ᵐ s ∂volume, 1 ≤ s →
            sliceH1Norm p.c g gq gη s ≤
              ENNReal.ofReal (C_sl * (p.ν ^ k_sl)⁻¹) *
                tailSliceRHS p.ν p.c b0' b0q b0η D2 s)

/-- **Proof of `TailSource` from `TailSourceSliceBound`** using the proved weighted Hölder theorem
`tailSource_integrals_of_slice_bound`. -/
theorem tailSource_of_slice (hSl : TailSourceSliceBound) : TailSource := by
  intro dm dp hdm
  obtain ⟨C_sl, C_G, k_sl, ν_sl, hC_sl, hC_G, hν_sl, hsl⟩ := hSl dm dp hdm
  set C_tot : ℝ := C_sl + 21 * C_sl * C_G
  have hC_tot : 0 < C_tot := by positivity
  set k_tot : ℕ := k_sl + 1
  set ν₀ : ℝ := min ν_sl 1
  have hν₀ : 0 < ν₀ := lt_min hν_sl one_pos
  refine ⟨C_tot, k_tot, ν₀, hC_tot, hν₀, ?_⟩
  intro p d hreg hν F b0 b0' b0q b0η D2 hF hb0 hresp hae0 hb0'H hbqH hbηH hD2H
    hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11
  have hν_sl' : p.ν ≤ ν_sl := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hν0 : 0 < p.ν := p.ν_pos
  obtain ⟨hb0_bd, hbq_bd, hbη_bd, hD2_bd, g, gq, gη, hgper, hgwq, hgwη, hgsrc, hmg1, hslice⟩ :=
    hsl p d hreg hν_sl' F b0 b0' b0q b0η D2 hF hb0 hresp hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11
  have hpow_le : (p.ν ^ k_sl)⁻¹ ≤ (p.ν ^ k_tot)⁻¹ :=
    inv_anti₀ (pow_pos hν0 k_tot) (pow_le_pow_of_le_one hν0.le hν1 (Nat.le_succ k_sl))
  have hC_le : C_sl * (p.ν ^ k_sl)⁻¹ ≤ C_tot * (p.ν ^ k_tot)⁻¹ := by
    have : C_sl ≤ C_tot := by dsimp [C_tot]; linarith [mul_pos hC_sl hC_G]
    exact mul_le_mul this hpow_le (by positivity) hC_tot.le
  refine ⟨g, gq, gη, hgper, hgwq, hgwη, hgsrc, hmg1, ?_, ?_⟩
  · filter_upwards [hslice] with s hs hs1
    refine (hs hs1).trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hC_le) zero_le
  · intro T hT1
    have hint := tailSource_integrals_of_slice_bound hν0 hν1 (by positivity) hC_G.le
      hsm0 hsmq hsmη hsmD2 hb0_bd hbq_bd hbη_bd hD2_bd hslice T hT1
    refine hint.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
    calc 21 * (C_sl * (p.ν ^ k_sl)⁻¹) * C_G * p.ν⁻¹
        = (21 * C_sl * C_G) * ((p.ν ^ k_sl)⁻¹ * p.ν⁻¹) := by ring
      _ = (21 * C_sl * C_G) * (p.ν ^ k_tot)⁻¹ := by
          dsimp [k_tot]
          rw [pow_succ, mul_inv]
      _ ≤ C_tot * (p.ν ^ k_tot)⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          dsimp [C_tot]
          linarith

/-- **Leaf 2 (`PartII-b:F7/2`, `GlobalEnergyContinuation`, SP 2289–2295, display
`short-bg:global-energy` at 2294)**:
from `EarlyBound` (`PartII-b:F6`), `BodySourceBound` (`PartII-b:F5`), and `TailSource` (`SP 2281`),
differentiated `H¹` velocity energy and the late-train integrable tail bound (`short-bg:train-late`,
SP 2054–2057: `∫_{Σ/ν}^∞ (‖Dv_c(s)‖_∞ + ‖D²v_c(s)‖_∞) ds ≤ C_late / (ν(1 + Σ)) + C_late ν³`)
continue the meridional correction `z` from `(0, p.H]` to `(0, ∞)` with
`sup_{s > 0} ‖z(s)‖_{H¹} + ‖αMap F‖ ≤ C ν^{-k} exp((a'Σ + C_late/(1+Σ))/ν + C_late ν³) ‖F‖`. -/
def GlobalEnergyContinuation : Prop :=
  EarlyBound → BodySourceBound → TailSource → GlobalEnergy

/-- **Conditional assembly of `TailSourceAndGlobalEnergy` (`PartII-b:F7`)** from
`TailSourceSliceBound` (`PartII-b:F7/1`), `GlobalEnergyContinuation` (`PartII-b:F7/2`),
`EarlyBound` (`PartII-b:F6`), and `BodySourceBound` (`PartII-b:F5`). -/
theorem tailSourceAndGlobalEnergy_of_leaves
    (hSl : TailSourceSliceBound)
    (hCont : GlobalEnergyContinuation)
    (hEB : UnforcedLeray.Short.IIb.EarlyBound)
    (hBS : UnforcedLeray.Short.IIb.BodySourceBound) :
    UnforcedLeray.Short.IIb.TailSourceAndGlobalEnergy :=
  let hTS := tailSource_of_slice hSl
  ⟨hTS, hCont hEB hBS hTS⟩

end UnforcedLeray.Short.IIb

end
