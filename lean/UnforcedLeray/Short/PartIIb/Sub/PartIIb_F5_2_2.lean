import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2

/-!
# Sub-goals for `PartII-b:F5/2/2` (`CylBodySourceProjection`)

Source of record: `the November 2 reference manuscript` (SP), lines 2213–2239
(`g = -P_0(v_c · ∇b_0 + b_0 · ∇v_c)`, display `short-bg:source` at line 2235).

## Proved here (zero `sorry`)

1. `CylProjectionSub.measurable_sliceL2Norm_cp`, `CylProjectionSub.measurable_sliceH1Norm_cp`,
   `CylProjectionSub.measurable_profCurl_cp`, `CylProjectionSub.measurable_sliceXmNorm_cp`:
   measurability of the `L²(C_c)`, `H¹(C_c)`, and `X_{m,c}` slice seminorms for strongly measurable
   profiles;
2. `p0Merid`, `norm_p0Merid_le`, `eLpNorm_p0Merid_le`: the `ℂ²`-valued cylinder Leray projection
   `IIIa.P0C c` lifted to `CMerid` and its `L²(B0579.cell c)` boundedness with constant `K_L = 2`
   (from `Cyl.norm_P0_le`);
3. `CylProjectionSub.sliceH1Norm_zero_of_eq_zero`, `CylProjectionSub.sliceXmNorm_zero_of_eq_zero`,
   `CylProjectionSub.sliceXmNorm_eq_of_ae_neg_cell`,
   `CylProjectionSub.integrableOn_and_integral_zero_of_ae_neg_cell`: transfer of `sliceH1Norm`,
   `sliceXmNorm`, and zero cell circulation under a.e. equality
   `profCurl gq gη (s, ·) = -profCurl Uq Uη (s, ·)` on good slices and vanishing on bad slices;
4. Conditional assembly `cylBodySourceProjection_of_leaves`: proves `CylBodySourceProjection` (via
   `cylBodySourceProjection_of_leray` in `Short/PartII-b/Sub/PartII-b_F5_2.lean`) from the three
   leaf propositions:
   * `FlatBvWeakLeibniz` (`PartII-b:F5/2/2/1`);
   * `FlatBvSliceGoodAe` (`PartII-b:F5/2/2/2`; restated with the train hypothesis
     `∀ᵐ s, 0 < s → trainSliceNorm22_3 c m tr s < ⊤`, SP 2228-2233);
   * `P0SliceLiftH1` (`PartII-b:F5/2/2/3`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

namespace CylProjectionSub

/-! ## 1. Measurability of `sliceH1Norm` and `sliceXmNorm` -/

theorem sliceL2Norm_eq_lintegral_cp (c : ℝ) (u : CProf) (s : ℝ) :
    eLpNorm (fun x => u (s, x)) 2 (volume.restrict (B0579.cell c)) =
      (∫⁻ x in B0579.cell c, ‖u (s, x)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have h0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have ht : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ht]
  simp

theorem measurable_sliceL2Norm_cp (c : ℝ) {u : CProf} (hu : StronglyMeasurable u) :
    Measurable (fun s : ℝ => eLpNorm (fun x => u (s, x)) 2 (volume.restrict (B0579.cell c))) := by
  have h1 : Measurable (fun p : Coord => ‖u p‖ₑ ^ (2 : ℝ)) :=
    (hu.measurable.enorm).pow_const (2 : ℝ)
  have h2 : Measurable (fun s : ℝ => ∫⁻ x in B0579.cell c, ‖u (s, x)‖ₑ ^ (2 : ℝ)) :=
    h1.lintegral_prod_right'
  have h3 : (fun s : ℝ => eLpNorm (fun x => u (s, x)) 2 (volume.restrict (B0579.cell c))) =
      fun s : ℝ => (∫⁻ x in B0579.cell c, ‖u (s, x)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    funext (sliceL2Norm_eq_lintegral_cp c u)
  rw [h3]
  exact h2.pow_const (1 / 2 : ℝ)

theorem measurable_sliceH1Norm_cp (c : ℝ) {z zq zη : CProf}
    (hz : StronglyMeasurable z) (hzq : StronglyMeasurable zq) (hzη : StronglyMeasurable zη) :
    Measurable (sliceH1Norm c z zq zη) := by
  unfold sliceH1Norm
  exact ((measurable_sliceL2Norm_cp c hz).add (measurable_sliceL2Norm_cp c hzq)).add
    (measurable_sliceL2Norm_cp c hzη)

theorem measurable_profCurl_cp {zq zη : CProf}
    (hzq : StronglyMeasurable zq) (hzη : StronglyMeasurable zη) :
    Measurable (profCurl zq zη) := by
  unfold profCurl
  have h1 : Measurable (fun x : Coord => zq x 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : CMerid →L[ℂ] ℂ).measurable.comp hzq.measurable
  have h0 : Measurable (fun x : Coord => zη x 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : CMerid →L[ℂ] ℂ).measurable.comp hzη.measurable
  exact h1.sub h0

theorem sliceXmNorm_eq_lintegral_cp (c m : ℝ) (w : Coord → ℂ) (s : ℝ) :
    sliceXmNorm c m w s =
      (∫⁻ x in B0579.cell c, ‖B0579.jb x ^ (m / 2) * ‖w (s, x)‖‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  unfold sliceXmNorm
  rw [← eLpNorm_norm (fun x => w (s, x)), B0579.eLpNorm_cellMeasure]
  have h0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have ht : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ht]
  simp

theorem measurable_sliceXmNorm_cp (c m : ℝ) {w : Coord → ℂ} (hw : Measurable w) :
    Measurable (sliceXmNorm c m w) := by
  have hjb : Measurable (fun p : Coord => B0579.jb p.2 ^ (m / 2)) :=
    (B0579.continuous_jb_rpow (m / 2)).measurable.comp measurable_snd
  have h1 : Measurable (fun p : Coord => ‖B0579.jb p.2 ^ (m / 2) * ‖w p‖‖ₑ ^ (2 : ℝ)) :=
    ((hjb.mul hw.norm).enorm).pow_const (2 : ℝ)
  have h2 : Measurable (fun s : ℝ =>
      ∫⁻ x in B0579.cell c, ‖B0579.jb x ^ (m / 2) * ‖w (s, x)‖‖ₑ ^ (2 : ℝ)) :=
    h1.lintegral_prod_right'
  have h3 : sliceXmNorm c m w =
      fun s : ℝ =>
        (∫⁻ x in B0579.cell c, ‖B0579.jb x ^ (m / 2) * ‖w (s, x)‖‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    funext (sliceXmNorm_eq_lintegral_cp c m w)
  rw [h3]
  exact h2.pow_const (1 / 2 : ℝ)

theorem norm_reVec_le (u : B0579.Plane → CMerid) (z : B0579.Plane) :
    ‖IIIa.reVec (fun y i => u y i) z‖ ≤ ‖u z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two]
  apply Real.sqrt_le_sqrt
  have h0 : ‖(IIIa.reVec (fun y i => u y i) z) 0‖ ^ 2 ≤ ‖u z 0‖ ^ 2 := by
    change |(u z 0).re| ^ 2 ≤ ‖u z 0‖ ^ 2
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (u z 0)) 2
  have h1 : ‖(IIIa.reVec (fun y i => u y i) z) 1‖ ^ 2 ≤ ‖u z 1‖ ^ 2 := by
    change |(u z 1).re| ^ 2 ≤ ‖u z 1‖ ^ 2
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (u z 1)) 2
  linarith

theorem norm_imVec_le (u : B0579.Plane → CMerid) (z : B0579.Plane) :
    ‖IIIa.imVec (fun y i => u y i) z‖ ≤ ‖u z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two]
  apply Real.sqrt_le_sqrt
  have h0 : ‖(IIIa.imVec (fun y i => u y i) z) 0‖ ^ 2 ≤ ‖u z 0‖ ^ 2 := by
    change |(u z 0).im| ^ 2 ≤ ‖u z 0‖ ^ 2
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm (u z 0)) 2
  have h1 : ‖(IIIa.imVec (fun y i => u y i) z) 1‖ ^ 2 ≤ ‖u z 1‖ ^ 2 := by
    change |(u z 1).im| ^ 2 ≤ ‖u z 1‖ ^ 2
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm (u z 1)) 2
  linarith

theorem eLpNorm_toL2v_le (c : ℝ) (F : B0579.Plane → UnforcedLeray.Cyl.Vec2) :
    eLpNorm (UnforcedLeray.Cyl.P0 c (IIIa.toL2v c F) : B0579.Plane → UnforcedLeray.Cyl.Vec2) 2
        (volume.restrict (B0579.cell c)) ≤
      eLpNorm F 2 (volume.restrict (B0579.cell c)) := by
  rw [← IIIa.cellμ_eq c]
  by_cases hF : MemLp F 2 (UnforcedLeray.Cyl.cellμ c)
  · have hto : IIIa.toL2v c F = hF.toLp F := by
      unfold IIIa.toL2v
      simp [hF]
    rw [hto]
    have hnorm_P0 : ‖UnforcedLeray.Cyl.P0 c (hF.toLp F)‖ ≤ ‖hF.toLp F‖ := by
      calc ‖UnforcedLeray.Cyl.P0 c (hF.toLp F)‖
          ≤ ‖UnforcedLeray.Cyl.P0 c‖ * ‖hF.toLp F‖ :=
            (UnforcedLeray.Cyl.P0 c).le_opNorm _
        _ ≤ 1 * ‖hF.toLp F‖ :=
            mul_le_mul_of_nonneg_right UnforcedLeray.Cyl.norm_P0_le (norm_nonneg _)
        _ = ‖hF.toLp F‖ := one_mul _
    have h1 : eLpNorm (UnforcedLeray.Cyl.P0 c (hF.toLp F) : B0579.Plane → UnforcedLeray.Cyl.Vec2) 2
          (UnforcedLeray.Cyl.cellμ c) =
        ENNReal.ofReal ‖UnforcedLeray.Cyl.P0 c (hF.toLp F)‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    have h2 : eLpNorm F 2 (UnforcedLeray.Cyl.cellμ c) = ENNReal.ofReal ‖hF.toLp F‖ := by
      rw [Lp.norm_toLp, ENNReal.ofReal_toReal hF.eLpNorm_lt_top.ne]
    rw [h1, h2]
    exact ENNReal.ofReal_le_ofReal hnorm_P0
  · have hto : IIIa.toL2v c F = 0 := by
      unfold IIIa.toL2v
      simp [hF]
    rw [hto, map_zero]
    have h0 : eLpNorm ((0 : UnforcedLeray.Cyl.L2v c) : B0579.Plane → UnforcedLeray.Cyl.Vec2) 2
        (UnforcedLeray.Cyl.cellμ c) = 0 := by
      rw [eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
    rw [h0]
    exact zero_le

/-! ## 3. Slice norm and zero-circulation transfer lemmas -/

theorem sliceH1Norm_zero_of_eq_zero (c : ℝ) {g gq gη : CProf} {s : ℝ}
    (hg : ∀ z, g (s, z) = 0) (hgq : ∀ z, gq (s, z) = 0) (hgη : ∀ z, gη (s, z) = 0) :
    sliceH1Norm c g gq gη s = 0 := by
  unfold sliceH1Norm
  have e0 : (fun z => g (s, z)) = 0 := funext hg
  have eq : (fun z => gq (s, z)) = 0 := funext hgq
  have eη : (fun z => gη (s, z)) = 0 := funext hgη
  rw [e0, eq, eη, eLpNorm_zero, add_zero, add_zero]

theorem sliceXmNorm_zero_of_eq_zero (c m : ℝ) {gq gη : CProf} {s : ℝ}
    (hgq : ∀ z, gq (s, z) = 0) (hgη : ∀ z, gη (s, z) = 0) :
    sliceXmNorm c m (profCurl gq gη) s = 0 := by
  unfold sliceXmNorm
  have ew : (fun z => profCurl gq gη (s, z)) = 0 := by
    funext z
    unfold profCurl
    rw [hgq z, hgη z]
    simp
  rw [ew, eLpNorm_zero]

theorem sliceXmNorm_eq_of_ae_neg_cell (c m : ℝ) {w₁ w₂ : Coord → ℂ} {s : ℝ}
    (hae : ∀ᵐ z ∂(volume.restrict (B0579.cell c)), w₁ (s, z) = -w₂ (s, z)) :
    sliceXmNorm c m w₁ s = sliceXmNorm c m w₂ s := by
  unfold sliceXmNorm
  rw [← eLpNorm_norm (fun z => w₁ (s, z)), ← eLpNorm_norm (fun z => w₂ (s, z)),
    B0579.eLpNorm_cellMeasure, B0579.eLpNorm_cellMeasure]
  refine eLpNorm_congr_ae ?_
  filter_upwards [hae] with z hz
  rw [hz, norm_neg]

theorem integrableOn_and_integral_zero_of_ae_neg_cell (c : ℝ) {w₁ w₂ : Coord → ℂ} {s : ℝ}
    (hae : ∀ᵐ z ∂(volume.restrict (B0579.cell c)), w₁ (s, z) = -w₂ (s, z))
    (hint : IntegrableOn (fun z => w₂ (s, z)) (B0579.cell c) volume)
    (hcirc : ∫ z in B0579.cell c, w₂ (s, z) = 0) :
    IntegrableOn (fun z => w₁ (s, z)) (B0579.cell c) volume ∧
      ∫ z in B0579.cell c, w₁ (s, z) = 0 := by
  have hae' : (fun z => -w₂ (s, z)) =ᵐ[volume.restrict (B0579.cell c)] (fun z => w₁ (s, z)) :=
    hae.mono fun _ hz => hz.symm
  refine ⟨hint.neg.congr hae', ?_⟩
  rw [integral_congr_ae hae, integral_neg, hcirc, neg_zero]

end CylProjectionSub

open CylProjectionSub

/-! ## 2. `CMerid` lift of `IIIa.P0C` and `L²(cell)` contraction bound -/

/-- The `CMerid`-valued cylinder Leray projection `P_0` on a slice `u : B0579.Plane → CMerid`,
defined via `IIIa.P0C c` on the real and imaginary parts in `L²(B0579.cell c; ℝ²)`. -/
def p0Merid (c : ℝ) (u : B0579.Plane → CMerid) : B0579.Plane → CMerid :=
  fun z => WithLp.toLp 2 (IIIa.P0C c (fun y i => u y i) z)

theorem norm_p0Merid_le (c : ℝ) (u : B0579.Plane → CMerid) (z : B0579.Plane) :
    ‖p0Merid c u z‖ ≤
      ‖(IIIa.P0re c (fun y i => u y i) : B0579.Plane → UnforcedLeray.Cyl.Vec2) z‖ +
        ‖(IIIa.P0im c (fun y i => u y i) : B0579.Plane → UnforcedLeray.Cyl.Vec2) z‖ := by
  set a := (IIIa.P0re c (fun y i => u y i) : B0579.Plane → UnforcedLeray.Cyl.Vec2) z
  set b := (IIIa.P0im c (fun y i => u y i) : B0579.Plane → UnforcedLeray.Cyl.Vec2) z
  let aC : CMerid := WithLp.toLp 2 fun i : Fin 2 => ((a i : ℝ) : ℂ)
  let bC : CMerid := WithLp.toLp 2 fun i : Fin 2 => Complex.I * ((b i : ℝ) : ℂ)
  have heq : p0Merid c u z = aC + bC := by
    ext i
    rfl
  have haC : ‖aC‖ = ‖a‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [aC]
  have hbC : ‖bC‖ = ‖b‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [bC]
  rw [heq, ← haC, ← hbC]
  exact norm_add_le aC bC

theorem eLpNorm_p0Merid_le (c : ℝ) (u : B0579.Plane → CMerid) :
    eLpNorm (p0Merid c u) 2 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal 2 * eLpNorm u 2 (volume.restrict (B0579.cell c)) := by
  obtain ⟨Fr, hFr⟩ : ∃ Fr : B0579.Plane → UnforcedLeray.Cyl.Vec2,
      Fr = (IIIa.P0re c (fun y i => u y i) : B0579.Plane → UnforcedLeray.Cyl.Vec2) := ⟨_, rfl⟩
  obtain ⟨Fi, hFi⟩ : ∃ Fi : B0579.Plane → UnforcedLeray.Cyl.Vec2,
      Fi = (IIIa.P0im c (fun y i => u y i) : B0579.Plane → UnforcedLeray.Cyl.Vec2) := ⟨_, rfl⟩
  have hFr_meas : AEStronglyMeasurable (fun z => ‖Fr z‖) (volume.restrict (B0579.cell c)) := by
    rw [← IIIa.cellμ_eq c, hFr]
    exact (Lp.aestronglyMeasurable _).norm
  have hFi_meas : AEStronglyMeasurable (fun z => ‖Fi z‖) (volume.restrict (B0579.cell c)) := by
    rw [← IIIa.cellμ_eq c, hFi]
    exact (Lp.aestronglyMeasurable _).norm
  have h1 : eLpNorm (p0Merid c u) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm ((fun z => ‖Fr z‖) + (fun z => ‖Fi z‖)) 2 (volume.restrict (B0579.cell c)) := by
    refine eLpNorm_mono_real fun z => ?_
    simp only [Pi.add_apply, hFr, hFi]
    exact norm_p0Merid_le c u z
  have h2 : eLpNorm ((fun z => ‖Fr z‖) + (fun z => ‖Fi z‖)) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm Fr 2 (volume.restrict (B0579.cell c)) +
        eLpNorm Fi 2 (volume.restrict (B0579.cell c)) := by
    refine (eLpNorm_add_le hFr_meas hFi_meas one_le_two).trans_eq ?_
    rw [eLpNorm_norm, eLpNorm_norm]
  have hFr_le : eLpNorm Fr 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm u 2 (volume.restrict (B0579.cell c)) := by
    rw [hFr]
    unfold IIIa.P0re
    exact (eLpNorm_toL2v_le c _).trans
      ((eLpNorm_mono_real (norm_reVec_le u)).trans_eq (eLpNorm_norm u))
  have hFi_le : eLpNorm Fi 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm u 2 (volume.restrict (B0579.cell c)) := by
    rw [hFi]
    unfold IIIa.P0im
    exact (eLpNorm_toL2v_le c _).trans
      ((eLpNorm_mono_real (norm_imVec_le u)).trans_eq (eLpNorm_norm u))
  have htwo : ENNReal.ofReal 2 = (1 : ℝ≥0∞) + 1 := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one zero_le_one]
    norm_num
  calc eLpNorm (p0Merid c u) 2 (volume.restrict (B0579.cell c))
      ≤ eLpNorm Fr 2 (volume.restrict (B0579.cell c)) +
          eLpNorm Fi 2 (volume.restrict (B0579.cell c)) := h1.trans h2
    _ ≤ eLpNorm u 2 (volume.restrict (B0579.cell c)) +
          eLpNorm u 2 (volume.restrict (B0579.cell c)) := add_le_add hFr_le hFi_le
    _ = ENNReal.ofReal 2 * eLpNorm u 2 (volume.restrict (B0579.cell c)) := by
        rw [htwo, add_mul, one_mul]

/-! ## 4. Leaf propositions for `CylBodySourceProjection` (`PartII-b:F5/2/2`) -/

/-- **Leaf 1 (`PartII-b:F5/2/2/1`, `FlatBvWeakLeibniz`)**: spacetime weak Leibniz rule on `Coord`
for the unprojected convective interaction `flatBv tr b0' b0q b0η = (v·∇)b0' + (b0'·∇)v`.
From `b0' = b0` a.e. on `0 < x.1`, the `H_p` bounds on `b0', √s b0q, √s b0η, s D2 i j`, the
first- and second-order weak derivatives `HasWeakVec` of `b0, b0q, b0η`, and the `C^∞` regularity
of `tr.v` on `[0, ∞) × ℝ²`, `flatBv tr b0' b0q b0η` has weak `q`-derivative
`flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)` and weak `η`-derivative
`flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)`. -/
def FlatBvWeakLeibniz : Prop :=
  ∀ {ν c : ℝ} (tr : B0140.TrainSol ν c), 0 < c →
  ∀ (b0 b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf),
    InFlatClass c bgp b0 →
    (∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) →
    InHr c bgp b0' → InHr c bgp (sqrtS b0q) → InHr c bgp (sqrtS b0η) →
    (∀ i j, InHr c bgp (mulS (D2 i j))) →
    StronglyMeasurable b0' → StronglyMeasurable b0q → StronglyMeasurable b0η →
    (∀ i j, StronglyMeasurable (D2 i j)) →
    HasWeakVec vQ0 dZero b0 b0q → HasWeakVec vEta dZero b0 b0η →
    HasWeakVec vQ0 dZero b0q (D2 0 0) → HasWeakVec vEta dZero b0q (D2 0 1) →
    HasWeakVec vQ0 dZero b0η (D2 1 0) → HasWeakVec vEta dZero b0η (D2 1 1) →
    HasWeakVec vQ0 dZero (flatBv tr b0' b0q b0η)
      (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)) ∧
    HasWeakVec vEta dZero (flatBv tr b0' b0q b0η)
      (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1))

/-- **Leaf 2 (`PartII-b:F5/2/2/2`, `FlatBvSliceGoodAe`)**: Fubini slice disintegration for
`U = flatBv tr b0' b0q b0η`, `Uq = flatBvQ ...`, `Uη = flatBvEta ...`.
For `m > 8`, `0 < c`, and a train whose weighted `L^{22/3}` jet norm `trainSliceNorm22_3 c m tr s`
is finite for a.e. `s > 0` (SP 2228-2233: Hölder `1/2 = 3/22 + 4/11` with the train in `L^{22/3}`;
an arbitrary `B0140.TrainSol` has no such bound; same statement as
`FlatBvSliceGoodAeNeeded.FlatBvSliceGoodAeTr`), for a.e. `s > 0`:
1. the slice norms `sliceH1Norm c U Uq Uη s` and `sliceXmNorm c m (profCurl Uq Uη) s` are finite
   (by Tonelli from `InHr c bgp` of `b0', sqrtS b0q, sqrtS b0η, mulS (D2 i j)`, the train
   hypothesis, and `sliceH1Norm_flatBv_le` / `sliceXmNorm_flatBv_curl_le`);
2. each component of `U(s, ·)` has cylinder weak derivatives `Uq(s, ·)` and `Uη(s, ·)` on
   `B0579.cell c` (`IIIa.HasWeakCellDerivC c 0` and `IIIa.HasWeakCellDerivC c 1`);
3. `profCurl Uq Uη (s, ·)` is integrable on `B0579.cell c` with zero integral
   `∫ z in B0579.cell c, profCurl Uq Uη (s, z) = 0` (by `q`-periodicity of `U_1` and `η`-decay of
   `U_0`). -/
def FlatBvSliceGoodAe : Prop :=
  ∀ (m : ℝ), 8 < m → ∀ {ν c : ℝ} (tr : B0140.TrainSol ν c), 0 < c →
  (∀ᵐ s ∂volume, 0 < s → trainSliceNorm22_3 c m tr s < ⊤) →
  ∀ (b0 b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf),
    InFlatClass c bgp b0 →
    (∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) →
    InHr c bgp b0' → InHr c bgp (sqrtS b0q) → InHr c bgp (sqrtS b0η) →
    (∀ i j, InHr c bgp (mulS (D2 i j))) →
    StronglyMeasurable b0' → StronglyMeasurable b0q → StronglyMeasurable b0η →
    (∀ i j, StronglyMeasurable (D2 i j)) →
    HasWeakVec vQ0 dZero b0 b0q → HasWeakVec vEta dZero b0 b0η →
    HasWeakVec vQ0 dZero b0q (D2 0 0) → HasWeakVec vEta dZero b0q (D2 0 1) →
    HasWeakVec vQ0 dZero b0η (D2 1 0) → HasWeakVec vEta dZero b0η (D2 1 1) →
    HasWeakVec vQ0 dZero (flatBv tr b0' b0q b0η)
      (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)) →
    HasWeakVec vEta dZero (flatBv tr b0' b0q b0η)
      (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) →
    let U := flatBv tr b0' b0q b0η
    let Uq := flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)
    let Uη := flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)
    ∀ᵐ s ∂volume, 0 < s →
      sliceH1Norm c U Uq Uη s < ⊤ ∧
      sliceXmNorm c m (profCurl Uq Uη) s < ⊤ ∧
      (∀ i : Fin 2,
        IIIa.HasWeakCellDerivC c 0 (fun z => U (s, z) i) (fun z => Uq (s, z) i) ∧
        IIIa.HasWeakCellDerivC c 1 (fun z => U (s, z) i) (fun z => Uη (s, z) i)) ∧
      IntegrableOn (fun z => profCurl Uq Uη (s, z)) (B0579.cell c) volume ∧
      ∫ z in B0579.cell c, profCurl Uq Uη (s, z) = 0

/-- **Leaf 3 (`PartII-b:F5/2/2/3`, `P0SliceLiftH1`)**: jointly measurable slice-by-slice cylinder
Leray projection of `-U = -flatBv tr b0' b0q b0η` in `H¹(C_c)` (set to `0` on the null set of bad
slices `s` where the slice `H¹` / `X_m` / weak-derivative properties fail).
Using `p0Merid c`, `IIIa.p0CommWeakC`, `IIIa.p0DivFreeC`, `IIIa.p0OrthC`, `Cyl.curl_P0`, and
`Infra/JointMeasurableRep.lean`, produces strongly measurable `g, gq, gη : CProf` such that:
1. `QPeriodic c g`, `HasWeakVec vQ0 dZero g gq`, `HasWeakVec vEta dZero g gη`, and
   `IsBodySource tr b0' b0q b0η g`;
2. for every `s > 0`, `sliceH1Norm c g gq gη s ≤ ENNReal.ofReal 2 * sliceH1Norm c U Uq Uη s`;
3. for every `s > 0`, either `gq (s, ·) = gη (s, ·) = 0` (when `s` is a bad slice) or
   `profCurl gq gη (s, ·) =ᵐ[volume.restrict (B0579.cell c)] -profCurl Uq Uη (s, ·)` (when `s` is a
   good slice), and the latter holds for a.e. `s > 0`. -/
def P0SliceLiftH1 : Prop :=
  ∀ (m : ℝ), 8 < m → ∀ {ν c : ℝ} (tr : B0140.TrainSol ν c), 0 < c →
  ∀ (b0 b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf),
    InFlatClass c bgp b0 →
    (∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) →
    InHr c bgp b0' → InHr c bgp (sqrtS b0q) → InHr c bgp (sqrtS b0η) →
    (∀ i j, InHr c bgp (mulS (D2 i j))) →
    StronglyMeasurable b0' → StronglyMeasurable b0q → StronglyMeasurable b0η →
    (∀ i j, StronglyMeasurable (D2 i j)) →
    HasWeakVec vQ0 dZero b0 b0q → HasWeakVec vEta dZero b0 b0η →
    HasWeakVec vQ0 dZero b0q (D2 0 0) → HasWeakVec vEta dZero b0q (D2 0 1) →
    HasWeakVec vQ0 dZero b0η (D2 1 0) → HasWeakVec vEta dZero b0η (D2 1 1) →
    let U := flatBv tr b0' b0q b0η
    let Uq := flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)
    let Uη := flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)
    HasWeakVec vQ0 dZero U Uq → HasWeakVec vEta dZero U Uη →
    (∀ᵐ s ∂volume, 0 < s →
      sliceH1Norm c U Uq Uη s < ⊤ ∧
      sliceXmNorm c m (profCurl Uq Uη) s < ⊤ ∧
      (∀ i : Fin 2,
        IIIa.HasWeakCellDerivC c 0 (fun z => U (s, z) i) (fun z => Uq (s, z) i) ∧
        IIIa.HasWeakCellDerivC c 1 (fun z => U (s, z) i) (fun z => Uη (s, z) i)) ∧
      IntegrableOn (fun z => profCurl Uq Uη (s, z)) (B0579.cell c) volume ∧
      ∫ z in B0579.cell c, profCurl Uq Uη (s, z) = 0) →
    ∃ g gq gη : CProf,
      StronglyMeasurable g ∧ StronglyMeasurable gq ∧ StronglyMeasurable gη ∧
      QPeriodic c g ∧ HasWeakVec vQ0 dZero g gq ∧ HasWeakVec vEta dZero g gη ∧
      IsBodySource tr b0' b0q b0η g ∧
      (∀ s : ℝ, 0 < s →
        sliceH1Norm c g gq gη s ≤ ENNReal.ofReal 2 * sliceH1Norm c U Uq Uη s) ∧
      (∀ s : ℝ, 0 < s →
        ((∀ z, gq (s, z) = 0 ∧ gη (s, z) = 0) ∨
          (∀ᵐ z ∂(volume.restrict (B0579.cell c)),
            profCurl gq gη (s, z) = -profCurl Uq Uη (s, z)))) ∧
      (∀ᵐ s ∂volume, 0 < s →
        ∀ᵐ z ∂(volume.restrict (B0579.cell c)),
          profCurl gq gη (s, z) = -profCurl Uq Uη (s, z))

/-! ## 5. Conditional assembly of `CylBodySourceProjection` (`PartII-b:F5/2/2`) -/

/-- **Conditional proof of `CylBodySourceProjection`** from `FlatBvWeakLeibniz`,
`FlatBvSliceGoodAe`, and `P0SliceLiftH1` via `cylBodySourceProjection_of_leray` (`K_L = 2`).
The train hypothesis of `FlatBvSliceGoodAe` (a.e. finiteness of `trainSliceNorm22_3`) follows from
the local train bound carried by `CylBodySourceProjection` (take `a = b = s`).
Composed by `PartII-b:F5/2/2` (`Tasks/BodySource/SliceHolder/CylProjection.lean`). -/
theorem cylBodySourceProjection_of_leaves
    (hLeib : FlatBvWeakLeibniz)
    (hGood : FlatBvSliceGoodAe)
    (hLift : P0SliceLiftH1) :
    UnforcedLeray.Short.IIb.CylBodySourceProjection := by
  apply cylBodySourceProjection_of_leray
  refine ⟨2, by norm_num,
    fun m hm p T hcp _hTp hTrp b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11 => ?_⟩
  have hTr_ae : ∀ᵐ s ∂volume, 0 < s → trainSliceNorm22_3 p.c m p.train s < ⊤ :=
    Eventually.of_forall fun s hs => by
      obtain ⟨C, hC⟩ := hTrp s s hs
      exact (hC s ⟨le_rfl, le_rfl⟩).trans_lt ENNReal.ofReal_lt_top
  obtain ⟨hwU_q, hwU_η⟩ :=
    hLeib p.train hcp b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11
  have hgood_ae :=
    hGood m hm p.train hcp hTr_ae b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11 hwU_q hwU_η
  obtain ⟨g, gq, gη, hsm_g, hsm_gq, hsm_gη, hgper, hgwq, hgwη, hgsrc,
      hH1_le, hcurl_dichot, hcurl_ae⟩ :=
    hLift m hm p.train hcp b0 b0' b0q b0η D2 hb0 hae0 hb0'H hbqH hbηH hD2H
      hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11 hwU_q hwU_η hgood_ae
  set U := flatBv p.train b0' b0q b0η
  set Uq := flatBvQ p.train b0' b0q b0η (D2 0 0) (D2 1 0)
  set Uη := flatBvEta p.train b0' b0q b0η (D2 0 1) (D2 1 1)
  refine ⟨g, gq, gη, hgper, hgwq, hgwη, hgsrc,
    measurable_sliceH1Norm_cp p.c hsm_g hsm_gq hsm_gη,
    measurable_sliceXmNorm_cp p.c m (measurable_profCurl_cp hsm_gq hsm_gη),
    fun s hs => ⟨hH1_le s hs.1, ?_⟩, ?_⟩
  · have h1le2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    rcases hcurl_dichot s hs.1 with hzero | hae_eq
    · rw [sliceXmNorm_zero_of_eq_zero p.c m (fun z => (hzero z).1) (fun z => (hzero z).2)]
      exact zero_le
    · rw [sliceXmNorm_eq_of_ae_neg_cell p.c m hae_eq]
      calc sliceXmNorm p.c m (profCurl Uq Uη) s
          = 1 * sliceXmNorm p.c m (profCurl Uq Uη) s := (one_mul _).symm
        _ ≤ ENNReal.ofReal 2 * sliceXmNorm p.c m (profCurl Uq Uη) s :=
            mul_le_mul_of_nonneg_right h1le2 zero_le
  · filter_upwards [hgood_ae, hcurl_ae] with s hgs hcs hs
    obtain ⟨_, _, _, hintU, hcircU⟩ := hgs hs.1
    exact integrableOn_and_integral_zero_of_ae_neg_cell p.c (hcs hs.1) hintU hcircU

end UnforcedLeray.Short.IIb

end
